#!/usr/bin/env python3
# python 3.6+

# Server for web component and state machine for expressions.

import getopt
import io
import json
import os
import re
import subprocess
import sys
import time
import threading
import traceback
import webbrowser

from collections import OrderedDict
from http.server import HTTPServer, SimpleHTTPRequestHandler
from socketserver import ThreadingMixIn
from urllib.parse import parse_qs

_RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT

_VERSION         = '1.0.19'

__OPTS, __ARGV   = getopt.getopt (sys.argv [1:], 'hvdnuEqysmtNOSgGz', ['child', 'firstrun',
	'help', 'version', 'debug', 'nobrowser', 'ugly', 'EI', 'quick', 'nopyS', 'simplify', 'nomatsimp',
	'nodoit', 'noN', 'noO', 'noS', 'nogamma', 'noGamma', 'nozeta'])

_SYMPAD_PATH     = os.path.dirname (sys.argv [0])
_SYMPAD_NAME     = os.path.basename (sys.argv [0])
_SYMPAD_CHILD    = ('--child', '') in __OPTS
_SYMPAD_FIRSTRUN = ('--firstrun', '') in __OPTS

_DEFAULT_ADDRESS = ('localhost', 9000)
_FILES           = {} # pylint food # AUTO_REMOVE_IN_SINGLE_SCRIPT
_STATIC_FILES    = {'/style.css': 'text/css', '/script.js': 'text/javascript', '/index.html': 'text/html',
	'/help.html': 'text/html', '/bg.png': 'image/png', '/wait.webp': 'image/webp'}

__name_indent    = ' ' * (7 + len (_SYMPAD_NAME))
_HELP            = f'usage: {_SYMPAD_NAME} ' \
		'[-h | --help] [-v | --version] \n' \
		f'{__name_indent} [-d | --debug] [-n | --nobrowser] \n' \
		f'{__name_indent} [-u | --ugly] [-E | --EI] \n' \
		f'{__name_indent} [-q | --quick] [-y | --nopyS] \n' \
		f'{__name_indent} [-s | --simplify] [-m | -nomatsimp] \n' \
		f'{__name_indent} [-t | --nodoit] \n' \
		f'{__name_indent} [-N | --noN] [-O | --noO] [-S | --noS] \n'\
		f'{__name_indent} [-b | --nobeta] [-g | --nogamma] \n' \
		f'{__name_indent} [-G | --noGamma] [-L | --noLambda] \n' \
		f'{__name_indent} [-z | --nozeta] \n' \
		f'{__name_indent} [host:port | host | :port]' '''

  -h, --help       - Show help information
  -v, --version    - Show version string
  -d, --debug      - Dump debug info to server log
  -n, --nobrowser  - Don't start system browser to SymPad page
  -u, --ugly       - Start in draft display style (only on command line)
  -E, --EI         - Start with SymPy constants 'E' and 'I' not 'e' and 'i'
  -q, --quick      - Start in quick input mode
  -y, --nopyS      - Start without Python S escaping
  -s, --simplify   - Start with post-evaluation simplification
  -m, --nomatsimp  - Start without matrix simplification
  -t, --nodoit     - Start without automatic expression doit()
  -N, --noN        - Start without N function
  -S, --noS        - Start without S function
  -O, --noO        - Start without O function
  -b, --nobeta     - Start without beta function
  -g, --nogamma    - Start without gamma function
  -G, --noGamma    - Start without Gamma function
  -L, --noLambda   - Start without Lambda function
  -z, --nozeta     - Start without zeta function
'''

if _SYMPAD_CHILD: # sympy slow to import so don't do it for watcher process as is unnecessary there
	sys.path.insert (0, '') # allow importing from current directory first (for SymPy development version) # AUTO_REMOVE_IN_SINGLE_SCRIPT

	import sympy as sp
	from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
	import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT
	import sparser       # AUTO_REMOVE_IN_SINGLE_SCRIPT
	import spatch        # AUTO_REMOVE_IN_SINGLE_SCRIPT
	import splot         # AUTO_REMOVE_IN_SINGLE_SCRIPT

	_SYS_STDOUT   = sys.stdout
	_DISPLAYSTYLE = [1] # use "\displaystyle{}" formatting in MathJax
	_HISTORY      = []  # persistent history across browser closings

	_PARSER       = sparser.Parser ()
	_ONE_FUNCS    = ('N', 'O', 'S', 'beta', 'gamma', 'Gamma', 'Lambda', 'zeta')

	_START_ENV    = OrderedDict ([('EI', False), ('quick', False), ('pyS', True), ('simplify', False), ('matsimp', True), ('doit', True),
		('N', True), ('O', True), ('S', True), ('beta', True), ('gamma', True), ('Gamma', True), ('Lambda', True), ('zeta', True)])

	_ENV          = _START_ENV.copy () # This is individual session STATE! Threading can corrupt this! It is GLOBAL to survive multiple Handlers.
	_VARS         = {'_': AST.Zero} # This also!
	_UFUNCS2VARS  = {} # Yup...

#...............................................................................................
def _admin_vars (*args):
	asts = _sorted_vars ()

	if not asts:
		return 'No variables defined.'

	return asts

def _admin_del (*args):
	vars = OrderedDict ()
	msgs = []

	for arg in args:
		var = arg.as_identifier

		if var is None or var == '_':
			raise TypeError (f'invalid argument {sym.ast2nat (arg)!r}')

		vars [var] = _VARS.get (var)

		if vars [var] is None:
			raise AE35UnitError (f'Variable {var!r} is not defined, it can only be attributable to human error.')

	for var, ast in vars.items ():
		msgs.append (f'{"Lambda function" if ast.is_lamb else "Undefined function" if ast.is_ufunc else "Variable"} {var!r} deleted.')

		del _VARS [var]

	_vars_updated ()

	if not msgs:
		msgs.append ('No variables specified!')

	return msgs

def _admin_delall (*args):
	last_var    = _VARS ['_']
	_VARS.clear ()
	_VARS ['_'] = last_var
	_vars_updated ()

	return 'All variables deleted.'

def _admin_env (*args):
	def _envop (env, apply):
		msgs = []

		for var, state in env.items ():
			if apply:
				_ENV [var] = state

			if var == 'EI':
				msgs.append (f'Uppercase E and I is {"on" if state else "off"}.')

				if apply:
					AST.EI (state)

					for var in (AST.E.var, AST.I.var):
						if var in _VARS:
							del _VARS [var]

			elif var == 'quick':
				msgs.append (f'Quick input mode is {"on" if state else "off"}.')

				if apply:
					_PARSER.set_quick (state)

			elif var == 'pyS':
				msgs.append (f'Python S escaping {"on" if state else "off"}.')

				if apply:
					sym.set_pyS (state)

			elif var == 'simplify':
				msgs.append (f'Post-evaluation simplify is {"on" if state else "off"}.')

				if apply:
					sym.set_simplify (state)

			elif var == 'matsimp':
				msgs.append (f'Matrix simplify is {"broken" if not spatch.SPATCHED else "on" if state else "off"}.')

				if apply:
					spatch.set_matmulsimp (state)

			elif var == 'doit':
				msgs.append (f'Expression doit is {"on" if state else "off"}.')

				if apply:
					sym.set_doit (state)

			elif var in _ONE_FUNCS:
				msgs.append (f'Function {var} is {"on" if state else "off"}.')

				if apply:
					_vars_updated ()

		return msgs

	# start here
	if not args:
		return _envop (_ENV, False)

	env = OrderedDict ()

	for arg in args:
		if arg.is_ass:
			var = arg.lhs.as_identifier

			if var:
				state = bool (sym.ast2spt (arg.rhs))

		else:
			var = arg.as_identifier

			if var:
				if var [:2] == 'no':
					var, state = var [2:], False
				else:
					state = True

		if var is None:
			raise TypeError (f'invalid argument {sym.ast2nat (arg)!r}')
		elif var not in {'EI', 'quick', 'pyS', 'simplify', 'matsimp', 'doit', *_ONE_FUNCS}:
			raise NameError (f'invalid environment setting {var!r}')

		env [var] = state

	return _envop (env, True)

def _admin_envreset (*args):
	return ['Environment has been reset.'] + _admin_env (*(AST ('@', var if state else f'no{var}') for var, state in _START_ENV.items ()))

#...............................................................................................
class RealityRedefinitionError (NameError):	pass
class CircularReferenceError (RecursionError): pass
class AE35UnitError (Exception): pass

def _present_vars (vars):
	asts = []

	for v, e in vars:
		if v != '_':
			if e.is_lamb:
 				asts.append (AST ('=', ('-ufunc', v, tuple (('@', vv) for vv in e.vars)), e.lamb))
			else:
				asts.append (AST ('=', ('@', v), e))

	return asts

def _sorted_vars ():
	return _present_vars (sorted (_VARS.items (), key = lambda kv: (kv [1].op not in {'-lamb', '-ufunc'}, kv [0])))

def _vars_updated ():
	_UFUNCS2VARS.clear ()

	one_funcs  = set (f for f in filter (lambda f: _ENV.get (f), _ONE_FUNCS))
	user_funcs = one_funcs.copy ()

	for var, ast in _VARS.items ():
		if ast.is_ufunc:
			_UFUNCS2VARS [ast] = AST ('@', var)
		elif ast.is_lamb:
			user_funcs.add (var)

	sparser.set_sp_user_funcs (user_funcs)
	sparser.set_sp_user_vars (_VARS)
	sym.set_sym_user_funcs (user_funcs)
	sym.set_sym_user_vars (_VARS)

def _prepare_ass (ast): # check and prepare for simple or tuple assignment
	if not ast.ass_validate:
		vars = None
	elif ast.ass_validate.error:
		raise RealityRedefinitionError (ast.ass_validate.error)

	else:
		vars, ast = ast.ass_validate.lhs, ast.ass_validate.rhs
		vars      = list (vars.comma) if vars.is_comma else [vars]

	return AST.apply_vars (ast, _VARS), vars

def _execute_ass (ast, vars): # execute assignment if it was detected
	def set_vars (vars):
		vars = dict ((v.var, a) for v, a in vars.items ())

		try: # check for circular references
			AST.apply_vars (AST (',', tuple (('@', v) for v in vars)), {**_VARS, **vars})
		except RecursionError:
			raise CircularReferenceError ("I'm sorry, Dave. I'm afraid I can't do that.") from None

		_VARS.update (vars)

	if not vars: # no assignment
		_VARS ['_'] = ast

		_vars_updated ()

		return [ast]

	if len (vars) == 1: # simple assignment
		set_vars ({vars [0]: ast})

		vars = ((vars [0].var, ast),)

	else: # tuple assignment
		ast = ast.strip_paren

		if ast.op in {',', '[', '-set'}:
			asts = ast [1]

		else:
			asts = []
			itr  = iter (sym.ast2spt (ast))

			for i in range (len (vars) + 1):
				try:
					ast = sym.spt2ast (next (itr))
				except StopIteration:
					break

				if vars [i].is_ufunc:
					asts.append (AST.Ass.ufunc2lamb (vars [i], ast))

					vars [i] = AST ('@', vars [i].ufunc)

				else:
					asts.append (ast)

		if len (vars) < len (asts):
			raise ValueError (f'too many values to unpack (expected {len (vars)})')
		elif len (vars) > len (asts):
			raise ValueError (f'not enough values to unpack (expected {len (vars)}, got {len (asts)})')

		set_vars (dict (zip (vars, asts)))

		vars = tuple (zip ((v.var for v in vars), asts))

	_vars_updated ()

	return _present_vars (vars)

#...............................................................................................
class Handler (SimpleHTTPRequestHandler):
	def vars (self, request):
		asts = _sorted_vars ()

		return {'vars': [{
			'tex': sym.ast2tex (ast),
			'nat': sym.ast2nat (ast),
			'py' : sym.ast2py (ast),
			} for ast in asts]}

	def validate (self, request):
		ast, erridx, autocomplete = _PARSER.parse (request ['text'])
		tex = nat = py            = None

		if ast is not None:
			tex = sym.ast2tex (ast)
			nat = sym.ast2nat (ast)
			py  = sym.ast2py (ast)

			if os.environ.get ('SYMPAD_DEBUG'):
				print ('ast:', ast, file = sys.stderr)
				print ('tex:', tex, file = sys.stderr)
				print ('nat:', nat, file = sys.stderr)
				print ('py: ', py, file = sys.stderr)
				print (file = sys.stderr)

		return {
			'tex'         : tex,
			'nat'         : nat,
			'py'          : py,
			'erridx'      : erridx,
			'autocomplete': autocomplete,
		}

	def evaluate (self, request):
		def evalexpr (ast):
			sym.ast2spt.set_precision (ast)

			if ast.is_func and ast.func in AST.Func.PLOT: # plotting?
				args, kw = AST.args2kwargs (AST.apply_vars (ast.args, _VARS), sym.ast2spt)
				ret      = getattr (splot, ast.func) (*args, **kw)

				return {'msg': ['Plotting not available because matplotlib is not installed.']} if ret is None else {'img': ret}

			elif ast.is_func and ast.func in AST.Func.ADMIN: # special admin function?
				asts = globals () [f'_admin_{ast.func}'] (*ast.args)

				if isinstance (asts, str):
					return {'msg': [asts]}
				elif isinstance (asts, list) and isinstance (asts [0], str):
					return {'msg': asts}

			else: # not admin function, normal evaluation
				ast, vars = _prepare_ass (ast)

				spt = sym.ast2spt (ast) # , _VARS)
				ast = sym.spt2ast (spt)

				if os.environ.get ('SYMPAD_DEBUG'):
					import sympy as sp

					print ('spt:        ', repr (spt), file = sys.stderr)
					print ('spt type:   ', type (spt), file = sys.stderr)

					try:
						print ('spt args:   ', repr (spt.args), file = sys.stderr)
					except:
						pass

					print ('sympy latex:', sp.latex (spt), file = sys.stderr)
					print ('ast:        ', ast, file = sys.stderr)
					print (file = sys.stderr)

				asts = _execute_ass (ast, vars)

			response = {}

			if asts and asts [0] != AST.None_:
				response.update ({'math': [{
					'tex': sym.ast2tex (ast),
					'nat': sym.ast2nat (ast),
					'py' : sym.ast2py (ast),
					} for ast in asts]})

			return response

		# start here
		responses = []

		try:
			_HISTORY.append (request ['text'])

			ast, _, _ = _PARSER.parse (request ['text'])

			if ast:
				for ast in (ast.scolon if ast.is_scolon else (ast,)):
					sys.stdout = io.StringIO ()
					response   = evalexpr (ast)

					if sys.stdout.tell ():
						responses.append ({'msg': sys.stdout.getvalue ().strip ().split ('\n')})

					responses.append (response)

		except Exception:
			if sys.stdout is not _SYS_STDOUT and sys.stdout.tell ():
				responses.append ({'msg': sys.stdout.getvalue ().strip ().split ('\n')})

			responses.append ({'err': ''.join (traceback.format_exception (*sys.exc_info ())).strip ().split ('\n')})

		finally:
			sys.stdout = _SYS_STDOUT

		return {'data': responses} if responses else {}

	def do_GET (self):
		if self.path == '/':
			self.path = '/index.html'

		fnm = os.path.join (_SYMPAD_PATH, self.path.lstrip ('/'))

		if self.path != '/env.js' and (self.path not in _STATIC_FILES or (not _RUNNING_AS_SINGLE_SCRIPT and not os.path.isfile (fnm))):
			self.send_error (404, f'Invalid path {self.path!r}')

		else:
			self.send_response (200)

			if self.path == '/env.js':
				content = 'text/javascript'
				data    = f'History = {_HISTORY}\nHistIdx = {len (_HISTORY)}\nVersion = {_VERSION!r}\nSymPyVersion = {sp.__version__!r}\nDisplayStyle = {_DISPLAYSTYLE [0]}'.encode ('utf8')

				self.send_header ('Cache-Control', 'no-store')

			else:
				content = _STATIC_FILES [self.path]

				if _RUNNING_AS_SINGLE_SCRIPT:
					data = _FILES [self.path [1:]]
				else:
					data = open (fnm, 'rb').read ()

			self.send_header ('Content-type', f'{content}')
			self.end_headers ()
			self.wfile.write (data)

	def do_POST (self):
		request = parse_qs (self.rfile.read (int (self.headers ['Content-Length'])).decode ('utf8'), keep_blank_values = True)

		for key, val in list (request.items ()):
			if isinstance (val, list) and len (val) == 1:
				request [key] = val [0]

		if request ['mode'] == 'vars':
			response = self.vars (request)

		else:
			if request ['mode'] == 'validate':
				response = self.validate (request)
			else: # if request ['mode'] == 'evaluate':
				response = {**self.evaluate (request), **self.vars (request)}

			response ['idx']  = request ['idx']
			response ['text'] = request ['text']

		response ['mode'] = request ['mode']

		self.send_response (200)
		self.send_header ('Content-type', 'application/json')
		self.send_header ('Cache-Control', 'no-store')
		self.end_headers ()
		self.wfile.write (json.dumps (response).encode ('utf8'))
		# self.wfile.write (json.dumps ({**request, **response}).encode ('utf8'))

#...............................................................................................
def start_server (logging = True):
	if not logging:
		Handler.log_message = lambda *args, **kwargs: None

	if ('--ugly', '') in __OPTS or ('-u', '') in __OPTS:
		_DISPLAYSTYLE [0] = 0

	# make sure all env options are initialized according to command line options
	for short, long in zip ('EqysmtNOSbgGLz', \
			['EI', 'quick', 'nopyS', 'simplify', 'nomatsimp', 'nodoit', 'noN', 'noO', 'noS', 'nobeta', 'nogamma', 'noGamma', 'noLambda', 'nozeta']):
		if (f'--{long}', '') in __OPTS or (f'-{short}', '') in __OPTS:
			_admin_env (AST ('@', long))
		else:
			_admin_env (AST ('@', long [2:] if long [:2] == 'no' else f'no{long}'))

	_START_ENV.update (_ENV)

	if not __ARGV:
		host, port = _DEFAULT_ADDRESS
	else:
		host, port = (re.split (r'(?<=\]):' if __ARGV [0].startswith ('[') else ':', __ARGV [0]) + [_DEFAULT_ADDRESS [1]]) [:2]
		host, port = host.strip ('[]'), int (port)

	try:
		httpd  = HTTPServer ((host, port), Handler)
		thread = threading.Thread (target = httpd.serve_forever, daemon = True)

		thread.start ()

		return httpd

	except OSError as e:
		if e.errno != 98:
			raise

		print (f'Port {port} seems to be in use, try specifying different port as a command line parameter, e.g. localhost:9001')

		sys.exit (-1)

_MONTH_NAME = (None, 'Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec')

def child ():
	httpd = start_server ()

	def log_message (msg):
		y, m, d, hh, mm, ss, _, _, _ = time.localtime (time.time ())

		sys.stderr.write (f'{httpd.server_address [0]} - - ' \
				f'[{"%02d/%3s/%04d %02d:%02d:%02d" % (d, _MONTH_NAME [m], y, hh, mm, ss)}] {msg}\n')

	fnms    = (_SYMPAD_NAME,) if _RUNNING_AS_SINGLE_SCRIPT else (_SYMPAD_NAME, 'splot.py', 'spatch.py', 'sparser.py', 'sym.py', 'sxlat.py', 'sast.py', 'lalr1.py')
	watch   = [os.path.join (_SYMPAD_PATH, fnm) for fnm in fnms]
	tstamps = [os.stat (fnm).st_mtime for fnm in watch]

	if _SYMPAD_FIRSTRUN:
		print (f'SymPad v{_VERSION} server running. If a browser window does not automatically open to the address below then try navigating to that URL manually.\n')

	log_message (f'Serving at http://{httpd.server_address [0]}:{httpd.server_address [1]}/')

	if _SYMPAD_FIRSTRUN and ('--nobrowser', '') not in __OPTS and ('-n', '') not in __OPTS:
		webbrowser.open (f'http://{httpd.server_address [0] if httpd.server_address [0] != "0.0.0.0" else "127.0.0.1"}:{httpd.server_address [1]}')

	try:
		while 1:
			time.sleep (0.5)

			if [os.stat (fnm).st_mtime for fnm in watch] != tstamps:
				log_message ('Files changed, restarting...')
				sys.exit (0)

	except KeyboardInterrupt:
		sys.exit (0)

	sys.exit (-1)

def parent ():
	if ('--help', '') in __OPTS or ('-h', '') in __OPTS:
		print (_HELP.lstrip ())
		sys.exit (0)

	if ('--version', '') in __OPTS or ('-v', '') in __OPTS:
		print (_VERSION)
		sys.exit (0)

	base      = [sys.executable] + sys.argv [:1] + ['--child']
	opts      = [o [0] for o in __OPTS]
	first_run = ['--firstrun']

	try:
		while 1:
			ret       = subprocess.run (base + opts + first_run + __ARGV)
			first_run = []

			if ret.returncode != 0 and not os.environ.get ('SYMPAD_DEBUG'):
				sys.exit (0)

	except KeyboardInterrupt:
		sys.exit (0)

#...............................................................................................
# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: # DEBUG!
# 	Handler.__init__ = lambda self: None

# 	h = Handler ()

# 	print (h.evaluate ({'text': 'f = lambda: @y'}))

# 	sys.exit (0)

if __name__ == '__main__':
	if ('--debug', '') in __OPTS or ('-d', '') in __OPTS:
		os.environ ['SYMPAD_DEBUG'] = '1'

	if _SYMPAD_CHILD:
		child ()
	else:
		parent ()
