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

_VERSION         = '1.1.3'

_ONE_FUNCS       = {'N', 'O', 'S', 'beta', 'gamma', 'Gamma', 'Lambda', 'zeta'}
_ENV_OPTS        = {'EI', 'quick', 'pyS', 'simplify', 'matsimp', 'ufuncmap', 'prodrat', 'doit', 'strict', *_ONE_FUNCS}
_ENV_OPTS_ALL    = _ENV_OPTS.union (f'no{opt}' for opt in _ENV_OPTS)

__OPTS, __ARGV   = getopt.getopt (sys.argv [1:], 'hvnudr', ['child', 'firstrun', 'help', 'version', 'nobrowser', 'ugly', 'debug', 'restert', *_ENV_OPTS_ALL])
__IS_MAIN        = __name__ == '__main__'
__IS_MODULE_RUN  = sys.argv [0] == '-m'

_SERVER_DEBUG    = __IS_MAIN and __ARGV and __ARGV [0] == 'server-debug'

_SYMPAD_PATH     = os.path.dirname (sys.argv [0])
_SYMPAD_NAME     = os.path.basename (sys.argv [0])
_SYMPAD_RESTART  = not __IS_MODULE_RUN and (('-r', '') in __OPTS or ('--restart', '') in __OPTS)
_SYMPAD_CHILD    = not _SYMPAD_RESTART or ('--child', '') in __OPTS
_SYMPAD_FIRSTRUN = not _SYMPAD_RESTART or ('--firstrun', '') in __OPTS
_SYMPAD_DEBUG    = os.environ.get ('SYMPAD_DEBUG')

_DEFAULT_ADDRESS = ('localhost', 9000)
_FILES           = {} # pylint food # AUTO_REMOVE_IN_SINGLE_SCRIPT
_STATIC_FILES    = {'/style.css': 'text/css', '/script.js': 'text/javascript', '/index.html': 'text/html',
	'/help.html': 'text/html', '/bg.png': 'image/png', '/wait.webp': 'image/webp'}

_HELP            = f'usage: sympad [options] [host:port | host | :port]' '''

  -h, --help               - Show help information
  -v, --version            - Show version string
  -n, --nobrowser          - Don't start system browser to SymPad page
  -u, --ugly               - Start in draft display style (only on command line)
  -d, --debug              - Dump debug info to server log
  -r, --restart            - Restart server on source file changes (for development)
  --EI, --noEI             - Start with SymPy constants 'E' and 'I' or regular 'e' and 'i'
  --quick, --noquick       - Start in/not quick input mode
  --pyS, --nopyS           - Start with/out Python S escaping
  --simplify, --nosimplify - Start with/out post-evaluation simplification
  --matsimp, --nomatsimp   - Start with/out matrix simplification
  --ufuncmap, --noufuncmap - Start with/out undefined function mapping back to variables
  --prodrat, --noprodrat   - Start with/out separate product leading rational
  --doit, --nodoit         - Start with/out automatic expression doit()
  --strict, --nostrict     - Start with/out strict LaTeX formatting
  --N, --noN               - Start with/out N function
  --S, --noS               - Start with/out S function
  --O, --noO               - Start with/out O function
  --beta, --nobeta         - Start with/out beta function
  --gamma, --nogamma       - Start with/out gamma function
  --Gamma, --noGamma       - Start with/out Gamma function
  --Lambda, --noLambda     - Start with/out Lambda function
  --zeta, --nozeta         - Start with/out zeta function
'''.lstrip ()

if _SYMPAD_CHILD: # sympy slow to import so don't do it for watcher process as is unnecessary there
	sys.path.insert (0, '') # allow importing from current directory first (for SymPy development version) # AUTO_REMOVE_IN_SINGLE_SCRIPT

	import sympy as sp
	import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
	from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
	import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT
	import sparser       # AUTO_REMOVE_IN_SINGLE_SCRIPT
	import spatch        # AUTO_REMOVE_IN_SINGLE_SCRIPT
	import splot         # AUTO_REMOVE_IN_SINGLE_SCRIPT

	_SYS_STDOUT    = sys.stdout
	_DISPLAYSTYLE  = [1] # use "\displaystyle{}" formatting in MathJax
	_HISTORY       = []  # persistent history across browser closings

	_UFUNC_MAPBACK = True # map undefined functions from SymPy back to variables if possible
	_UFUNC_MAP     = {} # map of ufunc asts to ordered sequence of variable names
	_SYM_MAP       = {} # map of sym asts to ordered sequence of variable names
	_SYM_VARS      = set () # set of all variables mapped to symbols

	_PARSER        = sparser.Parser ()
	_START_ENV     = OrderedDict ([
		('EI', False), ('quick', False), ('pyS', True), ('simplify', False), ('matsimp', True), ('ufuncmap', True), ('prodrat', False), ('doit', True), ('strict', False),
		('N', True), ('O', True), ('S', True), ('beta', True), ('gamma', True), ('Gamma', True), ('Lambda', True), ('zeta', True)])

	_ENV           = _START_ENV.copy () # This is individual session STATE! Threading can corrupt this! It is GLOBAL to survive multiple Handlers.
	_VARS          = {'_': AST.Zero} # This also!

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
	vars_updated = False

	def _envop (env, apply):
		nonlocal vars_updated

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
					sym.set_quick (state)
					_PARSER.set_quick (state)

					vars_updated = True

			elif var == 'pyS':
				msgs.append (f'Python S escaping is {"on" if state else "off"}.')

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

			elif var == 'ufuncmap':
				msgs.append (f'Undefined function map to variable is {"on" if state else "off"}.')

				if apply:
					global _UFUNC_MAPBACK
					_UFUNC_MAPBACK = state

			elif var == 'prodrat':
				msgs.append (f'Leading product rational is {"on" if state else "off"}.')

				if apply:
					sym.set_prodrat (state)

			elif var == 'doit':
				msgs.append (f'Expression doit is {"on" if state else "off"}.')

				if apply:
					sym.set_doit (state)

			elif var == 'strict':
				msgs.append (f'Strict LaTeX formatting is {"on" if state else "off"}.')

				if apply:
					sym.set_strict (state)

			elif var in _ONE_FUNCS:
				msgs.append (f'Function {var} is {"on" if state else "off"}.')

				if apply:
					vars_updated = True

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
		elif var not in _ENV_OPTS:
			raise NameError (f'invalid environment setting {var!r}')

		env [var] = state

	ret = _envop (env, True)

	if vars_updated:
		_vars_updated ()

	return ret

def _admin_envreset (*args):
	return ['Environment has been reset.<br><br>'] + _admin_env (*(AST ('@', var if state else f'no{var}') for var, state in _START_ENV.items ()))

#...............................................................................................
class RealityRedefinitionError (NameError):	pass
class CircularReferenceError (RecursionError): pass
class AE35UnitError (Exception): pass

def _mapback (ast, assvar = None, exclude = set ()): # map back ufuncs and symbols to the variables they are assigned to if possible
	if not isinstance (ast, AST):
		return ast

	if ast.is_var:
		if ast.var not in _SYM_VARS:
			return ast

		if ast.var == assvar:
			raise CircularReferenceError ('trying to assign unqualified symbol to variable of the same name')

		return AST ('-sym', ast.var)

	if ast.is_sym:
		vars = _SYM_MAP.get (ast)

		if not vars:
			return ast

		if ast.sym in vars:
			return AST ('@', ast.sym)

		return AST ('@', next (iter (vars)))

	if _UFUNC_MAPBACK:
		if ast.is_ass and ast.lhs.is_ufunc:
			return AST ('=', ast.lhs, _mapback (ast.rhs, assvar, exclude))
		elif not ast.is_ufunc:
			return AST (*(_mapback (a, assvar, exclude) for a in ast))

		vars = _UFUNC_MAP.get (ast)

		if vars: # prevent mapping to self on assignment
			if ast.ufunc in vars and ast.ufunc not in exclude:
				return AST ('@', ast.ufunc)

			for var in vars:
				if var not in exclude:
					return AST ('@', var)

	return AST (*(_mapback (a, assvar, exclude) for a in ast))

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
	one_funcs  = set (f for f in filter (lambda f: _ENV.get (f), _ONE_FUNCS)) # hidden functions for stuff like N and gamma
	user_funcs = one_funcs.copy ()

	for var, ast in _VARS.items ():
		if ast.is_lamb:
			user_funcs.add (var)

	vars = {v: AST.apply_vars (a, _VARS, mode = False) for v, a in _VARS.items ()} # flattened vars so sym and sparser don't need to do apply_vars()

	sym.set_sym_user_funcs (user_funcs)
	sym.set_sym_user_vars (vars)
	sparser.set_sp_user_funcs (user_funcs)
	sparser.set_sp_user_vars (vars)

	_UFUNC_MAP.clear ()
	_SYM_MAP.clear ()
	_SYM_VARS.clear ()

	for v, a in vars.items (): # build ufunc and sym mapback dict
		if v != '_':
			if a.is_ufunc:
				_UFUNC_MAP.setdefault (a, set ()).add (v)

			elif a.is_sym:
				_SYM_MAP.setdefault (a, set ()).add (v)
				_SYM_VARS.add (v)

def _prepare_ass (ast): # check and prepare for simple or tuple assignment
	if not ast.ass_valid:
		vars = None
	elif ast.ass_valid.error:
		raise RealityRedefinitionError (ast.ass_valid.error)

	else:
		vars, ast = ast.ass_valid.lhs, ast.ass_valid.rhs
		vars      = list (vars.comma) if vars.is_comma else [vars]

	return AST.apply_vars (ast, _VARS), vars

def _execute_ass (ast, vars): # execute assignment if it was detected
	def set_vars (vars):
		nvars = {}

		for v, a in vars.items ():
			v = v.var

			if a.is_ufunc_anonymous:
				a = AST (a.op, v, *a [2:])

			elif a.is_sym_anonymous:
				if a.is_sym_unqualified:
					raise CircularReferenceError ('cannot asign unqualified anonymous symbol')

				a = AST (a.op, v, *a [2:])

			nvars [v] = a

		try: # check for circular references
			AST.apply_vars (AST (',', tuple (('@', v) for v in nvars)), {**_VARS, **nvars})
		except RecursionError:
			raise CircularReferenceError ("I'm sorry, Dave. I'm afraid I can't do that.") from None

		_VARS.update (nvars)

		return list (nvars.items ())

	# start here
	if not vars: # no assignment
		if not ast.is_ufunc:
			ast = _mapback (ast)

		_VARS ['_'] = ast

		_vars_updated ()

		return [ast]

	if len (vars) == 1: # simple assignment
		if ast.op not in {'-ufunc', '-sym'}:
			ast = _mapback (ast, vars [0].var, {vars [0].var})

		vars = set_vars ({vars [0]: ast})

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

				if vars [i].is_ufunc_named:
					asts.append (AST.Ass.ufunc2lamb (vars [i], ast))

					vars [i] = AST ('@', vars [i].ufunc)

				else:
					asts.append (ast)

		if len (vars) < len (asts):
			raise ValueError (f'too many values to unpack (expected {len (vars)})')
		elif len (vars) > len (asts):
			raise ValueError (f'not enough values to unpack (expected {len (vars)}, got {len (asts)})')

		vasts   = list (zip (vars, asts))
		exclude = set (va [0].var for va in filter (lambda va: va [1].is_ufunc, vasts))
		asts    = [a if a.op in {'-ufunc', '-sym'} else _mapback (a, v.var, exclude) for v, a in vasts]
		vars    = set_vars (dict (zip (vars, asts)))

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
		ast, erridx, autocomplete, error = _PARSER.parse (request ['text'])
		tex = nat = py                   = None

		if ast is not None:
			tex, xlattex = sym.ast2tex (ast, retxlat = True)
			nat, xlatnat = sym.ast2nat (ast, retxlat = True)
			py, xlatpy  = sym.ast2py (ast, retxlat = True)

			if _SYMPAD_DEBUG:
				print ('free:', list (v.var for v in ast.free_vars), file = sys.stderr)
				print ('ast: ', ast, file = sys.stderr)

				if xlattex:
					print ('astt:', repr (xlattex), file = sys.stderr)

				if xlatnat:
					print ('astn:', repr (xlatnat), file = sys.stderr)

				if xlatpy:
					print ('astp:', repr (xlatpy), file = sys.stderr)

				print ('tex: ', tex, file = sys.stderr)
				print ('nat: ', nat, file = sys.stderr)
				print ('py:  ', py, file = sys.stderr)
				print (file = sys.stderr)

		if isinstance (error, Exception):
			error = (f'{error.__class__.__name__}: ' if not isinstance (error, SyntaxError) else '') + error.args [0].replace ('\n', ' ').strip ()

		return {
			'tex'         : tex,
			'nat'         : nat,
			'py'          : py,
			'erridx'      : erridx,
			'autocomplete': autocomplete,
			'error'       : error,
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

				if _SYMPAD_DEBUG:
					print ('ast:       ', ast, file = sys.stderr)

				try:
					spt, xlat = sym.ast2spt (ast, retxlat = True) # , _VARS)

					if _SYMPAD_DEBUG and xlat:
						print ('xlat:      ', xlat, file = sys.stderr)

					sptast = sym.spt2ast (spt)

				except:
					if _SYMPAD_DEBUG:
						print (file = sys.stderr)

					raise

				if _SYMPAD_DEBUG:
					try:
						print ('spt:       ', repr (spt), file = sys.stderr)
					except:
						pass

					print ('spt type:  ', type (spt), file = sys.stderr)

					try:
						print ('spt args:  ', repr (spt.args), file = sys.stderr)
					except:
						pass

					print ('spt latex: ', sp.latex (spt), file = sys.stderr)
					print ('spt ast:   ', sptast, file = sys.stderr)
					print ('spt tex:   ', sym.ast2tex (sptast), file = sys.stderr)
					print ('spt nat:   ', sym.ast2nat (sptast), file = sys.stderr)
					print ('spt py:    ', sym.ast2py (sptast), file = sys.stderr)
					print (file = sys.stderr)

				asts = _execute_ass (sptast, vars)

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

			ast, _, _, _ = _PARSER.parse (request ['text'])

			if ast:
				for ast in (ast.scolon if ast.is_scolon else (ast,)):
					sys.stdout = _SYS_STDOUT if _SERVER_DEBUG else io.StringIO ()
					response   = evalexpr (ast)

					if sys.stdout.tell ():
						responses.append ({'msg': sys.stdout.getvalue ().strip ().split ('\n')})

					responses.append (response)

		except Exception:
			if sys.stdout is not _SYS_STDOUT and sys.stdout.tell (): # flush any printed messages before exception
				responses.append ({'msg': sys.stdout.getvalue ().strip ().split ('\n')})

			etype, exc, tb = sys.exc_info ()

			if exc.args and isinstance (exc.args [0], str):
				exc = etype (exc.args [0].replace ('\n', ' ').strip (), *exc.args [1:]).with_traceback (tb) # reformat text to remove newlines

			responses.append ({'err': ''.join (traceback.format_exception (etype, exc, tb)).strip ().split ('\n')})

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

	for opt, _ in __OPTS:
		opt = opt.lstrip ('-')

		if opt in _ENV_OPTS_ALL:
			_admin_env (AST ('@', opt))

	_START_ENV.update (_ENV)
	_vars_updated ()

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
	def log_message (msg):
		y, m, d, hh, mm, ss, _, _, _ = time.localtime (time.time ())

		sys.stderr.write (f'{httpd.server_address [0]} - - ' \
				f'[{"%02d/%3s/%04d %02d:%02d:%02d" % (d, _MONTH_NAME [m], y, hh, mm, ss)}] {msg}\n')

	# start here
	httpd = start_server ()

	if _SYMPAD_FIRSTRUN and ('--nobrowser', '') not in __OPTS and ('-n', '') not in __OPTS:
		webbrowser.open (f'http://{httpd.server_address [0] if httpd.server_address [0] != "0.0.0.0" else "127.0.0.1"}:{httpd.server_address [1]}')

	if _SYMPAD_FIRSTRUN:
		print (f'SymPad v{_VERSION} server running. If a browser window does not automatically open to the address below then try navigating to that URL manually.\n')

	log_message (f'Serving at http://{httpd.server_address [0]}:{httpd.server_address [1]}/')

	if not _SYMPAD_RESTART:
		try:
			while 1:
				time.sleep (0.5) # thread.join () doesn't catch KeyboardInterupt on Windows

		except KeyboardInterrupt:
			sys.exit (0)

	else:
		fnms    = (_SYMPAD_NAME,) if _RUNNING_AS_SINGLE_SCRIPT else (_SYMPAD_NAME, 'splot.py', 'spatch.py', 'sparser.py', 'sym.py', 'sxlat.py', 'sast.py', 'lalr1.py')
		watch   = [os.path.join (_SYMPAD_PATH, fnm) for fnm in fnms]
		tstamps = [os.stat (fnm).st_mtime for fnm in watch]

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
	if not _SYMPAD_RESTART or __IS_MODULE_RUN:
		child () # does not return

	# continue as parent process and wait for child process to return due to file changes and restart it
	base      = [sys.executable] + sys.argv [:1] + ['--child'] # (['--child'] if __IS_MAIN else ['sympad', '--child'])
	opts      = [o [0] for o in __OPTS]
	first_run = ['--firstrun']

	try:
		while 1:
			ret       = subprocess.run (base + opts + first_run + __ARGV)
			first_run = []

			if ret.returncode != 0 and not _SYMPAD_DEBUG:
				sys.exit (0)

	except KeyboardInterrupt:
		sys.exit (0)

#...............................................................................................
# AUTO_REMOVE_IN_SINGLE_SCRIPT_BLOCK_START
if _SERVER_DEBUG: # DEBUG!
	Handler.__init__ = lambda self: None

	h = Handler ()

	# _VARS ['_'] = AST ('[', (('=', ('-ufunc', 'x', (('@', 't'),)), ('*', (('+', (('@', 'C1'), ('*', (('#', '8'), ('@', 'C2'), ('-intg', ('/', ('^', ('@', 'e'), ('/', ('*', (('#', '19'), ('^', ('@', 't'), ('#', '2')))), ('#', '2'))), ('^', ('-ufunc', 'x0', (('@', 't'),)), ('#', '2'))), ('@', 'dt')))))), ('-ufunc', 'x0', (('@', 't'),))))), ('=', ('-ufunc', 'y', (('@', 't'),)), ('+', (('*', (('@', 'C1'), ('-ufunc', 'y0', (('@', 't'),)))), ('*', (('@', 'C2'), ('+', (('/', ('^', ('@', 'e'), ('/', ('*', (('#', '19'), ('^', ('@', 't'), ('#', '2')))), ('#', '2'))), ('-ufunc', 'x0', (('@', 't'),))), ('*', (('#', '8'), ('-intg', ('/', ('^', ('@', 'e'), ('/', ('*', (('#', '19'), ('^', ('@', 't'), ('#', '2')))), ('#', '2'))), ('^', ('-ufunc', 'x0', (('@', 't'),)), ('#', '2'))), ('@', 'dt')), ('-ufunc', 'y0', (('@', 't'),))), {2}))))))))))
	_VARS ['_'] = AST.Zero

	# print (h.validate ({'text': r'del'}))
	# print (h.evaluate ({'text': r'f = f(x)'}))
	print (h.evaluate ({'text': r'\[[1+i, 1-i], [1-i, 1+i]].rref ()'}))
	# print (h.evaluate ({'text': r'\[[1+i, 1-i], [1-i, 1+i]]*2'}))
	# print (h.evaluate ({'text': r'\[[1+i, 1-i], [1-i, 1+i]].multiply (2)'}))

	sys.exit (0)
# AUTO_REMOVE_IN_SINGLE_SCRIPT_BLOCK_END

def main ():
	if ('--help', '') in __OPTS or ('-h', '') in __OPTS:
		print (_HELP)
		sys.exit (0)

	if ('--version', '') in __OPTS or ('-v', '') in __OPTS:
		print (_VERSION)
		sys.exit (0)

	if ('--debug', '') in __OPTS or ('-d', '') in __OPTS:
		_SYMPAD_DEBUG = os.environ ['SYMPAD_DEBUG'] = '1'

	if _SYMPAD_CHILD:
		child ()
	else:
		parent ()

if __IS_MAIN:
	main ()
