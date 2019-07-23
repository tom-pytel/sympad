#!/usr/bin/env python
# python 3.6+

# TODO: Exception prevents restart on file date change or too much time?

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

from urllib.parse import parse_qs
from socketserver import ThreadingMixIn
from http.server import HTTPServer, SimpleHTTPRequestHandler

_RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT

_SYMPAD_PATH              = os.path.dirname (sys.argv [0])
_SYMPAD_FIRST_RUN         = os.environ.get ('SYMPAD_FIRST_RUN')
_SYMPAD_CHILD             = os.environ.get ('SYMPAD_CHILD')

_DEFAULT_ADDRESS          = ('localhost', 8000)
_STATIC_FILES             = {'/style.css': 'css', '/script.js': 'javascript', '/index.html': 'html', '/help.html': 'html'}
_FILES                    = {} # pylint food # AUTO_REMOVE_IN_SINGLE_SCRIPT

_HELP = f"""
usage: {os.path.basename (sys.argv [0])} [--help | -h] [--debug | -d] [--nobrowser | -n] [--sympyEI | -E] [--quick | -q] [host:port]
"""

if _SYMPAD_CHILD: # sympy slow to import if not precompiled so don't do it for watcher process as is unnecessary there
	sys.path.insert (0, '') # allow importing from current directory first (for SymPy development version)

	import sast          # AUTO_REMOVE_IN_SINGLE_SCRIPT
	from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
	import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT
	import sparser       # AUTO_REMOVE_IN_SINGLE_SCRIPT

	_VAR_LAST   = '_'
	_START_VARS = {
		'beta' : AST ('lamb', ('func', '$beta', (('@', 'x'), ('@', 'y'))), (('@', 'x'), ('@', 'y'))),
		'gamma': AST ('lamb', ('func', '$gamma', (('@', 'z'),)), (('@', 'z'),)),
		'Gamma': AST ('lamb', ('func', '$gamma', (('@', 'z'),)), (('@', 'z'),)),
		'zeta' : AST ('lamb', ('func', '$zeta', (('@', 'z'),)), (('@', 'z'),)),
	}

	_sys_stdout = sys.stdout
	_parser     = sparser.Parser ()

	_vars       = {_VAR_LAST: AST.Zero} # This is individual session STATE! Threading can corrupt this! It is GLOBAL to survive multiple Handlers.
	_history    = [] # persistent history across browser closing

#...............................................................................................
# class ThreadingHTTPServer (ThreadingMixIn, HTTPServer):
# 	pass

class RealityRedefinitionError (NameError):	pass
class CircularReferenceError (RecursionError): pass
class AE35UnitError (Exception): pass

def _ast_remap (ast, map_):
	if not isinstance (ast, AST) or (ast.is_func and ast.func == AST.Func.NOREMAP): # non-AST or stop remap
		return ast

	if ast.is_var and ast.var in map_: # variable
		ast = map_ [ast.var]

		return AST ('func', AST.Func.NOEVAL, (ast,)) if ast.is_lamb else _ast_remap (ast, map_)

	if ast.is_func and ast.func in map_: # user function
		lamb = map_ [ast.func]

		if lamb.is_lamb:
			if len (ast.args) != len (lamb.vars):
				raise TypeError (f"lambda function '{ast.func}()' takes {len (lamb.vars)} argument(s)")

			ast = _ast_remap (lamb.lamb, dict (zip ((v.var for v in lamb.vars), ast.args)))

	if ast.is_lamb: # do not remap lambda owned vars within lambda, they belong to the lambda
		lvars = {v.var for v in ast.vars}
		map_  = {v: a for v, a in filter (lambda va: va [0] not in lvars, map_.items ())}

		return AST (*(_ast_remap (a, map_) if a not in ast.vars else a for a in ast))

	return AST (*(_ast_remap (a, map_) for a in ast))

def _ast_prepare_ass (ast): # check and prepare for simple or tuple assignment
	vars = None

	if ast.is_ass:
		if ast.lhs.is_var: # simple assignment?
			ast, vars = ast.rhs, [ast.lhs.var]

	elif ast.is_comma: # tuple assignment? ('x, y = y, x' comes from parser as ('x', 'y = y', 'x')) so restructure
		lhss = []
		itr  = iter (ast.commas)

		for c in itr:
			if c.is_var:
				lhss.append (c.var)
			elif not c.is_ass or not c.lhs.is_var:
				break

			else:
				t    = (c.rhs,) + tuple (itr)
				ast  = t [0] if len (t) == 1 else AST (',', t)
				vars = lhss + [c.lhs.var]

	if vars:
		for var in vars: # trying to change a fundemental law of the universe?
			if AST ('@', var) in AST.CONSTS:
				raise RealityRedefinitionError ('The only thing that is constant is change - Heraclitus, except for constants, they never change - Me.')

	return _ast_remap (ast, _vars), vars

def _ast_execute_ass (ast, vars): # execute assignment if it was detected
	def _set_vars (vars):
		try: # check for circular references
			_ast_remap (AST (',', tuple (('@', v) for v in vars)), {**_vars, **vars})
		except RecursionError:
			raise CircularReferenceError ("I'm sorry, Dave. I'm afraid I can't do that.") from None

		_vars.update (vars)

	if not vars: # no assignment
		_vars [_VAR_LAST] = ast

		return [ast]

	if len (vars) == 1: # simple assignment
		_set_vars ({vars [0]: ast})

		asts = [AST ('=', '=', ('@', vars [0]), ast)]

	else: # tuple assignment
		ast  = ast.strip_paren ()
		asts = ast.commas if ast.is_comma else tuple (sym.spt2ast (a) for a in sym.ast2spt (ast))

		if len (vars) < len (asts):
			raise ValueError (f'too many values to unpack (expected {len (vars)})')
		if len (vars) > len (asts):
			raise ValueError (f'not enough values to unpack (expected {len (vars)}, got {len (asts)})')

		_set_vars (dict (zip (vars, asts)))

		asts = [AST ('=', '=', ('@', vars [i]), asts [i]) for i in range (len (vars))]

	user_funcs = {va [0] for va in filter (lambda va: va [1].is_lamb, _vars.items ())}

	sym.set_user_funcs (user_funcs)
	_parser.set_user_funcs (user_funcs)

	return asts

def _admin_vars (ast):
	asts = []

	for v, e in sorted (_vars.items ()):
		if v != _VAR_LAST:
			if not e.is_lamb:
				asts.append (AST ('=', '=', ('@', v), e))

	if not asts:
		return 'No variables defined.'

	return asts

def _admin_funcs (ast):
	asts = []

	for v, e in sorted (_vars.items ()):
		if v != _VAR_LAST:
			if e.is_lamb:
				asts.append (AST ('=', '=', ('@', v), e))

	if not asts:
		return 'No functions defined.'

	return asts

def _admin_del (ast):
	var = ast.args [0] if ast.args else AST.VarNull

	try:
		ast = _vars [var.var]

		del _vars [var.var]

	except KeyError:
		raise AE35UnitError (f'Variable {sym.ast2nat (var)!r} is not defined, it can only be attributable to human error.')

	return f'{"Function" if ast.is_lamb else "Variable"} {sym.ast2nat (var)!r} deleted.'

def _admin_delvars (ast):
	for v, e in list (_vars.items ()):
		if not e.is_lamb:# and v != _VAR_LAST:
			del _vars [v]

	return 'All variables deleted.'

def _admin_delall (ast):
	last_var = _vars [_VAR_LAST]

	_vars.clear ()

	_vars [_VAR_LAST] = last_var

	return 'All assignments deleted.'

def _admin_sympyEI (ast):
	sast.sympyEI (bool (sym.ast2spt (ast.args [0])) if ast.args else True)

	if AST.E.var in _vars:
		del _vars [AST.E.var]

	if AST.I.var in _vars:
		del _vars [AST.I.var]

	return f'Constant representation set to {AST.E.var!r} and {AST.I.var!r}.'

def _admin_quick (ast):
	yes = bool (sym.ast2spt (ast.args [0])) if ast.args else True

	_parser.set_quick (yes)

	return f'Quick mode is {"on" if yes else "off"}.'

#...............................................................................................
class Handler (SimpleHTTPRequestHandler):
	def do_GET (self):
		if self.path == '/':
			self.path = '/index.html'

		fnm = os.path.join (_SYMPAD_PATH, self.path.lstrip ('/'))

		if self.path != '/history.js' and (self.path not in _STATIC_FILES or (not _RUNNING_AS_SINGLE_SCRIPT and not os.path.isfile (fnm))):
			self.send_error (404, f'Invalid path {self.path!r}')

		else:
			if self.path == '/history.js':
				content = 'text/javascript'
				data    = f'History = {_history}\nHistIdx = {len (_history)}'.encode ('utf8')

			else:
				content = _STATIC_FILES [self.path]

				if _RUNNING_AS_SINGLE_SCRIPT:
					data = _FILES [self.path [1:]]
				else:
					data = open (fnm, 'rb').read ()

			self.send_response (200)
			self.send_header ('Content-type', f'text/{content}')
			self.end_headers ()
			self.wfile.write (data)

	def do_POST (self):
		request = parse_qs (self.rfile.read (int (self.headers ['Content-Length'])).decode ('utf8'), keep_blank_values = True)

		for key, val in list (request.items ()):
			if isinstance (val, list) and len (val) == 1:
				request [key] = val [0]

		if request ['mode'] == 'validate':
			response = self.validate (request)
		else: # request ['mode'] == 'evaluate':
			response = self.evaluate (request)

		response ['mode'] = request ['mode']
		response ['idx']  = request ['idx']
		response ['text'] = request ['text']

		self.send_response (200)
		self.send_header ("Content-type", "application/json")
		self.end_headers ()
		self.wfile.write (json.dumps (response).encode ('utf8'))
		# self.wfile.write (json.dumps ({**request, **response}).encode ('utf8'))

	def validate (self, request):
		ast, erridx, autocomplete = _parser.parse (request ['text'])
		tex = nat = py            = None

		if ast is not None:
			ast = _ast_remap (ast, {_VAR_LAST: _vars [_VAR_LAST]}) # just remap last evaluated _
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
		try:
			_history.append (request ['text'])

			sys.stdout = io.StringIO ()
			ast, _, _  = _parser.parse (request ['text'])

			if ast.is_func and ast.func in AST.Func.ADMIN: # special admin function?
				asts = globals () [f'_admin_{ast.func}'] (ast)

				if isinstance (asts, str):
					return {'msg': [asts]}

			else: # not admin function, normal evaluation
				ast, vars = _ast_prepare_ass (ast)

				sym.set_precision (ast)

				spt = sym.ast2spt (ast)
				ast = sym.spt2ast (spt)

				if os.environ.get ('SYMPAD_DEBUG'):
					import sympy as sp

					print ('spt:        ', repr (spt), file = sys.stderr)
					print ('spt type:   ', type (spt), file = sys.stderr)
					print ('sympy latex:', sp.latex (spt), file = sys.stderr)
					print ('ast:        ', ast, file = sys.stderr)
					print (file = sys.stderr)

				asts = _ast_execute_ass (ast, vars)

			response = {}

			if asts and asts [0] is not AST.None_:
				response.update ({'math': [{
					'tex': sym.ast2tex (ast),
					'nat': sym.ast2nat (ast),
					'py' : sym.ast2py (ast),
				} for ast in asts]})

			if sys.stdout.tell ():
				sys.stdout.seek (0)

				response ['msg'] = sys.stdout.read ().strip ().split ('\n')

			return response

		except Exception:
			return {'err': ''.join (traceback.format_exception (*sys.exc_info ())).strip ().split ('\n')}

		finally:
			sys.stdout = _sys_stdout

#...............................................................................................
_month_name = (None, 'Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec')

if __name__ == '__main__':
	try:
		opts, argv = getopt.getopt (sys.argv [1:], 'hdnEq', ['help', 'debug', 'nobrowser', 'sympyEI', 'quick'])

		if ('--help', '') in opts or ('-h', '') in opts:
			print (_HELP.strip ())
			sys.exit (0)

		if ('--debug', '') in opts or ('-d', '') in opts:
			os.environ ['SYMPAD_DEBUG'] = '1'

		if not _SYMPAD_CHILD: # watcher parent
			args      = [sys.executable] + sys.argv
			first_run = '1'

			while 1:
				ret       = subprocess.run (args, env = {**os.environ, 'SYMPAD_CHILD': '1', 'SYMPAD_FIRST_RUN': first_run})
				first_run = ''

				if ret.returncode != 0 and not os.environ.get ('SYMPAD_DEBUG'):
					sys.exit (0)

		# child starts here
		_vars.update (_START_VARS)
		sym.set_user_funcs (set (_START_VARS))
		_parser.set_user_funcs (set (_START_VARS))

		if ('--sympyEI', '') in opts or ('-E', '') in opts:
			sast.sympyEI ()

		if ('--quick', '') in opts or ('-q', '') in opts:
			_parser.set_quick ()

		if not argv:
			host, port = _DEFAULT_ADDRESS
		else:
			host, port = (re.split (r'(?<=\]):' if argv [0].startswith ('[') else ':', argv [0]) + [_DEFAULT_ADDRESS [1]]) [:2]
			host, port = host.strip ('[]'), int (port)

		fnms    = ('sympad.py',) if _RUNNING_AS_SINGLE_SCRIPT else ('lalr1.py', 'sparser.py', 'sym.py', 'server.py')
		watch   = [os.path.join (_SYMPAD_PATH, fnm) for fnm in fnms]
		tstamps = [os.stat (fnm).st_mtime for fnm in watch]
		httpd   = HTTPServer ((host, port), Handler) # ThreadingHTTPServer ((host, port), Handler)
		thread  = threading.Thread (target = httpd.serve_forever, daemon = True)

		thread.start ()

		def log_message (msg):
			y, m, d, hh, mm, ss, _, _, _ = time.localtime (time.time ())

			sys.stderr.write (f'{httpd.server_address [0]} - - ' \
					f'[{"%02d/%3s/%04d %02d:%02d:%02d" % (d, _month_name [m], y, hh, mm, ss)}] {msg}\n')

		if _SYMPAD_FIRST_RUN:
			print ('Sympad server running. If a browser window does not automatically open to the address below then try navigating to that URL manually.\n')

		log_message (f'Serving at http://{httpd.server_address [0]}:{httpd.server_address [1]}/')

		if os.environ.get ('SYMPAD_FIRST_RUN') and ('--nobrowser', '') not in opts and ('-n', '') not in opts:
			webbrowser.open (f'http://{httpd.server_address [0] if httpd.server_address [0] != "0.0.0.0" else "127.0.0.1"}:{httpd.server_address [1]}')

		while 1:
			time.sleep (0.5)

			if [os.stat (fnm).st_mtime for fnm in watch] != tstamps:
				log_message ('Files changed, restarting...')
				sys.exit (0)

	except OSError as e:
		if e.errno != 98:
			raise

		print (f'Port {port} seems to be in use, try specifying different port as a command line parameter, e.g. localhost:8001')

	except KeyboardInterrupt:
		sys.exit (0)

	sys.exit (-1)
