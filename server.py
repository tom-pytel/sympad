#!/usr/bin/env python
# python 3.6+

# TODO: Working directory.
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

_SYMPAD_FIRST_RUN         = os.environ.get ('SYMPAD_FIRST_RUN')
_SYMPAD_CHILD             = os.environ.get ('SYMPAD_CHILD')

_VAR_LAST = '_'

if _SYMPAD_CHILD: # sympy slow to import if not precompiled so don't do it for watcher process as is unnecessary there
	import sympy as sp
	import sast          # AUTO_REMOVE_IN_SINGLE_SCRIPT
	from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
	import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT
	import sparser       # AUTO_REMOVE_IN_SINGLE_SCRIPT

	_sys_stdout = sys.stdout
	_parser     = sparser.Parser ()
	_vars       = {_VAR_LAST: AST.Zero} # This is individual session STATE! Threading can corrupt this! It is GLOBAL to survive multiple Handlers.

_DEFAULT_ADDRESS = ('localhost', 8000)

_STATIC_FILES    = {'/style.css': 'css', '/script.js': 'javascript', '/index.html': 'html', '/help.html': 'html'}
_FILES           = {} # pylint food # AUTO_REMOVE_IN_SINGLE_SCRIPT

_HELP = f"""
usage: {os.path.basename (sys.argv [0])} [--help] [--debug] [--nobrowser] [--sympyEI] [host:port]
"""

#...............................................................................................
# class ThreadingHTTPServer (ThreadingMixIn, HTTPServer):
# 	pass

class RealityRedefinitionError (NameError):	pass
class CircularReferenceError (RecursionError): pass
class AE35UnitError (Exception): pass

def _ast_remap (ast, map_):
	if not isinstance (ast, AST) or (ast.is_func and ast.func == '@'): # non-AST or stop remap
		return ast

	if ast.is_var and ast.var in map_: # variable
		return _ast_remap (map_ [ast.var], map_)

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
	if len (_vars) == 1:
		return 'No variables defined.'

	asts = []

	for v, e in sorted (_vars.items ()):
		if v != _VAR_LAST:
			asts.append (AST ('=', '=', ('@', v), e))
			# if e.is_lamb:
			# 	asts.append (AST ('=', '=', ('func', v, e.vars), e.lamb))
			# else:
			# 	asts.append (AST ('=', '=', ('@', v), e))

	return asts

def _admin_del (ast):
	arg = ast.args [0] if ast.args else AST.VarNull

	try:
		del _vars [arg.var]
	except KeyError:
		raise AE35UnitError (f'Variable {sym.ast2nat (arg)!r} is not defined, it can only be attributable to human error.')

	return f'Variable {sym.ast2nat (arg)!r} deleted.'

def _admin_delall (ast):
	last_var = _vars [_VAR_LAST]
	_vars.clear ()
	_vars [_VAR_LAST] = last_var

	return 'All variables deleted.'

def _admin_sympyEI (ast):
	sast.sympyEI (bool (sym.ast2spt (ast.args [0])) if ast.args else True)

	return f'Constant representation set to {AST.E.var!r} and {AST.I.var!r}.'

#...............................................................................................
class Handler (SimpleHTTPRequestHandler):
	def do_GET (self):
		if self.path == '/':
			self.path = '/index.html'

		if self.path not in _STATIC_FILES:
			self.send_error (404, f'Invalid path {self.path!r}')

		elif not _RUNNING_AS_SINGLE_SCRIPT:
			return SimpleHTTPRequestHandler.do_GET (self)

		else:
			self.send_response (200)
			self.send_header ('Content-type', f'text/{_STATIC_FILES [self.path]}')
			self.end_headers ()
			self.wfile.write (_FILES [self.path [1:]])

	def do_POST (self):
		request = parse_qs (self.rfile.read (int (self.headers ['Content-Length'])).decode ('utf8'), keep_blank_values = True)

		for key, val in list (request.items ()):
			if isinstance (val, list) and len (val) == 1:
				request [key] = val [0]

		if request ['mode'] == 'validate':
			response = self.validate (request)
		else: # request ['mode'] == 'evaluate':
			response = self.evaluate (request)

		self.send_response (200)
		self.send_header ("Content-type", "application/json")
		self.end_headers ()
		self.wfile.write (json.dumps ({**request, **response}).encode ('utf8'))

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
		sys.stdout = io.StringIO ()

		try:
			ast, _, _ = _parser.parse (request ['text'])

			if ast.is_func and ast.func in {'vars', 'del', 'delall', 'sympyEI'}: # special admin function?
				asts = globals () [f'_admin_{ast.func}'] (ast)

				if isinstance (asts, str):
					return {'msg': [asts]}

			else: # not admin function, normal evaluation
				ast, vars = _ast_prepare_ass (ast)

				sym.set_precision (ast)

				spt = sym.ast2spt (ast)
				ast = sym.spt2ast (spt)

				if os.environ.get ('SYMPAD_DEBUG'):
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
		opts, argv = getopt.getopt (sys.argv [1:], '', ['help', 'nobrowser', 'debug', 'sympyEI'])

		if ('--help', '') in opts:
			print (_HELP.strip ())
			sys.exit (0)

		if ('--debug', '') in opts:
			os.environ ['SYMPAD_DEBUG'] = '1'

		if not _SYMPAD_CHILD:
			args      = [sys.executable] + sys.argv
			first_run = '1'

			while 1:
				ret       = subprocess.run (args, env = {**os.environ, 'SYMPAD_CHILD': '1', 'SYMPAD_FIRST_RUN': first_run})
				first_run = ''

				if ret.returncode != 0 and not os.environ.get ('SYMPAD_DEBUG'):
					sys.exit (0)

		if ('--sympyEI', '') in opts:
			sast.sympyEI ()

		if not argv:
			host, port = _DEFAULT_ADDRESS
		else:
			host, port = (re.split (r'(?<=\]):' if argv [0].startswith ('[') else ':', argv [0]) + [_DEFAULT_ADDRESS [1]]) [:2]
			host, port = host.strip ('[]'), int (port)

		watch   = ('sympad.py',) if _RUNNING_AS_SINGLE_SCRIPT else ('lalr1.py', 'sparser.py', 'sym.py', 'server.py')
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

		if os.environ.get ('SYMPAD_FIRST_RUN') and ('--nobrowser', '') not in opts:
			webbrowser.open (f'http://{httpd.server_address [0] if httpd.server_address [0] != "0.0.0.0" else "127.0.0.1"}:{httpd.server_address [1]}/')

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
