#!/usr/bin/env python
# python 3.6+

# TODO: Exception prevents restart on file date change?

import getopt
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

if _SYMPAD_CHILD: # sympy slow to import if not precompiled so don't do it for watcher process as is unnecessary there
	import sympy as sp
	import sast          # AUTO_REMOVE_IN_SINGLE_SCRIPT
	from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
	import sparser       # AUTO_REMOVE_IN_SINGLE_SCRIPT
	import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

	_var_last = AST ('@', '_')
	_vars     = {_var_last: AST.Zero} # This is individual session STATE! Threading can corrupt this! It is GLOBAL to survive multiple Handlers.
	_parser   = sparser.Parser ()

_DEFAULT_ADDRESS = ('localhost', 8000)

_STATIC_FILES    = {'/style.css': 'css', '/script.js': 'javascript', '/index.html': 'html', '/help.html': 'html'}
_FILES           = {} # pylint food # AUTO_REMOVE_IN_SINGLE_SCRIPT

_HELP = f"""
usage: {os.path.basename (sys.argv [0])} [--help] [--debug] [--nobrowser] [--sympyEI] [host:port]
"""

#...............................................................................................
# class ThreadingHTTPServer (ThreadingMixIn, HTTPServer):
# 	pass

def _ast_remap (ast, map_):
	return \
			ast                                        if not isinstance (ast, AST) or (ast.is_func and ast.func == '@') else \
			_ast_remap (map_ [ast], map_)              if ast in map_ else \
			AST (*(_ast_remap (a, map_) for a in ast))

def _ast_prepare_ass (ast): # check and prepare for simple or tuple assignment
	vars = None

	if ast.is_ass:
		if ast.lhs.is_var: # simple assignment?
			ast, vars = ast.rhs, [ast.lhs]

	elif ast.is_comma: # tuple assignment? ('x, y = y, x' comes from parser as ('x', 'y = y', 'x')) so remap
		lhss = []
		itr  = iter (ast.commas)

		for c in itr:
			if c.is_var:
				lhss.append (c)
			elif not c.is_ass or not c.lhs.is_var:
				break

			else:
				t    = (c.rhs,) + tuple (itr)
				ast  = t [0] if len (t) == 1 else AST (',', t)
				vars = lhss + [c.lhs]

	return _ast_remap (ast, _vars), vars

def _ast_execute_ass (ast, vars): # execute assignment if it was detected
	global _vars

	asts = None

	if not vars: # no assignment
		_vars [_var_last] = ast

	else:
		if len (vars) == 1: # simple assignment
			new_vars = {**_vars, vars [0]: ast}

		else: # tuple assignment
			ast  = ast.strip_paren ()
			asts = ast.commas if ast.is_comma else tuple (sym.spt2ast (a) for a in sym.ast2spt (ast))

			if len (vars) < len (asts):
				raise ValueError (f'too many values to unpack (expected {len (vars)})')
			elif len (vars) > len (asts):
				raise ValueError (f'not enough values to unpack (expected {len (vars)}, got {len (asts)})')
			else:
				new_vars = {**_vars, **dict ((vars [i], asts [i]) for i in range (len (vars)))}

			asts = [AST ('=', '=', vars [i], asts [i]) for i in range (len (vars))]

		try: # check for circular references
			_ast_remap (AST (',', tuple (vars)), new_vars)
		except RecursionError:
			raise RecursionError ("I'm sorry, Dave. I'm afraid I can't do that. (circular reference detected)") from None

		_vars = new_vars

	return asts or [ast]

def _admin_vars (ast):
	if len (_vars) == 1:
		return 'No variables defined.'
	else:
		return [AST ('=', '=', v, e) for v, e in filter (lambda ve: ve [0] != _var_last, sorted (_vars.items ()))]

def _admin_del (ast):
	ast = ast.arg.strip_paren ()

	try:
		del _vars [ast]
	except KeyError:
		raise NameError (f'Variable {sym.ast2nat (ast)!r} is not defined, it can only be attributable to human error.')

	return f'Variable {sym.ast2nat (ast)!r} deleted.'

def _admin_delall (ast):
	global _vars

	_vars = {_var_last: _vars [_var_last]}

	return 'All variables deleted.'

def _admin_sympyEI (ast):
	arg = ast.arg.strip_paren ()
	arg = \
		bool (sym.ast2spt (arg))             if not arg.is_comma else \
		True                                 if not len (arg.commas) else \
		bool (sym.ast2spt (arg.commas [0]))

	sast.sympyEI (arg)

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
			if len (val) == 1:
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

	def validate (self, request):
		ast, erridx, autocomplete = _parser.parse (request ['text'])
		tex = nat = py            = None

		if ast is not None:
			ast = _ast_remap (ast, {_var_last: _vars [_var_last]}) # just remap last evaluated _
			tex = sym.ast2tex (ast)
			nat = sym.ast2nat (ast)
			py  = sym.ast2py (ast)

			if os.environ.get ('SYMPAD_DEBUG'):
				print ()
				print ('ast:', ast)
				print ('tex:', tex)
				print ('nat:', nat)
				print ('py: ', py)
				print ()

		return {
			'tex'         : tex,
			'nat'         : nat,
			'py'          : py,
			'erridx'      : erridx,
			'autocomplete': autocomplete,
		}

	def evaluate (self, request):
		try:
			ast, _, _ = _parser.parse (request ['text'])

			if ast.is_func and ast.func in {'vars', 'del', 'delall', 'sympyEI'}: # special admin function?
				asts = globals () [f'_admin_{ast.func}'] (ast)

				if isinstance (asts, str):
					return {'msg': asts}

			else: # not admin function, normal evaluation
				ast, vars = _ast_prepare_ass (ast)

				sym.set_precision (ast)

				spt = sym.ast2spt (ast, doit = True)
				ast = sym.spt2ast (spt)

				if os.environ.get ('SYMPAD_DEBUG'):
					print ()
					print ('spt:        ', repr (spt))
					print ('spt type:   ', type (spt))
					print ('sympy latex:', sp.latex (spt))
					print ()

				asts = _ast_execute_ass (ast, vars)

			return {'math': [{
				'tex': sym.ast2tex (ast),
				'nat': sym.ast2nat (ast),
				'py' : sym.ast2py (ast),
			} for ast in asts]}

		except Exception:
			return {'err': ''.join (traceback.format_exception (*sys.exc_info ())).replace ('  ', '&emsp;').strip ().split ('\n')}

#...............................................................................................
_month_name = (None, 'Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec')

if __name__ == '__main__':
	try:
		opts, argv = getopt.getopt (sys.argv [1:], '', ['help', 'debug', 'nobrowser', 'sympyEI'])

		if ('--help', '') in opts:
			print (_HELP.strip ())
			sys.exit (0)

		if not _SYMPAD_CHILD:
			args      = [sys.executable] + sys.argv
			first_run = '1'

			while 1:
				ret       = subprocess.run (args, env = {**os.environ, 'SYMPAD_CHILD': '1', 'SYMPAD_FIRST_RUN': first_run})
				first_run = ''

				if ret.returncode != 0:
					sys.exit (0)

		if ('--debug', '') in opts:
			os.environ ['SYMPAD_DEBUG'] = '1'

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
