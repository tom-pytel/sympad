#!/usr/bin/env python
# python 3.6+

import json
import os
import re
import subprocess
import sys
import time
import threading
import traceback

from urllib.parse import parse_qs
from socketserver import ThreadingMixIn
from http.server import HTTPServer, SimpleHTTPRequestHandler

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sparser       # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

import sympy as sp ## DEBUG!

_RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT

#...............................................................................................
_last_ast = AST.Zero # last evaluated expression for _ usage

def _ast_replace (ast, src, dst):
	return \
			ast if not isinstance (ast, AST) else \
			dst if ast == src else \
			AST (*(_ast_replace (s, src, dst) for s in ast))

class Handler (SimpleHTTPRequestHandler):
	def do_GET (self):
		if self.path == '/':
			self.path = '/index.html'

		return SimpleHTTPRequestHandler.do_GET (self)

	def do_POST (self):
		global _last_ast

		req    = parse_qs (self.rfile.read (int (self.headers ['Content-Length'])).decode ('utf8'), keep_blank_values = True)
		parser = sparser.Parser ()

		for key, val in list (req.items ()):
			if len (val) == 1:
				req [key] = val [0]

		if req ['mode'] == 'validate':
			ast, erridx, autocomplete = parser.parse (req ['text'])
			tex = simple = py         = None

			if ast is not None:
				ast    = _ast_replace (ast, ('@', '_'), _last_ast)
				tex    = sym.ast2tex (ast)
				simple = sym.ast2simple (ast)
				py     = sym.ast2py (ast)

				## DEBUG!
				print ()
				print ('ast:   ', ast)
				print ('tex:   ', tex)
				print ('simple:', simple)
				print ('py:    ', py)
				print ()
				## DEBUG!

			resp = {
				'tex'         : tex,
				'simple'      : simple,
				'py'          : py,
				'erridx'      : erridx,
				'autocomplete': autocomplete,
			}

		else: # mode = 'evaluate'
			try:
				ast, _, _ = parser.parse (req ['text'])
				ast       = _ast_replace (ast, ('@', '_'), _last_ast)

				sym.set_precision (ast)

				spt       = sym.ast2spt (ast)
				ast       = sym.spt2ast (spt)
				_last_ast = ast

				## DEBUG!
				print ()
				print ('spt:        ', repr (spt))
				print ('sympy latex:', sp.latex (spt))
				print ()
				## DEBUG!

				resp      = {
					'tex'   : sym.ast2tex (ast),
					'simple': sym.ast2simple (ast),
					'py'    : sym.ast2py (ast),
				}

			except Exception:
				resp = {'err': ''.join (traceback.format_exception (*sys.exc_info ())).replace ('  ', '&emsp;').strip ().split ('\n')}

		resp ['mode'] = req ['mode']
		resp ['idx']  = req ['idx']

		self.send_response (200)
		self.send_header ("Content-type", "application/json")
		self.end_headers ()
		self.wfile.write (json.dumps (resp).encode ('utf-8'))

class ThreadingHTTPServer (ThreadingMixIn, HTTPServer):
	pass

#...............................................................................................
_month_name = (None, 'Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec')

if __name__ == '__main__':
	try:
		if 'SYMPAD_RUNNED' not in os.environ:
			args = [sys.executable] + sys.argv

			while 1:
				subprocess.run (args, env = {**os.environ, 'SYMPAD_RUNNED': '1'})

		if len (sys.argv) < 2:
			host, port = 'localhost', 8000
		else:
			host, port = (re.split (r'(?<=\]):' if sys.argv [1].startswith ('[') else ':', sys.argv [1]) + ['8000']) [:2]
			host, port = host.strip ('[]'), int (port)

		watch   = ('lalr1.py', 'sparser.py', 'sym.py', 'server.py')
		tstamps = [os.stat (fnm).st_mtime for fnm in watch]
		httpd   = HTTPServer ((host, port), Handler) # ThreadingHTTPServer ((host, port), Handler)
		thread  = threading.Thread (target = httpd.serve_forever, daemon = True)

		thread.start ()

		def log_message (msg):
			y, m, d, hh, mm, ss, _, _, _ = time.localtime (time.time ())

			sys.stderr.write (f'{httpd.server_address [0]} - - ' \
					f'[{"%02d/%3s/%04d %02d:%02d:%02d" % (d, _month_name [m], y, hh, mm, ss)}] {msg}\n')

		log_message (f'Serving on {httpd.server_address [0]}:{httpd.server_address [1]}')

		while 1:
			time.sleep (0.5)

			if [os.stat (fnm).st_mtime for fnm in watch] != tstamps:
				log_message ('Files changed, restarting...')

				break

	except KeyboardInterrupt:
		pass
