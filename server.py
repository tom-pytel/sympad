#! /usr/bin/env python

import sys
assert sys.version_info >= (3, 6), 'Python version 3.6+ required'
import json
import os
import re
import subprocess
import time
import threading

from urllib.parse import parse_qs
from socketserver import ThreadingMixIn
from http.server import HTTPServer, SimpleHTTPRequestHandler

import lalr1
import sparser
import sym

#...............................................................................................
_last_ast = ('#', 0) # last evaluated expression for _ usage

def _ast_replace (ast, src, dst):
	return \
			ast if not isinstance (ast, tuple) else \
			dst if ast == src else \
			tuple (_ast_replace (s, src, dst) for s in ast)

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
			tex                       = None

			if ast is not None:
				tex = sym.ast2tex (_ast_replace (ast, ('@', '_'), _last_ast))

			resp = {
				'tex'         : tex,
				'erridx'      : erridx,
				'autocomplete': autocomplete,
			}

		else: # mode = 'evaluate'
			try:
				ast, _, _ = parser.parse (req ['text'])
				ast       = _ast_replace (ast, ('@', '_'), _last_ast)
				spt       = sym.ast2spt (ast)
				ast       = sym.spt2ast (spt)
				_last_ast = ast
				resp      = {'tex': sym.ast2tex (ast)}

			except Exception as e:
				s    = str (e)
				s    = (s if s [0] != '"' else s [1 : -1]) if s else ''
				resp = {'err': f'{e.__class__.__name__}' + (f': {s}' if s else '')}

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
			host, port = '', 8000
		else:
			host, port = (re.split (r'(?<=\]):' if sys.argv [1].startswith ('[') else ':', sys.argv [1]) + ['8000']) [:2]
			host, port = host.strip ('[]'), int (port)

		watch   = ('lalr1.py', 'sparser.py', 'sym.py', 'server.py')
		tstamps = [os.stat (fnm).st_mtime for fnm in watch]
		# httpd   = ThreadingHTTPServer ((host, port), Handler)
		httpd   = HTTPServer ((host, port), Handler)
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
