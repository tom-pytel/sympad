#!/usr/bin/env python
# python 3.6+

# Testing of server state machine (vars, env, lambdas).

import os
import sys
import time
import subprocess
import unittest

import requests

if __name__ == '__main__':
	if len (sys.argv) == 1:
		subprocess.run ([sys.executable, '-m', 'unittest', '-v', os.path.basename (sys.argv [0])])
		sys.exit (0)

class Test (unittest.TestCase):
	def test_vars (self):
		self.assertEqual (get ('x'), {'math': ('x', 'x', 'x')})
		self.assertEqual (get ('x = 2'), {'math': ('x = 2', 'x = 2', 'x = 2')})
		self.assertEqual (get ('x'), {'math': ('2', '2', '2')})
		self.assertEqual (get ('x*3'), {'math': ('6', '6', '6')})
		self.assertEqual (get ('x**2'), {'math': ('4', '4', '4')})
		self.assertEqual (get ('y'), {'math': ('y', 'y', 'y')})
		self.assertEqual (get ('y = x'), {'math': ('y = 2', 'y = 2', 'y = 2')})
		self.assertEqual (get ('y'), {'math': ('2', '2', '2')})
		self.assertEqual (get ('del (x, y)'), {'msg': ["Variable 'x' deleted.", "Variable 'y' deleted."]})
		self.assertEqual (get ('x'), {'math': ('x', 'x', 'x')})
		self.assertEqual (get ('y'), {'math': ('y', 'y', 'y')})
		self.assertEqual (get ('x = x'), {'err': "server.CircularReferenceError: I'm sorry, Dave. I'm afraid I can't do that."})
		self.assertEqual (get ('x, y = x, y'), {'err': "server.CircularReferenceError: I'm sorry, Dave. I'm afraid I can't do that."})
		self.assertEqual (get ('x, y = y, x'), {'err': "server.CircularReferenceError: I'm sorry, Dave. I'm afraid I can't do that."})
		self.assertEqual (get ('x, y = 1, 2'), {'math': [('x = 1', 'x = 1', 'x = 1'), ('y = 2', 'y = 2', 'y = 2')]})
		self.assertEqual (get ('x, y = y, x'), {'math': [('x = 2', 'x = 2', 'x = 2'), ('y = 1', 'y = 1', 'y = 1')]})
		self.assertEqual (get ('x, y'), {'math': ('(2, 1)', '(2, 1)', '\\left(2, 1 \\right)')})
		self.assertEqual (get ('delvars'), {'math': ('delvars', 'delvars', 'delvars')})
		self.assertEqual (get ('x'), {'math': ('2', '2', '2')})
		self.assertEqual (get ('y'), {'math': ('1', '1', '1')})

	def test_lambdas (self):
		self.assertEqual (get ('f = lambda: 2'), {'math': ('f = lambda: 2', 'f = Lambda((), 2)', 'f = \\left(\\left( \\right) \\mapsto 2 \\right)')})
		self.assertEqual (get ('f'), {'math': ('lambda: 2', 'Lambda((), 2)', '\\left(\\left( \\right) \\mapsto 2 \\right)')})
		self.assertEqual (get ('f ()'), {'math': ('2', '2', '2')})
		self.assertEqual (get ('f = lambda x: x'), {'math': ('f = lambda x: x', 'f = Lambda(x, x)', 'f = \\left(x \\mapsto x \\right)')})
		self.assertEqual (get ('f'), {'math': ('lambda x: x', 'Lambda(x, x)', '\\left(x \\mapsto x \\right)')})
		self.assertEqual (get ('f (x)'), {'math': ('x', 'x', 'x')})
		self.assertEqual (get ('f (y)'), {'math': ('y', 'y', 'y')})
		self.assertEqual (get ('f (2)'), {'math': ('2', '2', '2')})
		self.assertEqual (get ('f = lambda x: x**2'), {'math': ('f = lambda x: x**2', 'f = Lambda(x, x**2)', 'f = \\left(x \\mapsto x^2 \\right)')})
		self.assertEqual (get ('f (x)'), {'math': ('x**2', 'x**2', 'x^2')})
		self.assertEqual (get ('f (y)'), {'math': ('y**2', 'y**2', 'y^2')})
		self.assertEqual (get ('f (2)'), {'math': ('4', '4', '4')})
		self.assertEqual (get ('g = lambda x: f(x) + f(2x)'), {'math': ('g = lambda x: f(2 x) + f(x)', 'g = Lambda(x, f(2*x) + f(x))', 'g = \\left(x \\mapsto \\operatorname{f}\\left(2 x \\right) + \\operatorname{f}\\left(x \\right) \\right)')})
		self.assertEqual (get ('g'), {'math': ('lambda x: f(2 x) + f(x)', 'Lambda(x, f(2*x) + f(x))', '\\left(x \\mapsto \\operatorname{f}\\left(2 x \\right) + \\operatorname{f}\\left(x \\right) \\right)')})
		self.assertEqual (get ('g (x)'), {'math': ('5x**2', '5*x**2', '5 x^2')})
		self.assertEqual (get ('g (y)'), {'math': ('5y**2', '5*y**2', '5 y^2')})
		self.assertEqual (get ('g (2)'), {'math': ('20', '20', '20')})
		self.assertEqual (get ('del f'), {'msg': ["Function 'f' deleted."]})
		self.assertEqual (get ('g (2)'), {'err': "NameError: function 'f' is not defined"})
		self.assertEqual (get ('g = lambda f, x: f (x)'), {'math': ('g = lambda f, x: f x', 'g = Lambda((f, x), f*x)', 'g = \\left(\\left(f, x \\right) \\mapsto f x \\right)')})
		self.assertEqual (get ('g (f, 2)'), {'math': ('2 f', '2*f', '2 f')})
		self.assertEqual (get ('f = lambda x: x**2'), {'math': ('f = lambda x: x**2', 'f = Lambda(x, x**2)', 'f = \\left(x \\mapsto x^2 \\right)')})
		self.assertEqual (get ('g = lambda f, x: f (x)'), {'math': ('g = lambda f, x: f(x)', 'g = Lambda((f, x), f(x))', 'g = \\left(\\left(f, x \\right) \\mapsto \\operatorname{f}\\left(x \\right) \\right)')})
		self.assertEqual (get ('g (f, 2)'), {'math': ('4', '4', '4')})
		self.assertEqual (get ('g = lambda h, x: $h (x)'), {'math': ('g = lambda h, x: $h(x)', 'g = Lambda((h, x), h(x))', 'g = \\left(\\left(h, x \\right) \\mapsto \\operatorname{$h}\\left(x \\right) \\right)')})
		self.assertEqual (get ('g (f, 2)'), {'math': ('4', '4', '4')})
		self.assertEqual (get ('f = lambda x, y: x + y'), {'math': ('f = lambda x, y: x + y', 'f = Lambda((x, y), x + y)', 'f = \\left(\\left(x, y \\right) \\mapsto x + y \\right)')})
		self.assertEqual (get ('f (1, 2)'), {'math': ('3', '3', '3')})
		self.assertEqual (get ('g = lambda h, x, y: h (x, y)'), {'math': ('g = lambda h, x, y: h(x, y)', 'g = Lambda((h, x, y), h(x, y))', 'g = \\left(\\left(h, x, y \\right) \\mapsto \\operatorname{h}\\left(x, y \\right) \\right)')})
		self.assertEqual (get ('g (f, 1, 2)'), {'math': ('3', '3', '3')})
		self.assertEqual (get ('f = lambda x, y, z: x + y + z'), {'math': ('f = lambda x, y, z: x + y + z', 'f = Lambda((x, y, z), x + y + z)', 'f = \\left(\\left(x, y, z \\right) \\mapsto x + y + z \\right)')})
		self.assertEqual (get ('f (1, 2, 3)'), {'math': ('6', '6', '6')})
		self.assertEqual (get ('f = lambda x, y, z, w: x + y + z + w'), {'math': ('f = lambda x, y, z, w: w + x + y + z', 'f = Lambda((x, y, z, w), w + x + y + z)', 'f = \\left(\\left(x, y, z, w \\right) \\mapsto w + x + y + z \\right)')})
		self.assertEqual (get ('f (1, 2, 3, 4)'), {'math': ('10', '10', '10')})
		self.assertEqual (get ('f (1, 2, 3)'), {'err': "TypeError: lambda function 'f' takes 4 argument(s)"})
		self.assertEqual (get ('f (1, 2, 3, 4, 5)'), {'err': "TypeError: lambda function 'f' takes 4 argument(s)"})

	def test_env (self):
		self.assertEqual (get ('env (quick)'), {'msg': ['Quick input mode is on.']})
		self.assertEqual (get ('env (noquick)'), {'msg': ['Quick input mode is off.']})
		self.assertEqual (get ('env'), {'msg': ['Uppercase E and I is off.', 'Quick input mode is off.', 'Python S escaping on.', 'Expression evaluation is on.', 'Expression doit is on.', 'Function N is on.', 'Function O is on.', 'Function S is on.', 'Function gamma is on.', 'Function Gamma is on.', 'Function zeta is on.']})
		self.assertEqual (get ('env(EI, quick, nopyS, noeval, nodoit, noN, noO, noS, nogamma, noGamma, nozeta)'), {'msg': ['Uppercase E and I is on.', 'Quick input mode is on.', 'Python S escaping off.', 'Expression evaluation is off.', 'Expression doit is off.', 'Function N is off.', 'Function O is off.', 'Function S is off.', 'Function gamma is off.', 'Function Gamma is off.', 'Function zeta is off.']})
		self.assertEqual (get ('env'), {'msg': ['Uppercase E and I is on.', 'Quick input mode is on.', 'Python S escaping off.', 'Expression evaluation is off.', 'Expression doit is off.', 'Function N is off.', 'Function O is off.', 'Function S is off.', 'Function gamma is off.', 'Function Gamma is off.', 'Function zeta is off.']})
		self.assertEqual (get ('envreset'), {'msg': ['Uppercase E and I is off.', 'Quick input mode is off.', 'Python S escaping on.', 'Expression evaluation is on.', 'Expression doit is on.', 'Function N is on.', 'Function O is on.', 'Function S is on.', 'Function gamma is on.', 'Function Gamma is on.', 'Function zeta is on.', 'Environment has been reset.']})
		self.assertEqual (get ('env'), {'msg': ['Uppercase E and I is off.', 'Quick input mode is off.', 'Python S escaping on.', 'Expression evaluation is on.', 'Expression doit is on.', 'Function N is on.', 'Function O is on.', 'Function S is on.', 'Function gamma is on.', 'Function Gamma is on.', 'Function zeta is on.']})

def get (text):
	resp = requests.post (URL, {'idx': 1, 'mode': 'evaluate', 'text': text}).json ()
	ret  = {}

	if 'math' in resp:
		math         = [(resp ['math'] [i] ['nat'], resp ['math'] [i] ['py'], resp ['math'] [i] ['tex']) for i in range (len (resp ['math']))]
		ret ['math'] = math if len (math) > 1 else math [0]

	if 'msg' in resp:
		ret ['msg'] = resp ['msg']

	if 'err' in resp:
		ret ['err'] = resp ['err'] [-1]

	return ret

_SESSIONS = (

('vars', """

x
x = 2
x
x*3
x**2
y
y = x
y
del (x, y)
x
y
x = x
x, y = x, y
x, y = y, x
x, y = 1, 2
x, y = y, x
x, y
delvars
x
y

"""), ('lambdas', """

f = lambda: 2
f
f ()
f = lambda x: x
f
f (x)
f (y)
f (2)
f = lambda x: x**2
f (x)
f (y)
f (2)
g = lambda x: f(x) + f(2x)
g
g (x)
g (y)
g (2)
del f
g (2)
g = lambda f, x: f (x)
g (f, 2)
f = lambda x: x**2
g = lambda f, x: f (x)
g (f, 2)
g = lambda h, x: $h (x)
g (f, 2)
f = lambda x, y: x + y
f (1, 2)
g = lambda h, x, y: h (x, y)
g (f, 1, 2)
f = lambda x, y, z: x + y + z
f (1, 2, 3)
f = lambda x, y, z, w: x + y + z + w
f (1, 2, 3, 4)
f (1, 2, 3)
f (1, 2, 3, 4, 5)

"""), ('env', """

env (quick)
env (noquick)
env
env(EI, quick, nopyS, noeval, nodoit, noN, noO, noS, nogamma, noGamma, nozeta)
env
envreset
env

"""),

)

SYSARGV  = sys.argv [:]
sys.argv = [os.path.abspath ('server.py'), '--child']

import server

HTTPD = server.start_server (logging = False)
URL   = f'http://{HTTPD.server_address [0]}:{HTTPD.server_address [1]}/'

if __name__ == '__main__':
	for name, texts in _SESSIONS:
		get ('env (reset)')
		get ('delall')
		get ('0')

		texts = [s.strip () for s in texts.strip ().split ('\n')]

		print (f'\n\tdef test_{name} (self):')

		for text in texts:
			print (f'\t\tself.assertEqual (get ({text!r}), {get (text)!r})')
