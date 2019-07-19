#!/usr/bin/env python

from getopt import getopt
from random import random, randrange, choice
import sys

import sast
from sast import AST
import sym
import sparser

TERMS = [
	'0',
	'1',
	'-1',
	'1.0',
	'-1.0',
	# '1e-100',
	# '1e100',
	# '1e+100',
	'a',
	"a'",
	'd',
	'dx',
	'partial',
	'partialx',
	'oo',
	"'str'",
]

_EQS = ["=", "==", "!=", "<", "<=", ">", ">="]
def expr_eq (): ## BROKEN!
	return f'{{{expr ()}}} {choice (_EQS)} {{{expr ()}}}'

def expr_paren ():
	return '(' + ','.join (f'{{{expr ()}}}' for i in range (randrange (4))) + ')'

def expr_brack ():
	return '[' + ','.join (f'{{{expr ()}}}' for i in range (randrange (4))) + ']'

def expr_abs ():
	return f'\\left|{{{expr ()}}}\\right|'

def expr_minus ():
	return f'-{{{expr ()}}}'

def expr_fact ():
	return f'{{{expr ()}}}!'

def expr_add ():
	return '{' + '+'.join (f'{{{expr ()}}}' for i in range (randrange (2, 4))) + '}'

def expr_mul_imp ():
	return '{' + '  '.join (f'{{{expr ()}}}' for i in range (randrange (2, 4))) + '}'

def expr_mul_exp ():
	return '{' + '*'.join (f'{{{expr ()}}}' for i in range (randrange (2, 4))) + '}'

def expr_mul_cdot ():
	return '{' + ' \\cdot '.join (f'{{{expr ()}}}' for i in range (randrange (2, 4))) + '}'

def expr_div ():
	return f'{{{expr ()}}} / {{{expr ()}}}'

def expr_frac ():
	return f'\\frac{{{expr ()}}}{{{expr ()}}}'

def expr_caret ():
	return f'{{{expr ()}}}^{{{expr ()}}}'

def expr_dblstar ():
	return f'{{{expr ()}}}**{{{expr ()}}}'

def expr_log ():
	return \
			choice (['', '\\']) + f'{choice (["ln", "log"])}{{{expr ()}}}' \
			if random () >= 0.5 else \
			f'\\log_{{{expr ()}}}{{{expr ()}}}'

def expr_sqrt ():
	return \
			choice (['', '\\']) + f'sqrt{{{expr ()}}}' \
			if random () >= 0.5 else \
			f'\\sqrt[{{{expr ()}}}]{{{expr ()}}}'

def expr_func ():
	while 1:
		py = choice (list (AST.Func.PY))

		if py not in sparser._FUNC_AST_XLAT and py not in sym._ast2tex_func_xlat:
			break

	return \
			'\\' + f'{choice (list (AST.Func.TEX))}{expr_paren ()}' \
			if random () >= 0.5 else \
			f'{py}{expr_paren ()}' \

def expr_lim ():
	return \
			'\\lim_{x \\to ' + f'{expr ()}}} {{{expr ()}}}' \
			if random () >= 0.5 else \
			f'Limit ({expr ()}, x, {expr ()})'

def expr_sum ():
	return \
			'\\sum_{x = ' + f'{expr ()}}}^{{{expr ()}}} {{{expr ()}}}' \
			if random () >= 0.5 else \
			f'Sum ({expr ()}, (x, {expr ()}, {expr ()}))'

def expr_diff ():
	d  = 'partial' # choice (['d', 'partial '])
	p  = 0
	dv = []

	for i in range (randrange (1, 4)):
		n  = randrange (1, 4)
		p += n

		dv.append ((choice (['x', 'y', 'z']), n))

	return \
			f'{d}^{{{p}}} / {" ".join (f"{d + v}^{{{dp}}}" for v, dp in dv)} {{{expr ()}}}'
			# if random () >= 0.5 else \
			# f'Derivative ({expr ()}, {", ".join (f"{v}, {dp}" for v, dp in dv)})'

def expr_intg ():
	return \
			f'\\int_{{{expr ()}}}^{{{expr ()}}} {{{expr ()}}} dx' \
			if random () >= 0.5 else \
			f'\\int {{{expr ()}}} dx'

def expr_vec ():
	return '({' + ','.join (f'{{{expr ()}}}' for i in range (randrange (1, 4))) + ',})'

def expr_mat ():
	cols = randrange (1, 4)

	return '({' + ','.join ('{' + ','.join (f'{{{expr ()}}}' for j in range (cols)) + ',}' for i in range (randrange (1, 4))) + ',})'

def expr_piece ():
	p = [f'{{{expr ()}}} if {{{expr ()}}}']

	for i in range (randrange (3)):
		p.append (f'else {{{expr ()}}} if {{{expr ()}}}')

	if random () >= 0.5:
		p.append (f'else {{{expr ()}}}')

	return ' '.join (p)

def expr_lamb ():
	return f'lambda{choice (["", " x", " x, y", " x, y, z"])}: {{{expr ()}}}'

EXPRS = [va [1] for va in filter (lambda va: va [0] [:5] == 'expr_', globals ().items ())]

def expr (depth = None):
	global DEPTH

	if depth is not None:
		DEPTH = depth

	if not DEPTH:
		return choice (TERMS)

	DEPTH -= 1
	expr   = choice (EXPRS) ()
	DEPTH += 1

	return expr

def remove_paren (ast):
	if not isinstance (ast, AST):
		return ast

	if ast.is_paren:
		return remove_paren (ast.paren)

	return AST (*tuple (remove_paren (a) for a in ast))

def flatten (ast):
	if not isinstance (ast, AST):
		return ast

	t = [flatten (a) for a in ast]

	if ast.op in {'+', '*'}:
		t = (ast.op, tuple (sum (((m,) if m.op != ast.op else m [1] for m in t [1]), ())))

	return AST (*t)

#...............................................................................................
_DEPTH = 3

def test ():
	opts, argv = getopt (sys.argv [1:], '', ['tex', 'nat', 'py', 'print', 'show'])
	parser     = sparser.Parser ()

	if ('--print', '') in opts:
		global DEPTH

		DEPTH = 0

		for e in EXPRS:
			print (e ())

		sys.exit (0)

	dotex = ('--tex', '') in opts
	donat = ('--nat', '') in opts
	dopy  = ('--py', '') in opts

	try:
		while 1:
			text              = expr (_DEPTH)
			ast, erridx, auto = parser.parse (text)

			if erridx or auto:
				print ('Invalid:', text)
				continue

			ast = flatten (ast)
			tex = dotex and sym.ast2tex (ast)
			nat = donat and sym.ast2nat (ast)
			py  = dopy and sym.ast2py (ast)

			if ('--show', '') in opts:
				print ()
				print ('text:', text)
				print ('ast: ', ast)
				print ('tex: ', tex)
				print ('nat: ', nat)
				print ('py:  ', py)

			ast_tex = dotex and parser.parse (tex) [0]
			ast_nat = donat and parser.parse (nat) [0]
			ast_py  = dopy and parser.parse (py) [0]
			ast_srp = remove_paren (ast)
			ast_tex = dotex and remove_paren (ast_tex)
			ast_nat = donat and remove_paren (ast_nat)
			ast_py  = dopy and remove_paren (ast_py)

			if (dotex and ast_tex != ast_srp) or (donat and ast_nat != ast_srp) or (dopy and ast_py != ast_py):
				print ()
				print ('text:', text)
				print ('ast: ', ast)

				if dotex and ast_tex != ast_srp:
					print ('tex: ', ast_tex)

				if donat and ast_nat != ast_srp:
					print ('nat: ', ast_nat)

				if dopy and ast_py != ast_py:
					print ('py:  ', ast_py)

				sys.exit (0)

	except Exception as e:
		print ()
		print ('text:', text)
		print ('ast: ', ast)
		print ('srp: ', ast_srp)
		print ('tex: ', ast_tex)
		print ('nat: ', ast_nat)
		print ('py:  ', ast_py)
		print ()

		if not isinstance (e, KeyboardInterrupt):
			raise

if __name__ == '__main__':
	# parser = sparser.Parser ()
	# ast = parser.parse ("{{\\lim_{x \\to {{oo},}} {\\frac{d}{d}}}  {{{{{partialx} \\cdot {a'}}} \\cdot {{{a'}*{'str'}}}}}}") [0]
	# ast = parser.parse ('{{1+{2+3}}+4}') [0]
	# print (ast)
	# ast = flatten (ast)
	# print (ast)
	test ()
