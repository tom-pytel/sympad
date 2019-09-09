#!/usr/bin/env python
# python 3.6+

# Randomized CONSISTENCY testing of parsing: text -> ast -> tex/nat/py -> text -> ast

# test_sym.py -i --show --nc

from getopt import getopt
from random import random, randrange, choice
import sys
import time

from sast import AST
import spatch
import sxlat
import sym
import sparser

_TERMS = [
	'0',
	'1',
	'-1',
	'1.0',
	'-1.0',
	'.1',
	'1.',
	'1e-100',
	'1e100',
	'1e+100',
	'a',
	"a'",
	'd',
	'dx',
	'partial',
	'partialx',
	'\\partial ',
	'\\partialx',
	'\\partial x',
	'oo',
	'\\infty '
	'zoo',
	'\\tilde\\infty ',
	"'str'",
	'"str"',
	'None',
	'True',
	'False',
	'\\emptyset',
]

# previously problematic static test expressions
_EXPRESSIONS = r"""
\sqrt[{{1} / {1.0}}]{({oo},{partial})}
sqrt{{-1.0}**{0}}
{{\frac{1.0}{dx}} \cdot {{partial} / {partialx}} \cdot {{d} >= {oo}}}
\frac{{partial}**{1}}{{{partialx}*{dx}*{1.0}}}
{{\frac{1.0}{partialx}} \cdot {\exp({0},{a})} \cdot {{{d}+{oo}}}}
{\arcsin({-1.0},{dx},{oo})}^{{d} <= {-1}}
@({{d}**{1}},{\arcsech({partial},{partial})})
Limit ({d} > {-1.0}, x, {{1.0}*{partial}*{dx}})
{{d}^{1}} / {{{dx}  {oo}}}
{{{d}*{1}}} / {partial^{5} / partialy^{1} partialy^{2} partialz^{2} {oo}}
{{{0}!} \cdot {partial^{1} / partialx^{1} {dx}} \cdot {{d}**{d}}}
{{partial^{4} / partialy^{3} partialy^{1} {a}} \cdot {{'str'}^{d}}}
{\int {-1} dx} / {\int {1} dx}
{\int_{dx}^{a'} {-1} dx}!
\int {partial^{3} / partialy^{3} {a'}} dx
{{\int {partial} dx}  {partial^{4} / partialy^{1} partialz^{1} partialz^{2} {a}}}
\int_{[{-1.0}]}^{\int {partialx} dx} {{{oo}+{-1}}} dx
\int_{partial^{6} / partialy^{2} partialx^{2} partialz^{2} {partialx}}^{partial^{4} / partialz^{1} partialz^{2} partialx^{1} {0}} {{a} != {'str'}} dx
{{{oo}**{'str'}}+{\int {oo} dx}+{partial^{7} / partialz^{3} partialx^{2} partialx^{2} {0}}}
[{{{-1} \cdot {oo}}},{{{dx},{1.0},{oo}}},{partial^{8} / partialx^{3} partialx^{2} partialz^{3} {oo}}]
{{lambda x, y, z: {1}}+{{1.0} > {1.0}}+{{oo} / {'str'}}}
{{lambda: {-1}} \cdot {\frac{partialx}{oo}} \cdot {{1.0} if {1} else {a'} if {0}}}
{{{a'} / {-1}} {\lim_{x \to partial} {-1}} * [lambda x, y, z: {partialx}]}
\int_{\sqrt[{a}]{1.0}}^{[]} {lambda x: {partialx}} dx
lambda x: {{dx} = {dx}}
\int {{{{a} / {dx}}  {partial^{2} / partialz^{2} {partialx}}}} dx
\int \frac{d}{dx} x dx
\int d / dx x dx
\int_{{partial^{4} / partialx^{1} partialy^{3} {partial}}**{\sqrt[{oo}]{0}}}^{{{{-1} == {0}}*{({partial},{'str'},{a'})}*{{1} / {1}}}} {-{partial^{6} / partialy^{3} partialx^{3} {0}}} dx
\int {-{partial^{6} / partialy^{3} partialx^{3} {0}}} dx
\lim_{x \to \frac{lambda x, y, z: {-{0}}}{partial^{5} / partialz^{2} partialz^{1} partialx^{2} {Limit (a', x, 1)}}} {\arctan()}
-{{{{{{partialx},{partial},{oo},},{{dx},{-1.0},{a},},}}**{StrictGreaterThan({1.0})}} > {partial^{4} / partialz^{1} partialx^{2} partialy^{1} {{1.0}^{1}}}}
-{{{{{\sum_{x = 0}^{-1.0} {oo}} \cdot {({0})}}},}}
\int {{{{d}+{partialx}+{1}}} if {lambda x, y, z: {a}} else {{1} / {partialx}}} dx
{|{\log_{partial^{1} / partialy^{1} {{{0}*{'str'}}}}{[{{-1.0} / {'str'}}]}}|}
{\lim_{x \to -1.0} {dx}} > {{oo} if {-1.0} else {d} if {d} else {1}}
\frac{{-1.0} > {oo}}{\ln{-1.0}}
{{|{d}|}{{({1.0},{1})},{[{oo}]},},}
1/2 * {a+b} [lambda: {d}]
{{{'str'} < {1.0}} \cdot {({a'})} \cdot {{1} if {a'}}}
-{1.0 if partial else d if 1 else oo if 1.0 else 'str'}
{partial^{5} / partialy^{2} partialy^{2} partialy^{1} {partial}}^{{-1.0} > {d}}
{lambda x: {a}} if {{{'str'}*{a}*{1}}}
\int_{{-1.0} <= {1}}^{-{1}} {{-1.0} <= {1.0}} dx
{{({a'1.0})}+{{a}!}+{{d} if {1} else {dx}}}
\int_{{{a}+{a}+{0}}}^{{'str'} / {a}} {\int {1} dx} dx
lambda x: {lambda x, y: {oo}}
\sqrt[3]{({oo},{a'})}
Limit (\sum_{x = oo}^{partial} {-1.0}, x, \sec({-1.0},{-1},{partialx}))
{{a} = {partial}} if {{{oo}+{0}+{-1}}} else {\int {a} dx}
\sum_{x = {{1}*{d}*{oo}}}^{\exp({a'},{1})} {\log_{1.0}{a}}
lambda x: {{a} = {dx}}
{{{d}^{oo}}*{{a}^{d}}}
{{oo} if {oo}} = {is_mersenne_prime({'str'})}
\lim_{x \to 0} {sqrt(dx) + [lambda x, y: -1.0]}
{{\frac{\int_{a}^{1} {dx} dx}{{{oo} \cdot {d} \cdot {dx}}}}}
\int d/dx dx
(((-1)**partial)**({a_prime, oo, 'str'}))**-{-{0}}
Limit ({{{0}^{'str'}}  {\left|{a}\right|}  {({a},{a'})}}, x, lambda x: {{1}!})
\left(\left(\text{'str'} \right)! \le \left(\left(x, y \right) \mapsto -1.0 \right) \right) == \int_{\left[-1.0, \partial, -1 \right]}^{\log_{-1.0}\left(-1 \right)} \begin{cases} 1 & \text{for}\: \infty \\ 1.0 & \text{for}\: 1.0 \end{cases} \ dx
x^{-{{1} / {1.0}}}
cofactors( 1 , {lambda x: 1 = lambda: 2} )
({{{-{cse()}},{{{{partial} != {-1}}*{{{-1.0}  {1.0}}}}},{lambda: {{-1.0} == {dx}}},},{{\lim_{x \to \log_{0}{d}} {[{-1.0}]}},{partial^{7} / partialx^{3} partialy^{1} partialx^{3} {{partialx} if {a'} else {-1.0} if {a} else {d} if {1.0} else {partialx}}},{{lambda x, y, z: {oo}} = {\tanh()}},},{{partial^{3} / partialz^{3} {{oo} / {'str'}}},{({{{\left|{dx}\right|},{{a} if {d}},},{{-{oo}},{({{-1.0},{oo},{-1.0},})},},})},{partial^{5} / partialx^{1} partialy^{1} partialz^{3} {{-1}!}},},})
{\left|{a}\right|} if {\int {'str'} dx} else {({-1},{-1},{a})} if {\left|{1.0}\right|}
{lambda x: {{1.0} if {oo} else {1.0} if {oo}}} = {{{{partial} \cdot {partialx}}}**{{a}!}}
{Sum (\int {1} dx, (x, 0, 1))} dx
{{\sum_{x = \left|{0}\right|}^{\tan({-1.0})} {\int_{partialx}^{oo} {d} dx}}+{{{\lim_{x \to 1} {d}} \cdot {{{a'}+{-1}+{dx}}}}}+{{{{a} = {a'}}+{({dx0d})}+{{{dx}*{dx}*{a'}}}}}}
log(partialx*'str'*partialx) / log(Derivative(a, z, 3, y, 2))
dpartial
a, lambda: b = 1
\exp({a},{-1},{1})
x, y = lambda: 1, lambda: 2
doo
partial'
Sum(a*Integral(x, x), (x, 0, 1)) + 1*dx
(dx**p*artial)*Limit(sqrt(-1), x, 0**d)[(Matrix([[partialx]])), lcm_list()]
ln((a)**b)
a * \int dx + {\int dx dx}
1 if {a = x if z} else 0 if y
a, lambda: b = 1
a * [2]
sqrt(1, 2)
x*[][y]
lambda: x:
a*[x][y][z]
a*()**2
a*().t
a*()[2]
lambda*x:2
lambda*x, y:2
d**2e0/dx**2e0 x**3
y**z [w]
{y**z} [w]
x {y**z} [w]
{x y**z} [w]
\sqrt[{lambda x, y, z: {ConditionSet()}}]{x}
{1:2:3}[2]
{1:2:3}.x
None**-1.0**\[[\emptyset,],[0,],[\partial x,],] / {not \[None,\emptyset,]}
\int_\lim_{x \to 1} oo^{not 1e100}^\{{partialx+dx},{\partialx*.1},partialx!} \log_\left|partialx\right|{1 \cdot False} dx
{{\[[{{\emptyset} = {.1}},{\[[{\emptyset},],[{"str"},],]},],]} if {-{{\partial x}!}} else {{{{False}!} and {{{\partial x}||{oo}||{"str"}}}}}}
{\int {{{{{1e-100}  {1}  {partialx}}}*{{True}^{\tilde\infty }}}} dx}
{{{{-{"str"}} : {lambda x, y: {\partialx}}} \cdot {{not {{'str'} : {1.} : {.1}}}}}}
{-{-1}}^{{1} : {\partial x} : {0}}
{{{\sum_{x = {{a'} : {"str"} : {True}}}^{({\partial x})} {[]}}||{{{1.0} : {False} : {\emptyset}} [{{-1} == {\partialx}}]}||{{{{oo} if {None} else {\partialx}}^^{{.1} [{oo}]}}}}}
{lambda x, y, z: {lambda x, y: {{{-1.0}&&{False}&&{d}}}}}
\int {{\partialx} : {d} : {1.0}} dx
{\lim_{x \to {{1} : {1e+100} : {.1}}} {({\partial x},{\partialx})}}
x + {-1 2}
x + {-1 * 2}
x - {{1 2} 3}
x - {{1 * 2} * 3}
{sqrt{{{{not {1.}}}+{\int_{a'}^{-1.0} {str} dx}+{{{-1} \cdot {1e100} \cdot {\infty zoo}}}}}}
x - a b!
\int x * \frac{y}{z} \ dx
1+{{-1 * 2}+1}
-1 * a
x - y! ()
-x * a!
a * {-b} * c
a * {-b} c
--1 * x
---1 * x
a**{-1 [y]}
-{\int x dx} + y * dz
""".strip ().split ('\n')

_ALLOW_LAMB = 1

def expr_eq (): # BROKEN?
	return f'{expr (_ALLOW_LAMB)} {choice (["=", "==", "!=", "<", "<=", ">", ">=", " in ", " not in "])} {expr (_ALLOW_LAMB)}'

def expr_curly ():
	return '{' + ','.join (f'{expr (1)}' for i in range (randrange (4))) + '}'

def expr_paren ():
	return '(' + ','.join (f'{expr (1)}' for i in range (randrange (4))) + ')'

def expr_brack ():
	return '[' + ','.join (f'{expr (1)}' for i in range (randrange (4))) + ']'

def expr_abs ():
	return f'\\left|{expr (1)}\\right|'

def expr_minus ():
	return f'-{expr (_ALLOW_LAMB)}'

def expr_fact ():
	return f'{expr (_ALLOW_LAMB)}!'

def expr_add ():
	return '{' + '+'.join (f'{expr (_ALLOW_LAMB)}' for i in range (randrange (2, 4))) + '}'

def expr_mul_imp ():
	return '{' + '  '.join (f'{expr (_ALLOW_LAMB)}' for i in range (randrange (2, 4))) + '}'

def expr_mul_exp ():
	return '{' + '*'.join (f'{expr (_ALLOW_LAMB)}' for i in range (randrange (2, 4))) + '}'

def expr_mul_cdot ():
	return '{' + ' \\cdot '.join (f'{expr (_ALLOW_LAMB)}' for i in range (randrange (2, 4))) + '}'

def expr_div ():
	return f'{expr (_ALLOW_LAMB)} / {expr (_ALLOW_LAMB)}'

def expr_frac ():
	return f'\\frac{expr (_ALLOW_LAMB)}{expr (_ALLOW_LAMB)}'

def expr_caret ():
	return f'{expr (_ALLOW_LAMB)}^{expr (_ALLOW_LAMB)}'

def expr_dblstar ():
	return f'{expr (_ALLOW_LAMB)}**{expr (_ALLOW_LAMB)}'

def expr_log ():
	return \
			choice (['', '\\']) + f'{choice (["ln", "log"])}{expr (_ALLOW_LAMB)}' \
			if random () >= 0.5 else \
			f'\\log_{expr (_ALLOW_LAMB)}{expr (_ALLOW_LAMB)}'

def expr_sqrt ():
	return \
			choice (['', '\\']) + f'sqrt{expr (_ALLOW_LAMB)}' \
			if random () >= 0.5 else \
			f'\\sqrt[{expr (_ALLOW_LAMB)}]{expr (_ALLOW_LAMB)}'

_FORBIDDEN_FUNCS = set (sxlat.XLAT_FUNC2AST_TEX) | set (sxlat.XLAT_FUNC2AST_NAT) | set (sxlat.XLAT_FUNC2AST_PY) | set (sxlat._XLAT_FUNC2TEX) | {'Gamma'}

def expr_func ():
	while 1:
		py = choice (list (AST.Func.PY))

		if py not in _FORBIDDEN_FUNCS:
			break

	while 1:
		tex = choice (list (AST.Func.TEX))

		if tex not in _FORBIDDEN_FUNCS:
			break

	return \
			'\\' + f'{tex}{expr_paren ()}' \
			if random () >= 0.5 else \
			f'{py}{expr_paren ()}' \

def expr_lim ():
	return \
			'\\lim_{x \\to ' + f'{expr (_ALLOW_LAMB)}}} {expr (_ALLOW_LAMB)}' \
			if random () >= 0.5 else \
			f'Limit ({expr (_ALLOW_LAMB)}, x, {expr (_ALLOW_LAMB)})'

def expr_sum ():
	return \
			'\\sum_{x = ' + f'{expr (_ALLOW_LAMB)}}}^{expr (_ALLOW_LAMB)} {expr (_ALLOW_LAMB)}' \
			if random () >= 0.5 else \
			f'Sum ({expr (_ALLOW_LAMB)}, (x, {expr (_ALLOW_LAMB)}, {expr (_ALLOW_LAMB)}))'

def expr_diff ():
	d  = 'd' # choice (['d', 'partial'])
	p  = 0
	dv = []

	for _ in range (randrange (1, 4)):
		n  = randrange (1, 4)
		p += n

		dv.append ((choice (['x', 'y', 'z']), n))

	return \
			f'{d}^{{{p}}} / {" ".join (f"{d + v}^{{{dp}}}" for v, dp in dv)} {expr (_ALLOW_LAMB)}'
			# if random () >= 0.5 else \
			# f'Derivative ({expr (_ALLOW_LAMB)}, {", ".join (f"{v}, {dp}" for v, dp in dv)})'

def expr_intg ():
	return \
			f'\\int_{expr (_ALLOW_LAMB)}^{expr (_ALLOW_LAMB)} {expr (_ALLOW_LAMB)} dx' \
			if random () >= 0.5 else \
			f'\\int {expr (_ALLOW_LAMB)} dx'

def expr_vec ():
	return '\\[' + ','.join (f'{expr (1)}' for i in range (randrange (1, 4))) + ',]'

def expr_mat ():
	cols = randrange (1, 4)

	return '\\[' + ','.join ('[' + ','.join (f'{expr (1)}' for j in range (cols)) + ',]' for i in range (randrange (1, 4))) + ',]'

def expr_piece ():
	p = [f'{expr (1)} if {expr (_ALLOW_LAMB)}']

	for _ in range (randrange (3)):
		p.append (f'else {expr (1)} if {expr (_ALLOW_LAMB)}')

	if random () >= 0.5:
		p.append (f'else {expr (1)}')

	return ' '.join (p)

def expr_lamb ():
	return f'lambda{choice (["", " x", " x, y", " x, y, z"])}: {expr (_ALLOW_LAMB)}'

def expr_idx ():
	if random () >= 0.5:
		return f'{expr (1)} [{expr (1)}]'
	elif random () >= 0.5:
		return f'{expr (1)} [{expr (1)}, {expr (1)}]'
	else:
		return f'{expr (1)} [{expr (1)}, {expr (1)}, {expr (1)}]'

def expr_slice ():
	if random () >= 0.5:
		return f'{expr (1)} : {expr (1)}'
	else:
		return f'{expr (1)} : {expr (1)} : {expr (1)}'

def expr_set ():
	return '\\{' + ','.join (f'{expr (1)}' for i in range (randrange (4))) + '}'

def expr_dict ():
	return '{' + ','.join (f'{choice (_TERMS)} : {expr (1)}' for i in range (randrange (4))) + '}'

def expr_union ():
	return '{' + '||'.join (f'{expr (_ALLOW_LAMB)}' for i in range (randrange (2, 4))) + '}'

def expr_sdiff ():
	return '{' + '^^'.join (f'{expr (_ALLOW_LAMB)}' for i in range (randrange (2, 4))) + '}'

def expr_xsect ():
	return '{' + '&&'.join (f'{expr (_ALLOW_LAMB)}' for i in range (randrange (2, 4))) + '}'

def expr_or ():
	return '{' + ' or '.join (f'{expr (_ALLOW_LAMB)}' for i in range (randrange (2, 4))) + '}'

def expr_and ():
	return '{' + ' and '.join (f'{expr (_ALLOW_LAMB)}' for i in range (randrange (2, 4))) + '}'

def expr_not ():
	return f'{{not {expr (1)}}}'

#...............................................................................................
EXPRS = [va [1] for va in filter (lambda va: va [0] [:5] == 'expr_', globals ().items ())]

def expr (allow_lamb = 0, depth = None):
	global DEPTH, CURLYS

	if depth is not None:
		DEPTH = depth

	if DEPTH <= 0:
		ret = choice (_TERMS)

	else:
		DEPTH -= 1

		while 1:
			e = choice (EXPRS)

			if e is not expr_lamb or allow_lamb:
				break

		ret    = e ()
		DEPTH += 1

	return f'{{{ret}}}' if CURLYS else ret

def fix_vars (ast):
	if not isinstance (ast, AST):
		return ast

	if ast == ('@', '_'): # remove LAST_VAR with other innocuous var
		return AST ('@', 'x')

	return AST (*tuple (fix_vars (a) for a in ast))

def fix_rest (ast):
	if not isinstance (ast, AST):
		return ast

	if ast.is_comma: # wrap tuples in parens
		return AST ('(', AST (*tuple (fix_vars (a) for a in ast)))

	return AST (*tuple (fix_vars (a) for a in ast))

def process (ast):
	if not isinstance (ast, AST):
		return ast

	if ast.is_partial:
		return ast.as_diff

	if ast.is_paren:
		return process (ast.paren)

	return AST (*tuple (process (a) for a in ast))

def flatten (ast):
	if not isinstance (ast, AST):
		return ast

	t = [flatten (a) for a in ast]

	if ast.op in {'+', '*', '||', '^^', '&&', 'or', 'and'}:
		t = (ast.op, tuple (sum (((m,) if m.op != ast.op else m [1] for m in t [1]), ())))

	return AST (*t)

#...............................................................................................
CURLYS = True
parser = sparser.Parser ()

sym.set_pyS (False)

def parse (text):
	t0  = time.process_time ()
	ret = parser.parse (text)
	t   = time.process_time () - t0

	if t > 2:
		print (f'\n{text}', file = sys.stderr)

	return ret

def test (argv = None):
	global DEPTH, CURLYS

	_DEPTH  = 3
	single  = None
	opts, _ = getopt (sys.argv [1:] if argv is None else argv, 'tnpixd:e:', ['tex', 'nat', 'py', 'dump', 'show', 'inf', 'infinite', 'xlat', 'nc', 'nocurlys', 'depth=', 'expr='])
	xlat    = ('-x', '') in opts or ('--xlat', '') in opts

	for opt, arg in opts:
		if opt in ('-d', '--depth'):
			_DEPTH = int (arg)
		elif opt in ('-e', '--expr'):
			single = [arg]

	if ('--dump', '') in opts:
		DEPTH = 0

		for e in EXPRS:
			print (e ())

		sys.exit (0)

	dotex = ('--tex', '') in opts or ('-t', '') in opts
	donat = ('--nat', '') in opts or ('-n', '') in opts
	dopy  = ('--py', '') in opts or ('-p', '') in opts

	if not (dotex or donat or dopy):
		dotex = donat = dopy = True

	CURLYS = not (('--nc', '') in opts or ('--nocurlys', '') in opts)

	if (('-i', '') in opts or ('--inf', '') in opts or ('--infinite', '') in opts) and not single:
		expr_func = lambda: expr (1, _DEPTH)
	else:
		expr_func = iter (single or _EXPRESSIONS).__next__

	try:
		while 1:
			text              = expr_func ()
			ast, erridx, auto = parse (text)

			if not ast or erridx or auto:
				print ()
				print ('Invalid:', text)

				continue

			ast = flatten (ast)
			ast = fix_rest (ast)

			if ('--show', '') in opts:
				print ()
				print ('-' * 78)
				print ()
				print ('text:', text)

			if dopy:
				if not CURLYS:
					ast = fix_vars (ast)

				text              = sym.ast2py (ast, xlat = xlat)
				ast, erridx, auto = parse (text)

				if not ast or erridx or auto:
					print ()
					print ('Invalid:', text)

					continue

				ast = fix_rest (ast)

			tex = dotex and sym.ast2tex (ast, xlat = xlat)
			nat = donat and sym.ast2nat (ast, xlat = xlat)
			py  = dopy and sym.ast2py (ast, xlat = xlat)

			if ('--show', '') in opts:
				print ()
				print ('text:', text)
				print ()
				print ('ast: ', ast)
				print ()
				print ('tex: ', tex)
				print ()
				print ('nat: ', nat)
				print ()
				print ('py:  ', py)

			ast_tex = dotex and parse (tex) [0]
			ast_nat = donat and parse (nat) [0]
			ast_py  = dopy and parse (py) [0]
			ast_srp = process (ast)
			ast_tex = dotex and process (ast_tex)
			ast_nat = donat and process (ast_nat)
			ast_py  = dopy and process (ast_py)

			if (dotex and ast_tex != ast_srp) or (donat and ast_nat != ast_srp) or (dopy and ast_py != ast_srp):
				print ()
				print ('!' * 78)
				print ('text:', text)
				print ()
				print ('ast: ', ast_srp)

				if dotex and ast_tex != ast_srp:
					print ()
					print ('tex: ', ast_tex)

				if donat and ast_nat != ast_srp:
					print ()
					print ('nat: ', ast_nat)

				if dopy and ast_py != ast_srp:
					print ()
					print ('py:  ', ast_py)

				print ()
				print ('FAILED!')

				break

	except (Exception, KeyboardInterrupt) as e:
		if isinstance (e, StopIteration):
			return True

		print ()
		print ('!' * 78)
		print ('text:   ', text)
		print ('ast:    ', ast)
		print ('ast_srp:', ast_srp)
		print ('ast_tex:', ast_tex)
		print ('ast_nat:', ast_nat)
		print ('ast_py: ', ast_py)
		print ()

		if not isinstance (e, KeyboardInterrupt):
			raise

if __name__ == '__main__':
	# test (['-nt', '-e', 'x + {-1 * 2}'])
	test ()
