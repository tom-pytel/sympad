# TODO: \int_0^\infty e^{-st} dt, sp.Piecewise

import re
import sympy as sp
sp.numbers = sp.numbers # pylint medication

import aststuff as ass

_FUNCS_PY_AND_TEX = set (ass.FUNCS_PY_AND_TEX)
_FUNCS_ALL_PY     = set (ass.FUNCS_PY) | _FUNCS_PY_AND_TEX

_rec_var_diff_or_part_start = re.compile (r'^(?:d(?=[^_])|\\partial )')

#...............................................................................................
def ast2tex (ast): # abstract syntax tree -> LaTeX text
	return _ast2tex_funcs [ast [0]] (ast)

def _ast2tex_curly (ast):
	return f'{ast2tex (ast)}' if ass.is_single_unit (ast) else f'{{{ast2tex (ast)}}}'

def _ast2tex_paren (ast):
	return f'\\left({ast2tex (ast)} \\right)' if ast [0] != '(' else ast2tex (ast)

def _ast2tex_paren_mul_exp (ast, ret_has = False, also = {'+'}):
	if ast [0] == '*':
		s, has = _ast2tex_mul (ast, True)
	else:
		s, has = ast2tex (ast), ast [0] in also

	s = f'\\left({s} \\right)' if has else s

	return (s, has) if ret_has else s

_rec_ast2tex_num = re.compile (r'^(-?\d*\.?\d*)[eE](?:(-\d+)|\+?(\d+))$')

def _ast2tex_num (ast):
	m = _rec_ast2tex_num.match (ast [1])

	return ast [1] if not m else f'{m.group (1)} \\cdot 10^{_ast2tex_curly (("#", m.group (2) or m.group (3)))}'

def _ast2tex_mul (ast, ret_has = False):
	t   = []
	has = False

	for i in range (1, len (ast)):
		s = f'{_ast2tex_paren (ast [i]) if ast [i] [0] == "+" or (i != 1 and ass.is_neg (ast [i])) else ast2tex (ast [i])}'

		if i != 1 and (ast [i] [0] in {'!', '#', 'lim', 'sum', 'int'} or ast [i] == ('@', '') or \
				(ast [i] [0] == '^' and ass.is_pos_num (ast [i] [1])) or \
				(ast [i] [0] in {'/', 'diff'} and ast [i - 1] [0] in {'#', '/', 'diff'})):
			t.append (f' \\cdot {s}')
			has = True

		elif i != 1 and (ast [i - 1] in {('@', 'd'), ('@', '\\partial')} or ast [i - 1] [0] == 'sqrt' or \
				(ast [i] [0] == '@' and _rec_var_diff_or_part_start.match (ast [i]  [1])) or \
				(ast [i - 1] [0] == '@' and _rec_var_diff_or_part_start.match (ast [i - 1] [1]))):
			t.append (f'\\ {s}')

		else:
			t.append (f'{"" if i == 1 else " "}{s}')

	return (''.join (t), has) if ret_has else ''.join (t)

def _ast2tex_pow (ast):
	b = ast2tex (ast [1])
	p = _ast2tex_curly (ast [2])

	if ast [1] [0] == 'trigh' and ast [1] [1] [0] != 'a' and ass.is_single_unit (ast [2]):
		i = len (ast [1] [1]) + (15 if ast [1] [1] in {'sech', 'csch'} else 1)

		return f'{b [:i]}^{p}{b [i:]}'

	if ast [1] [0] in {'(', '|', '@'} or ass.is_pos_num (ast [1]):
		return f'{b}^{p}'

	return f'\\left({b} \\right)^{p}'

def _ast2tex_log (ast):
	return \
			f'\\log{_ast2tex_paren (ast [1])}' \
			if len (ast) == 2 else \
			f'\\log_{_ast2tex_curly (ast [2])}{_ast2tex_paren (ast [1])}'

def _ast2tex_trigh (ast):
	n = (f'\\operatorname{{{ast [1] [1:]}}}^{{-1}}' \
			if ast [1] in {'asech', 'acsch'} else \
			f'\\{ast [1] [1:]}^{{-1}}') \
			if ast [1] [0] == 'a' else \
			(f'\\operatorname{{{ast [1]}}}' if ast [1] in {'sech', 'csch'} else f'\\{ast [1]}')

	return f'{n}{_ast2tex_paren (ast [2])}'

def _ast2tex_func (ast):
	return \
			f'\\{ast [1]}{_ast2tex_paren (ast [2])}' \
			if ast [1] in _FUNCS_PY_AND_TEX else \
			f'\\operatorname{{{ast [1]}}}{_ast2tex_paren (ast [2])}'

def _ast2tex_lim (ast):
	s = ast2tex (ast [3]) if len (ast) == 4 else ast2tex (('^', ast [3], ('#', '1'))) [:-1] + ast [4]

	return f'\\lim_{{{ast2tex (ast [2])} \\to {s}}} {_ast2tex_paren_mul_exp (ast [1])}'

def _ast2tex_sum (ast):
	return f'\\sum_{{{ast2tex (ast [2])} = {ast2tex (ast [3])}}}^{_ast2tex_curly (ast [4])} {_ast2tex_paren_mul_exp (ast [1])}' \

_ast2tex_paren_mul_exp

_diff_var_single_start_rec = re.compile (r'^d(?=[^_])')

def _ast2tex_diff (ast):
	ds = set ()
	p  = 0

	for i in range (2, len (ast)):
		if ast [i] [0] == '@':
			ds.add (ast [i] [1])
			p += 1
		else: # ast [i] = ('^', ('@', 'differential'), ('#', 'int'))
			ds.add (ast [i] [1] [1])
			p += int (ast [i] [2] [1])

	if len (ds) == 1 and ds.pop () [0] != '\\': # is not '\\partial'
		return f'\\frac{{d{"" if p == 1 else f"^{p}"}}}{{{"".join (ast2tex (ast [i]) for i in range (2, len (ast)))}}}{_ast2tex_paren (ast [1])}'

	else:
		s = ''.join (_diff_var_single_start_rec.sub ('\\partial ', ast2tex (ast [i])) for i in range (2, len (ast)))

		return f'\\frac{{\\partial{"" if p == 1 else f"^{p}"}}}{{{s}}}{_ast2tex_paren (ast [1])}'

def _ast2tex_int (ast):
	l = len (ast)

	return \
			f'\\int \\ {ast2tex (ast [1])}' \
			if l == 2 else \
			f'\\int {ast2tex (ast [1])} \\ {ast2tex (ast [2])}' \
			if l == 3 else \
			f'\\int_{_ast2tex_curly (ast [2])}^{_ast2tex_curly (ast [3])} \\ {ast2tex (ast [1])}' \
			if l == 4 else \
			f'\\int_{_ast2tex_curly (ast [3])}^{_ast2tex_curly (ast [4])} {ast2tex (ast [1])} \\ {ast2tex (ast [2])}' \

_ast2tex_funcs = {
	'#': _ast2tex_num,
	'@': lambda ast: str (ast [1]) if ast [1] else '{}',
	'(': lambda ast: f'\\left({ast2tex (ast [1])} \\right)',
	'|': lambda ast: f'\\left|{ast2tex (ast [1])} \\right|',
	'-': lambda ast: f'-{_ast2tex_paren (ast [1])}' if ast [1] [0] == '+' else f'-{ast2tex (ast [1])}',
	'!': lambda ast: f'{_ast2tex_paren (ast [1])}!' if (ast [1] [0] not in {'#', '@', '(', '|', '!', '^'} or ass.is_neg_num (ast [1])) else f'{ast2tex (ast [1])}!',
	'+': lambda ast: ' + '.join (ast2tex (n) for n in ast [1:]).replace (' + -', ' - '),
	'*': _ast2tex_mul,
	'/': lambda ast: f'\\frac{{{ast2tex (ast [1])}}}{{{ast2tex (ast [2])}}}',
	'^': _ast2tex_pow,
	'log': _ast2tex_log,
	'sqrt': lambda ast: f'\\sqrt{{{ast2tex (ast [1])}}}' if len (ast) == 2 else f'\\sqrt[{ast2tex (ast [2])}]{{{ast2tex (ast [1])}}}',
	'trigh': _ast2tex_trigh,
	'func': _ast2tex_func,
	'lim': _ast2tex_lim,
	'sum': _ast2tex_sum,
	'diff': _ast2tex_diff,
	'int': _ast2tex_int,
}

#...............................................................................................
def ast2simple (ast): # abstract syntax tree -> simple text
	return _ast2simple_funcs [ast [0]] (ast)

def _ast2simple_curly (ast):
	return f'{ast2simple (ast)}' if ass.is_single_unit (ast) else f'{{{ast2simple (ast)}}}'

def _ast2simple_paren (ast):
	return f'({ast2simple (ast)})' if ast [0] != '(' else ast2simple (ast)

def _ast2simple_paren_mul_exp (ast, ret_has = False, also = {'+'}):
	if ast [0] == '*':
		s, has = _ast2simple_mul (ast, True)
	else:
		s, has = ast2simple (ast), ast [0] in also

	s = f'({s})' if has else s

	return (s, has) if ret_has else s

def _ast2simple_mul (ast, ret_has = False):
	t   = []
	has = False

	for i in range (1, len (ast)):
		s = f'{_ast2simple_paren (ast [i]) if ast [i] [0] == "+" or (i != 1 and ass.is_neg (ast [i])) else ast2simple (ast [i])}'

		if i != 1 and (ast [i] [0] in {'!', '#', 'lim', 'sum', 'int'} or ast [i] == ('@', '') or \
				(ast [i] [0] == '^' and ass.is_pos_num (ast [i] [1])) or \
				ast [i] [0] in {'/', 'diff'} or ast [i - 1] [0] in {'/', 'diff'}):
			t.append (f' * {ast2simple (ast [i])}')
			has = True

		elif i != 1 and (ast [i - 1] in {('@', 'd'), ('@', '\\partial')} or \
				(ast [i] [0] not in {'#', '@', '(', '|', '^'} or ast [i - 1] [0] not in {'#', '@', '(', '|', '^'}) or \
				(ast [i] [0] == '@' and _rec_var_diff_or_part_start.match (ast [i] [1])) or \
				(ast [i - 1] [0] == '@' and _rec_var_diff_or_part_start.match (ast [i - 1] [1]))):
			t.append (f' {s}')

		else:
			t.append (s)

	return (''.join (t), has) if ret_has else ''.join (t)

def _ast2simple_div (ast):
	n, ns = _ast2simple_paren_mul_exp (ast [1], True, {'+', '/', 'lim', 'sum', 'diff'})
	d, ds = _ast2simple_paren_mul_exp (ast [2], True, {'+', '/', 'lim', 'sum', 'diff'})

	return f'{n}{" / " if ns or ds else "/"}{d}'

def _ast2simple_pow (ast):
	b = ast2simple (ast [1])
	p = f'{ast2simple (ast [2])}' if ast [2] [0] in {'+', '*', '/', 'lim', 'sum', 'diff', 'int'} else ast2simple (ast [2])

	if ast [1] [0] == 'trigh' and ast [1] [1] [0] != 'a' and ass.is_single_unit (ast [2]):
		i = len (ast [1] [1]) + 1

		return f'{b [:i]}**{p}{b [i:]}'

	if ast [1] [0] in {'@', '(', '|'} or ass.is_pos_num (ast [1]):
		return f'{b}**{p}'

	return f'({b})**{p}'

def _ast2simple_log (ast):
	return \
			f'log{_ast2simple_paren (ast [1])}' \
			if len (ast) == 2 else \
			f'log_{_ast2simple_curly (ast [2])}{_ast2simple_paren (ast [1])}'

def _ast2simple_trigh (ast):
	return f'{ast [1]}{_ast2simple_paren (ast [2])}'

def _ast2simple_func (ast):
	return \
			f'{ast [1]}{_ast2simple_paren (ast [2])}' \
			if ast [1] in _FUNCS_ALL_PY else \
			f'${ast [1]}{_ast2simple_paren (ast [2])}'

def _ast2simple_lim (ast):
	s = ast2simple (ast [3]) if len (ast) == 4 else ast2simple (('^', ast [3], ('#', '0'))) [:-1] + ast [4]

	return f'\\lim_{{{ast2simple (ast [2])} \\to {s}}} {_ast2simple_paren_mul_exp (ast [1])}'

def _ast2simple_sum (ast):
	return f'\\sum_{{{ast2simple (ast [2])}={ast2simple (ast [3])}}}^{_ast2simple_curly (ast [4])} {_ast2simple_paren_mul_exp (ast [1])}' \

_ast2simple_diff_single_rec = re.compile ('^d')

def _ast2simple_diff (ast):
	ds = set ()
	p  = 0

	for i in range (2, len (ast)):
		if ast [i] [0] == '@':
			ds.add (ast [i] [1])
			p += 1
		else: # ast [i] = ('^', ('@', 'differential'), ('#', 'int'))
			ds.add (ast [i] [1] [1])
			p += int (ast [i] [2] [1])

	if len (ds) == 1 and ds.pop () [0] != '\\': # is not '\\partial'
		return f'd{"" if p == 1 else f"^{p}"}/{"".join (ast2simple (ast [i]) for i in range (2, len (ast)))}{_ast2simple_paren (ast [1])}'

	else:
		s = ''.join (_ast2simple_diff_single_rec.sub ('\\partial ', ast2simple (ast [i])) for i in range (2, len (ast)))

		return f'\\partial{"" if p == 1 else f"^{p}"}/{s}{_ast2simple_paren (ast [1])}'

def _ast2simple_int (ast):
	l = len (ast)

	return \
			f'\\int {ast2simple (ast [1])}' \
			if l == 2 else \
			f'\\int {ast2simple (ast [1])} {ast2simple (ast [2])}' \
			if l == 3 else \
			f'\\int_{_ast2simple_curly (ast [2])}^{_ast2simple_curly (ast [3])} {ast2simple (ast [1])}' \
			if l == 4 else \
			f'\\int_{_ast2simple_curly (ast [3])}^{_ast2simple_curly (ast [4])} {ast2simple (ast [1])} {ast2simple (ast [2])}' \

_ast2simple_funcs = {
	'#': lambda ast: ast [1],
	'@': lambda ast: str (ast [1]) if ast [1] else '',
	'(': lambda ast: f'({ast2simple (ast [1])})',
	'|': lambda ast: f'|{ast2simple (ast [1])}|',
	'-': lambda ast: f'-{_ast2simple_paren (ast [1])}' if ast [1] [0] == '+' else f'-{ast2simple (ast [1])}',
	'!': lambda ast: f'{_ast2simple_paren (ast [1])}!' if (ast [1] [0] not in {'#', '@', '(', '|', '!', '^'} or ass.is_neg_num (ast [1])) else f'{ast2simple (ast [1])}!',
	'+': lambda ast: ' + '.join (ast2simple (n) for n in ast [1:]).replace (' + -', ' - '),
	'*': _ast2simple_mul,
	'/': _ast2simple_div,
	'^': _ast2simple_pow,
	'log': _ast2simple_log,
	'sqrt': lambda ast: f'\\sqrt{{{ast2simple (ast [1])}}}' if len (ast) == 2 else f'\\sqrt[{ast2simple (ast [2])}]{{{ast2simple (ast [1])}}}',
	'trigh': _ast2simple_trigh,
	'func': _ast2simple_func,
	'lim': _ast2simple_lim,
	'sum': _ast2simple_sum,
	'diff': _ast2simple_diff,
	'int': _ast2simple_int,
}

#...............................................................................................
def ast2py (ast): # abstract syntax tree -> python code text
	return _ast2py_funcs [ast [0]] (ast)

def _ast2py_curly (ast):
	return \
			_ast2py_paren (ast) \
			if ast [0] in {'+', '*', '/'} or ass.is_neg_num (ast) or (ast [0] == 'log' and len (ast) > 2) else \
			ast2py (ast)

def _ast2py_paren (ast):
	return f'({ast2py (ast)})' if ast [0] != '(' else ast2py (ast)

def _ast2py_div (ast):
	n = _ast2py_curly (ast [1])
	d = _ast2py_curly (ast [2])

	return f'{n}{" / " if ast [1] [0] not in {"#", "@", "-"} or ast [2] [0] not in {"#", "@", "-"} else "/"}{d}'

def _ast2py_pow (ast):
	b = _ast2py_curly (ast [1])
	e = _ast2py_curly (ast [2])

	return f'{b}**{e}'

def _ast2py_log (ast):
	return \
			f'log{_ast2py_paren (ast [1])}' \
			if len (ast) == 2 else \
			f'log{_ast2py_paren (ast [1])} / log{_ast2py_paren (ast [2])}' \

def _ast2py_lim (ast):
	return \
		f'''Limit({ast2py (ast [1])}, {ast2py (ast [2])}, {ast2py (ast [3])}''' \
		f'''{", dir='+-'" if len (ast) == 4 else ", dir='-'" if ast [4] == '-' else ""})'''

def _ast2py_diff (ast):
	args = sum ((
			(ast2py (('@', _rec_var_diff_or_part_start.sub ('', n [1]))),) \
			if n [0] == '@' else \
			(ast2py (('@', _rec_var_diff_or_part_start.sub ('', n [1] [1]))), str (n [2] [1])) \
			for n in ast [2:] \
			), ())

	return f'Derivative({ast2py (ast [1])}, {", ".join (args)})'

def _ast2py_int (ast):
	l = len (ast)

	return \
			f'Integral(1, {ast2py (("@", _rec_var_diff_or_part_start.sub ("", ast [1] [1])))})' \
			if l == 2 else \
			f'Integral({ast2py (ast [1])}, {ast2py (("@", _rec_var_diff_or_part_start.sub ("", ast [2] [1])))})' \
			if l == 3 else \
			f'Integral(1, ({ast2py (("@", _rec_var_diff_or_part_start.sub ("", ast [1] [1])))}, {ast2py (ast [2])}, {ast2py (ast [3])}))' \
			if l == 4 else \
			f'Integral({ast2py (ast [1])}, ({ast2py (("@", _rec_var_diff_or_part_start.sub ("", ast [2] [1])))}, {ast2py (ast [3])}, {ast2py (ast [4])}))'

_rec_ast2py_varname_sanitize = re.compile (r'\{|\}')

_ast2py_funcs = {
	'#': lambda ast: ast [1],
	'@': lambda ast: _rec_ast2py_varname_sanitize.sub ('_', ast [1]).replace ('\\infty', 'oo').replace ('\\', '').replace ("'", '_prime'),
	'(': lambda ast: f'({ast2py (ast [1])})',
	'|': lambda ast: f'abs({ast2py (ast [1])})',
	'-': lambda ast: f'-{ast2py (ast [1])}',
	'!': lambda ast: f'factorial({ast2py (ast [1])})',
	'+': lambda ast: ' + '.join (ast2py (n) for n in ast [1:]).replace (' + -', ' - '),
	'*': lambda ast: '*'.join (_ast2py_paren (n) if n [0] == "+" else ast2py (n) for n in ast [1:]),
	'/': _ast2py_div,
	'^': _ast2py_pow,
	'log': _ast2py_log,
	'sqrt': lambda ast: f'sqrt{_ast2py_paren (ast [1])}' if len (ast) == 2 else ast2py (('^', ast [1], ('/', ('#', '1'), ast [2]))),
	'trigh': lambda ast: f'{ast [1]}({ast2py (ast [2])})',
	'func': lambda ast: f'{ast [1]}({ast2py (ast [2])})',
	'lim': _ast2py_lim,
	'sum': lambda ast: f'Sum({ast2py (ast [1])}, ({ast2py (ast [2])}, {ast2py (ast [3])}, {ast2py (ast [4])}))',
	'diff': _ast2py_diff,
	'int': _ast2py_int,
}

#...............................................................................................
def ast2spt (ast): # abstract syntax tree -> SymPy tree (expression)
	return _ast2spt_funcs [ast [0]] (ast)

def _ast2spt_diff (ast):
	args = sum ((
			(ast2spt (('@', _rec_var_diff_or_part_start.sub ('', n [1]))),) \
			if n [0] == '@' else \
			(ast2spt (('@', _rec_var_diff_or_part_start.sub ('', n [1] [1]))), sp.Integer (n [2] [1])) \
			for n in ast [2:] \
			), ())

	return sp.diff (ast2spt (ast [1]), *args)

def _ast2spt_int (ast):
	l = len (ast)

	return \
			sp.integrate (1, ast2spt (('@', _rec_var_diff_or_part_start.sub ('', ast [1] [1])))) \
			if l == 2 else \
			sp.integrate (ast2spt (ast [1]), ast2spt (('@', _rec_var_diff_or_part_start.sub ('', ast [2] [1])))) \
			if l == 3 else \
			sp.integrate (1, (ast2spt (('@', _rec_var_diff_or_part_start.sub ('', ast [1] [1]))), ast2spt (ast [2]), ast2spt (ast [3]))) \
			if l == 4 else \
			sp.integrate (ast2spt (ast [1]), (ast2spt (('@', _rec_var_diff_or_part_start.sub ('', ast [2] [1]))), ast2spt (ast [3]), ast2spt (ast [4])))

_ast2spt_consts = {
	'i': sp.I,
	'\\pi': sp.pi,
	'e': sp.E,
	'\\infty': sp.oo,
}

_ast2spt_func_alias = {
	'?': 'N',
}

_ast2spt_funcs = {
	'#': lambda ast: sp.Integer (ast [1]) if ass.is_int_text (ast [1]) else sp.Float (ast [1]),
	'@': lambda ast: _ast2spt_consts.get (ast [1], sp.Symbol (ast [1])),
	'(': lambda ast: ast2spt (ast [1]),
	'|': lambda ast: sp.Abs (ast2spt (ast [1])),
	'-': lambda ast: -ast2spt (ast [1]),
	'!': lambda ast: sp.factorial (ast2spt (ast [1])),
	'+': lambda ast: sp.Add (*(ast2spt (n) for n in ast [1:])),
	'*': lambda ast: sp.Mul (*(ast2spt (n) for n in ast [1:])),
	'/': lambda ast: sp.Mul (ast2spt (ast [1]), sp.Pow (ast2spt (ast [2]), -1)),
	'^': lambda ast: sp.Pow (ast2spt (ast [1]), ast2spt (ast [2])),
	'log': lambda ast: sp.log (ast2spt (ast [1])) if len (ast) == 2 else sp.log (ast2spt (ast [1]), ast2spt (ast [2])),
	'sqrt': lambda ast: sp.Pow (ast2spt (ast [1]), sp.Pow (2, -1)) if len (ast) == 2 else sp.Pow (ast2spt (ast [1]), sp.Pow (ast2spt (ast [2]), -1)),
	'trigh': lambda ast: getattr (sp, ast [1]) (ast2spt (ast [2])),
	'func': lambda ast: getattr (sp, _ast2spt_func_alias.get (ast [1], ast [1])) (ast2spt (ast [2])),
	'lim': lambda ast: sp.limit (ast2spt (ast [1]), ast2spt (ast [2]), ast2spt (ast [3]), dir = '+-' if len (ast) == 4 else ast [4]),
	'sum': lambda ast: sp.Sum (ast2spt (ast [1]), (ast2spt (ast [2]), ast2spt (ast [3]), ast2spt (ast [4]))).doit (),
	'diff': _ast2spt_diff,
	'int': _ast2spt_int,
}

#...............................................................................................
def spt2ast (spt): # SymPy tree (expression) -> abstract syntax tree
	for cls in spt.__class__.__mro__:
		func = _spt2ast_funcs.get (cls)

		if func:
			return func (spt)

	raise RuntimeError (f'unexpected class {spt.__class__.__name__!r}')

def _spt2ast_nan (spt):
	raise ValueError ('undefined')

_rec_spt2ast_num = re.compile (r'(-?)(\d*[^0.e])?(0*)(?:(\.)(0*)(\d*[^0e])?(0*))?(?:(e)([+-]\d+))?') # -101000.000101000e+123 -> (-) (101) (000) (.) (000) (101) (000) (e) (+123)

def _spt2ast_num (spt):
	m = _rec_spt2ast_num.match (str (spt))
	g = [g or '' for g in m.groups ()]

	if g [5]:
		return ('#', ''.join (g [:6] + g [7:]))

	e = len (g [2]) + (int (g [8]) if g [8] else 0)

	return ('#', \
			f'{g [0]}{g [1]}e+{e}'     if e >= 16 else \
			f'{g [0]}{g [1]}{"0" * e}' if e >= 0 else \
			f'{g [0]}{g [1]}e{e}')

def _spt2ast_mul (spt):
	if spt.args [0] == -1:
		return ('-', spt2ast (sp.Mul (*spt.args [1:])))

	if spt.args [0].is_negative:
		return ('-', spt2ast (sp.Mul (-spt.args [0], *spt.args [1:])))

	numer = []
	denom = []

	for arg in spt.args:
		if isinstance (arg, sp.Pow) and arg.args [1].is_negative:
			denom.append (spt2ast (sp.Pow (arg.args [0], -arg.args [1])))
		else:
			numer.append (spt2ast (arg))

	if not denom:
		return ('*',) + tuple (numer) if len (numer) > 1 else numer [0]

	if not numer:
		return ('/', ('#', '1'), ('*',) + tuple (denom) if len (denom) > 1 else denom [0])

	return ('/', ('*',) + tuple (numer) if len (numer) > 1 else numer [0], \
			('*',) + tuple (denom) if len (denom) > 1 else denom [0])

def _spt2ast_pow (spt):
	if spt.args [1].is_negative:
		return ('/', ('#', '1'), spt2ast (sp.Pow (spt.args [0], -spt.args [1])))

	if spt.args [1] == 0.5:
		return ('sqrt', spt2ast (spt.args [0]))

	return ('^', spt2ast (spt.args [0]), spt2ast (spt.args [1]))

def _spt2ast_trigh (spt):
	return ('trigh', spt.__class__.__name__, spt2ast (spt.args [0]))

def _spt2ast_integral (spt):
	return \
			('int', spt2ast (spt.args [0]), ('@', f'd{spt2ast (spt.args [1] [0]) [1]}'), spt2ast (spt.args [1] [1]), spt2ast (spt.args [1] [2])) \
			if len (spt.args [1]) == 3 else \
			('int', spt2ast (spt.args [0]), ('@', f'd{spt2ast (spt.args [1] [0]) [1]}'))

_spt2ast_funcs = {
	sp.numbers.NaN: _spt2ast_nan,
	sp.Integer: _spt2ast_num,
	sp.Float: _spt2ast_num,
	sp.Rational: lambda spt: ('/', ('#', str (spt.p)), ('#', str (spt.q))) if spt.p >= 0 else ('-', ('/', ('#', str (-spt.p)), ('#', str (spt.q)))),
	sp.numbers.ImaginaryUnit: lambda ast: ('@', 'i'),
	sp.numbers.Pi: lambda spt: ('@', '\\pi'),
	sp.numbers.Exp1: lambda spt: ('@', 'e'),
	sp.exp: lambda spt: ('^', ('@', 'e'), spt2ast (spt.args [0])),
	sp.numbers.Infinity: lambda spt: ('@', '\\infty'),
	sp.numbers.NegativeInfinity: lambda spt: ('-', ('@', '\\infty')),
	sp.numbers.ComplexInfinity: lambda spt: ('@', '\\infty'), # not exactly but whatever
	sp.Symbol: lambda spt: ('@', spt.name),

	sp.Abs: lambda spt: ('|', spt2ast (spt.args [0])),
	sp.Add: lambda spt: ('+',) + tuple (spt2ast (arg) for arg in reversed (spt._sorted_args)),
	sp.arg: lambda spt: ('func', 'arg', spt2ast (spt.args [0])),
	sp.factorial: lambda spt: ('!', spt2ast (spt.args [0])),
	sp.log: lambda spt: ('log', spt2ast (spt.args [0])) if len (spt.args) == 1 else ('log', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Mul: _spt2ast_mul,
	sp.Pow: _spt2ast_pow,
	sp.functions.elementary.trigonometric.TrigonometricFunction: _spt2ast_trigh,
	sp.functions.elementary.hyperbolic.HyperbolicFunction: _spt2ast_trigh,
	sp.functions.elementary.trigonometric.InverseTrigonometricFunction: _spt2ast_trigh,
	sp.functions.elementary.hyperbolic.InverseHyperbolicFunction: _spt2ast_trigh,

	sp.Sum: lambda spt: ('sum', spt2ast (spt.args [0]), spt2ast (spt.args [1] [0]), spt2ast (spt.args [1] [1]), spt2ast (spt.args [1] [2])),
	sp.Integral: _spt2ast_integral,
}

if __name__ == '__main__':
	print (_rec_spt2ast_num.match ('10100.0010100').groups ())
	t = ast2spt (('int', ('@', 'dx')))
	print (t)
