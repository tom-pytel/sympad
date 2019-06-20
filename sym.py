# TODO: -{1+2}

import re

import sympy as sp

_diff_var_single_start_rec = re.compile (r'^d(?=[^_])')
_diff_var_start_rec        = re.compile (r'^(?:d(?=[^_])|\\partial )')
_var_multiple_rec          = re.compile (r'^(?:d(?=[^_])|\\partial )|(?:.*_)')

def _fltoint (v):
	v = float (v)
	return int (v) if v.is_integer () else v

def _num_is_int (n):
	return isinstance (n, int) or (isinstance (n, float) and n.is_integer ())

def _ast_is_0to9 (ast):
	return ast [0] == '#' and _num_is_int (ast [1]) and 0 <= ast [1] <= 9

def _ast_is_single_var (ast):
	return ast [0] == '@' and not _var_multiple_rec.match (ast [1]) # and '_' not in ast [1]

def _ast_is_single_unit (ast):
	return _ast_is_0to9 (ast) or _ast_is_single_var (ast)

def _ast_ignore_fact (ast):
	return ast if ast [0] != '!' else _ast_ignore_fact (ast [1])

#...............................................................................................
def _ast2tex_paren (ast):
	return f'\\left({ast2tex (ast)} \\right)' if ast [0] != '(' else ast2tex (ast)

def _ast2tex_mul (ast):
	t = []

	for i in range (1, len (ast)):
		aif = _ast_ignore_fact (ast [i])

		if i != 1 and (aif [0] == '#' or ast [i] [0] == '!' or (aif [0] in {'/', 'diff'} and ast [i - 1] [0] in {'#', '/', 'diff'})):
			t.append (f' \\cdot {ast2tex (ast [i])}')
		elif i != 1 and (ast [i - 1] in {('@', 'd'), ('@', '\\partial')} or ast [i - 1] [0] == 'sqrt' or \
				(aif [0] == '@' and _diff_var_start_rec.match (aif [1])) or \
				(ast [i - 1] [0] == '@' and _diff_var_start_rec.match (ast [i - 1] [1]))):
			t.append (f'\\ {ast2tex (ast [i])}')
		else:
			t.append (f'{"" if i == 1 else " "}{_ast2tex_paren (ast [i]) if ast [i] [0] == "+" else ast2tex (ast [i])}')

	return ''.join (t)

def _ast2tex_pow (ast):
	b = ast2tex (ast [1])
	p = f'^{ast2tex (ast [2])}' if _ast_is_single_unit (ast [2]) else f'^{{{ast2tex (ast [2])}}}'

	if ast [1] [0] in '([|':
		return f'{b}{p}'

	if ast [1] [0] == 'trigh' and ast [1] [1] [0] != 'a' and ast [2] [0] == '#' and ast [2] [1] >= 0:
		i = len (ast [1] [1]) + 1

		return f'{b [:i]}{p}{b [i:]}'

	elif ast [1] [0] == '@' or (ast [1] [0] == '#' and ast [1] [1] >= 0):
		return f'{b}{p}'

	return f'\\left({b} \\right){p}'

def _ast2tex_log (ast):
	if len (ast) == 2:
		return f'\\ln\\left({ast2tex (ast [1])} \\right)'

	t = ast2tex (ast [2])

	return f'\\log_{{{t}}}\\left({ast2tex (ast [1])} \\right)' if len (t) > 1 else \
			f'\\log_{t}\\left({ast2tex (ast [1])} \\right)'

def _ast2tex_trigh (ast):
	n = (f'\\operatorname{{{ast [1] [1:]}}}^{{-1}}' if ast [1] in {'asech', 'acsch'} else f'\\{ast [1] [1:]}^{{-1}}') \
			if ast [1] [0] == 'a' else \
			(f'\\operatorname{{{ast [1]}}}' if ast [1] in {'sech', 'csch'} else f'\\{ast [1]}')

	return f'{n}{_ast2tex_paren (ast [2])}'

def _ast2tex_sympy (ast):
	return f'\\operatorname{{{ast [1]}}}{_ast2tex_paren (ast [2])}'

def _ast2tex_lim (ast):
	s = ast2tex (ast [2]) if not ast [4] else ast2tex (('^', ast [2], ('#', 1))) [:-1] + ast [4]

	return f'\\lim_{{{ast2tex (ast [1])} \\to {s}}}{_ast2tex_paren (ast [3])}'

def _ast2tex_sum (ast):
	s = ast2tex (('^', ('#', 1), ast [3])) [1:]

	return f'\\sum_{{{ast2tex (ast [1])} = {ast2tex (ast [2])}}}{s}{_ast2tex_paren (ast [4])}'

def _ast2tex_diff (ast):
	ds = set ()
	p  = 0

	for i in range (2, len (ast)):
		if ast [i] [0] == '@':
			ds.add (ast [i] [1])
			p += 1
		else:
			ds.add (ast [i] [1] [1])
			p += ast [i] [2] [1]

	if len (ds) == 1 and ds.pop () [0] != '\\': # is not '\\partial'
		return f'\\frac{{d{"" if p == 1 else f"^{p}"}}}{{{"".join (ast2tex (ast [i]) for i in range (2, len (ast)))}}}{_ast2tex_paren (ast [1])}'

	else:
		s = ''.join (_diff_var_single_start_rec.sub ('\\partial ', ast2tex (ast [i])) for i in range (2, len (ast)))

		return f'\\frac{{\\partial{"" if p == 1 else f"^{p}"}}}{{{s}}}{_ast2tex_paren (ast [1])}'

_ast2tex_funcs = {
	'#': lambda ast: str (ast [1]),
	'@': lambda ast: str (ast [1]) if ast [1] else '{}', # '\\Vert', # '{}',
	'(': lambda ast: f'\\left({ast2tex (ast [1])} \\right)',
	'[': lambda ast: f'\\left[{ast2tex (ast [1])} \\right]',
	'|': lambda ast: f'\\left|{ast2tex (ast [1])} \\right|',
	'-': lambda ast: f'-{ast2tex (ast [1])}',
	'!': lambda ast: f'{_ast2tex_paren (ast [1])}!' if ast [1] [0] in {'+', '-', '*', '/', 'sqrt'} else f'{ast2tex (ast [1])}!',
	'+': lambda ast: ' + '.join (ast2tex (n) for n in ast [1:]).replace (' + -', ' - '),
	'*': _ast2tex_mul,
	'/': lambda ast: f'\\frac{{{ast2tex (ast [1])}}}{{{ast2tex (ast [2])}}}',
	'^': _ast2tex_pow,
	'log': _ast2tex_log,
	'sqrt': lambda ast: f'\\sqrt{{{ast2tex (ast [1])}}}' if len (ast) == 2 else f'\\sqrt[{ast2tex (ast [2])}]{{{ast2tex (ast [1])}}}',
	'trigh': _ast2tex_trigh,
	'sympy': _ast2tex_sympy,
	'lim': _ast2tex_lim,
	'sum': _ast2tex_sum,
	'diff': _ast2tex_diff,
}

def ast2tex (ast):
	return _ast2tex_funcs [ast [0]] (ast)

#...............................................................................................
def _ast2simple_paren (ast):
	return f'({ast2simple (ast)})' if ast [0] != '(' else ast2simple (ast)

def _ast2simple_mul (ast, ret_has_star = False):
	t        = []
	has_star = False

	for i in range (1, len (ast)):
		aif = _ast_ignore_fact (ast [i])

		if i != 1 and (aif [0] == '#' or ast [i] [0] == '!' or aif [0] in {'/', 'diff'} or ast [i - 1] [0] in {'/', 'diff'}):
			t.append (f' * {ast2simple (ast [i])}')
			has_star = True
		elif i != 1 and (ast [i - 1] in {('@', 'd'), ('@', '\\partial')} or \
				(aif [0] == '@' and _diff_var_start_rec.match (aif [1])) or \
				(ast [i - 1] [0] == '@' and _diff_var_start_rec.match (ast [i - 1] [1]))):
			t.append (f' {ast2tex (ast [i])}')
		else:
			t.append (f'{_ast2simple_paren (ast [i]) if ast [i] [0] == "+" else ast2simple (ast [i])}')

	return ''.join (t) if not ret_has_star else (''.join (t), has_star)

def _ast2simple_div (ast):
	n, ns = _ast2simple_mul (ast [1], True) if ast [1] [0] == '*' else (ast2simple (ast [1]), True) if ast [1] [0] == '+' else (ast2simple (ast [1]), False)
	d, ds = _ast2simple_mul (ast [2], True) if ast [2] [0] == '*' else (ast2simple (ast [2]), True) if ast [2] [0] == '+' else (ast2simple (ast [2]), False)

	return f'{f"{{{n}}}" if ns else n}/{f"{{{d}}}" if ds else d}'

def _ast2simple_pow (ast):
	b = ast2simple (ast [1])
	p = f'^{ast2simple (ast [2])}' if _ast_is_single_unit (ast [2]) else f'^{{{ast2simple (ast [2])}}}'

	if ast [1] [0] in '([|':
		return f'{b}{p}'

	if ast [1] [0] == 'trigh' and ast [1] [1] [0] != 'a' and ast [2] [0] == '#' and ast [2] [1] >= 0:
		i = len (ast [1] [1]) + 1

		return f'{b [:i]}{p}{b [i:]}'

	elif ast [1] [0] == '@' or (ast [1] [0] == '#' and ast [1] [1] >= 0):
		return f'{b}{p}'

	return f'({b}){p}'

def _ast2simple_log (ast):
	if len (ast) == 2:
		return f'\\ln({ast2simple (ast [1])})'

	return f'\\log_{ast2simple (ast [2])}({ast2simple (ast [1])})' if _ast_is_single_unit (ast [2]) else \
			f'\\log_{{{ast2simple (ast [2])}}}({ast2simple (ast [1])})'

def _ast2simple_trigh (ast):
	n = f'\\{ast [1] [1:]}^{{-1}}' if ast [1] [0] == 'a' else f'\\{ast [1]}'

	return f'{n}{_ast2simple_paren (ast [2])}'

def _ast2simple_sympy (ast):
	return f'{ast [1]}{_ast2simple_paren (ast [2])}'

def _ast2simple_lim (ast):
	s = ast2simple (ast [2]) if not ast [4] else ast2simple (('^', ast [2], ('#', 0))) [:-1] + ast [4]
	s = f' {s}' if s [0] != '\\' else s

	return f'\\lim_{{{ast2simple (ast [1])}\\to{s}}}{_ast2simple_paren (ast [3])}'

def _ast2simple_sum (ast):
	s = ast2simple (('^', ('#', 0), ast [3])) [1:]

	return f'\\sum_{{{ast2simple (ast [1])}={ast2simple (ast [2])}}}{s}{_ast2simple_paren (ast [4])}'

_ast2simple_diff_single_rec = re.compile ('^d')

def _ast2simple_diff (ast):
	ds = set ()
	p  = 0

	for i in range (2, len (ast)):
		if ast [i] [0] == '@':
			ds.add (ast [i] [1])
			p += 1
		else:
			ds.add (ast [i] [1] [1])
			p += ast [i] [2] [1]

	if len (ds) == 1 and ds.pop () [0] != '\\': # is not '\\partial'
		return f'd{"" if p == 1 else f"^{p}"}/{"".join (ast2simple (ast [i]) for i in range (2, len (ast)))}{_ast2simple_paren (ast [1])}'

	else:
		s = ''.join (_ast2simple_diff_single_rec.sub ('\\partial ', ast2simple (ast [i])) for i in range (2, len (ast)))

		return f'\\partial{"" if p == 1 else f"^{p}"}/{s}{_ast2simple_paren (ast [1])}'

_ast2simple_funcs = {
	'#': lambda ast: str (ast [1]),
	'@': lambda ast: str (ast [1]) if ast [1] else '', # '\\Vert', # '{}',
	'(': lambda ast: f'({ast2simple (ast [1])})',
	'[': lambda ast: f'[{ast2simple (ast [1])}]',
	'|': lambda ast: f'|{ast2simple (ast [1])}|',
	'-': lambda ast: f'-{ast2simple (ast [1])}',
	'!': lambda ast: f'{ast2simple (ast [1])}!',
	'+': lambda ast: ' + '.join (ast2simple (n) for n in ast [1:]).replace (' + -', ' - '),
	'*': _ast2simple_mul,
	'/': _ast2simple_div,
	'^': _ast2simple_pow,
	'log': _ast2simple_log,
	'sqrt': lambda ast: f'\\sqrt{{{ast2simple (ast [1])}}}' if len (ast) == 2 else f'\\sqrt[{ast2simple (ast [2])}]{{{ast2simple (ast [1])}}}',
	'trigh': _ast2simple_trigh,
	'sympy': _ast2simple_sympy,
	'lim': _ast2simple_lim,
	'sum': _ast2simple_sum,
	'diff': _ast2simple_diff,
}

def ast2simple (ast):
	return _ast2simple_funcs [ast [0]] (ast)

#...............................................................................................
def ast2py (ast):
	return ''

#...............................................................................................
def _ast2spt_diff (ast):
	args = sum ((
			(ast2spt (('@', _diff_var_start_rec.sub ('', n [1]))),) \
			if n [0] == '@' else \
			(ast2spt (('@', _diff_var_start_rec.sub ('', n [1] [1]))), sp.Integer (n [2] [1])) \
			for n in ast [2:] \
	), ())

	return sp.diff (ast2spt (ast [1]), *args)

_ast2spt_vars = {
	'i': sp.I,
	'\\pi': sp.pi,
	'e': sp.E,
	'\\infty': sp.oo,
}

_ast2spt_sympy = {
	'?': 'N',
}

_ast2spt_funcs = {
	'#': lambda ast: sp.S (ast [1]),
	'@': lambda ast: _ast2spt_vars.get (ast [1], sp.Symbol (ast [1])),
	'(': lambda ast: ast2spt (ast [1]),
	'[': lambda ast: ast2spt (ast [1]),
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
	'sympy': lambda ast: getattr (sp, _ast2spt_sympy.get (ast [1], ast [1])) (ast2spt (ast [2])),
	'lim': lambda ast: sp.limit (ast2spt (ast [3]), ast2spt (ast [1]), ast2spt (ast [2]), dir = ast [4] if ast [4] else '+-'),
	'sum': lambda ast: sp.Sum (ast2spt (ast [4]), (ast2spt (ast [1]), ast2spt (ast [2]), ast2spt (ast [3]))).doit (),
	'diff': _ast2spt_diff,
}

def ast2spt (ast):
	return _ast2spt_funcs [ast [0]] (ast)

#...............................................................................................
def _spt2ast_mul (spt):
	if spt.args [0] == -1:
		return ('-', spt2ast (sp.Mul (*spt.args [1:])))

	if spt.args [0].is_negative:
		return ('-', spt2ast (sp.Mul (*((-spt.args [0],) + spt.args [1:]))))

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
		return ('/', ('#', 1), ('*',) + tuple (denom) if len (denom) > 1 else denom [0])

	return ('/', ('*',) + tuple (numer) if len (numer) > 1 else numer [0], \
			('*',) + tuple (denom) if len (denom) > 1 else denom [0])

def _spt2ast_pow (spt):
	if spt.args [1].is_negative:
		return ('/', ('#', 1), spt2ast (sp.Pow (spt.args [0], -spt.args [1])))

	if spt.args [1] == 0.5:
		return ('sqrt', spt2ast (spt.args [0]))

	return ('^', spt2ast (spt.args [0]), spt2ast (spt.args [1]))

def _spt2ast_trigh (spt):
	return ('trigh', spt.__class__.__name__, spt2ast (spt.args [0]))

_spt2ast_funcs = {
	sp.Integer: lambda spt: ('#', spt.p),
	sp.Float: lambda spt: ('#', _fltoint (spt)),
	sp.Rational: lambda spt: ('/', ('#', spt.p), ('#', spt.q)) if spt.p >= 0 else ('-', ('/', ('#', -spt.p), ('#', spt.q))),
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
	sp.factorial: lambda spt: ('!', spt2ast (spt.args [0])),
	sp.Mul: _spt2ast_mul,
	sp.Pow: _spt2ast_pow,
	sp.log: lambda spt: ('log', spt2ast (spt.args [0])) if len (spt.args) == 1 else ('log', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.functions.elementary.trigonometric.TrigonometricFunction: _spt2ast_trigh,
	sp.functions.elementary.hyperbolic.HyperbolicFunction: _spt2ast_trigh,
	sp.functions.elementary.trigonometric.InverseTrigonometricFunction: _spt2ast_trigh,
	sp.functions.elementary.hyperbolic.InverseHyperbolicFunction: _spt2ast_trigh,
	sp.Sum: lambda spt: ('sum', spt2ast (spt.args [1] [0]), spt2ast (spt.args [1] [1]), spt2ast (spt.args [1] [2]), spt2ast (spt.args [0])),
}

def spt2ast (spt):
	for cls in spt.__class__.__mro__:
		func = _spt2ast_funcs.get (cls)

		if func:
			return func (spt)

	raise RuntimeError (f'unexpected class {spt.__class__!r}')

# if __name__ == '__main__':
# 	t = ast2simple (('trigh', 'sin', ('(', ('@', 'x'))))