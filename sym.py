# Convert between internal AST and sympy expressions and write out LaTeX, simple and python code

from ast import literal_eval
import re
import sympy as sp

import sast          # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import xlat          # AUTO_REMOVE_IN_SINGLE_SCRIPT

_SYMPY_FLOAT_PRECISION = None
_USER_FUNCS            = set () # set or dict of user function names

class AST_Text (AST): # for displaying elements we do not know how to handle, only returned from SymPy processing, not passed in
	op = 'text'

	def _init (self, tex = None, nat = None, py = None, spt = None):
		self.tex, self.nat, self.py, self.spt = tex, nat, py, spt

sast.register_AST (AST_Text)

class ExprNoEval (sp.Expr): # prevent any kind of evaluation on AST on instantiation or doit, args = (str (AST), sp.S.One)
	is_number  = False
	SYMPAD_ast = lambda self: AST (*literal_eval (self.args [0]))

	def SYMPAD_eval (self):
		return self.SYMPAD_ast () if self.args [1] == 1 else AST ('func', AST.Func.NOEVAL, (self.SYMPAD_ast (), spt2ast (self.args [1] - 1)))

def _tuple2ast (args):
	return args [0] if len (args) == 1 else AST (',', args)

def _trail_comma (obj):
	return ',' if len (obj) == 1 else ''

def _ast_slice_bounds (ast, None_ = AST.VarNull):
	return tuple (a or None_ for a in ((ast.start, ast.stop) if ast.step is None else (ast.start, ast.stop, ast.step)))

def _ast_is_neg (ast):
	return ast.is_minus or ast.is_neg_num or (ast.is_mul and _ast_is_neg (ast.mul [0]))

def _ast_func_call (func, args, _ast2spt = None, is_escaped = False):
	if _ast2spt is None:
		_ast2spt = ast2spt

	pyargs = []
	pykw   = {}

	for arg in args:
		if arg.is_ass:
			pykw [arg.lhs.as_identifier ()] = _ast2spt (arg.rhs)
		elif pykw:
			raise SyntaxError ('positional argument follows keyword argument')
		else:
			pyargs.append (_ast2spt (arg))

	spt = func (*pyargs, **pykw)

	if type (spt) is func:
		try:
			spt.SYMPAD_ESCAPED = is_escaped
		except AttributeError: # couldn't assign to python object (probably because is built-in type)
			pass

	return spt

def _ast_xlat_funcs (ast, XLAT): # translate eligible functions in tree to other AST representations
	if not isinstance (ast, AST):
		return ast

	if ast.is_func:
		xact = XLAT.get (ast.func)

		if xact is not None:
			args = AST (*(_ast_xlat_funcs (arg, XLAT) for arg in ast.args))

			if xact is True: # True means execute function and use return value for ast
				return spt2ast (_ast_func_call (getattr (sp, ast.func), args))

			try:
				ast2 = xlat.xlat_func (xact, args)

				if ast2 is not None:
					return ast2

			except:
				pass

			return AST ('func', ast.func, args)

	return AST (*(_ast_xlat_funcs (e, XLAT) for e in ast))

#...............................................................................................
def ast2tex (ast, doxlat = True): # abstract syntax tree -> LaTeX text
	return _ast2tex (_ast_xlat_funcs (ast, xlat.XLAT_FUNC_TEX) if doxlat else ast)

def _ast2tex (ast):
	return _ast2tex_funcs [ast.op] (ast)

def _ast2tex_wrap (obj, curly = None, paren = None):
	s = _ast2tex (obj) if isinstance (obj, AST) else str (obj)

	if (obj.op in paren) if isinstance (paren, set) else paren:
		return f'\\left({s} \\right)'

	if (obj.op in curly) if isinstance (curly, set) else curly:
		return f'{{{s}}}'

	return s

def _ast2tex_curly (ast):
	return \
			f'{_ast2tex (ast)}'                     if ast.is_single_unit else \
			f'{{{_ast2tex (ast)}}}'                 if not ast.is_comma else \
			f'{{\\left({_ast2tex (ast)}\\right)}}'

def _ast2tex_paren (ast, ops = {}):
	return _ast2tex_wrap (ast, 0, not (ast.is_paren or (ops and ast.op not in ops)))

def _ast2tex_paren_mul_exp (ast, ret_has = False, also = {'=', '+'}):
	if ast.is_mul:
		s, has = _ast2tex_mul (ast, True)
	else:
		s, has = _ast2tex (ast), ast.op in also

	s = _ast2tex_wrap (s, 0, has)

	return (s, has) if ret_has else s

def _ast2tex_eq_hs (ast, hs, lhs = True):
	return _ast2tex_wrap (hs, 0, (hs.is_ass or (lhs and hs.op in {',', 'piece'})) if ast.is_ass else {'=', 'piece'})

def _ast2tex_num (ast):
	m, e = ast.mant_and_exp

	return f'{m}{{e}}{{{e}}}' if e else m

_ast2tex_var_xlat = {'Naturals', 'Naturals0', 'Integers', 'Reals', 'Complexes'}

def _ast2tex_var (ast):
	if not ast.var:
		return '{}' # Null var

	if ast.var in _ast2tex_var_xlat:
		return sp.latex (getattr (sp, ast.var))

	v = ast.as_var.var
	p = ''

	while v [-6:] == '_prime':
		v, p = v [:-6], p + "'"

	n = v.replace ('_', '\\_')
	t = AST.Var.PY2TEX.get (n)

	return \
			f'{t or n}{p}'       if not ast.diff_or_part_type else \
			f'd{t or n}{p}'		   if ast.is_diff_any else \
			f'\\partial{p}'      if ast.is_part_solo else \
			f'\\partial{t}{p}'   if t else \
			f'\\partial {n}{p}'  if n else \
			f'\\partial{p}'

def _ast2tex_attr (ast):
	a = ast.attr.replace ('_', '\\_')
	a = a if ast.args is None else f'\\operatorname{{{a}}}{_ast2tex_paren (_tuple2ast (ast.args))}'

	return f'{_ast2tex_paren (ast.obj, {"=", "#", ",", "-", "+", "*", "/", "lim", "sum", "intg", "piece"})}.{a}'

def _ast2tex_add (ast):
	return ' + '.join (_ast2tex_wrap (n, \
			((n.strip_mls ().is_intg or (n.is_mul and n.mul [-1].strip_mls ().is_intg)) and n is not ast.add [-1]), \
			(n.op in ("piece") and n is not ast.add [-1]) or n.op in {'='})
			for n in ast.add).replace (' + -', ' - ').replace (' + {-', ' - {')

def _ast2tex_mul (ast, ret_has = False):
	t   = []
	p   = None
	has = False

	for n in ast.mul:
		s = _ast2tex_wrap (n, \
				(p and _ast_is_neg (n)) or (n.strip_mls ().is_intg and n is not ast.mul [-1]), \
				n.op in {'=', '+'} or (n.is_piece and n is not ast.mul [-1]))

		if p and p.is_attr and s [:6] == '\\left(':
			s = _ast2tex_wrap (s, 1)

		if p and (n.op in {'#', '[', '!', 'mat'} or n.is_null_var or p.op in {'lim', 'sum', 'diff', 'intg', 'mat'} or \
				(n.is_pow and n.base.is_pos_num) or (n.op in {'/', 'diff'} and p.op in {'#', '/'}) or _ast_is_neg (n) or \
				(p.is_div and (p.numer.is_diff_or_part_solo or (p.numer.is_pow and p.numer.base.is_diff_or_part_solo))) or \
				(n.is_paren and p.is_var and p.var in _USER_FUNCS) or \
				(n.is_idx and n.obj.op in {'[', 'idx'})):
			t.append (f' \\cdot {s}')
			has = True

		elif p and (p.op in {'sqrt'} or p.num_exp or \
				p.is_diff_or_part_solo or n.is_diff_or_part_solo or p.is_diff_or_part or n.is_diff_or_part or \
				(p.is_long_var and n.op not in {'(', '['}) or (n.is_long_var and p.op not in {'(', '['})):
			t.append (f'\\ {s}')

		else:
			t.append (f'{"" if not p else " "}{s}')

		p = n

	return (''.join (t), has) if ret_has else ''.join (t)

def _ast2tex_pow (ast, trighpow = True):
	b = _ast2tex_wrap (ast.base, {'mat'}, not (ast.base.op in {'@', '"', '(', '|', 'func', 'mat'} or ast.base.is_pos_num))
	p = _ast2tex_curly (ast.exp)

	if ast.base.is_trigh_func_noninv and ast.exp.is_single_unit and trighpow:
		i = len (ast.base.func) + (15 if ast.base.func in {'sech', 'csch'} else 1)

		return f'{b [:i]}^{p}{b [i:]}'

	return f'{b}^{p}'

def _ast2tex_log (ast):
	return \
			f'\\ln{_ast2tex_paren (ast.log)}' \
			if ast.base is None else \
			f'\\log_{_ast2tex_curly (ast.base)}{_ast2tex_paren (ast.log)}'

_ast2tex_xlat_func2text = {
	'beta'    : lambda ast: f'\\beta\\left({_ast2tex (_tuple2ast (ast.args))} \\right)',
	'gamma'   : lambda ast: f'\\Gamma\\left({_ast2tex (_tuple2ast (ast.args))} \\right)',
	'Gamma'   : lambda ast: f'\\Gamma\\left({_ast2tex (_tuple2ast (ast.args))} \\right)',
	'zeta'    : lambda ast: f'\\zeta\\left({_ast2tex (_tuple2ast (ast.args))} \\right)',
	'binomial': lambda ast: f'\\binom{{{_ast2tex (ast.args [0])}}}{{{_ast2tex (ast.args [1])}}}' if len (ast.args) == 2 else None,
}

def _ast2tex_func (ast):
	if ast.is_trigh_func:
		n = (f'\\operatorname{{{ast.func [1:]}}}^{{-1}}' \
				if ast.func in {'asech', 'acsch'} else \
				f'\\{ast.func [1:]}^{{-1}}') \
				if ast.func [0] == 'a' else \
				(f'\\operatorname{{{ast.func}}}' if ast.func in {'sech', 'csch'} else f'\\{ast.func}')

		return f'{n}\\left({_ast2tex (_tuple2ast (ast.args))} \\right)'

	xact = _ast2tex_xlat_func2text.get (ast.func)

	if xact:
		text = xact (ast)

		if text is not None:
			return text

	if ast.func in AST.Func.TEX:
		return f'\\{ast.func}\\left({_ast2tex (_tuple2ast (ast.args))} \\right)'
	else:
		return '\\operatorname{' + ast.func.replace ('_', '\\_').replace (AST.Func.NOEVAL, '\\%') + f'}}\\left({_ast2tex (_tuple2ast (ast.args))} \\right)'

def _ast2tex_lim (ast):
	s = _ast2tex (ast.to) if ast.dir is None else (_ast2tex_pow (AST ('^', ast.to, AST.Zero), trighpow = False) [:-1] + ast.dir)

	return f'\\lim_{{{_ast2tex (ast.lvar)} \\to {s}}} {_ast2tex_paren_mul_exp (ast.lim)}'

def _ast2tex_sum (ast):
	return f'\\sum_{{{_ast2tex (ast.svar)} = {_ast2tex (ast.from_)}}}^{_ast2tex_curly (ast.to)} {_ast2tex_paren_mul_exp (ast.sum)}' \

_rec_diff_var_single_start = re.compile (r'^d(?=[^_])')

def _ast2tex_diff (ast):
	ds = set ()
	p  = 0

	for n in ast.dvs:
		if n.is_var:
			p += 1

			if n.var:
				ds.add (n)

		else: # n = ('^', ('@', 'diff or part'), ('#', 'int'))
			p += int (n.exp.num)
			ds.add (n.base)

	if not ds:
		return f'\\frac{{d}}{{}}{_ast2tex_paren (ast.diff)}'

	dv = next (iter (ds))

	if len (ds) == 1 and not dv.is_partial:
		return f'\\frac{{d{"" if p == 1 else f"^{p}"}}}{{{" ".join (_ast2tex (n) for n in ast.dvs)}}}{_ast2tex_paren (ast.diff)}'

	else:
		s = ''.join (_rec_diff_var_single_start.sub (r'\\partial ', _ast2tex (n)) for n in ast.dvs)

		return f'\\frac{{\\partial{"" if p == 1 else f"^{p}"}}}{{{s}}}{_ast2tex_paren (ast.diff)}'

def _ast2tex_intg (ast):
	if ast.from_ is None:
		return \
				f'\\int \\ {_ast2tex (ast.dv)}' \
				if ast.intg is None else \
				f'\\int {_ast2tex_wrap (ast.intg, {"diff"}, {"="})} \\ {_ast2tex (ast.dv)}'
	else:
		return \
				f'\\int_{_ast2tex_curly (ast.from_)}^{_ast2tex_curly (ast.to)} \\ {_ast2tex (ast.dv)}' \
				if ast.intg is None else \
				f'\\int_{_ast2tex_curly (ast.from_)}^{_ast2tex_curly (ast.to)} {_ast2tex_wrap (ast.intg, {"diff"}, {"="})} \\ {_ast2tex (ast.dv)}'

_ast2tex_funcs = {
	'=': lambda ast: f'{_ast2tex_eq_hs (ast, ast.lhs)} {AST.Eq.PY2TEX.get (ast.rel, ast.rel)} {_ast2tex_eq_hs (ast, ast.rhs, False)}',
	'#': _ast2tex_num,
	'@': _ast2tex_var,
	'.': _ast2tex_attr,
	'"': lambda ast: f'\\text{{{repr (ast.str_)}}}',
	',': lambda ast: f'{", ".join (_ast2tex (c) for c in ast.comma)}{_trail_comma (ast.comma)}',
	'(': lambda ast: _ast2tex_wrap (ast.paren, 0, not ast.paren.is_lamb),
	'[': lambda ast: f'\\left[{", ".join (_ast2tex (b) for b in ast.brack)} \\right]',
	'|': lambda ast: f'\\left|{_ast2tex (ast.abs)} \\right|',
	'-': lambda ast: f'-{_ast2tex_wrap (ast.minus, ast.minus.is_pos_num or ast.minus.is_mul, {"=", "+"})}',
	'!': lambda ast: _ast2tex_wrap (ast.fact, {'^'}, (ast.fact.op not in {'#', '@', '"', '(', '|', '!', '^', 'vec', 'mat'} or ast.fact.is_neg_num)) + '!',
	'+': _ast2tex_add,
	'*': _ast2tex_mul,
	# '/': lambda ast: f'\\frac{{{_ast2tex_wrap (ast.numer, 0, (ast.numer.base.is_diff_or_part_solo and ast.numer.exp.remove_curlys ().is_pos_int) if ast.numer.is_pow else ast.numer.is_diff_or_part_solo)}}}{{{_ast2tex (ast.denom)}}}',
	'/': lambda ast: f'\\frac{{{_ast2tex_wrap (ast.numer, 0, (ast.numer.base.is_diff_or_part_solo and ast.numer.exp.is_pos_int) if ast.numer.is_pow else ast.numer.is_diff_or_part_solo)}}}{{{_ast2tex (ast.denom)}}}',
	'^': _ast2tex_pow,
	'log': _ast2tex_log,
	'sqrt': lambda ast: f'\\sqrt{{{_ast2tex_wrap (ast.rad, 0, {","})}}}' if ast.idx is None else f'\\sqrt[{_ast2tex (ast.idx)}]{{{_ast2tex_wrap (ast.rad, 0, {","})}}}',
	'func': _ast2tex_func,
	'lim': _ast2tex_lim,
	'sum': _ast2tex_sum,
	'diff': _ast2tex_diff,
	'intg': _ast2tex_intg,
	'vec': lambda ast: '\\begin{bmatrix} ' + r' \\ '.join (_ast2tex (e) for e in ast.vec) + ' \\end{bmatrix}',
	'mat': lambda ast: '\\begin{bmatrix} ' + r' \\ '.join (' & '.join (_ast2tex (e) for e in row) for row in ast.mat) + f'{" " if ast.mat else ""}\\end{{bmatrix}}',
	'piece': lambda ast: '\\begin{cases} ' + r' \\ '.join (f'{_ast2tex_wrap (p [0], 0, {"=", ","})} & \\text{{otherwise}}' if p [1] is True else f'{_ast2tex_wrap (p [0], 0, {"=", ","})} & \\text{{for}}\\: {_ast2tex (p [1])}' for p in ast.piece) + ' \\end{cases}',
	'lamb': lambda ast: f'\\left({_ast2tex (ast.vars [0] if len (ast.vars) == 1 else AST ("(", (",", ast.vars)))} \\mapsto {_ast2tex_wrap (ast.lamb, 0, ast.lamb.is_ass)} \\right)',
	'idx': lambda ast: f'{_ast2tex_wrap (ast.obj, 0, ast.obj.is_neg_num or ast.obj.op in {",", "=", "lamb", "piece", "+", "*", "/", "-", "diff", "intg", "lim", "sum"})}\\left[{_ast2tex (_tuple2ast (ast.idx))} \\right]',
	'slice': lambda ast: '{:}'.join (_ast2tex_wrap (a, a and _ast_is_neg (a), a and (a.is_ass or a.op in {',', 'lamb', 'slice'})) for a in _ast_slice_bounds (ast, '')),

	'text': lambda ast: ast.tex,
}

#...............................................................................................
def ast2nat (ast, doxlat = True): # abstract syntax tree -> simple text
	return _ast2nat (_ast_xlat_funcs (ast, xlat.XLAT_FUNC_NAT) if doxlat else ast)

def _ast2nat (ast):
	return _ast2nat_funcs [ast.op] (ast)

def _ast2nat_wrap (obj, curly = None, paren = None):
	s = _ast2nat (obj) if isinstance (obj, AST) else str (obj)

	if (obj.op in paren) if isinstance (paren, set) else paren:
		return f'({s})'

	if (obj.op in curly) if isinstance (curly, set) else curly:
		return f'{{{s}}}'

	return s

def _ast2nat_curly (ast, ops = {}):
	return _ast2nat_wrap (ast, ops if ops else (ast.is_div or not ast.is_single_unit or (ast.is_var and ast.var in AST.Var.PY2TEX)))

def _ast2nat_paren (ast, ops = {}):
	return _ast2nat_wrap (ast, 0, not (ast.is_paren or (ops and ast.op not in ops)))

def _ast2nat_curly_mul_exp (ast, ret_has = False, also = {}):
	if ast.is_mul:
		s, has = _ast2nat_mul (ast, True)
	else:
		s, has = _ast2nat (ast), False

	has = has or ((ast.op in also) if isinstance (also, set) else also)
	s   = _ast2nat_wrap (s, has)

	return (s, has) if ret_has else s

def _ast2nat_eq_hs (ast, hs, lhs = True):
	return _ast2nat_wrap (hs, 0, (hs.is_ass or (lhs and hs.op in {',', 'piece', 'lamb'})) if ast.is_ass else {'=', 'piece', 'lamb'})

def _ast2nat_add (ast):
	return ' + '.join (_ast2nat_wrap (n, \
			n.is_piece or ((n.strip_mls ().is_intg or (n.is_mul and n.mul [-1].strip_mls ().is_intg)) and n is not ast.add [-1]), \
			(n.op in ('piece', 'lamb') and n is not ast.add [-1]) or n.op in {'=', 'lamb'} \
			) for n in ast.add).replace (' + -', ' - ').replace (' + {-', ' - {')

def _ast2nat_mul (ast, ret_has = False):
	t   = []
	p   = None
	has = False

	for n in ast.mul:
		s = _ast2nat_wrap (n, \
				(p and _ast_is_neg (n)) or n.is_piece or (n.strip_mls ().is_intg and n is not ast.mul [-1]), \
				n.op in {'=', '+', 'lamb'} or (n.is_piece and n is not ast.mul [-1]))

		if p and (n.op in {'#', '[', '!', 'lim', 'sum', 'intg'} or n.is_null_var or p.op in {'lim', 'sum', 'diff', 'intg'} or \
				(n.is_pow and n.base.is_pos_num) or \
				n.op in {'/', 'diff'} or p.strip_minus ().op in {'/', 'diff'} or \
				(n.is_paren and p.is_var and p.var in _USER_FUNCS) or \
				(n.is_idx and n.obj.op in {'[', 'idx'})):
			t.append (f' * {s}')
			has = True

		elif p and (p.is_diff_or_part_solo or \
				(n.op not in {'#', '(', '|', '^'} or p.op not in {'#', '(', '|'})):
			t.append (f' {s}')

		else:
			t.append (s)

		p = n

	return (''.join (t), has) if ret_has else ''.join (t)

def _ast2nat_div (ast):
		# (_ast2nat_wrap (ast.numer, 0, 1), True) if ((ast.numer.base.is_diff_or_part_solo and ast.numer.exp.remove_curlys ().is_pos_int) if ast.numer.is_pow else ast.numer.is_diff_or_part_solo) else \
	n, ns = (_ast2nat_wrap (ast.numer, 1), True) if _ast_is_neg (ast.numer) else \
		(_ast2nat_wrap (ast.numer, 0, 1), True) if ((ast.numer.base.is_diff_or_part_solo and ast.numer.exp.is_pos_int) if ast.numer.is_pow else ast.numer.is_diff_or_part_solo) else \
		_ast2nat_curly_mul_exp (ast.numer, True, {'=', '+', '/', 'lim', 'sum', 'diff', 'intg', 'piece', 'lamb'})

	d, ds = (_ast2nat_wrap (ast.denom, 1), True) if _ast_is_neg (ast.denom) else _ast2nat_curly_mul_exp (ast.denom, True, {'=', '+', '/', 'lim', 'sum', 'diff', 'intg', 'piece', 'lamb'})
	s     = ns or ds or ast.numer.strip_minus ().op not in {'#', '@', '*'} or ast.denom.strip_minus ().op not in {'#', '@', '*'}

	return f'{n}{" / " if s else "/"}{d}'

def _ast2nat_pow (ast, trighpow = True):
	b = _ast2nat_wrap (ast.base, 0, not (ast.base.op in {'@', '"', '(', '|', 'func', 'mat'} or ast.base.is_pos_num))
	p = _ast2nat_wrap (ast.exp, ast.exp.strip_minus ().op in {'=', '+', '*', '/', 'lim', 'sum', 'diff', 'intg', 'piece', 'lamb'}, {","})

	if ast.base.is_trigh_func_noninv and ast.exp.is_single_unit and trighpow:
		i = len (ast.base.func)

		return f'{b [:i]}**{p}{b [i:]}'
		# return f'{b [1 : i + 1]}**{p}{b [i + 1 : -1]}'

	return f'{b}**{p}'

def _ast2nat_log (ast):
	return \
			f'ln{_ast2nat_paren (ast.log)}' \
			if ast.base is None else \
			f'\\log_{_ast2nat_curly (ast.base)}{_ast2nat_paren (ast.log)}'

def _ast2nat_lim (ast):
	s = _ast2nat_wrap (ast.to, {'piece'}) if ast.dir is None else (_ast2nat_pow (AST ('^', ast.to, AST.Zero), trighpow = False) [:-1] + ast.dir)

	return f'\\lim_{{{_ast2nat (ast.lvar)} \\to {s}}} {_ast2nat_curly_mul_exp (ast.lim, False, ast.lim.op in {"=", "+", "piece", "lamb"} or ast.lim.is_mul_has_abs)}'

def _ast2nat_sum (ast):
	return f'\\sum_{{{_ast2nat (ast.svar)}={_ast2nat_curly (ast.from_, {"piece"})}}}^{_ast2nat_curly (ast.to)} {_ast2nat_curly_mul_exp (ast.sum, False, ast.sum.op in {"=", "+", "piece", "lamb"} or ast.sum.is_mul_has_abs)}' \

def _ast2nat_diff (ast):
	p = 0
	d = ''

	for n in ast.dvs:
		if n.is_var:
			d  = n.diff_or_part_type
			p += 1
		else: # n = ('^', ('@', 'differential'), ('#', 'int'))
			d  = n.base.diff_or_part_type
			p += int (n.exp.num)

	return f'{d.strip () if d else "d"}{"" if p == 1 else f"^{p}"} / {" ".join (_ast2nat (n) for n in ast.dvs)} {_ast2nat_paren (ast.diff)}'

def _ast2nat_intg (ast):
	if ast.from_ is None:
		return \
				f'\\int {_ast2nat (ast.dv)}' \
				if ast.intg is None else \
				f'\\int {_ast2nat_wrap (ast.intg, ast.intg.op in {"diff", "piece"} or ast.intg.is_mul_has_abs, {"=", "lamb"})} {_ast2nat (ast.dv)}'
	else:
		return \
				f'\\int_{_ast2nat_curly (ast.from_)}^{_ast2nat_curly (ast.to)} {_ast2nat (ast.dv)}' \
				if ast.intg is None else \
				f'\\int_{_ast2nat_curly (ast.from_)}^{_ast2nat_curly (ast.to)} {_ast2nat_wrap (ast.intg, ast.intg.op in {"diff", "piece"} or ast.intg.is_mul_has_abs, {"=", "lamb"})} {_ast2nat (ast.dv)}'

_ast2nat_funcs = {
	'=': lambda ast: f'{_ast2nat_eq_hs (ast, ast.lhs)} {AST.Eq.PY2TEX.get (ast.rel, ast.rel)} {_ast2nat_eq_hs (ast, ast.rhs, False)}',
	'#': lambda ast: ast.num,
	'@': lambda ast: ast.var,
	'.': lambda ast: f'{_ast2nat_paren (ast.obj, {"=", "#", ",", "-", "+", "*", "/", "lim", "sum", "intg", "piece", "lamb"})}.{ast.attr}' \
			if ast.args is None else f'{_ast2nat (ast.obj)}.{ast.attr}{_ast2nat_paren (_tuple2ast (ast.args))}',
	'"': lambda ast: repr (ast.str_),
	',': lambda ast: f'{", ".join (_ast2nat (c) for c in ast.comma)}{_trail_comma (ast.comma)}',
	'(': lambda ast: f'({_ast2nat (ast.paren)})',
	'[': lambda ast: f'[{", ".join (_ast2nat (b) for b in ast.brack)}]',
	'|': lambda ast: f'{{|{_ast2nat (ast.abs)}|}}',
	'-': lambda ast: f'-{_ast2nat_wrap (ast.minus, ast.minus.is_pos_num or ast.minus.op in {"*", "piece"}, {"=", "+", "lamb"})}',
	'!': lambda ast: _ast2nat_wrap (ast.fact, {'^'}, ast.fact.op not in {'#', '@', '"', '(', '|', '!', '^', 'vec', 'mat'} or ast.fact.is_neg_num) + '!',
	'+': _ast2nat_add,
	'*': _ast2nat_mul,
	'/': _ast2nat_div,
	'^': _ast2nat_pow,
	'log': _ast2nat_log,
	'sqrt': lambda ast: f'sqrt{_ast2nat_paren (ast.rad)}' if ast.idx is None else f'\\sqrt[{_ast2nat (ast.idx)}]{{{_ast2nat_wrap (ast.rad, 0, {","})}}}',
	'func': lambda ast: f'{ast.func}({_ast2nat (_tuple2ast (ast.args))})',
	'lim': _ast2nat_lim,
	'sum': _ast2nat_sum,
	'diff': _ast2nat_diff,
	'intg': _ast2nat_intg,
	'vec': lambda ast: f'{{{", ".join (_ast2nat (e) for e in ast.vec)}{_trail_comma (ast.vec)}}}',
	'mat': lambda ast: ('{' + ', '.join (f'{{{", ".join (_ast2nat (e) for e in row)}{_trail_comma (row)}}}' for row in ast.mat) + f'{_trail_comma (ast.mat)}}}') if ast.mat else 'Matrix([])',
	'piece': lambda ast: ' else '.join (f'{_ast2nat_wrap (p [0], p [0].is_ass or p [0].op in {"piece", "lamb"}, {","})}' if p [1] is True else \
			f'{_ast2nat_wrap (p [0], p [0].is_ass or p [0].op in {"piece", "lamb"}, {","})} if {_ast2nat_wrap (p [1], p [1].is_ass or p [1].op in {"piece", "lamb"}, {","})}' for p in ast.piece),
	'lamb': lambda ast: f'lambda{" " + ", ".join (v.var for v in ast.vars) if ast.vars else ""}: {_ast2nat_wrap (ast.lamb, 0, ast.lamb.is_eq)}',
	'idx': lambda ast: f'{_ast2nat_wrap (ast.obj, 0, ast.obj.is_neg_num or ast.obj.op in {",", "=", "lamb", "piece", "+", "*", "/", "-", "diff", "intg", "lim", "sum"})}[{_ast2nat (_tuple2ast (ast.idx))}]',
	'slice': lambda ast: ':'.join (_ast2nat_wrap (a, 0, a.is_ass or a.op in {',', 'lamb', 'slice'}) for a in _ast_slice_bounds (ast)),

	'text': lambda ast: ast.nat,
}

#...............................................................................................
def ast2py (ast): # abstract syntax tree -> Python code text
	return _ast2py_funcs [ast.op] (ast)

def _ast2py_curly (ast):
	return \
			_ast2py_paren (ast) \
			if ast.strip_minus ().op in {',', '+', '*', '/'} or (ast.is_log and ast.base is not None) else \
			ast2py (ast)

def _ast2py_paren (ast, paren = None):
	if paren is None:
		return ast2py (ast) if ast.is_paren else f'({ast2py (ast)})'

	if (ast.op in paren) if isinstance (paren, set) else paren:
		return f'({ast2py (ast)})'

	return ast2py (ast)

def _ast2py_div (ast):
	n = _ast2py_curly (ast.numer)
	d = _ast2py_curly (ast.denom)

	return f'{n}{" / " if ast.numer.strip_minus ().op not in {"#", "@"} or ast.denom.strip_minus ().op not in {"#", "@"} else "/"}{d}'

def _ast2py_pow (ast):
	b = _ast2py_paren (ast.base) if _ast_is_neg (ast.base) else _ast2py_curly (ast.base)
	e = _ast2py_curly (ast.exp)

	return f'{b}**{e}'

def _ast2py_log (ast):
	return \
			f'ln{_ast2py_paren (ast.log)}' \
			if ast.base is None else \
			f'log{_ast2py_paren (ast.log)} / log{_ast2py_paren (ast.base)}' \

def _ast2py_lim (ast):
	return \
		f'''Limit({ast2py (ast.lim)}, {ast2py (ast.lvar)}, {ast2py (ast.to)}''' \
		f'''{", dir='+-'" if ast.dir is None else ", dir='-'" if ast.dir == '-' else ""})'''

def _ast2py_diff (ast):
	args = sum ((
			(ast2py (n.as_var),) \
			if n.is_var else \
			(ast2py (n.base.as_var), str (n.exp.num)) \
			for n in ast.dvs \
			), ())

	return f'Derivative({ast2py (ast.diff)}, {", ".join (args)})'

def _ast2py_intg (ast):
	if ast.from_ is None:
		return \
				f'Integral(1, {ast2py (ast.dv.as_var)})' \
				if ast.intg is None else \
				f'Integral({ast2py (ast.intg)}, {ast2py (ast.dv.as_var)})'
	else:
		return \
				f'Integral(1, ({ast2py (ast.dv.as_var)}, {ast2py (ast.from_)}, {ast2py (ast.to)}))' \
				if ast.intg is None else \
				f'Integral({ast2py (ast.intg)}, ({ast2py (ast.dv.as_var)}, {ast2py (ast.from_)}, {ast2py (ast.to)}))'

_ast2py_funcs = {
	'=': lambda ast: f'{_ast2py_paren (ast.lhs) if (ast.is_eq and ast.lhs.is_lamb) else ast2py (ast.lhs)} {ast.rel} {ast2py (ast.rhs)}',
	'#': lambda ast: ast.num,
	'@': lambda ast: ast.var,
	'.': lambda ast: f'{ast2py (ast.obj)}.{ast.attr}' if ast.args is None else f'{ast2py (ast.obj)}.{ast.attr}{_ast2py_paren (_tuple2ast (ast.args))}',
	'"': lambda ast: repr (ast.str_),
	',': lambda ast: f'{", ".join (ast2py (parm) for parm in ast.comma)}{_trail_comma (ast.comma)}',
	'(': lambda ast: f'({ast2py (ast.paren)})',
	'[': lambda ast: f'[{", ".join (ast2py (b) for b in ast.brack)}]',
	'|': lambda ast: f'abs({ast2py (ast.abs)})',
	'-': lambda ast: f'-{_ast2py_paren (ast.minus, ast.minus.op in {"+", "lamb"})}',
	'!': lambda ast: f'factorial({ast2py (ast.fact)})',
	'+': lambda ast: ' + '.join (ast2py (n) for n in ast.add).replace (' + -', ' - ').replace (' + -', ' - '),
	'*': lambda ast: '*'.join (_ast2py_paren (n) if n.is_add else ast2py (n) for n in ast.mul),
	'/': _ast2py_div,
	'^': _ast2py_pow,
	'log': _ast2py_log,
	'sqrt': lambda ast: f'sqrt{_ast2py_paren (ast.rad)}' if ast.idx is None else ast2py (AST ('^', ast.rad.strip_paren (1), ('/', AST.One, ast.idx))),
	'func': lambda ast: f'{ast.unescaped}({ast2py (_tuple2ast (ast.args))})',
	'lim': _ast2py_lim,
	'sum': lambda ast: f'Sum({ast2py (ast.sum)}, ({ast2py (ast.svar)}, {ast2py (ast.from_)}, {ast2py (ast.to)}))',
	'diff': _ast2py_diff,
	'intg': _ast2py_intg,
	'vec': lambda ast: 'Matrix([' + ', '.join (f'[{ast2py (e)}]' for e in ast.vec) + '])',
	'mat': lambda ast: 'Matrix([' + ', '.join (f'[{", ".join (ast2py (e) for e in row)}]' for row in ast.mat) + '])',
	'piece': lambda ast: 'Piecewise(' + ', '.join (f'({ast2py (p [0])}, {True if p [1] is True else ast2py (p [1])})' for p in ast.piece) + ')',
	'lamb': lambda ast: f'lambda{" " + ", ".join (v.var for v in ast.vars) if ast.vars else ""}: {ast2py (ast.lamb)}',
	'idx': lambda ast: f'{_ast2py_paren (ast.obj) if ast.obj.is_neg_num or ast.obj.op in {",", "=", "lamb", "piece", "+", "*", "/", "-", "diff", "intg", "lim", "sum"} else ast2py (ast.obj)}[{ast2py (_tuple2ast (ast.idx))}]',
	'slice': lambda ast: ':'.join (_ast2py_paren (a, a.is_ass or a.op in {',', 'lamb', 'slice'}) for a in _ast_slice_bounds (ast)),

	'text': lambda ast: ast.py,
}

#...............................................................................................
_ast2spt_consts = { # 'e' and 'i' dynamically set on use from AST.E or AST.I
	'pi'   : sp.pi,
	'oo'   : sp.oo,
	'zoo'  : sp.zoo,
	'None' : None,
	'True' : sp.boolalg.true,
	'False': sp.boolalg.false,
	'nan'  : sp.nan,
}

# Potentially bad __builtins__: eval, exec, globals, locals, vars, hasattr, getattr, setattr, delattr, exit, help, input, license, open, quit, __import__
_builtins_dict         = __builtins__ if isinstance (__builtins__, dict) else __builtins__.__dict__ # __builtins__.__dict__ if __name__ == '__main__' else __builtins__
_builtins_names        = ['abs', 'all', 'any', 'ascii', 'bin', 'callable', 'chr', 'dir', 'divmod', 'format', 'hash', 'hex', 'id',
		'isinstance', 'issubclass', 'iter', 'len', 'max', 'min', 'next', 'oct', 'ord', 'pow', 'print', 'repr', 'round', 'sorted', 'sum', 'bool',
		'bytearray', 'bytes', 'complex', 'dict', 'enumerate', 'filter', 'float', 'frozenset', 'property', 'int', 'list', 'map', 'object', 'range',
		'reversed', 'set', 'slice', 'str', 'tuple', 'type', 'zip']

_ast2spt_func_builtins = dict (no for no in filter (lambda no: no [1], ((n, _builtins_dict.get (n)) for n in _builtins_names)))

class ast2spt:
	def __new__ (cls, ast):
		self = super ().__new__ (cls)
		spt  = self._ast2spt (ast)

		try:
			spt = spt.doit ()
		except:
			pass

		return spt

	def _ast2spt (self, ast): # abstract syntax tree -> sympy tree (expression)
		return self._ast2spt_funcs [ast.op] (self, ast)

	def _ast2spt_var (self, ast):
		spt = {**_ast2spt_consts, AST.E.var: sp.E, AST.I.var: sp.I}.get (ast.var, None)

		if spt is None:
			if len (ast.var) > 1 and ast.var not in AST.Var.GREEK:
				spt = getattr (sp, ast.var, None)

			if spt is None:
				spt = sp.Symbol (ast.var)

		return spt

	def _ast2spt_attr (self, ast):
		obj = ast.obj

		while obj.is_func and obj.func == AST.Func.NOEVAL and obj.args:
			obj = obj.args [0]

		if obj.is_lamb and obj.lamb.is_func: # support S.Half and other lambdized sympy function or class attributes
			spt = getattr (sp, obj.lamb.unescaped)
		else:
			spt = self._ast2spt (ast.obj)

		try:
			mbr = getattr (spt, ast.attr)

			return mbr if ast.args is None else _ast_func_call (mbr, ast.args, self._ast2spt)

		except: # unresolved symbols should not raise but be returned as origninal attribute access op
			if not obj.free_vars ():
				raise

		return ExprNoEval (str (AST ('.', spt2ast (spt), *ast [2:])), sp.S.One)

	def _ast2spt_func (self, ast):
		if ast.func == AST.Func.NOREMAP: # special reference meta-function
			return self._ast2spt (ast.args [0])

		if ast.func == AST.Func.NOEVAL: # special no-evaluate meta-function
			return ExprNoEval (str (ast.args [0]), self._ast2spt (ast.args [1]) if len (ast.args) > 1 else sp.S.One)

		func = getattr (sp, ast.unescaped, None) or _ast2spt_func_builtins.get (ast.unescaped)

		if func is None:
			raise NameError (f'function {ast.unescaped!r} is not defined')

		return _ast_func_call (func, ast.args, self._ast2spt, is_escaped = ast.is_escaped)

	def _ast2spt_diff (self, ast):
		args = sum ((
				(self._ast2spt (n.as_var),) \
				if n.is_var else \
				(self._ast2spt (n.base.as_var), sp.Integer (n.exp.num)) \
				for n in ast.dvs \
				), ())

		return sp.Derivative (self._ast2spt (ast [1]), *args)

	def _ast2spt_intg (self, ast):
		if ast.from_ is None:
			return \
					sp.Integral (1, self._ast2spt (ast.dv.as_var)) \
					if ast.intg is None else \
					sp.Integral (self._ast2spt (ast.intg), self._ast2spt (ast.dv.as_var))
		else:
			return \
					sp.Integral (1, (self._ast2spt (ast.dv.as_var), self._ast2spt (ast.from_), self._ast2spt (ast.to))) \
					if ast.intg is None else \
					sp.Integral (self._ast2spt (ast [1]), (self._ast2spt (ast.dv.as_var), self._ast2spt (ast.from_), self._ast2spt (ast.to)))

	def _ast2spt_idx (self, ast):
		spt = self._ast2spt (ast.obj)
		idx = self._ast2spt (ast.idx [0]) if len (ast.idx) == 1 else tuple (self._ast2spt (i) for i in ast.idx)

		try:
			return spt [idx]
		except: # unresolved symbols should not raise but be returned as origninal indexing op
			if not ast.free_vars ():
				raise

		return ExprNoEval (str (AST ('idx', spt2ast (spt), ast.idx)), sp.S.One)

	_ast2spt_eq = {
		'=':  sp.Eq,
		'==': sp.Eq,
		'!=': sp.Ne,
		'<':  sp.Lt,
		'<=': sp.Le,
		'>':  sp.Gt,
		'>=': sp.Ge,
	}

	_ast2spt_funcs = {
		'=': lambda self, ast: self._ast2spt_eq [ast.rel] (self._ast2spt (ast.lhs), self._ast2spt (ast.rhs)),
		'#': lambda self, ast: sp.Integer (ast [1]) if ast.is_int_text (ast.num) else sp.Float (ast.num, _SYMPY_FLOAT_PRECISION),
		'@': _ast2spt_var,
		'.': _ast2spt_attr,
		'"': lambda self, ast: ast.str_,
		',': lambda self, ast: tuple (self._ast2spt (p) for p in ast.comma),
		'(': lambda self, ast: self._ast2spt (ast.paren),
		'[': lambda self, ast: [self._ast2spt (b) for b in ast.brack],
		'|': lambda self, ast: sp.Abs (self._ast2spt (ast.abs)),
		'-': lambda self, ast: -self._ast2spt (ast.minus),
		'!': lambda self, ast: sp.factorial (self._ast2spt (ast.fact)),
		'+': lambda self, ast: sp.Add (*(self._ast2spt (n) for n in ast.add)),
		'*': lambda self, ast: sp.Mul (*(self._ast2spt (n) for n in ast.mul)),
		'/': lambda self, ast: sp.Mul (self._ast2spt (ast.numer), sp.Pow (self._ast2spt (ast.denom), -1)),
		'^': lambda self, ast: sp.Pow (self._ast2spt (ast.base), self._ast2spt (ast.exp)),
		'log': lambda self, ast: sp.log (self._ast2spt (ast.log)) if ast.base is None else sp.log (self._ast2spt (ast.log), self._ast2spt (ast.base)),
		'sqrt': lambda self, ast: sp.Pow (self._ast2spt (ast.rad), sp.Pow (2, -1)) if ast.idx is None else sp.Pow (self._ast2spt (ast.rad), sp.Pow (self._ast2spt (ast.idx), -1)),
		'func': _ast2spt_func,
		'lim': lambda self, ast: (sp.Limit if ast.dir else sp.limit) (self._ast2spt (ast.lim), self._ast2spt (ast.lvar), self._ast2spt (ast.to), dir = ast.dir or '+-'),
		'sum': lambda self, ast: sp.Sum (self._ast2spt (ast.sum), (self._ast2spt (ast.svar), self._ast2spt (ast.from_), self._ast2spt (ast.to))),
		'diff': _ast2spt_diff,
		'intg': _ast2spt_intg,
		'vec': lambda self, ast: sp.Matrix ([[self._ast2spt (e)] for e in ast.vec]),
		'mat': lambda self, ast: sp.Matrix ([[self._ast2spt (e) for e in row] for row in ast.mat]),
		'piece': lambda self, ast: sp.Piecewise (*((self._ast2spt (p [0]), True if p [1] is True else self._ast2spt (p [1])) for p in ast.piece)),
		'lamb': lambda self, ast: sp.Lambda (tuple (self._ast2spt (v) for v in ast.vars), self._ast2spt (ast.lamb)),
		'idx': _ast2spt_idx, # lambda self, ast: self._ast2spt (ast.obj) [self._ast2spt (ast.idx [0]) if len (ast.idx) == 1 else tuple (self._ast2spt (i) for i in ast.idx)], #
		'slice': lambda self, ast: slice (*(self._ast2spt (a) if a else a for a in _ast_slice_bounds (ast, None))),

		'text': lambda self, ast: ast.spt,
	}

#...............................................................................................
def spt2ast (spt): # sympy tree (expression) -> abstract syntax tree
	for cls in spt.__class__.__mro__:
		func = _spt2ast_funcs.get (cls)

		if func:
			return func (spt)

	tex = sp.latex (spt)

	if tex [0] == '<' and tex [-1] == '>': # for Python repr style of objects <class something> TODO: Move this to Javascript.
		tex = '\\text{' + tex.replace ("<", "&lt;").replace (">", "&gt;").replace ("\n", "") + '}'

	return AST ('text', tex, str (spt), str (spt), spt)

_rec_num_deconstructed = re.compile (r'^(-?)(\d*[^0.e])?(0*)(?:(\.)(0*)(\d*[^0e])?(0*))?(?:([eE])([+-]?\d+))?$') # -101000.000101000e+123 -> (-) (101) (000) (.) (000) (101) (000) (e) (+123)

def _spt2ast_num (spt):
	m = _rec_num_deconstructed.match (str (spt))
	g = [g or '' for g in m.groups ()]

	if g [5]:
		return AST ('#', ''.join (g [:6] + g [7:]))

	e = len (g [2]) + (int (g [8]) if g [8] else 0)

	return AST ('#', \
			f'{g [0]}{g [1]}e+{e}'     if e >= 16 else \
			f'{g [0]}{g [1]}{"0" * e}' if e >= 0 else \
			f'{g [0]}{g [1]}e{e}')

def _spt2ast_MatrixBase (spt):
	return \
			AST ('mat', tuple (tuple (spt2ast (e) for e in spt [row, :]) for row in range (spt.rows))) \
			if spt.cols > 1 else \
			AST ('vec', tuple (spt2ast (e) for e in spt)) \
			if spt.rows > 1 else \
 			spt2ast (spt [0])

def _spt2ast_Add (spt):
	args = spt._sorted_args

	for arg in args:
		if isinstance (arg, sp.Order):
			break
	else:
		args = args [::-1]

	return AST ('+', tuple (spt2ast (arg) for arg in args))

def _spt2ast_Mul (spt):
	if spt.args [0] == -1:
		return AST ('-', spt2ast (sp.Mul (*spt.args [1:])))

	if spt.args [0].is_negative and isinstance (spt, sp.Number):
		return AST ('-', spt2ast (sp.Mul (-spt.args [0], *spt.args [1:])))

	numer = []
	denom = []

	for arg in spt.args:
		if isinstance (arg, sp.Pow) and arg.args [1].is_negative:
			denom.append (spt2ast (sp.Pow (arg.args [0], -arg.args [1])))
		else:
			numer.append (spt2ast (arg))

	if not denom:
		return AST ('*', tuple (numer)) if len (numer) > 1 else numer [0]

	if not numer:
		return AST ('/', AST.One, AST ('*', tuple (denom)) if len (denom) > 1 else denom [0])

	return AST ('/', AST ('*', tuple (numer)) if len (numer) > 1 else numer [0], \
			AST ('*', tuple (denom)) if len (denom) > 1 else denom [0])

def _spt2ast_Pow (spt):
	if spt.args [1].is_negative:
		return AST ('/', AST.One, spt2ast (sp.Pow (spt.args [0], -spt.args [1])))

	if spt.args [1] == 0.5:
		return AST ('sqrt', spt2ast (spt.args [0]))

	return AST ('^', spt2ast (spt.args [0]), spt2ast (spt.args [1]))

def _spt2ast_MatPow (spt):
	try: # compensate for some MatPow.doit() != mat**pow
		return spt2ast (spt.args [0] ** spt.args [1])
	except:
		return AST ('^', spt2ast (spt.args [0]), spt2ast (spt.args [1]))

def _spt2ast_Function (spt, name = None):
	if name is None:
		name = spt.__class__.__name__

	return AST ('func', \
			f'{AST.Func.ESCAPE}{name}' \
			if getattr (spt, 'SYMPAD_ESCAPED', None) else \
			name \
			, tuple (spt2ast (arg) for arg in spt.args))

def _spt2ast_Derivative (spt):
	return AST ('diff', spt2ast (spt.args [0]), tuple ( \
			('@', f'd{s.name}') if p == 1 else ('^', ('@', f'd{s.name}'), ('#', str (p))) \
			for s, p in spt.args [1:]))

def _spt2ast_Integral (spt):
	return \
			AST ('intg', spt2ast (spt.args [0]), AST ('@', f'd{spt2ast (spt.args [1] [0]) [1]}'), spt2ast (spt.args [1] [1]), spt2ast (spt.args [1] [2])) \
			if len (spt.args [1]) == 3 else \
			AST ('intg', spt2ast (spt.args [0]), AST ('@', f'd{spt2ast (spt.args [1] [0]) [1]}'))

_spt2ast_Limit_dirs = {'+': ('+',), '-': ('-',), '+-': ()}

_spt2ast_funcs = {
	ExprNoEval: lambda spt: spt.SYMPAD_eval (),

	None.__class__: lambda spt: AST.None_,
	True.__class__: lambda spt: AST.True_,
	False.__class__: lambda spt: AST.False_,
	int: lambda spt: AST ('#', str (spt)),
	str: lambda spt: AST ('"', spt),
	tuple: lambda spt: AST ('(', (',', tuple (spt2ast (e) for e in spt))),
	list: lambda spt: AST ('[', tuple (spt2ast (e) for e in spt)),
	bool: lambda spt: AST.True_ if spt else AST.False_,
	sp.Tuple: lambda spt: spt2ast (spt.args),

	sp.Integer: _spt2ast_num,
	sp.Float: _spt2ast_num,
	sp.Rational: lambda spt: AST ('/', ('#', str (spt.p)), ('#', str (spt.q))) if spt.p >= 0 else AST ('-', ('/', ('#', str (-spt.p)), ('#', str (spt.q)))),
	sp.numbers.ImaginaryUnit: lambda ast: AST.I,
	sp.numbers.Pi: lambda spt: AST.Pi,
	sp.numbers.Exp1: lambda spt: AST.E,
	sp.numbers.Infinity: lambda spt: AST.Infty,
	sp.numbers.NegativeInfinity: lambda spt: AST ('-', AST.Infty),
	sp.numbers.ComplexInfinity: lambda spt: AST.CInfty,
	sp.numbers.NaN: lambda spt: AST.NaN,
	sp.Symbol: lambda spt: AST ('@', spt.name),

	sp.boolalg.BooleanTrue: lambda spt: AST.True_,
	sp.boolalg.BooleanFalse: lambda spt: AST.False_,
	sp.Eq: lambda spt: AST ('=', '=', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Ne: lambda spt: AST ('=', '!=', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Lt: lambda spt: AST ('=', '<', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Le: lambda spt: AST ('=', '<=', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Gt: lambda spt: AST ('=', '>', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Ge: lambda spt: AST ('=', '>=', spt2ast (spt.args [0]), spt2ast (spt.args [1])),

	sp.fancysets.Complexes: lambda spt: AST.Complexes,

	sp.matrices.MatrixBase: _spt2ast_MatrixBase,

	sp.Add: _spt2ast_Add,
	sp.Mul: _spt2ast_Mul,
	sp.Pow: _spt2ast_Pow,
	sp.MatPow: _spt2ast_MatPow,

	sp.Abs: lambda spt: AST ('|', spt2ast (spt.args [0])),
	sp.arg: lambda spt: AST ('func', 'arg', (spt2ast (spt.args [0]),)),
	sp.exp: lambda spt: AST ('^', AST.E, spt2ast (spt.args [0])),
	sp.factorial: lambda spt: AST ('!', spt2ast (spt.args [0])),
	sp.Function: _spt2ast_Function,
	sp.functions.elementary.trigonometric.TrigonometricFunction: _spt2ast_Function,
	sp.functions.elementary.hyperbolic.HyperbolicFunction: _spt2ast_Function,
	sp.functions.elementary.trigonometric.InverseTrigonometricFunction: _spt2ast_Function,
	sp.functions.elementary.hyperbolic.InverseHyperbolicFunction: _spt2ast_Function,
	sp.log: lambda spt: AST ('log', spt2ast (spt.args [0])) if len (spt.args) == 1 else AST ('log', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Min: lambda spt: AST ('func', 'Min', ((spt2ast (spt.args [0]) if len (spt.args) == 1 else spt2ast (spt.args)),)),
	sp.Max: lambda spt: AST ('func', 'Max', ((spt2ast (spt.args [0]) if len (spt.args) == 1 else spt2ast (spt.args)),)),

	sp.Limit: lambda spt: AST (*(('lim', spt2ast (spt.args [0]), spt2ast (spt.args [1]), spt2ast (spt.args [2])) + _spt2ast_Limit_dirs [spt.args [3].name])),
	sp.Sum: lambda spt: AST ('sum', spt2ast (spt.args [0]), spt2ast (spt.args [1] [0]), spt2ast (spt.args [1] [1]), spt2ast (spt.args [1] [2])),
	sp.Derivative: _spt2ast_Derivative,
	sp.Integral: _spt2ast_Integral,

	sp.Order: lambda spt: AST ('func', 'O', ((spt2ast (spt.args [0]) if spt.args [1] [1] == 0 else spt2ast (spt.args)),)),
	sp.Piecewise: lambda spt: AST ('piece', tuple ((spt2ast (t [0]), True if isinstance (t [1], sp.boolalg.BooleanTrue) else spt2ast (t [1])) for t in spt.args)),
	sp.Lambda: lambda spt: AST ('lamb', spt2ast (spt.args [1]), tuple (spt2ast (v) for v in spt.args [0])),
}

#...............................................................................................
def set_precision (ast): # recurse through ast to set sympy float precision according to longest string of digits found
	global _SYMPY_FLOAT_PRECISION

	prec  = 15
	stack = [ast]

	while stack:
		ast = stack.pop ()

		if not isinstance (ast, AST):
			pass # nop
		elif ast.is_num:
			prec = max (prec, len (ast.num)) # will be a little more than number of digits to compensate for falling precision with some calculations
		else:
			stack.extend (ast [1:])

	_SYMPY_FLOAT_PRECISION = prec if prec > 15 else None

def set_user_funcs (user_funcs):
	global _USER_FUNCS

	_USER_FUNCS = user_funcs

class sym: # for single script
	set_precision  = set_precision
	set_user_funcs = set_user_funcs
	ast2tex        = ast2tex
	ast2nat        = ast2nat
	ast2py         = ast2py
	ast2spt        = ast2spt
	spt2ast        = spt2ast

_RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
	ast = AST ('*', (('#', '-1'), ('@', 'x')))
	res = ast2nat (ast)
	# res = spt2ast (res)
	print (res)
