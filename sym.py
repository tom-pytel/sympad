# Convert between internal AST and SymPy expressions and write out LaTeX, native shorthand and Python code.
# Here be dragons! MUST REFACTOR AT SOME POINT!

from ast import literal_eval
from functools import reduce
import re
import sympy as sp
from sympy.core.function import AppliedUndef as sp_AppliedUndef

from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sxlat         # AUTO_REMOVE_IN_SINGLE_SCRIPT

_SYMPY_FLOAT_PRECISION = None
_USER_FUNCS            = {} # dict user funcs {name: AST, ...}
_POST_SIMPLIFY         = True # post-evaluation simplification
_PYS                   = True # Python S() escaping
_DOIT                  = True # expression doit()

class _None: pass # unique non-None None marker

class AST_Text (AST): # for displaying elements we do not know how to handle, only returned from SymPy processing, not passed in
	op, is_text = 'text', True

	def _init (self, tex = None, nat = None, py = None, spt = None):
		self.tex, self.nat, self.py, self.spt = tex, nat, py, spt

AST.register_AST (AST_Text)

class ExprAss (sp.Eq): # assignment instead of equality comparison
	pass

class ExprNoEval (sp.Expr): # prevent any kind of evaluation on AST on instantiation or doit, args = (str (AST), sp.S.One)
	is_number  = False
	SYMPAD_ast = lambda self: AST (*literal_eval (self.args [0]))

	def SYMPAD_eval (self):
		return self.SYMPAD_ast () if self.args [1] == 1 else AST ('-func', AST.Func.NOEVAL, (self.SYMPAD_ast (), spt2ast (self.args [1] - 1)))

def _raise (exc):
	raise exc

def _sympify (spt, sympify = sp.sympify, fallback = None): # try to sympify argument with optional fallback conversion function
	ret = _None

	if fallback is True: # True for return original value
		ret = spt

	else: # func for conversion function
		try:
			ret = fallback (spt)
		except:
			pass

	try:
		ret = sympify (spt)

	except:
		if ret is _None:
			raise

	return ret

def _simplify (spt):
	if isinstance (spt, (bool, int, float, complex, str, slice)):
		return spt

	if isinstance (spt, (tuple, list, set, frozenset)):
		return spt.__class__ (_simplify (a) for a in spt)

	if isinstance (spt, dict):
		return dict ((_simplify (k), _simplify (v)) for k, v in spt.items ())

	try:
		spt2 = sp.simplify (spt)

		if sp.count_ops (spt2) <= sp.count_ops (spt): # sometimes simplify doesn't
			spt = spt2

	except:
		pass

	return spt

def _Mul (*args):
	itr = iter (args)
	res = next (itr)

	for arg in itr:
		try:
			res = res * arg
		except:
			res = sp.sympify (res) * sp.sympify (arg)

	return res

def _Pow (base, exp): # fix inconsistent sympy Pow (..., evaluate = True)
	return base**exp

def _fltoint (num):
	return int (num) if isinstance (num, int) or num.is_integer () else num

def _trail_comma (obj):
	return ',' if len (obj) == 1 else ''

def _ast_is_neg (ast):
	return ast.is_minus or ast.is_num_neg or (ast.is_mul and _ast_is_neg (ast.mul [0]))

def _ast_is_neg_nominus (ast):
	return ast.is_num_neg or (ast.is_mul and _ast_is_neg (ast.mul [0]))

def _ast_slice_bounds (ast, None_ = AST.VarNull):
	return tuple (a or None_ for a in ((ast.start, ast.stop) if ast.step is None else (ast.start, ast.stop, ast.step)))

def _ast_followed_by_slice (ast, seq):
	try:
		return seq [seq.index (ast) + 1].is_slice
	except:
		pass

	return False

def _ast_func_call (func, args, _ast2spt = None, is_escaped = False):
	if _ast2spt is None:
		_ast2spt = ast2spt

	pyargs, pykw = AST.args2kwargs (args, _ast2spt)

	spt          = func (*pyargs, **pykw)

	if type (spt) is func: # try to pass func name escaped status through SymPy object
		try:
			spt.SYMPAD_ESCAPED = is_escaped
		except (AttributeError, TypeError): # couldn't assign to Python object (probably because is built-in type or otherwise has no __dict__)
			pass

	return spt

#...............................................................................................
class ast2tex: # abstract syntax tree -> LaTeX text
	def __init__ (self): self.parent = self.ast = None # pylint medication
	def __new__ (cls, ast, xlat = True):
		def func_call (func, args):
			return spt2ast (_ast_func_call (getattr (sp, func), args))

		self         = super ().__new__ (cls)
		self.parents = [None]
		self.parent  = self.ast = AST ()

		if xlat:
			ast = sxlat.xlat_funcs2asts (ast, sxlat.XLAT_FUNC2AST_TEX, func_call = func_call)

		return self._ast2tex (ast)

	def _ast2tex (self, ast):
		self.parents.append (self.ast)

		self.parent = self.ast
		self.ast    = ast

		ast         = self._ast2tex_funcs [ast.op] (self, ast)

		del self.parents [-1]

		self.ast    = self.parent
		self.parent = self.parents [-1]

		return ast

	def _ast2tex_wrap (self, obj, curly = None, paren = None):
		s = self._ast2tex (obj) if isinstance (obj, AST) else str (obj)

		if (obj.op in paren) if isinstance (paren, set) else paren:
			return f'\\left({s} \\right)'

		if (obj.op in curly) if isinstance (curly, set) else curly:
			return f'{{{s}}}'

		return s

	def _ast2tex_curly (self, ast):
		return \
				f'{self._ast2tex (ast)}'     if ast.is_single_unit else \
				f'{{{self._ast2tex (ast)}}}' if not ast.is_comma else \
				f'{{\\left({self._ast2tex (ast)}\\right)}}'

	def _ast2tex_paren (self, ast, ops = {}):
		return self._ast2tex_wrap (ast, 0, not (ast.is_paren or (ops and ast.op not in ops)))

	def _ast2tex_paren_mul_exp (self, ast, ret_has = False, also = {'=', '<>', '+', '-slice', '||', '^^', '&&', '-or', '-and', '-not'}):
		if ast.is_mul:
			s, has = self._ast2tex_mul (ast, True)
		else:
			s, has = self._ast2tex (ast), ast.op in also

		s = self._ast2tex_wrap (s, 0, has)

		return (s, has) if ret_has else s

	def _ast2tex_ass_hs (self, hs, lhs = True):
		return self._ast2tex_wrap (hs, 0, hs.is_ass or hs.is_slice or (lhs and hs.op in {',', '-piece'}))

	def _ast2tex_cmp_hs (self, hs):
		return self._ast2tex_wrap (hs, 0, {'=', '<>', '-piece', '-slice', '-or', '-and', '-not'})

	def _ast2tex_num (self, ast):
		m, e = ast.num_mant_and_exp

		return f'{m}{{e}}{{{e}}}' if e else m

	def _ast2tex_var (self, ast):
		if not ast.var:
			return '{}' # Null var

		v = ast.as_var.var
		n = v.replace ('_', '\\_')
		t = AST.Var.PY2TEX.get (n)

		return \
				f'{t or n}'      if not ast.diff_or_part_type else \
				f'd{t or n}'     if ast.is_diff_any else \
				f'\\partial'     if ast.is_part_solo else \
				f'\\partial{t}'  if t else \
				f'\\partial {n}' if n else \
				f'\\partial'

	def _ast2tex_attr (self, ast):
		tex = sxlat.xlat_attr2tex (ast, self._ast2tex)

		if tex is not None:
			return tex

		a = ast.attr.replace ('_', '\\_')

		if ast.is_attr_func:
			a = f'\\operatorname{{{a}}}{self._ast2tex_paren (AST.tuple2ast (ast.args))}'

		return f'{self._ast2tex_paren (ast.obj, {"=", "<>", "#", ",", "-", "+", "*", "/", "-lim", "-sum", "-int", "-piece", "-slice", "||", "^^", "&&", "-or", "-and", "-not"})}.{a}'

	def _ast2tex_add (self, ast):
		terms = []

		for n in ast.add:
			not_first = n is not ast.add [0]
			not_last  = n is not ast.add [-1]
			op        = ' + '

			if n.is_minus and not_first: # and n.minus.is_num_pos
				op, n = ' - ', n.minus

			terms.extend ([op, self._ast2tex_wrap (n,
				n.is_piece or (not_first and _ast_is_neg_nominus (n)) or ((n.strip_mmls.is_intg or (n.is_mul and n.mul [-1].strip_mmls.is_intg)) and not_last),
				(n.is_piece and not_last) or n.op in {'=', '<>', '+', '-slice', '||', '^^', '&&', '-or', '-and', '-not'})])

		return ''.join (terms [1:]).replace (' + -', ' - ')

	def _ast2tex_mul (self, ast, ret_has = False):
		t   = []
		p   = None
		has = False

		for n in ast.mul:
			s = self._ast2tex_wrap (n, \
					(p and _ast_is_neg (n)) or (n.strip_mmls.is_intg and n is not ast.mul [-1]), \
					n.op in {'=', '<>', '+', '-slice', '||', '^^', '&&', '-or', '-and', '-not'} or (n.is_piece and n is not ast.mul [-1]))

			if p and p.is_attr and s [:6] == '\\left(':
				s = self._ast2tex_wrap (s, 1)

			if p and (n.op in {'#', '-mat'} or n.is_null_var or p.strip_minus.op in {'-lim', '-sum', '-diff', '-int', '-mat'} or \
					_ast_is_neg (n) or s [:6] == '\\left[' or \
					n.strip_fdpi.strip_paren.is_comma or \
					(p.is_var_lambda and (self.parent.is_slice or (self.parent.is_comma and _ast_followed_by_slice (ast, self.parent.comma)))) or \
					(n.op in {'/', '-diff'} and p.op in {'#', '/'}) or \
					(n.is_paren and p.is_var and p.var in _USER_FUNCS) or \
					(n.is_attr and n.strip_attr.strip_paren.is_comma) or \
					(p.is_div and (p.numer.is_diff_or_part_solo or (p.numer.is_pow and p.numer.base.is_diff_or_part_solo))) or \
					(n.is_pow and (n.base.is_num_pos or n.base.strip_paren.is_comma)) or \
					(n.is_idx and (n.obj.is_idx or n.obj.strip_paren.is_comma))):
				t.append (f' \\cdot {s}')
				has = True

			elif p and (p.op in {'-sqrt'} or p.num_exp or \
					p.strip_minus.is_diff_or_part_any or n.is_diff_or_part_any or \
					(p.is_long_var and n.op not in {'(', '['}) or (n.is_long_var and p.op not in {'(', '['})):
				t.append (f'\\ {s}')

			else:
				t.append (f'{"" if not p else " "}{s}')

			p = n

		return (''.join (t), has) if ret_has else ''.join (t)

	def _ast2tex_pow (self, ast, trighpow = True):
		b = self._ast2tex_wrap (ast.base, {'-mat'}, not (ast.base.op in {'@', '"', '(', '[', '|', '-func', '-mat', '-lamb', '-set', '-dict'} or ast.base.is_num_pos))
		p = self._ast2tex_curly (ast.exp)

		if ast.base.is_trigh_func_noninv and ast.exp.is_single_unit and trighpow:
			i = len (ast.base.func) + (15 if ast.base.func in {'sech', 'csch'} else 1)

			return f'{b [:i]}^{p}{b [i:]}'

		return f'{b}^{p}'

	def _ast2tex_log (self, ast):
		return \
				f'\\ln{self._ast2tex_paren (ast.log)}' \
				if ast.base is None else \
				f'\\log_{self._ast2tex_curly (ast.base)}{self._ast2tex_paren (ast.log)}'

	def _ast2tex_func (self, ast):
		if ast.is_trigh_func:
			n = (f'\\operatorname{{{ast.func [1:]}}}^{{-1}}' \
					if ast.func in {'asech', 'acsch'} else \
					f'\\{ast.func [1:]}^{{-1}}') \
					if ast.func [0] == 'a' else \
					(f'\\operatorname{{{ast.func}}}' if ast.func in {'sech', 'csch'} else f'\\{ast.func}')

			return f'{n}\\left({self._ast2tex (AST.tuple2ast (ast.args))} \\right)'

		tex = sxlat.xlat_func2tex (ast, self._ast2tex)

		if tex is not None:
			return tex

		if ast.func in AST.Func.TEX:
			return f'\\{ast.func}\\left({self._ast2tex (AST.tuple2ast (ast.args))} \\right)'
		else:
			return '\\operatorname{' + ast.func.replace ('_', '\\_').replace (AST.Func.NOEVAL, '\\%') + f'}}\\left({self._ast2tex (AST.tuple2ast (ast.args))} \\right)'

	def _ast2tex_lim (self, ast):
		s = self._ast2tex_wrap (ast.to, False, ast.to.is_slice) if ast.dir is None else (self._ast2tex_pow (AST ('^', ast.to, AST.Zero), trighpow = False) [:-1] + ast.dir)

		return f'\\lim_{{{self._ast2tex (ast.lvar)} \\to {s}}} {self._ast2tex_paren_mul_exp (ast.lim)}'

	def _ast2tex_sum (self, ast):
		return f'\\sum_{{{self._ast2tex (ast.svar)} = {self._ast2tex (ast.from_)}}}^{self._ast2tex_curly (ast.to)} {self._ast2tex_paren_mul_exp (ast.sum)}' \

	_rec_diff_var_single_start = re.compile (r'^d(?=[^_])')

	def _ast2tex_diff (self, ast):
		ds = set ()
		p  = 0

		for n in ast.dvs:
			if n.is_var:
				p += 1

				if n.var:
					ds.add (n)

			else: # n = ('^', ('@', 'diff or part'), ('#', 'int'))
				p += n.exp.as_int
				ds.add (n.base)

		if not ds:
			return f'\\frac{{d}}{{}}{self._ast2tex_paren (ast.diff)}'

		dv = next (iter (ds))

		if len (ds) == 1 and not dv.is_partial:
			return f'\\frac{{d{"" if p == 1 else f"^{p}"}}}{{{" ".join (self._ast2tex (n) for n in ast.dvs)}}}{self._ast2tex_paren (ast.diff)}'

		else:
			s = ''.join (self._rec_diff_var_single_start.sub (r'\\partial ', self._ast2tex (n)) for n in ast.dvs)

			return f'\\frac{{\\partial{"" if p == 1 else f"^{p}"}}}{{{s}}}{self._ast2tex_paren (ast.diff)}'

	def _ast2tex_intg (self, ast):
		if ast.intg is None:
			intg = ' '
		else:
			intg = f' {self._ast2tex_wrap (ast.intg, {"-diff", "-slice", "||", "^^", "&&", "-or", "-and", "-not"}, {"=", "<>"})} '

		if ast.from_ is None:
			return f'\\int{intg}\\ {self._ast2tex (ast.dv)}'
		else:
			return f'\\int_{self._ast2tex_curly (ast.from_)}^{self._ast2tex_curly (ast.to)}{intg}\\ {self._ast2tex (ast.dv)}'

	_ast2tex_funcs = {
		';'     : lambda self, ast: ';\\: '.join (self._ast2tex (a) for a in ast.scolon),
		'='     : lambda self, ast: f'{self._ast2tex_ass_hs (ast.lhs)} = {self._ast2tex_ass_hs (ast.rhs, False)}',
		# '<>'    : lambda self, ast: f"""{self._ast2tex_cmp_hs (ast.lhs)} {" ".join (f"{AST.Cmp.PY2TEX.get (r, r).replace ('==', '=')} {self._ast2tex_cmp_hs (e)}" for r, e in ast.cmp)}""",
		'<>'    : lambda self, ast: f"""{self._ast2tex_cmp_hs (ast.lhs)} {" ".join (f"{AST.Cmp.PY2TEX.get (r, r)} {self._ast2tex_cmp_hs (e)}" for r, e in ast.cmp)}""",
		'#'     : _ast2tex_num,
		'@'     : _ast2tex_var,
		'.'     : _ast2tex_attr,
		'"'     : lambda self, ast: '\\text{' + repr (ast.str_).replace ('}', '\\}') + '}',
		','     : lambda self, ast: f'{", ".join (self._ast2tex (c) for c in ast.comma)}{_trail_comma (ast.comma)}',
		'('     : lambda self, ast: self._ast2tex_wrap (ast.paren, 0, not ast.paren.is_lamb),
		'['     : lambda self, ast: f'\\left[{", ".join (self._ast2tex (b) for b in ast.brack)} \\right]',
		'|'     : lambda self, ast: f'\\left|{self._ast2tex (ast.abs)} \\right|',
		'-'     : lambda self, ast: f'-{self._ast2tex_wrap (ast.minus, ast.minus.strip_fdpi.is_num_pos or ast.minus.is_mul, {"=", "<>", "+", "-slice", "||", "^^", "&&", "-or", "-and", "-not"})}',
		'!'     : lambda self, ast: self._ast2tex_wrap (ast.fact, {'^'}, (ast.fact.op not in {'#', '@', '"', '(', '[', '|', '!', '^', '-func', '-mat'} or ast.fact.is_num_neg)) + '!',
		'+'     : _ast2tex_add,
		'*'     : _ast2tex_mul,
		'/'     : lambda self, ast: f'\\frac{{{self._ast2tex_wrap (ast.numer, 0, ast.numer.is_slice or ((ast.numer.base.is_diff_or_part_solo and ast.numer.exp.is_num_pos_int) if ast.numer.is_pow else ast.numer.is_diff_or_part_solo))}}}{{{self._ast2tex_wrap (ast.denom, 0, {"-slice"})}}}',
		'^'     : _ast2tex_pow,
		'-log'  : _ast2tex_log,
		'-sqrt' : lambda self, ast: f'\\sqrt{{{self._ast2tex_wrap (ast.rad, 0, {",", "-slice"})}}}' if ast.idx is None else f'\\sqrt[{self._ast2tex (ast.idx)}]{{{self._ast2tex_wrap (ast.rad, 0, {",", "-slice"})}}}',
		'-func' : _ast2tex_func,
		'-lim'  : _ast2tex_lim,
		'-sum'  : _ast2tex_sum,
		'-diff' : _ast2tex_diff,
		'-difp' : lambda self, ast: self._ast2tex_wrap (ast.diffp, 0, ast.diffp.is_num_neg or ast.diffp.op in {"=", "<>", "-", "+", "*", "/", "^", "-sqrt", "-lim", "-sum", "-diff", "-int", "-piece", "-slice", "||", "^^", "&&", "-or", "-and", "-not"}) + "'" * ast.count,
		'-int'  : _ast2tex_intg,
		'-mat'  : lambda self, ast: '\\begin{bmatrix} ' + r' \\ '.join (' & '.join (self._ast2tex_wrap (e, 0, e.is_slice) for e in row) for row in ast.mat) + f'{" " if ast.mat else ""}\\end{{bmatrix}}',
		'-piece': lambda self, ast: '\\begin{cases} ' + r' \\ '.join (f'{self._ast2tex_wrap (p [0], 0, {"=", "<>", ",", "-slice"})} & \\text{{otherwise}}' if p [1] is True else f'{self._ast2tex_wrap (p [0], 0, {"=", "<>", ",", "-slice"})} & \\text{{for}}\\: {self._ast2tex_wrap (p [1], 0, {"-slice"})}' for p in ast.piece) + ' \\end{cases}',
		'-lamb' : lambda self, ast: f'\\left({self._ast2tex (AST ("@", ast.vars [0]) if ast.vars.len == 1 else AST ("(", (",", tuple (("@", v) for v in ast.vars))))} \\mapsto {self._ast2tex_wrap (ast.lamb, 0, ast.lamb.is_ass)} \\right)',
		'-idx'  : lambda self, ast: f'{self._ast2tex_wrap (ast.obj, {"^", "-slice"}, ast.obj.is_num_neg or ast.obj.op in {"=", "<>", ",", "-", "+", "*", "/", "-lim", "-sum", "-diff", "-int", "-piece", "||", "^^", "&&", "-or", "-and", "-not"})}\\left[{self._ast2tex (AST.tuple2ast (ast.idx))} \\right]',
		'-slice': lambda self, ast: '{:}'.join (self._ast2tex_wrap (a, a and _ast_is_neg (a), a and a.op in {'=', ',', '-slice'}) for a in _ast_slice_bounds (ast, '')),
		'-set'  : lambda self, ast: f'\\left\\{{{", ".join (self._ast2tex_wrap (c, 0, c.is_slice) for c in ast.set)} \\right\\}}' if ast.set else '\\emptyset',
		'-dict' : lambda self, ast: f'\\left\\{{{", ".join (f"{self._ast2tex_wrap (k, 0, k.is_slice)}{{:}} {self._ast2tex_wrap (v, 0, v.is_slice)}" for k, v in ast.dict)} \\right\\}}',
		'||'    : lambda self, ast: ' \\cup '.join (self._ast2tex_wrap (a, 0, a.op in {'=', '<>', ',', '-slice', '-or', '-and', '-not'} or (a.is_piece and a is not ast.union [-1])) for a in ast.union),
		'^^'    : lambda self, ast: ' \\ominus '.join (self._ast2tex_wrap (a, 0, a.op in {'=', '<>', ',', '-slice', '||', '-or', '-and', '-not'} or (a.is_piece and a is not ast.sdiff [-1])) for a in ast.sdiff),
		'&&'    : lambda self, ast: ' \\cap '.join (self._ast2tex_wrap (a, 0, a.op in {'=', '<>', ',', '-slice', '||', '^^', '-or', '-and', '-not'} or (a.is_piece and a is not ast.xsect [-1])) for a in ast.xsect),
		'-or'   : lambda self, ast: ' \\vee '.join (self._ast2tex_wrap (a, 0, a.op in {'=', ',', '-slice'} or (a.is_piece and a is not ast.or_ [-1])) for a in ast.or_),
		'-and'  : lambda self, ast: ' \\wedge '.join (self._ast2tex_wrap (a, 0, a.op in {'=', ',', '-slice', '-or'} or (a.is_piece and a is not ast.and_ [-1])) for a in ast.and_),
		'-not'  : lambda self, ast: f'\\neg\\ {self._ast2tex_wrap (ast.not_, 0, ast.not_.op in {"=", ",", "-slice", "-or", "-and"})}',
		'-ufunc': lambda self, ast: f'\\operatorname{{?{ast.ufunc}}}\\left({", ".join (ast.vars + tuple (f"{k} = {self._ast2tex_wrap (a, 0, a.is_comma)}" for k, a in ast.kw))} \\right)',

		'text'  : lambda self, ast: ast.tex,
	}

#...............................................................................................
class ast2nat: # abstract syntax tree -> native text
	def __init__ (self): self.parent = self.ast = None # pylint droppings
	def __new__ (cls, ast, xlat = True):
		self         = super ().__new__ (cls)
		self.parents = [None]
		self.parent  = self.ast = AST ()

		if xlat:
			ast = sxlat.xlat_funcs2asts (ast, sxlat.XLAT_FUNC2AST_NAT)

		return self._ast2nat (ast)

	def _ast2nat (self, ast):
		self.parents.append (self.ast)

		self.parent = self.ast
		self.ast    = ast

		nat         = self._ast2nat_funcs [ast.op] (self, ast)

		del self.parents [-1]

		self.ast    = self.parent
		self.parent = self.parents [-1]

		return nat

	def _ast2nat_wrap (self, obj, curly = None, paren = None):
		s = self._ast2nat (obj) if isinstance (obj, AST) else str (obj)

		if (obj.op in paren) if isinstance (paren, set) else paren:
			return f'({s})'

		if (obj.op in curly) if isinstance (curly, set) else curly:
			return f'{{{s}}}'

		return s

	def _ast2nat_curly (self, ast, ops = {}):
		return self._ast2nat_wrap (ast, ops if ops else (ast.is_div or not ast.is_single_unit or (ast.is_var and ast.var in AST.Var.PY2TEX)))

	def _ast2nat_paren (self, ast, ops = {}):
		return self._ast2nat_wrap (ast, 0, not (ast.is_paren or (ops and ast.op not in ops)))

	def _ast2nat_curly_mul_exp (self, ast, ret_has = False, also = {}):
		if ast.is_mul:
			s, has = self._ast2nat_mul (ast, True)
		else:
			s, has = self._ast2nat (ast), False

		has = has or ((ast.op in also) if isinstance (also, set) else also)
		s   = self._ast2nat_wrap (s, has)

		return (s, has) if ret_has else s

	def _ast2nat_ass_hs (self, hs, lhs = True):
		return self._ast2nat_wrap (hs, 0, hs.is_ass or hs.is_slice or (lhs and hs.op in {',', '-piece', '-lamb'}) or \
				(not lhs and hs.is_lamb and self.parent.op in {'-set', '-dict'}))

	def _ast2nat_cmp_hs (self, hs):
		return self._ast2nat_wrap (hs, 0, {'=', '<>', '-piece', '-lamb', '-slice', '-or', '-and', '-not'})

	def _ast2nat_attr (self, ast):
		obj = self._ast2nat_paren (ast.obj, {"=", "<>", "#", ",", "-", "+", "*", "/", "-lim", "-sum", "-int", "-piece", "-lamb", "-slice", "||", "^^", "&&", "-or", "-and", "-not"})

		if ast.is_attr_var:
			return f'{obj}.{ast.attr}'
		else:
			return f'{obj}.{ast.attr}{self._ast2nat_paren (AST.tuple2ast (ast.args))}'

	def _ast2nat_str (self, ast):
		s = repr (ast.str_)

		return s if s [0] != "'" else f' {s}'

	def _ast2nat_add (self, ast):
		terms = []

		for n in ast.add:
			not_first = n is not ast.add [0]
			not_last  = n is not ast.add [-1]
			op        = ' + '

			if n.is_minus and not_first: # and n.minus.is_num_pos
				op, n = ' - ', n.minus

			terms.extend ([op, self._ast2nat_wrap (n,
				n.is_piece or (not_first and _ast_is_neg_nominus (n)) or ((n.strip_mmls.is_intg or (n.is_mul and n.mul [-1].strip_mmls.is_intg)) and not_last),
				(n.op in ('-piece', '-lamb') and not_last) or n.op in {'=', '<>', '+', '-lamb', '-slice', '||', '^^', '&&', '-or', '-and', '-not'})])

		return ''.join (terms [1:]).replace (' + -', ' - ')

	def _ast2nat_mul (self, ast, ret_has = False):
		t   = []
		p   = None
		has = False

		for n in ast.mul:
			s = self._ast2nat_wrap (n, \
					(p and _ast_is_neg (n)) or n.is_piece or (n.strip_mmls.is_intg and n is not ast.mul [-1]), \
					n.op in {'=', '<>', '+', '-lamb', '-slice', '||', '^^', '&&', '-or', '-and', '-not'} or (n.is_piece and n is not ast.mul [-1]))

			if p and (n.op in {'#', '-lim', '-sum', '-int'} or n.is_null_var or p.strip_minus.op in {'-lim', '-sum', '-diff', '-int'} or \
					n.op in {'/', '-diff'} or p.strip_minus.op in {'/', '-diff'} or s [:1] == '[' or \
					n.strip_fdpi.strip_paren.is_comma or (n.is_pow and n.base.strip_paren.is_comma) or \
					(p.is_var_lambda and (self.parent.is_slice or (self.parent.is_comma and _ast_followed_by_slice (ast, self.parent.comma)))) or \
					(s [:1] == '(' and ((p.is_var and p.var in _USER_FUNCS) or p.is_attr_var or (p.is_pow and p.exp.is_attr_var))) or \
					(n.is_pow and n.base.is_num_pos) or \
					(n.is_attr and n.strip_attr.strip_paren.is_comma) or \
					(n.is_idx and (n.obj.is_idx or n.obj.strip_paren.is_comma))):
				t.append (f' * {s}')
				has = True

			elif p and (p.is_diff_or_part_solo or \
					(n.op not in {'#', '(', '|', '^'} or p.op not in {'#', '(', '|'})):
				t.append (f' {s}')

			else:
				t.append (s)

			p = n

		return (''.join (t), has) if ret_has else ''.join (t)

	def _ast2nat_div (self, ast):
		n, ns = (self._ast2nat_wrap (ast.numer, 1), True) if _ast_is_neg (ast.numer) else \
				(self._ast2nat_wrap (ast.numer, 0, 1), True) if (ast.numer.is_slice or ((ast.numer.base.is_diff_or_part_solo and ast.numer.exp.is_num_pos_int) if ast.numer.is_pow else ast.numer.is_diff_or_part_solo)) else \
				self._ast2nat_curly_mul_exp (ast.numer, True, {'=', '<>', '+', '/', '-lim', '-sum', '-diff', '-int', '-piece', '-lamb', '||', '^^', '&&', '-or', '-and', '-not'})

		d, ds = (self._ast2nat_wrap (ast.denom, 1), True) if (_ast_is_neg (ast.denom) and ast.denom.strip_minus.is_div) else \
				(self._ast2nat_wrap (ast.denom, 0, 1), True) if ast.denom.is_slice else \
				self._ast2nat_curly_mul_exp (ast.denom, True, {'=', '<>', '+', '/', '-lim', '-sum', '-diff', '-int', '-piece', '-lamb', '||', '^^', '&&', '-or', '-and', '-not'})
		s     = ns or ds or ast.numer.strip_minus.op not in {'#', '@'} or ast.denom.strip_minus.op not in {'#', '@'}

		return f'{n}{" / " if s else "/"}{d}'

	def _ast2nat_pow (self, ast, trighpow = True):
		b = self._ast2nat_wrap (ast.base, 0, not (ast.base.op in {'@', '"', '(', '[', '|', '-func', '-mat', '-set', '-dict'} or ast.base.is_num_pos))
		p = self._ast2nat_wrap (ast.exp, ast.exp.strip_minus.op in {'=', '<>', '+', '*', '/', '-lim', '-sum', '-diff', '-int', '-piece', '-lamb', '-slice', '||', '^^', '&&', '-or', '-and', '-not'}, {","})

		if ast.base.is_trigh_func_noninv and ast.exp.is_single_unit and trighpow:
			i = len (ast.base.func)

			return f'{b [:i]}**{p}{b [i:]}'

		return f'{b}**{p}'

	def _ast2nat_log (self, ast):
		return \
				f'ln{self._ast2nat_paren (ast.log)}' \
				if ast.base is None else \
				f'\\log_{self._ast2nat_curly (ast.base)}{self._ast2nat_paren (ast.log)}'

	def _ast2nat_lim (self, ast):
		s = self._ast2nat_wrap (ast.to, (ast.to.is_ass and ast.to.rhs.is_lamb) or ast.to.op in {'-lamb', '-piece'}, ast.to.is_slice) if ast.dir is None else (self._ast2nat_pow (AST ('^', ast.to, AST.Zero), trighpow = False) [:-1] + ast.dir)

		return f'\\lim_{{{self._ast2nat (ast.lvar)} \\to {s}}} {self._ast2nat_curly_mul_exp (ast.lim, False, ast.lim.op in {"=", "<>", "+", "-piece", "-lamb", "-slice", "||", "^^", "&&", "-or", "-and", "-not"} or ast.lim.is_mul_has_abs)}'

	def _ast2nat_sum (self, ast):
		return f'\\sum_{{{self._ast2nat (ast.svar)} = {self._ast2nat_curly (ast.from_, {"-lamb", "-piece"})}}}^{self._ast2nat_curly (ast.to)} {self._ast2nat_curly_mul_exp (ast.sum, False, ast.sum.op in {"=", "<>", "+", "-piece", "-lamb", "-slice", "||", "^^", "&&", "-or", "-and", "-not"} or ast.sum.is_mul_has_abs)}'

	def _ast2nat_diff (self, ast):
		p = 0
		d = ''

		for n in ast.dvs:
			if n.is_var:
				d  = n.diff_or_part_type
				p += 1
			else: # n = ('^', ('@', 'differential'), ('#', 'int'))
				d  = n.base.diff_or_part_type
				p += n.exp.as_int

		return f'{d.strip () if d else "d"}{"" if p == 1 else f"^{p}"} / {" ".join (self._ast2nat (n) for n in ast.dvs)} {self._ast2nat_paren (ast.diff)}'

	def _ast2nat_intg (self, ast):
		if ast.intg is None:
			intg = ' '
		else:
			intg = f' {self._ast2nat_wrap (ast.intg, ast.intg.op in {"-diff", "-piece", "-slice"} or ast.intg.is_mul_has_abs, {"=", "<>", "-lamb", "||", "^^", "&&", "-or", "-and", "-not"})} '

		if ast.from_ is None:
			return f'\\int{intg}{self._ast2nat (ast.dv)}'
		else:
			return f'\\int_{self._ast2nat_curly (ast.from_)}^{self._ast2nat_curly (ast.to)}{intg}{self._ast2nat (ast.dv)}'

	def _ast2nat_mat (self, ast):
		if not ast.rows:
			return '\\[]'
		elif ast.is_mat_column and not any (r [0].is_brack for r in ast.mat): # (ast.rows > 1 or not ast.mat [0] [0].is_brack):
			return f"\\[{', '.join (self._ast2nat (row [0]) for row in ast.mat)}]"
		else:
			return f"""\\[{', '.join (f'[{", ".join (self._ast2nat (e) for e in row)}]' for row in ast.mat)}]"""

	_ast2nat_funcs = {
		';'     : lambda self, ast: '; '.join (self._ast2nat (a) for a in ast.scolon),
		'='     : lambda self, ast: f'{self._ast2nat_ass_hs (ast.lhs)} = {self._ast2nat_ass_hs (ast.rhs, False)}',
		'<>'    : lambda self, ast: f'{self._ast2nat_cmp_hs (ast.lhs)} {" ".join (f"{AST.Cmp.PYFMT.get (r, r)} {self._ast2nat_cmp_hs (e)}" for r, e in ast.cmp)}',
		'#'     : lambda self, ast: ast.num,
		'@'     : lambda self, ast: ast.var,
		'.'     : _ast2nat_attr,
		'"'     : _ast2nat_str,
		','     : lambda self, ast: f'{", ".join (self._ast2nat (c) for c in ast.comma)}{_trail_comma (ast.comma)}',
		'('     : lambda self, ast: f'({self._ast2nat (ast.paren)})',
		'['     : lambda self, ast: f'[{", ".join (self._ast2nat (b) for b in ast.brack)}]',
		'|'     : lambda self, ast: f'{{|{self._ast2nat (ast.abs)}|}}',
		'-'     : lambda self, ast: f'-{self._ast2nat_wrap (ast.minus, ast.minus.strip_fdpi.is_num_pos or ast.minus.op in {"*", "-diff", "-piece"}, {"=", "<>", "+", "-lamb", "-slice", "||", "^^", "&&", "-or", "-and", "-not"})}',
		'!'     : lambda self, ast: self._ast2nat_wrap (ast.fact, {'^'}, ast.fact.op not in {'#', '@', '"', '(', '[', '|', '!', '^', '-func', '-mat'} or ast.fact.is_num_neg) + '!',
		'+'     : _ast2nat_add,
		'*'     : _ast2nat_mul,
		'/'     : _ast2nat_div,
		'^'     : _ast2nat_pow,
		'-log'  : _ast2nat_log,
		'-sqrt' : lambda self, ast: f'sqrt{self._ast2nat_paren (ast.rad)}' if ast.idx is None else f'\\sqrt[{self._ast2nat (ast.idx)}]{{{self._ast2nat_wrap (ast.rad, 0, {",", "-slice"})}}}',
		'-func' : lambda self, ast: f'{ast.func}({self._ast2nat (AST.tuple2ast (ast.args))})',
		'-lim'  : _ast2nat_lim,
		'-sum'  : _ast2nat_sum,
		'-diff' : _ast2nat_diff,
		'-difp' : lambda self, ast: self._ast2nat_wrap (ast.diffp, 0, ast.diffp.is_num_neg or ast.diffp.op in {"=", "<>", "-", "+", "*", "/", "^", "-lim", "-sum", "-diff", "-int", "-piece", "-lamb", "-slice", "||", "^^", "&&", "-or", "-and", "-not"}) + "'" * ast.count,
		'-int'  : _ast2nat_intg,
		'-mat'  : _ast2nat_mat,
		'-piece': lambda self, ast: ' else '.join (f'{self._ast2nat_wrap (p [0], p [0].op in {"=", "-piece", "-lamb"}, {",", "-slice"})}' if p [1] is True else \
				f'{self._ast2nat_wrap (p [0], p [0].op in {"=", "-piece", "-lamb"}, {",", "-slice"})} if {self._ast2nat_wrap (p [1], p [1].op in {"=", "-piece", "-lamb"}, {",", "-slice"})}' for p in ast.piece),
		'-lamb' : lambda self, ast: f'lambda{" " + ", ".join (ast.vars) if ast.vars else ""}: {self._ast2nat_wrap (ast.lamb, ast.lamb.is_lamb, ast.lamb.op in {"=", "<>", "-slice"})}',
		'-idx'  : lambda self, ast: f'{self._ast2nat_wrap (ast.obj, {"^", "-slice"}, ast.obj.is_num_neg or ast.obj.op in {"=", "<>", ",", "+", "*", "/", "-", "-lim", "-sum", "-diff", "-int", "-piece", "-lamb", "||", "^^", "&&", "-or", "-and", "-not"})}[{self._ast2nat (AST.tuple2ast (ast.idx))}]',
		'-slice': lambda self, ast: ':'.join (self._ast2nat_wrap (a, 0, a.op in {'=', ',', '-lamb', '-slice'}) for a in _ast_slice_bounds (ast)),
		'-set'  : lambda self, ast: f'{{{", ".join (self._ast2nat_wrap (c, 0, c.is_slice) for c in ast.set)}{_trail_comma (ast.set)}}}' if ast.set else '\\{}',
		'-dict' : lambda self, ast: f'{{{", ".join (self._ast2nat_wrap (k, 0, k.op in {"-lamb", "-slice"}) + f": {self._ast2nat_wrap (v, v.is_lamb, v.is_slice)}" for k, v in ast.dict)}}}',
		'||'    : lambda self, ast: ' || '.join (self._ast2nat_wrap (a, 0, a.op in {'=', '<>', ',', '-slice', '-piece', '-lamb', '-or', '-and', '-not'}) for a in ast.union),
		'^^'    : lambda self, ast: ' ^^ '.join (self._ast2nat_wrap (a, 0, a.op in {'=', '<>', ',', '-slice', '-piece', '-lamb', '||', '-or', '-and', '-not'}) for a in ast.sdiff),
		'&&'    : lambda self, ast: ' && '.join (self._ast2nat_wrap (a, 0, a.op in {'=', '<>', ',', '-slice', '-piece', '-lamb', '||', '^^', '-or', '-and', '-not'}) for a in ast.xsect),
		'-or'   : lambda self, ast: ' or '.join (self._ast2nat_wrap (a, 0, a.op in {'=', ',', '-slice', '-piece', '-lamb'}) for a in ast.or_),
		'-and'  : lambda self, ast: ' and '.join (self._ast2nat_wrap (a, 0, a.op in {'=', ',', '-slice', '-piece', '-lamb', '-or'}) for a in ast.and_),
		'-not'  : lambda self, ast: f'not {self._ast2nat_wrap (ast.not_, 0, ast.not_.op in {"=", ",", "-slice", "-piece", "-lamb", "-or", "-and"})}',
		'-ufunc': lambda self, ast: f'?{ast.ufunc}({", ".join (ast.vars + tuple (f"{k} = {self._ast2nat_wrap (a, 0, a.is_comma)}" for k, a in ast.kw))})',

		'text'  : lambda self, ast: ast.nat,
	}

#...............................................................................................
class ast2py: # abstract syntax tree -> Python code text
	def __init__ (self): self.parent = self.ast = None # pylint droppings
	def __new__ (cls, ast, xlat = True, ass2eq = True):
		self         = super ().__new__ (cls)
		self.ass2eq  = ass2eq
		self.parents = [None]
		self.parent  = self.ast = AST ()

		if xlat:
			ast = sxlat.xlat_funcs2asts (ast, sxlat.XLAT_FUNC2AST_PY)

		if _PYS:
			ast = sxlat.xlat_pyS (ast)

		return self._ast2py (ast)

	def _ast2py (self, ast):
		self.parents.append (self.ast)

		self.parent = self.ast
		self.ast    = ast

		py          = self._ast2py_funcs [ast.op] (self, ast)

		del self.parents [-1]

		self.ast    = self.parent
		self.parent = self.parents [-1]

		return py

	def _ast2py_curly (self, ast):
		return \
				self._ast2py_paren (ast) \
				if ast.strip_minus.op in {'<>', ',', '+', '*', '/'} or (ast.is_log and ast.base is not None) else \
				self._ast2py (ast)

	def _ast2py_paren (self, ast, paren = _None):
		if paren is _None:
			return self._ast2py (ast) if ast.is_paren else f'({self._ast2py (ast)})'

		if ((ast.op in paren) if isinstance (paren, set) else paren):
			return f'({self._ast2py (ast)})'

		return self._ast2py (ast)

	def _ast2py_ass (self, ast):
		if not self.parent or self.parent.is_func: # present assignment with = instead of Eq for keyword argument or at top level?
			return f'{self._ast2py_paren (ast.lhs) if ast.lhs.is_lamb else self._ast2py (ast.lhs)} = {self._ast2py (ast.rhs)}'

		return f'Eq({self._ast2py_paren (ast.lhs, bool (ast.lhs.is_comma))}, {self._ast2py_paren (ast.rhs, bool (ast.rhs.is_comma))})'

	_ast2py_cmpfuncs = {'==': 'Eq', '!=': 'Ne', '<': 'Lt', '<=': 'Le', '>': 'Gt', '>=': 'Ge'}

	def _ast2py_cmp (self, ast):
		def cmppy (lhs, rel, rhs):
			if rel in {'in', 'notin'}:
				return f'{self._ast2py_paren (lhs, lhs.op in {"<>", "-lamb"})} {AST.Cmp.PYFMT.get (rel, rel)} {self._ast2py_paren (rhs, rhs.op in {"<>", "-lamb"})}'
			else:
				return f'{self._ast2py_cmpfuncs [rel]}({self._ast2py_paren (lhs, bool (lhs.is_comma))}, {self._ast2py_paren (rhs, bool (rhs.is_comma))})'

		if ast.cmp.len == 1:
			return cmppy (ast.lhs, *ast.cmp [0])
		else:
			return f'And({cmppy (ast.lhs, *ast.cmp [0])}, {", ".join (cmppy (ast.cmp [i - 1] [1], *ast.cmp [i]) for i in range (1, ast.cmp.len))})'

	def _ast2py_attr (self, ast):
		obj = self._ast2py_paren (ast.obj, {"=", "<>", "#", ",", "-", "+", "*", "/"})

		if ast.is_attr_func:
			args, kw = AST.args2kwargs (ast.args, self._ast2py, ass2eq = self.ass2eq)

			return f'{obj}.{ast.attr}({", ".join (args + [f"{k} = {a}" for k, a in kw.items ()])})'

		return f'{obj}.{ast.attr}'

	def _ast2py_div (self, ast):
		n = self._ast2py_curly (ast.numer)
		d = self._ast2py_curly (ast.denom)

		return f'{n}{" / " if ast.numer.strip_minus.op not in {"#", "@"} or ast.denom.strip_minus.op not in {"#", "@"} else "/"}{d}'

	def _ast2py_pow (self, ast):
		b = self._ast2py_paren (ast.base) if _ast_is_neg (ast.base) else self._ast2py_curly (ast.base)
		e = self._ast2py_curly (ast.exp)

		return f'{b}**{e}'

	def _ast2py_log (self, ast):
		if ast.base is None:
			return f'ln{self._ast2py_paren (ast.log)}'
		else:
			return f'log{self._ast2py_paren (ast.log)} / log{self._ast2py_paren (ast.base)}'

	def _ast2py_func (self, ast):
		args, kw = AST.args2kwargs (ast.args, self._ast2py, ass2eq = self.ass2eq)

		return f'{ast.unescaped}({", ".join (args + [f"{k} = {a}" for k, a in kw.items ()])})'

	def _ast2py_lim (self, ast):
		return \
				f'''Limit({self._ast2py (ast.lim)}, {self._ast2py (ast.lvar)}, {self._ast2py (ast.to)}''' \
				f'''{", dir='+-'" if ast.dir is None else ", dir='-'" if ast.dir == '-' else ""})'''

	def _ast2py_diff (self, ast):
		args = sum ((
				(self._ast2py (n.as_var),)
				if n.is_var else
				(self._ast2py (n.base.as_var), str (n.exp.as_int))
				for n in ast.dvs), ())

		return f'Derivative({self._ast2py (ast.diff._strip_paren (keeptuple = True))}, {", ".join (args)})'

	def _ast2py_intg (self, ast):
		if ast.intg is not None and ast.intg.is_intg:
			intg = self._ast2py_intg (ast.intg)
		else:
			intg = f'Integral({1 if ast.intg is None else self._ast2py (ast.intg)})'

		if ast.from_ is None:
			intg = intg [:-1] + f', {self._ast2py (ast.dv.as_var)})'
		else:
			intg = intg [:-1] + f', ({self._ast2py (ast.dv.as_var)}, {self._ast2py (ast.from_)}, {self._ast2py (ast.to)}))'

		return intg

	def _ast2py_mat (self, ast):
		if not ast.rows:
			return 'Matrix()'
		elif ast.is_mat_column and not any (r [0].is_brack for r in ast.mat): # (ast.rows > 1 or not ast.mat [0] [0].is_brack):
			return f"Matrix([{', '.join (self._ast2py (row [0]) for row in ast.mat)}])"
		else:
			return f"""Matrix([{', '.join (f'[{", ".join (self._ast2py (e) for e in row)}]' for row in ast.mat)}])"""

	def _ast2py_slice (self, ast):
		if self.parent.is_idx and ast in self.parent.idx or \
				self.parent.is_comma and len (self.parents) > 1 and self.parents [-2].is_idx and ast in self.parents [-2].idx:
			return ':'.join (self._ast2py_paren (a, a.op in {'=', ',', '-slice'}) for a in _ast_slice_bounds (ast))

		return f'slice({", ".join (self._ast2py_paren (a, a.op in {"=", ",", "-slice"}) for a in _ast_slice_bounds (ast, AST.None_))})'

	def _ast2py_sdiff (self, ast):
		sdiff = self._ast2py (ast.sdiff [0])

		for a in ast.sdiff [1:]:
			a     = self._ast2py (a)
			sdiff = f'Union(Complement({sdiff}, {a}), Complement({a}, {sdiff}))'

		return sdiff

	_ast2py_funcs = {
		';'     : lambda self, ast: '; '.join (self._ast2py (a) for a in ast.scolon),
		'='     : _ast2py_ass,
		'<>'    : _ast2py_cmp,
		'#'     : lambda self, ast: ast.num,
		'@'     : lambda self, ast: ast.var,
		'.'     : _ast2py_attr,
		'"'     : lambda self, ast: repr (ast.str_),
		','     : lambda self, ast: f'{", ".join (self._ast2py (parm) for parm in ast.comma)}{_trail_comma (ast.comma)}',
		'('     : lambda self, ast: f'({self._ast2py (ast.paren)})',
		'['     : lambda self, ast: f'[{", ".join (self._ast2py (b) for b in ast.brack)}]',
		'|'     : lambda self, ast: f'abs({self._ast2py (ast.abs)})',
		'-'     : lambda self, ast: f'-{self._ast2py_paren (ast.minus, ast.minus.op in {"+"})}',
		'!'     : lambda self, ast: f'factorial({self._ast2py (ast.fact)})',
		'+'     : lambda self, ast: ' + '.join (self._ast2py_paren (n, n.is_cmp_in or (n.is_num_neg and n is not ast.add [0])) for n in ast.add).replace (' + -', ' - '),
		'*'     : lambda self, ast: '*'.join (self._ast2py_paren (n, n.is_cmp_in or n.is_add) for n in ast.mul),
		'/'     : _ast2py_div,
		'^'     : _ast2py_pow,
		'-log'  : _ast2py_log,
		'-sqrt' : lambda self, ast: f'sqrt{self._ast2py_paren (ast.rad)}' if ast.idx is None else self._ast2py (AST ('^', ast.rad._strip_paren (1), ('/', AST.One, ast.idx))),
		'-func' : _ast2py_func,
		'-lim'  : _ast2py_lim,
		'-sum'  : lambda self, ast: f'Sum({self._ast2py (ast.sum)}, ({self._ast2py (ast.svar)}, {self._ast2py (ast.from_)}, {self._ast2py (ast.to)}))',
		'-diff' : _ast2py_diff,
		'-difp' : lambda self, ast: f'{"diff(" * ast.count}{self._ast2py (ast.diffp)}{")" * ast.count}',
		'-int'  : _ast2py_intg,
		'-mat'  : _ast2py_mat,
		'-piece': lambda self, ast: 'Piecewise(' + ', '.join (f'({self._ast2py (p [0])}, {True if p [1] is True else self._ast2py (p [1])})' for p in ast.piece) + ')',
		'-lamb' : lambda self, ast: f"""Lambda({ast.vars [0] if ast.vars.len == 1 else f'({", ".join (ast.vars)})'}, {self._ast2py (ast.lamb)})""",
		'-idx'  : lambda self, ast: f'{self._ast2py_paren (ast.obj) if ast.obj.is_num_neg or ast.obj.op in {"=", "<>", ",", "+", "*", "/", "^", "-", "-lim", "-sum", "-diff", "-int", "-piece"} else self._ast2py (ast.obj)}[{self._ast2py (AST.tuple2ast (ast.idx))}]',
		'-slice': _ast2py_slice,
		'-set'  : lambda self, ast: f'FiniteSet({", ".join (self._ast2py (c) for c in ast.set)})',
		'-dict' : lambda self, ast: f'{{{", ".join (f"{self._ast2py (k)}: {self._ast2py (v)}" for k, v in ast.dict)}}}',
		'||'    : lambda self, ast: f'Union({", ".join (self._ast2py (a) for a in ast.union)})',
		'^^'    : _ast2py_sdiff,
		'&&'    : lambda self, ast: f'Intersection({", ".join (self._ast2py (a) for a in ast.xsect)})',
		'-or'   : lambda self, ast: f'Or({", ".join (self._ast2py_paren (a, a.is_comma) for a in ast.or_)})',
		'-and'  : lambda self, ast: f'And({", ".join (self._ast2py_paren (a, a.is_comma) for a in ast.and_)})',
		'-not'  : lambda self, ast: f'Not({self._ast2py_paren (ast.not_, ast.not_.is_ass or ast.not_.is_comma)})',
		'-ufunc': lambda self, ast: f'Function({", ".join ((f"{ast.ufunc!r}",) + tuple (f"{k} = {self._ast2py_paren (a, a.is_comma)}" for k, a in ast.kw))})({", ".join (ast.vars)})',

		'text'  : lambda self, ast: ast.py,
	}

#...............................................................................................
# Potentially bad __builtins__: eval, exec, globals, locals, vars, setattr, delattr, exit, help, input, license, open, quit, __import__
_builtins_dict         = __builtins__ if isinstance (__builtins__, dict) else __builtins__.__dict__
_builtins_names        = ['abs', 'all', 'any', 'ascii', 'bin', 'callable', 'chr', 'dir', 'divmod', 'format', 'getattr', 'hasattr', 'hash', 'hex', 'id',
	'isinstance', 'issubclass', 'iter', 'len', 'max', 'min', 'next', 'oct', 'ord', 'pow', 'print', 'repr', 'round', 'sorted', 'sum', 'bool',
	'bytearray', 'bytes', 'complex', '-dict', 'enumerate', 'filter', 'float', 'frozenset', 'property', 'int', 'list', 'map', 'object', 'range',
	'reversed', 'set', 'slice', 'str', 'tuple', 'type', 'zip']

_ast2spt_func_builtins = dict (no for no in filter (lambda no: no [1], ((n, _builtins_dict.get (n)) for n in _builtins_names)))
_ast2spt_pyfuncs       = {**_ast2spt_func_builtins, **sp.__dict__, **{'simplify': _simplify}}

class ast2spt: # abstract syntax tree -> sympy tree (expression)
	def __init__ (self): self.vars = self.eval = [] # pylint kibble
	def __new__ (cls, ast, vars = {}, xlat = True):
		self      = super ().__new__ (cls)
		self.vars = [vars]
		self.eval = True

		if xlat:
			ast = sxlat.xlat_funcs2asts (ast, sxlat.XLAT_FUNC2AST_PY)

		spt = self._ast2spt (ast)

		if _POST_SIMPLIFY:
			spt = _simplify (spt)

		return spt

	def _ast2spt (self, ast):
		spt = self._ast2spt_funcs [ast.op] (self, ast)

		if _DOIT and self.eval:
			try:
				spt = spt.doit (deep = False)
			except:
				pass

		return spt

	def _ast2spt_ass (self, ast):
		lhs, rhs = self._ast2spt (ast.lhs), self._ast2spt (ast.rhs)

		try:
			return ExprAss (lhs, rhs) # try to use SymPy comparison object
		except:
			return lhs == rhs # fall back to Python comparison

	_ast2spt_cmpfuncs = {
		'=='   : (sp.Eq, lambda a, b: a == b),
		'!='   : (sp.Ne, lambda a, b: a != b),
		'<'    : (sp.Lt, lambda a, b: a < b),
		'<='   : (sp.Le, lambda a, b: a <= b),
		'>'    : (sp.Gt, lambda a, b: a > b),
		'>='   : (sp.Ge, lambda a, b: a >= b),
		'in'   : (sp.Contains, lambda a, b: a in b),
		'notin': (lambda a, b: sp.Not (sp.Contains (a, b)), lambda a, b: a not in b),
	}

	def _ast2spt_cmp (self, ast):
		def cmpspt (lhs, rel, rhs):
			fspt, fpy = self._ast2spt_cmpfuncs [rel]

			try:
				return fspt (lhs, rhs) # try to use SymPy comparison object
			except:
				return fpy (lhs, rhs) # fall back to Python comparison

		hss = [self._ast2spt (ast.lhs)] + [self._ast2spt (cmp [1]) for cmp in ast.cmp]

		if ast.cmp.len == 1:
			return cmpspt (hss [0], ast.cmp [0] [0], hss [1])
		else:
			return sp.And (*(_sympify (cmpspt (hss [i], ast.cmp [i] [0], hss [i + 1])) for i in range (ast.cmp.len)))

	_ast2spt_consts = { # 'e' and 'i' dynamically set on use from AST.E or AST.I
		'pi'   : sp.pi,
		'oo'   : sp.oo,
		'zoo'  : sp.zoo,
		'None' : None,
		'True' : True,
		'False': False,
		'nan'  : sp.nan,
	}

	def _ast2spt_var (self, ast):
		spt = {**self._ast2spt_consts, AST.E.var: sp.E, AST.I.var: sp.I}.get (ast.var, _None)

		if spt is _None:
			if len (ast.var) > 1 and ast.var not in AST.Var.GREEK:
				spt = getattr (sp, ast.var, _None)

			if spt is _None:
				spt = sp.Symbol (ast.var)

		return spt

	def _ast2spt_attr (self, ast):
		obj = ast.obj
		spt = None

		while obj.is_func and obj.args and (obj.func == AST.Func.NOEVAL or obj.func == AST.Func.NOREMAP):
			obj = obj.args [0]

		if obj.is_var and obj.var not in self.vars: # always support S.Half and the like unless base object redefined by assignment
			spt = getattr (sp, obj.var, None)

		if spt is None:
			spt = self._ast2spt (ast.obj)

		try:
			attr = getattr (spt, ast.attr)

			return attr if ast.is_attr_var else _ast_func_call (attr, ast.args, self._ast2spt)

		except AttributeError: # unresolved attributes of expressions with free vars remaining should not raise
			if not obj.free_vars:
				raise

		return ExprNoEval (str (AST ('.', spt2ast (spt), *ast [2:])), 1)

	def _ast2spt_add (self, ast): # specifically try to subtract negated objects (because of sets)
		itr = iter (ast.add)
		res = self._ast2spt (next (itr))

		for arg in itr:
			arg, neg    = arg._strip_minus (retneg = True)
			arg, is_neg = self._ast2spt (arg), neg.is_neg

			try:
				res = res - arg if is_neg else res + arg
			except:
				res = sp.sympify (res) - sp.sympify (arg) if is_neg else sp.sympify (res) + sp.sympify (arg)

		return res

	def _ast2spt_func (self, ast):
		if ast.func == AST.Func.NOREMAP: # special reference meta-function
			return self._ast2spt (ast.args [0])

		if ast.func == AST.Func.NOEVAL: # special no-evaluate meta-function
			return ExprNoEval (str (ast.args [0]), 1 if ast.args.len == 1 else self._ast2spt (ast.args [1]))

		func = _ast2spt_pyfuncs.get (ast.unescaped)

		if func is not None:
			return _ast_func_call (func, ast.args, self._ast2spt, is_escaped = ast.is_escaped)

		if ast.unescaped in _USER_FUNCS: # user lambda, within other lambda if it got here
			return ExprNoEval (str (ast), 1)

		raise NameError (f'function {ast.unescaped!r} is not defined')

	def _ast2spt_diff (self, ast):
		args = sum (( \
				(self._ast2spt (n.as_var),) \
				if n.is_var else \
				(self._ast2spt (n.base.as_var), sp.Integer (n.exp.as_int)) \
				for n in ast.dvs \
				), ())

		return sp.Derivative (self._ast2spt (ast [1]), *args)

	def _ast2spt_diffp (self, ast):
		spt = self._ast2spt (ast.diffp)

		for _ in range (ast.count):
			spt = sp.Derivative (spt)

		return spt

			# raise ValueError ('multiple possible variables of differentiation for prime')

	def _ast2spt_intg (self, ast):
		if ast.from_ is None:
			if ast.intg is None:
				return sp.Integral (1, sp.Symbol (ast.dv.as_var.var))
			else:
				return sp.Integral (self._ast2spt (ast.intg), sp.Symbol (ast.dv.as_var.var))

		else:
			if ast.intg is None:
				return sp.Integral (1, (sp.Symbol (ast.dv.as_var.var), self._ast2spt (ast.from_), self._ast2spt (ast.to)))
			else:
				return sp.Integral (self._ast2spt (ast [1]), (sp.Symbol (ast.dv.as_var.var), self._ast2spt (ast.from_), self._ast2spt (ast.to)))

	def _ast2spt_lamb (self, ast):
		oldeval   = self.eval
		self.eval = False
		spt       = sp.Lambda (tuple (sp.Symbol (v) for v in ast.vars), self._ast2spt (ast.lamb))
		self.eval = oldeval

		return spt

	def _ast2spt_idx (self, ast):
		spt = self._ast2spt (ast.obj)
		idx = self._ast2spt (ast.idx [0]) if len (ast.idx) == 1 else tuple (self._ast2spt (i) for i in ast.idx)

		try:
			return spt [idx]
		except TypeError: # invalid indexing of expressions with free vars remaining should not raise
			if not getattr (spt, 'free_symbols', None) and not hasattr (spt, '__getitem__') and not isinstance (spt, ExprNoEval): # ast.free_vars:
				raise

		return ExprNoEval (str (AST ('-idx', spt2ast (spt), ast.idx)), 1)

	def _ast2spt_sdiff (self, ast):
		sdiff = self._ast2spt (ast.sdiff [0])

		for a in ast.sdiff [1:]:
			a     = self._ast2spt (a)
			sdiff = sp.Union (sp.Complement (sdiff, a), sp.Complement (a, sdiff))

		return sdiff

	_ast2spt_funcs = {
		';'     : lambda self, ast: _raise (RuntimeError ('semicolon expression should never get here')),
		'='     : _ast2spt_ass,
		'<>'    : _ast2spt_cmp,
		'#'     : lambda self, ast: sp.Integer (ast.num) if ast.is_num_int else sp.Float (ast.num, _SYMPY_FLOAT_PRECISION),
		'@'     : _ast2spt_var,
		'.'     : _ast2spt_attr,
		'"'     : lambda self, ast: ast.str_,
		','     : lambda self, ast: tuple (self._ast2spt (p) for p in ast.comma),
		'('     : lambda self, ast: self._ast2spt (ast.paren),
		'['     : lambda self, ast: [self._ast2spt (b) for b in ast.brack],
		'|'     : lambda self, ast: sp.Abs (self._ast2spt (ast.abs)),
		'-'     : lambda self, ast: -self._ast2spt (ast.minus),
		'!'     : lambda self, ast: sp.factorial (self._ast2spt (ast.fact)),
		'+'     : _ast2spt_add,
		'*'     : lambda self, ast: _Mul (*(self._ast2spt (n) for n in ast.mul)),
		'/'     : lambda self, ast: _Mul (self._ast2spt (ast.numer), _Pow (self._ast2spt (ast.denom), -1)),
		'^'     : lambda self, ast: _Pow (self._ast2spt (ast.base), self._ast2spt (ast.exp)),
		'-log'  : lambda self, ast: sp.log (self._ast2spt (ast.log)) if ast.base is None else sp.log (self._ast2spt (ast.log), self._ast2spt (ast.base)),
		'-sqrt' : lambda self, ast: _Pow (self._ast2spt (ast.rad), _Pow (sp.S (2), -1)) if ast.idx is None else _Pow (self._ast2spt (ast.rad), _Pow (self._ast2spt (ast.idx), -1)),
		'-func' : _ast2spt_func,
		'-lim'  : lambda self, ast: (sp.Limit if ast.dir else sp.limit) (self._ast2spt (ast.lim), self._ast2spt (ast.lvar), self._ast2spt (ast.to), dir = ast.dir or '+-'),
		'-sum'  : lambda self, ast: sp.Sum (self._ast2spt (ast.sum), (self._ast2spt (ast.svar), self._ast2spt (ast.from_), self._ast2spt (ast.to))),
		'-diff' : _ast2spt_diff,
		'-difp' : _ast2spt_diffp,
		'-int'  : _ast2spt_intg,
		'-mat'  : lambda self, ast: sp.Matrix ([[self._ast2spt (e) for e in row] for row in ast.mat]),
		'-piece': lambda self, ast: sp.Piecewise (*((self._ast2spt (p [0]), True if p [1] is True else self._ast2spt (p [1])) for p in ast.piece)),
		'-lamb' : _ast2spt_lamb,
		'-idx'  : _ast2spt_idx,
		'-slice': lambda self, ast: slice (*(self._ast2spt (a) if a else a for a in _ast_slice_bounds (ast, None))),
		'-set'  : lambda self, ast: sp.FiniteSet (*(self._ast2spt (a) for a in ast.set)),
		'-dict' : lambda self, ast: dict ((self._ast2spt (k), self._ast2spt (v)) for k, v in ast.dict),
		'||'    : lambda self, ast: sp.Union (*(self._ast2spt (a) for a in ast.union)),
		'^^'    : _ast2spt_sdiff,
		'&&'    : lambda self, ast: sp.Intersection (*(self._ast2spt (a) for a in ast.xsect)),
		'-or'   : lambda self, ast: sp.Or (*(_sympify (self._ast2spt (a), sp.Or, bool) for a in ast.or_)),
		'-and'  : lambda self, ast: sp.And (*(_sympify (self._ast2spt (a), sp.And, bool) for a in ast.and_)),
		'-not'  : lambda self, ast: _sympify (self._ast2spt (ast.not_), sp.Not, lambda x: not x),
		'-ufunc': lambda self, ast: sp.Function (ast.ufunc, **{k: self._ast2spt (a) for k, a in ast.kw}) (*(sp.Symbol (v) for v in ast.vars)),

		'text'  : lambda self, ast: ast.spt,
	}

#...............................................................................................
class spt2ast:
	def __init__ (self): self.parent = self.spt = None # pylint droppings
	def __new__ (cls, spt):
		self         = super ().__new__ (cls)
		self.parents = [None]
		self.parent  = self.spt = AST ()

		return self._spt2ast (spt)

	def _spt2ast (self, spt): # sympy tree (expression) -> abstract syntax tree
		def __spt2ast (spt):
			for cls in spt.__class__.__mro__:
				func = spt2ast._spt2ast_funcs.get (cls)

				if func:
					return func (self, spt)

			tex = sp.latex (spt)

			if tex == str (spt): # no native latex representation?
				tex = tex.replace ('_', '\\_')

			if tex [0] == '<' and tex [-1] == '>': # for Python repr style of objects <class something> TODO: Move this to Javascript.
				tex = '\\text{' + tex.replace ("<", "&lt;").replace (">", "&gt;").replace ("\n", "") + '}'

			return AST ('text', tex, str (spt), str (spt), spt)

		self.parents.append (self.spt)

		self.parent = self.spt
		self.spt    = spt

		spt         = __spt2ast (spt)

		del self.parents [-1]

		self.spt    = self.parent
		self.parent = self.parents [-1]

		return spt

	def _spt2ast_num (self, spt):
		num = AST ('#', str (spt))

		if num.grp [5]:
			return AST ('#', ''.join (num.grp [:6] + num.grp [7:]))

		e = len (num.grp [2]) + num.num_exp_val

		return AST ('#', \
				f'{num.grp [0]}{num.grp [1]}e+{e}'     if e >= 16 else \
				f'{num.grp [0]}{num.grp [1]}{"0" * e}' if e >= 0 else \
				f'{num.grp [0]}{num.grp [1]}e{e}')

	def _spt2ast_Union (self, spt): # convert union of complements to symmetric difference if present
		if len (spt.args) == 2 and spt.args [0].is_Complement and spt.args [1].is_Complement and \
				spt.args [0].args [0] == spt.args [1].args [1] and spt.args [0].args [1] == spt.args [1].args [0]:
			return AST ('^^', (self._spt2ast (spt.args [0].args [0]), self._spt2ast (spt.args [0].args [1])))

		return self._spt2ast (spt.args [0]) if len (spt.args) == 1 else AST ('||', tuple (self._spt2ast (a) for a in spt.args))

	def _spt2ast_MatrixBase (self, spt):
		if not spt.rows or not spt.cols:
			return AST.MatEmpty
		if spt.cols > 1:
			return AST ('-mat', tuple (tuple (self._spt2ast (e) for e in spt [row, :]) for row in range (spt.rows)))
		else:
			return AST ('-mat', tuple ((self._spt2ast (e),) for e in spt))

	def _spt2ast_Add (self, spt):
		args = spt.args

		for arg in args:
			if isinstance (arg, sp.Order):
				break
		else:
			if args [0].is_number:
				args = spt.args [1:] + (spt.args [0],)

		terms = []

		for arg in args:
			ast = self._spt2ast (arg)

			if ast.is_num_neg:
				ast = AST ('-', ast.neg ())
			elif ast.is_mul and _ast_is_neg (ast.mul [0]):
				ast = AST ('-', ('*', (ast.mul [0].neg (),) + ast.mul [1:]))

			terms.append (ast)

		return AST ('+', tuple (terms))

	def _spt2ast_Mul (self, spt):
		if spt.args [0] == -1:
			return AST ('-', self._spt2ast (sp.Mul (*spt.args [1:])))

		if spt.args [0].is_negative and isinstance (spt, sp.Number):
			return AST ('-', self._spt2ast (sp.Mul (-spt.args [0], *spt.args [1:])))

		args = spt.args [1:] if spt.args [0] == 1 else spt.args # sometimes we get Mul (1, ...), strip the 1

		if len (spt.args) == 1:
			return self._spt2ast (args [0])

		numer = []
		denom = []

		for arg in args:
			if isinstance (arg, sp.Pow) and arg.args [1].is_negative:
				denom.append (self._spt2ast (arg.args [0] if arg.args [1] is sp.S.NegativeOne else _Pow (arg.args [0], -arg.args [1])))
			else:
				numer.append (self._spt2ast (arg))

		if not denom:
			return AST ('*', tuple (numer)) if len (numer) > 1 else numer [0]

		if not numer:
			return AST ('/', AST.One, AST ('*', tuple (denom)) if len (denom) > 1 else denom [0])

		return AST ('/', AST ('*', tuple (numer)) if len (numer) > 1 else numer [0], \
				AST ('*', tuple (denom)) if len (denom) > 1 else denom [0])

	def _spt2ast_Pow (self, spt):
		if spt.args [1].is_negative:
			return AST ('/', AST.One, self._spt2ast (spt.args [0] if spt.args [1] is sp.S.NegativeOne else _Pow (spt.args [0], -spt.args [1])))

		if spt.args [1] == 0.5:
			return AST ('-sqrt', self._spt2ast (spt.args [0]))

		return AST ('^', self._spt2ast (spt.args [0]), self._spt2ast (spt.args [1]))

	def _spt2ast_MatPow (self, spt):
		try: # compensate for some MatPow.doit() != mat**pow
			return self._spt2ast (spt.args [0]**spt.args [1])
		except:
			return AST ('^', self._spt2ast (spt.args [0]), self._spt2ast (spt.args [1]))

	def _spt2ast_Derivative (self, spt):
		if len (spt.args) == 2:
			syms = spt.free_symbols

			if len (syms) == 1 and spt.args [1] [0] == syms.pop ():
				return AST ('-difp', self._spt2ast (spt.args [0]), int (spt.args [1] [1]))

		return AST ('-diff', self._spt2ast (spt.args [0]), tuple (
			('@', f'd{s.name}') if p == 1 else ('^', ('@', f'd{s.name}'), ('#', str (p)))
			for s, p in spt.args [1:]))

	def _spt2ast_Integral (self, spt):
		return \
				AST ('-int', self._spt2ast (spt.args [0]), AST ('@', f'd{self._spt2ast (spt.args [1] [0]) [1]}'), self._spt2ast (spt.args [1] [1]), self._spt2ast (spt.args [1] [2])) \
				if len (spt.args [1]) == 3 else \
				AST ('-int', self._spt2ast (spt.args [0]), AST ('@', f'd{self._spt2ast (spt.args [1] [0]) [1]}'))

	def _spt2ast_Function (self, spt, name = None, args = None, kw = None):
		if name is None:
			name = spt.__class__.__name__

		if getattr (spt, 'SYMPAD_ESCAPED', None):
			name = f'{AST.Func.ESCAPE}{name}'

		if args is None:
			args = spt.args

		if kw:
			return AST ('-func', name, tuple (self._spt2ast (arg) for arg in spt.args) + tuple (AST ('=', ('@', kw), a) for kw, a in kw))
		else:
			return AST ('-func', name, tuple (self._spt2ast (arg) for arg in spt.args))

	def _spt2ast_AppliedUndef (self, spt):
		if spt.__class__.__name__ == 'slice': # special cased converted slice object with start, stop and step present, this is REALLY unnecessary...
			return AST ('-slice', *tuple (self._spt2ast (s) for s in spt.args))

		return AST ('-ufunc', spt.name, tuple (a.name for a in spt.args), tuple (sorted ((k, self._spt2ast (a)) for k, a in spt._extra_kwargs.items ()))) # i._explicit_class_assumptions.items ()))

	_dict_keys   = {}.keys ().__class__
	_dict_values = {}.values ().__class__
	_dict_items  = {}.items ().__class__

	_spt2ast_Limit_dirs = {'+': ('+',), '-': ('-',), '+-': ()}

	_spt2ast_funcs = {
		ExprNoEval: lambda self, spt: spt.SYMPAD_eval (),

		None.__class__: lambda self, spt: AST.None_,
		bool: lambda self, spt: AST.True_ if spt else AST.False_,
		int: lambda self, spt: AST ('#', str (spt)),
		float: lambda self, spt: AST ('#', str (_fltoint (spt))),
		complex: lambda self, spt: AST ('#', str (_fltoint (spt.real))) if not spt.imag else AST ('+', (('#', str (_fltoint (spt.real))), AST.I if spt.imag == 1 else ('*', (('#', str (_fltoint (spt.imag))), AST.I)))),
		str: lambda self, spt: AST ('"', spt),
		tuple: lambda self, spt: AST ('(', (',', tuple (self._spt2ast (e) for e in spt))),
		list: lambda self, spt: AST ('[', tuple (self._spt2ast (e) for e in spt)),
		set: lambda self, spt: AST ('-set', tuple (self._spt2ast (e) for e in spt)),
		frozenset: lambda self, spt: AST ('-set', tuple (self._spt2ast (e) for e in spt)),
		dict: lambda self, spt: AST ('-dict', tuple ((self._spt2ast (k), self._spt2ast (v)) for k, v in spt.items ())),
		slice: lambda self, spt: AST ('-slice', False if spt.start is None else self._spt2ast (spt.start), False if spt.stop is None else self._spt2ast (spt.stop), None if spt.step is None else self._spt2ast (spt.step)),
		_dict_keys: lambda self, spt: AST ('[', tuple (self._spt2ast (e) for e in spt)),
		_dict_values: lambda self, spt: AST ('[', tuple (self._spt2ast (e) for e in spt)),
		_dict_items: lambda self, spt: AST ('[', tuple (self._spt2ast (e) for e in spt)),
		sp.Tuple: lambda self, spt: self._spt2ast (spt.args),

		sp.Integer: _spt2ast_num,
		sp.Float: _spt2ast_num,
		sp.Rational: lambda self, spt: AST ('/', ('#', str (spt.p)), ('#', str (spt.q))) if spt.p >= 0 else AST ('-', ('/', ('#', str (-spt.p)), ('#', str (spt.q)))),
		sp.numbers.ImaginaryUnit: lambda self, spt: AST.I,
		sp.numbers.Pi: lambda self, spt: AST.Pi,
		sp.numbers.Exp1: lambda self, spt: AST.E,
		sp.numbers.Infinity: lambda self, spt: AST.Infty,
		sp.numbers.NegativeInfinity: lambda self, spt: AST ('-', AST.Infty),
		sp.numbers.ComplexInfinity: lambda self, spt: AST.CInfty,
		sp.numbers.NaN: lambda self, spt: AST.NaN,

		sp.Symbol: lambda self, spt: AST ('@', spt.name),

		sp.boolalg.BooleanTrue: lambda self, spt: AST.True_,
		sp.boolalg.BooleanFalse: lambda self, spt: AST.False_,
		sp.Or: lambda self, spt: AST ('-or', tuple (self._spt2ast (a) for a in spt.args)),
		sp.And: lambda self, spt: sxlat._xlat_f2a_And (*tuple (self._spt2ast (a) for a in spt.args), canon = True), # collapse possibly previously segmented extended comparison
		sp.Not: lambda self, spt: AST ('-not', self._spt2ast (spt.args [0])),

		ExprAss: lambda self, spt: AST ('=', self._spt2ast (spt.args [0]), self._spt2ast (spt.args [1])),
		sp.Eq: lambda self, spt: AST ('<>', self._spt2ast (spt.args [0]), (('==', self._spt2ast (spt.args [1])),)),
		sp.Ne: lambda self, spt: AST ('<>', self._spt2ast (spt.args [0]), (('!=', self._spt2ast (spt.args [1])),)),
		sp.Lt: lambda self, spt: AST ('<>', self._spt2ast (spt.args [0]), (('<',  self._spt2ast (spt.args [1])),)),
		sp.Le: lambda self, spt: AST ('<>', self._spt2ast (spt.args [0]), (('<=', self._spt2ast (spt.args [1])),)),
		sp.Gt: lambda self, spt: AST ('<>', self._spt2ast (spt.args [0]), (('>',  self._spt2ast (spt.args [1])),)),
		sp.Ge: lambda self, spt: AST ('<>', self._spt2ast (spt.args [0]), (('>=', self._spt2ast (spt.args [1])),)),

		sp.EmptySet: lambda self, spt: AST.SetEmpty,
		sp.fancysets.Complexes: lambda self, spt: AST.Complexes,
		sp.FiniteSet: lambda self, spt: AST ('-set', tuple (self._spt2ast (arg) for arg in spt.args)),
		sp.Union: _spt2ast_Union,
		sp.Intersection: lambda self, spt: self._spt2ast (spt.args [0]) if len (spt.args) == 1 else AST.flatcat ('&&', self._spt2ast (spt.args [0]), self._spt2ast (spt.args [1])),
		sp.Complement: lambda self, spt: AST ('+', (self._spt2ast (spt.args [0]), ('-', self._spt2ast (spt.args [1])))),

		sp.matrices.MatrixBase: _spt2ast_MatrixBase,

		sp.Poly: lambda self, spt: self._spt2ast_Function (spt, args = spt.args + spt.gens, kw = (('domain', AST ('"', str (spt.domain))),)),

		sp.Add: _spt2ast_Add,
		sp.Mul: _spt2ast_Mul,
		sp.Pow: _spt2ast_Pow,
		sp.MatPow: _spt2ast_MatPow,

		sp.Abs: lambda self, spt: AST ('|', self._spt2ast (spt.args [0])),
		sp.arg: lambda self, spt: AST ('-func', 'arg', (self._spt2ast (spt.args [0]),)),
		sp.exp: lambda self, spt: AST ('^', AST.E, self._spt2ast (spt.args [0])),
		sp.factorial: lambda self, spt: AST ('!', self._spt2ast (spt.args [0])),
		sp.functions.elementary.trigonometric.TrigonometricFunction: _spt2ast_Function,
		sp.functions.elementary.hyperbolic.HyperbolicFunction: _spt2ast_Function,
		sp.functions.elementary.trigonometric.InverseTrigonometricFunction: _spt2ast_Function,
		sp.functions.elementary.hyperbolic.InverseHyperbolicFunction: _spt2ast_Function,
		sp.log: lambda self, spt: AST ('-log', self._spt2ast (spt.args [0])) if len (spt.args) == 1 else AST ('-log', self._spt2ast (spt.args [0]), self._spt2ast (spt.args [1])),
		sp.Min: lambda self, spt: AST ('-func', 'Min', tuple (self._spt2ast (arg) for arg in spt.args)),
		sp.Max: lambda self, spt: AST ('-func', 'Max', tuple (self._spt2ast (arg) for arg in spt.args)),

		sp.Limit: lambda self, spt: AST (*(('-lim', self._spt2ast (spt.args [0]), self._spt2ast (spt.args [1]), self._spt2ast (spt.args [2])) + spt2ast._spt2ast_Limit_dirs [spt.args [3].name])),
		sp.Sum: lambda self, spt: AST ('-sum', self._spt2ast (spt.args [0]), self._spt2ast (spt.args [1] [0]), self._spt2ast (spt.args [1] [1]), self._spt2ast (spt.args [1] [2])),
		sp.Derivative: _spt2ast_Derivative,
		sp.Integral: _spt2ast_Integral,

		sp.Lambda: lambda self, spt: AST ('-lamb', self._spt2ast (spt.args [1]), tuple (v.name for v in spt.args [0])),
		sp.Order: lambda self, spt: AST ('-func', 'O', ((self._spt2ast (spt.args [0]) if spt.args [1] [1] == 0 else self._spt2ast (spt.args)),)),
		sp.Piecewise: lambda self, spt: AST ('-piece', tuple ((self._spt2ast (t [0]), True if isinstance (t [1], sp.boolalg.BooleanTrue) else self._spt2ast (t [1])) for t in spt.args)),
		sp.Subs: lambda self, spt: AST ('-func', 'Subs', tuple (self._spt2ast (a) for a in spt.args) if len (spt.args [1]) > 1 else (self._spt2ast (spt.args [0]), self._spt2ast (spt.args [1] [0]), self._spt2ast (spt.args [2] [0]))),

		sp.Function: _spt2ast_Function,
		sp_AppliedUndef: _spt2ast_AppliedUndef,
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

def set_pyS (state):
	global _PYS
	_PYS = state

def set_simplify (state):
	global _POST_SIMPLIFY
	_POST_SIMPLIFY = state

def set_doit (state):
	global _DOIT
	_DOIT = state

class sym: # for single script
	set_precision  = set_precision
	set_user_funcs = set_user_funcs
	set_pyS        = set_pyS
	set_simplify   = set_simplify
	set_doit       = set_doit
	ast2tex        = ast2tex
	ast2nat        = ast2nat
	ast2py         = ast2py
	ast2spt        = ast2spt
	spt2ast        = spt2ast

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: # DEBUG!
# 	# vars = {'f': AST ('-lamb', ('^', ('@', 'x'), ('#', '2')), (('@', 'x'),))}
# 	# vars = {'f': AST ('-lamb', ('-int', ('@', 'x'), ('@', 'dx')), (('@', 'x'),))}
# 	# vars = {'theq': AST ('=', '=', ('+', (('@', 'c1'), ('^', ('@', 'x'), ('#', '2')), ('-', ('@', 'c2')), ('*', (('#', '2'), ('@', 'x'))))), ('+', (('@', 'x'), ('@', 'y'), ('-', ('*', (('@', 'c5'), ('@', 'c6')))))))}
# 	# vars = {'S': AST ('-lamb', ('-func', '$S', (('@', 'x'),)), (('@', 'x'),))}
# 	# ast = AST ('.', ('@', 'S'), 'Half')
# 	# res = ast2spt (ast, vars)

# 	ast = AST ('-dict', ((('@', 'partialx'), ('-func', 'Sum', (('-func', 'abs', (('-func', 'abs', (('@', 'dz'),)),)), ('(', (',', (('@', 'x'), ('*', (('@', 'lambda'), ('@', 'x'))), ('@', 'y'), ('-func', 'slice', (('@', 'z'), ('#', '1e+100'), ('-func', 'factorial', (('@', 'partial'),)))), ('/', ('-func', 'Intersection', (('-func', 'FiniteSet', ()), ('#', '0'), ('@', 'None'))), ('-dict', ((('#', '-1.0'), ('@', 'a')), (('"', 'str'), ('@', 'False')), (('#', '1e+100'), ('@', 'True'))))))))))), (('#', '0.1'), ('-sqrt', ('[', (('*', (('@', 'partial'), ('-func', 'diff', (('-func', 'diff', (('"', ' if \x0crac1xyzd]Sum (\x0cracpartialx1, (x, xyzd / "str", Sum (-1, (x, partialx, \\partial ))))}'),)),)))),))))))
# 	res = ast2tex (ast)
# 	# res = spt2ast (res)

# 	print (res)
