# Convert between internal AST and SymPy expressions and write out LaTeX, native shorthand and Python code.
# Here be dragons! MUST REFACTOR AT SOME POINT FOR THE LOVE OF ALL THAT IS GOOD AND PURE!

from ast import literal_eval
from collections import OrderedDict
from functools import reduce
import re
import sympy as sp
from sympy.core.function import AppliedUndef as sp_AppliedUndef

from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sxlat         # AUTO_REMOVE_IN_SINGLE_SCRIPT

_SYM_MARK_PY_ASS_EQ = False # for testing to write extra information into python text representation of Eq() if is assignment

_SYM_USER_FUNCS = set () # set of user funcs present {name, ...} - including hidden N and gamma and the like
_SYM_USER_VARS  = {} # flattened user vars {name: ast, ...}
_SYM_USER_ALL   = {} # all funcs and vars dict, user funcs not in vars stored as AST.Null

_POST_SIMPLIFY  = False # post-evaluation simplification
_PYS            = True # Python S() escaping
_DOIT           = True # expression doit()
_MUL_RATIONAL   = False # products should lead with a rational fraction if one is present instead of absorbing into it
_STRICT_TEX     = False # strict LaTeX formatting to assure copy-in ability of generated tex

class _None: pass # unique non-None None marker

class AST_Text (AST): # for displaying elements we do not know how to handle, only returned from SymPy processing, not passed in
	op, is_text = '-text', True

	def _init (self, tex = None, nat = None, py = None, spt = None):
		self.tex, self.nat, self.py, self.spt = tex, nat, py, spt

AST.register_AST (AST_Text)

class EqAss (sp.Eq): pass # explicit assignment instead of equality comparison
class EqCmp (sp.Eq): pass # explicit equality comparison instead of assignment

class IdLambda (sp.Lambda): # having SymPy remap Lambda (y, y) to Lambda (_x, _x) is really annoying
	def __new__ (cls, a, l, **kw):
		self = sp.Lambda.__new__ (cls, sp.Symbol (l.name), l.name)

		return self

class NoEval (sp.Expr): # prevent any kind of evaluation on AST on instantiation or doit, args = (str (AST), sp.S.One)
	is_number    = False
	free_symbols = set ()

	def __new__ (cls, ast):
		self     = sp.Expr.__new__ (cls, str (ast))
		self.ast = AST (*literal_eval (ast)) if isinstance (ast, str) else ast # SymPy might re-create this object using string argument

		return self

	def doit (self, *args, **kw):
		return self

def _raise (exc):
	raise exc

def _sympify (spt, sympify = sp.sympify, fallback = None): # try to sympify argument with optional fallback conversion function
	try:
		return sympify (spt)

	except:
		if fallback is True: # True for return original value
			return spt
		elif fallback is None:
			raise

		else:
			try:
				return fallback (spt)
			except Exception as e:
				raise e from None

def _free_symbols (spt): # extend sympy .free_symbols into standard python containers
	if isinstance (spt, (None.__class__, bool, int, float, complex, str)):
		pass # nop
	elif isinstance (spt, (tuple, list, set, frozenset)):
		return set ().union (*(_free_symbols (s) for s in spt))
	elif isinstance (spt, slice):
		return _free_symbols (spt.start).union (_free_symbols (spt.stop), _free_symbols (spt.step))
	elif isinstance (spt, dict):
		return set ().union (*(_free_symbols (s) for s in sum (spt.items (), ())))
	else:
		return getattr (spt, 'free_symbols', set ())

	return set ()

def _simplify (spt): # extend sympy simplification into standard python containers
	if isinstance (spt, (None.__class__, bool, int, float, complex, str)):
		return spt
	elif isinstance (spt, (tuple, list, set, frozenset)):
		return spt.__class__ (_simplify (a) for a in spt)
	elif isinstance (spt, slice):
		return slice (_simplify (spt.start), _simplify (spt.stop), _simplify (spt.step))
	elif isinstance (spt, dict):
		return dict ((_simplify (k), _simplify (v)) for k, v in spt.items ())

	if not isinstance (spt, (sp.Naturals.__class__, sp.Integers.__class__)): # these break on count_ops()
		try:
			spt2 = sp.simplify (spt)

			if sp.count_ops (spt2) <= sp.count_ops (spt): # sometimes simplify doesn't
				spt = spt2

		except:
			pass

	return spt

def _doit (spt): # extend sympy .doit() into standard python containers
	if isinstance (spt, (None.__class__, bool, int, float, complex, str)):
		return spt
	elif isinstance (spt, (tuple, list, set, frozenset)):
		return spt.__class__ (_doit (a) for a in spt)
	elif isinstance (spt, slice):
		return slice (_doit (spt.start), _doit (spt.stop), _doit (spt.step))
	elif isinstance (spt, dict):
		return dict ((_doit (k), _doit (v)) for k, v in spt.items ())

	try:
		return spt.doit (deep = True)
	except:
		pass

	return spt

def _subs (spt, subs): # extend sympy .subs() into standard python containers, subs = [(s1, d1), (s2, d2), ...]
	if not subs:
		return spt

	if isinstance (spt, (tuple, list, set, frozenset, slice, dict)):
		for i, (s, d) in enumerate (subs):
			if s == spt:
				return _subs (d, subs [:i] + subs [i + 1:])

		if isinstance (spt, slice):
			return slice (_subs (spt.start, subs), _subs (spt.stop, subs), _subs (spt.step, subs))
		elif isinstance (spt, dict):
			return dict ((_subs (k, subs), _subs (v, subs)) for k, v in spt.items ())
		else: # isinstance (spt, (tuple, list, set, frozenset)):
			return spt.__class__ (_subs (a, subs) for a in spt)

	elif isinstance (spt, sp.Derivative) and isinstance (spt.args [0], sp_AppliedUndef): # do not subs derivative of appliedundef (d/dx (f (x, y))) to preserve info about variables
		vars     = set (spt.args [0].args)
		spt      = sp.Subs (spt, *zip (*filter (lambda sd: sd [0] in vars, subs)))
		spt.doit = lambda self = spt, *args, **kw: self # disable doit because loses information

	else:
		try:
			if isinstance (spt, (bool, int, float, complex)):
				return sp.sympify (spt).subs (subs)
			else:
				return spt.subs (subs)

		except:
			pass

	return spt

# def _dsolve (*args, **kw):
# 	ast = spt2ast (sp.dsolve (*args, **kw))

# 	if ast.is_brack:
# 		ast = AST ('[', tuple (AST ('=', a.lhs, a.cmp [0] [1]) if a.cmp.len == 1 and a.cmp [0] [0] == '==' else a for a in ast.brack))

# 	elif ast.is_cmp:
# 		if ast.cmp.len == 1 and ast.cmp [0] [0] == '==': # convert equality to assignment
# 			ast = AST ('=', ast.lhs, ast.cmp [0] [1])

# 	return NoEval (ast) # never automatically simplify dsolve

# 	return ast

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

def _bool_or_None (v):
	return None if v is None else bool (v)

def _fltoint (num):
	return int (num) if isinstance (num, int) or num.is_integer () else num

def _trail_comma (obj):
	return ',' if len (obj) == 1 else ''

def _ast_is_neg (ast):
	return ast.is_minus or ast.is_num_neg or (ast.is_mul and _ast_is_neg (ast.mul [0]))

def _ast_is_neg_nominus (ast):
	return ast.is_num_neg or (ast.is_mul and _ast_is_neg (ast.mul [0]))

def _ast_is_top_ass_lhs (self, ast):
	return (self.parent.is_ass and ast is self.parent.lhs and self.parents [-2].op in {None, ';'}) or \
		(self.parent.is_comma and self.parents [-2].is_ass and self.parent is self.parents [-2].lhs and self.parents [-3].op in {None, ';'})

def _ast_eqcmp2ass (ast, parent = AST.Null):
	if not isinstance (ast, AST):
		return ast

	if ast.is_cmp and not ast.is_cmp_explicit and ast.cmp.len == 1 and ast.cmp [0] [0] == '==' and (
			parent.op in {None, ';', '<>', ',', '(', '[', '-', '!', '+', '*', '/', '^', '-log', '-sqrt', '-diff', '-diffp', '-mat', '-lamb', '-idx', '-set', '||', '^^', '&&', '-subs'} or
			parent.is_attr_var or
			(parent.is_attr_func and (ast is parent.obj or not ast.lhs.as_identifier)) or
			(parent.op in {'-lim', '-sum', '-intg'} and ast is parent [1]) or
			(parent.is_func and not ast.lhs.as_identifier)):
		return AST ('=', _ast_eqcmp2ass (ast.lhs, ast), _ast_eqcmp2ass (ast.cmp [0] [1], ast))

	return AST (*(_ast_eqcmp2ass (a, ast) for a in ast))

def _ast_slice_bounds (ast, None_ = AST.VarNull, allow1 = False):
	if allow1 and not ast.start and not ast.step:
		return (ast.stop or None_,)

	return tuple (a or None_ for a in ((ast.start, ast.stop) if ast.step is None else (ast.start, ast.stop, ast.step)))

def _ast_followed_by_slice (ast, seq):
	for i in range (len (seq)):
		if seq [i] is ast:
			for i in range (i + 1, len (seq)):
				if seq [i].is_slice:
					return True
				elif not seq [i].is_var:
					break

			break

	return False

def _ast_func_call (func, args, _ast2spt = None):
	if _ast2spt is None:
		_ast2spt = ast2spt

	pyargs, pykw = AST.args2kwargs (args, _ast2spt)

	return func (*pyargs, **pykw)

def _ast_has_open_differential (ast, istex):
	if ast.is_differential or (not istex and
			((ast.is_diff_d and (not ast.is_diff_dvdv and ast.dvs [-1] [-1] == 1)) or
			(ast.is_subs_diff_d_ufunc and (not ast.expr.is_diff_dvdv and ast.expr.dvs [-1] [-1] == 1)))):
		return True
	elif istex and ast.is_div or ast.op in {'[', '|', '-log', '-sqrt', '-func', '-diff', '-intg', '-mat', '-set', '-dict', '-ufunc', '-subs'}: # specifically not checking '(' because that might be added by ast2tex/nat in subexpressions
		return False
	elif ast.op in {'.', '^', '-log', '-sqrt', '-lim', '-sum', '-diffp', '-lamb', '-idx'}:
		return _ast_has_open_differential (ast [1], istex = istex)

	return any (_ast_has_open_differential (a, istex = istex) if isinstance (a, AST) else False for a in (ast if ast.op is None else ast [1:]))

def _ast_subs2func (ast): # ast is '-subs'
	func = ast.expr

	if func.op in {'-diff', '-diffp'}:
		func = func [1]

	func = _SYM_USER_VARS.get (func.var, func)

	if func.is_lamb:
		vars = ast.subs [:func.vars.len]

		if tuple (s.var for s, _ in vars) == func.vars:
			return [AST ('=', s, d) for s, d in ast.subs [func.vars.len:]], tuple (d for _, d in vars)

	elif func.is_ufunc_applied:
		subs = []
		vars = OrderedDict ((v, v) for v in func.vars)

		for s, d in ast.subs:
			if s.is_var_nonconst and d.is_const and vars.get (s) == s:
				vars [s] = d
			else:
				subs.append (AST ('=', s, d))

		return subs, vars.values ()

	return [AST ('=', s, d) for s, d in ast.subs], None

#...............................................................................................
class ast2tex: # abstract syntax tree -> LaTeX text
	def __init__ (self): self.parent = self.ast = None # pylint medication
	def __new__ (cls, ast, retxlat = False):
		def func_call (func, args):
			return spt2ast (_ast_func_call (getattr (sp, func), args))

		self         = super ().__new__ (cls)
		self.parents = [None]
		self.parent  = self.ast = AST.Null

		astx = sxlat.xlat_funcs2asts (ast, sxlat.XLAT_FUNC2AST_TEX, func_call = func_call)
		tex  = self._ast2tex (astx)

		return tex if not retxlat else (tex, (astx if astx != ast else None))

	def _ast2tex (self, ast):
		self.parents.append (self.ast)

		self.parent = self.ast
		self.ast    = ast

		tex         = self._ast2tex_funcs [ast.op] (self, ast)

		del self.parents [-1]

		self.ast    = self.parent
		self.parent = self.parents [-1]

		return tex

	def _ast2tex_wrap (self, obj, curly = None, paren = None):
		paren = (obj.op in paren) if isinstance (paren, set) else paren
		curly = (obj.op in curly) if isinstance (curly, set) else curly
		s     = self._ast2tex (obj if not obj.is_slice or paren or not curly or obj.step is not None else AST ('-slice', obj.start, obj.stop, False)) if isinstance (obj, AST) else str (obj)

		return f'\\left({s} \\right)' if paren else f'{{{s}}}' if curly else s

	def _ast2tex_cmp (self, ast):
		return f'{self._ast2tex_cmp_hs (ast.lhs)} {" ".join (f"{AST.Cmp.PY2TEX.get (r, r)} {self._ast2tex_cmp_hs (e)}" for r, e in ast.cmp)}'

	def _ast2tex_curly (self, ast):
		if ast.is_single_unit:
			return f'{self._ast2tex (ast)}'
		elif ast.op not in {',', '-slice'}:
			return f'{{{self._ast2tex (ast)}}}'
		else:
			return f'{{\\left({self._ast2tex (ast)} \\right)}}'

	def _ast2tex_paren (self, ast, ops = {}):
		return self._ast2tex_wrap (ast, 0, not (ast.op in {'(', '-lamb'} or (ops and ast.op not in ops)))

	def _ast2tex_paren_mul_exp (self, ast, ret_has = False, also = {'=', '<>', '+', '-slice', '||', '^^', '&&', '-or', '-and', '-not'}):
		if ast.is_mul:
			s, has = self._ast2tex_mul (ast, True)
		else:
			s, has = self._ast2tex (ast), ast.op in also

		s = self._ast2tex_wrap (s, 0, has)

		return (s, has) if ret_has else s

	def _ast2tex_ass_hs (self, hs, lhs = True):
		return self._ast2tex_wrap (hs, 0, hs.is_ass or hs.is_slice or
			(lhs and (hs.is_piece or (hs.is_comma and (self.parent and not self.parent.is_scolon)))))

	def _ast2tex_cmp_hs (self, hs):
		return self._ast2tex_wrap (hs, 0, {'=', '<>', '-piece', '-slice', '-or', '-and', '-not'})

	def _ast2tex_num (self, ast):
		m, e = ast.num_mant_and_exp

		return f'{m}{{e}}{{{e}}}' if e else m

	def _ast2tex_var (self, ast):
		if ast.is_var_null:
			return '\\{' if self.parent.op in {None, ';'} else '{}'

		texmulti = AST.Var.PY2TEXMULTI.get (ast.var)

		if texmulti: # for stuff like "Naturals0"
			return texmulti [0]

		n, s = ast.text_and_tail_num
		n    = n.replace ('_', '\\_')
		t    = AST.Var.PY2TEX.get (n)

		if s:
			s = f'_{{{s}}}'

		return \
				f'{t or n}{s}'      if not ast.diff_or_part_type else \
				f'd{t or n}{s}'     if ast.is_diff_any else \
				f'\\partial'        if ast.is_part_solo else \
				f'\\partial{t}{s}'  if t else \
				f'\\partial {n}{s}' if n else \
				f'\\partial'

	def _ast2tex_attr (self, ast):
		tex = sxlat.xlat_attr2tex (ast, self._ast2tex)

		if tex is not None:
			return tex

		a = ast.attr.replace ('_', '\\_')

		if ast.is_attr_func:
			a = f'\\operatorname{{{a}}}\\left({self._ast2tex (AST.tuple2ast (ast.args))} \\right)'

		return f'{self._ast2tex_wrap (ast.obj, ast.obj.is_pow or ast.obj.is_subs_diff_ufunc, {"=", "<>", "#", ",", "-", "+", "*", "/", "-lim", "-sum", "-diff", "-intg", "-piece", "-slice", "||", "^^", "&&", "-or", "-and", "-not"})}.{a}'

	def _ast2tex_minus (self, ast):
		s = self._ast2tex_wrap (ast.minus, ast.minus.is_mul, {"=", "<>", "+", "-slice", "||", "^^", "&&", "-or", "-and", "-not"})

		return f'-{{{s}}}' if s [:6] != '\\left(' and ast.minus.strip_fdpi.is_num_pos else f'-{s}'

	def _ast2tex_add (self, ast):
		terms = []

		for n in ast.add:
			not_first = n is not ast.add [0]
			not_last  = n is not ast.add [-1]
			op        = ' + '

			if n.is_minus and not_first: # and n.minus.is_num_pos
				op, n = ' - ', n.minus

			s = self._ast2tex (n)

			terms.extend ([op, self._ast2tex_wrap (s,
				n.is_piece or (not_first and _ast_is_neg_nominus (n)) or (not_last and s [-1:] != ')' and (n.strip_mmls.is_intg or (n.is_mul and n.mul [-1].strip_mmls.is_intg))),
				(n.is_piece and not_last) or n.op in {'=', '<>', '+', '-slice', '||', '^^', '&&', '-or', '-and', '-not'})]) # , '-subs'})])

		return ''.join (terms [1:]).replace (' + -', ' - ')

	def _ast2tex_mul (self, ast, ret_has = False):
		t   = []
		p   = None
		has = False

		for n in ast.mul: # i, n in enumerate (ast.mul):
			s = self._ast2tex_wrap (n, (p and _ast_is_neg (n)),
					n.op in {'=', '<>', '+', '-slice', '||', '^^', '&&', '-or', '-and', '-not'} or (n.is_piece and n is not ast.mul [-1]))

			if ((p and n.op in {'/', '-diff'} and p.op in {'#', '/'} and n.op != p.op) or
					(n.strip_mmls.is_intg and n is not ast.mul [-1] and s [-1:] not in {'}', ')', ']'})):
				s = f'{{{s}}}'

			if p and (
					t [-1] [-1:] == '.' or
					s [:1].isdigit () or
					s [:6] == '\\left[' or
					(s [:6] == '\\left(' and (
						p.tail_mul.is_attr_var or
						p.tail_mul.op in {'@', '-diffp', '-ufunc', '-subs'})) or
						# i in ast.exp)) or
					_ast_is_neg (n) or
					n.is_var_null or
					n.op in {'#', '-mat'} or
					p.strip_minus.op in {'-lim', '-sum', '-diff', '-intg', '-mat'} or
					(p.tail_mul.is_var and (p.tail_mul.var == '_' or p.tail_mul.var in _SYM_USER_FUNCS)) or
					(n.is_div and p.is_div) or
					(n.is_attr and n.strip_attr.strip_paren.is_comma) or
					(n.is_pow and (n.base.is_num_pos or n.base.strip_paren.is_comma)) or
					(n.is_idx and (n.obj.is_idx or n.obj.strip_paren.is_comma))):
				t.append (f' \\cdot {s}')
				has = True

			elif p and (
					p.is_sqrt or
					p.num_exp or
					(p.is_attr_var and s [:6] != '\\left(') or # comment this out if separating all variables with spaces
					p.strip_minus.is_diff_or_part_any or
					n.is_diff_or_part_any or
					# ((p.tail_mul.is_var or p.tail_mul.is_attr_var) and s [:1] != '{' and s [:6] != '\\left(' and n.strip_afpdpi.is_var) or # comment this IN if separating all variables with spaces
					(not s.startswith ('{') and s [:6] not in {'\\left(', '\\left['} and (
						p.is_var_long or
						(n.strip_afpdpi.is_var_long and t [-1] [-7:] not in {'\\right)', '\\right]'})
					))):
				t.append (f'\\ {s}')

			else:
				t.append (f'{"" if not p else " "}{s}')

			p = n

		return (''.join (t), has) if ret_has else ''.join (t)

	def _ast2tex_div (self, ast):
		false_diff = (ast.numer.base.is_diff_or_part_solo and ast.numer.exp.is_num_pos_int) if ast.numer.is_pow else \
				(ast.numer.mul.len == 2 and ast.numer.mul [1].is_var and ast.numer.mul [0].is_pow and ast.numer.mul [0].base.is_diff_or_part_solo and ast.numer.mul [0].exp.strip_curly.is_num_pos_int) if ast.numer.is_mul else \
				ast.numer.is_diff_or_part_solo

		return f'\\frac{{{self._ast2tex_wrap (ast.numer, 0, ast.numer.is_slice or false_diff)}}}{{{self._ast2tex_wrap (ast.denom, 0, {"-slice"})}}}'

	def _ast2tex_pow (self, ast, trighpow = True):
		b = self._ast2tex_wrap (ast.base, {'-mat'}, not (ast.base.op in {'@', '.', '"', '(', '[', '|', '-log', '-func', '-mat', '-lamb', '-idx', '-set', '-dict', '-ufunc'} or ast.base.is_num_pos))
		p = self._ast2tex_curly (ast.exp)

		if trighpow and ast.base.is_trigh_func_noninv and ast.exp.is_num and ast.exp.num != '-1': # and ast.exp.is_single_unit
			i = len (ast.base.func) + (15 if ast.base.func in {'sech', 'csch'} else 1)

			return f'{b [:i]}^{p}{b [i:]}'

		return f'{b}^{p}'

	def _ast2tex_log (self, ast):
		if ast.base is None:
			return f'\\ln{{\\left({self._ast2tex (ast.log)} \\right)}}'
		else:
			return f'\\log_{self._ast2tex_curly (ast.base)}{{\\left({self._ast2tex (ast.log)} \\right)}}'

	_rec_tailnum = re.compile (r'^(.+)(?<![\d_])(\d*)$')

	def _ast2tex_func (self, ast):
		if ast.is_trigh_func:
			if ast.func [0] != 'a':
				n = f'\\operatorname{{{ast.func}}}' if ast.func in {'sech', 'csch'} else f'\\{ast.func}'
			elif ast.func in {'asech', 'acsch'}:
				n = f'\\operatorname{{{ast.func [1:]}}}^{{-1}}'
			else:
				n = f'\\{ast.func [1:]}^{{-1}}'

			return f'{n}{{\\left({self._ast2tex (AST.tuple2ast (ast.args))} \\right)}}'

		tex = sxlat.xlat_func2tex (ast, self._ast2tex)

		if tex is not None:
			return tex

		if ast.func in AST.Func.TEX:
			func = f'\\{ast.func}'

		elif ast.func in {AST.Func.NOREMAP, AST.Func.NOEVAL}:
			func = ast.func.replace (AST.Func.NOEVAL, '\\%')

			if ast.args [0].op in {'@', '(', '[', '|', '-func', '-mat', '-lamb', '-set', '-dict'}:
				return f'{func}{self._ast2tex (AST.tuple2ast (ast.args))}'

		elif ast.func not in AST.Func.PY:
			m         = self._rec_tailnum.match (ast.func)
			func, sub = m.groups () if m else (ast.func, None)
			func      = func.replace ('_', '\\_')
			func      = f'\\operatorname{{{func}_{{{sub}}}}}' if sub else f'\\operatorname{{{func}}}'

		else:
			func = ast.func.replace ('_', '\\_')
			func = f'\\operatorname{{{AST.Var.GREEK2TEX.get (ast.func, func)}}}'

		return f'{func}{{\\left({self._ast2tex (AST.tuple2ast (ast.args))} \\right)}}'

	def _ast2tex_lim (self, ast):
		s = self._ast2tex_wrap (ast.to, False, ast.to.is_slice) if ast.dir is None else (self._ast2tex_pow (AST ('^', ast.to, AST.Zero), trighpow = False) [:-1] + ast.dir)

		return f'\\lim_{{{self._ast2tex (ast.lvar)} \\to {s}}} {self._ast2tex_paren_mul_exp (ast.lim)}'

	def _ast2tex_sum (self, ast):
		return f'\\sum_{{{self._ast2tex (ast.svar)} = {self._ast2tex (ast.from_)}}}^{self._ast2tex_curly (ast.to)} {self._ast2tex_paren_mul_exp (ast.sum)}' \

	def _ast2tex_diff (self, ast):
		if ast.diff.is_var and not ast.diff.is_diff_or_part:
			top  = self._ast2tex (ast.diff)
			topp = f' {top}'
			side = ''

		else:
			top  = topp = ''
			side = self._ast2tex_wrap (ast.diff, 0, ast.diff.op not in {'(', '-lamb'})

		ds = set ()
		dp = 0

		for v, p in ast.dvs:
			ds.add (v)
			dp += p

		if not ds:
			return f'\\frac{{d{top}}}{{}}{side}'

		is_d = len (ds) <= 1 and ast.is_diff_d

		if is_d:
			diff = _SYM_USER_VARS.get (ast.diff.var, ast.diff)

			if diff.is_lamb:
				diff = diff.lamb

			is_d = len (diff.free_vars) <= 1

		if is_d:
			dvs = " ".join (self._ast2tex (AST ('@', f'd{v}') if p == 1 else AST ('^', AST ('@', f'd{v}'), AST ('#', p))) for v, p in ast.dvs)

			return f'\\frac{{d{top if dp == 1 else f"^{dp}{topp}"}}}{{{dvs}}}{side}'

		else:
			dvs = " ".join (self._ast2tex (AST ('@', f'partial{v}') if p == 1 else AST ('^', AST ('@', f'partial{v}'), AST ('#', p))) for v, p in ast.dvs)

			return f'\\frac{{\\partial{topp if dp == 1 else f"^{dp}{topp}"}}}{{{dvs}}}{side}'

	def _ast2tex_intg (self, ast):
		if ast.intg is None:
			intg  = ' '

		else:
			curly = ast.intg.op in {"-diff", "-slice", "||", "^^", "&&", "-or", "-and", "-not"} or ast.intg.tail_mul.op in {"-lim", "-sum"}
			intg  = self._ast2tex_wrap (ast.intg, curly, {"=", "<>"})
			intg  = f' {{{intg}}} ' if not curly and _ast_has_open_differential (ast.intg, istex = True) else f' {intg} '

		if ast.from_ is None:
			return f'\\int{intg}\\ {self._ast2tex (ast.dv)}'
		else:
			return f'\\int_{self._ast2tex_curly (ast.from_)}^{self._ast2tex_curly (ast.to)}{intg}\\ {self._ast2tex (ast.dv)}'

	def _ast2tex_idx (self, ast):
		obj = self._ast2tex_wrap (ast.obj,
			ast.obj.op in {"^", "-slice"} or ast.obj.is_subs_diff_ufunc or (ast.obj.is_var and ast.obj.var in _SYM_USER_FUNCS),
			ast.obj.is_num_neg or ast.obj.op in {"=", "<>", ",", "-", "+", "*", "/", "-lim", "-sum", "-diff", "-intg", "-piece", "||", "^^", "&&", "-or", "-and", "-not"})
		idx = '[' if ast.idx.len and ast.idx [0].is_var_null else f'\\left[{self._ast2tex (AST.tuple2ast (ast.idx))} \\right]'

		return f'{obj}{idx}'

	def _ast2tex_ufunc (self, ast):
		user = _SYM_USER_ALL.get (ast.ufunc)

		# if not _STRICT_TEX and user and user.is_lamb and ast.matches_lamb_sig (user):
		# 	return self._ast2tex_func (AST ('-func', ast.ufunc, ast.vars))

		if _STRICT_TEX and (ast.is_ufunc_explicit or not ast.ufunc or
					(user and
					(not user.is_ufunc or (ast != user and not user.can_apply_argskw ((ast.vars, ast.kw)) if user.vars else (ast.kw and ast.kw != user.kw))) and
					# not (user.is_lamb and ast.matches_lamb_sig (user)) and
					not _ast_is_top_ass_lhs (self, ast)) or
				not ast.vars.as_ufunc_argskw):
			pre = '?' # '\\: ?'
		else:
			pre = ''

		name = self._ast2tex (AST ("@", ast.ufunc)) if ast.ufunc else ""
		args = ", ".join (tuple (self._ast2tex (v) for v in ast.vars) + tuple (f"{k} = {self._ast2tex_wrap (a, 0, a.is_comma)}" for k, a in ast.kw))

		return f'{pre}{name}\\left({args} \\right)'

	def _ast2tex_subs (self, ast):
		subs, vars = _ast_subs2func (ast)

		if len (subs) == ast.subs.len:
			expr = self._ast2tex (ast.expr)

		else:
			expr = f'{self._ast2tex (ast.expr)}\\left({", ".join (self._ast2tex (v) for v in vars)} \\right)'

			if not subs:
				return expr

		if len (subs) == 1:
			subs = self._ast2tex (subs [0])
		else:
			subs = '\\substack{' + ' \\\\ '.join (self._ast2tex (s) for s in subs) + '}'

		return f'\\left. {expr} \\right|_{{{subs}}}'

	_ast2tex_funcs = {
		';'     : lambda self, ast: ';\\: '.join (self._ast2tex (a) for a in ast.scolon),
		'='     : lambda self, ast: f'{self._ast2tex_ass_hs (ast.lhs)} = {self._ast2tex_ass_hs (ast.rhs, False)}',
		'<>'    : _ast2tex_cmp,
		'#'     : _ast2tex_num,
		'@'     : _ast2tex_var,
		'.'     : _ast2tex_attr,
		'"'     : lambda self, ast: '\\text{' + repr (ast.str_).replace ('}', '\\}') + '}',
		','     : lambda self, ast: f'{", ".join (self._ast2tex (c) for c in ast.comma)}{_trail_comma (ast.comma)}',
		'('     : lambda self, ast: '(' if ast.paren.is_var_null else self._ast2tex_wrap (ast.paren, 0, 1), # not ast.paren.is_lamb),
		'['     : lambda self, ast: '[' if ast.brack.len == 1 and ast.brack [0].is_var_null else f'\\left[{", ".join (self._ast2tex (b) for b in ast.brack)} \\right]',
		'|'     : lambda self, ast: '|' if ast.abs.is_var_null else f'\\left|{self._ast2tex (ast.abs)} \\right|',
		'-'     : _ast2tex_minus,
		'!'     : lambda self, ast: self._ast2tex_wrap (ast.fact, {'^'}, (ast.fact.op not in {'#', '@', '.', '"', '(', '[', '|', '!', '^', '-func', '-mat', '-idx', '-set', '-dict', '-sym'} or ast.fact.is_num_neg)) + '!',
		'+'     : _ast2tex_add,
		'*'     : _ast2tex_mul,
		'/'     : _ast2tex_div,
		'^'     : _ast2tex_pow,
		'-log'  : _ast2tex_log,
		'-sqrt' : lambda self, ast: f'\\sqrt{{{self._ast2tex_wrap (ast.rad, 0, {",", "-slice"})}}}' if ast.idx is None else f'\\sqrt[{self._ast2tex (ast.idx)}]{{{self._ast2tex_wrap (ast.rad, 0, {",", "-slice"})}}}',
		'-func' : _ast2tex_func,
		'-lim'  : _ast2tex_lim,
		'-sum'  : _ast2tex_sum,
		'-diff' : _ast2tex_diff,
		'-diffp': lambda self, ast: self._ast2tex_wrap (ast.diffp, ast.diffp.is_subs_diff_any_ufunc, ast.diffp.is_num_neg or ast.diffp.op in {"=", "<>", "-", "+", "*", "/", "^", "-sqrt", "-lim", "-sum", "-diff", "-intg", "-piece", "-slice", "||", "^^", "&&", "-or", "-and", "-not"}) + "'" * ast.count,
		'-intg' : _ast2tex_intg,
		'-mat'  : lambda self, ast: '\\begin{bmatrix} ' + r' \\ '.join (' & '.join (self._ast2tex_wrap (e, 0, e.is_slice) for e in row) for row in ast.mat) + f'{" " if ast.mat else ""}\\end{{bmatrix}}',
		'-piece': lambda self, ast: '\\begin{cases} ' + r' \\ '.join (f'{self._ast2tex_wrap (p [0], 0, {"=", "<>", ",", "-slice"})} & \\text{{otherwise}}' if p [1] is True else f'{self._ast2tex_wrap (p [0], 0, {"=", "<>", ",", "-slice"})} & \\text{{for}}\\: {self._ast2tex_wrap (p [1], 0, {"-slice"})}' for p in ast.piece) + ' \\end{cases}',
		'-lamb' : lambda self, ast: f'\\left({self._ast2tex (AST ("@", ast.vars [0]) if ast.vars.len == 1 else AST ("(", (",", tuple (("@", v) for v in ast.vars))))} \\mapsto {self._ast2tex (ast.lamb)} \\right)',
		'-idx'  : _ast2tex_idx,
		'-slice': lambda self, ast: self._ast2tex_wrap ('{:}'.join (self._ast2tex_wrap (a, a and _ast_is_neg (a), a and a.op in {'=', ',', '-slice'}) for a in _ast_slice_bounds (ast, '')), 0, not ast.start and self.parent.is_comma and ast is self.parent.comma [0] and self.parents [-2].is_ass and self.parent is self.parents [-2].rhs),
		'-set'  : lambda self, ast: f'\\left\\{{{", ".join (self._ast2tex_wrap (c, 0, c.is_slice) for c in ast.set)} \\right\\}}' if ast.set else '\\emptyset',
		'-dict' : lambda self, ast: f'\\left\\{{{", ".join (f"{self._ast2tex_wrap (k, 0, k.is_slice)}{{:}} {self._ast2tex_wrap (v, 0, v.is_slice)}" for k, v in ast.dict)} \\right\\}}',
		'||'    : lambda self, ast: ' \\cup '.join (self._ast2tex_wrap (a, 0, a.op in {'=', '<>', ',', '-slice', '-or', '-and', '-not'} or (a.is_piece and a is not ast.union [-1])) for a in ast.union),
		'^^'    : lambda self, ast: ' \\ominus '.join (self._ast2tex_wrap (a, 0, a.op in {'=', '<>', ',', '-slice', '||', '-or', '-and', '-not'} or (a.is_piece and a is not ast.sdiff [-1])) for a in ast.sdiff),
		'&&'    : lambda self, ast: ' \\cap '.join (self._ast2tex_wrap (a, 0, a.op in {'=', '<>', ',', '-slice', '||', '^^', '-or', '-and', '-not'} or (a.is_piece and a is not ast.xsect [-1])) for a in ast.xsect),
		'-or'   : lambda self, ast: ' \\vee '.join (self._ast2tex_wrap (a, 0, a.op in {'=', ',', '-slice'} or (a.is_piece and a is not ast.or_ [-1])) for a in ast.or_),
		'-and'  : lambda self, ast: ' \\wedge '.join (self._ast2tex_wrap (a, 0, a.op in {'=', ',', '-slice', '-or'} or (a.is_piece and a is not ast.and_ [-1])) for a in ast.and_),
		'-not'  : lambda self, ast: f'\\neg\\ {self._ast2tex_wrap (ast.not_, 0, ast.not_.op in {"=", ",", "-slice", "-or", "-and"})}',
		'-ufunc': _ast2tex_ufunc,
		'-subs' : _ast2tex_subs,
		'-sym'  : lambda self, ast: f'\\${self._ast2tex (AST ("@", ast.sym)) if ast.sym else ""}\\left({", ".join (tuple (f"{k} = {self._ast2tex_wrap (a, 0, a.is_comma)}" for k, a in ast.kw))} \\right)',

		'-text' : lambda self, ast: ast.tex,
	}

#...............................................................................................
class ast2nat: # abstract syntax tree -> native text
	def __init__ (self): self.parent = self.ast = None # pylint droppings
	def __new__ (cls, ast, retxlat = False):
		self         = super ().__new__ (cls)
		self.parents = [None]
		self.parent  = self.ast = AST.Null

		astx = sxlat.xlat_funcs2asts (ast, sxlat.XLAT_FUNC2AST_NAT)
		nat  = self._ast2nat (astx)

		return nat if not retxlat else (nat, (astx if astx != ast else None))

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
		isast = isinstance (obj, AST)
		paren = (obj.op in paren) if isinstance (paren, set) else paren
		curly = ((obj.op in curly) if isinstance (curly, set) else curly) and not (isast and obj.is_abs)
		s     = self._ast2nat (obj if not obj.is_slice or paren or not curly or obj.step is not None else AST ('-slice', obj.start, obj.stop, False)) if isast else str (obj)

		return f'({s})' if paren else f'{{{s}}}' if curly else s

	def _ast2nat_curly (self, ast, ops = {}):
		if ast.is_slice:
			ast = AST ('(', ast)

		return self._ast2nat_wrap (ast, ops if ops else (ast.is_div or not ast.is_single_unit or (ast.is_var and ast.var in AST.Var.PY2TEX)))

	def _ast2nat_paren (self, ast, ops = {}):
		return self._ast2nat_wrap (ast, 0, not (ast.is_paren or (ops and ast.op not in ops)))

	def _ast2nat_curly_mul_exp (self, ast, ret_has = False, also = {}):
		if ast.is_mul:
			s, has = self._ast2nat_mul (ast, True)
		else:
			s, has = self._ast2nat (ast), False

		has = has or ((ast.op in also) if isinstance (also, set) else also)
		s   = self._ast2nat_wrap (s, has, ast.is_slice)

		return (s, has) if ret_has else s

	def _ast2nat_ass_hs (self, hs, lhs = True):
		return self._ast2nat_wrap (hs, 0, hs.is_ass or hs.is_slice or (lhs and (hs.op in {'-piece', '-lamb'}) or (hs.is_comma and (self.parent and not self.parent.is_scolon))) or \
				(not lhs and hs.is_lamb and self.parent.op in {'-set', '-dict'}))

	def _ast2nat_cmp_hs (self, hs):
		return self._ast2nat_wrap (hs, 0, {'=', '<>', '-piece', '-lamb', '-slice', '-or', '-and', '-not'})

	def _ast2nat_cmp (self, ast):
		return f'{self._ast2nat_cmp_hs (ast.lhs)} {" ".join (f"{AST.Cmp.PYFMT.get (r, r)} {self._ast2nat_cmp_hs (e)}" for r, e in ast.cmp)}'

	def _ast2nat_attr (self, ast):
		obj = self._ast2nat_wrap (ast.obj, ast.obj.is_pow or ast.obj.is_subs_diff_ufunc, {"=", "<>", "#", ",", "-", "+", "*", "/", "-lim", "-sum", "-diff", "-intg", "-piece", "-lamb", "-slice", "||", "^^", "&&", "-or", "-and", "-not"})

		if ast.is_attr_var:
			return f'{obj}.{ast.attr}'
		else:
			return f'{obj}.{ast.attr}({self._ast2nat (AST.tuple2ast (ast.args))})'

	def _ast2nat_minus (self, ast):
		s = self._ast2nat_wrap (ast.minus, ast.minus.op in {"*", "-diff", "-piece", "||", "^^", "&&", "-or", "-and"}, {"=", "<>", "+", "-lamb", "-slice", "-not"})

		return f'-{{{s}}}' if s [:1] not in {'{', '('} and ast.minus.strip_fdpi.is_num_pos else f'-{s}'

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

		for n in ast.mul: # i, n in enumerate (ast.mul):
			s = self._ast2nat_wrap (n,
				n.op in {'+', '-piece', '-lamb', '-slice', '||', '^^', '&&', '-or', '-and', '-not'} or
				(p and (
					_ast_is_neg (n) or
					(p.is_div and (p.denom.is_intg or (p.denom.is_mul and p.denom.mul [-1].is_intg)) and n.is_diff and n.diff.is_var and n.dvs [-1] [1] == 1))),
				n.op in {'=', '<>'})

			if n.strip_mmls.is_intg and n is not ast.mul [-1] and s [-1:] not in {'}', ')', ']'}:
				s = f'{{{s}}}'

			if p and (
					s [:1] == '[' or
					s [:1].isdigit () or
					(s [:1] == '(' and (
						p.tail_mul.is_attr_var or
						p.tail_mul.op in ('@', '-diffp', '-ufunc', '-subs'))) or
						# i in ast.exp)) or
					t [-1] [-1:] == '.' or
					n.is_num or
					n.is_var_null or
					n.op in {'/', '-diff'} or
					n.strip_attrdp.is_subs_diff_ufunc or
					p.strip_minus.op in {'/', '-lim', '-sum', '-diff', '-intg'} or
					(n.is_pow and (n.base.strip_paren.is_comma or n.base.is_num_pos)) or
					(n.is_attr and n.strip_attr.strip_paren.is_comma) or
					(n.is_idx and (n.obj.is_idx or n.obj.strip_paren.is_comma)) or
					(n.is_paren and p.tail_mul.is_var and not p.tail_mul.is_diff_or_part and n.as_pvarlist) or
					(p.has_tail_lambda and n is ast.mul [-1] and t [-1] [-6:] == 'lambda') or
					(p.tail_mul.is_var and p.tail_mul.var in _SYM_USER_FUNCS) or
					s [:1] in {'e', 'E'} and t [-1] [-1].isdigit ()
					):
				t.append (f' * {s}')
				has = True

			elif p and (
					p.is_diff_or_part_solo or
					n.op not in {'#', '|', '^'} or
					p.op not in {'#', '|'}):
				t.append (f' {s}')

			else:
				t.append (s)

			p = n

		return (''.join (t), has) if ret_has else ''.join (t)

	def _ast2nat_div (self, ast):
		false_diff = (ast.numer.base.is_diff_or_part_solo and ast.numer.exp.is_num_pos_int) if ast.numer.is_pow else \
				(ast.numer.mul.len == 2 and ast.numer.mul [1].is_var and ast.numer.mul [0].is_pow and ast.numer.mul [0].base.is_diff_or_part_solo and ast.numer.mul [0].exp.strip_curly.is_num_pos_int) if ast.numer.is_mul else \
				ast.numer.is_diff_or_part_solo

		n, ns = (self._ast2nat_wrap (ast.numer, 1), True) if _ast_is_neg (ast.numer) or (ast.numer.is_mul and ast.numer.mul [-1].op in {'-lim', '-sum'}) else \
				(self._ast2nat_wrap (ast.numer, 0, 1), True) if (ast.numer.is_slice or false_diff) else \
				self._ast2nat_curly_mul_exp (ast.numer, True, {'=', '<>', '+', '/', '-lim', '-sum', '-diff', '-intg', '-piece', '-lamb', '||', '^^', '&&', '-or', '-and', '-not'})

		d, ds = (self._ast2nat_wrap (ast.denom, 1), True) if ((_ast_is_neg (ast.denom) and ast.denom.strip_minus.is_div) or ast.denom.strip_minus.is_subs_diff_ufunc or (ast.denom.is_mul and ast.denom.mul [0].is_subs_diff_ufunc)) else \
				(self._ast2nat_wrap (ast.denom, 0, 1), True) if ast.denom.is_slice else \
				self._ast2nat_curly_mul_exp (ast.denom, True, {'=', '<>', '+', '/', '-lim', '-sum', '-diff', '-intg', '-piece', '-lamb', '||', '^^', '&&', '-or', '-and', '-not'})

		s     = ns or ds or ast.numer.strip_minus.op not in {'#', '@'} or ast.denom.strip_minus.op not in {'#', '@'}

		return f'{n}{" / " if s else "/"}{d}'

	def _ast2nat_pow (self, ast, trighpow = True):
		b = self._ast2nat_wrap (ast.base, 0, not (ast.base.op in {'@', '.', '"', '(', '[', '|', '-func', '-mat', '-idx', '-set', '-dict', '-ufunc'} or ast.base.is_num_pos))
		p = self._ast2nat_wrap (ast.exp,
				ast.exp.op in {'<>', '=', '+', '-lamb', '-slice', '-not'} or
				ast.exp.strip_minus.op in {'*', '/', '-lim', '-sum', '-diff', '-intg', '-piece', '||', '^^', '&&', '-or', '-and'} or
				ast.exp.strip_minus.is_subs_diff_ufunc,
				{","})

		if trighpow and ast.base.is_trigh_func_noninv and ast.exp.is_num and ast.exp.num != '-1': # and ast.exp.is_single_unit
			i = len (ast.base.func)

			return f'{b [:i]}**{p}{b [i:]}'

		return f'{b}**{p}'

	def _ast2nat_log (self, ast):
		if ast.base is None:
			return f'ln({self._ast2nat (ast.log)})'
		else:
			return f'\\log_{self._ast2nat_curly (ast.base)}({self._ast2nat (ast.log)})'

	def _ast2nat_lim (self, ast):
		s = self._ast2nat_wrap (ast.to, (ast.to.is_ass and ast.to.rhs.is_lamb) or ast.to.op in {'-lamb', '-piece'}, ast.to.is_slice) if ast.dir is None else (self._ast2nat_pow (AST ('^', ast.to, AST.Zero), trighpow = False) [:-1] + ast.dir)

		return f'\\lim_{{{self._ast2nat (ast.lvar)} \\to {s}}} {self._ast2nat_curly_mul_exp (ast.lim, False, ast.lim.op in {"=", "<>", "+", "-piece", "-lamb", "-slice", "||", "^^", "&&", "-or", "-and", "-not"} or ast.lim.is_mul_has_abs)}'

	def _ast2nat_sum (self, ast):
		return f'\\sum_{{{self._ast2nat (ast.svar)} = {self._ast2nat_curly (ast.from_, {"-lamb", "-piece"})}}}^{self._ast2nat_curly (ast.to)} {self._ast2nat_curly_mul_exp (ast.sum, False, ast.sum.op in {"=", "<>", "+", "-piece", "-lamb", "-slice", "||", "^^", "&&", "-or", "-and", "-not"} or ast.sum.is_mul_has_abs)}'

	def _ast2nat_diff (self, ast):
		if ast.diff.is_var and not ast.diff.is_diff_or_part:
			top  = self._ast2nat (ast.diff)
			topp = f' {top}'
			side = ''

		else:
			top  = topp = ''
			side = f' {self._ast2nat_paren (ast.diff)}'

		dp  = sum (dv [1] for dv in ast.dvs)
		dv  = (lambda v: AST ('@', f'd{v}')) if ast.is_diff_d else (lambda v: AST ('@', f'partial{v}'))
		dvs = " ".join (self._ast2nat (dv (v) if p == 1 else AST ('^', dv (v), AST ('#', p))) for v, p in ast.dvs)

		return f'{ast.d}{top if dp == 1 else f"**{dp}{topp}"} / {dvs}{side}'

	def _ast2nat_intg (self, ast):
		if ast.intg is None:
			intg  = ' '
		else:
			curly = (ast.intg.op in {"-piece", "-lamb", "-slice", "||", "^^", "&&", "-or", "-and", "-not"} or
				ast.intg.is_mul_has_abs or
				ast.intg.tail_mul.op in {"-lim", "-sum"} or
				(ast.intg.tail_mul.is_var and ast.intg.tail_mul.var in _SYM_USER_FUNCS))
			intg  = self._ast2nat_wrap (ast.intg, curly, {"=", "<>"})
			intg  = f' {{{intg}}} ' if not curly and _ast_has_open_differential (ast.intg, istex = False) else f' {intg} '

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

	def _ast2nat_idx (self, ast):
		obj = self._ast2nat_wrap (ast.obj,
			ast.obj.op in {"^", "-slice"} or ast.obj.is_subs_diff_ufunc or (ast.obj.is_var and ast.obj.var in _SYM_USER_FUNCS),
			ast.obj.is_num_neg or ast.obj.op in {"=", "<>", ",", "+", "*", "/", "-", "-lim", "-sum", "-diff", "-intg", "-piece", "-lamb", "||", "^^", "&&", "-or", "-and", "-not"})
		idx = '[' if ast.idx.len and ast.idx [0].is_var_null else f'[{self._ast2nat (AST.tuple2ast (ast.idx))}]'

		return f'{obj}{idx}'

	def _ast2nat_slice (self, ast):
		b = _ast_slice_bounds (ast)
		s = ':'.join (self._ast2nat_wrap (a, a is not b [-1] and not a.op in {'/', '-diff'} and a.has_tail_lambda_solo, a.op in {'=', ',', '-lamb', '-slice'}) for a in b)

		return self._ast2nat_wrap (s, 0, not ast.start and self.parent.is_comma and ast is self.parent.comma [0] and self.parents [-2].is_ass and self.parent is self.parents [-2].rhs)

	def _ast2nat_dict (self, ast):
		items = []

		for k, v in ast.dict:
			if k.op in {'-lamb', '-slice'}:
				k       = self._ast2nat_paren (k)
			else:
				_, wrap = k.tail_lambda_solo
				k       = self._ast2nat (wrap (AST ('@', '\\lambda')) if wrap else k)

			items.append ((k, self._ast2nat_wrap (v, v.is_lamb, v.is_slice)))

		return f'''{{{", ".join (f'{k}: {v}' for k, v in items)}}}'''

	def _ast2nat_ufunc (self, ast):
		user = _SYM_USER_ALL.get (ast.ufunc)

		if (ast.is_ufunc_explicit or not ast.ufunc or
					(user and
					(not user.is_ufunc or (ast != user and not user.can_apply_argskw ((ast.vars, ast.kw)) if user.vars else (ast.kw and ast.kw != user.kw))) and
					not _ast_is_top_ass_lhs (self, ast)) or
				not ast.vars.as_ufunc_argskw):
			pre = '?'
		else:
			pre = ''

		args = ", ".join (tuple (self._ast2nat (v) for v in ast.vars) + tuple (f"{k} = {self._ast2nat_wrap (a, 0, a.is_comma)}" for k, a in ast.kw))

		return f'{pre}{ast.ufunc}({args})'

	def _ast2nat_subs (self, ast):
		subs, vars = _ast_subs2func (ast)

		if len (subs) == ast.subs.len:
			expr = self._ast2nat (ast.expr)

		else:
			expr = f'{self._ast2nat (ast.expr)}({", ".join (self._ast2nat (v) for v in vars)})'

			if not subs:
				return expr

		if len (subs) == 1:
			subs = self._ast2nat (subs [0])
		else:
			subs = self._ast2nat (AST (',', tuple (subs)))

		return f'\\. {expr} |_{{{subs}}}'

	_ast2nat_funcs = {
		';'     : lambda self, ast: '; '.join (self._ast2nat (a) for a in ast.scolon),
		'='     : lambda self, ast: f'{self._ast2nat_ass_hs (ast.lhs)} = {self._ast2nat_ass_hs (ast.rhs, False)}',
		'<>'    : _ast2nat_cmp,
		'#'     : lambda self, ast: ast.num,
		'@'     : lambda self, ast: '{' if ast.is_var_null and self.parent.op in {None, ';'} else ast.var,
		'.'     : _ast2nat_attr,
		'"'     : _ast2nat_str,
		','     : lambda self, ast: f'{", ".join (self._ast2nat (c) for c in ast.comma)}{_trail_comma (ast.comma)}',
		'('     : lambda self, ast: '(' if ast.paren.is_var_null else f'({self._ast2nat (ast.paren)})',
		'['     : lambda self, ast: '[' if ast.brack.len == 1 and ast.brack [0].is_var_null else f'[{", ".join (self._ast2nat (b) for b in ast.brack)}]',
		'|'     : lambda self, ast: '|' if ast.abs.is_var_null else f'{{|{self._ast2nat (ast.abs)}|}}',
		'-'     : _ast2nat_minus,
		'!'     : lambda self, ast: self._ast2nat_wrap (ast.fact, {'^'}, ast.fact.op not in {'#', '@', '.', '"', '(', '[', '|', '!', '^', '-func', '-mat', '-idx', '-set', '-dict', '-sym'} or ast.fact.is_num_neg) + '!',
		'+'     : _ast2nat_add,
		'*'     : _ast2nat_mul,
		'/'     : _ast2nat_div,
		'^'     : _ast2nat_pow,
		'-log'  : _ast2nat_log,
		'-sqrt' : lambda self, ast: f'sqrt{"" if ast.idx is None else f"[{self._ast2nat (ast.idx)}]"}({self._ast2nat (ast.rad)})',
		'-func' : lambda self, ast: f"{ast.func}{self._ast2nat_wrap (AST.tuple2ast (ast.args), 0, not (ast.func in {AST.Func.NOREMAP, AST.Func.NOEVAL} and ast.args [0].op in {'@', '(', '[', '|', '-func', '-mat', '-set', '-dict'}))}",
		'-lim'  : _ast2nat_lim,
		'-sum'  : _ast2nat_sum,
		'-diff' : _ast2nat_diff,
		'-diffp': lambda self, ast: self._ast2nat_wrap (ast.diffp, ast.diffp.is_subs_diff_any_ufunc, ast.diffp.is_num_neg or ast.diffp.op in {"=", "<>", "-", "+", "*", "/", "^", "-lim", "-sum", "-diff", "-intg", "-piece", "-lamb", "-slice", "||", "^^", "&&", "-or", "-and", "-not"}) + "'" * ast.count,
		'-intg' : _ast2nat_intg,
		'-mat'  : _ast2nat_mat,
		'-piece': lambda self, ast: ' else '.join (f'{self._ast2nat_wrap (p [0], p [0].op in {"=", "-piece", "-lamb"}, {",", "-slice"})}' if p [1] is True else f'{self._ast2nat_wrap (p [0], p [0].op in {"=", "-piece", "-lamb"}, {",", "-slice"})} if {self._ast2nat_wrap (p [1], p [1].op in {"=", "-piece", "-lamb"}, {",", "-slice"})}' for p in ast.piece),
		'-lamb' : lambda self, ast: f'lambda{" " + ", ".join (ast.vars) if ast.vars else ""}: {self._ast2nat_wrap (ast.lamb, ast.lamb.op in {"=", "<>", "-lamb"}, ast.lamb.is_slice)}',
		'-idx'  : _ast2nat_idx,
		'-slice': _ast2nat_slice,
		'-set'  : lambda self, ast: f'{{{", ".join (self._ast2nat_wrap (c, 0, c.is_slice) for c in ast.set)}{_trail_comma (ast.set)}}}' if ast.set else '\\{}',
		'-dict' : _ast2nat_dict,
		'||'    : lambda self, ast: ' || '.join (self._ast2nat_wrap (a, 0, {'=', '<>', ',', '-slice', '-piece', '-lamb', '-or', '-and', '-not'}) for a in ast.union),
		'^^'    : lambda self, ast: ' ^^ '.join (self._ast2nat_wrap (a, 0, {'=', '<>', ',', '-slice', '-piece', '-lamb', '||', '-or', '-and', '-not'}) for a in ast.sdiff),
		'&&'    : lambda self, ast: ' && '.join (self._ast2nat_wrap (a, 0, {'=', '<>', ',', '-slice', '-piece', '-lamb', '||', '^^', '-or', '-and', '-not'}) for a in ast.xsect),
		'-or'   : lambda self, ast: ' or '.join (self._ast2nat_wrap (a, 0, {'=', ',', '-slice', '-piece', '-lamb'}) for a in ast.or_),
		'-and'  : lambda self, ast: ' and '.join (self._ast2nat_wrap (a, 0, {'=', ',', '-slice', '-piece', '-lamb', '-or'}) for a in ast.and_),
		'-not'  : lambda self, ast: f'not {self._ast2nat_wrap (ast.not_, 0, {"=", ",", "-slice", "-piece", "-lamb", "-or", "-and"})}',
		'-ufunc': _ast2nat_ufunc,
		'-subs' : _ast2nat_subs,
		'-sym'  : lambda self, ast: f'${ast.sym}({", ".join (tuple (f"{k} = {self._ast2nat_wrap (a, 0, a.is_comma)}" for k, a in ast.kw))})',

		'-text' : lambda self, ast: ast.nat,
	}

#...............................................................................................
class ast2py: # abstract syntax tree -> Python code text
	def __init__ (self): self.parent = self.ast = None # pylint droppings
	def __new__ (cls, ast, retxlat = False, ass2eq = True):
		self         = super ().__new__ (cls)
		self.ass2eq  = ass2eq
		self.parents = [None]
		self.parent  = self.ast = AST.Null

		astx = sxlat.xlat_funcs2asts (ast, sxlat.XLAT_FUNC2AST_PY)
		astS = sxlat.xlat_pyS (astx) if _PYS else astx # 1/2 -> S(1)/2
		py   = self._ast2py (astS)

		return py if not retxlat else (py, (astx if astx != ast else None))

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
		if ast.is_cmp_in or ast.strip_minus.op in {',', '+', '*', '/'} or ast.strip_minus.is_log_with_base:
			return self._ast2py_paren (ast)
		else:
			return self._ast2py (ast)

	def _ast2py_paren (self, ast, paren = _None):
		if paren is _None:
			return self._ast2py (ast) if ast.is_paren else f'({self._ast2py (ast)})'

		if ((ast.op in paren) if isinstance (paren, set) else paren):
			return f'({self._ast2py (ast)})'

		return self._ast2py (ast)

	def _ast2py_ass (self, ast):
		is_top_ass = self.parent.op in {None, ';'}

		if is_top_ass:
			if ast.ass_validate:
				ast = ast.ass_validate
			else:
				is_top_ass = False

		if is_top_ass or self.parent.is_func: # present assignment with = instead of Eq for keyword argument or at top level?
			return f'{self._ast2py_paren (ast.lhs) if ast.lhs.is_lamb else self._ast2py (ast.lhs)} = {self._ast2py (ast.rhs)}'

		return f'Eq({self._ast2py_paren (ast.lhs, bool (ast.lhs.is_comma))}, {self._ast2py_paren (ast.rhs, bool (ast.rhs.is_comma))}{", 1" if _SYM_MARK_PY_ASS_EQ else ""})' # _SYM_MARK_PY_ASS_EQ for when testing only

	_ast2py_cmpfuncs = {'==': 'Eq', '!=': 'Ne', '<': 'Lt', '<=': 'Le', '>': 'Gt', '>=': 'Ge'}

	def _ast2py_cmp (self, ast):
		def cmppy (lhs, rel, rhs):
			if rel in {'in', 'notin'}:
				return f'{self._ast2py_paren (lhs, lhs.is_cmp_in)} {AST.Cmp.PYFMT.get (rel, rel)} {self._ast2py_paren (rhs, rhs.is_cmp_in)}'
			else:
				return f'{self._ast2py_cmpfuncs [rel]}({self._ast2py_paren (lhs, bool (lhs.is_comma))}, {self._ast2py_paren (rhs, bool (rhs.is_comma))})'

		if ast.cmp.len == 1:
			return cmppy (ast.lhs, *ast.cmp [0])
		else:
			return f'And({cmppy (ast.lhs, *ast.cmp [0])}, {", ".join (cmppy (ast.cmp [i - 1] [1], *ast.cmp [i]) for i in range (1, ast.cmp.len))})'

	def _ast2py_attr (self, ast):
		obj = self._ast2py_paren (ast.obj, ast.obj.is_log_with_base or ast.obj.op in {"=", "<>", "#", ",", "-", "+", "*", "/", "^"})

		if ast.is_attr_func:
			args, kw = AST.args2kwargs (ast.args, self._ast2py, ass2eq = self.ass2eq)

			return f'{obj}.{ast.attr}({", ".join (args + [f"{k} = {a}" for k, a in kw.items ()])})'

		return f'{obj}.{ast.attr}'

	def _ast2py_minus (self, ast):
		s = self._ast2py_paren (ast.minus, ast.minus.is_add or ast.minus.is_cmp_in or (ast.minus.is_idx and ast.minus.obj.is_num) or
				(ast.minus.is_mul and (not self.parent.is_add or ast is self.parent.add [0] or (ast.minus.mul [0].is_idx and ast.minus.mul [0].obj.is_num))))

		return f'-({s})' if s [:1] != '(' and (ast.minus.strip_fdpi.is_num_pos and not self.parent.is_add) else f'-{s}'

	def _ast2py_add (self, ast):
		return ' + '.join (self._ast2py_paren (n, n.is_cmp_in or (n is not ast.add [0] and (n.is_num_neg or (n.is_mul and _ast_is_neg (n.mul [0]))))) for n in ast.add).replace (' + -', ' - ')

	def _ast2py_mul (self, ast):
		return '*'.join (self._ast2py_paren (n, n.is_cmp_in or n.is_add or (n is not ast.mul [0] and (n.is_div or n.is_log_with_base))) for n in ast.mul)

	def _ast2py_div (self, ast):
		nn = _ast_is_neg (ast.numer)
		n  = self._ast2py_paren (ast.numer) if nn else self._ast2py_curly (ast.numer)
		d  = self._ast2py_curly (ast.denom)
		s  = " / " if nn or (ast.numer.strip_minus.op not in {"#", "@"} and not (ast.numer.is_func and ast.numer.func == 'S' and ast.numer.args.len == 1 and ast.numer.args [0].op in {"#", "@"})) or \
			ast.denom.strip_minus.op not in {"#", "@"} or d.lstrip ("-") [:1] == "(" else "/"

		return f'{n}{s}{d}'

	def _ast2py_pow (self, ast):
		# b = self._ast2py_paren (ast.base) if _ast_is_neg (ast.base) or ast.base.is_pow or (ast.base.is_idx and self.parent.is_pow and ast is self.parent.exp) else self._ast2py_curly (ast.base)
		b = self._ast2py_paren (ast.base) if _ast_is_neg (ast.base) or ast.base.is_pow else self._ast2py_curly (ast.base)
		# e = self._ast2py_paren (ast.exp) if ast.exp.strip_minus.is_sqrt_with_base or (ast.base.op in {'|', '-set'} and ast.exp.strip_attrm.is_idx) or (ast.exp.is_attr and ast.exp.strip_attrm.is_idx) else self._ast2py_curly (ast.exp)
		e = self._ast2py_paren (ast.exp) if ast.exp.strip_minus.is_sqrt_with_base else self._ast2py_curly (ast.exp)

		return f'{b}**{e}'

	def _ast2py_log (self, ast):
		if ast.base is None:
			return f'ln({self._ast2py (ast.log)})'
		else:
			return f'ln({self._ast2py (ast.log)}) / ln({self._ast2py (ast.base)})'

	def _ast2py_func (self, ast):
		if ast.func in {AST.Func.NOREMAP, AST.Func.NOEVAL}:
			return self._ast2py (ast.args [0])

		args, kw = AST.args2kwargs (ast.args, self._ast2py, ass2eq = self.ass2eq)

		return f'{ast.func}({", ".join (args + [f"{k} = {a}" for k, a in kw.items ()])})'

	def _ast2py_lim (self, ast):
		return \
				f'''Limit({self._ast2py (ast.lim)}, {self._ast2py (ast.lvar)}, {self._ast2py_paren (ast.to, ast.to.is_comma)}''' \
				f'''{", dir = '+-'" if ast.dir is None else ", dir = '-'" if ast.dir == '-' else ""})'''

	def _ast2py_diff (self, ast):
		args = sum (((self._ast2py (AST ('@', v)),) if p == 1 else (self._ast2py (AST ('@', v)), str (p)) for v, p in ast.dvs), ())

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
		elif ast.is_mat_column and not any (r [0].is_brack for r in ast.mat):
			return f"Matrix([{', '.join (self._ast2py (row [0]) for row in ast.mat)}])"
		else:
			return f"""Matrix([{', '.join (f'[{", ".join (self._ast2py (e) for e in row)}]' for row in ast.mat)}])"""

	def _ast2py_idx (self, ast):
		obj = self._ast2py_paren (ast.obj, ast.obj.is_num_neg or ast.obj.is_log_with_base or ast.obj.is_sqrt_with_base or (ast.obj.is_var and ast.obj.var in _SYM_USER_FUNCS) or
			ast.obj.op in {"=", "<>", ",", "+", "*", "/", "^", "-", "-lim", "-sum", "-diff", "-intg", "-piece"})

		if ast.idx.len and ast.idx [0].is_var_null:
			idx = '['
		elif ast.idx.len == 1 and ast.idx [0].strip_paren.is_slice:
			idx = f'[{self._ast2py (ast.idx [0])}]'
		else:
			idx = f'[{self._ast2py (AST.tuple2ast (ast.idx))}]'

		return f'{obj}{idx}'

	def _ast2py_slice (self, ast):
		if self.parent.is_idx and any (i is ast for i in self.parent.idx) or \
				self.parent.is_comma and len (self.parents) > 1 and self.parents [-2].is_idx and ast in self.parents [-2].idx:
			b = _ast_slice_bounds (ast)

			return ':'.join (self._ast2py_paren (a, a is not b [-1] and a.has_tail_lambda_solo or a.op in {'=', ',', '-slice'}) for a in b)

		args = _ast_slice_bounds (ast, AST.None_, allow1 = True)

		if len (args) == 3 and args [2] is AST.None_:
			args = args [:2]

		return f'slice({", ".join (self._ast2py_paren (a, a.op in {"=", ",", "-slice"}) for a in args)})'

	def _ast2py_sdiff (self, ast):
		sdiff = self._ast2py (ast.sdiff [0])

		for a in ast.sdiff [1:]:
			a     = self._ast2py (a)
			sdiff = f'Union(Complement({sdiff}, {a}), Complement({a}, {sdiff}))'

		return sdiff

	def _ast2py_subs (self, ast):
		def tupletuple (a):
			return self._ast2py (AST ('(', (',', (a,))) if a.strip_paren.is_comma else a)

		if ast.subs.len > 1:
			subs = f'({", ".join (self._ast2py (s) for s, d in ast.subs)}), ({", ".join (self._ast2py (d) for s, d in ast.subs)})'
		else:
			subs = f'{tupletuple (ast.subs [0] [0])}, {tupletuple (ast.subs [0] [1])}'

		return f'Subs({self._ast2py (ast.expr)}, {subs})'

	_ast2py_funcs = {
		';'     : lambda self, ast: '; '.join (self._ast2py (a) for a in ast.scolon),
		'='     : _ast2py_ass,
		'<>'    : _ast2py_cmp,
		'#'     : lambda self, ast: ast.num,
		'@'     : lambda self, ast: '{' if ast.is_var_null and self.parent.op in {None, ';'} else ast.var,
		'.'     : _ast2py_attr,
		'"'     : lambda self, ast: repr (ast.str_),
		','     : lambda self, ast: f'{", ".join (self._ast2py (parm) for parm in ast.comma)}{_trail_comma (ast.comma)}',
		'('     : lambda self, ast: '(' if ast.paren.is_var_null else f'({self._ast2py (ast.paren)})',
		'['     : lambda self, ast: '[' if ast.brack.len == 1 and ast.brack [0].is_var_null else f'[{", ".join (self._ast2py (b) for b in ast.brack)}]',
		'|'     : lambda self, ast: '|' if ast.abs.is_var_null else f'abs({self._ast2py (ast.abs)})',
		'-'     : _ast2py_minus,
		'!'     : lambda self, ast: f'factorial({self._ast2py (ast.fact)})',
		'+'     : _ast2py_add,
		'*'     : _ast2py_mul,
		'/'     : _ast2py_div,
		'^'     : _ast2py_pow,
		'-log'  : _ast2py_log,
		'-sqrt' : lambda self, ast: f'sqrt({self._ast2py (ast.rad)})' if ast.idx is None else self._ast2py (AST ('^', ast.rad.strip_paren1, ('/', AST.One, ast.idx))),
		'-func' : _ast2py_func,
		'-lim'  : _ast2py_lim,
		'-sum'  : lambda self, ast: f'Sum({self._ast2py (ast.sum)}, ({self._ast2py (ast.svar)}, {self._ast2py_paren (ast.from_, ast.from_.is_comma)}, {self._ast2py (ast.to)}))',
		'-diff' : _ast2py_diff,
		'-diffp': lambda self, ast: f'{"diff(" * ast.count}{self._ast2py (ast.diffp)}{")" * ast.count}',
		'-intg' : _ast2py_intg,
		'-mat'  : _ast2py_mat,
		'-piece': lambda self, ast: 'Piecewise(' + ', '.join (f'({self._ast2py (p [0])}, {True if p [1] is True else self._ast2py (p [1])})' for p in ast.piece) + ')',
		'-lamb' : lambda self, ast: f"""Lambda({ast.vars [0] if ast.vars.len == 1 else f'({", ".join (ast.vars)})'}, {self._ast2py (ast.lamb)})""",
		'-idx'  : _ast2py_idx,
		'-slice': _ast2py_slice,
		'-set'  : lambda self, ast: f'FiniteSet({", ".join (self._ast2py (c) for c in ast.set)})',
		'-dict' : lambda self, ast: f'{{{", ".join (f"{self._ast2py_paren (k, k.has_tail_lambda_solo)}: {self._ast2py (v)}" for k, v in ast.dict)}}}',
		'||'    : lambda self, ast: f'Union({", ".join (self._ast2py (a) for a in ast.union)})',
		'^^'    : _ast2py_sdiff,
		'&&'    : lambda self, ast: f'Intersection({", ".join (self._ast2py (a) for a in ast.xsect)})',
		'-or'   : lambda self, ast: f'Or({", ".join (self._ast2py_paren (a, a.is_comma) for a in ast.or_)})',
		'-and'  : lambda self, ast: f'And({", ".join (self._ast2py_paren (a, a.is_comma) for a in ast.and_)})',
		'-not'  : lambda self, ast: f'Not({self._ast2py_paren (ast.not_, ast.not_.is_ass or ast.not_.is_comma)})',
		'-ufunc': lambda self, ast: f'Function({", ".join ((f"{ast.ufunc!r}",) + tuple (f"{k} = {self._ast2py_paren (a, a.is_comma)}" for k, a in ast.kw))})' + (f'({", ".join (self._ast2py (v) for v in ast.vars)})' if ast.vars else ''),
		'-subs' : _ast2py_subs,
		'-sym'  : lambda self, ast: f'Symbol({", ".join ((f"{ast.sym!r}",) + tuple (f"{k} = {self._ast2py_paren (a, a.is_comma)}" for k, a in ast.kw))})',

		'-text' : lambda self, ast: ast.py,
	}

#...............................................................................................
# Potentially bad __builtins__: eval, exec, globals, locals, vars, setattr, delattr, exit, help, input, license, open, quit, __import__
_builtins_dict         = __builtins__ if isinstance (__builtins__, dict) else __builtins__.__dict__
_ast2spt_func_builtins = dict (no for no in filter (lambda no: no [1], ((n, _builtins_dict.get (n)) for n in AST.Func.BUILTINS)))
_ast2spt_pyfuncs       = {**_ast2spt_func_builtins, **sp.__dict__, 'simplify': _simplify}#, 'dsolve': _dsolve}

class ast2spt: # abstract syntax tree -> sympy tree (expression)
	_SYMPY_FLOAT_PRECISION = None

	@staticmethod
	def set_precision (ast): # recurse through ast to set sympy float precision according to longest string of digits found
		prec  = 15
		stack = [ast]

		while stack:
			ast = stack.pop ()

			if not isinstance (ast, AST):
				pass # nop
			elif ast.is_num:
				prec = max (prec, len (ast.num)) # will be a little more than number of digits to compensate for falling precision with some calculations
			else:
				stack.extend (ast if ast.op is None else ast [1:])

		ast2spt._SYMPY_FLOAT_PRECISION = prec if prec > 15 else None

	def __init__ (self): self.parent = self.ast = None # pylint kibble
	def __new__ (cls, ast, retxlat = False):
		self         = super ().__new__ (cls)
		self.parents = [None]
		self.parent  = self.ast = AST.Null

		astx = sxlat.xlat_funcs2asts (ast, sxlat.XLAT_FUNC2AST_SPT)
		spt  = self._ast2spt (astx)

		if _DOIT:
			spt = _doit (spt)

		if _POST_SIMPLIFY:
			spt = _simplify (spt)

		return spt if not retxlat else (spt, (astx if astx != ast else None))

	def _ast2spt (self, ast):
		self.parents.append (self.ast)

		self.parent = self.ast
		self.ast    = ast

		spt         = self._ast2spt_funcs [ast.op] (self, ast)

		del self.parents [-1]

		self.ast    = self.parent
		self.parent = self.parents [-1]

		return spt

	def _ast2spt_ass (self, ast):
		lhs, rhs = self._ast2spt (ast.lhs), self._ast2spt (ast.rhs)

		try:
			return EqAss (lhs, rhs) # try to use SymPy comparison object
		except:
			return lhs == rhs # fall back to Python comparison

	_ast2spt_cmpfuncs = {
		'=='   : (EqCmp, lambda a, b: a == b),
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

		if obj.is_var: # and obj.var not in self.vars: # always support S.Half and the like unless base object redefined by assignment
			spt = getattr (sp, obj.var, None)

		if spt is None:
			spt = self._ast2spt (ast.obj)

		try:
			attr = getattr (spt, ast.attr)

			return attr if ast.is_attr_var else _ast_func_call (attr, ast.args, self._ast2spt)

		except AttributeError as e: # unresolved attributes of expressions with free vars remaining should not raise
			try:
				if not isinstance (spt, NoEval) and not spt.free_symbols:
					raise e

			except:
				raise e from None

		return NoEval (AST ('.', spt2ast (spt), *ast [2:]))

	def _ast2spt_add (self, ast): # specifically try to subtract negated objects (because of sets)
		itr = iter (ast.add)
		res = self._ast2spt (next (itr))

		for arg in itr:
			arg, neg    = arg.strip_minus_retneg
			arg, is_neg = self._ast2spt (arg), neg.is_neg

			try:
				res = res - arg if is_neg else res + arg
			except:
				res = sp.sympify (res) - sp.sympify (arg) if is_neg else sp.sympify (res) + sp.sympify (arg)

		return res

	def _ast2spt_mul (self, ast): # handle dynamic cases of function calls due to usage of implicit multiplication
		mul = list (self._ast2spt (a) for a in ast.mul)
		out = mul [:1]

		for i in range (1, ast.mul.len):
			m = mul [i]

			if ast.mul [i].is_paren and i not in ast.exp: # non-explicit multiplication with tuple - possible function call intended: "y (...)"
				o = out [-1]

				if callable (o): # isinstance (o, sp.Lambda): # Lambda or other callable being called?
					out [-1] = o (*m) if isinstance (m, tuple) else o (m)

					continue

			out.append (mul [i])

		return out [0] if len (out) == 1 else _Mul (*out)

	def _ast2spt_func (self, ast):
		if ast.func == AST.Func.NOREMAP: # special reference meta-function
			return self._ast2spt (ast.args [0])

		if ast.func == AST.Func.NOEVAL: # special no-evaluate meta-function
			if self.parent.is_lamb and ast is self.parent.lamb: # if at top-level in lambda body then lambda handles differnt meaning of this pseudo-func
				return self._ast2spt (ast.args [0])
			else:
				return NoEval (ast.args [0])

		func = _ast2spt_pyfuncs.get (ast.func)

		if func is not None:
			return _ast_func_call (func, ast.args, self._ast2spt)

		if ast.func in _SYM_USER_FUNCS: # user lambda, within other lambda if it got here
			return NoEval (ast)

		raise NameError (f'function {ast.func!r} is not defined')

	def _ast2spt_diff (self, ast):
		args     = sum (((self._ast2spt (AST ('@', v)),) if p == 1 else (self._ast2spt (AST ('@', v)), sp.Integer (p)) for v, p in ast.dvs), ())
		spt      = self._ast2spt (ast.diff)

		return spt.diff (*args) if isinstance (spt, sp_AppliedUndef) else sp.Derivative (spt, *args)

	def _ast2spt_diffp (self, ast):
		spt      = self._ast2spt (ast.diffp)
		is_ufunc = isinstance (spt, sp_AppliedUndef)

		for _ in range (ast.count):
			spt = spt.diff () if is_ufunc else sp.Derivative (spt)

		return spt

	def _ast2spt_intg (self, ast):
		if ast.from_ is None:
			if ast.intg is None:
				return sp.Integral (1, sp.Symbol (ast.dv.var_name))
			else:
				return sp.Integral (self._ast2spt (ast.intg), sp.Symbol (ast.dv.var_name))

		else:
			if ast.intg is None:
				return sp.Integral (1, (sp.Symbol (ast.dv.var_name), self._ast2spt (ast.from_), self._ast2spt (ast.to)))
			else:
				return sp.Integral (self._ast2spt (ast [1]), (sp.Symbol (ast.dv.var_name), self._ast2spt (ast.from_), self._ast2spt (ast.to)))

	def _ast2spt_lamb (self, ast):
		i = self.parent.mul.index (ast) if self.parent.is_mul else None

		if not (self.parent.op in {None, ',', '[', '-func', '-lamb', '-set', '-dict'} or # '(', # treat body of lambda as expression for calculation
				(self.parent.is_ass and ast is self.parent.rhs) or
				(i is not None and i < (self.parent.mul.len - 1) and self.parent.mul [i + 1].is_paren and i not in self.parent.exp)):

			if ast.lamb_vars_notfree:
				vars = dict (va for va in filter (lambda va: va [0] not in ast.lamb_vars_notfree, _SYM_USER_VARS.items ()))
			else:
				vars = _SYM_USER_VARS

			return self._ast2spt (AST.apply_vars (ast.lamb, vars))

		spt = self._ast2spt (ast.lamb)

		if ast.vars.len == 1 and isinstance (spt, sp.Symbol) and not isinstance (spt, sp.Dummy) and spt.name == ast.vars [0]:
			spt = IdLambda (None, sp.Symbol (ast.vars [0]))

		else:
			spt = sp.Lambda (tuple (sp.Symbol (v) for v in ast.vars), spt)

			if not (ast.lamb.is_func and ast.lamb.func == AST.Func.NOEVAL):
				spt.doit = lambda self, *args, **kw: self # disable doit for lambda definition

		return spt

	def _ast2spt_idx (self, ast):
		spt = self._ast2spt (ast.obj)
		idx = self._ast2spt (ast.idx [0]) if len (ast.idx) == 1 else tuple (self._ast2spt (i) for i in ast.idx)

		try:
			return spt [idx]
		except TypeError: # invalid indexing of expressions with free vars remaining should not raise
			if not isinstance (spt, NoEval) and not getattr (spt, 'free_symbols', None) and not hasattr (spt, '__getitem__'):
				raise

		return NoEval (AST ('-idx', spt2ast (spt), ast.idx))

	def _ast2spt_sdiff (self, ast):
		sdiff = self._ast2spt (ast.sdiff [0])

		for a in ast.sdiff [1:]:
			a     = self._ast2spt (a)
			sdiff = sp.Union (sp.Complement (sdiff, a), sp.Complement (a, sdiff))

		return sdiff

	def _ast2spt_ufunc (self, ast):
		spt = sp.Function (ast.ufunc, **{k: _bool_or_None (self._ast2spt (a)) for k, a in ast.kw}) (*(self._ast2spt (v) for v in ast.vars))

		if _ast_is_top_ass_lhs (self, ast): # pass explicit state of ufunc through spt if it is on left side of assign at top level
			spt.is_ufunc_explicit = ast.is_ufunc_explicit

		return spt

	def _ast2spt_subs (self, ast):
		return _subs (self._ast2spt (ast.expr), [(self._ast2spt (s), self._ast2spt (d)) for s, d in ast.subs])

	_ast2spt_funcs = {
		';'     : lambda self, ast: _raise (RuntimeError ('semicolon expression should never get here')),
		'='     : _ast2spt_ass,
		'<>'    : _ast2spt_cmp,
		'#'     : lambda self, ast: sp.Integer (ast.num) if ast.is_num_int else sp.Float (ast.num, ast2spt._SYMPY_FLOAT_PRECISION),
		'@'     : _ast2spt_var,
		'.'     : _ast2spt_attr,
		'"'     : lambda self, ast: ast.str_,
		','     : lambda self, ast: tuple (self._ast2spt (p) for p in ast.comma),
		'{'     : lambda self, ast: self._ast2spt (ast.curly),
		'('     : lambda self, ast: self._ast2spt (ast.paren),
		'['     : lambda self, ast: [self._ast2spt (b) for b in ast.brack],
		'|'     : lambda self, ast: sp.Abs (self._ast2spt (ast.abs)),
		'-'     : lambda self, ast: -self._ast2spt (ast.minus),
		'!'     : lambda self, ast: sp.factorial (self._ast2spt (ast.fact)),
		'+'     : _ast2spt_add,
		'*'     : _ast2spt_mul,
		'/'     : lambda self, ast: _Mul (self._ast2spt (ast.numer), _Pow (self._ast2spt (ast.denom), -1)),
		'^'     : lambda self, ast: _Pow (self._ast2spt (ast.base), self._ast2spt (ast.exp)),
		'-log'  : lambda self, ast: sp.log (self._ast2spt (ast.log)) if ast.base is None else sp.log (self._ast2spt (ast.log), self._ast2spt (ast.base)),
		'-sqrt' : lambda self, ast: _Pow (self._ast2spt (ast.rad), _Pow (sp.S (2), -1)) if ast.idx is None else _Pow (self._ast2spt (ast.rad), _Pow (self._ast2spt (ast.idx), -1)),
		'-func' : _ast2spt_func,
		'-lim'  : lambda self, ast: (sp.Limit if ast.dir else sp.limit) (self._ast2spt (ast.lim), self._ast2spt (ast.lvar), self._ast2spt (ast.to), dir = ast.dir or '+-'),
		'-sum'  : lambda self, ast: sp.Sum (self._ast2spt (ast.sum), (self._ast2spt (ast.svar), self._ast2spt (ast.from_), self._ast2spt (ast.to))),
		'-diff' : _ast2spt_diff,
		'-diffp': _ast2spt_diffp,
		'-intg' : _ast2spt_intg,
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
		'-ufunc': _ast2spt_ufunc,
		'-subs' : _ast2spt_subs,
		'-sym'  : lambda self, ast: sp.Symbol (ast.sym, **{k: _bool_or_None (self._ast2spt (a)) for k, a in ast.kw}),

		'-text' : lambda self, ast: ast.spt,
	}

#...............................................................................................
class spt2ast:
	def __init__ (self): self.parent = self.spt = None # pylint droppings
	def __new__ (cls, spt):
		self         = super ().__new__ (cls)
		self.parents = [None]
		self.parent  = self.spt = None

		return _ast_eqcmp2ass (self._spt2ast (spt))

	def _spt2ast (self, spt): # sympy tree (expression) -> abstract syntax tree
		def __spt2ast (spt):
			for cls in spt.__class__.__mro__:
				func = spt2ast._spt2ast_funcs.get (cls)

				if func:
					return func (self, spt)

			tex  = sp.latex (spt)
			text = str (spt)

			if tex == text: # no native latex representation?
				tex = tex.replace ('_', '\\_')

			if tex [0] == '<' and tex [-1] == '>': # for Python repr style of objects <class something> TODO: Move this to Javascript.
				tex = '\\text{' + tex.replace ("<", "&lt;").replace (">", "&gt;").replace ("\n", "") + '}'

			return AST ('-text', tex, text, text, spt)

		self.parents.append (self.spt)

		self.parent = self.spt
		self.spt    = spt

		spt         = __spt2ast (spt)

		del self.parents [-1]

		self.spt    = self.parent
		self.parent = self.parents [-1]

		return spt

	def _spt2ast_num (self, spt):
		s = str (spt)

		if s [:3] == '0.e' or s [:4] == '-0.e':
			return AST ('#', '0')

		num = AST ('#', s)

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
		terms = []
		hasO  = False

		for arg in spt.args: # spt._sorted_args: #
			ast  = self._spt2ast (arg)
			hasO = hasO or isinstance (arg, sp.Order)

			if ast.is_num_neg:
				ast = AST ('-', ast.neg ())
			elif ast.is_mul and _ast_is_neg (ast.mul [0]):
				ast = AST ('-', ('*', (ast.mul [0].neg (),) + ast.mul [1:]))

			terms.append (ast)

		if not hasO: # try to order so negative is not first, but not extensively where it might change standard equation forms returned from SymPy
			if spt.args [0].is_number and (not _ast_is_neg (terms [1]) or _ast_is_neg (terms [0])): # spt.args [0] < 0):
				terms = terms [1:] + [terms [0]]
			elif len (terms) == 2 and _ast_is_neg (terms [0]) and not _ast_is_neg (terms [1]):
				terms = terms [::-1]

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
		neg = False

		for arg in args: # absorb products into rational
			if isinstance (arg, sp.Pow) and arg.args [1].is_negative:
				denom.append (self._spt2ast (arg.args [0] if arg.args [1] is sp.S.NegativeOne else _Pow (arg.args [0], -arg.args [1])))
			elif not isinstance (arg, sp.Rational) or arg.q == 1:
				numer.append (self._spt2ast (arg))

			else:
				denom.append (self._spt2ast (arg.q))

				p = arg.p

				if p < 0:
					neg = not neg
					p   = -p

				if p != 1:
					numer.append (self._spt2ast (p))

		neg = (lambda ast: AST ('-', ast)) if neg else (lambda ast: ast)

		if not denom:
			return neg (AST ('*', tuple (numer)) if len (numer) > 1 else numer [0])

		if not numer:
			return neg (AST ('/', AST.One, AST ('*', tuple (denom)) if len (denom) > 1 else denom [0]))

		if _MUL_RATIONAL and len (denom) == 1 and denom [0].is_num: # leading rational enabled?
			if numer [0].is_num:
				return neg (AST ('*', (('/', numer [0], denom [0]), AST ('*', tuple (numer [1:])) if len (numer) > 2 else numer [1])))
			else:
				return neg (AST ('*', (('/', AST.One, denom [0]), AST ('*', tuple (numer)) if len (numer) > 1 else numer [0])))

		return neg (AST ('/', AST ('*', tuple (numer)) if len (numer) > 1 else numer [0], AST ('*', tuple (denom)) if len (denom) > 1 else denom [0]))

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
			syms = _free_symbols (spt.args [0])

			if len (syms) == 1 and spt.args [1] [0] == syms.pop ():
				return AST ('-diffp', self._spt2ast (spt.args [0]), int (spt.args [1] [1]))

		return AST ('-diff', self._spt2ast (spt.args [0]), 'd', tuple ((s.name, int (p)) for s, p in spt.args [1:]))

	def _spt2ast_Integral (self, spt):
		if len (spt.args [1]) == 3:
			return AST ('-intg', self._spt2ast (spt.args [0]), AST ('@', f'd{self._spt2ast (spt.args [1] [0]) [1]}'), self._spt2ast (spt.args [1] [1]), self._spt2ast (spt.args [1] [2]))
		else:
			return AST ('-intg', self._spt2ast (spt.args [0]), AST ('@', f'd{self._spt2ast (spt.args [1] [0]) [1]}'))

	def _spt2ast_Function (self, spt, name = None, args = None, kw = None):
		if name is None:
			name = spt.__class__.__name__

		if args is None:
			args = spt.args

		if kw:
			return AST ('-func', name, tuple (self._spt2ast (arg) for arg in spt.args) + tuple (AST ('=', ('@', kw), a) for kw, a in kw))
		else:
			return AST ('-func', name, tuple (self._spt2ast (arg) for arg in spt.args))

	def _spt2ast_AppliedUndef (self, spt):
		if spt.__class__.__name__ == 'slice': # special cased converted slice object with start, stop and step present, this is REALLY unnecessary...
			return AST ('-slice', *tuple (self._spt2ast (s) for s in spt.args))

		# if getattr (spt, 'is_explicit', False) or \
		# 		(isinstance (self.parent, EqAss) and self.parents [-2] is None and spt is self.parent.args [0]) or \
		# 		(isinstance (self.parent, sp.Tuple) and isinstance (self.parents [-2], EqAss) and self.parents [-3] is None and spt in self.parent):
		# 	name = f'?{spt.name}'
		# else:
		# 	name = spt.name

		name = f'?{spt.name}' if getattr (spt, 'is_ufunc_explicit', False) else spt.name

		return AST ('-ufunc', name, tuple (self._spt2ast (a) for a in spt.args), tuple (sorted ((k, self._spt2ast (a)) for k, a in spt._extra_kwargs.items ()))) # i._explicit_class_assumptions.items ()))

	_dict_keys   = {}.keys ().__class__
	_dict_values = {}.values ().__class__
	_dict_items  = {}.items ().__class__

	_spt2ast_Limit_dirs = {'+': ('+',), '-': ('-',), '+-': ()}

	_spt2ast_funcs = {
		NoEval: lambda self, spt: spt.ast,

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

		sp.Symbol: lambda self, spt: AST ('@', spt.name) if spt.name and spt == sp.Symbol (spt.name) else AST ('-sym', spt.name, tuple ((k, self._spt2ast (v)) for k, v in sorted (spt._assumptions._generator.items ()))),

		sp.boolalg.BooleanTrue: lambda self, spt: AST.True_,
		sp.boolalg.BooleanFalse: lambda self, spt: AST.False_,
		sp.Or: lambda self, spt: AST ('-or', tuple (self._spt2ast (a) for a in spt.args)),
		sp.And: lambda self, spt: (lambda args: sxlat._xlat_f2a_And (*args, canon = True) or AST ('-and', args)) (tuple (self._spt2ast (a) for a in spt.args)), # collapse possibly previously segmented extended comparison
		sp.Not: lambda self, spt: AST ('-not', self._spt2ast (spt.args [0])),

		EqAss: lambda self, spt: AST ('=', self._spt2ast (spt.args [0]), self._spt2ast (spt.args [1])),
		EqCmp: lambda self, spt: AST ('<>', self._spt2ast (spt.args [0]), (('==', self._spt2ast (spt.args [1])),), is_cmp_explicit = True),
		sp.Eq: lambda self, spt: AST ('<>', self._spt2ast (spt.args [0]), (('==', self._spt2ast (spt.args [1])),)),
		sp.Ne: lambda self, spt: AST ('<>', self._spt2ast (spt.args [0]), (('!=', self._spt2ast (spt.args [1])),)),
		sp.Lt: lambda self, spt: AST ('<>', self._spt2ast (spt.args [0]), (('<',  self._spt2ast (spt.args [1])),)),
		sp.Le: lambda self, spt: AST ('<>', self._spt2ast (spt.args [0]), (('<=', self._spt2ast (spt.args [1])),)),
		sp.Gt: lambda self, spt: AST ('<>', self._spt2ast (spt.args [0]), (('>',  self._spt2ast (spt.args [1])),)),
		sp.Ge: lambda self, spt: AST ('<>', self._spt2ast (spt.args [0]), (('>=', self._spt2ast (spt.args [1])),)),

		sp.EmptySet: lambda self, spt: AST.SetEmpty,
		sp.fancysets.Complexes: lambda self, spt: AST.Complexes,
		sp.fancysets.Reals: lambda self, spt: AST.Reals,
		sp.fancysets.Integers: lambda self, spt: AST.Integers,
		sp.fancysets.Naturals: lambda self, spt: AST.Naturals,
		sp.fancysets.Naturals0: lambda self, spt: AST.Naturals0,
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
		sp.Subs: lambda self, spt: AST ('-subs', self._spt2ast (spt.args [0]), tuple ((self._spt2ast (s), self._spt2ast (d)) for s, d in zip (spt.args [1], spt.args [2]))),

		sp.Function: _spt2ast_Function,
		sp_AppliedUndef: _spt2ast_AppliedUndef,
	}

#...............................................................................................
def set_sym_user_funcs (user_funcs):
	global _SYM_USER_FUNCS, _SYM_USER_ALL
	_SYM_USER_FUNCS = user_funcs
	_SYM_USER_ALL   = {**_SYM_USER_VARS, **{f: _SYM_USER_VARS.get (f, AST.VarNull) for f in _SYM_USER_FUNCS}}

def set_sym_user_vars (user_vars):
	global _SYM_USER_VARS, _SYM_USER_ALL
	_SYM_USER_VARS = user_vars
	_SYM_USER_ALL   = {**_SYM_USER_VARS, **{f: _SYM_USER_VARS.get (f, AST.VarNull) for f in _SYM_USER_FUNCS}}

def set_pyS (state):
	global _PYS
	_PYS = state

def set_simplify (state):
	global _POST_SIMPLIFY
	_POST_SIMPLIFY = state

def set_doit (state):
	global _DOIT
	_DOIT = state

def set_prodrat (state):
	global _MUL_RATIONAL
	_MUL_RATIONAL = state

def set_strict (state):
	global _STRICT_TEX
	_STRICT_TEX = state

class sym: # for single script
	set_sym_user_funcs = set_sym_user_funcs
	set_sym_user_vars  = set_sym_user_vars
	set_pyS            = set_pyS
	set_simplify       = set_simplify
	set_doit           = set_doit
	set_prodrat        = set_prodrat
	set_strict         = set_strict
	ast2tex            = ast2tex
	ast2nat            = ast2nat
	ast2py             = ast2py
	ast2spt            = ast2spt
	spt2ast            = spt2ast

# AUTO_REMOVE_IN_SINGLE_SCRIPT_BLOCK_START
if __name__ == '__main__': # DEBUG!
	vars = {'f': AST ('-lamb', ('^', ('@', 'x'), ('#', '2')), ('x',))}
	set_sym_user_funcs (set (vars))
	set_sym_user_vars (vars)

	set_strict (True)

	ast = AST ('-lamb', ('@', 'y'), ('y',))
	res = ast2tex (ast)
	# res = ast2nat (ast)
	# res = ast2py (ast)

	# res = ast2spt (ast)
	# res = spt2ast (res)
	# res = ast2nat (res)


	print (repr (res))
