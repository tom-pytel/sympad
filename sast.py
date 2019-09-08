# Base classes for abstract math syntax tree, tuple based.
#
# ('=', 'rel', lhs, rhs)                           - equality of type 'rel' relating Left-Hand-Side and Right-Hand-Side
# ('#', 'num')                                     - real numbers represented as strings to pass on maximum precision to sympy
# ('@', 'var')                                     - variable name, can take forms: 'x', "x'", 'dx', '\partial x', 'something'
# ('.', expr, 'name')                              - data member reference
# ('.', expr, 'name', (a1, a2, ...))               - method member call
# ('"', 'str')                                     - string
# (',', (expr1, expr2, ...))                       - comma expression (tuple)
# ('{', expr)                                      - invisible implicit parentheses for grouping and isolation during parsing
# ('(', expr)                                      - explicit parentheses (not tuple)
# ('[', (expr1, expr2, ...))                       - brackets (list, not index)
# ('|', expr)                                      - absolute value
# ('-', expr)                                      - negative of expression, negative numbers are represented with this at least initially
# ('!', expr)                                      - factorial
# ('+', (expr1, expr2, ...))                       - addition
# ('*', (expr1, expr2, ...))                       - multiplication
# ('/', numer, denom)                              - fraction numer(ator) / denom(inator)
# ('^', base, exp)                                 - power base ^ exp(onent)
# ('log', expr)                                    - natural logarithm of expr
# ('log', expr, base)                              - logarithm of expr in base
# ('sqrt', expr)                                   - square root of expr
# ('sqrt', expr, n)                                - nth root of expr
# ('func', 'name', (a1, a2, ...))                  - sympy or regular Python function 'name', will be called with expressions a1, a2, ...
# ('lim', expr, var, to)                           - limit of expr when variable var approaches to from both positive and negative directions
# ('lim', expr, var, to, 'dir')                    - limit of expr when variable var approaches to from specified direction dir which may be '+' or '-'
# ('sum', expr, var, from, to)                     - summation of expr over variable var from from to to
# ('diff', expr, (var1, ...))                      - differentiation of expr with respect to var1 and optional other vars
# ('intg', expr, var)                              - anti-derivative of expr (or 1 if expr is None) with respect to differential var ('dx', 'dy', etc ...)
# ('intg', expr, var, from, to)                    - definite integral of expr (or 1 if expr is None) with respect to differential var ('dx', 'dy', etc ...)
# ('vec', (e1, e2, ...))                           - vector
# ('mat', ((e11, e12, ...), (e21, e22, ...), ...)) - matrix
# ('piece', ((v1, c1), ..., (vn, True?)))          - piecewise expression: v = AST, c = condition AST, last condition may be True to catch all other cases
# ('lamb', expr, (v1, v2, ...))                    - lambda expression: v? = ('@', 'var')
# ('idx', expr, (i0, i1, ...))                     - indexing: expr [i0, i1, ...]
# ('slice', start, stop, step)                     - indexing slice object: obj [start : stop : step], None or False indicates not specified
# ('set', (expr1, expr2, ...))                     - set
# ('dict', ((k1, v1), (k2, v2), ...))              - python dict
# ('||', (expr1, expr2, ...))                      - set union
# ('^^', (expr1, expr2, ...))                      - set symmetric difference
# ('&&', (expr1, expr2, ...))                      - set intersection
# ('or', (expr1, expr2, ...))                      - Python or
# ('and', (expr1, expr2, ...))                     - Python and
# ('not', expr)                                    - Python not

import re
import types

import sympy as sp

#...............................................................................................
class AST (tuple):
	op      = None

	OPS     = set () # these will be filled in after all classes defined
	CONSTS  = set ()

	_OP2CLS = {}
	_CLS2OP = {}

	_rec_identifier = re.compile (r'^[a-zA-Z_]\w*$')
	_rec_int        = re.compile (r'^-?\d+$')

	def __new__ (cls, *args):
		op       = AST._CLS2OP.get (cls)
		cls_args = tuple (AST (*arg) if arg.__class__ is tuple else arg for arg in args)

		if op:
			args = (op,) + cls_args

		elif args:
			args = cls_args

			try:
				cls2 = AST._OP2CLS.get (args [0])
			except TypeError: # for unhashable types
				cls2 = None

			if cls2:
				cls      = cls2
				cls_args = cls_args [1:]

		self = tuple.__new__ (cls, args)

		if self.op:
			self._init (*cls_args)

		return self

	def __getattr__ (self, name): # calculate value for nonexistent self.name by calling self._name () and store
		func                 = getattr (self, f'_{name}') if name [0] != '_' else None
		val                  = func and func ()
		self.__dict__ [name] = val

		return val

	def _is_single_unit (self): # is single positive digit, fraction or single non-differential non-subscripted non-primed variable?
		if self.op == '/':
			return True
		elif self.op == '#':
			return len (self.num) == 1
		else:
			return self.is_single_var

	def _len (self):
		return len (self)

	def _no_curlys (self):
		if self.is_curly:
			return self.curly.no_curlys
		else:
			return AST (*tuple (a.no_curlys if isinstance (a, AST) else a for a in self))

	def flat (self, op = None, seq = None): # flatten trees of '+', '*', '||', '^^', '&&', 'or' and 'and' into single ASTs
		if self.op in {'+', '*', '||', '^^', '&&', 'or', 'and'}:
			if self.op == op:
				for e in self [1]:
					e.flat (op, seq)

				return

			seq2 = []

			for e in self [1]:
				e.flat (self.op, seq2)

			ast = AST (self.op, tuple (seq2))

		else:
			ast = AST (*tuple (a.flat () if isinstance (a, AST) else a for a in self))

		if op:
			seq.append (ast)
		else:
			return ast

	def neg (self, stack = False): # stack means stack negatives ('-', ('-', ('#', '-1')))
		if stack:
			if not self.is_pos_num:
				return AST ('-', self)
			else:
				return AST ('#', f'-{self.num}')

		else:
			if self.is_minus:
				return self.minus
			elif not self.is_num:
				return AST ('-', self)
			elif self.num [0] == '-':
				return AST ('#', self.num [1:])
			else:
				return AST ('#', f'-{self.num}')

	def strip (self, count = None, ops = {'{', '('}, idx = 1, keeptuple = False):
		count = -1 if count is None else count

		while count and self.op in ops and not (keeptuple and self [idx].is_comma):
			self   = self [idx]
			count -= 1

		return self

	strip_attr   = lambda self, count = None: self.strip (count, ('.',))
	strip_curlys = lambda self, count = None: self.strip (count, ('{',))
	strip_paren  = lambda self, count = None, keeptuple = False: self.strip (count, ('(',), keeptuple = keeptuple)

	def strip_minus (self, count = None, retneg = False):
		count       = -1 if count is None else count
		neg         = lambda ast: ast
		neg.has_neg = False
		neg.is_neg  = False

		while self.is_minus and count:
			self         = self.minus
			count       -= 1
			is_neg       = neg.is_neg
			neg          = lambda ast, neg = neg: neg (ast.neg (stack = True))
			neg.has_neg  = True
			neg.is_neg   = not is_neg

		return (self, neg) if retneg else self

	def strip_mls (self, count = None): # mls = mul, lim, sum
		count = -1 if count is None else count

		while self.op in {'*', 'lim', 'sum'} and count:
			self   = self.mul [-1] if self.is_mul else self [1]
			count -= 1

		return self

	def as_identifier (self, top = True):
		if self.op in {'#', '@', '"'}:
			name = self [1]
		elif not self.is_mul:
			return None

		else:
			try:
				name = ''.join (m.as_identifier () for m in self.mul)
			except TypeError:
				return None

		return name if AST._rec_identifier.match (name) else None

	def free_vars (self): # return set of unique unbound variables found in tree
		def _free_vars (ast, vars):
			if isinstance (ast, AST):
				if ast.is_const_var is False and ast.var:
					vars.add (ast)

				for e in ast:
					_free_vars (e, vars)

		vars = set ()

		_free_vars (self, vars)

		return vars

	@staticmethod
	def tuple2ast (args, paren = False):
		return args [0] if len (args) == 1 else AST ('(', (',', args)) if paren else AST (',', args)

	@staticmethod
	def args2kwargs (args, func = None):
		func  = (lambda x: x) if func is None else func
		rargs = []
		kw    = {}
		itr   = reversed (args)

		for arg in itr:
			if arg.is_ass:
				ident = arg.lhs.as_identifier ()

				if ident is not None:
					kw [ident] = func (arg.rhs)

					continue

			rargs = [func (arg)] + [func (arg) for arg in itr]

		return rargs [::-1], kw

	@staticmethod
	def is_int_text (text):
		return AST._rec_int.match (text)

	@staticmethod
	def flatcat (op, ast0, ast1): # ,,,/O.o\,,,~~
		if ast0.op == op:
			if ast1.op == op:
				return AST (op, ast0 [-1] + ast1 [-1])
			else:
				return AST (op, ast0 [-1] + (ast1,))

		else: # ast0.op != op
			if ast1.op == op:
				return AST (op, (ast0,) + ast1 [-1])
			else:
				return AST (op, (ast0, ast1))

	@staticmethod
	def register_AST (cls):
		AST._CLS2OP [cls]    = cls.op
		AST._OP2CLS [cls.op] = cls

		AST.OPS.add (cls.op)

		setattr (AST, cls.__name__ [4:], cls)

	@staticmethod
	def EI (state = True):
		AST.CONSTS.difference_update ((AST.E, AST.I))

		AST.E, AST.I = (AST ('@', 'E'), AST ('@', 'I')) if state else (AST ('@', 'e'), AST ('@', 'i'))

		AST.CONSTS.update ((AST.E, AST.I))

#...............................................................................................
class AST_Eq (AST):
	op, is_eq  = '=', True

	TEX2PY = {'\\ne': '!=', '\\le': '<=', '\\ge': '>=', '\\lt': '<', '\\gt': '>', '\\neq': '!=', '\\in': 'in', '\\notin': 'notin'}
	UNI2PY = {'\u2260': '!=', '\u2264': '<=', '\u2265': '>=', '\u2208': 'in', '\u2209': 'notin'}
	ANY2PY = {**UNI2PY, **TEX2PY}
	PY2TEX = {'!=': '\\ne', '<=': '\\le', '>=': '\\ge', 'in': '\\in', 'notin': '\\notin'}
	PYFMT  = {'notin': 'not in'}

	def _init (self, rel, lhs, rhs):
		self.rel, self.lhs, self.rhs = rel, lhs, rhs # should be py form

	_is_ass = lambda self: self.rel == '='

class AST_Num (AST):
	op, is_num = '#', True

	_rec_num   = re.compile (r'^(-?)(\d*[^0.e])?(0*)(?:(\.)(0*)(\d*[^0e])?(0*))?(?:([eE])([+-]?)(\d+))?$') # -101000.000101000e+123 -> (-) (101) (000) (.) (000) (101) (000) (e) (+) (123)

	def _init (self, num):
		self.num = num

	_grp              = lambda self: [g or '' for g in AST_Num._rec_num.match (self.num).groups ()]
	_is_pos_num       = lambda self: not self.grp [0]
	_is_neg_num       = lambda self: bool (self.grp [0])
	_is_int_num       = lambda self: not self.grp [3] and not self.grp [7] # self.num_exp_val >= -len (self.grp [2])
	_is_pos_int_num   = lambda self: self.is_int_num and not self.is_neg_num
	_num_exp          = lambda self: self.grp [8] + self.grp [9]
	_num_mant_and_exp = lambda self: (''.join (self.grp [:7]), self.num_exp)
	_num_exp_val      = lambda self: int (self.num_exp) if self.num_exp else 0
	_as_int           = lambda self: int (self.num)

class AST_Var (AST):
	op, is_var  = '@', True

	GREEK       = ('alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta', 'eta', 'theta', 'iota', 'kappa', 'lambda', 'mu', 'nu', 'xi', 'pi', 'rho', 'sigma',
		'tau', 'upsilon', 'phi', 'chi', 'psi', 'omega', 'Gamma', 'Delta', 'Theta', 'Lambda', 'Xi', 'Pi', 'Sigma', 'Upsilon', 'Phi', 'Psi', 'Omega')
	GREEKUNI    = ('\u03b1', '\u03b2', '\u03b3', '\u03b4', '\u03b5', '\u03b6', '\u03b7', '\u03b8', '\u03b9', '\u03ba', '\u03bb', '\u03bc', '\u03bd', '\u03be', '\u03c0', '\u03c1', '\u03c3',
		'\u03c4', '\u03c5', '\u03c6', '\u03c7', '\u03c8', '\u03c9', '\u0393', '\u0394', '\u0398', '\u039b', '\u039e', '\u03a0', '\u03a3', '\u03a5', '\u03a6', '\u03a8', '\u03a9')

	PY2TEXMULTI = {
		'partial'  : ('\\partial',),
		'oo'       : ('\\infty',),
		'zoo'      : ('\\widetilde\\infty', '\\tilde\\infty', '\\overline\\infty', '\\bar\\infty'),
		'Reals'    : ('\\mathbb{R}',),
		'Complexes': ('\\mathbb{C}',),
		'Naturals' : ('\\mathbb{N}', '\\mathbb{N}^*', '\\mathbb{N}^+', '\\mathbb{N}_1', '\\mathbb{N}_{>0}', '\\mathbb{Z}^+'),
		'Naturals0': ('\\mathbb{N}_0', '\\mathbb{N}^0', '\\mathbb{Z}^{\\ge0}'),
		'Integers' : ('\\mathbb{Z}',),
	}

	PY2TEX      = {**dict ((g, f'\\{g}') for g in GREEK), **dict ((p, ts [0]) for p, ts in PY2TEXMULTI.items ())}
	TEX2PY      = {**dict ((f'\\{g}', g) for g in GREEK), **dict ((t, p) for p, ts in PY2TEXMULTI.items () for t in ts)}
	UNI2PY      = {**dict (zip (GREEKUNI, GREEK)), '\u2202': 'partial', '\u221e': 'oo'}
	ANY2PY      = {**UNI2PY, **TEX2PY}

	_rec_groups = re.compile (r"^(?:(?:(d(?!elta|partial))|(partial))(?!['\d]))?(.*)$")

	def _init (self, var):
		self.var = var

		if AST._rec_identifier.match (var):
			self.__dict__ [f'is_var_{var}'] = True

	_grp                  = lambda self: [g or '' for g in AST_Var._rec_groups.match (self.var).groups ()]
	_is_null_var          = lambda self: not self.var
	_is_long_var          = lambda self: len (self.var) > 1 and self.var not in AST_Var.PY2TEX
	_is_const_var         = lambda self: self in AST.CONSTS
	_is_nonconst_var      = lambda self: self not in AST.CONSTS
	_is_differential      = lambda self: self.grp [0] and self.grp [2]
	_is_diff_solo         = lambda self: self.grp [0] and not self.grp [2]
	_is_diff_any          = lambda self: self.grp [0]
	_is_partial           = lambda self: self.grp [1] and self.grp [2]
	_is_part_solo         = lambda self: self.grp [1] and not self.grp [2]
	_is_part_any          = lambda self: self.grp [1]
	_is_diff_or_part      = lambda self: (self.grp [0] or self.grp [1]) and self.grp [2]
	_is_diff_or_part_solo = lambda self: (self.grp [0] or self.grp [1]) and not self.grp [2]
	_is_diff_or_part_any  = lambda self: self.grp [0] or self.grp [1]
	_diff_or_part_type    = lambda self: self.grp [0] or self.grp [1] or '' # 'dx' -> 'd', 'partialx' -> 'partial', else ''
	_is_single_var        = lambda self: len (self.var) == 1 or self.var in AST_Var.PY2TEX # is single atomic variable (non-differential, non-subscripted, non-primed)?
	_as_var               = lambda self: AST ('@', self.grp [2]) if self.var else self # 'x', dx', 'partialx' -> 'x'
	_as_diff              = lambda self: AST ('@', f'd{self.grp [2]}') if self.var else self # 'x', 'dx', 'partialx' -> 'dx'

class AST_Attr (AST):
	op, is_attr = '.', True

	def _init (self, obj, attr, args = None):
		self.obj, self.attr, self.args = obj, attr, args

class AST_Str (AST):
	op, is_str = '"', True

	def _init (self, str_):
		self.str_ = str_

class AST_Comma (AST):
	op, is_comma = ',', True

	def _init (self, comma):
		self.comma = comma

	_is_empty_comma = lambda self: not (len (self.comma))

class AST_Curly (AST):
	op, is_curly = '{', True

	def _init (self, curly):
		self.curly = curly

class AST_Paren (AST):
	op, is_paren = '(', True

	def _init (self, paren):
		self.paren = paren

class AST_Brack (AST):
	op, is_brack = '[', True

	def _init (self, brack):
		self.brack = brack

class AST_Abs (AST):
	op, is_abs = '|', True

	def _init (self, abs):
		self.abs = abs

class AST_Minus (AST):
	op, is_minus = '-', True

	def _init (self, minus):
		self.minus = minus

class AST_Fact (AST):
	op, is_fact = '!', True

	def _init (self, fact):
		self.fact = fact

class AST_Add (AST):
	op, is_add = '+', True

	def _init (self, add):
		self.add = add

class AST_Mul (AST):
	op, is_mul = '*', True

	def _init (self, mul):
		self.mul = mul

	def _is_mul_has_abs (self):
		for m in self.mul:
			if m.is_abs:
				return True

class AST_Div (AST):
	op, is_div = '/', True

	def _init (self, numer, denom):
		self.numer, self.denom = numer, denom

class AST_Pow (AST):
	op, is_pow = '^', True

	def _init (self, base, exp):
		self.base, self.exp = base, exp

class AST_Log (AST):
	op, is_log = 'log', True

	def _init (self, log, base = None):
		self.log, self.base = log, base

class AST_Sqrt (AST):
	op, is_sqrt = 'sqrt', True

	def _init (self, rad, idx = None):
		self.rad, self.idx = rad, idx

class AST_Func (AST):
	op, is_func = 'func', True

	_SYMPY_OBJECTS  = dict ((name, obj) for name, obj in filter (lambda no: no [0] [0] != '_', sp.__dict__.items ()))
	_SYMPY_FUNCS    = set (no [0] for no in filter (lambda no: len (no [0]) > 1 and callable (no [1]), _SYMPY_OBJECTS.items ()))

	ESCAPE          = '$'
	NOREMAP         = '@'
	NOEVAL          = '%'

	ADMIN           = {'vars', 'funcs', 'del', 'delall', 'env', 'envreset', 'plotf', 'plotv', 'plotw'}
	PSEUDO          = {NOREMAP, NOEVAL}
	BUILTINS        = {'max', 'min', 'abs', 'pow', 'set', 'sum', 'slice'}
	TEXNATIVE       = {'max', 'min', 'arg', 'deg', 'exp', 'gcd', 'Re', 'Im'}
	TRIGH           = {'sin', 'cos', 'tan', 'cot', 'sec', 'csc', 'sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch'}

	PY_TRIGHINV     = {f'a{f}' for f in TRIGH}
	TEX_TRIGHINV    = {f'arc{f}' for f in TRIGH}
	TEX2PY_TRIGHINV = {f'arc{f}': f'a{f}' for f in TRIGH}

	PY              = ADMIN | BUILTINS | PY_TRIGHINV | TRIGH | _SYMPY_FUNCS - {'sqrt', 'log', 'ln', 'evaluate', 'beta', 'gamma', 'zeta', 'Lambda'}
	TEX             = TEXNATIVE | TEX_TRIGHINV | (TRIGH - {'sech', 'csch'})

	_rec_trigh        = re.compile (r'^a?(?:sin|cos|tan|csc|sec|cot)h?$')
	_rec_trigh_inv    = re.compile (r'^a(?:sin|cos|tan|csc|sec|cot)h?$')
	_rec_trigh_noninv = re.compile (r'^(?:sin|cos|tan|csc|sec|cot)h?$')

	def _init (self, func, args):
		self.func, self.args = func, args

		if AST._rec_identifier.match (func):
			self.__dict__ [f'is_func_{func}'] = True

	_is_trigh_func        = lambda self: AST_Func._rec_trigh.match (self.func)
	_is_trigh_func_inv    = lambda self: AST_Func._rec_trigh_inv.match (self.func)
	_is_trigh_func_noninv = lambda self: AST_Func._rec_trigh_noninv.match (self.func)
	_is_escaped           = lambda self: self.func [:1] == self.ESCAPE
	_unescaped            = lambda self: self.func.lstrip (self.ESCAPE)

class AST_Lim (AST):
	op, is_lim = 'lim', True

	def _init (self, lim, lvar, to, dir = None):
		self.lim, self.lvar, self.to, self.dir = lim, lvar, to, dir

class AST_Sum (AST):
	op, is_sum = 'sum', True

	def _init (self, sum, svar, from_, to):
		self.sum, self.svar, self.from_, self.to = sum, svar, from_, to

class AST_Diff (AST):
	op, is_diff = 'diff', True

	def _init (self, diff, dvs):
		self.diff, self.dvs = diff, dvs

	_diff_type = lambda self: '' if not self.dvs else self.dvs [0].diff_or_part_type if self.dvs [0].is_var else self.dvs [0].base.diff_or_part_type

class AST_Intg (AST):
	op, is_intg = 'intg', True

	def _init (self, intg, dv, from_ = None, to = None):
		self.intg, self.dv, self.from_, self.to = intg, dv, from_, to

class AST_Vec (AST):
	op, is_vec = 'vec', True

	def _init (self, vec):
		self.vec = vec

class AST_Mat (AST):
	op, is_mat = 'mat', True

	def _init (self, mat):
		self.mat = mat

	_rows = lambda self: len (self.mat)
	_cols = lambda self: len (self.mat [0]) if self.mat else 0

class AST_Piece (AST):
	op, is_piece = 'piece', True

	def _init (self, piece):
		self.piece = piece

class AST_Lamb (AST):
	op, is_lamb = 'lamb', True

	def _init (self, lamb, vars):
		self.lamb, self.vars = lamb, vars

class AST_Idx (AST):
	op, is_idx = 'idx', True

	def _init (self, obj, idx):
		self.obj, self.idx = obj, idx

class AST_Slice (AST):
	op, is_slice = 'slice', True

	def _init (self, start, stop, step):
		self.start, self.stop, self.step = start, stop, step

class AST_Set (AST):
	op, is_set = 'set', True

	def _init (self, set):
		self.set = set

class AST_Dict (AST):
	op, is_dict = 'dict', True

	def _init (self, dict):
		self.dict = dict

class AST_Union (AST):
	op, is_union = '||', True

	def _init (self, union):
		self.union = union

class AST_Sdiff (AST): # symmetric difference
	op, is_sdiff = '^^', True

	def _init (self, sdiff):
		self.sdiff = sdiff

class AST_Xsect (AST): # intersection
	op, is_xsect = '&&', True

	def _init (self, xsect):
		self.xsect = xsect

class AST_Or (AST):
	op, is_or = 'or', True

	def _init (self, or_):
		self.or_ = or_

class AST_And (AST):
	op, is_and = 'and', True

	def _init (self, and_):
		self.and_ = and_

class AST_Not (AST):
	op, is_not = 'not', True

	def _init (self, not_):
		self.not_ = not_

#...............................................................................................
_AST_CLASSES = [AST_Eq, AST_Num, AST_Var, AST_Attr, AST_Str, AST_Comma, AST_Curly, AST_Paren, AST_Brack,
	AST_Abs, AST_Minus, AST_Fact, AST_Add, AST_Mul, AST_Div, AST_Pow, AST_Log, AST_Sqrt, AST_Func, AST_Lim, AST_Sum,
	AST_Diff, AST_Intg, AST_Vec, AST_Mat, AST_Piece, AST_Lamb, AST_Idx, AST_Slice, AST_Set, AST_Dict,
	AST_Union, AST_Sdiff, AST_Xsect, AST_Or, AST_And, AST_Not]

for _cls in _AST_CLASSES:
	AST.register_AST (_cls)

_AST_CONSTS = (('E', 'e'), ('I', 'i'), ('Pi', 'pi'), ('Infty', 'oo'), ('CInfty', 'zoo'), ('None_', 'None'), ('True_', 'True'), ('False_', 'False'), ('NaN', 'nan'),
	('Naturals', 'Naturals'), ('Naturals0', 'Naturals0'), ('Integers', 'Integers'), ('Reals', 'Reals'), ('Complexes', 'Complexes'))

for _vp, _vv in _AST_CONSTS:
	ast = AST ('@', _vv)

	AST.CONSTS.add (ast)
	setattr (AST, _vp, ast)

AST.Zero       = AST ('#', '0')
AST.One        = AST ('#', '1')
AST.NegOne     = AST ('#', '-1')
AST.VarNull    = AST ('@', '')
AST.CommaEmpty = AST (',', ())
AST.MatEmpty   = AST ('mat', ())
AST.SetEmpty   = AST ('set', ())
AST.DictEmpty  = AST ('dict', ())

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: # DEBUG!
# 	ast = AST ('*', (('*', (('@', 'x'), ('@', 'd'))), ('@', 'y')))
# 	res = ast.flat ()
# 	print (res)
