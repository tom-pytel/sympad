import re

# ('#', 'num')                  - numbers represented as strings to pass on maximum precision to sympy
# ('@', 'var')                  - variable name, can take forms: 'x', "x'", 'dx', '\partial x', 'x_2', '\partial x_{y_2}', "d\alpha_{x_{\beta''}'}'''"
# ('(', expr)                   - explicit parentheses
# ('|', expr)                   - absolute value
# ('-', expr)                   - negative of expression, negative numbers are represented with this at least initially
# ('!', expr)                   - factorial
# ('+', (expr1, expr2, ...))    - addition
# ('*', (expr1, expr2, ...))    - multiplication
# ('/', numer, denom)           - fraction numer(ator) / denom(inator)
# ('^', base, exp)              - power base ^ exp(onent)
# ('log', expr)                 - natural logarithm of expr
# ('log', expr, base)           - logarithm of expr in base
# ('sqrt', expr)                - square root of expr
# ('sqrt', expr, n)             - nth root of expr
# ('func', 'func', expr)        - sympy or regular python function 'func', will be called with sympy expression
# ('lim', expr, var, to)        - limit of expr when variable var approaches to from both positive and negative directions
# ('lim', expr, var, to, dir)   - limit of expr when variable var approaches to from direction dir which may be '+' or '-'
# ('sum', expr, var, from, to)  - summation of expr over variable var from from to to
# ('diff', expr, (var1, ...))   - differentiation of expr with respect to var1 and optional other vars
# ('intg', None, var)           - anti-derivative of 1 with respect to differential var ('dx', 'dy', etc ...)
# ('intg', expr, var)           - anti-derivative of expr with respect to differential var ('dx', 'dy', etc ...)
# ('intg', None, var, from, to) - definite integral of 1 with respect to differential var ('dx', 'dy', etc ...)
# ('intg', expr, var, from, to) - definite integral of expr with respect to differential var ('dx', 'dy', etc ...)

_rec_num_int                = re.compile (r'^-?\d+$')
_rec_num_pos_int            = re.compile (r'^\d+$')
_rec_var_diff_start         = re.compile (r'^d(?=[^_])')
_rec_var_part_start         = re.compile (r'^\\partial ')
_rec_var_not_single         = re.compile (r'^(?:d.|\\partial |.+_)')
_rec_func_trigh             = re.compile (r'^a?(?:sin|cos|tan|csc|sec|cot)h?$')
_rec_func_trigh_noninv_func = re.compile (r'^(?:sin|cos|tan|csc|sec|cot)h?$')

class AST (tuple):
	FUNCS_PY = list (reversed (sorted ('''
		abs
		expand
		factor
		factorial
		simplify
		'''.strip ().split ())))

	FUNCS_PY_AND_TEX = list (reversed (sorted ('''
		arg
		exp
		ln
		'''.strip ().split ())))

	def __new__ (cls, *args):
		op       = _AST_CLS2OP.get (cls)
		cls_args = tuple (AST (*arg) if arg.__class__ is tuple else arg for arg in args)

		if op:
			args = (op,) + cls_args

		elif args:
			args = cls_args
			cls2 = _AST_OP2CLS.get (args [0])

			if cls2:
				op       = args [0]
				cls      = cls2
				cls_args = cls_args [1:]

		self    = tuple.__new__ (cls, args)
		self.op = op

		if op:
			self._init (*cls_args)

		return self

	def __getattr__ (self, name): # calculate value for nonexistent self.name by calling self._name ()
		func                 = getattr (self, f'_{name}') if name [0] != '_' else None
		val                  = func and func ()
		self.__dict__ [name] = val

		return val

	def _is_neg (self):
		return \
				self.op == '-' or \
				self.op == '#' and self.num == '-' or \
				self.op == '*' and self.muls [0].is_neg

	def _is_single_unit (self): # is single positive digit or single non-differential non-subscripted variable?
		if self.op == '#':
			return len (self.num) == 1

		return self.op == '@' and not _rec_var_not_single.match (self.var)

	def neg (self, stack = False): # stack means stack negatives ('-', ('-', ('#', '-1')))
		if stack:
			return \
					AST ('-', self)            if not self.is_pos_num else \
					AST ('#', f'-{self.num}')

		else:
			return \
					self.minus                 if self.is_minus else \
					AST ('-', self)            if not self.is_num else \
					AST ('#', self.num [1:])   if self.num [0] == '-' else \
					AST ('#', f'-{self.num}')

	def strip_paren (self, count = None):
		count = 999999999 if count is None else count

		while self.op == '(' and count:
			self   = self.paren
			count -= 1

		return self

	@staticmethod
	def is_int_text (text): # >= 0
		return _rec_num_int.match (text)

	@staticmethod
	def flatcat (op, ast0, ast1): # ,,,/O.o\,,,~~
		if ast0.op == op:
			if ast1.op == op:
				return AST (op, ast0 [-1] + ast1 [-1])
			return AST (op, ast0 [-1] + (ast1,))
		elif ast1.op == op:
			return AST (op, (ast0,) + ast1 [-1])
		return AST (op, (ast0, ast1))

class AST_Num (AST):
	def _init (self, num):
		self.num = num

	def _is_num (self):
		return True

	def _is_pos_num (self):
		return self.num [0] != '-'

	def _is_neg_num (self):
		return self.num [0] == '-'

	def _is_pos_int (self):
		return _rec_num_pos_int.match (self.num)

class AST_Var (AST):
	def _init (self, var):
		self.var = var

	def _is_var (self):
		return True

	def _is_null_var (self):
		return not self.var

	def _is_diff_var (self):
		return _rec_var_diff_start.match (self.var)

	def _is_part_var (self):
		return _rec_var_part_start.match (self.var)

class AST_Paren (AST):
	def _init (self, paren):
		self.paren = paren

	def _is_paren (self):
		return True

class AST_Abs (AST):
	def _init (self, abs):
		self.abs = abs

	def _is_abs (self):
		return True

class AST_Minus (AST):
	def _init (self, minus):
		self.minus = minus

	def _is_minus (self):
		return True

class AST_Fact (AST):
	def _init (self, fact):
		self.fact = fact

	def _is_fact (self):
		return True

class AST_Add (AST):
	def _init (self, adds):
		self.adds = adds

	def _is_add (self):
		return True

class AST_Mul (AST):
	def _init (self, muls):
		self.muls = muls

	def _is_mul (self):
		return True

class AST_Div (AST):
	def _init (self, numer, denom):
		self.numer = numer
		self.denom = denom

	def _is_div (self):
		return True

class AST_Pow (AST):
	def _init (self, base, exp):
		self.base = base
		self.exp  = exp

	def _is_pow (self):
		return True

class AST_Log (AST):
	def _init (self, log, base = None):
		self.log  = log
		self.base = base

	def _is_log (self):
		return True

class AST_Sqrt (AST):
	def _init (self, rad, idx = None):
		self.rad = rad
		self.idx = idx

	def _is_sqrt (self):
		return True

class AST_Func (AST):
	def _init (self, func, arg):
		self.func = func
		self.arg  = arg

	def _is_func (self):
		return True

	def _is_trigh_func (self):
		return _rec_func_trigh.match (self.func)

	def _is_trigh_func_noninv_func (self):
		return _rec_func_trigh_noninv_func.match (self.func)

class AST_Lim (AST):
	def _init (self, lim, var, to, dir = None):
		self.lim = lim
		self.var = var
		self.to  = to
		self.dir = dir

	def _is_lim (self):
		return True

class AST_Sum (AST):
	def _init (self, sum, var, from_, to):
		self.sum   = sum
		self.var   = var
		self.from_ = from_
		self.to    = to

	def _is_sum (self):
		return True

class AST_Diff (AST):
	def _init (self, diff, vars):
		self.diff = diff
		self.vars = vars

	def _is_diff (self):
		return True

class AST_Intg (AST):
	def _init (self, intg, var, from_ = None, to = None):
		self.intg  = intg
		self.var   = var
		self.from_ = from_
		self.to    = to

	def _is_intg (self):
		return True

_AST_OP2CLS = {
	'#': AST_Num,
	'@': AST_Var,
	'(': AST_Paren,
	'|': AST_Abs,
	'-': AST_Minus,
	'!': AST_Fact,
	'+': AST_Add,
	'*': AST_Mul,
	'/': AST_Div,
	'^': AST_Pow,
	'log': AST_Log,
	'sqrt': AST_Sqrt,
	'func': AST_Func,
	'lim': AST_Lim,
	'sum': AST_Sum,
	'diff': AST_Diff,
	'intg': AST_Intg,
}

_AST_CLS2OP = dict ((b, a) for (a, b) in _AST_OP2CLS.items ())

for cls in _AST_CLS2OP:
	setattr (AST, cls.__name__ [4:], cls)

AST.Zero   = AST ('#', '0')
AST.One    = AST ('#', '1')
AST.NegOne = AST ('#', '-1')
AST.I      = AST ('@', 'i')
AST.E      = AST ('@', 'e')
AST.Pi     = AST ('@', '\\pi')
AST.Infty  = AST ('@', '\\infty')
