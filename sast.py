import re

FUNCS_PY = list (reversed (sorted ('''
	abs
	expand
	factor
	factorial
	simplify
	'''.strip ().split ())))

FUNCS_PY_AND_TEX = list (reversed (sorted ('''
	arg
	ln
	'''.strip ().split ())))

_rec_num_int        = re.compile (r'^-?\d+$')
_rec_num_pos_int    = re.compile (r'^\d+$')
_rec_var_diff_start = re.compile (r'^d(?=[^_])')
_rec_var_part_start = re.compile (r'^\\partial ')
_rec_var_not_single = re.compile (r'^(?:d.|\\partial |.+_)')
_rec_trigh          = re.compile (r'^a?(?:sin|cos|tan|csc|sec|cot)h?$')
_rec_trigh_noninv   = re.compile (r'^(?:sin|cos|tan|csc|sec|cot)h?$')

def is_int_text (text): # >= 0
	return _rec_num_pos_int.match (text)

def is_pos_num (ast): # >= 0
	return ast [0] == '#' and ast [1] [0] != '-'

def is_neg_num (ast): # < 0
	return ast [0] == '#' and ast [1] [0] == '-'

def is_pos_int (ast): # >= 0
	return ast [0] == '#' and _rec_num_pos_int.match (ast [1])

def is_neg (ast):
	return \
			ast [0] == '-' or \
			ast [0] == '#' and ast [1] [0] == '-' or \
			ast [0] == '*' and is_neg (ast [1])

def is_differential_var (ast):
	return ast [0] == '@' and _rec_var_diff_start.match (ast [1])

def is_partial_var (ast):
	return ast [0] == '@' and _rec_var_part_start.match (ast [1])

def is_single_unit (ast): # is single positive digit or single non-differential non-subscripted variable?
	if ast [0] == '#':
		return len (ast [1]) == 1

	return ast [0] == '@' and not _rec_var_not_single.match (ast [1])

def is_trigh (ast):
	return ast [0] == 'func' and _rec_trigh.match (ast [1])

def is_trigh_noninv (ast):
	return ast [0] == 'func' and _rec_trigh_noninv.match (ast [1])

def strip_paren (ast):
	return ast [1] if ast [0] == '(' else ast

def flatcat (op, ast0, ast1): # ,,,/O.o\,,,~~
	if ast0 [0] == op:
		if ast1 [0] == op:
			return ast0 + ast1 [1:]
		return ast0 + (ast1,)
	elif ast1 [0] == op:
		return (op, ast0) + ast1 [1:]
	return (op, ast0, ast1)

#...............................................................................................
class ast (tuple):
	def __new__ (cls, *args):
		op       = _AST_CLS2OP.get (cls)
		cls_args = tuple (ast (*arg) if arg.__class__ is tuple else arg for arg in args)

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

	def neg (self, stack = False): # stack means stack negatives ('-', ('-', ('#', '-1')))
		if stack:
			return \
					ast ('-', self)            if not self.is_pos_num else \
					ast ('#', f'-{self.num}')

		else:
			return \
					self.minus                 if self.is_minus else \
					ast ('-', self)            if not self.is_num else \
					ast ('#', self.num [1:])   if self.num [0] == '-' else \
					ast ('#', f'-{self.num}')

	def _is_single_unit (self): # is single positive digit or single non-differential non-subscripted variable?
		if self.op == '#':
			return len (self.num) == 1

		return self.op == '@' and not _rec_var_not_single.match (self.var)

	def strip_paren (self):
		while self.op == '(':
			self = self.arg

		return self

	@staticmethod
	def is_int_text (text): # >= 0
		return _rec_num_int.match (text)

	@staticmethod
	def flatcat (op, ast0, ast1): # ,,,/O.o\,,,~~
		if ast0.op == op:
			if ast1.op == op:
				return ast (op, ast0 [-1] + ast1 [-1])
			return ast (op, ast0 [-1] + (ast1,))
		elif ast1.op == op:
			return ast (op, (ast0,) + ast1 [-1])
		return ast (op, (ast0, ast1))

class ast_num (ast):
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

class ast_var (ast):
	def _init (self, var):
		self.var = var

	def _is_var (self):
		return True

	def _is_null_var (self):
		return not self.var

	def _is_differential_var (self):
		return _rec_var_diff_start.match (self.var)

	def _is_partial_var (self):
		return _rec_var_part_start.match (self.var)

class ast_paren (ast):
	def _init (self, paren):
		self.paren = paren

	def _is_paren (self):
		return True

class ast_abs (ast):
	def _init (self, abs):
		self.abs = abs

	def _is_abs (self):
		return True

class ast_minus (ast):
	def _init (self, minus):
		self.minus = minus

	def _is_minus (self):
		return True

class ast_fact (ast):
	def _init (self, fact):
		self.fact = fact

	def _is_fact (self):
		return True

class ast_add (ast):
	def _init (self, adds):
		self.adds = adds

	def _is_add (self):
		return True

class ast_mul (ast):
	def _init (self, muls):
		self.muls = muls

	def _is_mul (self):
		return True

class ast_div (ast):
	def _init (self, numer, denom):
		self.numer = numer
		self.denom = denom

	def _is_div (self):
		return True

class ast_pow (ast):
	def _init (self, base, exp):
		self.base = base
		self.exp  = exp

	def _is_pow (self):
		return True

class ast_log (ast):
	def _init (self, log, base = None):
		self.log  = log
		self.base = base

	def _is_log (self):
		return True

class ast_sqrt (ast):
	def _init (self, rad, idx = None):
		self.rad = rad
		self.idx = idx

	def _is_sqrt (self):
		return True

class ast_func (ast):
	def _init (self, func, arg):
		self.func = func
		self.arg  = arg

	def _is_func (self):
		return True

	def _is_trigh (self):
		return _rec_trigh.match (self.func)

	def _is_trigh_noninv (self):
		return _rec_trigh_noninv.match (self.func)

class ast_lim (ast):
	def _init (self, lim, var, to, dir = None):
		self.lim = lim
		self.var = var
		self.to  = to
		self.dir = dir

	def _is_lim (self):
		return True

class ast_sum (ast):
	def _init (self, sum, var, from_, to):
		self.sum   = sum
		self.var   = var
		self.from_ = from_
		self.to    = to

	def _is_sum (self):
		return True

class ast_diff (ast):
	def _init (self, diff, vars):
		self.diff = diff
		self.vars = vars

	def _is_diff (self):
		return True

class ast_intg (ast):
	def _init (self, intg, var, from_ = None, to = None):
		self.intg  = intg
		self.var   = var
		self.from_ = from_
		self.to    = to

	def _is_intg (self):
		return True

_AST_OP2CLS = {
	'#': ast_num,
	'@': ast_var,
	'(': ast_paren,
	'|': ast_abs,
	'-': ast_minus,
	'!': ast_fact,
	'+': ast_add,
	'*': ast_mul,
	'/': ast_div,
	'^': ast_pow,
	'log': ast_log,
	'sqrt': ast_sqrt,
	'func': ast_func,
	'lim': ast_lim,
	'sum': ast_sum,
	'diff': ast_diff,
	'intg': ast_intg,
}

_AST_CLS2OP = dict ((b, a) for (a, b) in _AST_OP2CLS.items ())

for cls in _AST_CLS2OP:
	setattr (ast, cls.__name__ [4:], cls)

ast.Zero   = ast ('#', '0')
ast.One    = ast ('#', '1')
ast.NegOne = ast ('#', '-1')
ast.I      = ast ('@', 'i')
ast.E      = ast ('@', 'e')
ast.Pi     = ast ('@', '\\pi')
ast.Infty  = ast ('@', '\\infty')
