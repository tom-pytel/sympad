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

rec_num_int        = re.compile (r'^-?\d+$')
rec_num_pos_int    = re.compile (r'^\d+$')
rec_var_diff_start = re.compile (r'^d(?=[^_])')
rec_var_part_start = re.compile (r'^\\partial ')
rec_var_not_single = re.compile (r'^(?:d.|\\partial |.+_)')
rec_trigh          = re.compile (r'^a?(?:sin|cos|tan|csc|sec|cot)h?$')
rec_trigh_noninv   = re.compile (r'^(?:sin|cos|tan|csc|sec|cot)h?$')

def is_int_text (text): # >= 0
	return rec_num_pos_int.match (text)

def is_pos_num (ast): # >= 0
	return ast [0] == '#' and ast [1] [0] != '-'

def is_neg_num (ast): # < 0
	return ast [0] == '#' and ast [1] [0] == '-'

def is_pos_int (ast): # >= 0
	return ast [0] == '#' and rec_num_pos_int.match (ast [1])

def is_neg (ast):
	return \
			ast [0] == '-' or \
			ast [0] == '#' and ast [1] [0] == '-' or \
			ast [0] == '*' and is_neg (ast [1])

def is_differential_var (ast):
	return ast [0] == '@' and rec_var_diff_start.match (ast [1])

def is_partial_var (ast):
	return ast [0] == '@' and rec_var_part_start.match (ast [1])

def is_single_unit (ast): # is single positive digit or single non-differential non-subscripted variable?
	if ast [0] == '#':
		return len (ast [1]) == 1

	return ast [0] == '@' and not rec_var_not_single.match (ast [1])

def is_trigh (ast):
	return ast [0] == 'func' and rec_trigh.match (ast [1])

def is_trigh_noninv (ast):
	return ast [0] == 'func' and rec_trigh_noninv.match (ast [1])

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



	# def is_trigh (self):
	# 	return self [0] == 'func' and rec_trigh.match (self [1])

	# def is_trigh_noninv (self):
	# 	return self [0] == 'func' and rec_trigh_noninv.match (self [1])

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

		self     = tuple.__new__ (cls, args)
		self.op  = op
		self.cls = cls

		if op:
			self._init (*cls_args)

		return self

	def __getattr__ (self, name): # calculate value for self.name* calling self._name ()
		func                 = getattr (self, f'_{name}') if name [0] != '_' else None
		val                  = func and func ()
		self.__dict__ [name] = val

		return val

	def _is_neg (self):
		return \
				self.op == '-' or \
				self.op == '#' and self.num == '-' or \
				self.op == '*' and self.args [0].is_neg

	def _is_single_unit (self): # is single positive digit or single non-differential non-subscripted variable?
		if self.op == '#':
			return len (self.num) == 1

		return self.op == '@' and not rec_var_not_single.match (self.name)

	def strip_paren (self):
		while self.op == '(':
			self = self.arg

		return self

	@staticmethod
	def is_int_text (text): # >= 0
		return rec_num_pos_int.match (text)

	@staticmethod # TODO: new args system
	def flatcat (op, ast0, ast1): # ,,,/O.o\,,,~~
		if ast0 [0] == op:
			if ast1 [0] == op:
				return ast0 + ast1 [1:]
			return ast0 + (ast1,)
		elif ast1 [0] == op:
			return ast (op, ast0) + ast1 [1:]
		return ast (op, ast0, ast1)

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
		return rec_num_pos_int.match (self.num)

class ast_var (ast):
	def _init (self, name):
		self.name = name

	def _is_differential_var (self):
		return rec_var_diff_start.match (self.name)

	def _is_partial_var (self):
		return rec_var_part_start.match (self.name)

class ast_paren (ast):
	def _init (self, arg):
		self.arg = arg

class ast_abs (ast):
	def _init (self, arg):
		self.arg = arg

class ast_neg (ast):
	def _init (self, arg):
		self.arg = arg

class ast_fact (ast):
	def _init (self, arg):
		self.arg = arg

class ast_add (ast):
	def _init (self, args):
		self.args = args

class ast_mul (ast):
	def _init (self, args):
		self.args = args

class ast_div (ast):
	def _init (self, numer, denom):
		self.numer = numer
		self.denom = denom

class ast_pow (ast):
	def _init (self, base, exp):
		self.base = base
		self.exp  = exp

class ast_log (ast):
	def _init (self, arg, base = None):
		self.arg  = arg
		self.base = base

class ast_sqrt (ast):
	def _init (self, rad, idx = None):
		self.rad = rad
		self.idx = idx

class ast_func (ast):
	def _init (self, name, arg):
		self.name = name
		self.arg  = arg

class ast_lim (ast):
	def _init (self, expr, var, to, dir = None):
		self.expr = expr
		self.var  = var
		self.to   = to
		self.dir  = dir

class ast_sum (ast):
	def _init (self, expr, var, from_, to):
		self.expr  = expr
		self.var   = var
		self.from_ = from_
		self.to    = to

class ast_diff (ast):
	def _init (self, expr, vars):
		self.expr = expr
		self.vars = vars

class ast_intg (ast):
	def _init (self, var, expr = None, from_ = None, to = None):
		self.var   = var
		self.expr  = expr
		self.from_ = from_
		self.to    = to

_AST_OP2CLS = {
	'#': ast_num,
	'@': ast_var,
	'(': ast_paren,
	'|': ast_abs,
	'-': ast_neg,
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
	setattr (ast, cls.__name__.split ('_') [1], cls)
