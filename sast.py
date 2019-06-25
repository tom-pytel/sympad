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
		return tuple.__new__ (cls, args)

	def __add__ (self, other):
		return ast (*(tuple (self) + tuple (other)))

	def __radd__ (self, other):
		return ast (*(tuple (other) + tuple (self)))

	def __getitem__ (self, idx):
		return ast (*tuple.__getitem__ (self, idx)) if isinstance (idx, slice) else tuple.__getitem__ (self, idx)

	def is_num (self):
		return self [0] == '#'

	def is_pos_num (self): # >= 0
		return self [0] == '#' and self [1] [0] != '-'

	def is_neg_num (self): # < 0
		return self [0] == '#' and self [1] [0] == '-'

	def is_pos_int (self): # >= 0
		return self [0] == '#' and rec_num_pos_int.match (self [1])

	def is_neg (self):
		return \
				self [0] == '-' or \
				self [0] == '#' and self [1] [0] == '-' or \
				self [0] == '*' and is_neg (self [1])

	def is_differential_var (self):
		return self [0] == '@' and rec_var_diff_start.match (self [1])

	def is_partial_var (self):
		return self [0] == '@' and rec_var_part_start.match (self [1])

	def is_single_unit (self): # is single positive digit or single non-differential non-subscripted variable?
		if self [0] == '#':
			return len (self [1]) == 1

		return self [0] == '@' and not rec_var_not_single.match (self [1])

	def strip_paren (self):
		return self [1] if self [0] == '(' else self

	@staticmethod
	def is_int_text (text): # >= 0
		return rec_num_pos_int.match (text)

	@staticmethod
	def flatcat (op, ast0, ast1): # ,,,/O.o\,,,~~
		if ast0 [0] == op:
			if ast1 [0] == op:
				return ast0 + ast1 [1:]
			return ast0 + (ast1,)
		elif ast1 [0] == op:
			return ast (op, ast0) + ast1 [1:]
		return ast (op, ast0, ast1)
