import re

FUNCS_PY = list (reversed (sorted ('''
	abs
	expand
	factor
	factorial
	simplify
	'''.replace (',', ' ').strip ().split ())))

FUNCS_PY_AND_TEX = list (reversed (sorted ('''
	arg
	ln
	'''.replace (',', ' ').strip ().split ())))

rec_var_diff_start = re.compile (r'^d(?=[^_])')
rec_var_part_start = re.compile (r'^\\partial ')
rec_var_not_single = re.compile (r'^(?:d.|\\partial |.+_)')

def is_var_differential (ast):
	return ast [0] == '@' and rec_var_diff_start.match (ast [1])

def is_var_partial (ast):
	return ast [0] == '@' and rec_var_part_start.match (ast [1])

def is_single_unit (ast): # is single positive digit or single non-differential non-subscripted variable?
	if ast [0] == '#':
		return isinstance (ast [1], int) and 0 <= ast [1] <= 9
	elif ast [0] == '@':
		return not rec_var_not_single.match (ast [1])

	return False

def is_neg (ast):
	return \
			ast [0] == '-' or \
			ast [0] == '#' and ast [1] < 0 or \
			ast [0] == '*' and is_neg (ast [1])

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
