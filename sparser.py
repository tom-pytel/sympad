# Builds expression tree from text, nodes are nested AST tuples.
#
# Time and interest permitting:
# sets
# var assumptions
# importing modules to allow custom code execution
# Proper implementation of vectors with "<b>\vec{x}</b>" and "<b>\hat{i}</b>" variables
# systems of equations, ODEs, graphical plots (using matplotlib?)...

import ast as py_ast
from collections import OrderedDict
import os
import re
import sys

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

def _FUNC_name (FUNC):
	return AST.Func.TEX2PY_TRIGHINV.get (FUNC.grp [1], FUNC.grp [1]) if FUNC.grp [1] else \
			FUNC.grp [0] or FUNC.grp [2] or FUNC.grp [3].replace ('\\', '') or FUNC.text

def _ast_from_tok_digit_or_var (tok, i = 0):
	return AST ('#', tok.grp [i]) if tok.grp [i] else \
			AST ('@', AST.Var.ANY2PY.get (tok.grp [i + 2].replace (' ', ''), tok.grp [i + 1]) if tok.grp [i + 2] else tok.grp [i + 1])

def _ast_func_tuple_args (ast):
	ast = ast.strip (1)

	return ast.comma if ast.is_comma else (ast,)

def _ast_func_reorder (ast):
	wrap2 = None

	if ast.is_fact:
		ast2, wrap2 = ast.fact, lambda a: AST ('!', a)
	elif ast.is_pow:
		ast2, wrap2 = ast.base, lambda a: AST ('^', a, ast.exp)
	elif ast.is_attr:
		ast2, wrap2 = ast.obj, lambda a: AST ('.', a, *ast [2:])

	if wrap2:
		ast3, wrap3 = _ast_func_reorder (ast2)

		if ast3.is_paren or ast3.is_brack:
			return ast3, lambda a: wrap2 (wrap3 (a))

	return ast, lambda a: a

def _ast_pre_slice (pre, post):
	if not post.is_slice:
		return AST ('slice', pre, post, None)
	elif post.step is None:
		return AST ('slice', pre, post.start, post.stop)

	raise SyntaxError ('invalid slice')

#...............................................................................................
def _expr_comma (lhs, rhs):
	if not rhs.is_slice or rhs.step is not None or not rhs.stop or not rhs.start or not rhs.start.is_var:
		return AST.flatcat (',', lhs, rhs)

	if lhs.is_mul:
		if lhs.mul.len == 2 and lhs.mul [0].is_var_lambda and lhs.mul [1].is_var:
			return AST ('lamb', rhs.stop, (lhs.mul [1], rhs.start))

	elif lhs.is_comma:
		for i in range (lhs.comma.len - 1, -1, -1):
			if lhs.comma [i].is_mul and lhs.comma [i].mul.len == 2 and lhs.comma [i].mul [0].is_var_lambda and lhs.comma [i].mul [1].is_var:
				if i:
					return AST (',', lhs.comma [:i] + (('lamb', rhs.stop, (lhs.comma [i].mul [1], *lhs.comma [i + 1:], rhs.start)),))
				else:
					return AST ('lamb', rhs.stop, (lhs.comma [0].mul [1], *lhs.comma [1:], rhs.start))

			if not lhs.comma [i].is_var:
				break

	return AST.flatcat (',', lhs, rhs)

def _expr_colon (lhs, rhs):
	if lhs.is_ass:
		l, wrap_ass = lhs.rhs, lambda rhs, lhs = lhs.lhs: AST ('=', '=', lhs, rhs)
	else:
		l, wrap_ass = lhs, lambda rhs: rhs

	if l.is_var:
		if l.is_var_lambda:
			return wrap_ass (AST ('lamb', rhs, ()))

	elif l.is_mul:
		if l.mul.len == 2 and l.mul [0].is_var_lambda and l.mul [1].is_var:
			return wrap_ass (AST ('lamb', rhs, (l.mul [1],)))

	return _ast_pre_slice (lhs, rhs)

def _expr_mapsto (args, lamb):
	if args.is_var:
		return AST ('lamb', lamb, (args,))

	elif args.is_comma:
		for var in args.comma:
			if not var.is_var:
				break
		else:
			return AST ('lamb', lamb, args.comma)

	raise SyntaxError ('invalid lambda function')

def _expr_piece (expr, expr_if, expr_else):
	if expr_else.is_piece:
		return AST ('piece', ((expr, expr_if),) + expr_else.piece)
	else:
		return AST ('piece', ((expr, expr_if), (expr_else, True)))

def _expr_mul_imp (lhs, rhs, user_funcs = {}):
	last      = lhs.mul [-1] if lhs.is_mul else lhs
	arg, wrap = _ast_func_reorder (rhs)
	ast       = None

	if last.is_attr: # {x.y} *imp* () -> x.y(), x.{y.z} -> {x.y}.z
		if last.args is None:
			if arg.is_paren:
				ast = wrap (AST ('.', last.obj, last.attr, _ast_func_tuple_args (arg)))
			elif rhs.is_attr:
				ast = AST ('.', _expr_mul_imp (last, rhs.obj), rhs.attr)

	elif last.is_pow: # {x^y.z} *imp* () -> x^{y.z()}
		if last.exp.is_attr and last.exp.args is None:
			if arg.is_paren:
				ast = AST ('^', last.base, wrap (AST ('.', last.exp.obj, last.exp.attr, _ast_func_tuple_args (arg))))
			elif rhs.is_attr:
				ast = AST ('^', last.base, ('.', _expr_mul_imp (last.exp, rhs.obj), rhs.attr))

	elif last.is_var: # user_func *imp* () -> user_func ()
		if last.var in user_funcs:
			if arg.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg)))
			else:
				ast = wrap (AST ('func', last.var, (arg,)))

	if arg.is_brack: # x * [y] -> x [y]
		if not arg.brack:
			raise SyntaxError ('missing index')

		ast = wrap (AST ('idx', last, arg.brack))

	if ast:
		return AST ('*', lhs.mul [:-1] + (ast,)) if lhs.is_mul else ast

	return AST.flatcat ('*', lhs, rhs)

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast.numer.is_diff_or_part_solo:
			p = 1
			v = ast.numer

		elif ast.numer.is_pow and ast.numer.base.is_diff_or_part_solo and ast.numer.exp.remove_curlys ().is_pos_int:
			p = int (ast.numer.exp.remove_curlys ().num)
			v = ast.numer.base

		else:
			return None

		ast_dv_check = (lambda n: n.is_differential) if v.is_diff_solo else (lambda n: n.is_partial)

		ns = ast.denom.mul if ast.denom.is_mul else (ast.denom,)
		ds = []
		cp = p

		for i in range (len (ns)):
			n = ns [i]

			if ast_dv_check (n):
				dec = 1
			elif n.is_pow and ast_dv_check (n.base) and n.exp.remove_curlys ().is_pos_int:
				dec = int (n.exp.remove_curlys ().num)
			else:
				return None

			cp -= dec

			if cp < 0:
				return None # raise SyntaxError?

			ds.append (n)

			if not cp:
				if i == len (ns) - 1:
					return AST ('diff', None, tuple (ds))
				elif i == len (ns) - 2:
					return AST ('diff', ns [-1], tuple (ds))
				else:
					return AST ('diff', AST ('*', ns [i + 1:]), tuple (ds))

		return None # raise SyntaxError?

	# start here
	if ast.is_div: # this part handles d/dx
		diff = _interpret_divide (ast)

		if diff and diff [1]:
			return diff

	elif ast.is_mul: # this part needed to handle \frac{d}{dx}
		tail = []
		end  = len (ast.mul)

		for i in range (end - 1, -1, -1):
			if ast.mul [i].is_div:
				diff = _interpret_divide (ast.mul [i])

				if diff:
					if diff.expr:
						if i < end - 1:
							tail [0 : 0] = ast.mul [i + 1 : end]

						tail.insert (0, diff)

					elif i < end - 1:
						tail.insert (0, AST ('diff', ast.mul [i + 1] if i == end - 2 else AST ('*', ast.mul [i + 1 : end]), diff.dvs))

					else:
						continue

					end = i

		if tail:
			tail = tail [0] if len (tail) == 1 else AST ('*', tuple (tail))

			return tail if end == 0 else AST.flatcat ('*', ast.mul [0], tail) if end == 1 else AST.flatcat ('*', AST ('*', ast.mul [:end]), tail)

	return ast

def _ast_strip_tail_differential (ast):
	if ast.is_differential or ast.is_null_var: # null_var is for autocomplete
		return None, ast

	if ast.is_intg:
		if ast.intg is not None:
			ast2, neg = ast.intg.strip_minus (retneg = True)
			ast2, dv  = _ast_strip_tail_differential (ast2)

			if dv:
				if ast2:
					return (AST ('intg', neg (ast2), dv, *ast [3:]), ast.dv)
				elif neg.has_neg:
					return (AST ('intg', neg (AST.One), dv, *ast [3:]), ast.dv)
				else:
					return (AST ('intg', None, dv, *ast [3:]), ast.dv)

	elif ast.is_diff:
		ast2, neg = ast.diff.strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			if ast2:
				return (AST ('diff', neg (ast2), ast.dvs), dv)
			elif len (ast.dvs) == 1:
				return (neg (AST ('/', ('@', ast.diff_type or 'd'), ast.dvs [0])), dv)
			else:
				return (neg (AST ('/', ('@', ast.diff_type or 'd'), ('*', ast.dvs))), dv)

	elif ast.is_div:
		ast2, neg = ast.denom.strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('/', ast.numer, neg (ast2)), dv

		ast2, neg = ast.numer.strip_minus (retneg = True)

		if dv:
			return AST ('/', neg (ast2) if ast2 else neg (AST.One), ast.denom), dv

	elif ast.is_mul:
		ast2, neg = ast.mul [-1].strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			if ast2:
				return (AST ('*', ast.mul [:-1] + (neg (ast2),)), dv)
			elif len (ast.mul) > 2:
				return (neg (AST ('*', ast.mul [:-1])), dv)
			else:
				return (neg (ast.mul [0]), dv)

	elif ast.is_add:
		ast2, neg = ast.add [-1].strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('+', ast.add [:-1] + (neg (ast2),)), dv

	return ast, None

def _expr_intg (ast, from_to = ()): # find differential for integration if present in ast and return integral ast
	ast, neg = ast.strip_minus (retneg = True)
	ast, dv  = _ast_strip_tail_differential (ast)

	if dv:
		if ast:
			return AST ('intg', neg (ast), dv, *from_to)
		elif neg.has_neg:
			return AST ('intg', neg (AST.One), dv, *from_to)
		else:
			return neg (AST ('intg', None, dv, *from_to))

	raise SyntaxError ('integration expecting a differential')

def _expr_func (iparm, *args, strip = 1): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	ast, wrap = _ast_func_reorder (args [iparm])

	return wrap (AST (*(args [:iparm] + ((_ast_func_tuple_args (ast) if args [0] == 'func' else ast.strip (strip)),) + args [iparm + 1:])))

def _expr_func_func (FUNC, expr_neg_func, expr_super = None):
	func = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC

	if expr_super is None:
		return _expr_func (2, 'func', func, expr_neg_func)
	elif expr_super.remove_curlys () != AST.NegOne or not AST ('func', func, ()).is_trigh_func_noninv:
		return AST ('^', _expr_func_func (FUNC, expr_neg_func), expr_super)
	else:
		return _expr_func_func (f'a{func}', expr_neg_func)

def _expr_mat (mat_rows):
	if not mat_rows:
		return AST.MatEmpty
	elif len (mat_rows [0]) > 1:
		return AST ('mat', mat_rows)
	else:
		return AST ('vec', tuple (c [0] for c in mat_rows))

def _expr_curly (ast): # convert curly expression to vector or matrix if appropriate
	if not ast.is_comma:
		return AST ('{', ast)
	elif not ast.comma: # empty {}?
		return AST.VarNull

	c = sum (bool (c.is_vec) for c in ast.comma)

	if c == len (ast.comma) and len (set (len (c.vec) for c in ast.comma)) == 1:
		if len (ast.comma [0].vec) > 1:
			return AST ('mat', tuple (c.vec for c in ast.comma))
		else:
			return AST ('vec', tuple (c.vec [0] for c in ast.comma))

	return AST ('vec', ast.comma) # raise SyntaxError ('invalid matrix syntax')

def _expr_num (NUM):
	num = NUM.grp [1] or (NUM.grp [0] if NUM.text [0] != '.' else f'0{NUM.grp [0]}')

	if not NUM.grp [2]:
		return AST ('#', num)

	g2  = NUM.grp [2].replace ('{', '').replace ('}', '')

	if g2 [1] in {'-', '+'}:
		return AST ('#', f'{num}{g2.lower ()}')
	else:
		return AST ('#', f'{num}{g2 [0].lower ()}+{g2 [1:]}')

def _expr_var (VAR, var_tex_xlat):
	if VAR.grp [0]:
		var = 'partial' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_'))
	elif VAR.grp [1]:
		var = 'd' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_'))
	elif VAR.grp [3] in var_tex_xlat:
		var = var_tex_xlat [VAR.grp [3]]
	else:
		var = AST.Var.ANY2PY.get (VAR.grp [3].replace (' ', ''), VAR.grp [3].replace ('\\_', '_'))

	return AST ('@', var + '_prime' * len (VAR.grp [4]))

#...............................................................................................
class Parser (lalr1.LALR1):
	def __init__ (self):
		self.TOKENS_LONG.update ([(v, self.TOKENS [v]) for v in self.TOKENS_QUICK])

		lalr1.LALR1.__init__ (self)

	def set_quick (self, yes = True):
		self.TOKENS.update (self.TOKENS_QUICK if yes else self.TOKENS_LONG)

		self.set_tokens (self.TOKENS)

	_USER_FUNCS = set () # set or dict of variable names to be translated into 'func' ASTs if variable followed by parentheses

	def set_user_funcs  (self, user_funcs):
		self._USER_FUNCS = user_funcs

	_PARSER_TABLES = \
			b'eJztXW2P3DaS/jMHZAZQAxLfJPmb4zhZ4/yStZ3gDgPDcBxnEVzi5Gzv3h0W+9+vqp6iRFLqGWmmZ6anpzGcFkVRZLFYT5Esvujk7Kt/+/Dx56+qrx69ePriOV2fPv72NV2+f/jy8fOn5Hny3fMXLx+/ffTDy6f/Sbffvnz4SC+NXg1dv3783dtHD189fqX+' \
			b'Zw9fq+/r0fvj6P0eXkmVc3n25PkP8i6l9+8c8Or1S/794Wv6ff7DM/r98SGHPHn++jum8skzeSy/f33JaT0V6l/w029/eM5Efi1vPHrx7NnDWKKXMdOXMTP2vHzy3V84icd/pZ+Hz76n32++fvrq6cNXf+HQ599oedj39ej9cfRqeR4/ffVYQyI3OKHXIIQI' \
			b'4EjPHn7/6vULzum1FPLxfzx6Gh8zT7958uOTbziZR9+8eC2s0JILed8/FUY9+ZZ+JBXiEb/1/t2nD1/e/vHp7c8//fb5y7tPFPThf//89Pbz3//8MNx8/PC3t7/8/eP78eFP5P393Ze37//4TX2f/vif0fdZUv784fPn94Pvz8EXk3n30+j98mXI7Zd3779E' \
			b'/5+SKoIzAn6P3t9+Hby/fvzyt+j//e+/vf319z/j7T/Gkn0c3/35139E75cPn5LgX36J/p8+vXv/Xx++JJyI3vd///Tb/6XZkWe4fTe88e7nn4c3uPQjsR/+eygaZTKU+NcP7z8MN1Q7H8dE//z85Y94N7w9pP7Hb398HG9+//1ddvP5qzfV2cnGNZUzpxU8' \
			b'lj3W8I+trD/VW7oTn+NoFV027jQLwJ2N79ELQxB7JdbGS0hTnZjKtNWmqSx7TodQCRsDNi17GoMfT1Q0SDQGNS4NYi+/WOPHKfE1EdBIlJYzbrxmTIExVMOGgE3Ti49o6iouvtNHRFMDRkiB6NaeJrfRn4Q3uGyENCP/pouPma+SroYjk2pjNBD3nhK0QmAd' \
			b'A4hI8VFKppaUavw4DtHExyDm0xjKXvJRsptQcf2EU9yTh2P0+HEIJh/xkH0UzjkzD1BSCgjJTYsLB/B7zG0r7Cb5YI70p0n4xtWToPTWTWO4/JZlrJsElS/5/DZMbvMXNlQJzNhaZY4La041iL0cjWSe2ci5u3qIEIPH240RgScaTkxTkVxxNRpK1QlPOK7y' \
			b'eD4GA5KkflnEpkxxY6Q6A/23lXNR5qjIKKJVNHD9+sqGFBP0LAYPAcwADmnHkAYh3RhiENLHEBJW8Tn8uH6gMAb5Og1iL5Nv8UNcPD0dvRyHyqPx9JZQIBjr8UDzpluqT3mXeCMxBP42qh1EozAJGW+dsNZFsJFIiC7oIAKenvmKax35p8EaQPeSbYcfEpFT' \
			b'vScsCWn0pJF09c5DTKhkVKNj3VobxcQlFRtiuSjwxJmhwHJrY6p056AimA/N4DPqA5vZAx5RvqCtxU+i4VtVXjbgR5S76uggXvb5+PBUb+kuPjg9pXbmrOaiWDC/I4ZXVKkEEpJUKhNBryexYc6Gtgpd1fmqC1XXVh35+6qvq55bJxZkRxUQKk98ozSo6gwz' \
			b'jKqeZDmQFqqrtqlaU7W2al3V+qoNVdsyN6lQXV11LA9U3IrAStQ1Nd3XlEZNidROgECxKVdKsaa3u6rtq0B0NVUwVbBVcFWgrELVkyNotaxiSbJJkr0AlqSBcOl95YlMKpipeiKcW1niu1RwXRF2GvOmOqm5hTg7sXI9IfbwhfjTEM9OiEny1KAdMQ6XVp6e' \
			b'sXKT+8CXIzffsNICN+V64mplVGjlnnsMzNbQIVoH/gXEbjpc4kudsPUos1Mud62y2R45tIVDUcIgWj3Q3TcqWk4Yh1JOC4cyDaUpi4ISUCYuIBPndpKaR2oeMPAKCmgergeoHFFQVO6K6rAift3TCmbqmVsNVEirlxB1h1Q4qNbOlRB3nVRlvE9ZfkXJoEL2' \
			b'R5zPisHZSSsV3UgQhXELUxN5NXGspsj1/WVMc2TMPGPMkTHzjLFHxsw1NS16/S36sBZ3nQ4U4vAB7Y8NuGCAcCKES5fW6FVb89rpa2jrW7ncrVbppHNaFm16tesf0NUKUvLeVb0f636o6cNomE+CdkICqjWAI8HrKAfC0OtF++wOYuRQ80641ndVzygjrhCx' \
			b'dh/LSv1SVKxv7g7FQJ1H7Xg3SuTdIB/A8iI/oHOkez8phmz3JhMRftKjDtwwAFOFGFRRKjia5tjR3dI6E1MMLFPmaGsCS5gLsModWaKjYs+sEPsbXe9V2cXIeJQD5UUngnBUpHNiIthga/ORQ/Mcauoja7aYlQP0ayeq5n7ywFrlAXDUQ1juHyNkFsFc2e5/' \
			b'lk1/8TyAA3+9KKhDHTuf8cwGle/wiuUOsFg87YSOJYZxsPhAXnWmTadydXzXSv/jMAp/xtNKB1ManhqTqmxgz5mZg3+jM/UVTzyxjm/jK/pO00S7Zqf1LVZiCYkj+hq2gLZBCgYXbTusMJTtpIyVu8jFtkNJgrAms3UEFLmcue2jvVSuu6Sl94MZ0sAMaWCG' \
			b'NFwTvfZZXAuyYHEcu3doutHJQwNedPXuSXvOtlgwSqp2jw2DfTdaBPeTwH7XIs4mTyzoMHtd9pPOanNY77UQsRkfvUyz53TG3rDdczrV8ubDftPZoyF22kahHW6aaFvmhemk/vlC7QJfqEmw6CbYUwxWLHoEx7nimTakAQspRJgWcAELrQULO7Cw5zhvZM2w' \
			b'1fGenek2NKiNcoETrzafBHM33aKbLr0t/r23S8R4SCL9oPtrqmk9hARi2AzQtbEzb7QTz4aG+4zbMxm43F85aSAZBhdVSBZicxcXp5zx0NLezaGljCnt4Vr+eCBsdLhqMVy1GK5yoXUAEZIb18ZuyXQPBg/WpDHtYIyGvaJDJ8ejFfYQa4/svCrDJnZrnHZr' \
			b'XDR0oBl3aMYd2m+nDbe7Z7OqJ+C9dv64qbC5lSeormjBvzupKwKquex5EfUO8ukgn07NKU7NKW6fO/qUrlfJ9rHVh2R7SDZful4jWbmlonoU1d/TplBUz30tPMu0hy04qFQESEWAVNCFiggQBERsNWJ7KPbxMy5vi/K2ghi0NzDrENltZu7lsndgUoeXOo3X' \
			b'HRRH+gMqjT+c0rCg9br0uNa1x7W0XnV1Rp0Z2SnGJgDeLdarYmK6JFXKmY09w0yA5JmyBEoQBWKqvfCgzwrtI8+IcGoLqaC8wLZlkIDaFnYhsRPRPRPAFHDZeDKCd7Sx2uT+HXfueM8tb8O1rEopjNnAqpHX1vPCet5UKtvt6Tnv4+NdeLyoWo5ZoHd5vSwv' \
			b'ROV9dLyJjhek82p0XqzNC7WZVTzbxaYTtpvwVjG2KrPlltnKmyt5oyAVwRD9hrhtRHBwDAefDiFb2yvZCt7HIwiqDTUUG6rdDb28cXywga82XvZ8V3JkBNXqhnQ/H9mx6TgZ7OffcN1uuHI3zK8NV68cbdDxLvuaX6REAmfA+VECnveu8950foUT5CMl5LQD' \
			b'CuPElSAS6E1oNEXZ+V/Tk463ylMon1xAlbghoeXjC2Qnv+yRl4Mg6E1KueP95bynnffA83u8u55p5Nz4fBCmjk8AoPgkwJuWwzhnToNZwOzgf3pOPN7wWQN8jIhs1w84y6LjEtB/YNqYHbKDn/zMWg5nWpgGik91twn+DXdgWLwz0W7GlrcQcOLLVWW8G8U8' \
			b'1QtzIm8Wiv0uRd5fUuybhaLvuey+lHbPQedI/DXKvEfmxlfxb6vk+6Wyvzu5Z1G+jOhzUgvEv/qne8AKyD9gFRRqurh/SR/ljGupS7CARgitSBPhkMztYtp3BTpcApAtreAIlrwRJYnRRi7pDJNQYAzFIHIjjqR/NbZ3sstILZTDTEM6+yAQcwqzUEAtJBCz' \
			b'ObR4BxafVjCBGKXFO7InUKN4vAWG95Yshlw9wo63SU2gR8/4sIMBfkYhSAqMcGKIDzkcueCQdPURCFn8iFi5eAlUFEpXIXNrUMmATEHJ/gSXnRtdidEi18IJoS5LoBsRzF4FMUfsUSLXa7TWANDyhkXmDS5KipQ7xbewSWHNkE7gHLmSgzqGjtAeqezdYoA3' \
			b'oDIosTnKNQ/FucTLsskwTzgnae27B1IxJI0PWNeQZNG1ZfzbAf91ogLafQL/LPLdIvAfgU/A50ILQDgL3HADrI0v3yrq8TB1a1Av6Sao5/sE9VmyJeonGWexnZsEEVdYyKUyi05rjzK5PsaVdSCNgF7yVhJAsUfsFPTNdtArUwrQa+gI+pHONaDHG0GJLUCv' \
			b'nADoJV6WzQzoZ8Dupo39/iP9CPNlMOexARABX4pxM2LclG4Vxk2BcZNjPE22xPgk4yy2c5MgbdYno9IeBXJ9jCgANwC4AcANAG4AcJMD3GwHuGZXAFxDE4APRK4BON4ISmwBcGWDAtwA4GM2ywDuDxTgx068gjxUcngiTIUhB3kYQR5KtwrkoQB5yEGeJluC' \
			b'fJJxFtu5SVAEeRhAzt4exXF9ElNQHoDyAJQHoDwA5SFHediOcmVJgXINTVA+5L0G5XgjKLEFypUPivIAlI/ZrOu7hyPaDxvtXSVyYyr1pWjvRrR3pVuF9sKCxvcp2tNkS7RPMs5iOzcJimjvRrR3QHsHtA8xBe0d0N4B7R3Q3gHtXY72bjvalSUF2jU0QfuQ' \
			b'9xq0442gxBZoVz4o2jugfcxmHdrbI9oPG+0916bAA74U7aOBHA9TtwrtfYH23GSeJVuifZJxFtu5SVBEez+ivQfae6B9iClo74H2HmjvgfYeaO9ztPfb0a4sKdCuoQnah7zXoF0ZpsQWaFc+KNphgk+yWYf27miXvx+w56qEeU59BHuDuTG5eLko+BEldWvA' \
			b'bwoLncktdFmyBfinGZd0ODcJUvyb0ULH3h4lcn0Sk/FvYKIzMNEZmOgMTHQmN9GZ7Sa6yJUc/zF0xP8YdQX+9Y2gxOb4j3wA/g1MdEk26/DfH/F/T/AfuPoEJ/Ax/gPwj8bfjAN7REndKvwXA3uTD+yzZEv8TzJuSkKcm9AWFcA4uDcY3BsM7seYogAwuDcY' \
			b'3BsM7g0G9yYf3Jvtg/vIlkIBaGiiAIa81ygAvBGU2EIBKB9UAWBwn2SzTgE09VED3BMN0OLDSvJ9JfaxBmihAVpogHbUAG3pVmmAttAAba4B0mRLDXCREwVQBEUF0I4KoIUCaKEAhpiiAFoogBYKoIUCaKEA2lwBtNsVgHKlUAAamiiAIe81CgBvBCW2UADK' \
			b'B1UALRTAmM1KBdAcFcA9UQCdfF6swbFpsPMZDP7l4uUSFUBXulUKoLD2mdzalyVbKoBJxiUdzk2CogIYDX4GBj8Dg98YUxQADH4GBj8Dg5+Bwc/kBj+z3eAXuVIoAA1NFMCQ9xoFgDeCElsoAOWDKgAY/JJsViqA49q8+6IAeq41AQp8nVSjKIAeCmA0ACJK' \
			b'6lYpgMIAaHIDYJZsqQAmGZd0ODcJigpgtAEa2AANbIBjTFEAsAEa2AANbIAGNkCT2wDNdhtg5EqhADQ0UQBD3msUgPJMiS0UgPJBFQBsgEk2KxWATRWAOQwdMN2XctQF2TQAFwJ2c8vs5ZsOF6bXYj7AjvMBtnSr5gNsMR9g8/mANNlyPmCScUmHc5OgOCVg' \
			b'xykBiykBPnHfgyDXJ2+IxFhMDWAlvlwQ04MV6dSA3T41oNwppgY0NJkaGPJeMzWAN4ISW0wNKD90asBiamDMZqVa2LqMr94bhXCbK/mKjTCrtcBNaACeGeLZLX9Rz8BxTUoLCl8yKcgnTLqxW+BKd6WNNCZfs49aGf8nfYNJ7hklbhoUNQHjiXdRhmpY3Wew' \
			b'9WzIC42GLgaodTVArcsBal0PUBfjA5fpAUk+6SEog4oegobmG3PMurX78sXjljMEyUUHQfmhHQQWAe76VBss+BvZk+mEvn0gqrINdK1FB/jZdfv72TUwV1rDf+wYqCrwXI+yjl98BhvpZANnwAWBUSFM3Kpxgi/0gS/0gUnSLZXBXOapC9h6V5LHi/pRQiFW' \
			b'hwseOgFb8sbIMlzwGC54DBc8hgsew4V8q55E3TJcUOYUykBDk+HCkPcadYA3ghJbaAMtl2oDDx0wZrOyXzCzHnA/FcLRXnA1VcD1AoOh+jpciFgLg6EdDYaIkro1eqDsF9jcYJglW6iBacYlHc5NgrRbYEeDoYXB0MJgOMZkBWDRKbDoE1h0CSx6BDbvENjt' \
			b'BsPIlVwBxNBRAYx5r1AA+kZQYnMFEPkABWBhMEyyWakAZpYIXpMCCBcfbHFUA9euBuTEIYELfJ1Ul6gBmA3taDZElNStUgOF2bCHGpAN8vzNQn6D1YEk3IOMUh1MCCjpcW4SFNXBaD60MB9amA/HmKIOYD60MB9amA8tzIc2Nx/a7ebDyJ1CHWhoog6GvNeo' \
			b'A7wRlNhCHSgfVB3AfJhks1IdHNcQ3hNFwNWBNYTq4wODsIbQYQ2hG9cQIkrq1igCV6whdPkawizZQgFMMy7pcG4SpArAjWsIHdYQOqwhHGPKFy6xhtBhDaHDGkKHNYQuX0Potq8hjFzJFUAMHRXAmPcKBaBvBCU2VwCRD1AADmsIk2xWKoDjIsIbVgBqw749' \
			b'RWAqAZtc2MeKwEARGCgCMyoCU7pVisAUisDkiiBNtlQEk4xLOpybBEVFYEZFYKAIDBTBEFMUgYEiMFAEBorAQBGYXBGY7YpA8ysUgYYmimDIu3dDERaqA8QOSnKhDjQpVQewESaZrVMHZmZF4TXtINrpRMHy47GuA9aXgPLVYeyYnSLu8CVWfzea/PEwdasA' \
			b'7AoA5xb/CWgnmWUZzwRFxLoq27/vYN3fXHS4lnPbcamFLXCpoQkuR/IWohGxZ87WiukoFB2gOKS/cH++mVnTd4TgXkIwsJFD5Be+FILjgnw8TN0qCBYL8l04H4KTzLKMnZsERQiGAoJhIQS3L7OPhS0gqKEJBEfyFkIQsecgqOkoBLG+fkx/KQRnVtUdIbiX' \
			b'EOzYwijyC18KwdG+jYepWwXBwr7tuvMhOMksy9i5SVCEYFdAsFsIwe1m61jYAoIamkBwJG8hBBF7DoKajkIQ9uox/aUQtAe6lX2fhqK3NQRllkPk1Zeg1o8nTOJh6tagVtJNUMv3CWqzZMtTYCcZZ7GdmwR1Q3Em51B5HDAZy1zrCxYZN7iAXI/YCbT99tMl' \
			b'I0dyaMfQEdojkSssUPpGUGJzhEc2AOESL8tmIcKPJ80dMMIbZrlAAr4U4aOdGQ9TtwrhhZ3Z53bmLNkS4ZOMs9jOTYIiwpsZhMPMHMtc13jBImPNH+R6xE4Rvt3GHDlSIFxDE4QPUdcgHG8EJbZAuLJBEQ4bc5LNQoQf6lFzR4QTwg3zWyABX4rw0YDsTelW' \
			b'IbwwIPvcgJwlWyJ8knEW27lJUES4mUE47MexzIxwGI89jMcexmMP47HPjcd+u/E4cqRAuIYmCB+IXINwvBGU2ALhygZFOMzGSTYLEX6ox8sdEU4It8xsgQR8KcLHzSV4mLpVCC82l/h8c0mWbInwScZZbOcmQRHhdgbh2FMSy8wIx4YSj3G3x4YSjw0lPt9Q' \
			b'4rdvKIkcKRCuoQnCByLXIBxvBCW2QLiyQRGODSVJNgsR3s5+7yddUO5vdWvJ5JtKt3MifD3zwaFUIZgdbTxZqxi6hcrBXUZBdBd9tyjgE3Zqlys+5+JH+xwipe5KG1N8bqDL0p185MhkHzqaUuJhsyuDeCE6jP++m1EnMN1pXFEnWIbqsQzVYxmqxzJUny9D' \
			b'5ZorP5nkExvflq/HRMYVqkZDR1XDCNfQhbqGRUT0TTd8V8ZPF6ryp2Uiv1TpwPg3Mi1TOv4BBZHmkWfy2/NvkBBWRXxpOda/8BH5s5v47Nh+fXPMr2j/t9nUXXXOB5j6/fvs2H5+ckxObVnWLF/m20ss4f2MhDfXIuRj29nujagvEXM/I+pLxPyiz+tZc0uy' \
			b'nrQ8jZ6OsEcyv6hpqKcyv0zeqexTeZ92KXcr7/1O5b2+AZm/QN6Jxw3Vb5T7hsvDnyu/e/Jvm2uQf+bfbX9qEj3pMOAg9qZLPDQLezg7+O7k5NuqxKpLLCO4re5OuwAX3SXbgvNwYNeZL3fyudXGlViw5nbaAx45LmsTzAJMNLPtQvVPkgL+CqV8eM7cTJ9/' \
			b'bB7O+wDrZQDBzTo9p4q4ne8PLx0H7P33h2WYrv87bSTQqWzFVHIb3yVmRbXs46xUmw8oVwGGrc72eyB80yODRPBJJFYK/yj0wRzG4PdmBwGpTLMJcd1Hh9sHpGpEqt1NSnUdez59Ray5A+JN/tZdZvC7Tzo9ke8m2bzLxu4Ns/1uCLuSGy417PU3KOV8alIf' \
			b'Bb27dlmfncq4rLxTGFXNIco9v5iIvqTR34j8T5fjX1rfcyGZuu7ySAgLkEAVuNuODNG+CyQsmNybndS7DBrCLbQATXOdY93ZcS6nhI8x7wYMTfoV16UtQtNcDhPc3RRcXAkR7RJEtLtGxACH5ib7QZdFw8EjoUBBU27Nuv5u0WVBcHUAdEsA0F0bAMwRAPsI' \
			b'gBsfF9weAPolAFi1nGoVAOwRAPsIgHKJ0eECgOrkaNpcMwF8p8a+u7Vp8rLG25rU3WKjt+YBYYytmUT3Ddp52szUc40Wnm0LVq9q5TkUCWcubVxq4LlmzW2vwapzCbVtrknatywAn1HhIV3TfdOKfM1GjQsmaGVFTyMrRvZL7LE6Pv9fouglXro6+ubt+is2' \
			b'VVy0epM/yiCf6JBSlQ2Adw9IO4j+v6452iMi9ggRYfK/DBHhoBDhFRHhfES46qyrxj2CRsTfiOCnUi8izwO8bDtdOy9rodjN0jckE0xEsltN6p3rnOub63qunoc6Lg8Vk4+Pz3CROZNyJPTSEPoVhQRyWwA2gnBJod204AwYKbwI2WVLzySI5OrhcnjKwreE' \
			b'JVFgSkFR1oQ1rPFT7uwJh7oR3xmXIkx3wKl2Dae2NAjKuLCqBVjA2jWafaLRY3c+XLkapCj5f6Z6tWokfJ2aXVJ/a9RnWcfxG191m6vHrqz0qw8QL2vjSMXgJtcobh3tzYnKlpa8dzsY0V3NVrFlM/C12CVmJGvaCFve0OtFyvqjlK2RMhaqa7Mb7EzKeItz' \
			b'c8syZuwDfGySZE2+Whjo6ljmKIujzK2RueucbtidzIHQfZW5Jpe5HVlcD1XsWNyu3Ux6UI0qy5jZWxm76c0lUc5slX+09FyZO78fdy0y1/pLipy8eD1Sx0ltGyNwEsyOGd03/eInpa3yuOuJprssktvEUCYPb3KWaHfq7ybmOxeqQCdfFGnaVjjLA/MOD7x8' \
			b'o8AbCqds+/7NKflONnK6PQ4PwnErw547Yi1/25zPJKC8eO+unKozbqHrAie8MRekQPKe/8lbep5w+p5u+7NlApYN6Vb/xj19LoZJei5LrymPO5pNPujeWl48PEyk6kk/OH2Hj7Su8EeS4mRJTnQu+5PN58RkesCST7XNu8B5SQx2hAuR/nJE8mlBF9JJMS/8' \
			b'49mDIkzoCkvpmjvaaStp/Gwgj3TWlj+e4tj6jMBMVyGyLYmcnGnl5JsPmf3t/OPo8hOpuKGUrdbx4CnWmizaFCYHTYX5cqYHQQ0HO/XVcIBTb9JDm95wmzD8+Sq/Kdzc31ysadh8wumjMaqwt7t+GSC1c7k/IbC/gfofdttHEQjXKAac2HU7Ng6PN93Vk5Sq' \
			b'aOrrFxbuu+zegfwmJZ/rs9uRQDW3LlNtNTh8pS0Nubyzu0roPIfKMefLlp79di6qt0pY5OMgZdwh3+6kr3qe4170TChVf7xBmezBChwPZ+6qQ91c0HNcIm+ogBVSZ6srujh0OzcWyucPVvZ4EH1XHepm0vGe1spi8UMdLBTCOW42Ver4o8zNJV00JlwQqzAF' \
			b'CEfaw5VWU91Zh7qZDBFuU1ptdUsOvOgPV05ddWcdDFKT0cltyqmvbsmBF4c71GGD+V11qBtzF+smfjB7WR211Z67puX/7pwoqCu7c53SnzdOrReoFhaLnTqu55lQInrLG2DNZAC1TYB3xZ05VbGdS7Y63/H3yC+Ks8Sl6cylCWZNpgD2i1m+2g8HZi0YHt0m' \
			b's9pqPxyYdTjzI6yGFjiZ6k7+F752XhLLk5uNgYpYMEy6IxXBSw7ujAPzb2KW6IaY76u74zCnv2DgdVeYH6q748D85nCY31Z3x4H5fDI2b2Vq9d7G+w73ju+ZNRzGq6QahFN3MK0h4h+vD2jl6C/Dx780Qas3zMbsqsQhYjuJyFXBkfsqdU2LLqmc8RRXBgWu' \
			b'TgT3+DB0FJVzq73tee6Rl6ClS8+GJWMzy8U6MIqPFyk2TMmuUpkB5hwlJ82FJwk9CwkGHnyiQ9NJzj0V5c3p/wOPNh1x'

	_PARSER_TOP             = 'expr_commas'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	_VAR_TEX_XLAT = {
		r'\mathbb{R}'  : 'Reals',
		r'\mathbb{C}'  : 'Complexes',
		r'\mathbb{N}'  : 'Naturals',
		r'\mathbb{N}_0': 'Naturals0',
		r'\mathbb{Z}'  : 'Integers',
	}

	_UPARTIAL = '\u2202'
	_USUM     = '\u2211'
	_UINTG    = '\u222b'
	_LETTER   = fr'[a-zA-Z]'
	_LETTERU  = fr'[a-zA-Z_]'

	_TEXGREEK = '(?:' + '|'.join (reversed (sorted (f'\\\\{g}' for g in AST.Var.GREEK))) + ')'
	_TEXXLAT  = '(?:' + '|'.join (reversed (sorted (x.replace ('\\', '\\\\') for x in _VAR_TEX_XLAT))) + ')'
	_VARPY    = fr'(?:{_LETTER}(?:\w|\\_)*)'
	_VARTEX   = fr'(?:{_TEXGREEK}|{_TEXXLAT}|\\partial|(?:(?:\\overline|\\bar|\\widetilde|\\tilde)\s*)?\\infty)'
	_VARTEX1  = fr'(?:(\d)|({_LETTER})|({_VARTEX}))'
	_VARUNI   = fr'(?:{"|".join (AST.Var.UNI2PY)})'
	_VAR      = fr'(?:{_VARPY}|{_VARTEX}(?!{_LETTERU})|{_VARUNI})'

	_STR      = r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY - AST.Func.PSEUDO)))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LETTERU})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\$?{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LETTER})'),
		('LOG',           r'log\b|\\log(?!{_LETTER})'),
		('LN',            r'ln\b|\\ln(?!{_LETTER})'),
		('LIM',          fr'\\lim(?!{_LETTER})'),
		('SUM',          fr'\\sum(?:\s*\\limits)?(?!{_LETTER})|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?(?!{_LETTER})|{_UINTG}'),
		('LEFT',         fr'\\left(?!{_LETTERU})'),
		('RIGHT',        fr'\\right(?!{_LETTERU})'),
		('CDOT',         fr'\\cdot(?!{_LETTERU})'),
		('TO',           fr'\\to(?!{_LETTERU})'),
		('MAPSTO',       fr'\\mapsto(?!{_LETTERU})'),
		('BEG_MAT',       r'\\begin\s*{\s*matrix\s*}'),
		('END_MAT',       r'\\end\s*{\s*matrix\s*}'),
		('BEG_BMAT',      r'\\begin\s*{\s*bmatrix\s*}'),
		('END_BMAT',      r'\\end\s*{\s*bmatrix\s*}'),
		('BEG_VMAT',      r'\\begin\s*{\s*vmatrix\s*}'),
		('END_VMAT',      r'\\end\s*{\s*vmatrix\s*}'),
		('BEG_PMAT',      r'\\begin\s*{\s*pmatrix\s*}'),
		('END_PMAT',      r'\\end\s*{\s*pmatrix\s*}'),
		('BEG_CASES',     r'\\begin\s*{\s*cases\s*}'),
		('END_CASES',     r'\\end\s*{\s*cases\s*}'),
		('FRAC2',        fr'\\frac\s*{_VARTEX1}\s*{_VARTEX1}'),
		('FRAC1',        fr'\\frac\s*{_VARTEX1}'),
		('FRAC',          r'\\frac'),
		('IF',            r'if(?!{_LETTERU})'),
		('ELSE',          r'else(?!{_LETTERU})'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))('*)"),
		('ATTR',         fr'\.(?:({_LETTERU}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"({_STR})|\\text\s*{{\s*({_STR})\s*}}"),
		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
		('COLON',         r'{:}|:'),
		('CARET1',       fr'\^{_VARTEX1}'),
		('CARET',         r'\^'),
		('DBLSTAR',       r'\*\*'),
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('CURLYL',        r'{'),
		('CURLYR',        r'}'),
		('BRACKL',        r'\['),
		('BRACKR',        r'\]'),
		('BAR',           r'\|'),
		('PLUS',          r'\+'),
		('MINUS',         r'-'),
		('STAR',          r'\*'),
		('INEQ',         fr'==|!=|\\neq?|<=|\\le|<|\\lt|>=|\\ge|>|\\gt|{"|".join (AST.Eq.UNI2PY)}'),
		('EQ',            r'='),
		('DIVIDE',        r'/'),
		('EXCL',          r'!'),
		('AMP',           r'&'),
		('DBLSLASH',      r'\\\\'),
		('COMMA',         r','),
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('ignore',        r'\\,|\\:|\\?\s+|\\text\s*{\s*[^}]*\s*}'),
	])

	_VARPY_QUICK = fr'(?:{_LETTER})'
	_VAR_QUICK   = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK = OrderedDict ([ # quick input mode different tokens
		('FUNC',         fr'(@|\%|{_FUNCPY})|\\({_FUNCTEX})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
		('SQRT',          r'sqrt|\\sqrt'),
		('LOG',           r'log|\\log'),
		('LN',            r'ln|\\ln'),
		('LIM',          fr'\\lim'),
		('SUM',          fr'\\sum(?:\s*\\limits)?|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?|{_UINTG}'),
		('LEFT',         fr'\\left'),
		('RIGHT',        fr'\\right'),
		('CDOT',         fr'\\cdot'),
		('TO',           fr'\\to'),
		('MAPSTO',       fr'\\mapsto'),
		('IF',            r'if'),
		('ELSE',          r'else'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR_QUICK})|({_VAR_QUICK}))('*)"),
	])

	TOKENS_LONG  = OrderedDict () # initialized in __init__()

	def expr_commas_1      (self, expr_comma, COMMA):                              return expr_comma if expr_comma.is_comma else AST (',', (expr_comma,))
	def expr_commas_2      (self, expr_comma):                                     return expr_comma
	def expr_commas_3      (self):                                                 return AST.CommaEmpty
	def expr_comma_1       (self, expr_comma, COMMA, expr_colon):                  return _expr_comma (expr_comma, expr_colon)
	def expr_comma_2       (self, expr_colon):                                     return expr_colon

	def expr_colon_1       (self, expr, COLON, expr_colon):                        return _expr_colon (expr, expr_colon)
	def expr_colon_2       (self, expr, COLON):                                    return AST ('slice', expr, False, None)
	def expr_colon_3       (self, COLON, expr_colon):                              return _ast_pre_slice (False, expr_colon)
	def expr_colon_4       (self, COLON):                                          return AST ('slice', False, False, None)
	def expr_colon_5       (self, expr):                                           return expr

	def expr               (self, expr_eq):                                        return expr_eq

	def expr_eq_1          (self, expr_mapsto1, EQ, expr_mapsto2):                 return AST ('=', '=', expr_mapsto1, expr_mapsto2)
	def expr_eq_2          (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr_colon):                 return _expr_mapsto (expr_paren.strip (), expr_colon)
	def expr_mapsto_2      (self, expr_piece):                                     return expr_piece

	def expr_piece_1       (self, expr_ineq, IF, expr_eq, ELSE, expr_mapsto):      return _expr_piece (expr_ineq, expr_eq, expr_mapsto)
	def expr_piece_2       (self, expr_ineq, IF, expr_eq):                         return AST ('piece', ((expr_ineq, expr_eq),))
	def expr_piece_3       (self, expr_ineq):                                      return expr_ineq

	def expr_ineq_2        (self, expr_add1, INEQ, expr_add2):                     return AST ('=', AST.Eq.ANY2PY.get (INEQ.text, INEQ.text), expr_add1, expr_add2)
	def expr_ineq_3        (self, expr_add):                                       return expr_add

	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                  return AST.flatcat ('+', expr_add, expr_mul_exp.neg (stack = True))
	def expr_add_3         (self, expr_mul_exp):                                   return expr_mul_exp

	def expr_mul_exp_1     (self, expr_mul_exp, CDOT, expr_neg):                   return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_2     (self, expr_mul_exp, STAR, expr_neg):                   return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_3     (self, expr_neg):                                       return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                return expr_neg.neg (stack = True)
	def expr_neg_2         (self, expr_diff):                                      return expr_diff

	def expr_diff          (self, expr_div):                                       return _expr_diff (expr_div)

	def expr_div_1         (self, expr_div, DIVIDE, expr_mul_imp):                 return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2         (self, expr_div, DIVIDE, MINUS, expr_mul_imp):          return AST ('/', expr_div, expr_mul_imp.neg (stack = True))
	def expr_div_3         (self, expr_mul_imp):                                   return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                        return _expr_mul_imp (expr_mul_imp, expr_intg, self._USER_FUNCS)
	def expr_mul_imp_2     (self, expr_intg):                                      return expr_intg

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add):           return _expr_intg (expr_add, (expr_sub, expr_super))
	def expr_intg_2        (self, INTG, expr_add):                                 return _expr_intg (expr_add)
	def expr_intg_3        (self, expr_lim):                                       return expr_lim

	def expr_lim_1         (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                           return AST ('lim', expr_neg, expr_var, expr)
	def expr_lim_2         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):   return AST ('lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg):  return AST ('lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                         return expr_sum

	def expr_sum_1         (self, SUM, SUB, CURLYL, expr_var, EQ, expr, CURLYR, expr_super, expr_neg):               return AST ('sum', expr_neg, expr_var, expr, expr_super)
	def expr_sum_2         (self, expr_func):                                                                        return expr_func

	def expr_func_1        (self, SQRT, BRACKL, expr, BRACKR, expr_neg_func):      return _expr_func (1, 'sqrt', expr_neg_func, expr)
	def expr_func_2        (self, SQRT, expr_super, expr_neg_func):                return AST ('^', _expr_func (1, 'sqrt', expr_neg_func), expr_super)
	def expr_func_3        (self, SQRT, expr_neg_func):                            return _expr_func (1, 'sqrt', expr_neg_func)
	def expr_func_4        (self, LN, expr_super, expr_neg_func):                  return AST ('^', _expr_func (1, 'log', expr_neg_func), expr_super)
	def expr_func_5        (self, LN, expr_neg_func):                              return _expr_func (1, 'log', expr_neg_func)
	def expr_func_6        (self, LOG, expr_sub, expr_neg_func):                   return _expr_func (1, 'log', expr_neg_func, expr_sub)
	def expr_func_7        (self, LOG, expr_super, expr_neg_func):                 return AST ('^', _expr_func (1, 'log', expr_neg_func), expr_super)
	def expr_func_8        (self, LOG, expr_neg_func):                             return _expr_func (1, 'log', expr_neg_func)
	def expr_func_9        (self, FUNC, expr_neg_func):                            return _expr_func_func (FUNC, expr_neg_func)
	def expr_func_10       (self, FUNC, expr_super, expr_neg_func):                return _expr_func_func (FUNC, expr_neg_func, expr_super)
	def expr_func_11       (self, expr_pow):                                       return expr_pow

	def expr_pow_1         (self, expr_pow, expr_super):                           return AST ('^', expr_pow, expr_super)
	def expr_pow_2         (self, expr_fact):                                      return expr_fact

	def expr_fact_1        (self, expr_fact, EXCL):                                return AST ('!', expr_fact)
	def expr_fact_2        (self, expr_attr):                                      return expr_attr

	def expr_attr_1        (self, expr_attr, ATTR):                                return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1])
	def expr_attr_2        (self, expr_abs):                                       return expr_abs

	def expr_abs_1         (self, LEFT, BAR1, expr_commas, RIGHT, BAR2):           return AST ('|', expr_commas)
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                        return AST ('|', expr_commas)
	def expr_abs_3         (self, expr_paren):                                     return expr_paren

	def expr_paren_1       (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):       return AST ('(', expr_commas)
	def expr_paren_2       (self, PARENL, expr_commas, PARENR):                    return AST ('(', expr_commas)
	def expr_paren_3       (self, IGNORE_CURLY, CURLYL, expr, CURLYR):             return AST ('{', expr)
	def expr_paren_4       (self, expr_frac):                                      return expr_frac

	def expr_frac_1        (self, FRAC, expr_cases1, expr_cases2):                 return AST ('/', expr_cases1.remove_curlys (), expr_cases2.remove_curlys ())
	def expr_frac_2        (self, FRAC1, expr_cases):                              return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_cases.remove_curlys ())
	def expr_frac_3        (self, FRAC2):                                          return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4        (self, expr_cases):                                     return expr_cases

	def expr_cases_1       (self, BEG_CASES, casess, END_CASES):                   return AST ('piece', casess)
	def expr_cases_2       (self, expr_mat):                                       return expr_mat
	def casess_1           (self, casessp, DBLSLASH):                              return casessp
	def casess_2           (self, casessp):                                        return casessp
	def casessp_1          (self, casessp, DBLSLASH, casessc):                     return casessp + (casessc,)
	def casessp_2          (self, casessc):                                        return (casessc,)
	def casessc_1          (self, expr1, AMP, expr2):                              return (expr1, expr2)
	def casessc_2          (self, expr, AMP):                                      return (expr, True)

	def expr_mat_1         (self, LEFT, BRACKL, BEG_MAT, mat_rows, END_MAT, RIGHT, BRACKR):  return _expr_mat (mat_rows)
	def expr_mat_2         (self, BEG_MAT, mat_rows, END_MAT):                               return _expr_mat (mat_rows)
	def expr_mat_3         (self, BEG_BMAT, mat_rows, END_BMAT):                             return _expr_mat (mat_rows)
	def expr_mat_4         (self, BEG_VMAT, mat_rows, END_VMAT):                             return _expr_mat (mat_rows)
	def expr_mat_5         (self, BEG_PMAT, mat_rows, END_PMAT):                             return _expr_mat (mat_rows)
	def expr_mat_6         (self, expr_curly):                                               return expr_curly
	def mat_rows_1         (self, mat_row, DBLSLASH):                              return mat_row
	def mat_rows_2         (self, mat_row):                                        return mat_row
	def mat_rows_3         (self):                                                 return ()
	def mat_row_1          (self, mat_row, DBLSLASH, mat_col):                     return mat_row + (mat_col,)
	def mat_row_2          (self, mat_col):                                        return (mat_col,)
	def mat_col_1          (self, mat_col, AMP, expr):                             return mat_col + (expr,)
	def mat_col_2          (self, expr):                                           return (expr,)

	def expr_curly_1       (self, CURLYL, expr_commas, CURLYR):                    return _expr_curly (expr_commas)
	def expr_curly_2       (self, expr_bracket):                                   return expr_bracket

	def expr_bracket_1     (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):       return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_2     (self, BRACKL, expr_commas, BRACKR):                    return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_3     (self, expr_term):                                      return expr_term

	def expr_term_1        (self, expr_num):                                       return expr_num
	def expr_term_2        (self, expr_var):                                       return expr_var
	def expr_term_3        (self, STR):                                            return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_4        (self, SUB):                                            return AST ('@', '_') # for last expression variable

	def expr_num           (self, NUM):                                            return _expr_num (NUM)
	def expr_var           (self, VAR):                                            return _expr_var (VAR, self._VAR_TEX_XLAT)

	def expr_sub_1         (self, SUB, expr_frac):                                 return expr_frac
	def expr_sub_2         (self, SUB1):                                           return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1       (self, DBLSTAR, expr_neg_func):                         return expr_neg_func
	def expr_super_3       (self, CARET, expr_frac):                               return expr_frac
	def expr_super_4       (self, CARET1):                                         return _ast_from_tok_digit_or_var (CARET1)

	def expr_neg_func_1    (self, MINUS, expr_neg_func):                           return expr_neg_func.neg (stack = True)
	def expr_neg_func_2    (self, expr_func):                                      return expr_func

	def caret_or_dblstar_1 (self, DBLSTAR):                                        return '**'
	def caret_or_dblstar_2 (self, CARET):                                          return '^'

	#...............................................................................................
	_AUTOCOMPLETE_SUBSTITUTE = { # autocomplete means autocomplete AST tree so it can be rendered, not necessarily expression
		'CARET1'          : 'CARET',
		'SUB1'            : 'SUB',
		'FRAC2'           : 'FRAC',
		'FRAC1'           : 'FRAC',
		'expr_super'      : 'CARET',
		'caret_or_dblstar': 'CARET',
	}

	_AUTOCOMPLETE_CONTINUE = {
		'RIGHT' : ' \\right',
		'COMMA' : ',',
		'PARENL': '(',
		'PARENR': ')',
		'CURLYR': '}',
		'BRACKR': ']',
		'BAR'   : '|',
	}

	def _insert_symbol (self, sym, tokinc = 0):
		tokidx       = self.tokidx
		self.tokidx += tokinc

		for sym in ((sym,) if isinstance (sym, str) else sym):
			if sym in self.TOKENS:
				self.tokens.insert (tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

				if self.autocompleting:
					if sym in self._AUTOCOMPLETE_CONTINUE:
						self.autocomplete.append (self._AUTOCOMPLETE_CONTINUE [sym])
					else:
						self.autocompleting = False

			else:
				self.tokens.insert (tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, ('', '', '', '', '')))
				self._mark_error ()

			tokidx += 1

		return True # for convenience

	def _mark_error (self, sym_ins = None, tokinc = 0, at = None):
		self.autocompleting = False

		if self.erridx is None:
			self.erridx = self.tokens [self.tokidx].pos if at is None else at

		if sym_ins is not None:
			return self._insert_symbol (sym_ins, tokinc)

	def _parse_autocomplete_expr_commas (self, rule, pos):
		idx = -pos + (self.stack [-pos].sym == 'LEFT')

		if self.stack [idx].sym != 'CURLYL':
			if self.tokens [self.tokidx - 1] == 'COMMA':
				self._mark_error ()

			if self.stack [idx - 1].sym == 'LEFT':
				return self._insert_symbol ('RIGHT')

			return self._insert_symbol ('PARENR' if self.stack [idx].sym == 'PARENL' else 'BRACKR')

		# vector or matrix potentially being entered
		if self.stack [idx - 1].sym == 'CURLYL':
			if self.stack [-1].red.is_null_var:
				return self._mark_error (('CURLYR', 'CURLYR'))
			elif not self.stack [-1].red.is_comma:
				return self._insert_symbol (('COMMA', 'CURLYR', 'COMMA', 'CURLYR'), 1)
			elif len (self.stack [-1].red.comma) == 1 or self.tokens [self.tokidx - 1] != 'COMMA':
				return self._insert_symbol (('CURLYR', 'COMMA', 'CURLYR'))
			else:
				return self._mark_error (('CURLYR', 'CURLYR'))

		if self.stack [-3].sym != 'COMMA' or self.stack [-4].sym != 'expr_comma' or self.stack [-5].sym != 'CURLYL':
			if self.stack [-1].red.is_vec:
				return self._insert_symbol (('COMMA', 'CURLYR'), 1)
			elif self.stack [-1].red.is_comma:
				if len (self.stack [-1].red.comma) == 1 or self.tokens [self.tokidx - 1] != 'COMMA':
					return self._insert_symbol ('CURLYR')
				else:
					return self._mark_error ('CURLYR')

		else:
			cols = \
					len (self.stack [-4].red.vec)             if self.stack [-4].red.is_vec else \
					len (self.stack [-4].red.comma [0].vec)  if self.stack [-4].red.is_comma and self.stack [-4].red.comma [0].is_vec else \
					None

			if cols is not None:
				vec             = self.stack [-1].red.comma if self.stack [-1].red.is_comma else (self.stack [-1].red,)
				self.stack [-1] = lalr1.State (self.stack [-1].idx, self.stack [-1].sym, AST (',', vec + (AST.VarNull,) * (cols - len (vec))))

				return self._mark_error (('CURLYR', 'CURLYR')) if len (vec) != cols else self._insert_symbol (('CURLYR', 'CURLYR'))

		return self._insert_symbol ('CURLYR')

	def _parse_autocomplete_expr_intg (self):
		s               = self.stack [-1]
		self.stack [-1] = lalr1.State (s.idx, s.sym, AST ('*', (s.red, AST.VarNull)))
		expr_vars       = set ()

		if self.autocompleting:
			stack = [s [2]]

			while stack:
				ast = stack.pop ()

				if ast.is_var:
					if not (ast.is_differential or ast.is_part_any):
						expr_vars.add (ast.var)
				else:
					stack.extend (filter (lambda a: isinstance (a, tuple), ast))

		expr_vars = expr_vars - {'_'} - {ast.var for ast in AST.CONSTS}

		if len (expr_vars) == 1:
			self.autocomplete.append (f' d{expr_vars.pop ()}')
		else:
			self._mark_error ()

		return True

	def parse_getextrastate (self):
		return (self.autocomplete [:], self.autocompleting, self.erridx)

	def parse_setextrastate (self, state):
		self.autocomplete, self.autocompleting, self.erridx = state

	def parse_error (self): # add tokens to continue parsing for autocomplete if syntax allows
		if isinstance (self.rederr, lalr1.Incomplete):
			self.parse_results.append ((self.rederr.red, self.tok.pos, []))

			return False

		if self.tok != '$end':
			self.parse_results.append ((None, self.tok.pos, []))

			return False

		if self.tokidx and self.tokens [self.tokidx - 1] == 'LEFT':
			for irule, pos in self.strules [self.stidx]:
				if self.rules [irule] [1] [pos] == 'PARENL':
					break
			else:
				raise RuntimeError ('could not find left parenthesis rule')

		else:
			irule, pos = self.strules [self.stidx] [0]

		rule = self.rules [irule]

		if pos == 1 and rule == ('expr_func', ('FUNC', 'expr_neg_func')):
			return self._insert_symbol (('PARENL', 'PARENR'))

		if pos and rule [1] [pos - 1] == 'expr_commas':
			return self._parse_autocomplete_expr_commas (rule, pos)

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_intg': # TODO: Fix this!
				return self._parse_autocomplete_expr_intg ()

			return False

		return self._insert_symbol (rule [1] [pos])

	def parse_success (self, red):
		self.parse_results.append ((red, self.erridx, self.autocomplete))

		return True # continue parsing if conflict branches remain to find best resolution

	def parse (self, text):
		if not text.strip ():
			return (AST.VarNull, 0, [])

		self.parse_results  = [] # [(reduction, erridx, autocomplete), ...]
		self.autocomplete   = []
		self.autocompleting = True
		self.erridx         = None

		lalr1.LALR1.parse (self, text)

		if not self.parse_results:
			return (None, 0, [])

		rated = sorted ((r is None, -e if e is not None else float ('-inf'), len (a), i, (r, e, a)) \
				for i, (r, e, a) in enumerate (self.parse_results))

		if os.environ.get ('SYMPAD_DEBUG'):
			rated = list (rated)

			print (file = sys.stderr)

			for res in rated [:32]:
				res = res [-1]
				res = (res [0].remove_curlys (),) + res [1:] if isinstance (res [0], AST) else res

				print ('parse:', res, file = sys.stderr)

			if len (rated) > 32:
				print (f'... total {len (rated)}', file = sys.stderr)

			print (file = sys.stderr)

		res = next (iter (rated)) [-1]

		return (res [0].remove_curlys (),) + res [1:] if isinstance (res [0], AST) else res

class sparser: # for single script
	Parser = Parser

_RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
	p = Parser ()
	a = p.parse (r'o [i].m') [0]
	# a = sym.ast2spt (a)
	print (a)
