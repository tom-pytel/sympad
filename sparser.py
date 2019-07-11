# TODO: Concretize empty matrix stuff.
# TODO: Concretize empty variable stuff.
# TODO: remap \begin{matrix} \end{matrix}?
# TODO: remap \begin{cases} \end{cases}?

# Time and interest permitting:
# Proper implementation of vectors with "<b>\vec{x}</b>" and "<b>\hat{i}</b>" variables
# sympy function/variable module prefix
# importing modules to allow custom code execution
# assumptions/hints, systems of equations, ODEs, piecewise expressions, long Python variable names, graphical plots (using matplotlib?)...

# Builds expression tree from text, nodes are nested AST tuples.

import ast as py_ast
from collections import OrderedDict
import os
import re

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT

def _FUNC_name (FUNC):
	return AST.Func.TEX2PY_TRIGHINV.get (FUNC.grp [1], FUNC.grp [1]) if FUNC.grp [1] else \
			FUNC.grp [0] or FUNC.grp [2] or FUNC.grp [3].replace ('\\_', '_') or FUNC.text

def _ast_from_tok_digit_or_var (tok, i = 0):
	return AST ('#', tok.grp [i]) if tok.grp [i] else \
			AST ('@', AST.Var.TEX2PY.get (tok.grp [i + 2].replace (' ', ''), tok.grp [i + 1]) if tok.grp [i + 2] else tok.grp [i + 1])

def _expr_mul_imp (expr_mul_imp, expr_int): # convert x.y * (...) -> x.y (...)
	if expr_mul_imp.is_attr and expr_mul_imp.arg is None:
		if expr_int.is_paren:
			return AST ('.', expr_mul_imp.obj, expr_mul_imp.attr, expr_int.strip_paren (1))
		elif expr_int.is_attr:
			return AST ('.', _expr_mul_imp (expr_mul_imp, expr_int.obj), expr_int.attr)

	return AST.flatcat ('*', expr_mul_imp, expr_int)

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast.numer.is_diff_or_part_solo:
			p = 1
			v = ast.numer

		elif ast.numer.is_pow and ast.numer.base.is_diff_or_part_solo and ast.numer.exp.is_pos_int:
			p = int (ast.numer.exp.num)
			v = ast.numer.base

		else:
			return None

		ast_dv_check = (lambda n: n.is_diff) if v.is_diff_solo else (lambda n: n.is_part)

		ns = ast.denom.muls if ast.denom.is_mul else (ast.denom,)
		ds = []
		cp = p

		for i in range (len (ns)):
			n = ns [i]

			if ast_dv_check (n):
				dec = 1
			elif n.is_pow and ast_dv_check (n.base) and n.exp.is_pos_int:
				dec = int (n.exp.num)
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
		end  = len (ast.muls)

		for i in range (end - 1, -1, -1):
			if ast.muls [i].is_div:
				diff = _interpret_divide (ast.muls [i])

				if diff:
					if diff.expr:
						if i < end - 1:
							tail [0 : 0] = ast.muls [i + 1 : end]

						tail.insert (0, diff)

					elif i < end - 1:
						tail.insert (0, AST ('diff', ast.muls [i + 1] if i == end - 2 else AST ('*', ast [i + 1 : end]), diff.dvs))

					else:
						continue

					end = i

		if tail:
			tail = tail [0] if len (tail) == 1 else AST ('*', tuple (tail))

			return tail if end == 0 else AST.flatcat ('*', ast.muls [0], tail) if end == 1 else AST.flatcat ('*', AST ('*', ast.muls [:end]), tail)

	return ast

def _expr_int (ast, from_to = ()): # find differential for integration if present in ast and return integral ast
	if ast.is_diff or ast.is_null_var: # null_var is for autocomplete
		return AST ('intg', None, ast, *from_to)

	elif ast.is_div:
		if ast.denom.is_mul and ast.denom.muls [-1].is_diff:
			return AST ('intg', ('/', ast.numer, ast.denom.muls [0] if len (ast.denom.muls) == 2 else \
					AST ('*', ast.denom.muls [:-1])), ast.denom.muls [-1], *from_to)

		if ast.numer.is_diff:
			return AST ('intg', ('/', ast.One, ast.denom), ast.numer, *from_to)

	elif ast.is_mul and (ast.muls [-1].is_diff or ast.muls [-1].is_null_var): # null_var is for autocomplete
		return AST ('intg', ast.muls [0] if len (ast.muls) == 2 else AST ('*', ast.muls [:-1]), ast.muls [-1], *from_to)

	elif ast.is_add:
		if ast.adds [-1].is_diff:
			return AST ('intg', \
					AST ('+', ast.adds [:-1])
					if len (ast.adds) > 2 else \
					ast.adds [0] \
					, ast.adds [-1], *from_to)

		if ast.adds [-1].is_mul and ast.adds [-1].muls [-1].is_diff:
			return AST ('intg', \
					AST ('+', ast.adds [:-1] + (AST ('*', ast.adds [-1].muls [:-1]),))
					if len (ast.adds [-1].muls) > 2 else \
					AST ('+', ast.adds [:-1] + (ast.adds [-1].muls [0],)) \
					, ast.adds [-1].muls [-1], *from_to)

	elif ast.is_intg and ast.intg is not None:
		return AST ('intg', _expr_int (ast.intg, () if ast.from_ is None else (ast.from_, ast.to)), ast.dv, *from_to)

	raise SyntaxError ('integration expecting a differential')

def _expr_func (iparm, *args, strip_paren = 0): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	if args [iparm].is_fact:
		if args [iparm].fact.is_paren:
			return AST ('!', args [:iparm] + (args [iparm].fact.strip_paren (strip_paren),) + args [iparm + 1:])

	elif args [iparm].is_pow:
		if args [iparm].base.is_paren:
			return AST ('^', args [:iparm] + (args [iparm].base.strip_paren (strip_paren),) + args [iparm + 1:], args [iparm].exp)

	elif args [iparm].is_attr:
		if args [iparm].obj.is_paren:
			return AST ('.', args [:iparm] + (args [iparm].obj.strip_paren (strip_paren),) + args [iparm + 1:], *args [iparm] [2:])

	return AST (*(args [:iparm] + (args [iparm].strip_paren (strip_paren),) + args [iparm + 1:]))

def _expr_func_remap (_remap_func, ast): # rearrange ast tree for a given function remapping like 'Derivative' or 'Limit'
	expr = _expr_func (1, None, ast, strip_paren = None) # strip all parentheses

	if expr.op is None:
		return _remap_func (expr [1])
	else:
		return AST (expr.op, _remap_func (expr [1] [1]), *expr [2:])

_remap_func_Limit_dirs = {'+': ('+',), '-': ('-',), '+-': ()}

def _remap_func_Derivative (ast): # remap function 'Derivative' to native ast representation for pretty rendering
	if ast.is_null_var:
		return AST ('diff', ast, (AST.VarNull,))
	elif not ast.is_comma:
		raise lalr1.Incomplete (AST ('diff', ast, (AST.VarNull,)))
	elif len (ast.commas) == 1:
		raise lalr1.Incomplete (AST ('diff', ast.commas [0], (AST.VarNull,)))

	commas = list (ast.commas [:0:-1])
	ds     = []

	while commas:
		d = commas.pop ().as_diff

		if commas and commas [-1].is_num:
			ds.append (AST ('^', d, commas.pop ()))
		else:
			ds.append (d)

	return AST ('diff', ast.commas [0], AST (*ds))

def _remap_func_Integral (ast): # remap function 'Integral' to native ast representation for pretty rendering
	if not ast.is_comma:
		return AST ('intg', ast, ast.as_diff if ast.is_var else AST.VarNull)
	elif len (ast.commas) == 1:
		ast = AST ('intg', ast.commas [0], AST.VarNull)

	else:
		ast2 = ast.commas [1].strip_paren (1)

		if not ast2.is_comma:
			return AST ('intg', ast.commas [0], ast2.as_diff)
		elif len (ast2.commas) == 3:
			return AST ('intg', ast.commas [0], ast2.commas [0].as_diff, ast2.commas [1], ast2.commas [2])
		else:
			ast = AST (*(('intg', ast.commas [0], ast2.commas [0].as_diff) + ast2.commas [1:] + (AST.VarNull, AST.VarNull)) [:5])

	raise lalr1.Incomplete (ast)

def _remap_func_Limit (ast): # remap function 'Limit' to native ast representation for pretty rendering
	if ast.is_null_var:
		return AST ('lim', ast, AST.VarNull, AST.VarNull)
	elif not ast.is_comma:
		raise lalr1.Incomplete (AST ('lim', ast, AST.VarNull, AST.VarNull))

	commas = ast.commas
	l      = len (commas)

	if l == 1:
		ast = AST ('lim', commas [0], AST.VarNull, AST.VarNull)
	elif l == 2:
		ast = AST ('lim', commas [0], commas [1], AST.VarNull)
	elif l == 3:
		return AST ('lim', commas [0], commas [1], commas [2], '+')
	elif commas [3].is_str:
		return AST ('lim', *(commas [:3] + _remap_func_Limit_dirs.get (commas [3].str_, ('+',))))
	elif commas [3].is_eq_eq and commas [3].lhs.as_identifier () == 'dir' and commas [3].rhs.is_str:
		return AST ('lim', *(commas [:3] + _remap_func_Limit_dirs.get (commas [3].rhs.str_, ('+',))))
	else:
		ast = AST ('lim', commas [0], commas [1], commas [2])

	if commas [-1].is_null_var:
		return ast

	raise lalr1.Incomplete (ast)

def _remap_func_Matrix (ast):
	if ast.is_brack and ast.bracks:
		if not ast.bracks [0].is_brack: # single layer or brackets, column matrix?
			return AST ('mat', tuple ((e,) for e in ast.bracks))

		elif ast.bracks [0].bracks:
			rows = [ast.bracks [0].bracks]
			cols = len (rows [0])

			for row in ast.bracks [1 : -1]:
				if len (row.bracks) != cols:
					break

				rows.append (row.bracks)

			else:
				l = len (ast.bracks [-1].bracks)

				if l <= cols:
					if len (ast.bracks) > 1:
						rows.append (ast.bracks [-1].bracks + (AST.VarNull,) * (cols - l))

					if l != cols:
						raise lalr1.Incomplete (AST ('mat', tuple (rows)))

					return AST ('mat', tuple (rows))

	return AST ('func', 'Matrix', ast)

def _remap_func_Pow (ast):
	if not ast.is_comma:
		raise lalr1.Incomplete (AST ('^', ast, AST.VarNull))

	if len (ast.commas) == 1:
		raise lalr1.Incomplete (AST ('^', ast.commas [0], AST.VarNull))

	if len (ast.commas) == 2:
		ast = AST ('^', ast.commas [0], ast.commas [1])

		if ast.exp.is_null_var:
			raise lalr1.Incomplete (ast)
		else:
			return ast

	raise SyntaxError ('too many parameters')

def _remap_func_Sum (ast): # remap function 'Sum' to native ast representation for pretty rendering
	if ast.is_null_var:
		return AST ('sum', ast, AST.VarNull, AST.VarNull, AST.VarNull)
	elif not ast.is_comma:
		ast = AST ('sum', ast, AST.VarNull, AST.VarNull, AST.VarNull)

	else:
		commas = ast.commas

		if len (commas) == 1:
			ast = AST ('sum', commas [0], AST.VarNull, AST.VarNull, AST.VarNull)

		else:
			ast2 = commas [1].strip_paren (1)

			if not ast2.is_comma:
				ast = AST ('sum', commas [0], ast2, AST.VarNull, AST.VarNull)
			elif len (ast2.commas) == 3:
				return AST ('sum', commas [0], ast2.commas [0], ast2.commas [1], ast2.commas [2])

			else:
				commas = ast2.commas
				ast    = AST (*(('sum', ast.commas [0], *commas) + (AST.VarNull, AST.VarNull, AST.VarNull)) [:5])

		if commas [-1].is_null_var:
			return ast

	raise lalr1.Incomplete (ast)

def _expr_curly (ast): # convert curly expression to vector or matrix if appropriate
	if ast.op != ',':
		return ast
	elif not ast.commas: # empty {}?
		return AST.VarNull

	c = sum (bool (c.is_vec) for c in ast.commas)

	if not c:
		return AST ('vec', ast.commas)

	if c == len (ast.commas) and len (set (len (c.vec) for c in ast.commas)) == 1:
		return AST ('mat', tuple (c.vec for c in ast.commas))

	raise SyntaxError ('invalid matrix syntax')

#...............................................................................................
class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJztXWuP3LaS/TMLZAZQA82nKH+zHd9cY20n13aCXQwCw3Gci2BjJ+s4d3cR5L9vVZ2SSL261TM9M93Tg+G0SEpFFUt1+KqidHbxxb+9//jjF9UXz5+++PYVHZ++eE2/z54+p99X38rvP15K1tdf0e/fvn3xmBNP/sZ5jx6+pN9vHr588uIZ03714uuXT948' \
			b'/vbls//ka18+fKwHo0fLRE++evP44asnrzT+/OFrjT3K0e9y9BtEpVS+yyMq59858ur1S2HyEf2+EFa/E34ef/38+cOW4mVL0XHKkZdPv/o7F/rw+Tf0++WjZ6+ePXz1d4o+efGlMsSxRzn6XY4qQ0+evXrCh39odlsnLu01GKHb8ZVP/yaClSu/eSZi/vLp' \
			b'd0+/ZPLHX379WuryUCvDonr4+nVHz+kn//GYK/zNy6fP5Ravv6afd28/vf/85tdPb3784ZffP7/9RFnv//e3T28+vP385t2vv5TJT7/+zyD5e5v+7ef3797//q6f/K2fbFO///Hb++42P/3x8d2bt5/+mU/+QNF/ZT4+/vGhjX5+/6mL//Dp7bv/ev+5Tb77' \
			b'49Mv/1cw17tzdy+i6U5QtT+2ibc/dMy9/fy5u/Vvub4/vX33uWQ5s9txVPD8y89d7s8fO7oPf/zy5ucPnVB+/PlfOfrTT1193/+zJKBIx9qPP+ZS3/93V/VfP3b5XW4++eHD217i9y++ry7OVn5d+fV5hYjhiKtWno/WVGepairKcOuqOW/zJKdLrqzlWC3/' \
			b'3lerdJ7TJicpwgRr/HilXxO93NTWfDMuz/DdLMg4F3k5Y2VRkvzbSMzgDEfoaDT/HImV1UxJB/qPlbdSJyoqDHM1vYpSZKS7r+Xu9blmEAdSIGcL48bgxxOVseeDLFNmcpQFLbdwqb295whfkfATzLkmV6aR27rqzBB31vP/eZflyqTxGuE8JifREUtO7y4p' \
			b'FqUjUfay4yhlejn1KOXKHOJTlIb4M7XGzowkzkWuohdE0qZXECBVwOq9upOa2SVWqJQhiRHbFFjqoQpOqkH3hhZNnxeF9osuM/2rVgaPP6hKGhZKXTlXaiad7PJzTo0cn3MSckLOaZAT2xxSK5Fbgx8RybnmQKddwg8L2YFNVh8n2uHq9uS5JinVnpCsJP8+' \
			b'tlXUdJ3TKynJWPyQ6M/Pc5RiDR7p+hwJjjHvTQVds5YlJZgQESm4WREAnyLDiPhdBynWa7kHafeZYY31ldZR9F2g4RgzLnR1pBMOJ6I0WIXM2gykQktH52ObxVGuXoOflT5AjlqpGBV3JkjSMgnKIlF64Ge+0CB5CKI7rMOqP7EDAmmzX3dI0KTpZ5h8F1cF' \
			b'iJWUzrYRpxESdhszaC2kausqKBK5WmCeHkA4p7b9gm5GTTA9mKai08QY8drIA1qzWpPoSSdIDeqKm/mYqthU9bqqXVVTLQM3rlQ3umVtqpouJp1piEdqoOiuDJ/gq8ZWjbSlrIFNJZ0IN6VeHgrJPaUqNawb3CBWoYpVTYFuSsU2gil63iTKWKV1lahkAmas' \
			b'Ql0FagmJq7XI21ekjIZbuaohZrlAKnFNfFHF1nRqTefW/vvqjLLPqV/jmp8L/ORAV5FIGLGcdLiGhCGptZy84Lae04x4PljN9iDyKBG/Sc+hhIi7xEZza7nBsUqwhhhIByClAHFACrZuhYU61yKsI6mYRY08WPfy8Boa2pi7BYGgGAhQ5GBxcMBA0+hzFSU9' \
			b'wRaCM0UgouBnDcTTaKPgAHAnOkLjBxrEHQ7vFzzoO8mnRg8Gba1f5wcD7B4Skx6q5W3BJFHRb6ya+rBYdVB0ow26Aw6SKH7BNJ9LkL1ZazdqtCFFF4CeIaCfMG23KckT0MyzCGHU9Wki86zWkYD2K070aj9FO5Wt83ssM6DMJA1JInm5KpEs6Jn4KoWTeGRJ' \
			b'ARxEvpFuGKtYV9FV0VfRVNGeghio/vWJ1z+deP2bU67/WdQJL/pxo+NhnTKvdRqozaVQSr7OI6iIbqptMce2J9Hhy8IBVfVuV3EtD5UreCIPlepEVb1bdRJk3pXKpLtUmSi1OfZKNEdfCV6rtbIcFtHgCWSOqgIGFfCiUYOJu5cnNFy0Rs+OhcD9M9S0kwth' \
			b'jJcfLZYfLQ8brMibV9344Gow7xLGEA6LBt0sGv0O5tJ3uPc58zqW8lg1ORzGDB6Xa1TJZFhwaMuivOwG9uwhskeI06H1gT1dYixeUxtQt4uLFmuKFsuHeEonM6aspVM5vTXBC14NtlgNPkkBnKH6tXZvdToZlXfSYexPiwqbAi8DS3Oi7UhSiwUMGSniolTr' \
			b'+i7a3KSm/xBBFFFkhNEiOh0TRVwdYQ05i2ozxdJGQPsVGm3GbLvgwd4Z/EzPMWN2mDG71m3AjYZeteQN/QXSRC4nHZJOx6fuuOztFzyYdkc1mJZRtLtbqwA83Lc6HncYjzuMx+nQv9I66FpjR+dkiM50RmHmQztid7DKOtg9+dB43LHBkuABiQKTPA8oRdQ2' \
			b'AMenbQvhNlakANGgnarxyB2ecVpDXgnNXxJZnozNTDoUiw7lNPpyRoTTLtOir+QFuFNBxAUPBk7lSQPvAXgPeUTj77qZo+YqHteoitkcDSyJZY/O3aNz9+LrJ0npu/3hrYvw+EBGDahPBK9UqD/X8Tr6JY+uyKPTka7Ia8uEnqkbtWOEQxobdMATIJMAmYST' \
			b'QLOM306jqqzYQTQoQIOCalA41+4LGtSqQ4Q6RKgDHUgugEmEB1vUC+sjN2tccDVrVLMWIcDSj6lxI+d6pgKuvFxvqgQhJVAnJUh3QSLN8VfCHX0lWJsa9Utfq2P6WjqxdXVBZVHDpVxUSbnqSubZZ2pbNNnKhjaOK+Kljo3Uzk2LApzzvC62LaCXyjZcLxrZ' \
			b'qyNgYmdds6Y6yP2JAeaAWWAeeBWTGeFlTV7XZE963h7BeyN4WwTvK2GrFXvUsjs5+5Kz2zI7B7Ohh3eS8B4E3oDAPvosCJ59cjfG61K8AsSbMHhUwltJeJ2LF7n4IbHtrjEkLNmuJHsEo2xjc7yV0lYr2dZVrYh+Vcv+qUo2DZFyrEgYq0Z2bxlK0MmGt7/J' \
			b'br5qlfgE5fMGPd4TxaUSbeKsNfYe8ta4hu+45sJ5v+Oa9+it+RTdteZ9fHQ5VUtuwzvReEMob2PjfU5Njf1+SYqQjV4rVgzZu2R58xUT8/0r3pIW+Z9zedMlM8o3xH69Fe/VbJgbOkfZte7AIvVcBc7irZ28v5LJmQve4cbX8T4qvjMdibrmrVosFzoVmEGO' \
			b'87/7nlc2WBmnVDCoFrJ5slPEPhqzUnbg6VRTgIehGDrkDZpaYgwTL12WCIUGr0WJQ6vHAlF1ay0Ump4v3OW52W+Ve06hqca8C2qjYocJ5aZ8disXJafzvHOqp+zrQuFDofR0Da9+9hTfQvnZrZo9jNm9mF12OzDwM2C7QhoAo2FJzUCg6UAwgAHdpZEmrx4h' \
			b'omFMND1UNIKLRv8W4KMZ/DFWDAOYaircMmSMQKbpQCO8GD4YN4ZPV1QLIy5nhBwud70RP80QQVJoiHrMSAKWojDUogkMZDQFIIofFd+tWmV0KbcFxqo/Y3qwEr2wdEx/yQCFQMflLgJduHGslUAz2/E1gS22ggm+rhNbC3G1FUvcMovVrgSTJK0cFEwm9NHE' \
			b'6QGKOCuCNOPIoIMxIYcFYCov75HWuPOgDxJm5ruhXgldl9QDUj6/AUcijh6QlCbELpbBpDlFx9RyMAKTUAJDmZEejIx7wA0cqdcDxjypAR3rv2Sj6z2cDglOMjaTsVIBpxpwqjOc6gGcxp0SZ0WQFnCqAac6hyVwqqeDwKkew2nzqK5XwgycuvOb4FSP4ASa' \
			b'ELtYASflq4CTcjCGU53h1DGyEE7+Hk6HBCee7jS8sFXCSZJWDgonjpZwkllSH06cFUGa4cTJJOe6sABO5eU90hp3HsBJmJmHU6+EaTjl8xvgJOLowUlpQuxiGU6aU8Cp5WAEJ5tHeJmRhXAKO8HpQGZY9c6TrE0w2zTJMjc/0doOOS+Q833IeUDOZ8j5AeR8' \
			b'DiPsecGe72PPA3sl3QLszQTBnu9jT6dbwhAucuDbt7cdYbEscQaL3fkNsy6rkPQjSOJciF2sgKTKLoFcUam8jFHpMyozS8tQGe9ReXSojILK2EdlBCpjRmUcoDLmMEJlFFT2VwM5mUyfbgEq43QQVMZpVEagMgKVEagE1RCVZYkzqOzOb0JlBCpHK4pKGrpC' \
			b'SlSq7BLIFZXKyxiVMaMys7QMlfU9Ko8OlTLbs/3ZnsVsz+bZnh3M9viZtWGESpn22f60z2La16NbgMp6Oggq62lUYuon7zsD37697QiVZYkzqOzOb0JlDVSOZoNKGmIXK1CprCaQKyqVlzEq84SwYGkZKtPeUTky0d0cNv08PMPdRKiTCaTrTyAdJpAuTyDd' \
			b'YALpbA5DhDqZSTrMJNk8RSBtgFOH+WSPejtOy8t7pLXDATjleyhMHaaUeFkkUu1dm3H/WZbZzHah+bYbwCqnUfk+WJU0xC6WwdqKEW+3VLBq5hisLk83C5YmwBqbB7KUNsZsw5jNBuYrYtceaqdqe/3qFgv2bSCY373SWbyvjGQ3YQSXF8uOjYCc3SLbDZBd' \
			b'hCGyEy6PKDZ3v6Ljpk+6ANZuOgis3WT3KzwJpeDaAde4fAjqtjijdB2qN9rZ28I2QNwB4m4EcZCGrpAS4q4zwwt9kIfcWuP1+gmsu4z1TjxDrHMdCeN8IIg79xf2Ge6jWz5YaN/R8bITY6PrGxsdjI0uGxvdwNjoQg4j2/1aciOKKTALw2OPdAFmw3QQzIZp' \
			b'zML4KC8dBuu+ve0Is2WJM71wd34TRAMgOrJHKmmIXayAqIovgVx7YeVljMxskixYWjZkNuZ+Jnt0yJT1JddfX3JYX3J5fckN1pco3YXROFnWl1x/fclhfalHtwCWcToILKfXlxzWlxzWlxzWl5RqCMuyxBlYduc3wRLrS260vqSkoSukhKXKLoFcYam8jGGZ' \
			b'15cKlhbCcjfPm4OF5YZJ7J1EZhJkpj4ydZybMjLTAJkphxEykyAz9ZGZgMySbgEy03QQZKYOmVIJBWYCMBOAmQDMjm6IzbLMGWxm2g3YTMBmGmETpCF2sQKbKj0tXbGpvIyxmTI2M0s7TVzNbt489xA9DIiynsmSXglRSVo5KETlSxEFROW7PBqGEOWsiDIy' \
			b'RDmZTJ9uO0TLy3uktcMBEJVKAKLCjxCusFTJEM10A4j2ypyGaEE7D1E5jTr3IaqkIXaxDNFWegnkgGjLywiiQgyIFiztBtHdPITuIXogEBWHcf4tIWoAUZMhagYQNTmMICpbKaSMAqIGEC3pFkDUTAeBqMkQNRmiBhA1gKgBRDu6IUTLczMQzbQbIGoAUTOC' \
			b'KEhD7GIFRFV6CeQKUeVlDFGTIZpZ2g2i+/c6urfZ3CRWxWbj+zYbD5uNzzYbP7DZeJvDCKtis/Gw2chn4PRrcCg4mT71AsTa6SCIzTYbqYoiFjYbD5uNh80m0w0ROyh2BrSZfANoYbPxI5uNkobYxQrQqhgTyBW0yssYtNlmU7C0G2j375R0D9qbBK24Dfq+' \
			b'26CH26DPboN+4DbIj6QNI9CK26CH26B40CLlUHAyfeoFoJ0JAtrsPChVUdDCd1Dddz18BzPdELSSa8Cfn3UhLOg3oBYuhH7kQqikIXaxArUqxwRyRa3yMkZtdiEsWNoNtft3WrpH7U2iVgwyvm+Q8TDI+GyQ8QODjA85jFAr1hgPawwfHFIOVyfTp16A2jAd' \
			b'BLXZJiNVUdTCJONhkvEwyWS6IWoHxc6ANpNvAC0MM35kmFHSELtYAVoVYwK5glZ5GYM2G2YKlnYD7b1P03GDVmw1vm+r8bDV+Gyr8QNbDT+MNoxAK7YaD1uNh0+T1xktLDY96gWgjdNBQJstNj77NHkYbDwMNh4Gm0w3BO2g2BnQZvINoIXZxo/MNkoaukJK' \
			b'0KoY9aO7ClrlZQzabLYpWNoNtM09aI8atOKv5Puuwh6uwj67CvuBqzA/iTaMQCuuwh6uwnxwSDkUnEyfegFo6+kgoM0Ow1IVBS38hT38hT38hTPdELSDYmdAm8k3gBZew37kNaykIXaxArTKsH4ZW0GrvIxBm72GC5Z2Aq3dj5tS8Xqem8Ct0ZcP3aM3b+tm' \
			b'x4LK9F85Ikkrh3Zb9+CdI6bJYbS/W946Qr8NJrgGi8hyQNnJ9AtYsNG7mQ6y0bvpAGzgJmH4+9eyu6wGgx53V3aLu4+2gA+Kn9kFnsnngSynUe0+kJU0xC6WgdxKNIEcQG55GQFZiAHkgqXdgLwflyZ7JB1wvJsotjLbtf3ZrsVs1+bZrh3Mdmu5SC8duh8a' \
			b'yY0oBrQOKQeCZDK1XTThLS/vkdYOB6DY5gmvxYTXYsJrMeHNdMOdO/1im1mbUFHChv07mPPa0ZxXSUPsYsX+HRVmAjkArJkT+3fynLdgaTcA79/56WDRexehKy9vY2GW0A2w34Zsvw0D+y1Lvw1D6Aax3wbYb/ngkHIoOJk+9XbcBjMdGLchW3FDtuIGWHED' \
			b'rLgBVtxMN8DtsNhp0Bbk86ANMOSGkSFXSUPsYhm0rRgTyAHalpcRaEM25BYs7QbaLe5QdR+39h66hwhdIw6Mpu/AaODAGDF2ZmQ0uKZFL79qkkfQXBpfZsZujEbcGA3cGPngkHIoPhmlRlgyfE7TQYbP2ZnRZGdGA2dGA2dGA2fGTDccNg+KnRk2Z/INw2b4' \
			b'M5qRP6OShtjFimEzcryWrsNm5WU8bM7+jAVLuwF4/85S99C9yV7XSa/b32QnSRFu1+sO9tiFIox6XdlgF7DBjg8OKYeCk+lTL+h13XSQXjdvs5OqaK+LXXYBu+wCdtllumGvOyh2ptfN5Bt6XWytC6OtdUoaYhcrel0VYwK59rrKy7jXzTvqCpZ2A+29+9QI' \
			b'tFaB648JvDLbDf3ZbsBsN+TZbhjMdkPIYQRemeoGTHUDproBU92AqW6PegF4w3QQ8OapbshT3YCpbsBUN2Cqm+mG4B0UOwPeTC4kjF8peQLCmO2G0WxXCwixixUQVmEmkCuElaMxhPNst2BsNwjH6uKaX7J+LW9YDzPwshOw2vUt6wqdyTeti+TZclfd8kvW' \
			b'r/kF61zHmdcHXvEl66q7My9aJ+Il+tjrV67+3n97Y6/+57H/VV7/X/M7WkOhnDzAD9XwcwDpUlp6PZo68TkAFtXNfhKABXqFzwKgH83rFG0/OtTetGNrGvb01QqMadIhtazrDUocZ1rXfXzDYsKAtufvWLQWMH331R6U18yMIXZsbo1wO63AabrJpSGCDQ9I' \
			b'5n/h67VXGgyEvX50xd3Kd1dCmtfba9PZCX0VI+z+dHZDQ2t6G2Zv6vsrLNTdvsFCwr3uoepS1cTEcF/ayW/mYWfweM1j1+P+QpDREcp+NFXeOCVYH20i3XF4YDZoLbWutX1ABcr3F0x1cQjTLFPJCvY6LHsd2F4/aMUVDbs0rreuqpeYZ2ERh51frarqTX3Q' \
			b'Cnc1uzSq9hCUsvtAnLtG3XQL9JPi0Z2OnvJda1lsXFGVr0FfU9jenCZ2G+e7u1111+1Hd/3V21S7Z92dWh1uV4XnBq7NgbaxixyKL6e/rDVxb7obRy7CorsxzOovj7dEh3fXXb8f3Q1X191Sb+M1jQk26O1p6WyprwYu/PseH2zQ10vqatiPrsb96mp9r6s3' \
			b'qavpOHQ17kdX543Nl9LVdK+rN6mrzXHoan0Ic6+bXwQ4FGW8RiOrhbvGoXzBuvqTnu4DgoKsQ6XTUjt/2eVSx15FR6p917rcxN5GlzDvV3+GBwRo0cHmEHSQ5N6tPO1bG0tfriUrTne6UTTysjsnq037XmGyu60yLe6d6b7LVbS+gpbWfffEK7WXm9yG9+ga' \
			b'xV4o4jS/Zw1NUFLRlH3oqJSnaqpegftoQTc47u7PQcqwGriZhtQ21JJa+QzxLlalezXdj5p6qKnfl5r6I1ZT9qH229XUVheHMOC8ifnNYl/SdERdOBTu2uczix1FSRAXt69OB6NKzVGp0YGokD8EFbqlFom9BWQz5HpGpfj535pKxfVuGsXX71uphIdZnWLP' \
			b'6xWv9s10fTE9kB2gwdIxSRcYqovbVrZDaa8KzYr3bdX2hRNZvQuiRfFei7omyh5Nlxcl3LYaUZskz+/Bih9beLBCw1Tfq1SnUu54VMpVYnI6SJVK1YXhzb4kUl4wWMt4q5FXPPBnPnfSo6bUFNGKersG8FMfP3HpevQxijwv/dRQSjkXd5D7FjnXU3Jl6VDF' \
			b'VTqXXKapF67OXHn1ZROmzEjKAWsl4Yow4QJ2Xh+54grIPBZkxTn0VjjocbTP7xIPb3sTeW2PrP+44j6atN2sVdfxgPTp8CBcPgNMwr4QUfNrZtZSWS+oc5oPIXOTdlFuVGDPzlh/f07ZZyt5tZ+Rd5KRMKjKshGES5QtpLJniedV2M3Bxa/sHImtij+51BWX' \
			b'yjdkve29/YA3jCcuonw1gbiKdsYmfWkAXgjAXwSs+K/hXTPw+w/9f+nziZg3/TlcLDtU5byBZYrj7EOCnafCqd8/p0S9y5+wERawUS/lhF+u0HETqqk/XteeOUMDHToKV/HauKLB1K5/wpF8ecGERUwRqoZ88asttvIm1oF65o8XOYoUYXFwhbCZdmMTL/q4' \
			b'FLOp2vTXDkY3XCP8NpfhFy8m2Z1r3YHcvcFDmrFq59COr5dTDEbIXHF8Ur251bobnl6InelmAipubr/itrrZgIrbq1Q8hlHd21fm7F5/V10+8KxykMUTxUXUkINTObg9iiJtFwdzOS8SHuzxVBuRq4cNRU2dgmT8IUomVrcaIJkwlEzxHiyIyOFDpIsFFaWT' \
			b'puqy7bV7eVX/hVX9N1MxknmIYTZLkofBs9Lkmc3tBRqaiy/fLkSQfzxAzeRFtdsMkEy9VTN3ElFPIWfFdSUVdFUZaL6HX0R2DTydBjFPpKcvCTMlT90RQk1HJ9RUHWqARJujk2hTHWrAosT62CTqsGZ8iAESNUcnUVMdaoBE7dFJ1FeHGiDR0eTlChLdOgTd' \
			b'o1zral+BbR/DLP7UylULhnxHU6CbH+hfTdBNtTngPbhbL1se2GBxKUoI/ABmVlcSOBuEjiNA3qOZ1LHJO1VHEiDv7fOzA5d3Ux1JgLy3T90OW95sVz6OAHlvn9gduLxtdSQBBubt077jWIlkg/0xBUjfZJeoyAJDLk1z+DHIM4AQjTgpsDuI+IJ0zh4RrRS/' \
			b'9Yo9hBr2+DGJfQlY8jXkm7DoLK8XYseOBl2JvMJF0loIvyaDRW/FkMgWF9URfidB8ezpIckVVl8OVONlFkGLSdNXu2rwj6ub0dX84IXCV6P/CLnxPkxTe76qpsp8f/7/LT50DQ==' 

	_PARSER_TOP             = 'expr_commas'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	_TEXGREEK = '(?:' + '|'.join (reversed (sorted (f'\\\\{g}' for g in AST.Var.GREEK))) + ')'
	_LETTER   = fr'[a-zA-Z]'
	_VARPY    = fr'(?:{_LETTER}(?:\w|\\_)*)'
	_VARTEX   = fr'(?:{_TEXGREEK}|\\partial|(?:(?:\\overline|\\bar|\\widetilde|\\tilde)\s*)?\\infty)'
	_VARTEX1  = fr'(?:(\d)|({_LETTER})|({_VARTEX}))'
	_VAR      = fr'(?:{_VARPY}|{_VARTEX})'

	_STR      = r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY - {'@'})))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LETTER})'),
		('LOG',           r'log\b|\\log(?!{_LETTER})'),
		('FUNC',         fr'(@|{_FUNCPY}\b)|\\({_FUNCTEX})\b|\$({_LETTER}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}}'),
		('LIM',          fr'\\lim(?!{_LETTER})'),
		('SUM',          fr'\\sum(?!{_LETTER})'),
		('INT',          fr'\\int(?:\s*\\limits)?(?!{_LETTER})'),
		('LEFT',         fr'\\left(?!{_LETTER})'),
		('RIGHT',        fr'\\right(?!{_LETTER})'),
		('CDOT',         fr'\\cdot(?!{_LETTER})'),
		('TO',           fr'\\to(?!{_LETTER})'),
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
		('IF',            r'if(?!{_LETTER})'),
		('ELSE',          r'else(?!{_LETTER})'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
		('VAR',          fr'(\\partial)\s?({_VAR})|{_VAR}'),
		('ATTR',         fr'\.(?:({_LETTER}\w*)|\\text\s*{{\s*({_LETTER}\w*)\s*}})'),
		('STR',          fr"(?<!\d|{_LETTER}|')({_STR})|\\text\s*{{\s*({_STR})\s*}}"),
		('PRIMES',        r"'+"),
		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
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
		('INEQ',          r'==|!=|\\neq?|<=|\\le|<|\\lt|>=|\\ge|>|\\gt'),
		('EQ',            r'='),
		('DIVIDE',        r'/'),
		('EXCL',          r'!'),
		('AMP',           r'&'),
		('DBLSLASH',      r'\\\\'),
		('COMMA',         r','),
		('ignore',        r'\\,|\\:|\\?\s+|\\text\s*{\s*[^}]*\s*}'),
	])

	_FUNC_AST_REMAP = {
		'Abs'       : lambda expr: _expr_func (1, '|', expr, strip_paren = 1),
		'abs'       : lambda expr: _expr_func (1, '|', expr, strip_paren = 1),
		'Derivative': lambda expr: _expr_func_remap (_remap_func_Derivative, expr),
		'diff'      : lambda expr: _expr_func_remap (_remap_func_Derivative, expr),
		'exp'       : lambda expr: _expr_func (2, '^', AST.E, expr, strip_paren = 1),
		'factorial' : lambda expr: _expr_func (1, '!', expr, strip_paren = 1),
		'Integral'  : lambda expr: _expr_func_remap (_remap_func_Integral, expr),
		'integrate' : lambda expr: _expr_func_remap (_remap_func_Integral, expr),
		'Limit'     : lambda expr: _expr_func_remap (_remap_func_Limit, expr),
		'limit'     : lambda expr: _expr_func_remap (_remap_func_Limit, expr),
		'Matrix'    : lambda expr: _expr_func_remap (_remap_func_Matrix, expr),
		'ln'        : lambda expr: _expr_func (1, 'log', expr),
		'Pow'       : lambda expr: _expr_func_remap (_remap_func_Pow, expr),
		'pow'       : lambda expr: _expr_func_remap (_remap_func_Pow, expr),
		'Sum'       : lambda expr: _expr_func_remap (_remap_func_Sum, expr),
	}

	def expr_commas_1   (self, expr_comma, COMMA):                              return expr_comma if expr_comma.is_comma else AST (',', (expr_comma,))
	def expr_commas_2   (self, expr_comma):                                     return expr_comma
	def expr_commas_3   (self):                                                 return AST (',', ())
	def expr_comma_1    (self, expr_comma, COMMA, expr):                        return AST.flatcat (',', expr_comma, expr)
	def expr_comma_2    (self, expr):                                           return expr

	def expr            (self, expr_eq):                                        return expr_eq

	def expr_eq_1       (self, expr_cond1, EQ, expr_cond2):                     return AST ('=', '=', expr_cond1, expr_cond2)
	def expr_eq_2       (self, expr_cond):                                      return expr_cond

	def expr_cond_1     (self, expr_ineq, IF, expr, ELSE, expr_cond):
		return \
				AST ('piece', ((expr_ineq, expr),) + expr_cond.pieces) \
				if expr_cond.is_piece else \
				AST ('piece', ((expr_ineq, expr), (expr_cond, True))) \

	def expr_cond_2     (self, expr_ineq, IF, expr):                            return AST ('piece', ((expr_ineq, expr),))
	def expr_cond_3     (self, expr_ineq):                                      return expr_ineq

	def expr_ineq_2     (self, expr_add1, INEQ, expr_add2):                     return AST ('=', AST.Eq.LONG2SHORT.get (INEQ.text, INEQ.text), expr_add1, expr_add2)
	def expr_ineq_3     (self, expr_add):                                       return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2      (self, expr_add, MINUS, expr_mul_exp):                  return AST.flatcat ('+', expr_add, expr_mul_exp.neg (stack = True))
	def expr_add_3      (self, expr_mul_exp):                                   return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_neg):                   return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_2  (self, expr_mul_exp, STAR, expr_neg):                   return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_3  (self, expr_neg):                                       return expr_neg

	def expr_neg_1      (self, MINUS, expr_diff):                               return expr_diff.neg (stack = True)
	def expr_neg_2      (self, expr_diff):                                      return expr_diff

	def expr_diff       (self, expr_div):                                       return _expr_diff (expr_div)

	def expr_div_1      (self, expr_div, DIVIDE, expr_mul_imp):                 return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2      (self, expr_div, DIVIDE, MINUS, expr_mul_imp):          return AST ('/', expr_div, expr_mul_imp.neg (stack = True))
	def expr_div_3      (self, expr_mul_imp):                                   return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_int):                         return _expr_mul_imp (expr_mul_imp, expr_int)
	def expr_mul_imp_2  (self, expr_int):                                       return expr_int

	def expr_int_1      (self, INT, expr_sub, expr_super, expr_add):            return _expr_int (expr_add, (expr_sub, expr_super))
	def expr_int_2      (self, INT, expr_add):                                  return _expr_int (expr_add)
	def expr_int_3      (self, expr_lim):                                       return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                           return AST ('lim', expr_neg, expr_var, expr)
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):   return AST ('lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg):  return AST ('lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6      (self, expr_sum):                                                                         return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQ, expr, CURLYR, expr_super, expr_neg):               return AST ('sum', expr_neg, expr_var, expr, expr_super)
	def expr_sum_2      (self, expr_func):                                                                        return expr_func

	def expr_func_1     (self, SQRT, expr_func_arg):                            return _expr_func (1, 'sqrt', expr_func_arg)
	def expr_func_2     (self, SQRT, BRACKL, expr, BRACKR, expr_func_arg):      return _expr_func (1, 'sqrt', expr_func_arg, expr)
	def expr_func_3     (self, LOG, expr_func_arg):                             return _expr_func (1, 'log', expr_func_arg)
	def expr_func_4     (self, LOG, expr_sub, expr_func_arg):                   return _expr_func (1, 'log', expr_func_arg, expr_sub)
	def expr_func_5     (self, FUNC, expr_func_arg):
		func  = _FUNC_name (FUNC)
		remap = self._FUNC_AST_REMAP.get (func)

		return remap (expr_func_arg) if remap else _expr_func (2, 'func', func, expr_func_arg)

	def expr_func_6     (self, FUNC, expr_super, expr_func_arg):
		ast = self.expr_func_5 (FUNC, expr_func_arg)

		return \
				AST ('^', ast, expr_super) \
				if expr_super != AST.NegOne or not ast.is_trigh_func_noninv else \
				AST ('func', f'a{ast.func}', ast.arg)

	def expr_func_7     (self, expr_fact):                                      return expr_fact

	def expr_func_arg_1 (self, expr_func):                                      return expr_func
	def expr_func_arg_2 (self, MINUS, expr_func):                               return expr_func.neg (stack = True)

	def expr_fact_1     (self, expr_fact, EXCL):                                return AST ('!', expr_fact)
	def expr_fact_2     (self, expr_pow):                                       return expr_pow

	def expr_pow_1      (self, expr_pow, expr_super):                           return AST ('^', expr_pow, expr_super)
	def expr_pow_2      (self, expr_attr):                                      return expr_attr

	def expr_attr_1     (self, expr_attr, ATTR):                                return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1])
	def expr_attr_2     (self, expr_abs):                                       return expr_abs

	def expr_abs_1      (self, LEFT, BAR1, expr, RIGHT, BAR2):                  return AST ('|', expr)
	def expr_abs_2      (self, BAR1, expr, BAR2):                               return AST ('|', expr)
	def expr_abs_3      (self, expr_paren):                                     return expr_paren

	def expr_paren_1    (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):       return AST ('(', expr_commas)
	def expr_paren_2    (self, PARENL, expr_commas, PARENR):                    return AST ('(', expr_commas)
	def expr_paren_3    (self, IGNORE_CURLY, CURLYL, expr, CURLYR):             return expr
	def expr_paren_4    (self, expr_frac):                                      return expr_frac

	def expr_frac_1     (self, FRAC, expr_piece1, expr_piece2):                 return AST ('/', expr_piece1, expr_piece2)
	def expr_frac_2     (self, FRAC1, expr_piece):                              return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_piece)
	def expr_frac_3     (self, FRAC2):                                          return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4     (self, expr_piece):                                     return expr_piece

	def expr_piece_1    (self, BEG_CASES, expr_pieces, END_CASES):              return AST ('piece', expr_pieces)
	def expr_piece_2    (self, expr_mat):                                       return expr_mat
	def expr_pieces_1   (self, expr_piecesp, DBLSLASH):                         return expr_piecesp
	def expr_pieces_2   (self, expr_piecesp):                                   return expr_piecesp
	def expr_piecesp_1  (self, expr_piecesp, DBLSLASH, expr_piecesc):           return expr_piecesp + (expr_piecesc,)
	def expr_piecesp_2  (self, expr_piecesc):                                   return (expr_piecesc,)
	def expr_piecesc_1  (self, expr1, AMP, expr2):                              return (expr1, expr2)
	def expr_piecesc_2  (self, expr, AMP):                                      return (expr, True)

	def expr_mat_1      (self, LEFT, BRACKL, BEG_MAT, expr_mat_rows, END_MAT, RIGHT, BRACKR):  return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_2      (self, BEG_MAT, expr_mat_rows, END_MAT):                               return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_3      (self, BEG_BMAT, expr_mat_rows, END_BMAT):                             return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_4      (self, BEG_VMAT, expr_mat_rows, END_VMAT):                             return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_5      (self, BEG_PMAT, expr_mat_rows, END_PMAT):                             return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_6      (self, expr_curly):                                                    return expr_curly
	def expr_mat_rows_1 (self, expr_mat_row, DBLSLASH):                         return expr_mat_row
	def expr_mat_rows_2 (self, expr_mat_row):                                   return expr_mat_row
	def expr_mat_rows_3 (self):                                                 return ()
	def expr_mat_row_1  (self, expr_mat_row, DBLSLASH, expr_mat_col):           return expr_mat_row + (expr_mat_col,)
	def expr_mat_row_2  (self, expr_mat_col):                                   return (expr_mat_col,)
	def expr_mat_col_1  (self, expr_mat_col, AMP, expr):                        return expr_mat_col + (expr,)
	def expr_mat_col_2  (self, expr):                                           return (expr,)

	def expr_curly_1    (self, CURLYL, expr_commas, CURLYR):                    return _expr_curly (expr_commas)
	def expr_curly_2    (self, expr_bracket):                                   return expr_bracket

	def expr_bracket_1  (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):       return AST ('[', expr_commas.commas if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_2  (self, BRACKL, expr_commas, BRACKR):                    return AST ('[', expr_commas.commas if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_3  (self, expr_term):                                      return expr_term

	def expr_term_1     (self, STR):                                            return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_2     (self, SUB):                                            return AST ('@', '_') # for last expression variable
	def expr_term_3     (self, expr_num):                                       return expr_num
	def expr_term_4     (self, expr_var):                                       return expr_var

	def expr_num        (self, NUM):                                            return AST ('#', NUM.text) if NUM.grp [0] or NUM.grp [2] else AST ('#', NUM.grp [1])

	def expr_var_1      (self, var, PRIMES):                                    return AST ('@', var + PRIMES.text.replace ("'", '_prime'))
	def expr_var_2      (self, var):                                            return AST ('@', var)
	def var             (self, VAR):
		return \
				'partial' + AST.Var.TEX2PY.get (VAR.grp [1], VAR.grp [1].replace ('\\_', '_')) \
				if VAR.grp [0] else \
				AST.Var.TEX2PY.get (VAR.text.replace (' ', ''), VAR.text.replace ('\\_', '_'))

	# def expr_var_1      (self, var, PRIMES, subvar):                            return AST ('@', f'''{var}{subvar}{PRIMES.text.replace ("_prime", "'")}''')
	# def expr_var_2      (self, var, subvar, PRIMES):                            return AST ('@', f'''{var}{subvar}{PRIMES.text.replace ("_prime", "'")}''')
	# def expr_var_3      (self, var, PRIMES):                                    return AST ('@', f'''{var}{PRIMES.text.replace ("_prime", "'")}''')
	# def expr_var_4      (self, var, subvar):                                    return AST ('@', f'{var}{subvar}')
	# def expr_var_5      (self, var):                                            return AST ('@', var)

	# def var_2           (self, VAR):
	# 	return \
	# 			f'\\partial {VAR.grp [2]}' \
	# 			if VAR.grp [1] and VAR.grp [1] != 'd' else \
	# 			AST.Var.SHORT2LONG.get (VAR.grp [0] or VAR.grp [3], VAR.text)

	# def subvar_1        (self, SUB, CURLYL, expr_var, CURLYR):                  return f'_{expr_var.var}' if expr_var.var and expr_var.is_single_var else f'_{{{expr_var.var}}}'
	# def subvar_2        (self, SUB, CURLYL, NUM, CURLYR):                       return f'_{{{NUM.text}}}'
	# def subvar_3        (self, SUB, CURLYL, NUM, subvar, CURLYR):               return f'_{{{NUM.text}{subvar}}}'
	# def subvar_4        (self, SUB1):                                           return f'_{AST.Var.SHORT2LONG.get (SUB1.grp [1] or SUB1.grp [3], SUB1.text [1:])}'

	def expr_sub_1      (self, SUB, expr_frac):                                 return expr_frac
	def expr_sub_2      (self, SUB1):                                           return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1    (self, DBLSTAR, expr_func):                             return expr_func
	def expr_super_2    (self, DBLSTAR, MINUS, expr_func):                      return expr_func.neg (stack = True)
	def expr_super_3    (self, CARET, expr_frac):                               return expr_frac
	def expr_super_4    (self, CARET1):                                         return _ast_from_tok_digit_or_var (CARET1)

	def caret_or_dblstar_1 (self, DBLSTAR):                                     return '**'
	def caret_or_dblstar_2 (self, CARET):                                       return '^'

	#...............................................................................................
	_AUTOCOMPLETE_SUBSTITUTE = { # autocomplete means autocomplete AST tree so it can be rendered, not necessarily expression
		'CARET1'             : 'CARET',
		'SUB1'               : 'SUB',
		'FRAC2'              : 'FRAC',
		'FRAC1'              : 'FRAC',
		'expr_super'         : 'CARET',
		'caret_or_doublestar': 'CARET',
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
				self.tokens.insert (tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, ('', '', '', '')))
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
			elif len (self.stack [-1].red.commas) == 1 or self.tokens [self.tokidx - 1] != 'COMMA':
				return self._insert_symbol (('CURLYR', 'COMMA', 'CURLYR'))
			else:
				return self._mark_error (('CURLYR', 'CURLYR'))

		if self.stack [-3].sym != 'COMMA' or self.stack [-4].sym != 'expr_comma' or self.stack [-5].sym != 'CURLYL':
			if self.stack [-1].red.is_vec:
				return self._insert_symbol (('COMMA', 'CURLYR'), 1)
			elif self.stack [-1].red.is_comma:
				if len (self.stack [-1].red.commas) == 1 or self.tokens [self.tokidx - 1] != 'COMMA':
					return self._insert_symbol ('CURLYR')
				else:
					return self._mark_error ('CURLYR')

		else:
			cols = \
					len (self.stack [-4].red.vec)             if self.stack [-4].red.is_vec else \
					len (self.stack [-4].red.commas [0].vec)  if self.stack [-4].red.is_comma and self.stack [-4].red.commas [0].is_vec else \
					None

			if cols is not None:
				vec             = self.stack [-1].red.commas if self.stack [-1].red.is_comma else (self.stack [-1].red,)
				self.stack [-1] = lalr1.State (self.stack [-1].idx, self.stack [-1].sym, AST (',', vec + (AST.VarNull,) * (cols - len (vec))))

				return self._mark_error (('CURLYR', 'CURLYR')) if len (vec) != cols else self._insert_symbol (('CURLYR', 'CURLYR'))

		return self._insert_symbol ('CURLYR')

	def _parse_autocomplete_expr_int (self):
		s               = self.stack [-1]
		self.stack [-1] = lalr1.State (s.idx, s.sym, AST ('*', (s.red, AST.VarNull)))
		expr_vars       = set ()
		expr_diffs      = set ()
		expr_parts      = set ()

		if self.autocompleting:
			stack = [s [2]]

			while stack:
				ast = stack.pop ()

				if ast.is_var:
					(expr_diffs if ast.is_diff else expr_vars if not ast.is_part_any else expr_parts).add (ast.var)
				else:
					stack.extend (filter (lambda a: isinstance (a, tuple), ast))

		expr_vars = expr_vars - {'_', AST.E.var, AST.I.var, AST.Pi.var, AST.Infty.var, AST.CInfty.var} - set (var [1:] for var in expr_diffs)

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

		if pos == 1 and rule == ('expr_func', ('FUNC', 'expr_func_arg')): # and _FUNC_name (self.stack [-1].sym) in AST.Func.NO_PARMS:
			return self._insert_symbol (('PARENL', 'PARENR'))

		if pos and rule [1] [pos - 1] == 'expr_commas':
			return self._parse_autocomplete_expr_commas (rule, pos)

		assert rule [1] [pos - 1] != 'expr_comma'

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_int':
				return self._parse_autocomplete_expr_int ()

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

		lalr1.Parser.parse (self, text)

		if not self.parse_results:
			return (None, 0, [])

		rated = sorted ((r is None, -e if e is not None else float ('-inf'), len (a), i, (r, e, a)) \
				for i, (r, e, a) in enumerate (self.parse_results))

		if os.environ.get ('SYMPAD_DEBUG'):
			rated = list (rated)
			print ()
			for res in rated:
				print ('parse:', res [-1])

		return next (iter (rated)) [-1]

class sparser: # for single script
	Parser = Parser

# if __name__ == '__main__':
# 	p = Parser ()
# 	a = p.parse ('\\frac1x')
# 	print (a)
