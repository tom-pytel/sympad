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

def _expr_mul_imp (expr_mul_imp, expr_int):
	if expr_mul_imp.is_attr: # x.y * () -> x.y()
		if expr_mul_imp.arg is None:
			if expr_int.is_paren:
				return AST ('.', expr_mul_imp.obj, expr_mul_imp.attr, expr_int.strip_paren (1))
			elif expr_int.is_attr:
				return AST ('.', _expr_mul_imp (expr_mul_imp, expr_int.obj), expr_int.attr)

	elif expr_mul_imp.is_pow: # x^y.z * () -> x.{y.z()}
		if expr_mul_imp.exp.is_attr and expr_mul_imp.exp.arg is None:
			if expr_int.is_paren:
				return AST ('^', expr_mul_imp.base, ('.', expr_mul_imp.exp.obj, expr_mul_imp.exp.attr, expr_int.strip_paren (1)))
			elif expr_int.is_attr:
				return AST ('^', expr_mul_imp.base, ('.', _expr_mul_imp (expr_mul_imp.exp, expr_int.obj), expr_int.attr))

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

def _expr_func_xlat (_xlat_func, ast): # rearrange ast tree for a given function translation like 'Derivative' or 'Limit'
	expr = _expr_func (1, None, ast, strip_paren = None) # strip all parentheses

	if expr.op is None:
		return _xlat_func (expr [1])
	else:
		return AST (expr.op, _xlat_func (expr [1] [1]), *expr [2:])

_xlat_func_Limit_dirs = {'+': ('+',), '-': ('-',), '+-': ()}

def _xlat_func_Derivative (ast): # translate function 'Derivative' to native ast representation for pretty rendering
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

def _xlat_func_Integral (ast): # translate function 'Integral' to native ast representation for pretty rendering
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

def _xlat_func_Limit (ast): # translate function 'Limit' to native ast representation for pretty rendering
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
		return AST ('lim', *(commas [:3] + _xlat_func_Limit_dirs.get (commas [3].str_, ('+',))))
	elif commas [3].is_eq_eq and commas [3].lhs.as_identifier () == 'dir' and commas [3].rhs.is_str:
		return AST ('lim', *(commas [:3] + _xlat_func_Limit_dirs.get (commas [3].rhs.str_, ('+',))))
	else:
		ast = AST ('lim', commas [0], commas [1], commas [2])

	if commas [-1].is_null_var:
		return ast

	raise lalr1.Incomplete (ast)

def _xlat_func_Matrix (ast):
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

def _xlat_func_Piecewise (ast):
	pcs = []

	if ast.is_comma and ast.commas and ast.commas [0].strip_paren ().is_comma:
		for c in ast.commas [:-1]:
			c = c.strip_paren ()

			if not c.is_comma or len (c.commas) != 2:
				raise SyntaxError ('expecting tuple of length 2')

			pcs.append (c.commas)

		ast = ast.commas [-1].strip_paren ()

	pcs = tuple (pcs)

	if not ast.is_comma:
		raise lalr1.Incomplete (AST ('piece', pcs + ((ast, AST.VarNull),)))
	if len (ast.commas) == 0:
		raise lalr1.Incomplete (AST ('piece', pcs + ()))

	if not ast.commas [0].strip_paren ().is_comma:
		if len (ast.commas) == 1:
			raise lalr1.Incomplete (AST ('piece', pcs + ((ast.commas [0], AST.VarNull),)))
		if len (ast.commas) == 2:
			return AST ('piece', pcs + ((ast.commas [0], True if ast.commas [1] == AST.True_ else ast.commas [1]),))

		raise SyntaxError ('invalid tuple length')

def _xlat_func_Pow (ast):
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

def _xlat_func_Sum (ast): # translate function 'Sum' to native ast representation for pretty rendering
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
			b'd0+/ZPLHX379WuryUCvDonryH4+ftfScfvhaqvrNy6fP5Ravv6afd28/vf/85tdPb3784ZffP7/9RFnv//e3T28+vP385t2vv5TJT7/+zyD5e5v+7ef3797//q6f/K2fbFO///Hb++42P/3x8d2bt5/+mU/+QNF/ZT4+/vGhjX5+/6mL//Dp7bv/ev+5Tb77' \
			b'49Mv/1cw17tzdy+i6U5QtT+2ibc/dMz99PZdJs71ffv5c4/lzG7HUcHzLz93uT9/7Ir78Mcvb37+0Anlx5//laM//dTV9/0/SwKKdDz8+GMu9f1/d1X/9WOX3+Xmkx8+vO0lfv/i++ribOXXlV+fV4gYjrhq5floTXWWqqaiDLeumvM2T3K65MpajtXy7321' \
			b'Suc5bXKSInQ0CT/BnGtyZRopqeabcXmG72ZBxrnIyxkrKyVZ+beRmMEZjnCRmo/y6WrNlHSg/1h5K3WiosIwV9OrKEVGuvta7l6fawZxIAVytkjLGPx4ojL2fJBlykyOsqDlFi61t/cc4dLX+PEqW7qFlVtYV50Z4s56/j/vslyZNF4jnMf3I9ERS07vLikW' \
			b'pSNR9rLjKGV6OfUo5coceoaiNMSfqTV2ZiRxLnIVvSCSNr2CAKkCVu/VndTMLrFCpQxJjNimwFIPVXBSDbo3JDV9XhTaL7rM9K9aGTz+oCppWCh15VypmXSyy885NXJ8zknICTmnQU5sc0itRG4NfkQk55oDnXYJPyxkBzZZfZwgx9XtyXNNUqo9IVlJ/n1s' \
			b'q6jpOqdXUpKx+CHRn5/nKMUaPNL1ORIcY96bCrpmLUtKMCEiUgVmRQB8igwj4ncdpFiv5R6k3WeGNdZXWkfRd4GGY8y40NWRTjiciNJgFTJrM5AKLR2dj20WR7l6DX5W+gA5aqViVNyZIEnLJCij9aLCfaFB8hBEd1iHVX9iBwTSZr/ukKBJ088w+S6uChAr' \
			b'KZ1tI04jJOw2ZqTmRqq2roIikasF5ukBhHNq2y/oZtQE04NpKjpNjBGvjTygNas1iZ50gtSgrriZj6mKTVWvq9pVNdUycONKdaNb1qaq6WLSmYZ4pMab7srwCb5qbNVIW8oa2FTSiXBTSoinZ09PO6UqiVLTM/BVqGJVU6CbUrGNYIqeN4kyVmldJSqZgBmr' \
			b'UFeBegniai3y9hUpo+FWrmqIWarQmkpfE19UsTWdWvP9/PfVGWWfU7/GNT8X+MmBriKRMGI56XANCUNSazl5wW09pxnxfLCa7UHkUSJ+k55DCRF3iY3m1nKDY5VgDTGQDkBKAeKAFGzdCgt1rkVYR1Ixixp5sO7l4TU0tDF3CwJBMRCgyMHi4ICBptHnKkp6' \
			b'gi0EZ4pARMHPGoin0UbBAeBOdITGDzSIOxzeL3jQd5JPjR4M2lq/zg8G2D0kJj1Uy9uCSaKi31g19WGx6tA1tr2fAetJFL9gms8l7SkNmhDXNqToAtAzBPQTpu02JXkCmnkWIYy6Pk1kntU6EtB+xYle7adop7J1fo9lBpSZpCFJtkquSiQLeia+SuEkHlky' \
			b'OkIQ+Ua6YaxiXUVXRV9FU0V7CmKg+tcnXv904vVvTrn+Z1EnvOjHjY6Hdcq81mmgNpdCKfk6j6Aiuqm2xRzbnkSHLwsHVNW7XcW1PFSu4Ik8VKoTVfVu1UmQeVcqk+5SZaLU5tgr0Rx9JXit1spyWESDJ5A5qgoYVMCLRg0m7l6e0HDRGj07FgL3z1DTTi6E' \
			b'MV5+tFh+tDxssCJvXnXjg6vBvEsYQzgsGnSzaPQ7mEvf4d7nzOtYymPV5HAYM3hcrlElk2HBoS2L8rIb2LOHyB4hTofWB/Z0ibF4TW1A3S4uWqwpWiwf4imdzJiylk7l9NYEL3g12GI1+CQFcIbq19q91elkVN5Jh7E/LSpsCrwMLM3JGlJNWJFIMGSkiItS' \
			b'reu7aHOTmv5DBFFEkRFGi+h0TBRxdVQLR1SbKZY2AtqvgMEU86gLHuydwc/0HDNmhxmza90G3GjoVUve0F8gTeRy0iHpdHzqjsvefsGDaXdUg2kZRbu7tQrAw32r43GH8bjDeJwO/Sutg641dnROhuhMZxRmPrQjdgerrIPdkw+Nxx0bLAkekCgwyfOAUkRt' \
			b'A3B82rYQbmNFChAN2qkaj9zhGac15JXQ/CWR5cnYzKRDsehQTqMvZ0Q47TIt+kpegDsVRFzwYOBUnjTwHoD3kEc0/q6bOWqu4nGNqpjN0cCSWPbo3D06dy++fpKUvtsf3roIjw9k1ID6RPBKhfpzHa+jX/Loijw6HemKvLZM6Jm6UTtGOKSxQQc8ATIJkEk4' \
			b'CTTL+O00qsqKHUSDAjQoqAaFc+2+oEGtOkSoQ4Q60IHkAphEeLBFvbA+crPGBVezRjVrEQIs/ZgaN3KuZyrgysv1xCqElECdlCDdBYk0x18Jd/SVYG1q1C99rY7pa+nE1tUFlUUNl3JRJeWwK5lnn6lt0WQrG9o4Zt5LHRupnZsWBTjneV1sW0AvlW24XjSy' \
			b'V0fAxM66Zk11kPsTA8wBs8A88ComM8LLmryuyZ70vD2C90bwtgjeV8JWK3aTZXdy9iVnt2V2DmZDD+8k4T0IvAGBffRZEDz75G6M16V4BYg3YfCohLeS8DoXL3KxFy7b7hpDwpLtSrJ/Mso2NsfbBW21km1d1YroV7Xsn6pk0xApx4qEsWpk95ahBJ1sePsb' \
			b'b7PjfZq8EYou4g16HOVSiZbEsopr7D3krXEN33HNhfN+xzUTr/kU3bXmfXx0OVVLbsM70XhDKG9j431ODW8WJMqUdN8f062t7KTivWSym5R3qfFmUbor/3Mub7pkRvmG2K+34r2aDXND5yi71h1YpJ6rwFm8tZP3VzI5c8E73Pg63kfFu8/oSNQ1b9ViudCp' \
			b'wAxynP/d97yywco4pYJBtZDNk50i9tGYlbIDT6eaAjwMxdAhb9DUEmOYeOmyRCg0eC1KHFo9FoiqW2uh0PR84S7PzX6r3HMKTTXmXVAbFTtMKDflc6siSk7needUT9nXhcKHQunpGl797Cm+hfKzWzV7GLN7MbvsdmDgZ8B2hTQARsOSmoFA04FgAAO6SyNN' \
			b'Xj1CRMOYaHqoaAQXjf4twEcz+GOsGAYw1VS4ZcgYgUzTgUZ4MXwwbgyfrqgWRlzOCDlc7nojfpohgqTQEPWYkQQsRWGoRRMYyGgKQBQ/Kr5btcroUm4LjFV/xvRgJXph6Zj+kgEKgY7LXQS6cONYK4FmtuNrAltsBRN8XSe2FuJqK5a4ZRarXQkmSVo5KJhM' \
			b'6KOJ0wMUcVYEacaRQQdjQg4LwFRe3iOtcedBHyTMzHdDvRK6LqkHpHx+A45EHD0gKU2IXSyDSXOKjqnlYAQmoQSGMiM9GBn3gBs4Uq8HjHlSAzrWf8lG13s4HRKcZGwmY6UCTjXgVGc41QM4jTslzoogLeBUA051DkvgVE8HgVM9htPmUV2vhBk4dec3wake' \
			b'wQk0IXaxAk7KVwEn5WAMpzrDqWNkIZz8PZwOCU483Wl4YauEkyStHBROHC3hJLOkPpysTHyENMOJk0kWzrqwAE7l5T3SGncewEmYmYdTr4RpOOXzG+Ak4ujBSWlC7GIZTppTwKnlYAQnm0d4mZGFcAo7welAZlj1zpOsTTDbNMkyNz/R2g45L5Dzfch5QM5n' \
			b'yPkB5HwOI+x5wZ7vY88DeyXdAuzNBMGe72NPp1vCEC5y4Nu3tx1hsSxxBovd+Q2zLquQ9CNI4lyIXayApMougVxRqbyMUekzKjNLy1AZ71F5dKiMgsrYR2UEKmNGZRygMuYwQmUUVPZXAznJqCzpFqAyTgdBZZxGZQQqI1AZgUpQDVFZljiDyu78JlRGoHK0' \
			b'oqikoSukRKXKLoFcUam8jFEZMyozS8tQWd+j8uhQKbM925/tWcz2bJ7t2cFsj59ZG0aolGmf7U/7LKZ9PboFqKyng6CynkYlpn7yvjPw7dvbjlBZljiDyu78JlTWQOVoNqikIXaxApXKagK5olJ5GaMyTwgLlpahMu0dlSMT3c1h08/DM9xNhDqZQLr+BNJh' \
			b'AunyBNINJpDO5jBEKExoDjNJNk8RSBvg1GE+2aPejtPy8h5p7XAATvkeClOHKSVeFolUe9dm3H+WZTazXWi+7QawymlUvg9WJQ2xi2WwtmLE2y0VrJo5BqvL082CpQmwxuaBLKWNMdswZrOB+YrYtYfaqdpev7rFgn0bCOZ3r3QW7ysj2U0YweXFsmMjIGe3' \
			b'yHYDZBdhiOyEyyOKzd2v6Ljpky6AtZsOAms32f0KT0IpuHbANS4fgrotzihdh+qNdva2sA0Qd4C4G0EcpKErpIS468zwQh/kIbfWeL1+AusuY70TzxDrXEfCOB8I4s79hV2H++iWDxbad3S87MTY6PrGRgdjo8vGRjcwNrqQw8h2v5bciGIKzMLw2CNdgNkw' \
			b'HQSzYRqzMD7KS4fBum9vO8JsWeJML9yd3wTRAIiO7JFKGmIXKyCq4ksg115YeRkjM5skC5aWDZmNuZ/JHh0yZX3J9deXHNaXXF5fcoP1JUp3YTROlvUl119fclhf6tEtgGWcDgLL6fUlh/Ulh/Ulh/UlpRrCsixxBpbd+U2wxPqSG60vKWnoCilhqbJLIFdY' \
			b'Ki9jWOb1pYKlhbDczfPmYGG5YRJ7J5GZBJmpj0wd56aMzDRAZsphhMwkyEx9ZCYgs6RbgMw0HQSZqUOmVEKBmQDMBGAmALOjG2KzLHMGm5l2AzYTsJlG2ARpiF2swKZKT0tXbCovY2ymjM3M0k4TV7ObN889RA8DoqxnsqRXQlSSVg4KUflSRAFR+S6PhiFE' \
			b'OSuijAxRTpKQe3TbIVpe3iOtHQ6AqFQCEBV+hHCFpUqGaKYbQLRX5jREC9p5iMpp1LkPUSUNsYtliLbSSyAHRFteRhAVYkC0YGk3iO7mIXQP0QOBqDiM828JUQOImgxRM4CoyWEEUSMQNX2IGkC0pFsAUTMdBKImQ9RkiBpA1ACiBhDt6IYQLc/NQDTTboCo' \
			b'AUTNCKIgDbGLFRBV6SWQK0SVlzFETYZoZmk3iO7f6+jeZnOTWBWbje/bbDxsNj7bbPzAZuNtDiOsis3Gw2Yjn4HTr8Gh4GT61AsQa6eDIDbbbKQqiljYbDxsNh42m0w3ROyg2BnQZvINoIXNxo9sNkoaYhcrQKtiTCBX0CovY9Bmm03B0m6g3b9T0j1obxK0' \
			b'4jbo+26DHm6DPrsN+oHbID+SNoxAK26DHm6D4kGLlEPBDNqSegFoZ4KANjsPSlUUtPAdVPddD9/BTDcEreQa8OdnXQgL+g2ohQuhH7kQKmmIXaxArcoxgVxRq7yMUZtdCAuWdkPt/p2W7lF7k6gVg4zvG2Q8DDI+G2T8wCDjQw4j1Io1xsMawweHlMPVyfSp' \
			b'F6A2TAdBbbbJSFUUtTDJeJhkPEwymW6I2kGxM6DN5BtAC8OMHxlmlDTELlaAVsWYQK6gVV7GoM2GmYKl3UB779N03KAVW43v22o8bDU+22r8wFbDD6MNI9CKrcbDVuPh0+R1RguLTY96AWjjdBDQZouNzz5NHgYbD4ONh8Em0w1BOyh2BrSZfANoYbbxI7ON' \
			b'koaukBK0Kkb96K6CVnkZgzabbQqWdgNtcw/aowat+Cv5vquwh6uwz67CfuAqzE+iDSPQiquwh6swHxxSDgUzaEvqBaCtp4OANjsMS1UUtPAX9vAX9vAXznRD0A6KnQFtJt8AWngN+5HXsJKG2MUK0CrD+mVsBa3yMgZt9houWNoJtHY/bkrF63luArdGXz50' \
			b'j968rZsdCyrTf+WIJK0c2m3dg3eOmCaH0f5ueesI/TaY4BosIssBZfNG77KABRu9m+kgG72bDsAGbhKGv38tu8tqMOhxd2W3uPtoC/ig+Jld4Jl8HshyGtXuA1lJQ+xiGcitRBPIAeSWlxGQhRhALljaDcj7cWmyR9IBx7uJYiuzXduf7VrMdm2e7drBbLeW' \
			b'i/TSofuhkdyIYkDrkHIgSCZT20UT3vLyHmntcACKbZ7wWkx4LSa8FhPeTDfcudMvtpm1CRUlbNi/gzmvHc15lTTELlbs31FhJpADwJo5sX8nz3kLlnYD8P6dnw4WvXcRuvLyNhZmCd0A+23I9tswsN+y9NswhG4Q+22A/ZYPDimHgpPpU2/HbTDTgXEbshU3' \
			b'ZCtugBU3wIobYMXNdAPcDoudBm1BPg/aAENuGBlylTTELpZB24oxgRygbXkZgTZkQ27B0m6g3eIOVfdxa++he4jQNeLAaPoOjAYOjBFjZ0ZGg2ta9PKrJnkEzaXxZWbsxmjEjdHAjZEPDimH4nn4nHJYMnxO00GGz9mZ0WRnRgNnRgNnRgNnxkw3HDYPip0Z' \
			b'NmfyDcNm+DOakT+jkobYxYphM3K8lq7DZuVlPGzO/owFS7sBeP/OUvfQvcle10mv299kJ0kRbtfrDvbYhSKMel3ZYBewwY4PDimHgrnXLakX9LpuOkivm7fZSVW018Uuu4BddgG77DLdsNcdFDvT62byDb0uttaF0dY6JQ2xixW9rooxgVx7XeVl3OvmHXUF' \
			b'S7uB9t59agRaq8D1xwReme2G/mw3YLYb8mw3DGa7IeQwAq9MdQOmugFT3YCpbsBUt0e9ALxhOgh481Q35KluwFQ3YKobMNXNdEPwDoqdAW8mX8vB4u5TEMZsN4xmu1pAiF2sgLAKM4FcIawcjSGcZ7sFY7tBOFYX1/yS9Wt5w3qYgZedgNWub1lX6Ey+aV0k' \
			b'z5a76pZfsn7NL1jnOs68PvCKL1lX3Z150ToRL9HHXr9y9ff+2xt79T+P/a/y+v+a39EaCuXkAX6ohp8DSJfS0uvR1InPAbCobvaTACzQK3wWAP1oXqdo+9Gh9qYdW9Owp69WYEyTDqllXW9Q4jjTuu7jGxYTBrQ9f8eitYDpu6/2oLxmZgyxY3NrhNtpBU7T' \
			b'TS4NEWx4QDL/C1+vvdJgIOz1oyvuVr67EtK83l6bzk7oqxhh96ezGxpa09swe1PfX2Gh7vYNFhLudQ9Vl6omJob70k5+Mw87g8drHrse9xeCjI5Q9qOp8sYpwfr6igNas0FrqXWt7QMqUL6/YKqLQ5hmmUpWsNdh2evA9vpBK65o2KVxvXVVvcQ8C4s47Pxq' \
			b'VVVv6oNWuKvZpVG1h6CU3Qfi3DXqplugnxSP7nT0lDc01rLYuKIqX4O+prC9OU3sNs53d7vqrtuP7vqrt6l2z7o7tTrcrgrPDVybA21jFzkUX05/WWvi3nQ3jlyERXdjmNVfHm+JDu+uu34/uhuurrul3sZrGhNs0NvT0tlSXw1c+Pc9Ptigr5fU1bAfXY37' \
			b'1dX6XldvUlfTcehq3I+uzhubL6Wr6V5Xb1JXm+PQ1foQ5l43vwhwKMp4jUZWC3eNQ/mCdfUnPd0HBAVZh0qnpXb+ssuljr2KjlT7rnW5ib2NLmHer/4MDwjQooPNIeggyb1bedq3Npa+XEtWnO50o2jkZXdOVpv2vcJkd1tlWtw7032Xq2h9BS2t++6JV2ov' \
			b'N7kN79E1ir1QxGl+zxqaoKSiKfvQUSlP1VS9AvfRgm5w3N2fg5RhNXAzDaltHhCS5TPEu1iV7tV0P2rqoaZ+X2rqj1hN2Yfab1dTW10cwoDzJuY3i31J0xF14VC4a5/PLHYUJUFc3L46HYwqNUelRgeiQv4QVOiWWiT2FpDNkOsZleLnf2sqFde7aRRfv2+l' \
			b'Eh5mdYo9r1e82jfT9cX0QHaABkvHJF1gqC5uW9kOpb0qNCvet1XbF05k9S6IFsV7LeqaKHs0XV6UcNtqRG2SPL8HK35s4cEKDVN9r1KdSrnjUSlXicnpIFUqVReGN/uSSHnBYC3jrUZe8cCf+dxJj5pSU0Qr6u0awE99/MSl69HHKPK89FOTJ9WbizvIfYuc' \
			b'6ym5snSo4iqdSy7T1AtXZ668+rIJU2Yk5YC1knBFmHABO6+PXHEFZB4LsuIceisc9Dja53eJh7e9iby2R9Z/XHEfTdpu1qrreED6dHgQLp8BJmFfiKj5NTNrqawX1DnNh5C5SbsoNyqwZ2esvz+n7LOVvNrPyDvJSBhUZdkIwiXKFlLZs8TzKuzm4OJXdo7E' \
			b'VsWfXOqKS+Ubst723n7AG8YTF1G+mkBcRTtjk740AC8E4C8CVvzX8K4Z+P2H/r/0+UTMm/4cLpYdqnLewDLFcfYhwc5T4dTvn1Oi3uVP2AgL2KiXcsIvV+i4CdXUH69rz5yhgQ4dhat4bVzRYGrXP+FIvrxgwiKmCFVDvvjVFlt5E+tAPfPHixxFirA4uELY' \
			b'TLuxiRd9XIrZVG36awejG64RfpvL8IsXk+zOte5A7t7gIc1YtXNox9fLKQYjZK44Pqne3GrdDU8vxM50MwEVN7dfcVvdbEDF7VUqHsOo7u0rc3avv6suH3hWOcjiieIiasjBqRzcHkWRtouDuZwXCQ/2eKqNyNXDhqKmTkEy/hAlE6tbDZBMGEqmeA8WROTw' \
			b'IdLFgorSSVN12fbavbyq/8Kq/pupGMk8xDCbJcnD4Flp8szm9gINzcWXbxciyD8eoGbyotptBkim3qqZO4mop5Cz4rqSCrqqDDTfwy8iuwaeToOYJ9LTl4SZkqfuCKGmoxNqqg41QKLN0Um0qQ41YFFifWwSdVgzPsQAiZqjk6ipDjVAovboJOqrQw2Q6Gjy' \
			b'cgWJbh2C7lGudbWvwLaPYRZ/auWqBUO+oynQzQ/0ryboptoc8B7crZctD2ywuBQlBH4AM6srCZwNQscRIO/RTOrY5J2qIwmQ9/b52YHLu6mOJEDe26duhy1vtisfR4C8t0/sDlzetjqSAAPz9mnfcaxEssH+mAKkb7JLVGSBIZemOfwY5BlAiEacFNgdRHxB' \
			b'OmePiFaK33rFHkINe/yYxL4ELPka8k1YdJbXC7FjR4OuRF7hImkthF+TwaK3Ykhki4vqCL+ToHj29JDkCqsvB6rxMougxaTpq101+MfVzehqfvBC4avRf4TceB+mqT1fVVNlvj//fxLTdBM='

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
		'Derivative': lambda expr: _expr_func_xlat (_xlat_func_Derivative, expr),
		'diff'      : lambda expr: _expr_func_xlat (_xlat_func_Derivative, expr),
		'exp'       : lambda expr: _expr_func (2, '^', AST.E, expr, strip_paren = 1),
		'factorial' : lambda expr: _expr_func (1, '!', expr, strip_paren = 1),
		'Integral'  : lambda expr: _expr_func_xlat (_xlat_func_Integral, expr),
		'integrate' : lambda expr: _expr_func_xlat (_xlat_func_Integral, expr),
		'Limit'     : lambda expr: _expr_func_xlat (_xlat_func_Limit, expr),
		'limit'     : lambda expr: _expr_func_xlat (_xlat_func_Limit, expr),
		'Matrix'    : lambda expr: _expr_func_xlat (_xlat_func_Matrix, expr),
		'ln'        : lambda expr: _expr_func (1, 'log', expr),
		'Piecewise' : lambda expr: _expr_func_xlat (_xlat_func_Piecewise, expr),
		'Pow'       : lambda expr: _expr_func_xlat (_xlat_func_Pow, expr),
		'pow'       : lambda expr: _expr_func_xlat (_xlat_func_Pow, expr),
		'Sum'       : lambda expr: _expr_func_xlat (_xlat_func_Sum, expr),
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
				AST ('piece', ((expr_ineq, expr), (expr_cond, True)))

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
		xlat = self._FUNC_AST_REMAP.get (func)

		return xlat (expr_func_arg) if xlat else _expr_func (2, 'func', func, expr_func_arg)

	def expr_func_6     (self, FUNC, expr_super, expr_func_arg):
		ast = self.expr_func_5 (FUNC, expr_func_arg)

		return \
				AST ('^', ast, expr_super) \
				if expr_super != AST.NegOne or not ast.is_trigh_func_noninv else \
				AST ('func', f'a{ast.func}', ast.arg)

	def expr_func_7     (self, expr_attr):                                      return expr_attr

	def expr_func_arg_1 (self, expr_func):                                      return expr_func
	def expr_func_arg_2 (self, MINUS, expr_func):                               return expr_func.neg (stack = True)

	def expr_attr_1     (self, expr_attr, ATTR):                                return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1])
	def expr_attr_2     (self, expr_pow):                                       return expr_pow

	def expr_pow_1      (self, expr_pow, expr_super):                           return AST ('^', expr_pow, expr_super)
	def expr_pow_2      (self, expr_fact):                                      return expr_fact

	def expr_fact_1     (self, expr_fact, EXCL):                                return AST ('!', expr_fact)
	def expr_fact_2     (self, expr_abs):                                       return expr_abs

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

	def expr_piece_1    (self, BEG_CASES, expr_pieces, END_CASES):              return AST ('piece', expr_pieces) # translate this on the fly?
	def expr_piece_2    (self, expr_mat):                                       return expr_mat
	def expr_pieces_1   (self, expr_piecesp, DBLSLASH):                         return expr_piecesp
	def expr_pieces_2   (self, expr_piecesp):                                   return expr_piecesp
	def expr_piecesp_1  (self, expr_piecesp, DBLSLASH, expr_piecesc):           return expr_piecesp + (expr_piecesc,)
	def expr_piecesp_2  (self, expr_piecesc):                                   return (expr_piecesc,)
	def expr_piecesc_1  (self, expr1, AMP, expr2):                              return (expr1, expr2)
	def expr_piecesc_2  (self, expr, AMP):                                      return (expr, True)

	def expr_mat_1      (self, LEFT, BRACKL, BEG_MAT, expr_mat_rows, END_MAT, RIGHT, BRACKR):  return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty # translate these on the fly?
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
			print ()

		return next (iter (rated)) [-1]

class sparser: # for single script
	Parser = Parser

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT:
# 	p = Parser ()
# 	a = p.parse ('Piecewise ((1,x<0),')
# 	print (a)
