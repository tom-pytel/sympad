# Time and interest permitting:
# Proper implementation of vectors with "<b>\vec{x}</b>" and "<b>\hat{i}</b>" variables
# sympy function/variable module prefix
# importing modules to allow custom code execution
# assumptions/hints, systems of equations, ODEs, piecewise expressions, long Python variable names, graphical plots (using matplotlib?)...

# Builds expression tree from text, nodes are nested AST tuples.

# TODO: _xlat_func_Integral multiple integrals

import ast as py_ast
from collections import OrderedDict
import os
import re

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

def _FUNC_name (FUNC):
	return AST.Func.TEX2PY_TRIGHINV.get (FUNC.grp [1], FUNC.grp [1]) if FUNC.grp [1] else \
			FUNC.grp [0] or FUNC.grp [2] or FUNC.grp [3].replace ('\\_', '_') or FUNC.text

def _ast_from_tok_digit_or_var (tok, i = 0):
	return AST ('#', tok.grp [i]) if tok.grp [i] else \
			AST ('@', AST.Var.ANY2PY.get (tok.grp [i + 2].replace (' ', ''), tok.grp [i + 1]) if tok.grp [i + 2] else tok.grp [i + 1])

def _ast2tuple_func_args (ast):
	ast = ast.strip_paren ()

	return ast.commas if ast.is_comma else (ast,)

def _expr_mul_imp (expr_mul_imp, expr_int):
	if expr_mul_imp.is_attr: # x.y * () -> x.y()
		if expr_mul_imp.args is None:
			if expr_int.is_paren:
				return AST ('.', expr_mul_imp.obj, expr_mul_imp.attr, _ast2tuple_func_args (expr_int))
			elif expr_int.is_attr:
				return AST ('.', _expr_mul_imp (expr_mul_imp, expr_int.obj), expr_int.attr)

	elif expr_mul_imp.is_pow: # x^y.z * () -> x.{y.z()}
		if expr_mul_imp.exp.is_attr and expr_mul_imp.exp.args is None:
			if expr_int.is_paren:
				return AST ('^', expr_mul_imp.base, ('.', expr_mul_imp.exp.obj, expr_mul_imp.exp.attr, _ast2tuple_func_args (expr_int)))
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
	def astarg (arg):
		return (_ast2tuple_func_args (arg) if args [0] == 'func' else arg.strip_paren (strip_paren)),

	if args [iparm].is_fact:
		if args [iparm].fact.is_paren:
			return AST ('!', args [:iparm] + astarg (args [iparm].fact) + args [iparm + 1:])

	elif args [iparm].is_pow:
		if args [iparm].base.is_paren:
			return AST ('^', args [:iparm] + astarg (args [iparm].base) + args [iparm + 1:], args [iparm].exp)

	elif args [iparm].is_attr:
		if args [iparm].obj.is_paren:
			return AST ('.', args [:iparm] + astarg (args [iparm]) + args [iparm + 1:], *args [iparm] [2:])

	return AST (*(args [:iparm] + astarg (args [iparm]) + args [iparm + 1:]))

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

	return AST ('func', 'Matrix', (ast,))

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
			b'eJztXWuP3LaS/TMLZAZQA8235G9+JddY2/G1nWAXg8BwbOci2NjJ2s7dXVzkv29VHVKkXt3qGc109/RgOBJFsahisQ5fRbLPLr75tw+f3n9TffPsyfMfXtH9yfPX39Ht6ZNndH31g1z//vI1B33PL7794flDfnj8LYc9uP+Sri/uv3z8/CkTf/f8+5eP3zz8' \
			b'4eXT/+S4L+8/jDcV75qJHn/35uH9V49fRf+z+6+j70H2/pi9L+CVVPkrDyidf2fPq9f89efC5I/CycPvnz27n+K+THFbHtnz8sl3f+Pk7j97QddHD56+enr/1d/I+/j5o8gK+x5k74/ZG1l5/PTVY779PQan3HBqr8EIfY5jPvlWZCoxXzwVCT968uOTR0z+' \
			b'8NH3ryUXQvHqhwe4sqge/8fDpykVfr7/WrL64uWTZ/Kh19/T5d3bzx++vvn985v3P//25evbzxT04X//+Pzm49uvb979/lv5+Pn3/+k9fknP795++fDly7vu4x/dx/T05c8/PrSf+eXPT+/evP38j/zyZ/L+M/Px6c+Pyfv1w+fW//Pnt+/+68PX9gt/fv7t' \
			b'/wrmOl9uv0U0yf8HZftTenj7c47z9l1L/EfO79uvXzssZ3Zbjgqef/u1Df31U5vcxz9/e/Prx1Yo73/9Z/b+8kub3w//KAnI0/Lw/n1O9cN/t1n8/VMb3obmlx8/vu08fPnmp+ribGXXlWnOK/HYNXtMtbJ816o6q6umogDdVM15CpOQ9nGlNfuC/Fuirc/z' \
			b's8qP5KG7qnFx6jw+rpR8XQf+GKen+Gs6nKfQGNYGrLSkpG11phyxYiuDb1DISjvJgeWLqwy+Qo/0JD4v+TNrCjjvBODJJTp671MQezl5+dcukWr2cB5iODJELMRAeeYEfWU5vYq+penDrtJ+7N3K9UPj8wqfJ06ZXCVyCiBxyMc4WIlP4WIpx0qf94JUGche' \
			b'LnX5hAnp85Y9nPoaFxsLmj6h5RPakNwp7yJte94GmfJR2ejhMP4elSMLLn5dnrRknAu0CPaDJ9UJCYMnU4aQQkmhEX8qRN+ZkodzkasoKb1NzysIkDKg47dMehkD24cVMqVIYqayQcqSFNAZyQYlBUmNvxd0zYumurFWCsXvIj4UCyVUlLECJvSyDc8hASEm' \
			b'h9QIsTmkQYhLIaRWIrcGlwIpTdR3U+Mi0gKbphYv+0J6eR4f6Sm9kKBa/q1LWYzPPj+vJCWlcSHRn59nL/kaFCkg24iPeSdpyGutWVJqnWqSWDmwIiCsCFAiftNCivUaoG5wWUXpsVejdiQ82SDx4qNFzUbKZYsClaxLUbJKxeL0rV6ScrFEo2LGR9UJsOv8' \
			b'FVM55JJ0QEcPZTn5lGBWSfW1rlzEAyMOPK8rwiFV9xdrrsCIKYIdoZMwTFUPlRaLiYVFESlDjtTRV6Hiyj+EKtRVaKpaVzVFJgrHtRVlr15XNUUOlaP6vKn8uvKq8rry1DqQs1yoJA9LpdsQ+1TnE2dcMCT2mhoUbm+4orOVq3xVu6qmKyVbM0IJLFRjkZpQ' \
			b'Lkhs3laeYpEnVL6ufMMAIKmQViiubqqGpLempNeUNtV0a/4QvVjbn6ozCj6npo5yzjUY5V5u9JZEckYy4EeDOCQMeWrkJdHgWTcIXuOm4lvigZ5PT6IXZw6ydJBlkGsdpQJZBQSGFFqLrI4xt2cBOaqTjkSNgQiMT8oQpSA6cgS5qhWy48C3E01vVNXo26Oo' \
			b'Z65BJj2Q6xVuGthnEnmWkj1r4s2CxkK5rciH2md3MNm64O7WidY8FjWybXKpQGkPhkMHXXOq4NBVja+aUDX1AfEpNTL3ilCBKYChFskWHEudjjxZxD2zse5ATVijJvR4UjqmJ6EnoJNnHsKo/Wli8qyOLV8dlUL0aoF0rYsJmqUSjDW7koRpfKRkSEXdfurf' \
			b'U7/9FApLRW31IoNgq+CqQBmkVt9UYV0FdQpioPz7E89/OPH816ec/zMfR7To8io03U0TewRo7etUXa5TT8GkfrNth9QaY2l9Ek29TBBQVm91FnWNQm3kxnNHJ1G2PJujzzG3Qfdbk6+LsyD5uQ05qW9NToIUylHnoD7uHPCMpODdoBFj89z5EXG/jrWVKFJv' \
			b'uO5QhffmZWXQvjAbjW4n2DQm2DQm2DR3FBrpGPBMmvBqhdc4eWXyUDm2LTJgvs0tjIszyE66T4fClYqFVMdCknb/oOY7eUoNyq4OjjfCFaa/Gn9AhUpchetAe52mDDVmCjUmBaE4J9JRvOAJT32KM30XPMerMcd7kgI4Q1ehju1ZHU5G5a2U+EIqVJgJeHJX' \
			b'NMpBpAp9FhXt7ioa6WMvQ2GCQkczhI9EAUkGVMQhGSACJjdCjB2isc+ji4K+iEdPiXmMMxm8/oML9BxDYYOhsMFQ2JxjoGjiQNEMelkBYX3r90goPxo8mtgPNUdkQL7gHrM5nh6zdJXNLRrYc4dex763Qd/boO9Nt35vwIwEWuifrIDhus2m3rmBgdXAism3' \
			b'JiKtEfAcjACAYQvcOMDI4/G07RtcvUrxQTQeN5S3xSsV5aUgRC3KdDJ2MGlLNNqS02jDGREmtpYazSRPpp0KIi64H3AqJQ28e+Dd586MRWfG3nILBvFrj6onRTzaQU+S+LVo1i2adRun1GycS7MHNhXCvQNpYCB9B0Y9HqWvjobJoi2yaHWkLWpi1YSmqe2x' \
			b'r1vN5QXOcbltobntCBQqjHEoFNlkVQbgj1ehGbIudvQcNMJBI9xJ1GfSfT2NrDKsnUDIAUIuQsidxwYcEHIRFh6D1c6adc4ctMRDS+hGUEHd4bFQj29EHqJWhWM25FxwVgOyGkQ+mCTAlAGxGnr2ERaAxKcMQlA1qOtIUB+9OJojz4E+7hywEjVxvfk6Ljhf' \
			b'CzjXFe/BoaosskDVFq+7TWnyp0MchWktc6ttZSe7BAnsnAU9kk30BahCZM4988wjXsd1IsvN5vyyqWLNe6T44ywc4oBZYB6YCeaC1wkyKzwTxztneNsMsaN4Rwxvh+FNMLz3gbc9cNXDS4N5oSavmucl87xOm1dC8zJo3i3CK/B5zR0vPOL2nWfjeIKOJ8NY' \
			b'fLyImC2UbFBsDIkKez09dhry7rgGO/QcbxWrVlTNr2pTYXMnby/lV7IbjDyet1zxVkbeNEbPVPAr3lJJpFTWK959Jlsk6dk32KHFW+0aoae4Nb9cc+haNpVSCKVU8+5NJufNmrxZj/yUxVXDO7CYqpENfCsrhLKXrMLeON5kRs8kB9kJS1e6BX5DIY4/xskR' \
			b'uWNmeW8cb8ikmPQl3q7IW7k8/zPD9MozKXNB/oYzxaLir9OdUiNZyn453hpGyrDyzCR9wbMI9E/c4WI1DKPq57saCKNsO9PfaqNggbHZ6qTqgGgUia2KUiEyirsQzoirZVxq0vQNGnXBPtcJtoNc4JoBF7V6oyaT5vGk8qRG2xGtpnBe0yzaTe+5hii1nLci' \
			b'tJpuC23nO8XhlYYdrddR8ymMhyi8EYd3RyUU8DpqXoTPa+47iGCoirgm9J91sA+BwEKRCTA/gAPHl9clKGSTpIS2bgZGyugdUs4Yb56sI+Na4COcAkHCl3CozBBLnbRaXJHycWIDKHGkRk0iSr7aAVXKX/ZlgPEjqQL3LXyLsoKZDDUPuPELBiLvAW9xlwkK' \
			b'AFb/8vU9rkpIZ+ge/pLuiiCyia3VJkjam0ViAcNeOzKJvhHkselG0HddyNsFdVuR5mWfdSPXAmn8WGMPdh9oagRfXvDVbXRkD7CEtm4Ovvy4E3z5TtOkNrdOHeoSUV045ThTYPIDMMXMZF8BpphWbq8KJoZI8hk/bbQOfpS9x7UeadY9Ab5b090zjswdjg4I' \
			b'R/xCcFR3cVQDR/UIjuohjmrBUd3FUQ0c1dnNwVE97gRHdRdH9WYcldQbcNTGmcJRPcBRzEz2FTiKaRU4ykwMcZT7fznaTBzZOxwdDo7YOCfdPr4WOOLHGu/6OJKwLo60jICEJuNIjteR0NbNwFEZvUPKi2pVB0fCyDSOOtTTOMpxJnAkrzo4SpnJvoyjlFbG' \
			b'UcHEAEdCDBzlaDNx5Obj6BCGWv5So61N+Joaba33NOLaijXDJbGS9cgdrBlgzYxgzWQ3AJ0R0Jku6AxAV9LNAJ0ZdwI6k0EXB1nCDCLw2l4j8Eu564GwTG0DCNs4E6MseRXwrS4WYx6zr8BilBvoEhwzO0M4mgzHzNE8OPo7OB4ZHJ2cudbItYSjAxzdCBxd' \
			b'dgM4OoGj68LRAY4l3Qw4unEncHRDODrA0QGODnCMuevBsUxtAxzbOFNwjE2jG8Ax5jH7CjhGuYEuwTGzM4Sjy3DMHM2DY7iD45HB0eN4OrmWcMTMiB6ZGQFJJOzDUaZIdHeKRGOKpEM3A45+3Akc/RCOmCbhG8MRs5Apdz04lqltgGMbZwqOHnAczJykPGZf' \
			b'AcfIKugSHDM7QzjmyZOCo3lwrJeFY9rZtTgoSRu24NJMQ9PeXnQSU0bGiaY7TjQYJ5qRcSJIImEPnUYGjAYDRh5nUWYaYNRg2Nih3o7RMnqHlIrM5GGjDOkAU4PRI98szpx060jUDBvOMs1mY9uZPz0BVnkV8MUOWFNmsy+DNYkRdBGs+VNDsJo8siw4mgfW' \
			b'hsEKM3K05F0atOogm1HVaUln2KlvGrd8/GGLXb8Fv/VcDOvS3C1mY2lwRYWHRj+J0Me0zq6Pafouh3q5Fo2unJnru6QzAK3HnQBaDxpd4cfIzYIPt04UfSinpLikhKDF8jaLekpwAtgawNYDYMdMZ18BbN0a3IXeSwELurWY3iPJEOFshDfZHpgl1Ec5Z5VA' \
			b'zjfCuNF/YaPllRvkw8T2Le4is6CtINZ2G2ELwNoRwBZuAFgk5EFfABYLWDqkMwA74QSwdghYC8BaANYCsDGDPcCWqW1oeNs4U/i0wKcd4DPmMfsKfEbRgS41vJmdYcNrMyQzR/MaXqXuRq1HBknHawgZkt1JJINJJDMyiQSSSNjvF8skkulOIhlMInXoZuDR' \
			b'jTvB43ASyWASyWASyWASKeWuh8cytQ14bONM4RGTSGYwiZTymH0FHqPcQJfwmNkZ4jFPIhUczcTjDmtn9oTHKw1Yby0qg5yS38i1RGXs2YYRVIbsBqgMgsrQRWUAKku6GagM405QGVpUCvcRmAHADABmADBbuj42yzQ3YDPTT2AzAJuD1aIpp9lXYDMSxJQj' \
			b'NjM7Q2yGjM3M0Uxs7rAe5w6bB4TNhifuVriW2GyAzWYEm012A2w2gs2mi80G2CzpZmCzGXeCzSZjs8nYbIDNBthsgM2Wro/NMs0N2Mz0E9hsgM1mgM2Y0+wrsBmlB7qEzczOEJtNxmbmaCY2d1jjc4fNw8Gm/FIXY5OvBTb5kaRiR5aBgyQS9rBpZRm47S4D' \
			b't1gG3qHbjs0yeoeUSkpuwKZwD2xarASXbRN44Uq6HjY7aU5js6Afx6a8CvhcB5spp9mXsZmkB7qIzYKdATaFHtgsOJqJzYXXDd2ZYm4apEp+xK2RawlSmGLsiCkGJJGwD1IxxViYYvjGJacAVZhiOtQzoKrGnUA1m2Js3rRhYYqxMMVYmGIyXR+qvWQ3oDUn' \
			b'MYFWmGLswBSTMpt9BVqjGEGX0JrZGaI1m2IKjmaideFlRXdovWm0GvntykauJVqx6M+OLPoDSSTso1UW/Vks+uMbl5wBWrH0r0M9A61m3Ala89I/yUNEK1b/Waz+s1j9l+n6aJVQZdKXNsE1pzEBVywCtINFgCm32VfANcoRdAmu7adG4JoXARYczYTrwsuO' \
			b'7uB603C18hOnjVxLuMLEYkdMLLZwA7iKfcXCvsI3LjkLuMLK0qGeAdcJJ3DNVhbJQ4QrDC0WhhYLQ0um68O1l+wGtOYkJtAKc4sdmFtSZrOvQGsUI+gSWjM7Q7Rmc0vB0Uy03q1KOnK0Ovzeq1xLtML6YkesLyCJhH20ivXFwvpisSopjVphg+lQz0CrG3eC' \
			b'1myDsXlVkoUZxsIMY2GGyXR9tPaS3YDWnMQEWmGMsQNjTMps9hVojWIEXUJrZmeI1myMKTiaidbmDq3HjVaPX2OWa4lWrPC1Iyt8QRIJ+2iVFb4WK3z5hpITtGKdb4d6Blr9uBO05nW+koeIViz1tVjqa7HUN9P10dpLdgNacxITaMWCXztY8Jsym30FWiPD' \
			b'oEtozewM0ZoX/BYczUOrXmCBUYtWdyOAVeks1zvYlrANlZhSu5ZUGFJH7Kgh/vXRKibUwLJiuAZBaxCwwo7a0m3Haej9MT6z6RSWU8UHe8smL1/BgAr7Kcynka6HzyLFaWgm0nFcwmo6MJoiY+leHl4gJA5JApCJgwEas6008TATiQssKlJH0nS62wtDLhgZ' \
			b'meruyFRjZKpHRqZB3kbCHh7ppmVwqjE41RicagxONQanukxgxkaZCScbZfLgVOfBqcbgVGNwqjE4zXT97TLdZJuNppoilYlNMxif6sH4NOU3+4pNM1GYoEubZtpPjWyayePTgqOZyF14+dHBwva2YpZFKfZU17WnOthT3Yg9FSSRsIdZJ/ZUB3sq3ygzckOK' \
			b'yneptwO2jN4hpSJz2arqslXVwarqYFV1sKpmuh5g+8lOo7VIYhytDoZVNzCspsxmX0ZrEiPoIloLdgZoddmwWnA0E60LL0i6Q+tNo1WzHBmt3Q0x/FiLjIdo1dkN0CqbYRw2w/CN0aqBVmyJ6VDPQKsed4LWvCVG8hDRil0xDrtiHHbFZLo+WnvJbkBrTmIC' \
			b'rdgK4wZbYVJms69AaxQj6BJaMztDtObdLwVHM9G68BKlW4FWjJmODLWWJcmo7faLHfrFbqRf7Ao3QK10ih06xQ6dYodOsUOnuEM9A7UTTlCbO8Uud4odOsUOnWKHTnGm66O2l+wG1OYkVJv7EeyiX+wG/eKU5ewrsBuTA13CbmZqiN3cLy74moldR8Ohazzp' \
			b'ePljju0EqNQImHY96jiBxVbTRx7zbsa9n3Z8jScd63FVXuC047TZksU2feoxFWyhkePHH19NJ7mpqPdwAHe9g2a6Ee1MmskC8F0NJY75WNv+4dx+oKp8XvdeDudm0e3vgG4W6ny1Haoul3u7Odx01Dc1pb0aN3CV20gVG3apYu0S58mjexMOqLolxZo+XT5s' \
			b'qG6verq8Hs6fL3jCvMaEuIon1CygyGqiK7Fj/cuCnThxnuU8Vf+S4mpSXG3/wm+PXL5vYJf7IQS9l99CcGGDxl6Xto5oKqvY9f8egupscrup30Rgge7+uwgU+Vr7rHOUMo4Ll9JLZp6XdroFO7E3qKM38HsdOjbMy+ionArDCHeDnV879mq59dqkr9wV0Pco' \
			b'0b/w48QX+x1prdPv38w/sGex0Ra959+V3q1CPaZhFmZuWA9Vmji4gUpUDhiXr653rEhJqHtVRxKh/D6Tvkal1DMUk/z840+noKA8BNQytbjiHuLyiqrXM2pQ/ioLSl9GafUCSmuuWI2qhbV2bCY4zQBP9U/rw6xWwzVpLmurW0xrw2C5n2htsJOayx0r0d7L' \
			b'aa1ZQGvtFbW21Fh3TR2ADRp7OtpaaqqSFbSLdwY2aOoVtNQuoKVuQS31d1p6U1oajkdL3QJaOm1J3l1Lw52W3pSW1sejpX7fY/2bHt8fiBpel/nUYPnFIf1IbPUvKt17BASZXAqnonDmiiZ8Uj7WuePSvWudR+J1Q1vM9iypSTV0ydhJjO53Sim0s0pLa2O5' \
			b'MmvObNKtrQ6VnDtVy0zSwuqpwm4zSLu1yM1c3fRXUM9QHO175Zpyat3vkoudXNRLs6xu1ljGy7dFtFPS41pKL1pvbvgp6mWWO/FPh7NS1nqi7tT1PcKw/JznbPPQnYIuoKAGCmqWUlBzrAqKWpP536agqrrYb/fyJsYxIzo4vhJ0L2vpLtd/vO4xy8gyz/FG' \
			b'mBK82LcCHYTyNEejOAegNGb/SrOPWmctvQdV6wklEkntQ4lkOe0OOsTxl1QjyfikFvFy6BX3uiYaNE8NGptPnaJ7kIbNVhd3dVKhSyzJu/poatLN3COsid64O72hakgfRUPmxe1TcZp7K9YWe2/FReXurWpRIn+nRKRE5jiUyFTC6cEpUaguuPxIT/gHtFmg' \
			b'TTyHyTfSh6olgrzi0f9aAhsKbHZTrZ7ysJJsUwpWhKEScIvDJSuZv3RBDpoHLootoq/HRM3yoKyKPC43vxJmTavoK06bbAJWV64AC9+uhBVJYKdJDX2laYtpQDAnVFDllASlKyW2e3HNKqjrKKRcQG6Jmmy3SYCliySWR6CetPwaJon3QuRLmWQxMo+CLBPD' \
			b'IVynIYSUCVlQ4cNP5xR8torHbGn5xb9g424L5bnuUrx5M8i2IN44FrdNuJo/stIbCKkdLf8kvsnx5ecGcSx4e9gA7xQNkk5xEoCs1mytQXGPft5/z7/LU/EfIcDEFfe2999gZpU31/F3OR5bl+XdGuYj9lP1n+Y/vbBrr4VdIt/tT3hx23nxc9nhUw06LBHx' \
			b'yB9PSU+84cnjwHPnTpjz18kc9at2/xO24pHmOA5sM2fU7ekzx2dLzGKQiLjrN/7HMxnFE1UCgzjCa70Trzhy49IcE8WGv9RB3RhLmG4uwTTOCbkc63FHcHugBtdPqtrdpY73Lq7Xg+bsp58iZtPNPkXALScPQeC5EYf8q8PIv6lu3CH/+ir55xM0eyJIR9pc' \
			b'Tgy2urzjMWgviIeWcxOAOEwWh11KIvV2qbj1Nsm4Co6bLbeA25DOxCsIyB6qgEK1bwcBub6AigOsICkjv/03X15eGnY+e6opTp3qnjTVPU6KqzeG+BaBctd6s1DZsz9HIwNZurcbHYrBH6ie8vzcnh0EFLbq6U6S6qjnpNSuqpA8tVk4GujgCs+ujgfrIOZh' \
			b'+ngUN5HyxBch2/ooZRuqA3YQbHOUgq2rA3aYBVkfpWBlHvpQHQSrjlGwPCV6uA6C1UcpWFMdsINgB0OgKwh2a9d1YfH6ainHFpd+kBkEXcpBzIOB1M2PE64u77ra7HAG7tZo8x3bTy5LDLkfwPjsynJnG9XROIh9MB47RrGH6ngcxL59lHcEYq+r43EQ+/YB' \
			b'4BGIvamOx0Hs24eHhy92XnBwNA4m8e2Dx+OZ8uQVB0fmUAgqL9biZUVABB99xaUhRQFZKllowUtZZB1Lu1DFRwrq/vNippoXJ6ma19lxAXiIuUb9Jqe+KLbCopmR8zXkOb7nkwy4BCSMROujpgT8JnvSACoqWfSh4vFCHkdjxKUZsjN4JLauev+I3Qxic/EL' \
			b'hakG/x5i4w10KsgqkZoGlj+d/z/shdFE'

	_PARSER_TOP             = 'expr_commas'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	_UPARTIAL = '\u2202'
	_USUM     = '\u2211'
	_UINTG    = '\u222b'
	_LETTER   = fr'[a-zA-Z]'
	_LETTERU  = fr'[a-zA-Z_]'
	_TEXGREEK = '(?:' + '|'.join (reversed (sorted (f'\\\\{g}' for g in AST.Var.GREEK))) + ')'
	_VARPY    = fr'(?:{_LETTERU}(?:\w|\\_)*)'
	_VARTEX   = fr'(?:{_TEXGREEK}|\\partial|(?:(?:\\overline|\\bar|\\widetilde|\\tilde)\s*)?\\infty)'
	_VARTEX1  = fr'(?:(\d)|({_LETTER})|({_VARTEX}))'
	_VARUNI   = fr'(?:{"|".join (AST.Var.UNI2PY)})'
	_VAR      = fr'(?:{_VARPY}|{_VARTEX}|{_VARUNI})'

	_STR      = r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY - {'@'})))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LETTER})'),
		('LOG',           r'log\b|\\log(?!{_LETTER})'),
		('FUNC',         fr'(@|{_FUNCPY}\b)|\\({_FUNCTEX})\b|\$({_LETTERU}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}}'),
		('LIM',          fr'\\lim(?!{_LETTER})'),
		('SUM',          fr'\\sum(?:\s*\\limits)?(?!{_LETTER})|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?(?!{_LETTER})|{_UINTG}'),
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
		('IF',            r'if(?!{_LETTERU})'),
		('ELSE',          r'else(?!{_LETTERU})'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
		('VAR',          fr'(\\partial\s?|{_UPARTIAL})({_VAR})|{_VAR}'),
		('ATTR',         fr'\.(?:({_LETTERU}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"(?<!\d|{_LETTERU}|')({_STR})|\\text\s*{{\s*({_STR})\s*}}"),
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
		('INEQ',         fr'==|!=|\\neq?|<=|\\le|<|\\lt|>=|\\ge|>|\\gt|{"|".join (AST.Eq.UNI2PY)}'),
		('EQ',            r'='),
		('DIVIDE',        r'/'),
		('EXCL',          r'!'),
		('AMP',           r'&'),
		('DBLSLASH',      r'\\\\'),
		('COMMA',         r','),
		('ignore',        r'\\,|\\:|\\?\s+|\\text\s*{\s*[^}]*\s*}'),
	])

	_FUNC_AST_XLAT = {
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

	def expr_cond_1     (self, expr_ineq, IF, expr, ELSE, CURLYL, expr_cond, CURLYR):  return AST ('piece', ((expr_ineq, expr), (expr_cond, True)))
	def expr_cond_2     (self, expr_ineq, IF, expr, ELSE, expr_cond):
		return \
				AST ('piece', ((expr_ineq, expr),) + expr_cond.pieces) \
				if expr_cond.is_piece else \
				AST ('piece', ((expr_ineq, expr), (expr_cond, True)))

	def expr_cond_3     (self, expr_ineq, IF, expr):                            return AST ('piece', ((expr_ineq, expr),))
	def expr_cond_4     (self, expr_ineq):                                      return expr_ineq

	def expr_ineq_2     (self, expr_add1, INEQ, expr_add2):                     return AST ('=', AST.Eq.ANY2PY.get (INEQ.text, INEQ.text), expr_add1, expr_add2)
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

	def expr_int_1      (self, INTG, expr_sub, expr_super, expr_add):            return _expr_int (expr_add, (expr_sub, expr_super))
	def expr_int_2      (self, INTG, expr_add):                                  return _expr_int (expr_add)
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
		xlat = self._FUNC_AST_XLAT.get (func)

		return xlat (expr_func_arg) if xlat else _expr_func (2, 'func', func, expr_func_arg)

	def expr_func_6     (self, FUNC, expr_super, expr_func_arg):
		ast = self.expr_func_5 (FUNC, expr_func_arg)

		return \
				AST ('^', ast, expr_super) \
				if expr_super != AST.NegOne or not ast.is_trigh_func_noninv else \
				AST ('func', f'a{ast.func}', ast.args)

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

	def expr_frac_1     (self, FRAC, expr_cases1, expr_cases2):                 return AST ('/', expr_cases1, expr_cases2)
	def expr_frac_2     (self, FRAC1, expr_cases):                              return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_cases)
	def expr_frac_3     (self, FRAC2):                                          return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4     (self, expr_cases):                                     return expr_cases

	def expr_cases_1    (self, BEG_CASES, expr_casess, END_CASES):              return AST ('piece', expr_casess) # translate this on the fly?
	def expr_cases_2    (self, expr_mat):                                       return expr_mat
	def expr_casess_1   (self, expr_casessp, DBLSLASH):                         return expr_casessp
	def expr_casess_2   (self, expr_casessp):                                   return expr_casessp
	def expr_casessp_1  (self, expr_casessp, DBLSLASH, expr_casessc):           return expr_casessp + (expr_casessc,)
	def expr_casessp_2  (self, expr_casessc):                                   return (expr_casessc,)
	def expr_casessc_1  (self, expr1, AMP, expr2):                              return (expr1, expr2)
	def expr_casessc_2  (self, expr, AMP):                                      return (expr, True)

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
	def expr_term_3     (self, expr_num):                                       return expr_num
	def expr_term_4     (self, expr_var):                                       return expr_var

	def expr_num        (self, NUM):                                            return AST ('#', NUM.text) if NUM.grp [0] or NUM.grp [2] else AST ('#', NUM.grp [1])

	def expr_var_1      (self, var, PRIMES):                                    return AST ('@', var + PRIMES.text.replace ("'", '_prime'))
	def expr_var_2      (self, var):                                            return AST ('@', var)
	def var             (self, VAR):
		return \
				'partial' + AST.Var.ANY2PY.get (VAR.grp [1], VAR.grp [1].replace ('\\_', '_')) \
				if VAR.grp [0] else \
				AST.Var.ANY2PY.get (VAR.text.replace (' ', ''), VAR.text.replace ('\\_', '_'))

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

		if pos == 1 and rule == ('expr_func', ('FUNC', 'expr_func_arg')):
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
# 	a = p.parse ('sin**-1 x')
# 	print (a)
