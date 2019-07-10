# TODO: Fix! func (x).something. !!!
# TODO: Concretize empty matrix stuff.
# TODO: Concretize empty variable stuff.
# TODO: remap \begin{matrix} \end{matrix}?

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

		ast_dv_check = (lambda n: n.is_differential) if v.is_diff_solo else (lambda n: n.is_partial)

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
	if ast.is_differential or ast.is_null_var: # null_var is for autocomplete
		return AST ('intg', None, ast, *from_to)

	elif ast.is_div:
		if ast.denom.is_mul and ast.denom.muls [-1].is_differential:
			return AST ('intg', ('/', ast.numer, ast.denom.muls [0] if len (ast.denom.muls) == 2 else \
					AST ('*', ast.denom.muls [:-1])), ast.denom.muls [-1], *from_to)

		if ast.numer.is_differential:
			return AST ('intg', ('/', ast.One, ast.denom), ast.numer, *from_to)

	elif ast.is_mul and (ast.muls [-1].is_differential or ast.muls [-1].is_null_var): # null_var is for autocomplete
		return AST ('intg', ast.muls [0] if len (ast.muls) == 2 else AST ('*', ast.muls [:-1]), ast.muls [-1], *from_to)

	elif ast.is_add:
		if ast.adds [-1].is_differential:
			return AST ('intg', \
					AST ('+', ast.adds [:-1])
					if len (ast.adds) > 2 else \
					ast.adds [0] \
					, ast.adds [-1], *from_to)

		if ast.adds [-1].is_mul and ast.adds [-1].muls [-1].is_differential:
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

	return AST (*(args [:iparm] + (args [iparm].strip_paren (strip_paren),) + args [iparm + 1:]))

def _expr_func_remap (_remap_func, ast): # rearrange ast tree for a given function remapping like 'Derivative' or 'Limit'
	expr = _expr_func (1, None, ast, strip_paren = None) # strip all parentheses

	if expr.op is None:
		return _remap_func (expr [1])
	else:
		return AST (expr.op, _remap_func (expr [1] [1]), *expr [2:])

_remap_func_Limit_dirs = {'+': ('+',), '-': ('-',), '+-': ()}

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
		d = commas.pop ().as_differential ()

		if commas and commas [-1].is_num:
			ds.append (AST ('^', d, commas.pop ()))
		else:
			ds.append (d)

	return AST ('diff', ast.commas [0], AST (*ds))

def _remap_func_Integral (ast): # remap function 'Integral' to native ast representation for pretty rendering
	if not ast.is_comma:
		return AST ('intg', ast, ast.as_differential () if ast.is_var else AST.VarNull)
	elif len (ast.commas) == 1:
		ast = AST ('intg', ast.commas [0], AST.VarNull)

	else:
		ast2 = ast.commas [1].strip_paren (1)

		if not ast2.is_comma:
			return AST ('intg', ast.commas [0], ast2.as_differential ())
		elif len (ast2.commas) == 3:
			return AST ('intg', ast.commas [0], ast2.commas [0].as_differential (), ast2.commas [1], ast2.commas [2])
		else:
			ast = AST (*(('intg', ast.commas [0], ast2.commas [0].as_differential ()) + ast2.commas [1:] + (AST.VarNull, AST.VarNull)) [:5])

	raise lalr1.Incomplete (ast)

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
			b'eJztXW2P3DaS/jMHZAZQA03xVflmO96scbaTdZxgD4PAcBxnEVyc5Bxn9w4L//erqocUSVGt6Z7ume4ZD4YjiRRfqkr18KVYUp9dfPYfb3/98bPus2dPnn/7DZ2fPH9Jx6dPntHxm2/l+LcXkvTVl3T8y7fPH3Hk8V847eGDF3T8+sGLx8+fctkvn3/14vGr' \
			b'R9++ePpfnPfFg0fxpOK550KPv3z17MHLF0/+HiMPq9h3VezrMSa1cisPqZ7/fPySL795+ULIfEjH74SW50Lyo6+ePXuQyrzIZUZq+eLFky//ykw8ePY1Hb94+PSbpw+++StdPn7+RSaQIw+r2HdVLBPINbwUIh5RE1zz47+JQOX09VMR7xdPvnvyxWPO88VX' \
			b'L4WDB5EFFtGDly/H8hx//PdHzObLr+jw5vX7tx9e/fb+1Y8//PLHh9fvKent//7+/tW71x9evfntlzL6/rd/TaJ/pPgff/7+diz605+/vnn1+v0/8s0f0uWvf75Llx/evh+vf3j/+s1/v/2Qom/+fP/L/xVNjRVTtnT9O9H9a4q8/mGk5PWHDyMhv2eCf3r9' \
			b'5kNJX6ZtJOKfmflffh5Tf/51LPfuz19e/fzu9xT98ed/5suffhpZfPuPsgBdjKT9+GOu9e3/pOvxamT/t3fvXleRPz77vrs4W2nTaXfe4cLLRbcyfO7X3Vnoho4S+qEbzlOapIzRVa/4ysm/obg/z3GVoyupWw04GHseo1SH1GS5Ma5PcWs9inFqTBsTVr2Q' \
			b'28s/xzXu8AVXGdNRP+WOichkujNuk+pzKYHq5CtOFUrUGgdDhZU6nyRViXxJV1TpynY6dCu0aviCc3gcDGinq5UK0ioRr4jgXvP/+ZhURZWJF5zGxUmkzD0kjxjLhp6Or5JdEwtVip/G9LpMITqlYRaIi1dnSiLnwig/TU13U3wluYifsx5tcX24GRPHyEqB' \
			b'Fd2dEdnEIzdiOhOEDWo7nG++zxpKCrZNNlXnWil5HiRu6JhirVGd7ktVo5tjek5xSNE5xSPF5JSAFJtSSKsERxoHFgfKax2VVPc4ULFVrFv3cslXKt08j1GKpRuS5OXf9InFGNc5vhI9UwoHEv35eb6kqyCPFM888AVT7jsQ3iuWkxqxiEo5NaYVCUqEr0c8' \
			b'MeIAuYADacN5jBPcJQ/dEbWOYg6dkWZJ+memeJx61AqWYHyYNmklpZ1pN6pljKo6wY+tUNRAm12HHosv+niximBjsKCfIkL0OXWQF6QtviPiiShqnPRBSOpF3MZ0vuMu0tnOuc75zq87r5gHUgPqW6h7cqFz3N9R89QRsI6aobPrzqouUKDHTJxS70EVe2aZ' \
			b'kMVKHljyniqUB0FiNh3V1XndeWrUdt6xXkGJSa1s31k6UibbWddZz2pOD4MwR/pP3AQiNHSB+vF1N6jO9993Z1TvOQ0BzN+5qLGciElinDWfoxp5esR6Lzcvzoykn5EA+IQKQrw3SMxZnFxM9dLaLZGMA0f0KMF9D+7BdG8iS31kUQR3mnwMYMCAUiNP0Q9d' \
			b'WN9qxTU+sgWVNdA4u4bmhhCfmmjcnUVviFwrgC+eevCuAUwtz52mLeaIlF7wxOYOP4kLGXjOZbgZpQ2QHZMmYEMPmaagu0C5bRfcMSkza3SjabzoochepFfQKKNGHJQitFXskOOwg/7YonfmRqU+0fk7o11nDix7c5cxdOYxQvnIrRYduVJNOk5ZtLp6FbEX' \
			b'tVKV6zunO2c6t+6c6mzo7HB3JE9cmk+CS/tJcOnuPpdnFrPzHlMehcEgIHHA4DLgnu/HJU6PtU1/h4YGWZYRQ3eAEWKBGLnVLIiK3VLawy2m3QmobxnN7rbRzPabXlbVglQ2grDKnC69LoBeI+oxWVYYkf/EbuWxDoH5YP/l+Xq0UfSwUfSwUfS8kOlFmrxq' \
			b'55M2oFVbDFMaK5hxso/xClP+W9/Zn5m0iJPB+Xh0KGiydlH40oEf2VbCy3ZQM5wANTQwYIkdzFEfFdFhDwNKl0wPPSwOPYwL6Cnu2OTQi37fVYvBBdt9eth97jCbZxgSfBwh/F1bwWgB35UVoDD8scFHhlgNUTncdejB3DqO8g4rQ4tR/8xGK7pBWUjburRc' \
			b'5A1ZkrU+xxpFt5MGSZtudoWZVI5qRHWcSOmT3j264EmePuVJnszu9K1eN/Kss4/zRI15osY8kU6DwlRR9IUIjUkyUeRcKmqW6dO8UWMbQsPyz6cQ4RAwvB1vuwrQMsCQBk9UkwZk777VSkVeIYAoB8T0OolBx56rR5fFXePdEsMF97x3aQjjoUNj6NAYOtC7' \
			b'm86ceO/OVDXjGVOIbsigGzKypa44Kv2OOfqqhLsy6SpBvgZpVJNJoz/QZgAwuesiwtKoH+KQTuACtxbc2jukmTJk3CWGWP3kccmRarbxwdvUeeLB2/hoHR6tw6OlEzEKZXbYNnYxo79dtrgL5sqDKy88Y1ULswoR5ycGL+aV8xMPATIJKB1igXALBTDcNpqJ' \
			b'jFtGM6vGEB2s1tHDai3DxLq7oNLUtcRGuyESEauzsiAfpI2eOx+QywRp4SQwD7M8M6EDTwDjZHBgeTFLjj1qIBHS7oEaWjM91Oaar6nVtaF/anpN8+I1tc/EMCk8T2Z62ELAJgJhm9LYqMreJ+xtwG4D7DXFLlPsz8POPGypZJ859rHixSbPU3kfmchSvLhj' \
			b'/0DeYvSaZCLO7OLl6sQNmb2yqb9lx3LqZ1dePGM78WAnnlaGnXQpNwl8RfWviKuVEUdsysu1UBp7zXNl7DZMty27syrxjV3R01rRg1oN7GLPjtXcBPtdU1HjUDWxs2IvdnaTZWfaEH3BPTuir8VpWRxq2e2VnYeZIqqBCXTROZ1yGXHbptzs+EzEBXYzpjwU' \
			b'6KmIby7JZWXZ652TuSg3TNfUA608+1TTP1+yJzbzwawyPdS+YfbX3/PqhVVqRpVM0qZQKFTCDka2rFyi6vJKQ1Ixmatg6NuobjUuMOPGIiTqoBU1XCdNFHABeqVKjs5VDKJ+s1quiUNhcUk9zYyKUjq7psyq6jqrK8OVoVqprYHqsr2DbSFsBmELSVJlnqiy' \
			b'tyi76VZqHVgqG5Q4jGpcKzIVDnzwrU6zgvGh0OsQ/5b0O1R/rOlqHUTbbVT2sBaFD6PKc+NayFCsxhPlH6sioXIVje5z1mERAWGKATBR48CCkIgEtJjRYIEIlj2T1a0yOiJ5BUa6fzv9OYObHjid7UcZ8y+SK+/loDE3gpUSKG4ZH3PYCBEfh8TGtri4DAtK' \
			b'unM+FmCQKFIjGER/MxrkTo0CKSPHAgf80FJYwkKZLxdgYk3T/6vlIaCqgYeDCgb51gIKhNgKBomDDARVjwepvQYHUgzqn9uuEKD6z7nzIVX5nEFKj5jO5qO8qHCPhBtEgowJfCyR4IAEl5HgaiS4FglOkFDPdJTLYREJbiYIElyLBLeMhLKGFgnjrSUkuAYJ' \
			b'kYMCCa5GQmyvRYLLSBjb3hIJ5h4JN4gEVs2BF1IlEiSK1IgEviyQIHdqJEgZORZI6FUOS0go8+UCfo1aayRI25uRUNXQICHfWkCCEFshIXGQkSBUZCSk9hokSDEgIbe9JRLsLkg44pKi32lVsYSQpVXF+gZWFpeiRQtadI0WDbTojBZdo0Xn0MBGC2x0DZuy' \
			b'wBJs9EwQ2OgaNnF1Ie2jTY1GdUilpjAqa2xhlBvbvMjoI5p0g6bIWIEmLWiSEhFQseUWUDoDaqxqS0C5e0CdGqCsAMrWgMLynE8JULYGlM2hAZQVQNkaUGWBJUDZmSCAsvOAsgCUBaAsAIVSU0CVNbaAyo0tAMoCUI31KjFWAMoCUMUIFVtuAWUzoMZsWwLK' \
			b'3wPq1AAlK5u+Xtn0WNn0eWXT1ysbfiQpNICSJU5fL3GqAkuAcjNBAOXmAYVljnw1AXl1SKWmgCprbAGVG1sAlAOgmpVPYqwAFFY+UiICKrbcAiovfjIVWwIqHBpQxZbLDcAKrw3PI2t9+8GlZbGk68WSxmJJ58WSrhdLvIeVwhRcUliOJMNBPqeC06TYAsTK' \
			b'fLmAX6NuQIyzRoRpLJ80VlByCrGQ5KpBVtY5zC2oihY340wEYsFIhbPEXcaZxrpKSgBnMU+LM52XVpmKOZw587lYc1q4DQy3tAe4H+jUKQ1kfhzLFrYXbwR2/aGg1092JTlhZk+HkxMM+xqGRWi2dQzqk2MxzFVlljA4FwSD/ewwJySIxggIsdUTS00RmKpj' \
			b'+UtOtbDlmVpewGIPLPYNFiOX7Uaoxg4QPzgBJDLOADJv/2QhTAHJnBAQRXEcnT7iFYYDDHsnhcA7MJXUwFm9XaSxXaTzdpGut4tY+ik0MLMoL8cSZmWZJZiZmSAwM/Mww/YRnzQa1SGVmsKsrLEd5XJjC8gyQFazo5QYK0a5CCyTR7nYcguqvKmUqdhyNqnU' \
			b'/frs1EAlBg9dGzx0HLuywUPXBg/2n0qhmUKKwUPXBo+qwBKi7EwQRM0bPDQMHhoGDw2DRyw1RVRZY4uo3NgComDw0I3BIzFWIAoGD50NHqnlFlHZ4JGp2BZRO3ksnBKilpZmtx5UXkDla1B5gMpnUPkaVD6HBlReQOVrUJUFlkDlZ4KAyo+gEloipjww5YEp' \
			b'D0yN5aawKutsYZWbW4CVB6x8A6vIWgErD1j5DKvYcgsrn2GVid9pOaZ28oK4R9cNoWsQdNU+dBJFakLXUKNryKFB19DFj/CW6CoLLKFrmAmCriGja8joGoCuAegagK6x3BRdZZ0tunJzC+gagK6hQVdkrUDXAHQNGV2x5RZdQ0ZXJn43dO3kWXGPrptBF0ND' \
			b'zLMluiSK1IguvizQxXJPYYouKYxvmWd0VQUW0FXmywU8ThFdQgvQJc2jSY0bUSlQYIKuqs4GXUVzm9EltVpwUaErsZbRJbQha0RXarlBl5QEugrid0PXwb017k33h4SZmO5Nbbo3MN2bbLo3teme5Z5CAzMx3RuY7g1M9wam+6rYEtjUTBCwZdO9yaZ7A9N9' \
			b'dH4yMN3nclOwSSpLPZVpAJebXAAcbPemsd0n9grAwXZvsu0+tdwCLtvuCwZ2A9zBvTnuAXdIwPUCuNpKL1GkJsDVRnpThAZwYqE3sNCbHoDrAbiy2BLg5oIALtvphaIIOJjpDcz0Bmb6XG4KuEm1Ld5yiwt4g33eNPb5xF2Btx54yy9opJZbvGXTfEH/bng7' \
			b'uLPHPd4OiTdxTTS1a6KBa6LJrommdk1kiafQ4E1cEw1cE/mkkU1Pii3hTc8EwVt2UBSKIt7gn2jgn2jgn5jLTfE2qbbFW25xAW/wUjSNl2LirsAbvBRN9lJMLbd4y16KBf274e3eF+Sk8Sa7Y6beHTPYHTN5d8zUu2Ms7hQavMnWmMHWGJ+0xmlSbAlvZiYI' \
			b'3vIGmVAU8Yb9MYP9MYP9sVxuirdJtS3ecosLeMMumWl2yRJ3Bd6wS2byLllqucVb3iUr6N8Nb8NB8da88X4wyLn4yv0nCjx+R33gh1G9uxXw7lZ+pVfV7/SqkEPzEpe81avk6wGMPfnZJ43TpOTS21xhJsjbXGHEnsJOmuJGBRcG9IAGHZsuy0/f85pU377q' \
			b'lVvejEGp2IKhCoOJy4xBIQ9Z00tfseX2pa8wYrCgfycM9tfhCHJSw566/QDsZeTr65Gvx8jX55Gvr0c+9vk1MTR+IQ7l5ehx0hqnPhfrlwe/Ml8ugHYTAPs8+PUY/HoMfj0Gv1xu6m1cVxtmfY5zows+xxj/+mb8Swxm7EX3qz6PfzHPjM9xHv8KFnbD3sGd' \
			b'RU4KeLcddUaGPVMPewbDnsnDnqmHPRNyaOabMuzx0ePE802MeVWxpflmmAky38xjnsneIwZjncFYZzDW5XLT+eak2na+mVtcmG9irDPNWJe4K+abGOtMHutSy+18M491Bf274W3ZlcTVkFP3qDvKZFM8S1TtWaLgWeIw1jl4SKnsXMKKHyQbBW6i9S+RKuTo' \
			b'cWJOPOabPofF+aafCTLfzF4mKnuZKHiZKHiZKHiZ5HLTeeak2naemVtcmGfC0UQ1jiaJu2KeCUcTlR1NUsvtPDM7mhT074a9gzua3DrUqYg8fcLos7I3buu9cYu9cZv3xm29N85CTmGKOyksR48Tf1puLbirii3grsyXC3icIu5s3iG32CG32CG32CHP5Sa4' \
			b'm1bb4K5oETLoI58t+iy2ym2zVZ54zOiz2Cq3eas8td+gz+at8oKL3dB3cEeUW4e+Ux7zrGyV23qr3GKr3OatcltvlbNkU2hQJ1vlFlvlFlvlFlvlVbEl1KmZIKjLW+U2b5VbbJVbbJVbbJXnclPUTaptUZdb3DzaWeyU22anPHFX4A075TbvlKeWW7zlnfKC' \
			b'/t3wZmnRfj0fuzzkly7NBkyoGSwsfBJnTu9nv3jJUj3Kxy6v50OX8m2mg37sMmrghg9eEjWXa1U40FdU/fV/SDVcQb24S+U0X3SrFOffX598XDXsqmtqOJi+zXxclUVyIx9YZZld4SOrGKnyJmoaqaY66Hfp2czeX/LFhEAfu5ezG1QxbOjp9vyur2o9uA/x' \
			b'bV8Fz2yl3J4qqMylaniZCrL85tTQmdnujwZdRcOtch/xc1xXH17NYT4nTTK9sS9K63ntuw7Nm9E6NeyveUsfUuz9YTq+yzVOz2ncpsF2uLYp3JYKJiucvXWM7vHclF+uu5Y53e36grl8cn3YU9/wjQUtw8LVJno8cGzSPerpLPV0Vn/ED/1cHG0RMdhucDfQ' \
			b'vfESmq/Dtl3cbVg/KKlzuN4uTay20lDYslsjyo6oUOZep/bTKW5C3Yxerdx6F73q99UrtZ9q6UNo1yYj4CYtMyejaW7ZU+Nq2sZl9L4a5xq/i5Wb/+oNJmlX0j69r/b1h+nYBn/Avm1J8+6s1pUax+wfpp9b0LgraJvZV9v0gbQt3GvbIbXNnKS22X21bdO2' \
			b'3K7aNtxr2yG17VDmjsNqm9tW29yVlgh9vd+7cX9hSc+WtnMPsHUlv7qhD6prrGIkGD5dfaXgC2WLm66XKtxmBbvkt6r228DiXwvzYVbHun/34XPC3Uf88PS9sh1e2bB54Pdalkolt0XZwPNlyha6i6Ptxl+TqYNkeIVdeH3iZo5rMWuowtVq+y13auPiSCpz' \
			b'jZax7VXlpNXk2ixfW6sHMXws9TiGiqy75mdAa3WxN6wu3OCW2iLbzQdUGHvJmMQbp91qXnPmfpiTyL/4ZPuZQmt4tXLfx5RuDzSBkW92U6Ofrobwcz3NYYjdmf1RVYT6ENYK6lLY+sxOqaIu+lNWl3Cy6hI6e9weZYO6GPm54t6S9Hi9bGV+Y+WFLFaY7ZSE' \
			b'HkZUA3nkbvnxyiNtHiePB/EZsRR2fCTiyZkWpGsIdUGIfk5owrobWd/R+MBmh0ttDvvYFRbRoKciXIuG82l3BedSu1gA9ljnb9ZibpyeSbmWJ4mnh7PTk1nuua7leVTPQl25p9l2vnJw6UfR8zx1LaIP8paY0kHmbcz68P05XZ+t5HV2Je/DE6nUN4oLG7/T' \
			b'ye7kXnwm2fkJ/mgMslW/qQgNTvlPsuoiq/xIQ/nekZXPHZTvBclmfnqDB2/o8JeVO/4j4WrZ0UhBXOzYUZi/s9xp8U2Pd2QXQjzOhQpzCCqo1DZ/0qC9pEF6TFu1abv2jy2fM+nSrnzrUZlLmramaX29iQInk4eZP17MFjFS2zEmpPhtScH7ZVsTRDq54S9N' \
			b'YmbvCk1hN5rwztt2lEVX/NEFnygduqW/NNXacHcyOWLq5cNL4ebo5ze+MBO9riBs4VeNbpIv1V1zAF/qanzRWrphLezCXt9dJfCMf5LEE/mlQmCzj2z2B+HUz3Or3RLHPKzzOgcX+4S2krlqwbg+PuO2u9kAxs2U8eLd4/gzVV5eM95CDk7GIn552BavDdev' \
			b'CtfvBTPAeLBfzwhqvSSsoTtO4A9I6K3yQrz26HrFhoYbDWDcXapXW0qgVKfN0thVgdj2UgSv4hEX2wderqAYL1Tmsxg101YdIDN/4jLz3ckECCycuMBCdzIBAhtOXGBi5jqNgNXx+rQFxjaXUwkQmDpxgenuZAIE1ky5rySwS6dee4rNdfsHNrlOk0hfrlof' \
			b'xNdM3G9y/rq7HEO3HPAxnUuzbRPYUrpLAcjzqOuBneXJRuYTDRBnM/8/bXG67lQDxHn5quKkxOm7Uw0Q5+ULjpMS59CdaoA4Q7GBy3JAKn/GQEehQjbEJmcZ4i7YuNVlYWzkV855yzN04ufFu+lUiL+uuRaRIJOSH/gaHwuJks3Uml+AG4K8KmKwfyEvhrY5' \
			b'TVcEZNRNRn46nNl2ZVBRf/g1LGVlf8nR9O/78/8H2QiMAg=='

	_PARSER_TOP             = 'expr_commas'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	_TEXGREEK    = '(?:' + '|'.join (reversed (sorted (f'\\\\{g}' for g in AST.Var.GREEK))) + ')'
	_LETTER      = fr'[a-zA-Z]'
	_VARPY       = fr'{_LETTER}(?:\w|\\_)*'
	_VARTEX      = fr'(?:{_TEXGREEK}|\\partial|(?:(?:\\overline|\\bar|\\widetilde|\\tilde)\s*)?\\infty)'
	_VARTEX1     = fr'(?:(\d)|({_LETTER})|({_VARTEX}))'
	_VAR         = fr'(?:{_VARPY}|{_VARTEX})'

	_STR         =  r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY      = '|'.join (reversed (sorted (AST.Func.PY)))
	_FUNCTEX     = '|'.join (reversed (sorted (AST.Func.TEX)))

	TOKENS       = OrderedDict ([ # order matters
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LETTER})'),
		('LOG',           r'log\b|\\log(?!{_LETTER})'),
		('FUNC',         fr'({_FUNCPY})\b|\\({_FUNCTEX})\b|\$({_LETTER}\w*)|\\operatorname\s*\{{\s*({_LETTER}(?:\w|\\_)*)\s*\}}'),
		('LIM',          fr'\\lim(?!{_LETTER})'),
		('SUM',          fr'\\sum(?!{_LETTER})'),
		('INT',          fr'\\int(?:\s*\\limits)?(?!{_LETTER})'),
		('LEFT',         fr'\\left(?!{_LETTER})'),
		('RIGHT',        fr'\\right(?!{_LETTER})'),
		('CDOT',         fr'\\cdot(?!{_LETTER})'),
		('TO',           fr'\\to(?!{_LETTER})'),
		('BEG_MATRIX',    r'\\begin\s*\{\s*matrix\s*\}'),
		('END_MATRIX',    r'\\end\s*\{\s*matrix\s*\}'),
		('BEG_BMATRIX',   r'\\begin\s*\{\s*bmatrix\s*\}'),
		('END_BMATRIX',   r'\\end\s*\{\s*bmatrix\s*\}'),
		('BEG_VMATRIX',   r'\\begin\s*\{\s*vmatrix\s*\}'),
		('END_VMATRIX',   r'\\end\s*\{\s*vmatrix\s*\}'),
		('BEG_PMATRIX',   r'\\begin\s*\{\s*pmatrix\s*\}'),
		('END_PMATRIX',   r'\\end\s*\{\s*pmatrix\s*\}'),
		('FRAC2',        fr'\\frac\s*{_VARTEX1}\s*{_VARTEX1}'),
		('FRAC1',        fr'\\frac\s*{_VARTEX1}'),
		('FRAC',          r'\\frac(?!{_LETTER})'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
		('VAR',          fr'(\\partial)\s?({_VAR})|{_VAR}'),
		('ATTR',         fr'\.(?:({_LETTER}\w*)|\\text\s*{{\s*({_LETTER}\w*)\s*}})'),
		('STR',          fr"(?<!\d|{_LETTER}|['}}])({_STR})|\\text\s*\{{\s*({_STR})\s*\}}"),
		# ('PRIMES',        r"'+|(?:_prime)+"),
		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
		('CARET1',       fr'\^{_VARTEX1}'),
		('CARET',         r'\^'),
		('DBLSTAR',       r'\*\*'),
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('CURLYL',        r'{'),
		('CURLYR',        r'}'),
		('BRACKETL',      r'\['),
		('BRACKETR',      r'\]'),
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
		('ignore',        r'\\,|\\:|\\?\s+'),
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

	def expr            (self, expr_eq):                      	                return expr_eq

	def expr_eq_1       (self, expr_ineq1, EQ, expr_ineq2):                     return AST ('=', '=', expr_ineq1, expr_ineq2)
	def expr_eq_2       (self, expr_ineq):                                      return expr_ineq
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
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_func_arg):  return _expr_func (1, 'sqrt', expr_func_arg, expr)
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

	def expr_frac_1     (self, FRAC, expr_mat1, expr_mat2):                     return AST ('/', expr_mat1, expr_mat2)
	def expr_frac_2     (self, FRAC1, expr_mat):                                return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_mat)
	def expr_frac_3     (self, FRAC2):                                          return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4     (self, expr_mat):                                       return expr_mat

	def expr_mat_1      (self, LEFT, BRACKETL, BEG_MATRIX, expr_mat_rows, END_MATRIX, RIGHT, BRACKETR):  return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_2      (self, BEG_MATRIX, expr_mat_rows, END_MATRIX):                                   return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_3      (self, BEG_BMATRIX, expr_mat_rows, END_BMATRIX):                                 return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_4      (self, BEG_VMATRIX, expr_mat_rows, END_VMATRIX):                                 return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_5      (self, BEG_PMATRIX, expr_mat_rows, END_PMATRIX):                                 return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_6      (self, expr_curly):                                                              return expr_curly
	def expr_mat_rows_1 (self, expr_mat_row, DBLSLASH):                         return expr_mat_row
	def expr_mat_rows_2 (self, expr_mat_row):                                   return expr_mat_row
	def expr_mat_rows_3 (self):                                                 return ()
	def expr_mat_row_1  (self, expr_mat_row, DBLSLASH, expr_mat_col):           return expr_mat_row + (expr_mat_col,)
	def expr_mat_row_2  (self, expr_mat_col):                                   return (expr_mat_col,)
	def expr_mat_col_1  (self, expr_mat_col, AMP, expr):                        return expr_mat_col + (expr,)
	def expr_mat_col_2  (self, expr):                                           return (expr,)

	def expr_curly_1    (self, CURLYL, expr_commas, CURLYR):                    return _expr_curly (expr_commas)
	def expr_curly_2    (self, expr_bracket):                                   return expr_bracket

	def expr_bracket_1  (self, LEFT, BRACKETL, expr_commas, RIGHT, BRACKETR):   return AST ('[', expr_commas.commas if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_2  (self, BRACKETL, expr_commas, BRACKETR):                return AST ('[', expr_commas.commas if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_3  (self, expr_term):                                      return expr_term

	def expr_term_1     (self, STR):                                            return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_2     (self, SUB):                                            return AST ('@', '_') # for last expression variable
	def expr_term_3     (self, expr_num):                                       return expr_num
	def expr_term_4     (self, expr_var):                                       return expr_var

	def expr_num        (self, NUM):                                            return AST ('#', NUM.text) if NUM.grp [0] or NUM.grp [2] else AST ('#', NUM.grp [1])

	def expr_var        (self, VAR):
		return AST ('@', \
				'partial' + AST.Var.TEX2PY.get (VAR.grp [1], VAR.grp [1].replace ('\\_', '_')) \
				if VAR.grp [0] else \
				AST.Var.TEX2PY.get (VAR.text.replace (' ', ''), VAR.text.replace ('\\_', '_')))

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
		'RIGHT'   : ' \\right',
		'COMMA'   : ',',
		'PARENL'  : '(',
		'PARENR'  : ')',
		'CURLYR'  : '}',
		'BRACKETR': ']',
		'BAR'     : '|',
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

			return self._insert_symbol ('PARENR' if self.stack [idx].sym == 'PARENL' else 'BRACKETR')

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

		if self.autocompleting:
			stack = [s [2]]

			while stack:
				ast = stack.pop ()

				if ast.is_var:
					(expr_diffs if ast.is_differential else expr_vars).add (ast.var)
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

if __name__ == '__main__':
	p = Parser ()
	a = p.parse ('\\frac1x')
	print (a)
