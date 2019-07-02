# TODO: Merge trigh into func.
# TODO: Change vars to internal short representation?
# TODO: 1+1j complex number parsing?
# TODO: empty sequences

# Builds expression tree from text, nodes are nested AST tuples.

# FUTURE: verify vars in expr func remaps
# FUTURE: vectors and matrices, Python long variable names, Python '.' members, assumptions / hints, stateful variables, piecewise expressions, plots

import ast as py_ast
from collections import OrderedDict
import os
import re

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT

def _ast_from_tok_digit_or_var (tok, i = 0):
	return AST ('#', tok.grp [i]) if tok.grp [i] else AST ('@', AST.Var.SHORT2LONG.get (tok.grp [i + 1] or tok.grp [i + 3], tok.grp [i + 2]))

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

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast.numer.is_diff_or_part_solo:
			p = 1
			v = ast.numer.var

		elif ast.numer.is_pow and ast.numer.base.is_diff_or_part_solo and ast.numer.exp.is_pos_int:
			p = int (ast.numer.exp.num)
			v = ast.numer.base.var

		else:
			return None

		ast_dv_check = (lambda n: n.is_differential) if v [0] == 'd' else (lambda n: n.is_partial)

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

def _expr_func (iparm, *args): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	if args [iparm].is_fact:
		if args [iparm].fact.is_paren:
			return AST ('!', AST (*(args [:iparm] + (args [iparm].fact.paren,) + args [iparm + 1:])))

	elif args [iparm].is_pow:
		if args [iparm].base.is_paren:
			return AST ('^', AST (*(args [:iparm] + (args [iparm].base,) + args [iparm + 1:])), args [iparm].exp)

	return AST (*args)

def _expr_func_remap (remap_func, ast): # rearrange ast tree for a given function remapping like 'Derivative' or 'Limit'
	expr = _expr_func (1, '(', ast)
	ast  = remap_func (expr.paren if expr.is_paren else expr [1].paren)

	return AST (expr.op, ast, *expr [2:]) if not expr.is_paren else ast

_remap_func_lim_dirs = {'+': ('+',), '-': ('-',), '+-': ()}

def remap_func_lim (ast): # remap function 'Limit' to native ast representation for pretty rendering
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
		return AST ('lim', *(commas [:3] + _remap_func_lim_dirs.get (commas [3].str_, ('+',))))
	elif commas [3].is_eq_eq and commas [3].lhs.as_identifier () == 'dir' and commas [3].rhs.is_str:
		return AST ('lim', *(commas [:3] + _remap_func_lim_dirs.get (commas [3].rhs.str_, ('+',))))
	else:
		ast = AST ('lim', commas [0], commas [1], commas [2])

	if commas [-1].is_null_var:
		return ast

	raise lalr1.Incomplete (ast)

def remap_func_sum (ast): # remap function 'Sum' to native ast representation for pretty rendering
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

def remap_func_diff (ast): # remap function 'Derivative' to native ast representation for pretty rendering
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

def remap_func_intg (ast): # remap function 'Integral' to native ast representation for pretty rendering
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

def _expr_curly (ast):
	if ast.op != ',':
		return ast

	c = sum (bool (c.is_vec) for c in ast.commas)

	if not c:
		return AST ('vec', ast.commas)

	if c != len (ast.commas) or len (set (len (c.vec) for c in ast.commas)) != 1:
		raise SyntaxError ('invalid matrix syntax')

	return AST ('mat', tuple (c.vec for c in ast.commas))

#...............................................................................................
class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJztXfuP3DaS/mcOyAygBsS35N8cx5s1znayjhPsYRAYTuIcgoudnOPs3WGx//tV1UeKpKRudc/0TD9mMBw9KD6qivVRZBWpvrj67MWzl99+81nz2bOXr+n4/NkLOn7zrRz/9kqivvqSjn/59uUTvnn6F477/PErOn79+NXTl88575cvv3r19M2Tb189/w9O' \
			b'++rxk3hS8aw509Mv37x4/PrVs7/Hm8+ru++qu6+HOymVa/mcyvn3p6/58pvXr4TMz+n4Uoj9Tij6t3cffkpZ+P7JVy9ePM5ZB6L54vGLr+n49OUXmagvPn/+zfPH3/w1xmf6+O676i7T9+rZl399HTO/FiqeUBUc8/RvIlc5ff1cpPzFs++effGU03zx1Wth' \
			b'5HHkRKWMfPH070+Yza9fPXvxlLO9/ooOP779+O7Tm98+vvnph1//+PT2I0X98ecP/5CLd//7+8c3799+evPxt/8Z3f6R7v/48/d3Q9qf//zw45sP7/4z3f/42/v3b3PKH+iyKPnDn+/T5ad3H4frHz6+/fG/3n0ayvjz46//V9Q+1EXJ0vXvxMSHdPP2h4G4' \
			b'3zPdP7/98VNJZqZqqLgg7ddfhthfPgz53v/565tf3v+ebn/65R/58uefB7Yy/5yBLgbKfvopl/ruv9P1cPXZ983VxcqYxvjLBheBL1Sz0nIOzUVouoYijGu6yxQnMcPtSnV8ZeXfts3KXeb74pYu6Kw1l6l6qiJwqTpcpugYmWNW2shVwEF7quuyjkm39IAv' \
			b'lBTeDYWjbo6OkTmGKuAryirkd/JvKb6/rO7bHEMXnJdF1Ri6NSiLL1gUDgcLouhqpUSuxNeF4gpb/r8conR5q0y84Di+IvmRzHQUs9zxU9Uwt0W0m9z5KmZ615cxRKcwwW1q49VFKzeiE9J0hrKk+5WkUi0xEOsaHsbI4WalpFWI9wvdkMi5DYhrK/qjidQo' \
			b'qdnnrI6kTdskG6VaQZYkbmgac2nahkPWNyY1xecYhxidYzxiTI4JiLEphpRJJKNwYHFAS42KaknJ5cARJj4botItP6ErJ/9WJ37ivcn3K1GqXv5JypeXwxVdeGk88Oj5gmm0DXSdBHcRMRbbv2MRZSzmWGo9FZspxZFyypXHgdr9Mt5TLyD10BMGlsIDurXQ' \
			b'FVIiUzScGdqfZRWbzQz6R5wZPyhgvG3riJBr6RsLDaYq2nSh4gVVl640aGH0UtWWWxHNnKLonqIv61TjFOmebqXdtLAcGYuyypF6Po7vcjyERMVTb0cd8hUpRcM8SGdKHRD3wH3j28arxuvGu8Z7VmtSPSqRivOm8ZZVhrTE0gV3QcwgAST4JgTWO6qHu3fL' \
			b'zUziNNwTcocadBMoV0OFNr5rfN+EtgnSyVBHQMIlzbR949rGqcbpxpnGUUdEBEg/y2pCXOmmo2CazjYdvSh80xHRXdP1TU9kk4a571kvuVUMH68utJwviEnFTF9YPCV2+RTk2MVnvdx5pPAqxpIc6P4E5UBtKIx4SEKBPQ32dGJPx1Qip+PnyYIZC6qtUB1s' \
			b'E9zZqK9NLDqw6HEK0l4XXdRrJapLvRm9XOhtcp5I7ix47wBWSCIESMAAwkY0gbp6GjscBdVXPAY7+7Yh+aNnNTbLH0A8FvqAH+ML+kiEfdO1TaeOhkq8grRL3XFUctHqgl5CQ4jQByg8unOLk0I2rlqKEd7PUvEu4uvMd+cPsouAl3VQcTAjyrKnsk0bC+32' \
			b'WKjuUaiTwl1oXNc4Kto1zp9nGxGv6h7xqu8Rr+a+8Hrh8E5RGGgpDK67eHKAdIdXTBfnTEja4fXTC9x71fS66U3TW+6nkbB3w0SMpshnJTaZTRJTZ8NOYG7OgI/uTPjwol4nTL86ZfrZ8qOl65JmYJMJc3MitBvQToTq0UTiis0memL9CngHwMBwG2NZN9g1' \
			b'NOwaGnYNLdUr6XwuFGaVCvY6NpTHqT8/NApMGY20CrOcYRJwjq9m00Vzh7xpj4ImsXDMNJaJOke06aMyybAtAJT5I6OMYBeNW8fUvF17S31Ap5K1Q8PIgT5KGuUc0XvFZhp97maKK7ZCaZif7gGzyp8/lxexw/TdTEd/xXap84WslpHIHqExNdCy0U1HOxnL' \
			b'12Eo5tJYzCGTg1X4wkWbp1PzqfV8tJmN7jCW6oSCasp+xZN7jVk9BmU9+useloDegJweI0VqfHOJSbCZjiYlbuxL7WZi+dbg1sTRtjkZh+QVzwrMqcwKZDpgzsZgwVMWHacUBlMKgykFnUZZJL0KUDEFZKhzHngEv0YKMn1iOanYu5g+zaYM/HkGbjMBdeyn' \
			b'gqQ5CtZ4dCozR7Ql1WRm3lAW0ffJD6HaWUkoPxN9AcR4dMgBOXVIMhPJOrwMnKjAWUvOubPtCHjMII0KzDt5Z/MYwMCWLy3dY1zRYxzRS+8423MQ5/aE3s1M4WRkwtTiZWHxsrBiaIJggsRKF2mPylDAPbC83NAAPci0cp4fRXJ/YDHytMC4jag25dASHUEf' \
			b'B1891KQXaYwGhyQ4B8E5CM6dKWbk5XmuzLFqS/vJkSpyUZFc6vqhOg6q46AcFt2DhW7YOOjyUAcPdaATEfy9gMhjaYpHehfTh9N1BlwxowGMBhER5kCYmAV5Vi/XoXolPW9oEDF1yN3FDN2JC6M/afrDKdPP6tPHtaFtXBzaysutba5aIQG91VAmj/5crmvg' \
			b'Fx0c6Gc6hUjm0Qh3Ib4C0QPOimXKEYaKGHPn7jIkmYiU4pJdXy3Jy4wHGXLQkcVCPLTEQUsstCSvlvhomXFmmlgUHuk5s8gMMocsTl7vzIudeYEzL6/jdU68PInXjfKiUV6/yIsXeZ0gLxLklXjsbGFHCy8P5yXGLGAWLi8F4dcq22XYesGmC15ezQMhXpLM' \
			b'a8RZk3jNAy/d46V67E9jnxcvW2UjP1v4eUkFO9h4YSuvq+A1FV2ghvMsO95d4XlDBu9K4M0SfG1Jm1Yk8xXloyvKueINKaSKpF1eVIz3dATskQmSyPMhKNk/whsXfPxbOd6Hgz0Eq47/HVVKaYjuVe+GdJKWeWopLfHItFH1q8BbExQ/lF1JBlU7PinekNHx' \
			b'Th1KQyIoCuItPx3/E0u9lcJ4MxSVzDVjvxLTy7QFKZx3mTD1vG+Gn3BmScObUrC/auXayBIlJNVbCY0sIJaE4lqYOBL6KsSU1Oi8O4x0kDNj3xBF97wVix71LDrFLDBJlJS3GyWZrAK3Av9Ta/3Tt49WvPTcajrrf/GbknHHiZdxp28fbiXW7LYQm4NXFyF2' \
			b'W/C6LrSW4MT6zfRVeFKAE58ingQGGVB8WwBJ0suxgBKLIoUlOJVpYw7vcOLtbRFURqFiIIrhVOJoXMAITDWScjIVuZlHktBeQSkxNAWTiEsPSIoJl7GkMoQyWRWKFKGItacNj7gLIK2gs/qXjKoe0HRMaLKCJlujyQJNNqPJ1miyNZqsoMnWaLI5LKLJjoOg' \
			b'yU7RZNejaVTAZjQNyVTkZg2a7ARNkaEZNNkaTUi4BZpsRtNA1pZoMg9oOio09YKmeqwnt9h4ndDU12jqazT1gqa+RlMRFtHUj4OgqZ+iqV+PplEBm9E0JFORmzVo6idoigzNoKmv0YSEW6Cpz2gayNoSTXZ7NB1qhtVec5K1CWVLkyx1wInWEuJ4atJzc5SI' \
			b'k1srp4g4mcFkxHHzpVBCTzLKsYBelXgBemXamMM7nAroxbmWVN7hhLpNKqGE4rjAjVDMyeKcS4qdwlHqaMFShcjE5xSRIk6NsgHKJMBFUEpWgLIgcDtQugdQnhwoxd7BxxKUBqA0GZSmBqXJoQKlEVCaGpRl4iVQmnEQUJp5UBqA0gCUeDPGXCUoRwVuBuWQ' \
			b'LIHSzIPSAJRmAsrI5wwoDUBpMigj1cugNBmUmcDtQOkfQHlyoJSZnq5nehozPZ1nerqe6WmbQwVKmfLpespXJV4CpR0HAaWdByWmfXJC3SaVUIFyVOBmUA7JEijnp4FSRwuWalBGPmdAiZmglB1BGQW4DMo8GSwI3A6UYY+gLDwgdwHNsBad1H73BaCdALSr' \
			b'AdoBoF0GaFcDtMuhAmgnAO0EoAwAals+6b7OsgTTbhwEpt0AUy4zobQDSjGjlFMqgFOVQK2L7JYmmLnyhNVuHquYZwpfNVYjszNY7YDVLmM1srCM1S5jNRM4g1VPEOUmn0K2Y8jqJrkWrwnc7pheqG7mnao2uPnuGLr8wZnbgS9jjD8RRm2PSWltBtIwA+ls' \
			b'BtK1GUj3OZRI7vA9OC/H8m1bpl+CcT8OAuN+/m0Ls5CcQKVJJVQgLkpT0MEJimWM2Y7RPNCQ0DxvMpL6WrBXoznyPINmWI2k7F4aVhAdZbqM6Gw8Kojc7u3b3/Dte1QgvjejYiNQNbX9yMB+ZLL9yNT2I6NyqKCqkVeOBVSr9AtQLdPGHN7hNIWqgQnJwIRk' \
			b'YEKK8QVUxwVufNnmZBGeZt6EZGBCMhMTUuJzCk8DE5LJJqTEwyI0TTYhFQRuB03VPkxXTw6Y4uY3tZvfwM1vspvf1G5+Xr+VQglMySjHEpVl4iVU6nEQVOp5VMLnLyfUbVIJFSpHBW5G5ZAsoXJ+DYDU0YKlGpWRzxlUYhmAyd6WJMBlVOaVAAWBW6Jyh4U1' \
			b'x4PK9TPV+wJMsSOZ2o5kYEcy2Y5kajuSsTlUwBQ7kqntSFXiJWDacRBgZjuSlB1xCTOSgRnJwIyU85XQHBW5GZpDsgTNeUuSgSXJTCxJidMZaMKSZLIlKYlwGZrZklQQuNPsVO2wWOcBoceDUC8I9TVCPRCaV5yaeskpG/tSqBAqi05Nveq0SryEUD8OglCf' \
			b'EeozQrH+VE54YIoCKoSOityM0CFZQuj8UlSpowVTNUIjpzMI9UCozwiNIlxGqM8IzQTuhtAdFgA9IPR4EBoEoaFGaABCQ0ZoqBFahAqhQRAaaoSWiZcQGsZBEBoyQkNGaABCAxAagNAhX4nQUZGbETokSwgN8wgNQGiYIDRyOoPQAISGjNBY/DJCQ0ZoJnA3' \
			b'hO5zUdGDV+buoSpeGVN7ZQy8MiZ7ZUztleHWSaGCqnhlDLwy8qyVk+7rLEuA7cZBAJu9MlJDBCy8MnGdn4FXJucrASsx3Az58WbQDskSaOfdMgZuGTNxyyRuZ0ALt4zJbpnEwzJos1umIHA30O5z0dEDaO8etLIO19QOGAMHjMkOGFM7YEyfQwVa8b4YeF8M' \
			b'XKkGrtQqyxJo+3EQ0GYfjMmuVAMXjIELxsAFk/OVoJ2WuhmzQ7KE2Xnni4HzxUycL4nZGczC+WL6jNkoy2XMZsdLQeBumN3nmqQHzN45ZtlNKHIuMSu3+EW4iFm+LDDL7ZJCiVnJKEfCrDxDEt3XWRYwW6aNObzDCZiVGoBZqaXDCQ9MUUCJ2ZlSN2I2J4uY' \
			b'lcKnmJVqIl8VZhOzU8yKZDXKBmaTLBcxK1mB2YLA3TD7sGTptDEr3lNbe08tvKc2e09t7T3lRkmhwqy4Ti1cpxZTWT7pvs6yhFk1DoLZ7ECVGiJm4T+18J9a+E9zvhKz01I3Y3ZIljA770W18KLaiRc1MTuDWXhRbfaiJlkuYzZ7UQsCd8Nst8eFDpPPLewN' \
			b'uYY//3Bt/MYPIwmE+/7MUSw6wg1X7VqDvVhle7Gq7cXMZgrVGghkkvgONilJ0cpJ93XGpa1sfhxkK1u2HSvYjhWroGy3jLV1OCGBKQqqNrlNSu9qX4+SQckY2rmsCG01b01WsCariTU58T6FtoI1WWVrchLw8sa3bE0uCNwN2ntew3RMb+QS0ecNZy0rJ3S9' \
			b'ciJ+b0TnlRO6Xjnh8UujGr8tWsAZKb0cg8Jj2U4saxB1kWtpDaIeB1mDmJdQSA1xCSJWUGisoNBYQZHzlasQJ6Fb3I4zlJPWH84vpdBYSqEnSykSvzPrD7GUQuelFEmiy2sP81KKgsCd8Kv3uc7pmMB7T5BrnQynXT2cdhhOuzycdvVw2uVQDaedDKcdhtP4' \
			b'VWqLH0yusiwNpydBhtMuD6ddHk47DKcdhtMOw+khXzmcnpa6eTg9JEvDaTc/nHYYTrvJcDoyOzOcdhhOuzycjrJcHk67PJzOBO6G2U2roGwF2/JjZg/IvRFyw20MowW9qkavAno9JsMe6wRVBjAn48G048Bk1BiW7HIM8VkrJ93HLAhzGO77PIqeBBlFZwir' \
			b'DGEFCCtAWAHCOV85ep6WqmW2tOYjEUOqNGqeR7ACgtUEwYnVmVEzEKwygvskn20GzhnEBY0zILYEXv5QH7Dc0x3/Ut4MpPe5bOoBzBWY27t6FYvb19ZuXwu3r81uX1u7fbkNUqhexeL2tXD7Wrh9Ldy+VZalV3E3DvIqzm5fm92+Fm5fC7evhds35ytfxdNS' \
			b'N7+Kh2TpVTzv9bXw+tqJ1zcxOwdklGY1yo+v48jG8us4e34LInd7He9zQdUJY1cV+LWnimHxAtvaC2zhBbbZC2xrL7Dtc6gwLF5gCy+whRfYwgtcZVnCcD8OguHsBbbZC2zhBbbwAlt4gXO+EsPTUjdjeEgWIAuVGJ9FMnzBduILTizPDKrxxGpUEoEca1gG' \
			b'cnYHF5TuBmTbXKWNtRWUgeMBxAm4jNq0BnItQH39sbPJl8623/Yq4JoDlZ4B06ZRbQRPBZo5wCSwlACp96vOfZ82YaQESAmKla8WHS4pP6v6+CNk675Att1eUm51Vt51nxwbKey6T8qWnxor9XNGN5NilvqI3727XX2z8knrPWjduiFZqXntltpnowbq2IV7' \
			b'zK02aaNnwziVwbbtSjPpnn9D8Lg0VMkXV90+NXXD5yajtrIst9JYhc/+sHzhK4CMN2hwfnuGSpvTG3Ss1f4OtVpNPhzpr6PbboN+8yeC6RlRulsva9f0tOuGJ0fZ27J4Sl2W+7lvP6oZC/qyTq+Zz8tkXpnhf5ceWZnZXnnNqGFdzxxuWYfXK/Cetfc6Gqu2' \
			b'GB+oY9baWmPDnnpgnnnsY8ww9MB2aezA4l2npTSeVe4RcSoj1+6u9HUfve0eddX2Jz2WXRglqK2/j7LDSGE3HdU3Gd/2B5pP4VeqDjOr4t9w4V/TOlGNXBizKtl07A8zy0Ll7praSBI5jDaqW1RIs4VStvdDMVl3+ttSznnbc6mgPLCXrtKFmyipOrSS2oak' \
			b'3/sHbb1dbTWDtkIs+D+M5pq9aK4+6MveHkxhz15Zs6K6wyjoHpTTHFQ53YNy3r5yHui9vwflPJTbCcp5uFf9PVLOcLLKeds+qtt3UJn7bsS/O2eUfCpZbHJKPHw3N9yzpXlbdW3+SQ3ziCqSnznb0g1lr6O7rq+X19xEfdsde9ZdPfszqipy1eLQ26fKclMY' \
			b'nK6vtNKeUW/D3vQ2Lju7JZf/jHOJf+uX9VTYmVNV7R8RvEVTt3Q2PWjq/jQV/SufbqCp4Uw01UNTw7Kmds3VYZdH3bYR3+3hfc8yPt4haamFt2m053WZN3fEEx1Xh9S3u16Gt5OenYSO3eXSu910i7T/oLp1iGWe6/TLyoCFXwVrdE3fsa5xhTuqGme5DW1z' \
			b'OykbL0pccd1r3qa+fSTbp6yms5afkFUk34cebm5wl1WOjRgPvdv2M+H+EYFUtEs/aNeaPs0e+8vTSThG9XKPeN9qax6teBeQfbTqRNfMg66t0TV39LrmGiHyZHTNNldK9tJZ2TrUcxOxqNnQoUUlZB+zqEYr4z0nG67xs527aWK/vQVlL1aSXdRNLCP8sox6' \
			b'xC1kZF/fNTRImvca9ow9WC22VxMu1PaVZYJaK7XtLg27Xc9yp81ZNWV/7Z5g14HMnTVebDkCtQnScoFmYUBwFHcWB4miBz/KRDpzSQLpbsicm2sQuxmVJQLqR4sYhm3EXV04pb9YyYc2lHzIKP4kW7Enl2Qy2jMrfije25r2smJ/Kn/oQRxdjn/qko7sdk1B' \
			b'lu9TL4bnrA68k4pUNT4W76jsfWKGV3pfFFH+7f6kWrOpWmrpXWomUI7+2Ow8jZU/qV2+h88oXE+Am+Ve9iavo8Py2MJO/nhiXt3b6l4IclsRhG3Zu5JF7+HZvzTAWffcCWV+B8qwYXwn+rARLG+fJnrpVbP2Lw3GNqQYDZWYB/nCq79bLjoebnY3+xPiuwMQ' \
			b'T93fTf+E9v4atLswS363Iws8bNo5hLlYHrMv5BNm8QuPXmL2wPAGppmi9YzzZxN4ooOLm4TZQuYiwb86Dv5Nc+cB/Osx/+XHOSAI+fGrZXHIu4e/rmHydzWmn9OoZaSa4UsZ8lWMUl5Ri/lLF+vlFprDBB5WBbjKymhe5jSfBdI2x6FtXXPnAfzbZW3bQhCl' \
			b'ki0KZaxWSyrFBpoi+D4ecbFl4JkS8qiFhDRwn1ZXB4jOnYDoXHNMAXLzJyA33xxTgNzCCcgtNMcUILfu+OXGRqEjCpBbvwe5bTEE2YP0THPDwObRcZTWNywVhpHJcP5Oh3PXEqdrNgd8g20x2TaBDZQ75oFYJ7OEoxcr22uON0Cqh517XEuqpjniAKlO5hjH' \
			b'L1XbHHGAVLeYuRybVH1zxAFS3WJSc8TWB3a6nECAqH30FLNxvScxITbIr9jw4AOugygu9iBb/i5T5/lYbB1CNv7SjortBImTpDhTiE7EwUXoo8eGv4JieX4hkmQXNWXizTLcEl30r7Tys7FDS1OLsF1X5f34yqE4/kLAKCW3HafWTRmUA355YzYJY/CPs5tM' \
			b'fusGhgneGqu8+KgCZfj+8v8BK8rRHA=='

	_PARSER_TOP  = 'expr'

	_GREEK       = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'

	_SPECIAL     =  r'\\partial|\\pi|\\infty'
	_CHAR        = fr'[a-zA-Z]'
	_PYVAR       = '|'.join (reversed (sorted (AST.Var.PY)))
	_TEXTVAR     =  r'\\text\s*\{\s*(' + _PYVAR + r')\s*\}'
	_ONEVAR      = fr'{_CHAR}|{_GREEK}'
	_DSONEVARSP  = fr'(?:(\d)|({_PYVAR})|({_CHAR}|{_GREEK}|{_SPECIAL})|{_TEXTVAR})'
	_STR         =  r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPYONLY  = '|'.join (reversed (sorted (AST.Func.PY_ONLY)))
	_FUNCPYTEX   = '|'.join (reversed (sorted (AST.Func.PY_AND_TEX)))
	_FUNCTEXONLY = '|'.join (reversed (sorted (AST.Func.TEX_ONLY)))

	TOKENS       = OrderedDict ([ # order matters
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		# ('TRIGH',         r'\\?(?:(a)(?:rc)?)?((?:sin|cos|tan|csc|sec|cot)h?)|\\operatorname\s*\{(sech|csch)\s*\}'),
		('SQRT',          r'\\?sqrt'),
		('LOG',           r'\\?log'),
		# ('FUNC',         fr'({_FUNCPYONLY})|\\?({_FUNCPYTEX})|\$({_CHAR}\w*)|\\operatorname\s*\{{\s*({_CHAR}(?:\w|\\_)*)\s*\}}'),
		('FUNC',         fr'({_FUNCPYONLY})|\\?({_FUNCPYTEX})|\\({_FUNCTEXONLY})|\$({_CHAR}\w*)|\\operatorname\s*\{{\s*({_CHAR}(?:\w|\\_)*)\s*\}}'),
		('LIM',           r'\\lim'),
		('SUM',           r'\\sum'),
		('INT',           r'\\int(?:\s*\\limits)?'),
		('LEFT',          r'\\left'),
		('RIGHT',         r'\\right'),
		('CDOT',          r'\\cdot'),
		('TO',            r'\\to'),
		('BEG_MATRIX',    r'\\begin\s*\{\s*matrix\s*\}'),
		('END_MATRIX',    r'\\end\s*\{\s*matrix\s*\}'),
		('BEG_BMATRIX',   r'\\begin\s*\{\s*bmatrix\s*\}'),
		('END_BMATRIX',   r'\\end\s*\{\s*bmatrix\s*\}'),
		('BEG_VMATRIX',   r'\\begin\s*\{\s*vmatrix\s*\}'),
		('END_VMATRIX',   r'\\end\s*\{\s*vmatrix\s*\}'),
		('BEG_PMATRIX',   r'\\begin\s*\{\s*pmatrix\s*\}'),
		('END_PMATRIX',   r'\\end\s*\{\s*pmatrix\s*\}'),
		('FRAC2',        fr'\\frac\s*{_DSONEVARSP}\s*{_DSONEVARSP}'),
		('FRAC1',        fr'\\frac\s*{_DSONEVARSP}'),
		('FRAC',          r'\\frac'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
		('VAR',          fr"({_PYVAR})|(d|\\partial\s?)?({_ONEVAR})|{_SPECIAL}|{_TEXTVAR}"),
		('STR',          fr"(?<!\d|{_CHAR}|['}}])({_STR})|\\text\s*\{{\s*({_STR})\s*\}}"),
		('SUB1',         fr'_{_DSONEVARSP}'),
		('SUB',           r'_'),
		('CARET1',       fr'\^{_DSONEVARSP}'),
		('CARET',         r'\^'),
		('DBLSTAR',       r'\*\*'),
		('PRIMES',        r"'+"),
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
		('INEQ',          r'==|!=|\\neq?|<=|\\le|<|>=|\\ge|>'),
		('EQ',            r'='),
		('DIVIDE',        r'/'),
		('EXCL',          r'!'),
		('AMP',           r'&'),
		('DBLSLASH',      r'\\\\'),
		('COMMA',         r','),
		('ignore',        r'\\,|\\:|\\?\s+'),
	])

	_FUNC_AST_REMAP = {
		'Abs'       : lambda expr: _expr_func (1, '|', expr),
		'abs'       : lambda expr: _expr_func (1, '|', expr),
		'Derivative': lambda expr: _expr_func_remap (remap_func_diff, expr),
		'exp'       : lambda expr: _expr_func (2, '^', ('@', 'e'), expr),
		'factorial' : lambda expr: _expr_func (1, '!', expr),
		'Integral'  : lambda expr: _expr_func_remap (remap_func_intg, expr),
		'Limit'     : lambda expr: _expr_func_remap (remap_func_lim, expr),
		'ln'        : lambda expr: _expr_func (1, 'log', expr),
		'Sum'       : lambda expr: _expr_func_remap (remap_func_sum, expr),
	}

	def expr_comma_1    (self, expr_comma, COMMA, expr):                     return AST.flatcat (',', expr_comma, expr)
	def expr_comma_2    (self, expr_comma, COMMA):                           return expr_comma if expr_comma.is_comma else AST (',', (expr_comma,))
	def expr_comma_3    (self, expr):                                        return expr

	def expr            (self, expr_eq):                      	             return expr_eq

	def expr_eq_1       (self, expr_ineq1, EQ, expr_ineq2):                  return AST ('=', '=', expr_ineq1, expr_ineq2)
	def expr_eq_2       (self, expr_ineq):                                   return expr_ineq
	def expr_ineq_2     (self, expr_add1, INEQ, expr_add2):                  return AST ('=', AST.Eq.LONG2SHORT.get (INEQ.text, INEQ.text), expr_add1, expr_add2)
	def expr_ineq_3     (self, expr_add):                                    return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_mul_exp):                return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2      (self, expr_add, MINUS, expr_mul_exp):               return AST.flatcat ('+', expr_add, expr_mul_exp.neg (stack = True))
	def expr_add_3      (self, expr_mul_exp):                                return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_neg):                return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_2  (self, expr_mul_exp, STAR, expr_neg):                return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_3  (self, expr_neg):                                    return expr_neg

	def expr_neg_1      (self, MINUS, expr_diff):                            return expr_diff.neg (stack = True)
	def expr_neg_2      (self, expr_diff):                                   return expr_diff

	def expr_diff       (self, expr_div):                                    return _expr_diff (expr_div)

	def expr_div_1      (self, expr_div, DIVIDE, expr_mul_imp):              return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2      (self, expr_div, DIVIDE, MINUS, expr_mul_imp):       return AST ('/', expr_div, expr_mul_imp.neg (stack = True))
	def expr_div_3      (self, expr_mul_imp):                                return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_int):                      return AST.flatcat ('*', expr_mul_imp, expr_int)
	def expr_mul_imp_2  (self, expr_int):                                    return expr_int

	def expr_int_1      (self, INT, expr_sub, expr_super, expr_add):         return _expr_int (expr_add, (expr_sub, expr_super))
	def expr_int_2      (self, INT, expr_add):                               return _expr_int (expr_add)
	def expr_int_3      (self, expr_lim):                                    return expr_lim

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
		func  = f'a{FUNC.grp [2] [3:]}' if FUNC.grp [2] else \
				FUNC.grp [0] or FUNC.grp [1] or FUNC.grp [3] or FUNC.grp [4].replace ('\\_', '_') or FUNC.text
		args  = expr_func_arg.strip_paren ()
		remap = self._FUNC_AST_REMAP.get (func)

		return remap (args) if remap else _expr_func (2, 'func', func, args)

	def expr_func_6     (self, FUNC, expr_super, expr_func_arg):
		ast = self.expr_func_5 (FUNC, expr_func_arg)

		return \
				AST ('^', ast, expr_super) \
				if expr_super != AST.NegOne or not ast.is_trigh_func_noninv else \
				AST ('func', f'a{ast.func}', ast.arg)

	def expr_func_7     (self, expr_fact):                                   return expr_fact

	def expr_func_arg_1 (self, expr_func):                                   return expr_func
	def expr_func_arg_2 (self, MINUS, expr_func):                            return expr_func.neg (stack = True)

	def expr_fact_1     (self, expr_fact, EXCL):                             return AST ('!', expr_fact)
	def expr_fact_2     (self, expr_pow):                                    return expr_pow

	def expr_pow_1      (self, expr_pow, expr_super):                        return AST ('^', expr_pow, expr_super)
	def expr_pow_2      (self, expr_abs):                                    return expr_abs

	def expr_abs_1      (self, LEFT, BAR1, expr, RIGHT, BAR2):               return AST ('|', expr)
	def expr_abs_2      (self, BAR1, expr, BAR2):                            return AST ('|', expr)
	def expr_abs_3      (self, expr_paren):                                  return expr_paren

	def expr_paren_1    (self, PARENL, expr_comma, PARENR):                  return AST ('(', expr_comma)
	def expr_paren_2    (self, LEFT, PARENL, expr_comma, RIGHT, PARENR):     return AST ('(', expr_comma)
	def expr_paren_3    (self, IGNORE_CURLY, CURLYL, expr, CURLYR):          return expr
	def expr_paren_4    (self, expr_frac):                                   return expr_frac

	def expr_frac_1     (self, FRAC, expr_mat1, expr_mat2):                  return AST ('/', expr_mat1, expr_mat2)
	def expr_frac_2     (self, FRAC1, expr_mat):                             return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_mat)
	def expr_frac_3     (self, FRAC2):                                       return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 4))
	def expr_frac_4     (self, expr_mat):                                    return expr_mat

	def expr_mat_1      (self, LEFT, BRACKETL, BEG_MATRIX, expr_mat_rows, END_MATRIX, RIGHT, BRACKETR):  return AST ('mat', expr_mat_rows)
	def expr_mat_2      (self, BEG_MATRIX, expr_mat_rows, END_MATRIX):                                   return AST ('mat', expr_mat_rows)
	def expr_mat_3      (self, BEG_BMATRIX, expr_mat_rows, END_BMATRIX):                                 return AST ('mat', expr_mat_rows)
	def expr_mat_4      (self, BEG_VMATRIX, expr_mat_rows, END_VMATRIX):                                 return AST ('mat', expr_mat_rows)
	def expr_mat_5      (self, BEG_PMATRIX, expr_mat_rows, END_PMATRIX):                                 return AST ('mat', expr_mat_rows)
	def expr_mat_6      (self, expr_curly):                                                              return expr_curly

	def expr_mat_rows_1 (self, expr_mat_rows, DBLSLASH, expr_mat_row):       return expr_mat_rows + (expr_mat_row,)
	def expr_mat_rows_2 (self, expr_mat_rows, DBLSLASH):                     return expr_mat_rows
	def expr_mat_rows_3 (self, expr_mat_row):                                return (expr_mat_row,)
	def expr_mat_row_1  (self, expr_mat_row, AMP, expr):                     return expr_mat_row + (expr,)
	def expr_mat_row_2  (self, expr):                                        return (expr,)

	def expr_curly_1    (self, LEFT, CURLYL, expr_comma, RIGHT, CURLYR):     return _expr_curly (expr_comma)
	def expr_curly_2    (self, CURLYL, expr_comma, CURLYR):                  return _expr_curly (expr_comma)
	def expr_curly_3    (self, expr_bracket):                                return expr_bracket

	def expr_bracket_1  (self, LEFT, BRACKETL, expr_comma, RIGHT, BRACKETR): return AST ('[', expr_comma.commas if expr_comma.is_comma else (expr_comma,))
	def expr_bracket_2  (self, BRACKETL, expr_comma, BRACKETR):              return AST ('[', expr_comma.commas if expr_comma.is_comma else (expr_comma,))
	def expr_bracket_3  (self, expr_term):                                   return expr_term

	def expr_term_1     (self, STR):                                         return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_2     (self, SUB):                                         return AST ('@', '_')
	def expr_term_3     (self, expr_var):                                    return expr_var
	def expr_term_4     (self, expr_num):                                    return expr_num

	def expr_num        (self, NUM):                                         return AST ('#', NUM.text) if NUM.grp [0] or NUM.grp [2] else AST ('#', NUM.grp [1])

	def expr_var_1      (self, var, PRIMES, subvar):                         return AST ('@', f'{var}{subvar}{PRIMES.text}')
	def expr_var_2      (self, var, subvar, PRIMES):                         return AST ('@', f'{var}{subvar}{PRIMES.text}')
	def expr_var_3      (self, var, PRIMES):                                 return AST ('@', f'{var}{PRIMES.text}')
	def expr_var_4      (self, var, subvar):                                 return AST ('@', f'{var}{subvar}')
	def expr_var_5      (self, var):                                         return AST ('@', var)

	def var             (self, VAR):
		return \
				f'\\partial {VAR.grp [2]}' \
				if VAR.grp [1] and VAR.grp [1] != 'd' else \
				AST.Var.SHORT2LONG.get (VAR.grp [0] or VAR.grp [3], VAR.text)

	def subvar_1        (self, SUB, CURLYL, expr_var, CURLYR):               return f'_{expr_var.var}' if expr_var.var and expr_var.is_single_var else f'_{{{expr_var.var}}}'
	def subvar_2        (self, SUB, CURLYL, NUM, CURLYR):                    return f'_{{{NUM.text}}}'
	def subvar_3        (self, SUB, CURLYL, NUM, subvar, CURLYR):            return f'_{{{NUM.text}{subvar}}}'
	def subvar_4        (self, SUB1):                                        return f'_{AST.Var.SHORT2LONG.get (SUB1.grp [1] or SUB1.grp [3], SUB1.text [1:])}'

	def expr_sub_1      (self, SUB, expr_frac):                              return expr_frac
	def expr_sub_2      (self, SUB1):                                        return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1    (self, DBLSTAR, expr_func):                          return expr_func
	def expr_super_2    (self, DBLSTAR, MINUS, expr_func):                   return expr_func.neg (stack = True)
	def expr_super_3    (self, CARET, expr_frac):                            return expr_frac
	def expr_super_4    (self, CARET1):                                      return _ast_from_tok_digit_or_var (CARET1)

	def caret_or_dblstar_1 (self, DBLSTAR):                                  return '**'
	def caret_or_dblstar_2 (self, CARET):                                    return '^'

	#...............................................................................................
	_AUTOCOMPLETE_SUBSTITUTE = { # autocomplete means autocomplete AST tree so it can be rendered, not expression
		'CARET1'             : 'CARET',
		'SUB1'               : 'SUB',
		'FRAC2'              : 'FRAC',
		'FRAC1'              : 'FRAC',
		'expr_sub'           : 'SUB',
		'expr_super'         : 'CARET',
		'caret_or_doublestar': 'CARET',
	}

	_AUTOCOMPLETE_CLOSE = {
		'RIGHT'   : '\\right',
		'PARENR'  : ')',
		'CURLYR'  : '}',
		'BRACKETR': ']',
		'BAR'     : '|',
	}

	def _mark_error (self):
		self.autocompleting = False

		if self.erridx is None:
			self.erridx = self.tokens [self.tokidx - 1].pos

	def _insert_symbol (self, sym):
		if sym in self.TOKENS:
			self.tokens.insert (self.tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

			if self.autocompleting and sym in self._AUTOCOMPLETE_CLOSE:
				self.autocomplete.append (self._AUTOCOMPLETE_CLOSE [sym])
			else:
				self.autocompleting = False

		else:
			self.tokens.insert (self.tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, ('', '', '', '')))
			self._mark_error ()

		return True

	def _parse_autocomplete_expr_comma (self, rule):
		idx = -1 -len (rule [1])

		if self.stack [idx] [1] == 'CURLYL':
			return self._insert_symbol ('CURLYR')

		if self.stack [idx] [1] != 'PARENL':
			return False

		if self.stack [idx - 1] [1] == 'LEFT':
			return self._insert_symbol ('RIGHT')

		return self._insert_symbol ('PARENR')

	def _parse_autocomplete_expr_int (self):
		s               = self.stack [-1]
		self.stack [-1] = (s [0], s [1], AST ('*', (s [2], AST.VarNull)))
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

		expr_vars  = expr_vars - {'_', 'e', 'i'} - set (AST.Var.LONG2SHORT)
		expr_vars -= set (var [1:] for var in expr_diffs)

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

		if pos >= len (rule [1]): # special error raised by rule reduction function or end of comma expression
			if rule [0] == 'expr_comma':
				return self._parse_autocomplete_expr_comma (rule)

			if rule [0] == 'expr_int':
				return self._parse_autocomplete_expr_int ()

			return False

		return self._insert_symbol (rule [1] [pos])

	def parse_success (self, reduct):
		self.parse_results.append ((reduct, self.erridx, self.autocomplete))

		return True # continue parsing if conflict branches remain to find best resolution

	def parse (self, text):
		self.parse_results  = [] # [(reduct, erridx, autocomplete), ...]
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
	a = p.parse ('{')
	print (a)
