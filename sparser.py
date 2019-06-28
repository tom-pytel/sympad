# TODO: redo _expr_diff d or \partial handling

# Builds expression tree from text, nodes are nested AST tuples.
#
# ) When parsing, explicit and implicit multiplication have different precedence, as well as latex
#   \frac and regular '/' division operators.
#
# ) Explicit multiplication and addition have higher precedence than integration, so they are included in the expression to be integrated,
#   but lower precedence than limits or sums, so they end those expressions.
#
# ) Differentiation and partially integration are dynamically extracted from the tree being built so they have
#   no specific complete grammar rules.
#
# ) Future: vectors and matrices, assumptions, stateful variables, piecewise expressions

from collections import OrderedDict
import os
import re

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT

def _ast_from_tok_digit_or_var (tok, i = 0):
	return AST ('#', tok.grp [i]) if tok.grp [i] else AST ('@', AST.VARS_SPECIAL_SHORT.get (tok.grp [i + 1], tok.grp [i + 2]))

def _expr_int (ast, from_to = ()): # find differential for integration if present in ast and return integral ast
	if ast.is_diff_var or ast.is_null_var: # null_var is for autocomplete
		return AST ('intg', None, ast, *from_to)

	elif ast.is_div:
		if ast.denom.is_mul and ast.denom.muls [-1].is_diff_var:
			return AST ('intg', ('/', ast.numer, ast.denom.muls [0] if len (ast.denom.muls) == 2 else \
					AST ('*', ast.denom.muls [:-1])), ast.denom.muls [-1], *from_to)

		if ast.numer.is_diff_var:
			return AST ('intg', ('/', ast.One, ast.denom), ast.numer, *from_to)

	elif ast.is_mul and (ast.muls [-1].is_diff_var or ast.muls [-1].is_null_var): # null_var is for autocomplete
		return AST ('intg', ast.muls [0] if len (ast.muls) == 2 else AST ('*', ast.muls [:-1]), ast.muls [-1], *from_to)

	elif ast.is_add:
		if ast.adds [-1].is_diff_var:
			return AST ('intg', \
					AST ('+', ast.adds [:-1])
					if len (ast.adds) > 2 else \
					ast.adds [0] \
					, ast.adds [-1], *from_to)

		if ast.adds [-1].is_mul and ast.adds [-1].muls [-1].is_diff_var:
			return AST ('intg', \
					AST ('+', ast.adds [:-1] + (AST ('*', ast.adds [-1].muls [:-1]),))
					if len (ast.adds [-1].muls) > 2 else \
					AST ('+', ast.adds [:-1] + (ast.adds [-1].muls [0],)) \
					, ast.adds [-1].muls [-1], *from_to)

	elif ast.is_intg and ast.intg is not None:
		return AST ('intg', _expr_int (ast.intg, () if ast.from_ is None else (ast.from_, ast.to)), ast.var, *from_to)

	raise SyntaxError ('integration expecting a differential')

_rec_var_d_or_partial = re.compile (r'^(?:d|\\partial)$')

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast.numer.is_var and _rec_var_d_or_partial.match (ast.numer.var):
			p = 1
			v = ast.numer.var

		elif ast.numer.is_pow and ast.numer.base.is_var and _rec_var_d_or_partial.match (ast.numer.base.var) and ast.numer.exp.is_pos_int:
			p = int (ast.numer.exp.num)
			v = ast.numer.base.var

		else:
			return None

		ast_dv_check = (lambda n: n.is_diff_var) if v [0] == 'd' else (lambda n: n.is_part_var)

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
						tail.insert (0, AST ('diff', ast.muls [i + 1] if i == end - 2 else AST ('*', ast [i + 1 : end]), diff.vars))

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
			return AST ('^', AST (*(args [:iparm] + (args [iparm].base.paren,) + args [iparm + 1:])), args [iparm].exp)

	return AST (*args)

#...............................................................................................
class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJztnWlv3DgShv/MArEBNiDeUr7l8MwGm2PGSQZYGEGQcxFgciCZzC4wmP++VfWSoqhWy+qk3W4HRss6KLJYRT4q8er20dmNB/cePn18Q9249/AJ7e/fe0D7x09l/+upBD36mfZPTu/9/E86/vT04R0OPPmJ792+dUr7X26dnjy8zzJ+fvjo9OT5naen9//N' \
			b'cU9v3UkHnY6GjnKboz+UbH4TGf948+F1vsfXdx49eHAry+aA25T6XydP+JRV4dzvPnp6+/7J4yci4A5F5MBf7os5d+/9du/uCYfffcTBKdbjp7ex1zmJaHbrzpNHp/du3S/58Okvp/cenLCwJ49od/Lr01v3+erVi89v/nj+8fPz1x+/vvz9zZc/Xnym0C9f' \
			b'X/4pJ2/+9+nz8y9fP73pL95+/fDq+Yc3/8nXrz6+f/+ixHxJp4OkH76+z6d/vPncn7/9/OJVPv9EGnzIFy9efunDP/63j/7i1R/D/Et2vcRBnr+/60PffejTvf/6+/N37z/ly9fv/iynb9/2+hbDOAGd9Jq9fp1ObzxTZ0crE5Rxxwonnk+0Whk5enXUqk5R' \
			b'gLGqO85hEtJfrnSQ1PJHMlb2uFw35ZJO+GiwM3RHH6cQOqMTEiWSgvyZqFbxuLpuSgidcO4WO4s86GylxRQd1ZFmuS3/HfdBdnjZR+UwPiPVHJmehMmVdWK9qYL92pWuQsLaVS02Dq9IaykFVs2ks6NGLviqJa1TBixkGJbOVx0fO3VklG2UVEijbGC9NdWU' \
			b'O954W2o8LInVVJFWWurLyp9p84103ZXrlZRwlL8Vyl1O6OjESH+M8xW46xRY0lTllL9wAkg4pFU5zA6DtYa+pGIOo0qVM4cdFd1xuiZgpYy1OrKNxEuXVkzSHD4sgZiLkUs/SdF9TZF8Dk9VlS6bOsCXXAgnPFdcgV5MyTozp01/JjVK2VMa0oFjoqByEF1T' \
			b'8HEdaxwjX9Ol5O7F5GRYyrcE6jAZxlclHIVE4ski8h1nlK2Kil2E7ZRrlNPKOeUoCVlm6QFjKc4oR2VKYFl+nMgc4ooK1rbKe+WDSjXqyPswjvSgE1OmE5Wi8lp5kqC8CspF5VrlOuVJhZbrhXShygu0GRWsCk4FihhUiCpQzKCifcakkeJnVLOsf5Q9pWYT' \
			b'yJfxlcXBNSmUrKDrA7OCSleU9LCGtTsWnyYHl1TXHrHk7uXqa1OxQ1Erl94q764ENNYl9VGglL8cYirnILXBj5K+Ik9BSPXQysHDLB9gpcFNI5VEj7/VF6/RGbtLydWXXAHIPvJGhZo4yJtEU310KjR70aDdb2HDybFEeAp4Qi8gD0wnVLwBFagel50lqulq' \
			b'wJ4MiFftKXWoJZ/eWVoYOS+R0Sl2tyi2yD4KyT8H1HKAQwh4LALgCMi+U7FRUatoWEPEiCk5FcHxYZfpGb3tD19HUo+UPEzdqNwOVDduqhlB3/KR20Gs6QHoZaCXlWPlXs+4LWTWmqJeHqht8vCliWLQRDFoopjcRJEiQatWOkp48XOoSfoZUeVq+EabG/Ji' \
			b'ycXnZxJbRopsTy9qbpgg17jHXAm/1Bxo91K2lF+3Le4B7y3TAmvQ7jVKy10ZjM+4QWWuVqvEp0KOQ49yxo2Vq1PqWkr9PEt1B1ODAMXNITNqAJ1xU8mgjZQcLdpsEXxGDX8bTW4g2YkhhnYilC8tLm16p9mD6Muf8XvVHsJ7VV6opMkVII5f6Ca9ni1ezxav' \
			b'ZzqMksC/6VTtzRV6qrzfZI4BvRatEINCMHgafETReHkm91AV8lQfORSww8OXG0bQzEEzh0dQI0pwOHgkDBATGxzEsgnT5XFxB/LkUu5ura1Jmjgg6YCkkxZig8qRm9I0dPtr9niUeCq4FodODqFD8UfoF+U5GflkssjDIg+L/FV6hK6KssyEl1ryqCWP6nF4' \
			b'KhxqxyWvF1AhARVCB+LomfAVENGniPEwO5dnrH2E9lEeEDRA8V73onc9cEZKtjC6RbI2xWwP2MLuYHWLh6obV2mXZgWaNC3QiGdt1BkJoKeZpeOJRkO/157HXQc5FV2zouxxzdiw4hbEeBQKa9/xeDnM7gevk/a16uwwjYpORQKXdKN3VafaRrVatUa1VrWE' \
			b'KYHbqrZTnVGdVZ1THRnKxpENDRnRkBUNmdGQHQ2HkyVcNWwdly6PQPL4Io9I8pwCTyjwKD8P8XMFcBeeu+88KcQzQjy7wjMS3BDmVjBPcvFb0zEAjk3mCWcKXTmeueT5cjpyAagVlRDtAy8taNWK7Y9lW/FENE/uS1WvAu98k6bS6UhVuwo8d82LCVgcPisq' \
			b'2JYPRvL2TqZpObNGJoFFsuTUUcLAgTxjS+dEVRLB88WB7/ISBtKO57xJANvBk8Oiu+fstQjWMsu64gUPLJ1qkJdCuIjlC4GVZ9OlMCQCa90hK142wNpyREoXeYkES9WYuZZlFz7rRZCseE7fxmfqLxdvrrgCmpaO5m9u8iiZ0HWz5H4nrUNUmdNtCXUC6faE' \
			b'bkPnHJFaeOT9AEm5tHLgScOmYnLIodyS/QyJXOZ5YxrlwPIsVgw0PYsM4hjBknSWwhItaIhcRKHEND2CScQ0hBLXD3Kq8CPqCKjW3uTngeqJju5vebdeQ3guhEYgNDWEBhAaQGg2Q2gEQjMPoSmbQGhqCM08hH3SeQj7aEFD5DIITQ0hRGyAEA6w5LQIQnsN' \
			b'4fkQBoEw1BAGQBgAYdgMYRAIwzyEoWwCYaghDPMQ9knnIeyjBQ2RyyAMNYQQsQHCAAj7nBZB6JZAeFENyfjdbUm3uTkZdt+inCW1FVLbmtQWpLYgta1I5VLNW0VtK9S289QOEzvIztSm5qTk2kA6Ipic6RrFvah5ivtoqWEpWdQky91pmFuBWSIknpPt0zy3' \
			b'4LnkuYRnf83zjnjuhOe6WySXVg7Mc1fz3JWt4rkTnrt5noeJHWSPee7AM9bJyiFnusZzL2qe5z5a5rlb57nbyHMHnrvCc7J9mucOPJc8l/AcrnneDc9G+lSm7lMZ9KkM+lSm7lNxeeZtyLNEk/0Mz1ViB9kjng36WAaNCznkTMc8F1GzPJdoiWez3ueSu5M8' \
			b'G3S7JAJ4zrZP8mzQ8xrkuYTneM3zjnjWwrOuedbgWYNnXfOsy1bxrIVnPc/zMLGD7DHPGjzjWyQmffMDKcY896Lmee6jZZ71Os96I88aPOvCc7J9mmcNnkueS3hur3neEc9eePY1zxiF5YOVYfaKZ1+2imcvPPt5noeJHWSPefbg2YNnD56RYsxzL2qe5z5a' \
			b'5tmv8+w38uzBsy88J9unefbgueS5hOcuTyx8C9F+X1A3++Ha7YptLnXBux7IMBjIMBjIMPVAhhlsQ7ypCCSm7OcIH6Z3ED8mHGMbBl8elEOfYkw4vsTXIPY85b2MTPn6eIfcnaYcQx4SoZXyFtJTMUyTjpGPQb5LSNfNt7vuvYF+Zby3jH6YevTDYPTDYPTD' \
			b'1KMfPFWatwpviJEIs3gP0zuIH+ONARCDARCDAZCUYox3L2oe7T5aRnt9AMRsHAAxGAAxZQAkmz+NNQZABnkuwnrRBNt1i2QB0zICYuoREIMREIMREFOPgJiubFWLREZAzPwISJXYQfYYaIyAGIyAGIyApBRjoHtR80D30TLQ6yMgZuMIiMEIiCkjINn2aaAx' \
			b'AjLIcxHQiybrdgl0ex7Ta+s1rhLWVjqOtu44WnQcLTqOtu44Wl22IdYSTfYzWFeJHWQnrCUlyLboO1r0HS36jiXdCO5yYxbuEi3Bbde7j3Zj99Gi+2hL9zGXwCTcFt3HQZ6L4F40CXgN92K4pZnN+yHcFnBbwG1ruG3ZKritwG3n4R4mdpCd4S5uWzJukAHi' \
			b'mEG+a3D3N+bh7qNluO063HYj3BZw2wJ3KoFpuC3gLnkugnvvk4s/ONxO4HY13A5wY6WarZeqISSFD+GWtWp2frFaldilQ4LbFbixak0ySPkM8l2Du78xD3cfLcO9voRN7k7D7QC3K3AnzabhdoC75LkI7h3MNFKN4KU3ucj0HMqb9CMGW7NuB7jHwyZeizvX' \
			b'tTvXcOca7lzX7lzbslWTkOLOaR+xJEluaxwmZiOHUhwySehr+PU2qg6/E6Th3TW8u4Z3L6nHM5NDyYNnQDdhaoKyj5onKNedvN7o5DWcvC5OPpfL9AQlnPwgz0XPwY5mKL/tIfhO/HfFfrgojx/F48fa40d4/AiPH2uPH8tWefwoHj8K/HJP4zDh94ciHHLI' \
			b'fj8Wvx/h9yP8PhYsl3Rjvz+UOe/6+2jZ9cd11795wRR/oyrC/ZdFzLk4pt1/hPsv+S7CfkcTmYeGfczkN5cPv4wp2npM0WJM0WJM0dZjilxweavglwFFiwFFuadxmIB/KMIhhwx/W+DHyKLFyKLFyGJJN4Z/KHMe/j6aR34hp157BDaOMub40DI/AalMpp8A' \
			b'DDQOMl/0BLTqbPQNFD21bjVOt+GZ6n6J6tT61Dlc229ajbqRRD8iD5M1U98HWY0a2EPKVvPzMUzTcGHp3KrS87/cwWRs8aWO4SrSDRQwAsOaP5Zvqe+miuWrUDuuaLOhspuBC4ryQpiueAaC7vPPY2UI+HtW/B2r/cLQcr3ri2dCyyrlCS50WfGTi2eCkeK0' \
			b'Xc9LdtwjbsjgfXCjt0On685xE80huoq2W0RHe95I/xwg7bzfGPCx3HeQabthYHcALKt9f2gELKl+NutiXhqp8rVU/FYAmEttH+jrJgKPFyz/wtO3NxMo4oU/6ls5+vaK+vqLbQZgPZO/AFfvZuu/WYxAGKwn2JaCsNNeQUwIuO/CgE9JDB+WgxDqOf/vZMHv' \
			b'uqvA36lnDoJZQ0H9ZbiXGP/GD/FcMzHJBMal+bAFE/bAmbBgws4zEX6YEYPRb0vU41bdBb4mWPi+Bw9sd95LQed/4jBR/+s/AUE5nv0QFKx5gVLtXF2H2CC82Mag+ouHB1HJ7Q9ayU5f1LP9LbXMUwR677VMLr2jcr9JjLXNzVUrFd79qBVuDqrCZTuECiel' \
			b'+Zdq8IMMpKWVKZAok3BcbG1ao0AnMYrdvNxAegykrSRdT9RxW4/qWKLTjVaiG4rulrUaw9LG4vLW4bnEOPb9WOwsbTu3BIJQ1tBs5da3bL3N13RwVQuNeJSCPq+UF5XvLgo3F2xY/GhtW5y7KkouR3OTql/K0fEPQpDy3gu/1BlKoEvR1AZSieEXmXzSqMjE' \
			b'b7+d9Q9JSt67tG6trPDk1BbmqfFuTXbcLJvd93LZUhMD2fI/3+SbCBrfRJLfzOtno9suzw/zIh8e+KGEtOdRu1bJb1gZDNJgioaVXck6cL1Joq+FGn6ZmOrD3l/ORJodS8OU+5xMq/IHbyBbf0SsmxaLmfyNwtPESj8TzuSo4QcvOz/6jN9Vx/L/7UgBtxMV' \
			b'Ar+Ww7KP5B12lzf5kqUfyTrOZ+1cnbs7VwFyYOsf259yc2J0U/RooUe7WBM7UIabKBsV6qhNRU2QbuOnv1nHErW6C1OL/cQuN1EX380r+lbraKA7FkrXFjj8MmeUFTH9cpjBEphiVsyLXEJZwSKrVzba6dTFbuzMHfyuw9T1dEwUkL64CvVqpxv0NedW6Jru' \
			b'VT1O2dEtqreohhs3W/I2utVv1GxBhM5viMMWxEkRsNZelrXcctvfBmPdpRlr1R43GOsvzVin9rjB2HBpxka1xw3Gxi2NnX/ZbG0y97O22aj7Ogrp4nYSbAPD24t+1y4tAaPmN6xhPTfacOOu5rKoKIvuUMrCq8vb0Ns6vCYYd1Uvf0Pp5AEsHrOitgJa2bzk' \
			b'RctPEwS+4TUvUerSPSu/EdmXIcqHDOaILo+l+DRgog0awjK13vALiP8fogw0calGLkAqHMTB6EI/hhYDevEmqRr4t3yjfJuGe+bH/wfrivs/' 

	_PARSER_TOP = 'expr'

	_GREEK      = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\pi|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'

	_SPECIAL    = r'\\partial|\\infty'
	_CHAR       = fr'[a-zA-Z]'
	_SHORT      =  r'pi|oo'
	_ONEVAR     = fr'{_CHAR}|{_GREEK}'
	_ONEVARSP   = fr'{_CHAR}|{_GREEK}|{_SPECIAL}'
	_DSONEVARSP = fr'(\d)|({_SHORT})|({_ONEVARSP})'

	_FUNCPYONLY = '|'.join (reversed (sorted ('\\?' if s == '?' else s for s in AST.FUNCS_PY_ONLY))) # special cased function name '?' for regex
	_FUNCPYTEX  = '|'.join (reversed (sorted (AST.FUNCS_PY_AND_TEX)))

	TOKENS      = OrderedDict ([ # order matters
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('TRIGH',         r'\\?(?:(a)(?:rc)?)?((?:sin|cos|tan|csc|sec|cot)h?)|\\operatorname\{(sech|csch)\}'),
		('FUNC',         fr'({_FUNCPYONLY})|\\?({_FUNCPYTEX})|\\operatorname\{{({_CHAR}\w+)\}}|\$({_CHAR}\w+)'),
		('SQRT',          r'\\?sqrt'),
		('LOG',           r'\\?log'),
		('LIM',           r'\\lim'),
		('SUM',           r'\\sum'),
		('INT',           r'\\int(?:\s*\\limits)?'),
		('LEFT',          r'\\left'),
		('RIGHT',         r'\\right'),
		('CDOT',          r'\\cdot'),
		('TO',            r'\\to'),
		('FRAC2',        fr'\\frac\s*(?:{_DSONEVARSP})\s*(?:{_DSONEVARSP})'),
		('FRAC1',        fr'\\frac\s*(?:{_DSONEVARSP})'),
		('FRAC',          r'\\frac'),
		('VAR',          fr'\b_|({_SHORT})|(d|\\partial\s?)?({_ONEVAR})|{_SPECIAL}'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
		('SUB1',         fr'_(?:{_DSONEVARSP})'),
		('SUB',           r'_'),
		('CARET1',       fr'\^(?:{_DSONEVARSP})'),
		('CARET',         r'\^'),
		('DOUBLESTAR',    r'\*\*'),
		('PRIMES',        r"'+"),
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('CURLYL',        r'\{'),
		('CURLYR',        r'\}'),
		('BRACKETL',      r'\['),
		('BRACKETR',      r'\]'),
		('BAR',           r'\|'),
		('PLUS',          r'\+'),
		('MINUS',         r'\-'),
		('STAR',          r'\*'),
		('EQUALS',        r'='),
		('DIVIDE',        r'/'),
		('FACTORIAL',     r'!'),
		('COMMA',         r','),
		('ignore',        r'\\,|\\?\s+'),
	])

	_FUNC_AST_REMAP = {
		'abs'      : lambda expr: _expr_func (1, '|', expr.strip_paren ()),
		'exp'      : lambda expr: _expr_func (2, '^', ('@', 'e'), expr.strip_paren ()),
		'factorial': lambda expr: _expr_func (1, '!', expr.strip_paren ()),
		'ln'       : lambda expr: _expr_func (1, 'log', expr.strip_paren ()),
	}

	def expr_comma_1    (self, expr_comma, COMMA, expr):                     return AST.flatcat (',', expr_comma, expr)
	def expr_comma_2    (self, expr):                                        return expr

	def expr            (self, expr_add):                      	             return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_mul_exp):                return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2      (self, expr_add, MINUS, expr_mul_exp):               return AST.flatcat ('+', expr_add, expr_mul_exp.neg (True))
	def expr_add_3      (self, expr_mul_exp):                                return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_neg):                return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_2  (self, expr_mul_exp, STAR, expr_neg):                return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_3  (self, expr_neg):                                    return expr_neg

	def expr_neg_1      (self, MINUS, expr_diff):                            return expr_diff.neg (True)
	def expr_neg_2      (self, expr_diff):                                   return expr_diff

	def expr_diff       (self, expr_div):                                    return _expr_diff (expr_div)

	def expr_div_1      (self, expr_div, DIVIDE, expr_mul_imp):              return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2      (self, expr_div, DIVIDE, MINUS, expr_mul_imp):       return AST ('/', expr_div, expr_mul_imp.neg (True))
	def expr_div_3      (self, expr_mul_imp):                                return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_int):                      return AST.flatcat ('*', expr_mul_imp, expr_int)
	def expr_mul_imp_2  (self, expr_int):                                    return expr_int

	def expr_int_1      (self, INT, expr_sub, expr_super, expr_add):         return _expr_int (expr_add, (expr_sub, expr_super))
	def expr_int_2      (self, INT, expr_add):                               return _expr_int (expr_add)
	def expr_int_3      (self, expr_lim):                                    return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                              return AST ('lim', expr_neg, expr_var, expr)
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_doublestar, PLUS, CURLYR, expr_neg):   return AST ('lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_doublestar, MINUS, CURLYR, expr_neg):  return AST ('lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6      (self, expr_sum):                                                                            return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, expr_super, expr_neg):              return AST ('sum', expr_neg, expr_var, expr, expr_super)
	def expr_sum_2      (self, expr_func):                                                                           return expr_func

	def expr_func_1     (self, SQRT, expr_func_neg):                            return _expr_func (1, 'sqrt', expr_func_neg)
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_func_neg):  return _expr_func (1, 'sqrt', expr_func_neg, expr)
	def expr_func_3     (self, LOG, expr_func_neg):                             return _expr_func (1, 'log', expr_func_neg)
	def expr_func_4     (self, LOG, expr_sub, expr_func_neg):                   return _expr_func (1, 'log', expr_func_neg, expr_sub)
	def expr_func_5     (self, TRIGH, expr_func_neg):                           return _expr_func (2, 'func', f'{"a" if TRIGH.grp [0] else ""}{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func_neg)
	def expr_func_6     (self, TRIGH, expr_super, expr_func_neg):
		return \
				AST ('^', _expr_func (2, 'func', f'{TRIGH.grp [0] or ""}{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func_neg), expr_super) \
				if expr_super != AST.NegOne else \
				_expr_func (2, 'func', TRIGH.grp [1] or TRIGH.grp [2], expr_func_neg) \
				if TRIGH.grp [0] else \
				_expr_func (2, 'func', f'a{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func_neg)

	def expr_func_7     (self, FUNC, expr_func_neg):
		name = FUNC.grp [0] or FUNC.grp [1] or FUNC.grp [2] or FUNC.grp [3] or FUNC.text
		func = self._FUNC_AST_REMAP.get (name)

		return func (expr_func_neg) if func else _expr_func (2, 'func', name, expr_func_neg)

	def expr_func_8     (self, expr_fact):                                   return expr_fact

	def expr_func_neg_1 (self, expr_func):                                   return expr_func
	def expr_func_neg_2 (self, MINUS, expr_func):                            return expr_func.neg (True)

	def expr_fact_1     (self, expr_fact, FACTORIAL):                        return AST ('!', expr_fact)
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

	def expr_frac_1     (self, FRAC, expr_term1, expr_term2):                return AST ('/', expr_term1, expr_term2)
	def expr_frac_2     (self, FRAC1, expr_term):                            return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_term)
	def expr_frac_3     (self, FRAC2):                                       return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4     (self, expr_term):                                   return expr_term

	def expr_term_1     (self, CURLYL, expr_comma, CURLYR):                  return expr_comma
	def expr_term_2     (self, expr_var):                                    return expr_var
	def expr_term_3     (self, expr_num):                                    return expr_num

	def expr_num        (self, NUM):                                         return AST ('#', NUM.text) if NUM.grp [0] or NUM.grp [2] else AST ('#', NUM.grp [1])

	def expr_var_1      (self, var, PRIMES, subvar):                         return AST ('@', f'{var}{subvar}{PRIMES.text}')
	def expr_var_2      (self, var, subvar, PRIMES):                         return AST ('@', f'{var}{subvar}{PRIMES.text}')
	def expr_var_3      (self, var, PRIMES):                                 return AST ('@', f'{var}{PRIMES.text}')
	def expr_var_4      (self, var, subvar):                                 return AST ('@', f'{var}{subvar}')
	def expr_var_5      (self, var):                                         return AST ('@', var)

	def var             (self, VAR):                                         return f'\\partial {VAR.grp [2]}' if VAR.grp [1] and VAR.grp [1] [0] == '\\' else AST.VARS_SPECIAL_SHORT.get (VAR.grp [0], VAR.text)
	def subvar_1        (self, SUB, CURLYL, expr_var, CURLYR):               return f'_{{{expr_var [1]}}}'
	def subvar_2        (self, SUB, CURLYL, NUM, CURLYR):                    return f'_{{{NUM.text}}}'
	def subvar_3        (self, SUB, CURLYL, NUM, subvar, CURLYR):            return f'_{{{NUM.text}{subvar}}}'
	def subvar_4        (self, SUB1):                                        return f'_{AST.VARS_SPECIAL_SHORT.get (SUB1.grp [1], SUB1.text [1:])}'

	def expr_sub_1      (self, SUB, expr_frac):                              return expr_frac
	def expr_sub_2      (self, SUB1):                                        return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1    (self, DOUBLESTAR, expr_func):                       return expr_func
	def expr_super_2    (self, DOUBLESTAR, MINUS, expr_func):                return expr_func.neg (True)
	def expr_super_3    (self, CARET, expr_frac):                            return expr_frac
	def expr_super_4    (self, CARET1):                                      return _ast_from_tok_digit_or_var (CARET1)

	def caret_or_doublestar_1 (self, DOUBLESTAR):                            return '**'
	def caret_or_doublestar_2 (self, CARET):                                 return '^'

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
			self.tokens.insert (self.tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, (None, None, '')))
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
		self.stack [-1] = (s [0], s [1], AST ('*', (s [2], ('@', ''))))
		expr_vars       = set ()
		expr_diffs      = set ()

		if self.autocompleting:
			stack = [s [2]]

			while stack:
				ast = stack.pop ()

				if ast.is_var:
					(expr_diffs if ast.is_diff_var else expr_vars).add (ast.var)
				else:
					stack.extend (filter (lambda a: isinstance (a, tuple), ast))

		expr_vars -= {'_', 'e', 'i', '\\pi', '\\infty'}
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

		# sym = rule [1] [pos]

		# if sym in self.TOKENS:
		# 	self.tokens.insert (self.tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

		# 	if self.autocompleting and sym in self._AUTOCOMPLETE_CLOSE:
		# 		self.autocomplete.append (self._AUTOCOMPLETE_CLOSE [sym])
		# 	else:
		# 		self.autocompleting = False

		# else:
		# 	self.tokens.insert (self.tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, (None, None, '')))
		# 	self._mark_error ()

		# return True

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

# DEBUG!
if __name__ == '__main__':
	p = Parser ()
	a = p.parse ('\\left(1,2')
	print (a)

# 	print (p.parse ('1') [0])
# 	print (p.parse ('x') [0])
# 	print (p.parse ('x!') [0])
# 	print (p.parse ('|x|') [0])
# 	print (p.parse ('x/y') [0])
# 	print (p.parse ('x/(y/z)') [0])
# 	print (p.parse ('sin x') [0])
# 	print (p.parse ('sin x**2') [0])
# 	print (p.parse ('sin (x**2)') [0])
# 	print (p.parse ('sin (x)**2') [0])
# 	print (p.parse ('x') [0])
# 	print (p.parse ('-x') [0])
# 	print (p.parse ('-{-x}') [0])
# 	print (p.parse ('\\int dx') [0])
# 	print (p.parse ('\\int dx/2') [0])
# 	print (p.parse ('\\int 2 dx') [0])
# 	print (p.parse ('\\int 3 / 2 dx') [0])
# 	print (p.parse ('\\int x + y dx') [0])
# 	print (p.parse ('\\int_0^1 dx') [0])
# 	print (p.parse ('\\int_0^1 dx/2') [0])
# 	print (p.parse ('\\int_0^1 2 dx') [0])
# 	print (p.parse ('\\int_0^1 3 / 2 dx') [0])
# 	print (p.parse ('\\int_0^1 x + y dx') [0])
# 	print (p.parse ('dx') [0])
# 	print (p.parse ('d / dx x') [0])
# 	print (p.parse ('d**2 / dx**2 x') [0])
# 	print (p.parse ('d**2 / dx dy x') [0])
# 	print (p.parse ('\\frac{d}{dx} x') [0])
# 	print (p.parse ('\\frac{d**2}{dx**2} x') [0])
# 	print (p.parse ('\\frac{d**2}{dxdy} x') [0])
