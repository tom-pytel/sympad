# Builds expression tree from text, nodes are nested tuples of the form:
#
# ('#', int)                   - integer
# ('#', float, 'float')        - floating point number with original 'string' for arbitrary precision
# ('@', 'var')                 - variable name, can take forms: 'x', "x'", 'dx', '\partial x', 'x_2', '\partial x_{y_2}', "d\alpha_{x_{\beta''}'}'''"
# ('/', numer, denom)          - fraction numer(ator) / denom(inator)
# ('(', expr)                  - explicit parentheses
# ('|', expr)                  - absolute value
# ('^', base, exp)             - power base ^ exp(onent)
# ('!', expr)                  - factorial
# ('sympy', 'func', expr)      - SymPy (or regular py) function 'func' which takes a SymPy expression
# ('trigh', 'func', expr)      - trigonometric or hyperbolic function or inverse: 'sin', 'asin', 'acsch'
# ('log', expr)                - natural logarithm of expr
# ('log', expr, base)          - logarithm of expr in base
# ('sqrt', expr)               - square root of expr
# ('sqrt', expr, n)            - nth root of expr, n is ('#', int)
# ('*', expr1, expr2, ...)     - multiplication
# ('diff', expr, var1, ...)    - differentiation of expr with respect to var1 and optional other vars
# ('-', expr)                  - negative of expression, negative numbers are represented with this
# ('sum', expr, var, from, to) - summation of expr over variable var from from to to
# ('lim', expr, var, to)       - limit of expr when variable var approaches to from both positive and negative directions
# ('lim', expr, var, to, dir)  - limit of expr when variable var approaches to from direction dir: may be '+' or '-'
# ('int', var)                 - anti-derivative of 1 with respect to differential var
# ('int', expr, var)           - anti-derivative of expr with respect to differential var
# ('int', from, to)            - definite integral of 1 with respect to differential var
# ('int', expr, from, to)      - definite integral of expr with respect to differential var
#
# ) When parsing, explicit and implicit multiplication have different precedence, as well as latex
#   \frac and regular '/' division operators.
#
# ) Explicit multiplication and addition have higher precedence than integration, so they are included,
#   but lower precedence than limits or sums, so they end those expressions.
#
# ) Differentiation and partially integration are dynamically extracted from the ast tree being built so they have
#   no specific full grammar rules.
#
# ) Parsed negative numbers are always initiallly represented as ('-', ('#', positive))

from collections import OrderedDict
import re

import lalr1

def _tok_digit_or_var (tok, i = 0):
	return ('#', int (tok.grp [i])) if tok.grp [i] else ('@', tok.grp [i + 1])

_var_diff_start_rec = re.compile (r'^d(?=[^_])')

def _ast_is_var_differential (ast):
	return ast [0] == '@' and _var_diff_start_rec.match (ast [1])

_var_part_start_rec = re.compile (r'^\\partial ')

def _ast_is_var_partial (ast):
	return ast [0] == '@' and _var_part_start_rec.match (ast [1])

def _ast_neg (ast): # negatives are only represented here as ('-', ast), not as ('#', -1) or ('*', ('#', -1), ...)
	return ('-', ast)

def _ast_flatcat (op, ast0, ast1): # ,,,/O.o\,,,~~
	if ast0 [0] == op:
		if ast1 [0] == op:
			return ast0 + ast1 [1:]
		return ast0 + (ast1,)
	elif ast1 [0] == op:
		return (op, ast0) + ast1 [1:]
	return (op, ast0, ast1)

def _expr_int (ast): # construct indefinite integral ast
	if _ast_is_var_differential (ast) or ast == ('@', ''): # ('@', '') is for autocomplete
		return ('int', ast)

	elif ast [0] == '/':
		if _ast_is_var_differential (ast [1]):
			return ('int', ('/', ('#', 1), ast [2]), ast [1])
		elif ast [2] [0] == '*' and _ast_is_var_differential (ast [2] [-1]):
			return ('int', ('/', ast [1], ast [2] [1] if len (ast [2]) == 3 else ast [2] [:-1]), ast [2] [-1])

	elif ast [0] == '*' and (_ast_is_var_differential (ast [-1]) or ast [-1] == ('@', '')): # ('@', '') is for autocomplete
		return ('int', ast [1] if len (ast) == 3 else ast [:-1], ast [-1])

	elif ast [0] == '+' and ast [-1] [0] == '*' and _ast_is_var_differential (ast [-1] [-1]):
		return ('int', \
				ast [:-1] + (ast [-1] [:-1],) \
				if len (ast [-1]) > 3 else \
				ast [:-1] + (ast [-1] [1],) \
				, ast [-1] [-1])

	raise SyntaxError ('integration expecting a differential')

_diff_or_part_numer_rec = re.compile (r'^(?:d|\\partial)$')

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast [1] [0] == '@' and _diff_or_part_numer_rec.match (ast [1] [1]):
			p = 1
			v = ast [1] [1]

		elif ast [1] [0] == '^' and ast [1] [1] [0] == '@' and _diff_or_part_numer_rec.match (ast [1] [1] [1]) and \
				ast [1] [2] [0] == '#' and ast [1] [2] [1] > 0 and isinstance (ast [1] [2] [1], int):
			p = ast [1] [2] [1]
			v = ast [1] [1] [1]

		else:
			return None

		_ast_dv_check = _ast_is_var_differential if v [0] == 'd' else _ast_is_var_partial # make sure all are same type of differential, single or partial

		ns = (ast [2],) if ast [2] [0] != '*' else ast [2] [1:]
		ds = []
		cp = p

		for i in range (len (ns)):
			n = ns [i]

			if _ast_dv_check (n):
				dec = 1
			elif n [0] == '^' and _ast_dv_check (n [1]) and \
					n [2] [0] == '#' and n [2] [1] > 0 and isinstance (n [2] [1], int):
				dec = n [2] [1]
			else:
				return None

			cp -= dec

			if cp < 0:
				return None # raise SyntaxError?

			ds.append (n)

			if not cp:
				if i == len (ns) - 1:
					return ('diff', None) + tuple (ds)
				elif i == len (ns) - 2:
					return ('diff', ns [-1]) + tuple (ds)
				else:
					return ('diff', ('*',) + ns [i + 1:]) + tuple (ds)

		return None # raise SyntaxError?

	# start here
	if ast [0] == '/': # this part handles d/dx
		diff = _interpret_divide (ast)

		if diff and diff [1]:
			return diff

	elif ast [0] == '*': # this part needed to handle \frac{d}{dx}
		tail = []
		end  = len (ast)

		for i in range (end - 1, 0, -1):
			if ast [i] [0] == '/':
				diff = _interpret_divide (ast [i])

				if diff:
					if diff [1]:
						if i < end - 1:
							tail [0 : 0] = ast [i + 1 : end]

						tail.insert (0, diff)

					elif i < end - 1:
						tail.insert (0, ('diff', ast [i + 1] if i == end - 2 else ('*',) + ast [i + 1 : end]) + diff [2:])

					else:
						continue

					end = i

		if tail:
			tail = tail [0] if len (tail) == 1 else ('*',) + tuple (tail)

			return tail if end == 1 else _ast_flatcat ('*', ast [1], tail) if end == 2 else _ast_flatcat ('*', ast [:end], tail)

	return ast

def _expr_func (iparm, *args): # reorder higherarchy of ast tree for explicit parentheses func (x)^y or func(x)!
	if args [iparm] [0] == '!':
		if args [iparm] [1] [0] == '(':
			return ('!', args [:iparm] + (args [iparm] [1] [1],) + args [iparm + 1:])

	elif args [iparm] [0] == '^':
		if args [iparm] [1] [0] == '(':
			return ('^', args [:iparm] + (args [iparm] [1] [1],) + args [iparm + 1:], args [iparm] [2])

	return args

#...............................................................................................
class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJztnftv3DYSx/+ZA2IDFCDxrfyWh9szLq+6SYFiYQRpkx4CNLkiTXoFDv3fb2a+pB5caa111t61a6y84kvkcPjRkCKp9dHq3umzl/fUvSenT+n7+1f8/fT02avv2ffdGUc9f3Fy9uDl8zNO9Yy/nn9L3y/PTr/9Jyf68emLHzn05BtO/PABp3vx4Ozk2RNy' \
			b'nH777PnZyetHr86ecKJvzh48SqcmnTWdJZqTP5Pyf5A8/vHu49sc1+XJjod01b9OXrKTZeBSH1HcS5H/Ib4598fPXz18cvL9S8lNUkiZDx5RXU4fcHGPT384fXzCsY+fy+VI++KJVD+VwwlfnJ0+PeGwl8/p6+S7Vw+esO/3Lz/98eYTOT6/+/Pzazjf/fnb' \
			b'p9cfv3zIzs/vPnXu3958evcxe9789HsX/p//Zucvb37+3Lm/fPw5uz98+fX1+w+/Ze/b93/0zl9+6cp99+/s/L0XYSDYr+8/DHMkRyfO27dduZ/edOW+/5jFuXeuVkdVoyp9rOjs1VFTq4b8jdKWHMddsIT1AVUT2GXlz1hVueOBv/eSgy+o6YJGXA2+DOen' \
			b'j4sgMwxkJ7ssvkx9nLxVI5kakoo9kf+Oc4gb+BqPM4fwpRTPF5jj7HNDH2XdpzJOdGBGyf3IF5SmAFOGhVFALHzalZdQWDsK6H1aHdWpkHSdXgtvx4FhKmUok3XuSqrM7cv5NSR7UCZI1akB/PFsrONGvzjNKEklreDkz+gcnvym91fSbI3GV6caOMnVqiNW' \
			b'IXhoxcXxrUrNHEgYLRIklgKw1gnrYbARkbm6OaySMhqHLz1owD7IrAey1schbfZW4DCqIz3QUUxa5qZBzecSoEFzmqqVbCnxWHKKCdnRSJrATVwrQ5pPiVIIeSn0eJSmiE9e8gkodIt2gqXIPoxKnApjXx+uRTjKnGQjo7MiB1fd1HLfawaAiHLKK6p6q2yt' \
			b'bMN3IUlvRBnOKxeUi8paZZ2KitpbbJXVyhoukAig/LkszXcut7RjfTL/kZufWts1ymnlyEGFUSw1JWUXlKV8W+UoQzJ7jiwHV8K1ytfKN8pr5Y3yVnkS0CtLQjbnfCOxTWv4e3VElWGfQaBpcNI4GT7d9Oq6GjUlwblSTr7pSm5PsnxSUSjB1inUStJDEN6m' \
			b'ZjIQ23icQhLUieA3H0mf8IuorUM1Hap55CKaxyEWPjRZk5usAblWyN1LSxlI10A83exJEJKg3VvROtkWnVpF76s5qGiDdrBZFNxBGmjpsD/B4v7IgE4c7hUHK+9SoE03W7rLEGljUp+5HYbGonI23JLqtMnoSL0uSt2ElNotSo07xaceyAMID1o8OlOfelNJ' \
			b'6oPyUflWhZpFw+WhH2dojDPotE0VqVm09IANMiDNoutj7w1pJ9LejZLWSGMdupS2PnwpeSip0wBOYwCnMYDTYmxbxDoEu5Dgxs3SSAX3KLuGGBFCarkDb77RbJJ2UTutU+3MlpZpxWMLvZ/BpnZJaL+90GFvQieOHCy503sSZMVDni17IZduY30rboEVj+tu' \
			b'Q0WOpCF5OCetY9tbUSsZz+kFI7RkBTwsmZeLRqOwFY/XNAZq6Fk8Zjw8nlJ9i0F/qLtRmsEozWDU37B/u7GD5ktufAs4KKKYGPIToew18JrU0xv09AY9PZ2KUmBSWqR3SOjmEvJowOxzamPFAxGzz4GIbqAqKszsqe+ySQK/NwkCMEmqcHpfgjhphCMNKCMo' \
			b'hwciWvDaiMrYOBk8N4rcPsAeRZzEYE9CTxbEbmt6ar7kxpseEv3mV4P7AZvMoYU5tDCHFo/v8Lvsb6Tt9mnktKh9L7e2kbrrpBINH/QRcZKbgW8e3ES467zcaEWHT9y4W0BPzbXgW8EliBwgcoDI3YphnkN93O2oD99BTsh1INcBWQt7b0GssE0ZpWb1aFaP' \
			b'ZvXZNniohf18UYYgHPp8z4orE1CZkCsTUJkgg0USE1WOSBXTGDAeftWcSLutNtrDrxhJdvBSMiPtMVrh8IXlheo6rVTXaSm3lvuhViuycUlAtngNG7quLrB1VH7q07QKVgW68ynjqGKjIudEktQkSs2lUGVlmwyF8aoe14f3L/DmBROpRDKkvPPF1zjL9hNP' \
			b'ft7iQ2eSuAqNMukjO1+oOhXVpwq1bArjzTocwpt/jOo/FRm3iuSsfHsuOyoW1AxNRIWSZndWS/qjeF4f54UtXrNzPBZoFX+45nKeqXlbfEoNtGsaGKTtNdCHnksfcGC64KVPOVgdyTWjkC5pcZSKadbZKK8YqGccdS4PTaIj9PIx6YrvxcF9JpuU8p3aDQ82' \
			b'apI73sF93BkHvllxm4Z5VWsVjYpWRcdqj9Sa1NxOtWR7WEKSr9bTrcFSs8wsNFsc3gAxbCHeaMS7jHiL0VprsXHR41bjpU02OrxYzSvVzlArUidKOq+5srzNi4ZEQRq04m1nVMeKI3gnGbWo5e2EvIOTm8lxQstfM40e0qciVbZ0ldWyR5MTcxOTT/MfZU+V' \
			b'aVkKm68osOA4xfsGqWYV1UwY4Y2MlIS3WVKFKmod3hxnw4ge5MYb2Vh0ysHxVsc2l8ObEjkgjrhidVEWPDhCMh5wkJ8FYF9g1GxGLWTMwlq3MOwTlpE2jRm6BbMANgBGFkYLZjaTFpbB5r4CuDXz0LIyGK3k8uJiiFKAzlHCA5iSFAiYMSXt6MhUyRU9VpI9' \
			b'ctOIdHZYWGF2YJD7eA0RElsSPYnXSJICsUHEJGXjipzLPro7pDYixWqoBank8jgRUilA56iBmZIUCJhGaniR7g2VXNEjJdkjN41IZ4eFjZHSsFJ9vIYICSmJnkRqJEmB1CBiEqlxRc5lU+YdUpuR0qwDQQouLy5BCgE6R2ndI6UFKT2PlB4dHVJ6jBT6Pzkh' \
			b'0tlhYQVSGkh18RoiZKT0LFJDSUqk+ohppEYVYaTCHVIXIGXkdRFGCi4vLkEKATpH4bUSIGUEqfkxdHdFui4jZcZIGSBlgJQBUn1hBVIYb/fxGiJkpMwsUkNJSqT6iGmkRpczUvEOqQuQsqwAQQouLy5BCgE6R2nbI2UFKTuPlB0dHVJ2jJQFUhZIWSDVF1Yg' \
			b'ZYFUF59PCSk7i9Qw0xKpPmIaqVFFzmUv+x1Sm5HCq0qMFFxeXIIUAnSO0q5HyglSbh4pNzo6pNwYKQek8OwncthhYQVSDkh18Wi5Dik3i9RQkhKpPmIaqVFFzrF38I6pzUxFeU2OmYLLi0uYQoDOUXidDkxFYSrOMxVHR8dUHDMVwVQEUxFM9YUVTEUw1cVr' \
			b'iJCZirNMDSUpmeojppkaVUSYkhlO3c1ZhQ2zVrOcxY2o6WVTWXPA1cvmtC7FXzPNID8QdxxSHL9gspFHN2ByyZyXvGcr71s6nuiy8jJjK5Nfup2a/dKYt+Ad95i3gEv38xY+JULYNMeVMf2FkhrJM8/jKQyNKQyNKQyNKQxcyFrV69MYkqacJ+tL0ygtEz47' \
			b'qZGSG91d2FPOuhfSOQGrqekSrRMvukxp3UAQ3prdjubT1P+acJ+nGGN7v2I6LPnqv7CleDuju/lmuJ121+A1eodaN1iZwXxtCtA5Sl63T8i2SISwmTWc8ZFRlSt6VKUEhxMinR2WV6z/NAJmH68hQgLTzE7mjiQpTO8gYtL0jisiptfcdecXYKXl7XzGCi4v' \
			b'LsEKATpHmX5uRFIgYIYpPTo6psZzIwZzIwZzIwZzI4PCCqYwN9LHa4iQmZqdGxlJUjLVR0wzNarIOTbo7Yyp5mKs5paMZ/mqL4tY3DFmvkTNyA8/MGpweXEJagjQOcr0cyaSAgEzqJny6GgbT5vkQlznitnl7LDgAruUpB0k0ZAokzc7hVIKVsLXR0zDV+Yg' \
			b'/O1wCeHvxZ+TH3ph/uDy4hL+EKBzlOmfhiUFAmb4c+XR8Td+IM6FdMl0zC5nhwUX/KUk7SCJhkSZv9mH41Kwkr8+Ypq/smrC3w7XG/5e/Hn5dRYnP9LCLo+fa2H+EKBzlPE9f1748/P8+fLo+PNj/lIhrnPF7HJ2WHDBX0rSDpJoSJT587P8FYKV/PUR0/yV' \
			b'VRP+Lr04kbeHDjeBTYLIG7ear8DRDIgMhw0lZ4zl1uTyOFmTA3SOavrlVknB30EjOOA0sZRfj47oVYy4PK3pjxdgc5muc8XscnaU0xDTpg5Y408p20EybXFKy/yza7KFoGsr/X3E9Ep/XRzneAX4kqgu43Q3hH4NnuE67GbLtRe7CZcXl9hNBOgcZfrJGknR' \
			b'hQWcJqxnWx6d9RxP1eSiXOeK2eXsOIPSgKZUwyTa4pQM6PzmE23W5CuNaB8xbUTLQ8i89NrJXsj0Amc8TD659jChyeVxIj5TgM5RtjehkqILCzit82nr8sh82rHlzEW5zhWzy9lxBgWffYRrxwm1xQmU2lnbOSFkAekgYhLStRxkN2ytVrrf6LlxlyfTOTkv' \
			b'HjOIxYbOMOZs+x2c3cx2yVKezd4wiy0z2G0xY101w7lqnqheuEezml/9reRxuF/2ndqWyXyUTFx2L2Yl8zbr7Z8nkjdMIVfyGOPLPZh0wU4gqHfKgVnIghYLvpkJm7igeN733/FhZIvq9XISw5WiwkpZgktWzgZsWE+V6JPtctMhlG3zFEr6au1JcyUmpb7B' \
			b'ZoVreJWmpZH1iq8yL2affUxz182ss8AjtP10NfZAxhstP0/WdzxM2wbsHaiviQm3iAl7ERZmKRmhvdbBqE9kNLuig5/t/BI+Yn0pRPh57ppHp4081LXy6DeFifqf9vfprvgLv0aw4lf9Gtn6auQZLHAjsDL5IRlTiy1PDMoLVNT6AC3whRPXGH5oDhGpiQ/Z' \
			b'U0TKWXFzX2CQLrZDYQFbJVOTD8jMisPDr2DgLmRgK7uwrH3Ldp182By3VztQ5Oa7eOHNuzON8l1ZatVwiRcoNm6nW54c2al+eZpkpGOq2uHC6sKiDm2fsDb3qe3/wu96QJELxyOLRiILO5ipzuVC3eqtBw5bDxgW2/4puz+tcvxeLmn6ssPAq5tzWtwKc905' \
			b'z1L6XY3yLtF9W/mxg0t03Yubb24kR3q5vU26s4H7ZZo0SPn7aFLLTXr5x7XDaNR6U8Pu8qHsOueBl7ctT3TOta/jV8xJFU52nhgeW2N0LA0z7nSCSwvOHpIXBj101+Z27VtLl/2XTxobaqJbkQtreccNeZut8i46ovQPu1aypozfAxn+4kdas+JlfJ7g5n38' \
			b'jUwq5fkDk6eVWcyq/3WR9axioyZ+IeRcHn61Gn/kaTM/WfKubyUbI6u02RYriiGvJXYLiVLmxDqhywuDWBXEkmAnFxYAu3U/y8t9k2t6o981mV2rU9MfGrgPvS0/8rfJHVMglzZMxCWuf/hNBHGJSuxlVE4Kmf9Itq7IFipdlDnpNn1g1/z6R4rwk0Ws/+rM' \
			b'dEFqercxGdPhByZ14jNlEI/lf1RdTJiRbW/bchbMYK05rgP3NdDJ5MxVHxq2pgjmBailOYiG41U0Owu3g0MEbK9EQKt2cYiA+RXCsGsZHQ9txPuVB8RsrkhMr3Z0QEy9WUxdStrW2wgb1IaDjEAZyM286RrIvKgjXK9Fne3SoDprhmiJARpVMaru6Ee7eag7' \
			b'jB0e3Qi3uFxe3RsMbLtwHt1O5wWV2ANSicZM1H4OqMMdkjq82t8BdfhDUof8W9c9HVDHkmHOdamDn5z3dkAd8RpGfbt6wDDyD5I3H9jjuCTl8OAJhm2vGR/QZnuTtCn/XvggDzxR1zfygYRnwA79gH4bEbZbDA0eMyvM8vnx/wHH9LHX'

	_PARSER_TOP = 'expr'

	_GREEK    = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\pi|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'
	_SPECIAL  = r'\\partial|\\infty'
	_CHAR     = fr'[a-zA-Z]'
	_ONEVAR   = fr'{_CHAR}|{_GREEK}'
	_ONEVARPI = fr'{_CHAR}|{_GREEK}|{_SPECIAL}'

	TOKENS = OrderedDict ([ # order matters
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('TRIGH',         r'\\?(a(?:rc)?)?((?:sin|cos|tan|csc|sec|cot)h?)|\\operatorname\{(sech|csch)\}'),
		('SYMPY',         r'simplify|expand|factor|\?'),
		('SQRT',          r'\\?sqrt'),
		('LN',            r'\\?ln'),
		('LOG',           r'\\?log'),
		('LIM',           r'\\lim'),
		('SUM',           r'\\sum'),
		('INT',           r'\\int'),
		('LEFT',          r'\\left'),
		('RIGHT',         r'\\right'),
		('CDOT',          r'\\cdot'),
		('TO',            r'\\to'),
		('FRAC2',        fr'\\frac\s*(?:(\d)|({_ONEVARPI}))\s*(?:(\d)|({_ONEVARPI}))'),
		('FRAC1',        fr'\\frac\s*(?:(\d)|({_ONEVARPI}))'),
		('FRAC',          r'\\frac'),
		('VAR',          fr'\b_|(d|\\partial\s?)?({_ONEVAR})|{_SPECIAL}'),
		('OPERATOR',     fr'\\operatorname\{{({_CHAR}\w+)\}}|\$({_CHAR}\w+)'),
		('NUM',           r'(\d+\.\d*|\.\d+)|(\d+)'),
		('SUB1',         fr'_(?:(\d)|({_ONEVARPI}))'),
		('SUB',           r'_'),
		('CARET1',       fr'\^(?:(\d)|({_ONEVARPI}))'),
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
		('ignore',        r'\\,|\\?\s+'),
	])

	def expr            (self, expr_int):                      	             return expr_int

	def expr_int_1      (self, INT, SUB, expr_frac1, CARET, expr_frac2, expr_int):  return _expr_int (expr_int) + (expr_frac1, expr_frac2)
	def expr_int_2      (self, INT, SUB, expr_frac, CARET1, expr_int):              return _expr_int (expr_int) + (expr_frac, _tok_digit_or_var (CARET1))
	def expr_int_3      (self, INT, SUB1, CARET, expr_frac, expr_int):              return _expr_int (expr_int) + (_tok_digit_or_var (SUB1), expr_frac)
	def expr_int_4      (self, INT, SUB1, CARET1, expr_int):                        return _expr_int (expr_int) + (_tok_digit_or_var (SUB1), _tok_digit_or_var (CARET1))
	def expr_int_5      (self, INT, expr_int):                                      return _expr_int (expr_int)
	def expr_int_6      (self, expr_add):                                           return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_mul_exp):                return _ast_flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2      (self, expr_add, MINUS, expr_mul_exp):               return _ast_flatcat ('+', expr_add, _ast_neg (expr_mul_exp))
	def expr_add_3      (self, expr_mul_exp):                                return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_lim):                return _ast_flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_2  (self, expr_mul_exp, STAR, expr_lim):                return _ast_flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_3  (self, expr_lim):                                    return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_lim):                       return ('lim', expr_lim, expr_var, expr)
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CARET, PLUS, CURLYR, expr_lim):          return ('lim', expr_lim, expr_var, expr, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CARET, MINUS, CURLYR, expr_lim):         return ('lim', expr_lim, expr_var, expr, '-')
	def expr_lim_4      (self, expr_sum):                                                                     return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, CARET1, expr_lim):           return ('sum', expr_lim, expr_var, expr, _tok_digit_or_var (CARET1))
	def expr_sum_2      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, CARET, expr_frac, expr_lim): return ('sum', expr_lim, expr_var, expr, expr_frac)
	def expr_sum_3      (self, expr_neg):                                                                     return expr_neg

	def expr_neg_1      (self, MINUS, expr_diff):                            return _ast_neg (expr_diff)
	def expr_neg_2      (self, expr_diff):                                   return expr_diff

	def expr_diff       (self, expr_div):                                    return _expr_diff (expr_div)

	def expr_div_1      (self, expr_div, DIVIDE, expr_mul_imp):              return ('/', expr_div, expr_mul_imp)
	def expr_div_2      (self, expr_div, DIVIDE, MINUS, expr_mul_imp):       return ('/', expr_div, _ast_neg (expr_mul_imp))
	def expr_div_3      (self, expr_mul_imp):                                return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_func):                     return _ast_flatcat ('*', expr_mul_imp, expr_func)
	def expr_mul_imp_2  (self, expr_func):                                   return expr_func

	def expr_func_1     (self, SQRT, expr_func):                             return _expr_func (1, 'sqrt', expr_func)
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_func):   return _expr_func (1, 'sqrt', expr_func, expr)
	def expr_func_3     (self, LN, expr_func):                               return _expr_func (1, 'log', expr_func)
	def expr_func_4     (self, LOG, SUB, expr_frac, expr_func):              return _expr_func (1, 'log', expr_func, expr_frac)
	def expr_func_5     (self, LOG, SUB1, expr_func):                        return _expr_func (1, 'log', expr_func, _tok_digit_or_var (SUB1))
	def expr_func_6     (self, TRIGH, expr_func):                            return _expr_func (2, 'trigh', f'{"a" if TRIGH.grp [0] else ""}{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func)
	def expr_func_7     (self, TRIGH, CARET, expr_frac, expr_func):
		return \
				('^', _expr_func (2, 'trigh', TRIGH.grp [1] or TRIGH.grp [2], expr_func), expr_frac) \
				if expr_frac != ('-', ('#', 1)) else \
				_expr_func (2, 'trigh', TRIGH.grp [1] or TRIGH.grp [2], expr_func) \
				if TRIGH.grp [0] else \
				_expr_func (2, 'trigh', 'a' + (TRIGH.grp [1] or TRIGH.grp [2]), expr_func)

	def expr_func_8     (self, TRIGH, CARET1, expr_func):
		return \
				('^', _expr_func (2, 'trigh', f'a{TRIGH.grp [1] or TRIGH.grp [2]}' if TRIGH.grp [0] else TRIGH.grp [1] or TRIGH.grp [2], expr_func), \
				_tok_digit_or_var (CARET1))

	def expr_func_9     (self, SYMPY, expr_func):                            return _expr_func (2, 'sympy', SYMPY.text, expr_func)
	def expr_func_10    (self, OPERATOR, expr_func):                         return _expr_func (2, 'sympy', OPERATOR.grp [0] or OPERATOR.grp [1], expr_func)
	def expr_func_11    (self, expr_fact):                                   return expr_fact

	def expr_fact_1     (self, expr_fact, FACTORIAL):                        return ('!', expr_fact)
	def expr_fact_2     (self, expr_pow):                                    return expr_pow

	def expr_pow_1      (self, expr_pow, DOUBLESTAR, expr_func):             return ('^', expr_pow, expr_func)
	def expr_pow_2      (self, expr_pow, DOUBLESTAR, MINUS, expr_func):      return ('^', expr_pow, _ast_neg (expr_func))
	def expr_pow_3      (self, expr_pow, CARET, expr_frac):                  return ('^', expr_pow, expr_frac)
	def expr_pow_4      (self, expr_pow, CARET1):                            return ('^', expr_pow, _tok_digit_or_var (CARET1))
	def expr_pow_5      (self, expr_abs):                                    return expr_abs

	def expr_abs_1      (self, LEFT, BAR1, expr, RIGHT, BAR2):               return ('|', expr)
	def expr_abs_2      (self, BAR1, expr, BAR2):                            return ('|', expr)
	def expr_abs_3      (self, expr_paren):                                  return expr_paren

	def expr_paren_1    (self, PARENL, expr, PARENR):                        return ('(', expr)
	def expr_paren_2    (self, LEFT, PARENL, expr, RIGHT, PARENR):           return ('(', expr)
	def expr_paren_3    (self, IGNORE_CURLY, CURLYL, expr, CURLYR):          return expr
	def expr_paren_4    (self, expr_frac):                                   return expr_frac

	def expr_frac_1     (self, FRAC, expr_term1, expr_term2):                return ('/', expr_term1, expr_term2)
	def expr_frac_2     (self, FRAC1, expr_term):                            return ('/', _tok_digit_or_var (FRAC1), expr_term)
	def expr_frac_3     (self, FRAC2):                                       return ('/', _tok_digit_or_var (FRAC2), _tok_digit_or_var (FRAC2, 2))
	def expr_frac_4     (self, expr_term):                                   return expr_term

	def expr_term_1     (self, CURLYL, expr, CURLYR):                        return expr
	def expr_term_2     (self, expr_var):                                    return expr_var
	def expr_term_3     (self, expr_num):                                    return expr_num

	def expr_num        (self, NUM):                                         return ('#', float (NUM.grp [0]), NUM.text) if NUM.grp [0] else ('#', int (NUM.grp [1]))
	def expr_var_1      (self, text_var, PRIMES, subvar):                    return ('@', f'{text_var}{subvar}{PRIMES.text}')
	def expr_var_2      (self, text_var, subvar, PRIMES):                    return ('@', f'{text_var}{subvar}{PRIMES.text}')
	def expr_var_3      (self, text_var, PRIMES):                            return ('@', f'{text_var}{PRIMES.text}')
	def expr_var_4      (self, text_var, subvar):                            return ('@', f'{text_var}{subvar}')
	def expr_var_5      (self, text_var):                                    return ('@', text_var)
	def subvar_1        (self, SUB, CURLYL, expr_var, CURLYR):               return f'_{{{expr_var [1]}}}'
	def subvar_2        (self, SUB, CURLYL, NUM, CURLYR):                    return f'_{{{NUM.text}}}'
	def subvar_3        (self, SUB, CURLYL, NUM, subvar, CURLYR):            return f'_{{{NUM.text}{subvar}}}'
	def subvar_5        (self, SUB1):                                        return SUB1.text

	def text_var        (self, VAR):                                         return f'\\partial {VAR.grp [1]}' if VAR.grp [0] and VAR.grp [0] [0] == '\\' else VAR.text

	#...............................................................................................
	_AUTOCOMPLETE_SUBSTITUTE = { # autocomplete means autocomplete AST tree so it can be rendered, not expression
		'CARET1': 'CARET',
		'SUB1'  : 'SUB',
		'CARET1': 'CARET',
		'FRAC2' : 'FRAC',
		'FRAC1' : 'FRAC',
	}

	_AUTOCOMPLETE_CLOSE = {
		# 'LEFT'    : '\\left',
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

	def _parse_autocomplete_expr_int (self):
		s               = self.stack [-1]
		self.stack [-1] = (s [0], s [1], ('*', s [2], ('@', '')))
		expr_vars       = set ()

		if self.autocompleting:
			stack = [s [2]]

			while stack:
				ast = stack.pop ()

				if ast [0] == '@':
					expr_vars.add (ast [1])
				else:
					stack.extend (filter (lambda a: isinstance (a, tuple), ast))

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

		if pos >= len (rule [1]): # syntax error raised by rule reduction function?
			if rule [0] == 'expr_int': # special case error handling for integration
				return self._parse_autocomplete_expr_int ()

			return False

		sym = rule [1] [pos]

		if sym in self.TOKENS:
			self.tokens.insert (self.tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

			if self.autocompleting and sym in self._AUTOCOMPLETE_CLOSE:
				self.autocomplete.append (self._AUTOCOMPLETE_CLOSE [sym])
			else:
				self.autocompleting = False

		else:
			self.tokens.insert (self.tokidx, lalr1.Token ('VAR', '', self.tok.pos, (None, '')))
			self._mark_error ()

		return True

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

		# rated = list (rated)
		# for i in rated: print (i)

		return next (iter (rated)) [-1]

# if __name__ == '__main__':
# 	p = Parser ()
# 	a = p.parse ('sin^{-1}x')
# 	print (a)
