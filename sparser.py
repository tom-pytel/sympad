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
# ) Future: vectors and matrices, assumptions, stateful variables, multi-parameter function calls (comma expressions), piecewise expressions

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
			b'eJztnftv3DYSx/+ZA+IFuID4lvJbHm7PuDRpnaTAYREEeR4CtGmQNL0DDv3fb2a+lCjKkqyN1+vdnrGyHhTJmSE/GvG165PNnR/OHj9/ekfdOXv8jPaPzn6g/dPnsv/pXIKefE/7Z+dn3/+djt89f/yAA0+/43v3753T/sd756ePH3Ee3z9+cn768sHz80f/' \
			b'5Ljn9x6kg05HQ0e5zdEfi5ifJY+/vfv4tr3X5ckn9ynVP06f8SmrwFIfPnl+/9Hp02eS8AFF5MAfH4kZD89+Pnt4yuEPn3BwivX0+X3sdZtENLr34NmT87N7j7IcPv3x/OyHU87s2RPanf70/N4jvnrz6vO731/+9vnl29++vv7l3ZffX32m0C9fX/8hJ+/+' \
			b'8+nzyy9fP73rLt5//fjm5cd3/8o3X9NpL/bHr7+2p7+/+9ydv//86k17/omEfmwvXr3+0oX/9u8u+qs3v/dFZnFdjj2Zv3zoQj987NL9+vWXlx9+/dRevv3wRz59/77TN9vCCeik0+zt23R654XanKyNV8auFE4cn2i1NnL06qRWjaIAY1SzasMkpLtc6yCp' \
			b'5Y/yWNtVvq7y5VqE0H2JHuTPBLWOq+K6yiF0wiIsdtas0uVaQ82oTjTlq2v+W3VBtn/ZReUwPiO9HNmXMpMra8VEXQT7C1fl/XDhyhYhsX9FWksh8JlJZyeVXPBVTVonAZxJPyydrxs+NuqEirhRUuqVsnxQmqrDrSZvS7X6JbGqItJaaz6x8mdieyNd1/l6' \
			b'LSUc5W+NcpcTOjox0q9wTidcGiRZCNBU5bqSkq9WbUCtUpDph2oNbUnBNoyqVM4cdlRwq3RNTEoJa7KzkXjp0lYSg8Jt3/7QFqKxrVEUp60nspfDU0Wly6oMcFkKYSrFprn6CpUZ0qo7k+ok6ZSEVGD9k+QURNcUvCpjDWO013Qpwp1YnOxKcnMgFdpYGF/l' \
			b'cJQRZU8GkXfYkFgVFTsBG5WtlW2UM8pZriauFaPocXOVcly8ZDs9pfw4kUXEFRWtt8o7qkp+urhOqeQd40gPuuGHk5VwjfKUg/IqKEeXtI/K1aIwxam5cnyjQqWCVsGoYFVwKlB0iulU1C8YMyr2DVUsl36UPaVjE8hb8ZVFoG1DyQq6PjArLHR1FtZosUro' \
			b'X4mrg+oaVjq5e6P6Op2KHYpaufRaeXMU0FiT1EeBknw5+FTOXmrjOPgPqQaCHDwM8g72Gdw0Uj3kuunZv3aNSKqBVJulAo19yEZV8nuvk+2Vp/qIytd70SDst7Dh3jhH+AgPHyEI90wnVHzylSgiF1rajwj2ZMARqexQP5xKPLuYcFki3aTYcVFsyfskJJ8c' \
			b'8PgFuIKA2g7AIoj4EFWoVWhUrFhDxIgpeVTU/jnoMt3QG/7wdbRSkAeqW32ounHzzAj6mo/c9mFND0CvCnpZORaOdcPtH3Oh+enlgdpGhs/NEoNmiUGzxKz4biOXHjdN0seI6OPwhSY5QSPubQ/yEktGimxPr2RugkCq36NUwg0e3oe9lC3Ji1vjjfcUa4IW' \
			b'i0FDxaBRciwYb7jpdCzKnniUsk+lHI9Gc2krmQWtnwjTgjzs3N4xgxbOhttCBo0gI645wFOH1HBqxGOfxKptAdmRcYN6JJQvLS5temnZg+igb/jFaQ/hxSlvTNLkCIjjN7ZJ71+L96/F+5cOgySI36DavZ2KYQCEwavbIF8jGbLDFmleMN+DdRGuAIgG6ICL' \
			b'dADMGreCwcHCxoDUocZBDBqxWMBzB/IMkHR3oVlGmjhUrkPlOmlcSag0p9z+mgoeRQ1VOAfUAh9CTOUOvxMEtYFbI1M8TPEwxR+Nb/f2aJRlJrzUkkcteVSPw+PgUDsuOY6ACgmoEDqQbuArIKJPEeNhdsA2rH2E9jwTcIIx6NQz8aJ3OaxEStYwukayOsWs' \
			b'D9jC5mB184eqG1dpk0bLqzRcXolLrdSGhNPTzLnjiU6q2yS+kzHUUlQkd8uGmWxSdghiNoqD9GDVoxgjNjOIMq6bVe/pDW8ZtYpELdlAQEcVKaRRdaVqrWqjaqKWiI2qqVSjVWNUQ1ZSHZARbAXZUFH5V1wZbC8VV0XhYh6FcfGxbWwcD9rxgDuPtvMQOA8E' \
			b'c/lzr5d7vDxXwhMPXG48XM9NSW5H8tyPY3/u2FqegLU8G2tlMk9mvbkEKNTwPvDEelBrtj7kbc0TtTwBKLW8DrxzMt+IaXIqmjUVyZrKcB05O3zWVLI1S6hEtjc8pcjhPM9LRnhME9Kh4WlcDuRZU07YtFnwFHtgmSQ98iS+4mlrsm5tWQHRnVpWa88zrWm2' \
			b'lVcLeP6jWHRwspiAsiD5QSZdWR0Wzn9c46ITZcKSOSLLZLNYC83TqDyTTRJtqxUBsuZw61+o/7p4d81zVFWgY/UnN3KUzHC6WWSviGnBaLM9mlbo3AbNbbCcRVELiLzvsciXPPFXCYt86MHYB1BuIfo0gsiwzRb5MYNWC4Myuw0ImcAheznpLH452nL6xL6q' \
			b'Qy+lH4dP4tq+mD529V1+fGtzl58CqiQ6mj/lZXoL3xx8RuAzJXwG8BnAZ6bhMwKfmYfP5E3gMyV8Zh6+Luk8fF20LeAzJXxIPwEfHF5PzBL47C18s/AFgS+U8AXAFwBfmIYvCHxhHr6QN4EvlPCFefi6pPPwddG2gC+U8CH9BHwB8GUxS+BzS+C7rpZiuHJj' \
			b'0U60F92Om4zzhNZCaF0SWoPQGoTWBaEsqt0KWmuhtZ6ntZ/YIe+W1tRelGxT7ohgWqEX6O2ymqe3izbRcpRb4xDXArFESBwn1cY5rsFxFriEY3/L8dU5boTjsr8jC1GxKpMTNyXHTd4KjhvhuJnnuJ/YIe8hxw04bsBxk5ZIytmQ4y6reY67aFMcN5McN+C4' \
			b'yRwnw8c5bsBxFriE43DL8ZU5NtJXMmVfyaCvZNBXMmVfyVR563Ms0ZB0muMisUPeA44N+k5yQATTCh1ynLOa5ThHm+BYbo1ybNCdMrld0Wo4yrFBj6oncAnH8Zbjq3OshWNdcqzBsQbHuuRY563gWAvHep7jfmKHvIcca3CswbEGx0gx5LjLap7jLtoUx3qS' \
			b'Yw2OdeY4GT7OsQbHWeASjutbjq/OsReOfcmxB8ceHPuSY5+3gmMvHPt5jvuJHfIecuzBsQfHHhwjxZDjLqt5jrtoUxxPdvKkCKBTy3EyfJxjD46zwCUcN+2MwLeQ7PcEM8+jXjPPeldMc29bsC4HJgwGJgwGJkw5MGFC3vpY81S+jFOY+XGKIr1D9kOyMVYh' \
			b'B0QwrdwLZEtog8jzcHdCp+AOk3BjBMNg5kBLGz92RTAOOAYyekKXAK6rb/fU++L7KJy1DGaYcjDDYDDDYDDDlIMZjFu7FVQjJCD1DNX99A7ZD6nGeEYahDMYz0gBQ6q7rOaR7qJNIT05nmEwnmHyeEar2jjOGM/oCVyE86L5sNuGxzzLMqBhygENgwENgwEN' \
			b'Uw5omCZvRcNDBjTM/IBGkdgh7yHIGNAwGNAwGNBIKYYgd1nNg9xFmwJ5ckDDYEDD5AGN1vBxkDGg0RO4CORFc2u7BLm+jGVzpDhb6Q/asj9o0R+06A/asj9odd76OEs0JJ3GuUjskHfCuUe0RZfQokto0SXM6QZQ5xuzUPfSj0NtJ3uFFr1Cm3uFrfmjUFv0' \
			b'CnsCF0G9aM7uFuolUEsrmvd9qLHGRkJlaVUBtc1bAbUVqO081P3EDnm3UNsMtQXUFlBbQN2lG0Ld3ZiHOqefgNpOQm0Btc1QJ/PHobaAOgtcBPXe5wL/ulA7gdqVUDtAjZVjtlw6ZntbAbWsHbPzi8eKxA55t1C7DDVWkcnBpF+66KUbQt3dmIc6p5+A2k1C' \
			b'7QC1y1An88ehdoA6C1wE9Q4mBsmi0WWei+iu+Hv238K46WEeDpZ0Le5bl+47LZHUcN+6dN8stt2KOUNx37SPaJbIjwch67HJw34uDkIS8hp+vA6qrjGLCG+u4c01vHlOPZxI7OfcY19Xbmw+MWczMZ846dQ1nLrOTr0tlPH5RDj1nsBF/O9oQvHb4L8i9jtg' \
			b'3l2Xh4/i4WPp4SM8fISHj6WHj3krPHwUDx8Fej5o5Dvm5/tZOEho/XzMfj7Cz0f4+Qg/36Ub+vl+nvOuPmcx4erjJOoady20a919Kotxdx/h7rPQRbjvaN7x0HAPTDy5sxuGXsYGbTk2aDE2aDE2aMuxQS6zdiugl4FBi4FBi5aNHEag72fhIKGFvs7QY4TQ' \
			b'YoTQYoQwpxtC389zHvqcRZIHRYfoT44WptQWKrbkJ03HyceAYU/yIvJrtRl840OPLR+N4210prlbKTq2THQO029aFzoBoQDYhw7TLGNfwWDeptZ9rudnUhik/hLPufWdl3+fYstvUvSXdE4wsB702lbyEzS7qWC92zquLqlnJ95/vL55rTTd5x+H6uqeGzdu' \
			b'3wzU8fox0NKgnEahLZYRJLJ71h0erYseYEJWXK8fqHbrCsyxuYPmGj2ClrVj23gFiniDbr9ubj2/tLGu3fuThgf0eg+qif+PVT1WzVhTYnZc3Xa2uqvFNR56c7vb1vuWX8OdrXSXKl5fqfIDprH4sLz6Obg3YXVVCnbd3NMyt9xAzeGwjrHUvvfyFUV3S8QY' \
			b'EQZEmK2IMIdNBN9mIsw8Ef6QXgnf/jK48HX8YsihucYXA+e6786fbS57HWj8CP56rPYvfm+edN0cPwMXPUCudK60Y2kM7K4RoP5LVa1RxfEvWcVOX9dz/S11zIO6eu91TM68oVK/S4TF5u66luqu/5rVbQ6quo0ShQ6guhv5dQ9t8G8hpCprriOtPRdbneaQ' \
			b'6SQGsZungwP3EkiFDb6iOUzUcAuPaliik7D4Av8UYKPdsrZiWNpEXNomvJQX/rElBiFgWpgPlyMQ8pqdrRz6lm22+XoOtmiXUWlKMV9WxotK9+pF2xarX/xYbV2YOypILkVzlypfStHyF+tJee9e4DeuNglyKZjSwJgWBVBpiEa9PPG7WJvuAUnJO3c2zEpK' \
			b'gkuhb2E3jRku5B1m8q63yjuWect/hJJV4Bpfhqh5drGbOUyzebwEg4f05ScIZTxOxmZkWB5D6y/k38hIPhNZ1a6Xm+GXhyk+7O/pKBnZYUaYEp3Mzqr2g5eN7X8kRzeeIyZZx/NNY+HdNCVTovofvNLKsOEbaSX/AmvDP651ZemB37thyUfEhh2JJce+7CNS' \
			b'47xUevoLwXZedq1GPqY75XZCcUtUqKFCvViJdg5cmh2TuhD13OppJj/pZhlHNGquRyMZE9zVJori+01Z02INA7TG6tZSdyePOi9IqHtLEXrLD/IyA1kv1bje+oFmzkKnrndjz8we1GEOcXxD0ehrqkSvdrdBU3NpJV7Quqi7CxY0i+oqqv7GrY52G9zqNmp1' \
			b'IAK1OkYisPpxND3stDdiJze59rTBTHczZlq1rw1m+psx06l9bTAz3IyZUe1rg5lxSzPnXyHbGcsdoW026l0OQpoLIbMbTK6v+d25zHaj5jcsBrw0Wn/jfuCCeCiF5iBKwasb2tAROrBmFPcdb3hDueg0lMSjR2wmQo38ul1XQrCeLOIel23HLlwaoNA6pbLy' \
			b'G0x0cO3ADpdZkBZXWw/oz3cjVtGj35xeOTy3Rf1X+e1RyvTF6n+NqRPu' 

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
		('ignore',        r'\\,|\\?\s+'),
	])

	_FUNC_AST_REMAP = {
		'abs'      : lambda expr: _expr_func (1, '|', expr), # expr.strip_paren ()),
		'exp'      : lambda expr: _expr_func (2, '^', ('@', 'e'), expr), # expr.strip_paren ()),
		'factorial': lambda expr: _expr_func (1, '!', expr), # expr.strip_paren ()),
		'ln'       : lambda expr: _expr_func (1, 'log', expr),
	}

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

	def expr_paren_1    (self, PARENL, expr, PARENR):                        return AST ('(', expr)
	def expr_paren_2    (self, LEFT, PARENL, expr, RIGHT, PARENR):           return AST ('(', expr)
	def expr_paren_3    (self, IGNORE_CURLY, CURLYL, expr, CURLYR):          return expr
	def expr_paren_4    (self, expr_frac):                                   return expr_frac

	def expr_frac_1     (self, FRAC, expr_term1, expr_term2):                return AST ('/', expr_term1, expr_term2)
	def expr_frac_2     (self, FRAC1, expr_term):                            return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_term)
	def expr_frac_3     (self, FRAC2):                                       return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4     (self, expr_term):                                   return expr_term

	def expr_term_1     (self, CURLYL, expr, CURLYR):                        return expr
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
			self.tokens.insert (self.tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, (None, None, '')))
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
	a = p.parse ('\\lim') [0]
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
