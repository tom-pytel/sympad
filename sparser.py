# TODO: \int _

# Builds expression tree from text, nodes are nested tuples of the form:
#
# ('#', 'num')                  - numbers represented as strings to pass on arbitrary precision to sympy
# ('@', 'var')                  - variable name, can take forms: 'x', "x'", 'dx', '\partial x', 'x_2', '\partial x_{y_2}', "d\alpha_{x_{\beta''}'}'''"
# ('/', numer, denom)           - fraction numer(ator) / denom(inator)
# ('(', expr)                   - explicit parentheses
# ('|', expr)                   - absolute value
# ('^', base, exp)              - power base ^ exp(onent)
# ('!', expr)                   - factorial
# ('func', 'func', expr)        - sympy or regular python function 'func', will be called with sympy expression
# ('log', expr)                 - natural logarithm of expr
# ('log', expr, base)           - logarithm of expr in base
# ('sqrt', expr)                - square root of expr
# ('sqrt', expr, n)             - nth root of expr
# ('*', (expr1, expr2, ...))    - multiplication
# ('diff', expr, (var1, ...))   - differentiation of expr with respect to var1 and optional other vars
# ('-', expr)                   - negative of expression, negative numbers are represented with this at least initially
# ('sum', expr, var, from, to)  - summation of expr over variable var from from to to
# ('lim', expr, var, to)        - limit of expr when variable var approaches to from both positive and negative directions
# ('lim', expr, var, to, dir)   - limit of expr when variable var approaches to from direction dir: may be '+' or '-'
# ('intg', None, var)           - anti-derivative of 1 with respect to differential var
# ('intg', expr, var)           - anti-derivative of expr with respect to differential var
# ('intg', None, var, from, to) - definite integral of 1 with respect to differential var
# ('intg', expr, var, from, to) - definite integral of expr with respect to differential var
# ('+', (expr1, expr2, ...))    - addition
#
# ) When parsing, explicit and implicit multiplication have different precedence, as well as latex
#   \frac and regular '/' division operators.
#
# ) Explicit multiplication and addition have higher precedence than integration, so they are included in the expression to be integrated,
#   but lower precedence than limits or sums, so they end those expressions.
#
# ) Differentiation and partially integration are dynamically extracted from the tree being built so they have
#   no specific full grammar rules.

from collections import OrderedDict
import re

import lalr1
import sast as ass
from sast import ast as AST

def _ast_from_tok_digit_or_var (tok, i = 0): # special-cased infinity 'oo' is super-special
	return AST ('#', tok.grp [i]) if tok.grp [i] else AST ('@', '\\infty' if tok.grp [i + 1] else tok.grp [i + 2])

# def _ast_neg_stack (ast):
# 	return \
# 			AST ('-', ast)            if not ast.is_num else \
# 			AST ('#', ast.num [1:])   if ast.num.is_minus else \
# 			AST ('#', f'-{ast.num}')

def _expr_int (ast, from_to = ()): # construct indefinite integral ast
	if ast.is_differential_var or ast.is_null_var:# == ('@', ''): # ('@', '') is for autocomplete
		return AST ('intg', None, ast, *from_to)

	elif ast.is_div:
		if ast.numer.is_differential_var:
			return AST ('intg', ('/', ast.One, ast.denom), ast.numer, *from_to)
		elif ast.denom.is_mul and ast.denom.muls [-1].is_differential_var:
			return AST ('intg', ('/', ast.numer, ast.denom.muls [0] if len (ast.denom.muls) == 2 else AST ('*', ast.denom.muls [:-1])), ast.denom.muls [-1], *from_to)

	elif ast.is_mul and (ast.muls [-1].is_differential_var or ast.muls [-1].is_null_var): # null_var is for autocomplete
		return AST ('intg', ast.muls [0] if len (ast.muls) == 2 else AST ('*', ast.muls [:-1]), ast.muls [-1], *from_to)

	elif ast.is_add and ast.adds [-1].is_mul and ast.adds [-1].muls [-1].is_differential_var:
		return AST ('intg', \
				AST ('+', ast.adds [:-1] + (AST ('*', ast.adds [-1].muls [:-1]),))
				if len (ast.adds [-1]) > 3 else \
				AST ('+', ast.adds [:-1] + (ast.adds [-1].muls [0],)) \
				, ast.adds [-1].muls [-1], *from_to)

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

		ast_dv_check = (lambda n: n.is_differential_var) if v [0] == 'd' else (lambda n: n.is_partial_var)

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
			b'eJztXXlvGzcW/zILRAIoYHjP5L8cbtfYNGldp8BCEIKkcRcBmjTI0V2g6Hffd5HDoWd02LJs1YXoIYfD4x0/PpLzKHm2fHD6/PyBevDs9Du4/vgSr9+dPn/5I979cEaPXnwL1/Oz02//CfE3L58/wcyTb/DZ40dncP3+0dnJ82eQOP32+Yuzk1dPXp49+zeW' \
			b'PXv0RCItsYGYHmPx59TdT9TGPy4+vE3PcpuYeAy1/nVyjkkkAXt9+uLl42cnP55TxSdQ8Jxof8xX7Or7Z8TBk6cv6FFRkgh59OT8xdnpI6Th6elPp09P+n4w7/uz0+9OsP75C7ic/PDy0TO8+/n1p4svr3779Ortb1/f/Hrx+cvrT5D7+eub3ylx8b+Pn159' \
			b'/vrxorh5A8ni6Yev71Pyy8WnnP7l0+ufU/ojdPIh3bx+8znn//bfXPz1z19y+uuHXPX9119fvXv/Md2+ffd7n/zll0zDxX96+jIJBZG/vntftgiJTM7btyn57kMi4cFKLWcL45Sxc8UJhwmtFoZir2at6hRkGKO6ecqjnHy70AFTlv5MVAs37+9tf7ugtrFu' \
			b'QzUbvlgDOXpeZdkyE5OYsnyx8gDLML1RzTQ20+LfPGfZ8jYXxTxMGTVzcGPm/Z21xKseZPv6rnoe6jtjBjmxvAOqSdRq1nBDWJifSp6kF1QOhA30eIViDsoiKUqDCP186ilpMW5RyA7KLCLGjv5Mm/LlvuvvIYGMaL5kxjgJqVbNQIaMjRYT+LRTDBEdgJaG' \
			b'RNzMU0arJMuUudCiFm5THuiOUo4vILm53AMKSWhAlfFUTm4NdQtQMIUEQhIiip75AhURJiBnZmxmS26rDNf3ADhlLAPbQ3KB95ASmqQQsAJgGym38yJngV24+aBM9Vxu4Y66tcQnsyMd9nl6PA/v+nwWDDQOnIARWEKfqHbQtG1UVDjoASkgKhthuNGARCKV' \
			b'18ob5RrlNKoNtWQUDslW2Q70h2MHFQmtORS5CQRGh0S4qFyroA0VlLPKOeUgMxDBUKZFnfiofKt8p0KjglbBqGBVgJKQ6FY4QNASWLwuZ0Aw3gHREDmo3BwDD8uZZS4iXZEHzOyYM89RkFxHRW9D0jaykEFyRJHhyAphnh4fB2g84wQowcgzQ54ZcprZ1KwT' \
			b'zQ+RPmJTW65KLRxA6J0gm6kx+iDdQn8sDGPX9ccjbJ+9skKMX9ert8pDP175sNe+w6FEy8McW2RE8Qh3lF0wB9p3LWufxeJSDX88Iy0IA/Z4SHaiDyFdU7ypkpZxquNWpdn+eKkUeHAHNjWBh15gQxNI9wEYCipEFVqkUEok2wBCrZEDUjYkeCqzk21suNWI' \
			b'DdxFBS1n7d0lDahC2u4USeGOkYRrGCMrCcMrCcMrCTNHABLycFamQpoLaSp0sLUOQQxnXaLBEA3HYb6MEZpRnIfoz0l//iD9wezHhtG7A83X3u9sQgMvYwIjlwSE8ztb5KOB0hJXHMdC7MyzlK1I2R8N5bTEMFssGgRAgYwSLhNMtTBY4hLC8NrB0Eox8Fom' \
			b'MCBDpAXkLLR54WDnxyAiXMYYXpTYkT1xO5KLt5Zvrcw1lucay3MNRFVnDKPI5b2eKEEzkj3cFnCJU5893NRnmDtjOWIpehlW3h1mUvEymqlzxxFT4pgux3eatItDwvICmnQXuHZg+xto3IzpGpDvBBuOseEYG47WIZqfask+lLoN9XsAGYt0iTsnkacoeBGk' \
			b'iJfGRGVqQGieheZZaP5o7K3XR0MsosGTljxrybN6HOPbsXYSigMrJLBCIALaGMmBC3opGO/UhmCJREcmGt8+z3gjbHiW8kTucHsLxLfMa8vVWinZ3j3GurtGkr1jJKHeOnmj3Mgr5YYm9kaRH6JDqnoCqHdcu7Bf0BUDty1wEocGn61XpyLACdAGSPMqBtUC' \
			b'dlrVdqprVAfK8qoLqgNzgJ2CLBpggmQCRCHH+LYOeUPmkDt88WMsEIteIasWwOgCXZ7oiwHBWHIwQRJ9TB07JEEQC6BoAewvAnqdkEd2+6E7DT0zWBpLRCXNopcyYHlskJoF/tBvs0D/lsd7jKEKFobqIOoF8L/w2IznRtC7iLfwF9BVhMXiCqfR3eVc6vp2' \
			b'ZA5/8AxBg4CxDnQAjar2kg7Q84aXNTpo5YO6aCd1IWUqXbS76oI7GtNFomNF1u+voRM0JRRqtWBWoOsaxeTaWA6dIGZSO325SkHU904aSv2N6qggaUWuR9ITWsDI2kL7acU8shm8gv6AITbLpSLRhG6hy9iqCJgGKGvSq9+gWr+betE9g94SnAPQ1dqrG/7g' \
			b'Ge7AbATVB5wTQHigUmAwMALQ3e1R6XhCAP38oALbDZCBcsbLGlwE+Sxg1mohsjx2Q0ZHpy8BRGpU6IAcdPZDE9A5HgVAqODxhS3gQshiyFDT44BBcWg+ZAE96EQHqHeBR12sXdECj2AUBELF7FnPv+shZIZWoIJQKObibYAUE35CASE9jaJwHUPRqhwQKRih' \
			b'+7PMLs0HmXW93q4v0JvRDtsQqGi28xS53G1lUnKl2qRgtx1hJVHWo4UaGgVM6kWsjNQctzI9ySva/N57eHQqB4JHx/Aos0t4dHwWZjM8qjYSPPg4EEUud1vBI1eq4dH18BDKCnh0k/CQXgQeUnMcHj3JCI9w7+GBfKaA8MBINi85u4AH3ga6boCHGYYED2rO' \
			b'cORyt0N49JUqeFC3DI/UVA8PamgUHqkXhkeqOQqPguQVHSy69/CgQ5wcCB6a4VFml/DQBA+9GR562EaCB5/jNHL6Urqt4JEr1fDQPTyEsgIeehIe0ovAQ2qOw6MneUUnzu49PLzKgeDhGR5ldgkPOmiJ103w8MM2Ejw8w8MzPKTbCh65Ug0P38NDKCvg4Sfh' \
			b'Ib0IPKTmODx6khEeHcLDyB4nTO9yxiHjN6GmqYEzsvVZj504Dp+RbdAWUDJDODXtDhujdZshVC0es4Vrg1siSkWKRrZF9JQK5TDYIZFUF5y/9t2S4LBsx0nzgkXeM1HkUpEai5Tbcac1HAPD8dImKlFdgDNM7qRMm7t2JGACqbQwDtJAm6merWI/pf7Q4SHu' \
			b'LFv/EPdyoFGIzZ9zOm2+rbHbiNwjtnetyoHsHe+1Btkl3ALl8HWTyWuHzSSY8XbL8HYr9VzBLFeqMdZvtxJxBaomt1upFzF5UnMcTT3JKz71e++nxE7lQBDh/dYgu5wSab9lNu+3TNVGwgfvtwzvt1K3FT5ypRof/X4rUVbgY3K/lXoRfEjNcXz0JK/4NNp+' \
			b'8KF3gUhz91CCbqQUECWW19WD7NIdQutqu35dTU01gzZsv7S2vLS28p2lvvPKb5If1K6TfnWd6OuxYidX16kXcadIzVGsFFQTVuzfWGGsWJUDYYXf/A6yS6yw72y984yaagZtULOCFfarUeTKzius5Ac1VmyPFaGvwMrke+HUi2BFao5jpad6xWcF/8YKYcWp' \
			b'HAgrjrFSZpdYcYQVtx4rjrHihs0krDjGimOs9J1XWMkPaqy4HitCX4EVN4kV6UWwIjXHsdKTRVjZ/Z0wn3YpXf/rQQOSBYFdBTpNgR53GwCCxumD4OGVS84pcEOLlg4pRuB0BJ1x8PDiJbXRGtU61a9eePHCa5fU7xA3ufcCNrrRBJ1+9cL09biZXLpwFwwa' \
			b'rjQKGel1xUflrmJatsbKdVGyO0T0PuxMVDmQnYlsZ8rs0s5EsjOR4IKR7jgasTaRrU0cNpasTWRrE9na9CRU1qasWhuc2BscIbQwOHHSyaBN7kyMjtQeNzp9IBRd7VXy4VFkCEjuoFhqVQ6EJd5UD7JLLNGO2vKO2raMpXYcSy1jqR02lrDEW2vLW+uChApL' \
			b'ZdUaS7zBtnyWpSC3QNTkNrvoUQAllccB1ZNBgGphqymnJzacnYjTLxBjQs2l8y4DaOx4LiK9CkyAmAJCV73qw5+24Jd8CzEr25x6WGzxKs/1HqipYzC1aq9+uoFexPQnHCb0uaBt0eAsA3CwF53i94v3pda4VrNsFsc1jIeO8ESkKbTd0JGOA2q9tTereE3k' \
			b'TSs/iWMEBP3r7zYDIr0Cr4AB1N/oYAeu9zTem+6Yxnx3+bX8XoY9sr3b0IeCt2nO4/216Lh2uVGrDtTdlZkaNkbufmm31iz5JZtuzxq2mzTcbFYySElculuqetRRe+1RrEXX7bX07VnlGG3WuO/9rVdS/KgXdX+LNW1Y8UhmpXv1h7EPAdfoIAVK/wbBAASB' \
			b'j45htBkEVPgugyASCLDGOhB4/EILHZ3HXSntTyMukA1IDnft9GIQEtER1/iOj15KAmtLO1bHIBqi59KgcDpZAsQsrzWh3My+b5s5pD4DX0IL1bLfueSg+77NcwdugPrz7PUsAjv6o1TpJTX629YhvhPzN6TDMc11fxXNhVvXXFBExIE0BwpZ6mbrqXm7GXnr' \
			b'r4RNqQW/J446CHwIAKMtJlD2/u88ae72Da+pr+rowTQIgl7qLWS6UZrXE2USo91+77GD8PYhOJSaeQhK/pO/x4tS295ybGM29mIqRJA4dq5gBnadgPc56Ff8veilxjHlaakFQlzKKoskNOQzyvcnm4aJqZryuW4ScJairSUWeI034C07k+ylpsN0026npisB' \
			b'0E9T07k8Phfboo8oe4HEXYNfFML3xvQzFfg+SN4VxPQSd0U/c5u+W3u5nRiKpuhL8WbwwY0HfKgZu2UzTo1+qA03bIN9YZMtwRCRD0+jvvxQe36sPfGtjbY64siCzVjx4al6mFdPuXP6NeLeMxiGPkEixdLBGNw8VP4+R26+7OMr/XpBPO3sxev00FM3yQBa' \
			b'gBsJlkGcM7SeKkkiiXtQBvkmrhaIhnYfNFh11UA0dD00rkOFwwWp41+e2DkQIeXp7+tQwr+hfcXAlOi1lOiamHYtPfx7GxOh9Zcym8tZgckyG0bxusFbktsP2I2DNaocBisBo8pHZcjLgKouJhpOoaTresyhPTiHuAA6RGD+3OH5s+oggfnzh+fPqYME5m/T' \
			b'PHoD/EV1kMD8xU38bb9C2IlL3HqsDTGue9qZDdWHgXltb2ZNtAPTRq0PfHpqY7EcYL+1RTHmvrt17r26jcB7jOburIct/ZOT2wssEM2uAaSnw59xm/M/TKGv7lt8L8VvjPBNh6P1l+AI3ZLQTPYlwKayo4M5/NThbwxp+qUhkPxq/n9Hh+Kn'

	_PARSER_TOP  = 'expr'

	_GREEK       = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\pi|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'

	_SPECIAL     = r'\\partial|\\infty'
	_CHAR        = fr'[a-zA-Z]'
	_ONEVAR      = fr'{_CHAR}|{_GREEK}'
	_ONEVARSP    = fr'{_CHAR}|{_GREEK}|{_SPECIAL}'
	_DIONEVARSP  = fr'(\d)|(oo)|({_ONEVARSP})'

	_FUNCPY      = '|'.join (ass.FUNCS_PY)
	_FUNCPYTEX   = '|'.join (ass.FUNCS_PY_AND_TEX)

	TOKENS       = OrderedDict ([ # order matters
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('TRIGH',         r'\\?(?:(a)(?:rc)?)?((?:sin|cos|tan|csc|sec|cot)h?)|\\operatorname\{(sech|csch)\}'),
		('FUNC',         fr'({_FUNCPY})|\\?({_FUNCPYTEX})|\\operatorname\{{({_CHAR}\w+)\}}|\$({_CHAR}\w+)|\?'),
		('SQRT',          r'\\?sqrt'),
		('LOG',           r'\\?log'),
		('LIM',           r'\\lim'),
		('SUM',           r'\\sum'),
		('INT',           r'\\int(?:\s*\\limits)?'),
		('LEFT',          r'\\left'),
		('RIGHT',         r'\\right'),
		('CDOT',          r'\\cdot'),
		('TO',            r'\\to'),
		('FRAC2',        fr'\\frac\s*(?:{_DIONEVARSP})\s*(?:{_DIONEVARSP})'),
		('FRAC1',        fr'\\frac\s*(?:{_DIONEVARSP})'),
		('FRAC',          r'\\frac'),
		('VAR',          fr'\b_|(oo)|(d|\\partial\s?)?({_ONEVAR})|{_SPECIAL}'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
		('SUB1',         fr'_(?:{_DIONEVARSP})'),
		('SUB',           r'_'),
		('CARET1',       fr'\^(?:{_DIONEVARSP})'),
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
		'abs'      : lambda expr: _expr_func (1, '|', expr.strip_paren ()),
		'factorial': lambda expr: _expr_func (1, '!', expr.strip_paren ()),
		'ln'       : lambda expr: _expr_func (1, 'log', expr),
	}

	def expr            (self, expr_int):                      	             return expr_int

	def expr_int_1      (self, INT, expr_sub, expr_super, expr_int):         return _expr_int (expr_int, (expr_sub, expr_super))
	def expr_int_2      (self, INT, expr_int):                               return _expr_int (expr_int)
	def expr_int_3      (self, expr_add):                                    return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_mul_exp):                return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2      (self, expr_add, MINUS, expr_mul_exp):               return AST.flatcat ('+', expr_add, expr_mul_exp.neg (True))
	def expr_add_3      (self, expr_mul_exp):                                return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_lim):                return AST.flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_2  (self, expr_mul_exp, STAR, expr_lim):                return AST.flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_3  (self, expr_lim):                                    return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_lim):                             return AST ('lim', expr_lim, expr_var, expr)
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_doublestar, PLUS, CURLYR, expr_lim):  return AST ('lim', expr_lim, expr_var, expr, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_doublestar, MINUS, CURLYR, expr_lim): return AST ('lim', expr_lim, expr_var, expr, '-')
	def expr_lim_6      (self, expr_sum):                                                                           return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, expr_super, expr_lim):             return AST ('sum', expr_lim, expr_var, expr, expr_super)
	def expr_sum_2      (self, expr_neg):                                                                           return expr_neg

	def expr_neg_1      (self, MINUS, expr_diff):                            return expr_diff.neg (True) # _ast_neg_stack (expr_diff.neg (True) if expr_diff.is_pos_num else AST ('-', expr_diff)
	def expr_neg_2      (self, expr_diff):                                   return expr_diff

	def expr_diff       (self, expr_div):                                    return _expr_diff (expr_div)

	def expr_div_1      (self, expr_div, DIVIDE, expr_mul_imp):              return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2      (self, expr_div, DIVIDE, MINUS, expr_mul_imp):       return AST ('/', expr_div, expr_mul_imp.neg (True))
	def expr_div_3      (self, expr_mul_imp):                                return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_func):                     return AST.flatcat ('*', expr_mul_imp, expr_func)
	def expr_mul_imp_2  (self, expr_func):                                   return expr_func

	def expr_func_1     (self, SQRT, expr_func):                             return _expr_func (1, 'sqrt', expr_func)
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_func):   return _expr_func (1, 'sqrt', expr_func, expr)
	def expr_func_3     (self, LOG, expr_func):                              return _expr_func (1, 'log', expr_func)
	def expr_func_4     (self, LOG, expr_sub, expr_func):                    return _expr_func (1, 'log', expr_func, expr_sub)
	def expr_func_5     (self, TRIGH, expr_func):                            return _expr_func (2, 'func', f'{"a" if TRIGH.grp [0] else ""}{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func)
	def expr_func_6     (self, TRIGH, expr_super, expr_func):
		return \
				AST ('^', _expr_func (2, 'func', f'{TRIGH.grp [0] or ""}{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func), expr_super) \
				if expr_super != AST.NegOne else \
				_expr_func (2, 'func', TRIGH.grp [1] or TRIGH.grp [2], expr_func) \
				if TRIGH.grp [0] else \
				_expr_func (2, 'func', f'a{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func)

	def expr_func_7     (self, FUNC, expr_func):
		name = FUNC.grp [0] or FUNC.grp [1] or FUNC.grp [2] or FUNC.grp [3] or FUNC.text
		func = self._FUNC_AST_REMAP.get (name)

		return func (expr_func) if func else _expr_func (2, 'func', name, expr_func)

	def expr_func_8     (self, expr_fact):                                   return expr_fact

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

	def var             (self, VAR):                                         return f'\\partial {VAR.grp [2]}' if VAR.grp [1] and VAR.grp [1] [0] == '\\' else '\\infty' if VAR.grp [0] else VAR.text
	def subvar_1        (self, SUB, CURLYL, expr_var, CURLYR):               return f'_{{{expr_var [1]}}}'
	def subvar_2        (self, SUB, CURLYL, NUM, CURLYR):                    return f'_{{{NUM.text}}}'
	def subvar_3        (self, SUB, CURLYL, NUM, subvar, CURLYR):            return f'_{{{NUM.text}{subvar}}}'
	def subvar_4        (self, SUB1):                                        return SUB1.text

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
		'CARET1': 'CARET',
		'SUB1'  : 'SUB',
		'FRAC2' : 'FRAC',
		'FRAC1' : 'FRAC',
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

		if self.autocompleting:
			stack = [s [2]]

			while stack:
				ast = stack.pop ()

				if ast.is_var:
					expr_vars.add (ast.var)
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
			self.tokens.insert (self.tokidx, lalr1.Token ('VAR', '', self.tok.pos, (None, None, '')))
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

		## DEBUG!
		rated = list (rated)
		print ()
		for res in rated:
			print ('parse:', res [-1])
		## DEBUG!

		return next (iter (rated)) [-1]

if __name__ == '__main__':
	p = Parser ()
	# print (p.parse ('1') [0])
	# print (p.parse ('x') [0])
	# print (p.parse ('x!') [0])
	# print (p.parse ('|x|') [0])
	# print (p.parse ('x/y') [0])
	# print (p.parse ('x/(y/z)') [0])
	# print (p.parse ('sin x') [0])
	# print (p.parse ('sin x**2') [0])
	# print (p.parse ('sin (x**2)') [0])
	# print (p.parse ('sin (x)**2') [0])
	# print (p.parse ('x') [0])
	# print (p.parse ('-x') [0])
	# print (p.parse ('-{-x}') [0])
	# print (p.parse ('\\int dx') [0])
	# print (p.parse ('\\int dx/2') [0])
	# print (p.parse ('\\int 2 dx') [0])
	# print (p.parse ('\\int 3 / 2 dx') [0])
	# print (p.parse ('\\int x + y dx') [0])
	# print (p.parse ('\\int_0^1 dx') [0])
	# print (p.parse ('\\int_0^1 dx/2') [0])
	# print (p.parse ('\\int_0^1 2 dx') [0])
	# print (p.parse ('\\int_0^1 3 / 2 dx') [0])
	# print (p.parse ('\\int_0^1 x + y dx') [0])
	# print (p.parse ('dx') [0])
	# print (p.parse ('d / dx x') [0])
	# print (p.parse ('d**2 / dx**2 x') [0])
	# print (p.parse ('d**2 / dx dy x') [0])
	# print (p.parse ('\\frac{d}{dx} x') [0])
	# print (p.parse ('\\frac{d**2}{dx**2} x') [0])
	# print (p.parse ('\\frac{d**2}{dxdy} x') [0])
	a = p.parse ('\\int_0^1x') [0]
	print (a)