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
# ('func', 'func', expr)       - SymPy or regular python function 'func', will be called with SymPy expression
# ('trigh', 'func', expr)      - trigonometric or hyperbolic function or inverse: 'sin', 'asin', 'acsch'
# ('log', expr)                - natural logarithm of expr
# ('log', expr, base)          - logarithm of expr in base
# ('sqrt', expr)               - square root of expr
# ('sqrt', expr, n)            - nth root of expr, n is ('#', int)
# ('*', expr1, expr2, ...)     - multiplication
# ('diff', expr, var1, ...)    - differentiation of expr with respect to var1 and optional other vars
# ('-', expr)                  - negative of expression, negative numbers are represented with this at least initially
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
# ) Explicit multiplication and addition have higher precedence than integration, so they are included in the expression to be integrated,
#   but lower precedence than limits or sums, so they end those expressions.
#
# ) Differentiation and partially integration are dynamically extracted from the tree being built so they have
#   no specific full grammar rules.
#
# ) Parsed negative numbers are always initiallly represented as ('-', ('#', positive))

from collections import OrderedDict
import re

import lalr1
import aststuff as ass

def _ast_from_tok_digit_or_var (tok, i = 0): # special-cased infinity 'oo' is super-special
	return ('#', int (tok.grp [i])) if tok.grp [i] else ('@', '\\infty' if tok.grp [i + 1] else tok.grp [i + 2])

def _expr_int (ast): # construct indefinite integral ast
	if ass.is_var_differential (ast) or ast == ('@', ''): # ('@', '') is for autocomplete
		return ('int', ast)

	elif ast [0] == '/':
		if ass.is_var_differential (ast [1]):
			return ('int', ('/', ('#', 1), ast [2]), ast [1])
		elif ast [2] [0] == '*' and ass.is_var_differential (ast [2] [-1]):
			return ('int', ('/', ast [1], ast [2] [1] if len (ast [2]) == 3 else ast [2] [:-1]), ast [2] [-1])

	elif ast [0] == '*' and (ass.is_var_differential (ast [-1]) or ast [-1] == ('@', '')): # ('@', '') is for autocomplete
		return ('int', ast [1] if len (ast) == 3 else ast [:-1], ast [-1])

	elif ast [0] == '+' and ast [-1] [0] == '*' and ass.is_var_differential (ast [-1] [-1]):
		return ('int', \
				ast [:-1] + (ast [-1] [:-1],) \
				if len (ast [-1]) > 3 else \
				ast [:-1] + (ast [-1] [1],) \
				, ast [-1] [-1])

	raise SyntaxError ('integration expecting a differential')

_rec_var_d_or_partial = re.compile (r'^(?:d|\\partial)$')

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast [1] [0] == '@' and _rec_var_d_or_partial.match (ast [1] [1]):
			p = 1
			v = ast [1] [1]

		elif ast [1] [0] == '^' and ast [1] [1] [0] == '@' and _rec_var_d_or_partial.match (ast [1] [1] [1]) and \
				ast [1] [2] [0] == '#' and ast [1] [2] [1] > 0 and isinstance (ast [1] [2] [1], int):
			p = ast [1] [2] [1]
			v = ast [1] [1] [1]

		else:
			return None

		_ast_dv_check = ass.is_var_differential if v [0] == 'd' else ass.is_var_partial # make sure all are same type of differential, single or partial

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

			return tail if end == 1 else ass.flatcat ('*', ast [1], tail) if end == 2 else ass.flatcat ('*', ast [:end], tail)

	return ast

def _expr_func (iparm, *args): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
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
			b'eJztXftvGzcS/mcOiARQgPje7W95uD3j0iR1kwIHQQiSJj0EaNIgj94BRf/3m5lvuFytd2XJkWW7DURryVk+hjPfDjkkV56t7pw+enrH3Hl4+j19//iMv78/ffTsR079cCa3Hn9H30/PTr/7J12/ffboPhNPvuV79+6e0feTu2cnjx5S5PS7R4/PTp7ff3b2' \
			b'8N+c9+zufb1YvTq6ym3O/kia+0nq+Mfrd6/Kva5OjtyjUv86ecpRZoFbffD42b2HJz8+lYL3KeNT4f0evrmpJw+lB/cfPJZbvZzCyN37Tx+fnd5lHh6c/nT64KS2w7QnZ6ffn3D5p4/p6+SHZ3cfcurnFx9ef3r+24fnr377/PLX1x8/vfhA1I+fX/4ukdf/' \
			b'e//h+cfP71/3Ei8p2rv77vPbEv30+kMXf08VvyuJFy8/dvTf/luiv3x48XMXf/Hzpy7++V1Hf/v51+dv3r4vyVdvfq/RX37peHj9n8pfx0KPyV/fvO3XSJGOtVevSvTNu8LCnbVZzRYuGOfnBpHAEWsWTq7JzBrTGiI4Z9p5oQmlSy5s5piXP5fNIsxr2tfk' \
			b'QurmskspucSXd0Sx8wHJ94kc5ZjHl9cbnCdKLJiZ5Woa/pt3JN9P2qARpnHMmRkn3FxTVGGley+9tv0MszhMDe6nQcpx/WFA9MsNQu5SlFiiShL2YoOm8YUwGKlnxkVjiQGqjpkylsQa51N3RbN5h0x+I89C9BrkzzWFrum2phdQgsVX1zlEKdaYGUkTeGk4' \
			b'wndbY5NEMvGyFGEv54XQGCW5PpVqtNrbQluoViO+SHJzTS9QPYlz5qLk06QTOlXnehJIRYgsevSLKhecEGXmfNUSkgNCqC0QdoFv6vYmu9T3VCJWpJC4AOGditMj2KMsuIkw38gzuK9JSkmzXvqJ7miDlWbHaZyqdAiGKqfnmQzDitpkNRNevTXZsCEgOfls' \
			b'fCNPKHPI2InORG+CNcGx2lhLFKG7rQlL0h8/RaxIz88Dte0Sg5EAxQ9lNKExgXKaaJIJwQSiUCQLz/TdsFpiY2Jr0tIka5IzyZsUTKKc3uTlmp8RNhCev1cz4llSQoxLE+0t6cZqRhwy61m+qQjrYabdSbhkpQbJek3y9g1ETfITpjwuQXmLcvvWoCeqhKNc' \
			b'IvoU0afg0FMLiFkoiFmUnlrtudRwFGbDUlEOhpw7VsvUpHa+qNmh8y5cwAKewUMyAk05PBIuH0/4WYXfHE/qFp0N0mSkyuiZSSZmZqcFOwE5Ynn8btXTl7QP4VZxHZRtK9eLcltVlM075RZVz5I+6QmPXYJdSnjoEnSeRNcpmZRNakxqmTXkyMVQtMYNgUMS' \
			b'dnwvSp69bKVFrZkruKHKWdHQeZO5I8aYvZvGVb55XPEsx+lEw2Gi4TDRcHMGo+iZR2zJZCUzD87ckSPOhuQJ4xFZ2HBo/7ZYMhvAvVfuJXmUlrlWaVKeh/1mAPl4XAJkoVGTCcMb4/FmADHtbaVzmRjcIiSueAZzi/idRQAjABgh3SbmZebidpiLZPQuwbYm' \
			b'sRIb840Vz0wcpiRO5p8J8/IENzbBj52ltpuP+PktkRJPkBymO37EB29GqJz0SHoduTxGLo+Riy6DxtBSg/zRTeSQ8c0f1dlc8VjqjzqWOojLBUjDiTCP0zJ0HPVxjvFoI0xMMCTSPtUgbCChNEDK4pIAg+QgooTSKeMiw9QYwOiJCwrIAEAGADLIVMrhrtW7' \
			b'R8SYkyaPo+MkvYsqXUlwRZAxX1JSqQINSZ7Kgb0jCUZIMEKC8TbZ/ehuE7+Mjii6itBVhJICIB+gowLsBLUkqIUuxB7AnZAxasZ80zydFfOdwTcvv8/g9OvqYxSOBz68Mw2626BYozmbG9m39gZyFW4eV6zAVpfUl7qmvpTJxtLIjkwrjLXCBngQBvhpdtqL' \
			b'7lGmvlTMNKXFqPYsL00mXFG7BLlkMtkBAlFrWmtaYoKEk03LO3HU3pIksWSZUPMiGGKPe8Xd4n7xAhevSPMSMS9Ju0Qs8y6ZN4vYYlcz8HZdpGvL1CRbaC02bUkci8S3iJZ5d2spd2VbjP54Y49yBd6DzEar5d2/xBVRriRVUhd5E3PBe9CRtyWT4V3MwJtz' \
			b'FKXuLxLvrDKZ6QkV8ZYfZQm8dcbZuN5mzePt/hKnDnSKv07p0x/d4x0Nnp16sherxvBnTBusANNMaqPRD2ulmdSK5hlopbmMVtDYmFYKL2sxjX8l7bCdkTCmICYn+Z5QUVea80hbk3qq+Qaqkrb31lVpc1RbPbbWsj8rGmP7mFVvlq0rjKcayf01SYKKVk33' \
			b'iEr9Nq1mgiih2prGiYbThUrO+yuaxwfelOYdad4xrYqnP7rHk+3AI1LCuMFnZIiegAU+nRH59AyrjE9FcHx5DiMsdf6aQEjSz4IGt4ZK+VaAkkZx0nqBipYY4IQofDSCqqCYzwCNtTsBx26CR6ofhw6LJ+BYCrXiCi+RU8SLD2uZFAqgkoKpN8qODNVbwOQ2' \
			b'LcN5MGXB03I3SDUFSVnAtCx48tsg1Xyp/WhMFxg2fOGt4kaAovQg4umsith9O234F9Gafr2cRXFj60AgTURcAB+rlqYrNLQ0fH8pwNEMvIXcdOiR+6MAKtl79kcp4/anhrX41F/honBxmM1KYLjwBTNcOSKFGMGFLwoXjiYQpuHSr5ezKlykFOAiTURcABdh' \
			b'IfcKDeAi9wEXzcAqWnZwkfujcCnZK1wKZRQuPc4ZLukrXDq4yFFIBIGLBVws4AI6w8VWuFiBi90Ol83QwcVWuFjAxVa4WMClKzSEi61wQQZWka1wsZNw0ew9uChlHC6V87Uc2voKlwIXb7ogcMGURWYZttAZLr7CRVxCt8UnjNb06+WsBS7VV9SJjFwULpjL' \
			b'1EJDuPgKFy0fcFG4+Em4aPYeXJQyDpfK+VpO932FS4FLMl0QuCTAJQEuoDNcUoWLTHfd9HxX4JI2QgeXOumVJiIuCpcEuHSFhnBJFS7IwCpKFS5pEi6avQcXpYzDpXLOcGkZLk69p7TFf5qCUNqKouUQSONO1TSWiONROI04WLtCK4zAy+4BsW2eFmsLLyt4' \
			b'y/6WxBq5jPhc8lIDLizWDAIuxf0S+S7wPYVJr7jMNbA/5qo/JqUVmxnYzBWbGdiU0GrzA3hmwPOch6at4UWADqx52sVvuyIALMtZQKvUcdBmcdZq73r+mvnDpm/Ye234wkrOdHV/zuX8/x7GcDuS/wr2sDVdEHvYAn5YGFI6w6+t8EMqgbbFJLYboYNdW2HX' \
			b'AnZthV0L2HWFhphrq0lEyuH9kIKydtIkavaeSVTKOLoq52ucxf46hCpkeCevBIaMhz/n4c8pnSDjqz/nxZ/z2/25fr2++nO++nMe/pyv/pyHP1cLDVfqqz+nGXi3v/pzftKfK9l7C/hKGcVLj/M1zgUeBi92V8iMbvTcMOBY0wUBDjw7D89O6Qyc6tl58ez8' \
			b'tGcnVfXq1VoKdqpz5+Hc6f0CH+Ul94oOEVRdvFI24KIImnTxSvYegpQyjqDKvyDIf0XQeQR50wVBEJw9D2dP6Yyg6ux57P9NO3tSlTX9qn3193z19zz8Pb1fEKS85F7RIYKq11fK4p3PgqBJr69k7yFIKeMIqvyv8e7MVwSdQ1AwXRAEBSAoAEGgM4JCRVAQ' \
			b'BIVpBAUgKGyEDkGhIigAQbhfEKS85F7RIYJCRZCW1YsiaHIXpGTvIUgp4wiq/AuCLreKLXa3f9RhC5RCeWXrMoCyPUzFa4UVNSQfhhRm0JhAI5VNnT3LzLll9jF7HodUK4gqtTbkyERTp9B1Bo0JtNRS9tMMptAdRz0s2aUXPNVJNEoGU2fQkxNoZK1AQnoU' \
			b'Rtr2GucILwOhnfFzAORcEjb+UBYpmy6IRcICgMcCgNIDLsUiifevtyzSY3Ypwy7ljdDZper+e7j/er/YJeVoUHpomnI1TVo84KKmadLtt7a22DNPShk3T5URwdbllsGvBVte4BWvB2GN6YIgDPu1Hvu1Sg8ihA5hsl+rtyzSYwhrgLBmI3QIqxu3Hhu3er8g' \
			b'TDnKm6WHCMMOrsfxnpqNcVb3cf3kPm6vRA9mShmHWQ0Cs8asnJ4kufgcSTOx5JkLls6dAtpAy95nRMrKZR8gE8CQVcr+yiT/UArWJBcKjV1PgCy2rIaL+199sKnDQUM9X/6kh6wTbZ72mNAsLxgOznVQLw6iXRLKoRTctjvoOIgBHdc13edTDnxSotO7l0Mu' \
			b'R9R/E64WAlZ+cmc7DIpIRuBQTaXtoFHW7wcQoR5cqQGgnh/WBrjbZAfa8yb/YKbAytGSfcwB9e86jX3zd7f3PNu5cptPGW/KiE7OW/o76nmoY2y3uivQtf9SXeOFDPYNdtT46E70gR7roCq3B1E7q2m71jmHbiVfSvmjG8SHndhZ2Y1swOqm/s0fLnxD2P4T' \
			b'r3leDAT798RCxCoVK+0COISbDwfZbGzA6hY4RH5pSN4bYFdVXMLMko4kPV4LkIVJiuQoPecFxrjGL0Gt/FgZx7ggnUtuUr2cpaEurb5ooLkqv3HHseXc+wR9kDEoDjvGHNVv3G1Msfh5Tn03YDi6NGZ1e5V7XqHxurXJK2/xCrU5psP2r6XDdO06TEaYOKIO' \
			b'yTyt9N28XYbw3UbuPV/Dm1KQ5eFY37RLOBqTLpQ7R3mQ3Xdw3f+tuqmXouLGcElziSLgrdK9UK6HEKoKVDqwG4r3EuOBRMinENtvSOsiPwf57WxXdjEqBzQkRaT2cq7hvtPAA5uENd5iX1kS+irCItB0X2doIqvNvmYwzgIShgZVxa5sEXUVZxyKLWGCuNHB' \
			b'bo8rnas7bal7yOb2uvNm3fID63JOEedpW9636raldNuIX9/jtWr5gRFeb9IViLYsGa/lh5nL+87n68m5V5WTnyrY+LD7Qlepxu9YTTCjH6kjbNaB/bnJmuhx0Q8G3Nj/SH1xrD7d7xutdWRDjXL0PhjUN2nDYXkuv59ddyvlZULdpPTKipdDSOx6DPYgg+w7' \
			b'YtMR2439vcasxwOws8jbin5z73CyG2wRripEoLlP42nVeGYRTz6AYmQR6XJBeGgOwYM3lw3CQ1th8iVc8D8hkN8DCZcIwkj/pPyXcIJfgL9kACd2Kyd2yEyzlZ9ktoTmPJGfoyEVbLkLnujRB1mf4j67G0/uhU9tNl3QSUKZIfRv9UM3QxiUtXVqwCmeGQzL' \
			b'oqP+WjrammMF9DJc1Mu9TPO+3eXp4NZAHskonRrQSLighnMB/Y7XoV35BzDHCejlRcPv1fQymmMF9DJfSy8bc6yAXjZXNpXaq9/stW0NOAt2YbZ+YN9tt6wQRXtDRBHN9QX4LMubNr/28s9+rjtAOBabFsxVy7/pN8e/D2IzzC6KLFKRU5mlD7jrpQfd/kYO' \
			b'cFTxSjm77ityGeXnpNj5nP8f+6N6hA=='

	_PARSER_TOP = 'expr'

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
		('TRIGH',         r'\\?(a(?:rc)?)?((?:sin|cos|tan|csc|sec|cot)h?)|\\operatorname\{(sech|csch)\}'),
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
		('NUM',           r'(\d+\.\d*|\.\d+)|(\d+)'),
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
		'abs'      : lambda expr: _expr_func (1, '|', ass.strip_paren (expr)),
		'factorial': lambda expr: _expr_func (1, '!', ass.strip_paren (expr)),
		'ln'       : lambda expr: _expr_func (1, 'log', expr),
	}

	def expr            (self, expr_int):                      	             return expr_int

	def expr_int_1      (self, INT, expr_sub, expr_super, expr_int):         return _expr_int (expr_int) + (expr_sub, expr_super)
	def expr_int_2      (self, INT, expr_int):                               return _expr_int (expr_int)
	def expr_int_3      (self, expr_add):                                    return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_mul_exp):                return ass.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2      (self, expr_add, MINUS, expr_mul_exp):               return ass.flatcat ('+', expr_add, ass.neg (expr_mul_exp))
	def expr_add_3      (self, expr_mul_exp):                                return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_lim):                return ass.flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_2  (self, expr_mul_exp, STAR, expr_lim):                return ass.flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_3  (self, expr_lim):                                    return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_lim):                             return ('lim', expr_lim, expr_var, expr)
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_doublestar, PLUS, CURLYR, expr_lim):  return ('lim', expr_lim, expr_var, expr, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_doublestar, MINUS, CURLYR, expr_lim): return ('lim', expr_lim, expr_var, expr, '-')
	def expr_lim_6      (self, expr_sum):                                                                           return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, expr_super, expr_lim):             return ('sum', expr_lim, expr_var, expr, expr_super)
	def expr_sum_2      (self, expr_neg):                                                                           return expr_neg

	def expr_neg_1      (self, MINUS, expr_diff):                            return ass.neg (expr_diff)
	def expr_neg_2      (self, expr_diff):                                   return expr_diff

	def expr_diff       (self, expr_div):                                    return _expr_diff (expr_div)

	def expr_div_1      (self, expr_div, DIVIDE, expr_mul_imp):              return ('/', expr_div, expr_mul_imp)
	def expr_div_2      (self, expr_div, DIVIDE, MINUS, expr_mul_imp):       return ('/', expr_div, ass.neg (expr_mul_imp))
	def expr_div_3      (self, expr_mul_imp):                                return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_func):                     return ass.flatcat ('*', expr_mul_imp, expr_func)
	def expr_mul_imp_2  (self, expr_func):                                   return expr_func

	def expr_func_1     (self, SQRT, expr_func):                             return _expr_func (1, 'sqrt', expr_func)
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_func):   return _expr_func (1, 'sqrt', expr_func, expr)
	def expr_func_3     (self, LOG, expr_func):                              return _expr_func (1, 'log', expr_func)
	def expr_func_4     (self, LOG, expr_sub, expr_func):                    return _expr_func (1, 'log', expr_func, expr_sub)
	def expr_func_5     (self, TRIGH, expr_func):                            return _expr_func (2, 'trigh', f'{"a" if TRIGH.grp [0] else ""}{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func)
	def expr_func_6     (self, TRIGH, CARET, expr_frac, expr_func):
		return \
				('^', _expr_func (2, 'trigh', TRIGH.grp [1] or TRIGH.grp [2], expr_func), expr_frac) \
				if expr_frac != ('-', ('#', 1)) else \
				_expr_func (2, 'trigh', TRIGH.grp [1] or TRIGH.grp [2], expr_func) \
				if TRIGH.grp [0] else \
				_expr_func (2, 'trigh', 'a' + (TRIGH.grp [1] or TRIGH.grp [2]), expr_func)

	def expr_func_7     (self, TRIGH, CARET1, expr_func):
		return \
				('^', _expr_func (2, 'trigh', f'a{TRIGH.grp [1] or TRIGH.grp [2]}' if TRIGH.grp [0] else TRIGH.grp [1] or TRIGH.grp [2], expr_func), \
				_ast_from_tok_digit_or_var (CARET1))

	def expr_func_8     (self, FUNC, expr_func):
		name = FUNC.grp [0] or FUNC.grp [1] or FUNC.grp [2] or FUNC.grp [3] or FUNC.text
		func = self._FUNC_AST_REMAP.get (name)

		return func (expr_func) if func else  _expr_func (2, 'func', name, expr_func)

	def expr_func_10    (self, expr_fact):                                   return expr_fact

	def expr_fact_1     (self, expr_fact, FACTORIAL):                        return ('!', expr_fact)
	def expr_fact_2     (self, expr_pow):                                    return expr_pow

	def expr_pow_1      (self, expr_pow, expr_super):                        return ('^', expr_pow, expr_super)
	def expr_pow_2      (self, expr_abs):                                    return expr_abs

	def expr_abs_1      (self, LEFT, BAR1, expr, RIGHT, BAR2):               return ('|', expr)
	def expr_abs_2      (self, BAR1, expr, BAR2):                            return ('|', expr)
	def expr_abs_3      (self, expr_paren):                                  return expr_paren

	def expr_paren_1    (self, PARENL, expr, PARENR):                        return ('(', expr)
	def expr_paren_2    (self, LEFT, PARENL, expr, RIGHT, PARENR):           return ('(', expr)
	def expr_paren_3    (self, IGNORE_CURLY, CURLYL, expr, CURLYR):          return expr
	def expr_paren_4    (self, expr_frac):                                   return expr_frac

	def expr_frac_1     (self, FRAC, expr_term1, expr_term2):                return ('/', expr_term1, expr_term2)
	def expr_frac_2     (self, FRAC1, expr_term):                            return ('/', _ast_from_tok_digit_or_var (FRAC1), expr_term)
	def expr_frac_3     (self, FRAC2):                                       return ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4     (self, expr_term):                                   return expr_term

	def expr_term_1     (self, CURLYL, expr, CURLYR):                        return expr
	def expr_term_2     (self, expr_var):                                    return expr_var
	def expr_term_3     (self, expr_num):                                    return expr_num

	def expr_num        (self, NUM):                                         return ('#', float (NUM.grp [0]), NUM.text) if NUM.grp [0] else ('#', int (NUM.grp [1]))

	def expr_var_1      (self, var, PRIMES, subvar):                         return ('@', f'{var}{subvar}{PRIMES.text}')
	def expr_var_2      (self, var, subvar, PRIMES):                         return ('@', f'{var}{subvar}{PRIMES.text}')
	def expr_var_3      (self, var, PRIMES):                                 return ('@', f'{var}{PRIMES.text}')
	def expr_var_4      (self, var, subvar):                                 return ('@', f'{var}{subvar}')
	def expr_var_5      (self, var):                                         return ('@', var)

	def var             (self, VAR):                                         return f'\\partial {VAR.grp [2]}' if VAR.grp [1] and VAR.grp [1] [0] == '\\' else '\\infty' if VAR.grp [0] else VAR.text
	def subvar_1        (self, SUB, CURLYL, expr_var, CURLYR):               return f'_{{{expr_var [1]}}}'
	def subvar_2        (self, SUB, CURLYL, NUM, CURLYR):                    return f'_{{{NUM.text}}}'
	def subvar_3        (self, SUB, CURLYL, NUM, subvar, CURLYR):            return f'_{{{NUM.text}{subvar}}}'
	def subvar_4        (self, SUB1):                                        return SUB1.text

	def expr_sub_1      (self, SUB, expr_frac):                              return expr_frac
	def expr_sub_2      (self, SUB1):                                        return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1    (self, DOUBLESTAR, expr_func):                       return expr_func
	def expr_super_2    (self, DOUBLESTAR, MINUS, expr_func):                return ass.neg (expr_func)
	def expr_super_3    (self, CARET, expr_frac):                            return expr_frac
	def expr_super_4    (self, CARET1):                                      return _ast_from_tok_digit_or_var (CARET1)

	def caret_or_doublestar_1 (self, DOUBLESTAR):                            return '**'
	def caret_or_doublestar_2 (self, CARET):                                 return '^'

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

		# rated = list (rated)
		# for i in rated: print (i)

		return next (iter (rated)) [-1]

# if __name__ == '__main__':
# 	p = Parser ()
# 	a = p.parse ('dx')
# 	print (a)
