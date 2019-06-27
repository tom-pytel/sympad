# TODO: redo _expr_diff d or \partial handling
# TODO: iterated integrals

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

def _expr_int (ast, from_to = ()): # construct indefinite integral ast
	if ast.is_diff_var or ast.is_null_var: # null_var is for autocomplete
		return AST ('intg', None, ast, *from_to)

	elif ast.is_div:
		if ast.numer.is_diff_var:
			return AST ('intg', ('/', ast.One, ast.denom), ast.numer, *from_to)
		elif ast.denom.is_mul and ast.denom.muls [-1].is_diff_var:
			return AST ('intg', ('/', ast.numer, ast.denom.muls [0] if len (ast.denom.muls) == 2 else AST ('*', ast.denom.muls [:-1])), ast.denom.muls [-1], *from_to)

	elif ast.is_mul and (ast.muls [-1].is_diff_var or ast.muls [-1].is_null_var): # null_var is for autocomplete
		return AST ('intg', ast.muls [0] if len (ast.muls) == 2 else AST ('*', ast.muls [:-1]), ast.muls [-1], *from_to)

	elif ast.is_add and ast.adds [-1].is_mul and ast.adds [-1].muls [-1].is_diff_var:
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
			b'eJztnWmP20YShv/MAh4BLYB9k/7mY5IdrGM7k3GAhSAYPhcGYsfwkV0g2P++VfU2yWaLOkejkbKDoUWy2Ud11cPqU/LZ7N7F06t76t6Ti5/o85cX/PnTxdMXv/Ddz5fy6NmP9Hl1efHj3+n8w4unjzjw/Ad+9vDBJX0+f3B5/vQJXVz8+PTZ5fnLRy8un/yT' \
			b'414+eJROOp0NneUxR38qxf0qefzt3ae37bMuT754SKn+cX7FlywCl/r42YuHT85/uZKEjyjilcj+EJ9c1PMnUoNHj5/JoyymCPLg0dWzy4sHLMPji18vHp/35XDY88uLn845/dUz+jj/+cWDJ3z35tWXd99e/v7l5dvfv7/+7d3Xb6++UOjX76//kIt3//n8' \
			b'5eXX75/fdTfvv3968/LTu3/1D1/TZRb70/eP7eW3d1+66/dfXr1prz9ToZ/am1evv3bhv/+7i/7qzbe8yPb64/ffXn74+Lm9ffvhj/7y/ftOhly+ToRMyN8+fMxzpItOnLdv28sPn1oR7s3V7GxqvDJ2onDh+EKrqZGzV2e1ahQFGKOaSRsmId3tVAe+svLP' \
			b'RDV1k/7e9rdTyZvTVpKywoc1FKInRZDNA/mSryw+bHrAcSBvVGeas6n536QLsvltF5XD+MqoM0cVNZP+zlqpqx4E+4W74fOwcGcHITG/I6lF1Xxl0tWZlRu5U2dVKoAzycPS9VTSkxFITq9Y/UFZNoLSpFo/WfZUrBs3iGQHcaaRz07+mboNT/dNf08XXEGN' \
			b'j7Y66ZKuaqklmKn5gp82CujoQLJUovpq0gbUKgWZPJRy1Km2bRjZVK4cPkhzk3RPdIrSSCrjJV66NVIsIWIyDYRWiax61ItMJ6xQyJnJrITbIsD1JdAzME7VHopLdQ/thRYtBE5AzLPkeFVSCN1S6GQQp3iebulOinVST1QnFdiH6fEwvuvDoRjKnGpCzmFG' \
			b'ZVJV6I3jdzIqdgY2Klsr2/DLQkITOKQ5b5V3yhnlLJuNrWQUvX+uUo6tyu8UG5IchGOVmyAwOhbCNcpTNOVVUI5u6TMqV4vAFKdmm/hGhUoFrYJRwargVKDoFNOpqOf8grCHsPw5O7PpTvPJa+XNKdSB5DYid5RPSsIWIF8rdUGgbUOdRL0NTdsmKdlCIoeT' \
			b'T4J5eXwa0ITESZCTR4U8KuQSSxpxtMbJpGpqRHby9OYldRrSGEhj5JbcMXngA3BpwKWxfal4qw5RNszB7qor2ytP8ETl64NIEA6rbLzpnCNI8yBN3qus6kSFr0BFIja0r+AJvYGpAicksoN9OJX4B6nCukQ6OU0dN4oteZ+F9NIHvH4BLifA2gFYBCk+RBVq' \
			b'FRoVK5YQMaLuWkNTkkNaNvzMS5xtqu8Nco2cwTEaaEYt59GKZqG2oxKpPjKRuG9jUg/DoIdh0MMwEwawkVtvEUkLydww0+lgEsorxa2xyGBEhtNwXyb5LdMcpudikjGN2OtArSj3GlCqP2Cp5E7hlH04iG6pvLi1+0bTwpKgk2HQtzDoR5wKxjPu7ZyKsGce' \
			b'WvZJy/FkJJfujdmgwxJRtSAvO3dRTNEpmXH3xaDfYqSXGtCPCqmv00jn9SxWXafFTk5BRdyFMugQ2ZFxej0SyrcWtza1cxbtnEU7R6eiMJTUIL63S2JIa2gPNyydcbNrD9fsGtTOoAdgoDYj+mLXix6tAHsAs0e81NB3gAy4SScYWeNRMDhZmDAgdahxkgqN' \
			b'mZxeAJcQcUDEAREnXSGLp2QFd0irU/7ucG25hwZRdc4ByuVTiEmdeM2CvCCF3yHVeajOQ3X+ZJyvtycjLDPhxUoeVvIwjwPlDtZpWQ4wSIBB6ESygeeAiD5FjEc1Mpmx0BFC8/T4GSYF04jYi7jFONuqGnWtkaxOMevjq1hzbCL5IxOJ7dakKe8qzXlX0spX' \
			b'ShZKGpaqF0BKJy9psaDZ1gKvL+rCtEQpNysODixqFYkoKppgiyrWqiaFVKrRqjGqodLoltwBF0qKqEgTFalF9MJnqhdXjGvGs088c8zTxjyXawIJzctXVk0DryPxmqhXU19JiKzZyvIUVlRJIVMSa0pqmEZeI5RovBjIq5i87OX5mpfP6JoUnbLmpVaq1DTw' \
			b'KqKk8by4lhbYeEHO8z+KRScn68gUmbIMHJULjMiIl0M5Z37MebJMzZwb1+31TuhQPUDA7dqA/tEzhogXIGwkm1D+ql6wCYfwxwqb1OmPbVOvtE2KV9im3sU2KHDMNq08c/GOfy0bscuRozSTBMnnCkN1qTmeQaIV1urjFgbjoO0t1pY7arNMtLmspYrd2GNG' \
			b'WI/9rU3uNHebpeNdbVszMC8JhaWkgZ3rzBVvYPBIwBHD9BoYVVu2fx03QKDiHQbNdijw9BlPnfESMy/X9mjQP3rGq6OO+51BSbvB210oLIAW3mLgWfPsHXlzA3taLR2G9siJ4lT8scoZk+pC+puSbmv2E5WgFTqyPFb56dQsIpbSFnyxoJQ7738gselkk4vg' \
			b'HR0bQqdRcmJPShknj/XnsP2ECrKtSITElMOtn0vPUngMicU98VfCF3blT5gj7Q+wc3skb+iEatUdTBafeI04D85dkzQhenUbwijlGegeJY02RQMnObk2SumxurSlx6qBlG86AYcYSYRRktqSkhNLqcedWC/9XEbkd9D00DSqOwSaBtDkwTk0DbYRrYemGebR' \
			b'QtMAmgbQNGmnEXaXFdB0aUtomh6aJGABTbMUmlRSgialHoemPxiacAdNDw1XuT0YGj6lwVYXnEEjsRBpNTR5BhId0Eh2NU5GpU1wKbyApk9bQCNxAU2b4xAaiTAKTVsSoGlTj0KTST+XTVt30PTQyB5aHAKNBjR5cA6NFmj0emiKPFpoNKDRgEYDGkQpoenS' \
			b'ltDoHpokYAGNXgpNKilBk1KPQ9NLP5c9fnfQ9NB41R0CjQc0eXAOjexylUhroPHDPFpoPKDxgMYDGkQpoenSltD4HpokYAHN0t5xW1KCJqUeh6aXnqFpGBqThmZh28GZX8dStcEQbQOieP59s4HaxoD5AjK9BWirhmpsaavk0/CATa5wGhm0cTBjGfpjMGaL' \
			b'SIh4K8i0ic48H2dwSoRiBCcnPEieICwSKqENIpeQLhvLtcIXyIalAzpbdcUH0bWgm3IZRzfIgK6vYTamU3/qcJ+HwHW8z8NKMi6dzX8n8l2ATR3jWp7/Gr6xVt0hvhHjvUFwDmGKiHhr3GM9zKaFD0O+NINgMORLASV8XdqSvH7I12ZVsLZ0yNeWlNxjSj3O' \
			b'WC/9HDu17xrVHpxGdYeAgzHfIDhvVGXMZ9aP+fIMTD/mMxjzGYz5DMZ8KUpJTZe2pKYf87UCFtQsHfO1JSVqUupxavpjjv2D+6FGbw+OOVJ2eM25PZgdi178IDhfOpJevF3di0+tni2ySfhYdOQtOvIWHfk+VrnM1D0oV5r6vnwr5pAgu7Qv35aUVp9S6lGC' \
			b'sgoIQfaOoAWCrOoOIQjz3YPgnCCsPq5efuTHTJAdZtMShJVJORmcXBarJKh7UBJke4KSmAVBdilBqaREUEo9TlBfgTl2Y94RVBLkVHcIQQ4E5cE5QU4IcqsJciDIDbNpCXIgyIEgB4K6WCVB3YOSINcTlMQsCHJLCUolJYJS6nGCetGEoO3nu0mqbntRvtdi' \
			b'GUqkV9Lz7kCZjKlwa1g1Cn+MFHpEXUhGk3SGZBzLODUC1DhSjRDV5lE7VQfV94rQKUKfCF2iVFYBUydDxpKunPDUd4og5RCmpT0iFAOSkHCUo/Q3x4bFXbzQxgDtB50duXH7cElRdYe4pAiXlAfnLimKS4rCEJ90g9OIY4pwTHGYWeuYIhxThGOKcExdrNIx' \
			b'5TmUvin2vinJW/imuHRVRfuuwOSfUg7j/qmXQtjabZb8tthyglc4PGG16g4hDKP9QXBOmAz1LYb6Fu2enEYIq0FYPcysJQxjfosxv8WYv49VEpbnUBKGkX+aaMqkLjhbOv7PSk2YpQzGMetFEcxqGvimnSujU6M9ZnH5LGhsWRrbe5TTstPekzSZ2TGyhA2Z' \
			b'uMwnK/l3VDBNyXOUq3aV5IhMN5iMdKYDYdWWpNLU19sjYivZJ9JaeYl9p9KjHmwHoZrsxca8L3TPZq7WmNqJFx03OT3nVXL+untnfivbYw6IQe0PQ4KWH+hZTkOrlhEqesepO0La2f2CFKrFjXuDar8OwZyaU2hu0C9o2R6wjW+giLfr/+vmrgmQPtCNNwMk' \
			b'4XE19dS1jf+P1h6zNJZozZ4tbtdZvFpvdNJkWuje2PS7bjLexO4u2V5fy/4BCPBpPQGhX4LeGYRr7xBeD4GWFakG4g5ZUH8ae5945wVjkvYOinEoDKAwG0FhTgMKjsJQmNVQeP6WUy1faWjEzDVbjjrfpEGePJCpTLqIQWrP85Fhjl9HmNmxNIbpILNLbLK+' \
			b'TGqQdmfXaoBudqC5QZuz8KWGHDXmab9tz60MNNe3NRo//jldhGoiP5syO2UTL5rVH4NNedrO36BNxyzZ/NUsGY7CkkGJIAe0JBlopquNm/bNW/Stvj+4zEz8HWa2ScAat3wLb30DjMXtnRrd7b8OuOzrWHbQjFKHYKY30PFGL8X1Vduq1W9M9NbK3JMiWYvm' \
			b'PhlftGhEi5t7mk3dzN5cS1Iso7SL29ilq7hnJyFOwfK346guXlbESamz1IsTdQ3rGyE8K0gEKrLyXdpW2706w4Lq0IkcVLBbNFsUM6zIuxRzdd5xmLf8pLvsgcQO35oXw7qFrrQYxd8G46lv+ZUUma6SeQuZu8b881x+B7r97vZiRrHO8jI8cDKDPx7j0Fmy' \
			b'sRtm49Ton+Thhnlg1W9pTvTWpD80wz7/k/z8WH5pFXE015F1Omotsj809cOwsrWeyM9192ugYbj6KaJY2ePE45NiZVO+wUvvVL+UmS9f1mnbQVqsdMVa5LI6sE+4qSOA5S6Ae1rjMUUxcQ8mkRmn3Q6Rod6HDFbteogMTQ/IdaRw3LN1+P2TrQ8RJN+Gfx1J' \
			b'8FPzOx6QRK+URJfC1CvlCWrFQe9PGVjVi/EgllnzLq95hXOJ+9d27SsbVXdwL8H3R/4oP6h/gAjUPyiSy86EKmW0kBLVtLdRTe4hHehALd2t1NKqQx2opb+VWjp1qAO1XNfI3kwtozrUgVrGdbXcqhOxVV15zLLyiM2aCDROWZtJdqDG9Y11nraoulGrD+wm' \
			b'WxstP3istkE8KKE5BiV4dUsHRibVUfWirfz3Qbd6QC0aKxcsUsM/QTjB/zA1yxWEylOFeKBk2/kFl2YQtE6pLH78wfLkGaazWGVB+nqtFTC67hZIoscoNrU1vABDw0n50SzKdD75H6OtnPM=' 

	_PARSER_TOP = 'expr'

	_GREEK      = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\pi|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'

	_SPECIAL    = r'\\partial|\\infty'
	_CHAR       = fr'[a-zA-Z]'
	_SHORT      =  r'pi|oo'
	_ONEVAR     = fr'{_CHAR}|{_GREEK}'
	_ONEVARSP   = fr'{_CHAR}|{_GREEK}|{_SPECIAL}'
	_DSONEVARSP = fr'(\d)|({_SHORT})|({_ONEVARSP})'

	_FUNCPYONLY = '|'.join ('\\?' if s == '?' else s for s in AST.FUNCS_PY_ONLY) # special cased function name '?' for regex
	_FUNCPYTEX  = '|'.join (AST.FUNCS_PY_AND_TEX)

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
		'abs'      : lambda expr: _expr_func (1, '|', expr.strip_paren ()),
		'exp'      : lambda expr: _expr_func (2, '^', ('@', 'e'), expr.strip_paren ()),
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

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_lim):                              return AST ('lim', expr_lim, expr_var, expr)
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_doublestar, PLUS, CURLYR, expr_lim):   return AST ('lim', expr_lim, expr_var, expr, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_doublestar, MINUS, CURLYR, expr_lim):  return AST ('lim', expr_lim, expr_var, expr, '-')
	def expr_lim_6      (self, expr_sum):                                                                            return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, expr_super, expr_lim):              return AST ('sum', expr_lim, expr_var, expr, expr_super)
	def expr_sum_2      (self, expr_neg):                                                                            return expr_neg

	def expr_neg_1      (self, MINUS, expr_diff):                               return expr_diff.neg (True)
	def expr_neg_2      (self, expr_diff):                                      return expr_diff

	def expr_diff       (self, expr_div):                                       return _expr_diff (expr_div)

	def expr_div_1      (self, expr_div, DIVIDE, expr_mul_imp):                 return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2      (self, expr_div, DIVIDE, MINUS, expr_mul_imp):          return AST ('/', expr_div, expr_mul_imp.neg (True))
	def expr_div_3      (self, expr_mul_imp):                                   return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_func):                        return AST.flatcat ('*', expr_mul_imp, expr_func)
	def expr_mul_imp_2  (self, expr_func):                                      return expr_func

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

		expr_vars -= {'_', 'e', 'i', '\\pi', '\\infty'}

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

		if os.environ.get ('SYMPAD_DEBUG'):
			rated = list (rated)
			print ()
			for res in rated:
				print ('parse:', res [-1])

		return next (iter (rated)) [-1]

class sparser: # for single script
	Parser = Parser

## DEBUG!
# if __name__ == '__main__':
# 	p = Parser ()
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
# 	a = p.parse ('\\int_0^1x') [0]
# 	print (a)
