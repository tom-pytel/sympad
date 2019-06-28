# TODO: Redo _expr_diff d or \partial handling???

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
			b'eJztnfuP2zYSx/+ZA7IGaEB8SspvabrtBZdHu0kKHIwgSJP0EKBJirTpHVD0f7+Z+ZKiKEuynHq9drGw1npRw+Hww9eQ1l5s7jx68Pj50zvqzoPHz+j74YNH9P30uXx/fyWXnnxL38+uHnz7T9p/8/zxfb54+Q3f++reFX1/d+/q8vFDlvHt4ydXly/vP796' \
			b'+G8Oe3XvftzpuDe0l9sc/OkzfvqxRPaDSPrH2w9vUgg+v//k0aN7KQa+8BXJ+NelPMcKsQ5fP3n+1cPLp89EwH0KyBe/eyiJ+vrBDw++vuTrXz95JjFKqKfPv8K3To+IfvfuP3ty9eDewxwPH3539eDRJQt79oS+Lr9/fu8hn71+9entby8/fnr55uPnH39+' \
			b'++tvrz7R1V8///i7HLz93y+fXv76+Ze33clPnz+8fvnh7X/S+euP79+/yiF/pMPeox8+v0+Hv7391B3/9OnV63T8C2nwIZ28+vHX7vrH/3bBX73+rR9/jq6T2Ivz53fd1Xcfuufef/755bv3v6TTN+9+z4c//dTpmxPGD9BBp9mbN/Hwzgu1uViboIxfKRwE' \
			b'PtBqbWTv1UWjWkUXjFPtKl2TK93pWstDRv5MrdZ2lc+rfEoHvDf4MhSJXsUrdEQHJEokBfkzjVrXq+K8ylfogGO3+LJuFU/X2slRrS40y234b9Vdsv3TLihf4yNSzVHSoTDOrJfU2+Ky3zrTxZWwdVaKrftnpLVYgVUz8eiikhM+a0jrGAEL6V+Lx+uW9626' \
			b'MMpqJRlSKVuL3iQHphm9LTleLwlVFYHWWvLLyp9p0w2c2yqfr8XCtfytYXc5oL2TRPoVjtcCoG6VRr5SllP8wgmSyVcala65/mUd9SUV07V1FOPwRaZbxXMCVmys1YXVEi6eWhDP1/sWaJIZ2fpRiu5yiuQb32VVPK3KCyHHQjhJXmvOQI+kRJ0pbSEeULzd' \
			b'kWQt6UEPkzJMEiyWLtE5XV6VoYYh0jmdihpe0h5TGBXIF3U9eo3P8nVYi8RTyaFKZEPRqlpxXWFb5SrltHJOOXrSKCp0ZHiS4oxyZFwijEssFy1KETFGRvZeeWLRcEnj3KW4gGbDfFGOkgZeK08SlFdBuVq5RrlWeVZBETikC+VioM2oYFVwKlDAoEKtQqMC' \
			b'aRVU7V4wdQTvhnKZGa7lmwRwKqhe4zOLnaviVUoInZ9eQsjGoqdHgljBlVRxsnNRe+0RSu7euMo2Gh+6Wjn1Vnl3LvRYF1MAs5IKsqujtYPkCRUrqiTOpkQEIGMb2XmkzAck1CCrjIShup0qhGMoRRE7ROxzxCDlSNEjZ03di56kU8a0KlTHUqI5utVR+bFQ' \
			b'VB+oIb1w3TMAYeMNCEE+uVSJIr/Ohv2YhvoMy61DXvnYommBZcFzRscH2qUPSAwXAVVBiFVgQEURUFACQAmoRIKIritVa1UbVVtWFwHr+DiZZHXyNt5Q3+As1CQNSc+TVY+sd7rqcQ/PSIGwvOe+Eyt7GqoZqGZlX1TAG+4/ma1OrJeWes9ofO7WGHRrDLo1' \
			b'JnVrxDDoEsuICz0Fvmqiika0OZva06aBgCTmKFGayJkRwx2vWefODCKujxsx0Rj7D82xjExRtl9QAAKaONMAdPDvNczmzgnsDXfFzNl1Znw0dd2vaTbcxzkr22ux/YL06hYJDqhEg6S76DBtuGtl0KdCNVwD0hrVb21QG9c2dajsiPeiGbnKpxanNrZ79lR8' \
			b'BBtufu2JNL/S7pIy50EfN/0mtuIWrbhFK067wSOo9HTM/+q8Cpn3UykyINmiv2JgB4OS4WtYx0sRPU6GSCG/cDCzQ1lMvSgo56CcQ4nUCBJwLwQ8WFfo5yFVtfS3RlIvRcedTkEmBdxW95SUcWDTgU0nPcoKWSQ3pSvpjtpB8rB7NF+DXQv1YyVZS2Fh69ut' \
			b'ipoS5ZEoj0T5MytOZ6Qvw+ElrzzyyiOTHEqIQx65WA8GZEtAttCOgHohoAUE9DFgfbLD0w0noEYCaiks6Kqi1feieumZIz0bpLvBY00M2Zx2IttTVq8+YfU4b9s4HVHF+YhKqttKbUgGFW6OAAUcA4MuAezh7UWW1U26cjVshmnLtYSkH3Yhbbg8VjHlDKU4' \
			b'y3MCBo0W1aJU7RDBpBvB3aqmUo1WjVGNVY1TDRFMSreqrVRrVetUSwklUHgqmNJQUUZUlIqKklFx2vk6pZATx6njtLHzkj2ePJHBsxg8r8CTCuzgZx8Aj/95Poono3h2h23I3WXuK/MUGzemPG/lGAPHSeYZcN45mfpVsgaCbaDW9Dx9U0LXPHHMJmjytuaZ' \
			b'cp5JlQxfB/7yVZzbpz2ZaB34BovnFQ4sDJ812bfhWIzE753MHXOEmJkW6RJbS/IDX+TZYxJCfEURlMPrwHd5XQVpyBPxJIAj4xlr0Z86kOugRbCWGd81r+fw/EfhWIEaayoCr9XgmW0xCEfPf9xiKlnqoHhO33FMvGaDZHGVTHZtsKCA5PukF7Gy5pltW79Q' \
			b'f7jm7pozomppb/7kHpGSyWU3C/ABoO0Tq/cH1Qur+4O6D6RzYPL0vlimT6acWtkx2VWBZh9HuSXfO4Bk06eNoZQdZ6cVIiWmuFiCFz4MSMyPzsKYgwUNkYtglJCmIzGKGGdRwvpeTAWFBCFx1bi7XCwor2jv/pQm95bFJSwaYdGULBqwaMCimWbRCItmN4sm' \
			b'b8KiKVk08yx2j86z2AULGiKXsWhKFiFigkVUhzmmRSzaWxYXsRiExVCyGMBiAIthmsUgLIbdLIa8CYuhZDHMs9g9Os9iFyxoiFzGYihZxJUJFgNY7GJaxKJbwuI1djKbv9zP9NNdzfrwvc1ZYBsBtimBbQBsA2CbAlg2bNoKeBuBt9kNb1+Ag/wEb+xqSswV' \
			b'YkAAkyLegrkTNQ9zFyx2OiWKEmi5O850I0zr3PFM6R/HugHWOc4lWPtbrA+HdStYlyMnObWyY6zbEus2bwXWrWDd7sa6L8BB/hDrFli3wLoF1nhiiHUnah7rLljCut3Gup3EugXWbcY6pn8c6xZY5ziXYB1usT4Y1kaGXaYcdhkMuwyGXaYcdpkqb32sJZh8' \
			b'78C6EOAgf4C1wTAsLluXXYp4iHUWNYt1DhaxNtvDMrk7irXByEwCAOuU/lGsDQZnvTiXYF3fYn04rMXJxd99rDWw1sBal1jrvBVYa8Fa78a6L8BB/hBrDazxWxgTf7+CJ4ZYd6Lmse6CJaz1NtZ6EmsNrHXGOqZ/HGsNrHOcS7BubrE+HNZesPYl1vDe8s6K' \
			b'k77A2uetwNoL1n431n0BDvKHWHtg7YG1B9Z4Yoh1J2oe6y5YwtpvY+0nsfbA2mesY/rHsfbAOse5BOs2zUt8Cdj+iGzr4+DtD4U4G14oL10eBi4PA5eHKV0eprf1KQ8Qg+u7QO/LcIhiCDq8IAY/iJRd98QQdLnKpjO7vCJZRoJ92zMid8dhh3NEAjRicwE+' \
			b'mmIcePhIevEuAV5XX16RH5P3s6nLxU9iSj+JgZ/EwE9iSj8JT7umrU85r64RV4nZ7SopZDhEMaQcrhIDV4mBqyQ+MaS8EzVPeBcsEb7tKjGTrhIDV4nJrpJkgnG64SrpxbmI7kXTdLfdlGVoi6/ElL4SA1+Jga/ElL4S0+at6KaIr8Ts9pUUAhzkD7mGr8TA' \
			b'V2LgK4lPDLnuRM1z3QVLXG/7Ssykr8TAV2KyrySlf5xr+Ep6cS7ietGU32G5xgKQObS3loGcE91Wxpa2HFtajC0txpa2HFvSabf16ZZg8r2D7kKAg/xIt83LKSyGlxbDS4vhZX5uwHi+Mct4DhYZt9sjTDs5wrQYYdo8wkxWGGXcYoTZi3MR44umEm8Z34dx' \
			b'6YLzd59xC8YtGLcl4zZvBeNWGLe7Ge8LcJCfGM+VuEReIRKEMb24txjvbswz3gVLjNttxu0k4xaM28x4tMI44xaM5zgXMX4DU5R/d8adMO5Kxh0Yx1o4Wy6Gw5V4vc+4rIazu5fDFQJc3EXGXWYc6+IkkhhXL+4txrsb84x3wRLj24vk5O444w6Mu8x41Gyc' \
			b'cQfGc5yLGD/AfCXlCprA0QWtu2HX/IKGL0He9ahvTht8LZW7Lit3jcpdo3LXZeWubd6KqUyp3Om7Rv0utzV2E3OafUkOEcUSoFHLN5TtGpObqOs16nqNuj4/PZzf7EvuFQVd1WPTnF3QNM25XeXrySpfo8rXucpPthmf5kSV34tzUXE40DznF5eFv1gKTrkI' \
			b'WHGk29KRbuFIt3Ck29KRzqZLW1H3iyPdwpFu8So12U20AH0xDrGkFsDnFgAedQuPuoVHPT83bAH6MucbgS5YagS2/ep20q9u4Ve32a+ezDHeCMCv3otzEfUHmgY9d+rr6yJf3I62dDtauB0t3I62dDuy1dJWkC8+Rwufo9zT2E2Q3xfjEEsiv8nkw/lo4Xy0' \
			b'cD7m54bk92XOk98FS+RvuyDtpAtSa5jMQsFEfzTJOP1wQ/biXUT/gWZLT5D+JhUAffNlQPyTtvRPWvgnLfyTtvRP2jZvRRkQ/6SFf1LuaewmykBfjEMsqQy0uQzAUWnhqLRwVObnhmWgL3O+DHTBPOIL6emtkjDptEzhoWUqCNEu4wUBfste5IsKQqs2g199' \
			b'6bFl4fX0qNb1VoCPLf+eo7b9ssXeU0CGAYCY4Rz7DdZ6MOTsw7bePYnJUPXXbc8t2t79gyoGZI8fUvUXaU/AsB70A1bybq6D5bSRN+wdNr/tRJ7rnO9cH/MCxrH85/fv8Vvw+AeTiQX+dSO/rPD4TDT8pL5+NLSewEPnJXTJRCOo5Grcd9ikqnyIjz4WPmZf' \
			b'gqodtYY+1ZqjrRZR0u5adDkHCj88U430ONmjKjGHY+GQICyBIJwiCEso4KRdT1MSGdDy5uq9OLA33Xkwt/2HmOl6xLF2+D6EO0rB36fUt+05twDX20nAasFwDQ2An+Wg2geFurdEZ18a6kOOILj3KCT4v0RDgOued/vxIDLyDOxfRMIfeljB771gHILdIkL9' \
			b'YSwNKGv56Xu4RWMSDUxn8m5PNNyJo+GAhptHo77p7sIh+wqDN8GUb3+prrnt4AiO7XZwO1sKnf4PzAgG2y9sIV03fxcYtuqEnPsCwIl2Gq+3w6j+qKnoI6/bv29eO3OdJf1LMpsrCHP0zKZ6nm1/l1Br9N11Iy8fqf7G+W5PLt9lO4l81/KmKbxChSf1ZK6j' \
			b'lhk+Nl0bVwDRQd1IunkxT8NjC1JBHt16iDuCFeezBKcb7Qv8a6CNdos7lvXi/uTiDuROcDw3CPilgXT//FIWQl6psFddv2cHbz7Dgy86cWRTsfcCYy8y8yFsnOxb71XQ9rXqoSzK5jR3iQQxp+c3uTDd4QXey7iJ2It5ykTWcW1XFWKbnmXiXY6brsjExzv7' \
			b'VVv2QjkqUxhn4dliA9nNjGyzl2xdypb/LCk/CtLyq0PKAR4ppVnvtkrz0Lygjr1GtXyz56/lA5k44mYFkz+s7Fp+i6EnJDahFGq4eTHFh9sDORJpdigNU/tzMq1KH7RJtvyIWDcuFisGJoXH6Zpuxp3JUf0Pmj8/+Axbr5X8F01SwB1EhcANdVj2kbjD4eIm' \
			b'GJd+JOp6Pmrny9j9TgUaNfJx3SF3MAYf0aOBHs1iTVxPGe60TCpEVSr3mtrJT3ezDCVqtdemlnhhD7iJuvi1bNa3WLIjulv5mcEgBdwBkdeg8sqbbtlNb6lNXlLTpMU0dV4pwxFNp9Op6904pQ71rsOk+HhIGEhfX4Z6ddAN+ppdGbqte5GPY+loF+Vbrfqb' \
			b'7216YqOuCwJQ12U8DGfEuAik1t5UarkDd7wNiXU3llirjrghsf7GEuvUETckNtxYYmt1xA2JrfdM7Hxjs3eSebi1z9bUwytts58E6tWv8I+mr7etXWwBo+Y3rJXdGay/8XBzWVDYoj0VWwR1cxtGW6fXBeOh6s1vsE70hInbq+Z/uyFXjfw8jGxT84iZXy7C' \
			b'CMabVt7umv+tgxiIUswhfXKohOg10bF1lbUZFbdAvC5QnE5s1oYtSNZBGC+26VxqdY1hfKzZeO6WxtHy0zUemq/+D+ck1yg='

	_PARSER_TOP = 'expr'

	_GREEK      = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\pi|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'

	_SPECIAL    =  r'\\partial|\\infty'
	_CHAR       = fr'[a-zA-Z]'
	_SHORT      =  r'pi|oo'
	_ONEVAR     = fr'{_CHAR}|{_GREEK}'
	_ONEVARSP   = fr'{_CHAR}|{_GREEK}|{_SPECIAL}'
	_DSONEVARSP = fr'(\d)|({_SHORT})|({_ONEVARSP})'
	_STR        =  r'(?:\'([^\']*)\'|"([^"]*)["])'

	_FUNCPYONLY = '|'.join (reversed (sorted ('\\?' if s == '?' else s for s in AST.FUNCS_PY_ONLY))) # special cased function name '?' for regex
	_FUNCPYTEX  = '|'.join (reversed (sorted (AST.FUNCS_PY_AND_TEX)))

	TOKENS      = OrderedDict ([ # order matters
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('TRIGH',         r'\\?(?:(a)(?:rc)?)?((?:sin|cos|tan|csc|sec|cot)h?)|\\operatorname\s*\{(sech|csch)\s*\}'),
		('FUNC',         fr'({_FUNCPYONLY})|\\?({_FUNCPYTEX})|\\operatorname\s*\{{\s*({_CHAR}\w+)\s*\}}|\$({_CHAR}\w+)'),
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
		('STR',          fr'{_STR}|\\text\s*\{{\s*{_STR}\s*\}}'),
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
		('ignore',        r'\\,|\\:|\\?\s+'),
	])

	print (TOKENS ['STR'])

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
	def expr_term_2     (self, STR):                                         return AST ('"', STR.grp [0] or STR.grp [1] or STR.grp [2] or STR.grp [3])
	def expr_term_3     (self, expr_var):                                    return expr_var
	def expr_term_4     (self, expr_num):                                    return expr_num

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
