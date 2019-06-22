from collections import OrderedDict
import re

import lalr1

def _tok_digit_or_var (tok, i = 0):
	return ('#', int (tok.grp [i])) if tok.grp [i] else ('@', tok.grp [i + 1])

def _ast_negate (ast):
	return \
			ast [1]                        if ast [0] == '-' else \
			('-', ast)                     if ast [0] != '#' else \
			('#', -ast [1])                if len (ast) == 2 else \
			('#', -ast [1], ast [2] [1:])  if ast [2] [:1] == '-' else \
			('#', -ast [1], f'-{ast [2]}')

def _ast_flatcat (op, ast0, ast1): # ,,,/O.o\,,,~~
	if ast0 [0] == op:
		if ast1 [0] == op:
			return ast0 + ast1 [1:]
		return ast0 + (ast1,)
	elif ast1 [0] == op:
		return (op, ast0) + ast1 [1:]
	return (op, ast0, ast1)

_diff_rec       = re.compile (r'^(?:d|\\partial)$')
_diff_start_rec = re.compile (r'^(?:d(?!=[^_])|\\partial )')

def _ast_diff (ast): # here we catch and convert possible cases of derivatives
	def _interpret_divide (ast):
		if ast [1] [0] == '@' and _diff_rec.match (ast [1] [1]):
			p = 1
		elif ast [1] [0] == '^' and ast [1] [1] [0] == '@' and _diff_rec.match (ast [1] [1] [1]) and \
				ast [1] [2] [0] == '#' and ast [1] [2] [1] > 0 and isinstance (ast [1] [2] [1], int):
			p = ast [1] [2] [1]
		else:
			return None

		ns = (ast [2],) if ast [2] [0] != '*' else ast [2] [1:]
		ds = []
		cp = p

		for i in range (len (ns)):
			n = ns [i]

			if n [0] == '@' and _diff_start_rec.match (n [1]):
				dec = 1
			elif n [0] == '^' and n [1] [0] == '@' and _diff_start_rec.match (n [1] [1]) and \
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

#...............................................................................................
class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJztnftv3DYSx/+ZA+IFuID4lvqbk7o545w4dZIeikUQpI1zCNDmijTpFSj6v9/MfKkHKWntteN9tIbpFUmRoxnyQ4qvtY9WD56cPn35/IF6cHb6hD6fv5TPby9ecNRT/jh/TJ8vLk4f/5PvfP/k2fd0PX92cnH84vyCE5x8w4kfHnPg2fHFydMz8pw+fnp+' \
			b'cfL60cuLM07/zcXxo3TR6WroKrc5+VN57nci4x+XH9629zqZ7HlIuf518oK9rA4/9dn5v08kzZkY8ejrc459/kIEfX363enXJ2LVQw6ev3x4dpLuSUZR5fgR2XF6fNY/4AxZ+O6zi9MnJyz5xTl9nHz78viMQ79+/uG3Nx/J8+ny90+v4b38/ZePrz98/rn1' \
			b'frr82Pl/efPx8kMbePPDr138f//Xet+9+fFT5//84cfO//FN5/+1lz545k/vu9ifP//0+v3Pv7TBt+9/673v3nVKXv7nzaf3v10Oc5Gn0+/t2+R98EqtjpZaLc1C0dWro0bpSlGMseRZtLGI6yOWOrDPyK+hsF304aoPkoeudF+SB/k1tVrGBcLkYYEWH9Ys' \
			b'UnCpnfg0PZpDkX8XXZQbBrVPHo5jH2lBeepFH7BWTDLDWDcMeGUaJTKGcTZLE/KAcWWGoGwWjsNAPQiQheyryRJ+ribJjbJBdKzadJN3HRf2lWmqLMmSqo08Vn4NpXGLQTj24aWUeZTflFs8dHXqiCT6BfxLlHitUoFTvUrxK6MXbQQppRNHg1gyXic72zgq' \
			b'RPE5fFgmLXHQR40jUfx5ui64TExU6sgMyiemEh5U00yKonLxePZR6eQGUI6m9Wgpq4ZDJIuoT4lSzJIf7RdZmuJ+ClJI2g9r1+qWbvZx9MSpOA718RbtiG7WC2rrq0pp5VVQkRobNwtCnIy2taqVtHzS2koTJXlWSso1ylfKa5bNVd5I+Uhr4roFkYFB4rZo' \
			b'lHPKeeWCclE5kqOsophKORJFd6lbIeeo1bK+3ihvlXfKe+UpGJWvladHNyq4VwwdwbEiyJkRL59kJFtCrYtDZIVcbIq1Er2fxlBZi641jJILtxNRXFe4KUbuj8oBuhooy5CxklVS2kvpHxRR3sIEDcMcLPKw6Mjhrk93NSDT9T5VCqnV7Jc+BuwanbAwaJQG' \
			b'hWncnmm7V02M9Al7pk+Cvq1Njdp06L0cemEXcImp3aQ+LSVts9qD6x5c6haqw9PcpD5LCv2q1Dp17NpdKzUq3afS8SkIBjx48XhFeOmbQqWCVsGoYPktgk42tNkVjaUOoUxXPMw/FFVJS9Z1r1W0e64iDx8NI9qIonumm4durBDGYgZjMcM9sDe46xDtU7RO' \
			b'BmnJdFAdmm6SvZWovtErTHOWvbHEpLoxdnNL3H5Z4sGe9Is8RABzoiQPDdi8XfQsLmxYsjxyQZ0cWrtY8fDqwHQ+sgCkSrwcYKFrMeHKPsvBQo924gWybDC04mGTwXjJyCA5YPYUsMgRDEbUwbaDJTuxzBEmYjloEbR4h9m9W1CQt5fF28vi7UWXIi3m6QZW' \
			b'OCT0swl1jYRGUuyLofwKsqnP3yu1nBSnc6l0Ba+dTFeAMJB1GjQgUOGCWxqRHu3AB+gdpCfhNmPQZswkHIKbA24OuDlpPw5h34a1JNufWqqgtZULy5Wicigqh9LhS6hSeaAAg5RZ0d+QVR5F4FEE/tD6XgfV/cGpzlxJ2csnSfCoMwd2HarMpVF9QC0F1FJo' \
			b'QQ0wPchbQSRJ6rg/vK5Y7Qi1Y6t2hNocZnVrGFcjVZ269nqfjPCi16Z2N/tkAumwR/pwDTcLlOw+qcXbGFXax6jS6n8l3FZqVYlw9DHSqcjzWbzI7rWLrUFGeiHpeNAX0XOGqrHirbmsVPeGqtBJk1IqRBWozVB70SpaFZ2KXkXSIapIjYfIdKoOqiadqEyN' \
			b'aqxqvGqCaqiEKtKv4v16KoCKS4zsYbVZb1acC4a150U/Xqvn9XleledNEB488saU9WS/FClv+vLOt+UtayWbn2QZ7/pa8mm1JJOWns8M8JanoXDNdx1/yN6op9ucvKHk9Bv4Dn6WvMHKG6NU65ya9zxJAB8gMLITrGp6IlcxkvNWLhXXksprGfipis8MWD5X' \
			b'YHlPdOk5N6vCCvAv36YLb9hyelYlyJbo0nA8hblORDbJZOUpN1XEMvCVy4WTsxKsG1vA+97VKx6JMBtuigkwPAHwNRFxOSJAdziUmaMEZFiBw6/hQ9+AEQ1GuAVye+G2IryYghkWJI4p4UuBSXc/pRpQw0GH8ybT3JR5EzqSAwdVGOUqI4jx6XMUBIl+KYvG' \
			b'ZS05kiKHpxU8jU8l9PTPd0nNjCRzT9IkSU7BCUnjDqe7n1INSZIOSM/3QGXeliT0QiLN4FKQ1OUoSXIgyYEkdyVJbkxSEjxNkgNJ3fNdUjMjye6OpDUvr0mY6u3zFBWc8BTHPMXMZTxF4SnO81TkbXmK4CmCp5jxJEKHmUqkIpCKQCp2SEnGaarimKoke5qq' \
			b'CKo6FVxSNqPK3VO1hqpawQlV9ZiqOnMZVbVQVc9TVeRtqapBVQ2q6pwqjJj6TCVVNaiqQVXdU1XPUlWPqUqyp6mqQVWngkvKZlT5e6rWUNUoOKGqGVPVZC6jqhGqmnmqirwtVQ2owiBcLgOqGlDVZSqpwuBbciF1S1UzS1UzpirJnqaqAVWdCi4pm1EV7qma' \
			b'p0qOgsphYF4UG4/Nu/sp1YAqI2NzMz82L/MmqgzG5gZjc5OPzUVoHGQqqDIYnhsMz00/PJeMk1SZ8Qi9lT1JlcEIvVfBJWUzquI9VWuo0gpOqNJjqnKXUaWFKj1PVZG3pUqDKg2qdE4Vhup9ppIqDao0qOqXCyTjNFV6TFWSPU2VBlWdCi4pm1FV31O1hiqj' \
			b'4IQqM6bKZC6jyghVZp6qIm9LlQFVBlTlK1EiNA4ylVQZUIUVKLkkqswsVWZMVZI9TZUBVV0yl5TNqGruqVpDVVBwQlUYUxUyl1EVhKowT1WRt6UqgKoAqkJOVQBVXaaSqgCqAqgKPVVhlqrxAmcre5oqrHD2KrikbL7a2S2Fu/nF8FnAwibL4xth5q+xVH4j' \
			b'6vyXJk++S7SM8hWrfj3dYDnCjJcjTMzcEMWQvqgln3M0DvPadElEYlXCYFXC5KsSBqsSyNjg9tp1d4NlCoNlCtMvU5jZZQqTL1NwwQqmSbVpTLFU0dvkkgU9puqP+iven4h0af7EgbSN+8Lro/pX6A4bBScMjqeZ3f2Uasigkxh8zjFYZG/5w0zTYKZp8pmm' \
			b'wUyzz1T2iJhpGsw0TT/TNLMzTTOeabayp1HDTLNXwSVl8x5xh8v2+08Wb+uKY7LseKrZ3U+pBmRZmWra+almmTdhZTHVtJhq2nyqaTHV7DMVWFlMNS2mmrafatrZqaYdTzVb2ZNYWUw1exVcUjbHamtr+DO74oPjQjvmq76KMa3ghLHxxNPmLmNMJp52fuJZ' \
			b'5m0Zw8SzFWg634A0xLg4yF3ChhmoxQzU9jNQOzsDteMZaCt7GjbMQDMbXIPonLetre4fPm/ylwP4qAHba8e82cxlvFnhzc7zVuRtebPgLQk0nW/AG2JcHOQuebPgzYI32/NmZ3mzY96S7GneLHgb2uAaROe8bW3d//B5cwpOeBtvgHf3U6ohb7IBbuc3wMu8' \
			b'LW/YAG8Fms434A0xLg5yl7xhM9xiM9z2m+F2dj/cjvfDW9nTvGE/PLPBNYjOebvNjoCcTetPlq4HL/BJtJvgVw8INPsGoQhiJztR45eszl22EyUvWfoMcmyPUZTLxJZUIYRKOjaq1tiYwju3lW8632B7CjEu5mIGWDZpnwpvXo03r+7fvHr2zavHb95W/PQ+' \
			b'Fd68mSIOf/6kIPM2uwrXx/KWQG5CY1Nvo1eMCm4Jq0e9Ysxc1ivKokmK18g91TcWEtq+EcsmrVjT+QZ9I2JcIaDsHrFiYrFiYvsVEzt/sKPCX6Mpu8gkf7qLxIpJpolLYnIQb7MRsV0QuVeouGPYHxxrBSc4js9/dPdTqiGOcv4jxWvknsKxkNDiiFMgrVjT' \
			b'+QY4pmfEXECJI2J9L0HjkqCcPRfSJi+YTA+ZZhJHQzJ1XIPonMlGrYqD15OnruuJQWF/xro4YG2+5KHqOXimDlJj5XfiGPW6Q9TL+dHb8OD01LFprvK7Oi09U7Mzp6Qp823rMX6hqnRrarOqpYudrFUZgvALvelrmP9oDP+hlq3VdF3dWWVzAayr8LYgJiq+' \
			b'7y5tB0HbXU7BoO+mUYcv1a7DgbTtZjzH/xLNW8vB4o2buNlFV23+hr01j2buvse2u37zVqrRf5MaLWsT+853Uatuba1W+zqk4hevVKu9bdVyMVLtcjEd1OCKv56Hr6LVk5Wr/jDuK2KWN7xJywMdNc99BZHr5CBa7s1brJbHT7faQCVwgLU5VZNs9U6rkRcj' \
			b'9PYnQPEvVIVm11VolOiw5Sqs1WrjyrtOzd1xbbnbV9GGHeW2KqTB94zl6yVYdos8j23YatmGIS2iERt4R8W8wrf7VxvU31WVd6fLRRPVxaVyRW1t9Eq762oaDkvIlNVmw81tlf7sqLIcPOIscLi6yeysEnQ6Ibm2IszBtgEu42v0WPvWBuxXxM2f+DNsKx3J' \
			b'sPRNbSdf8is6L7I5WnRb7HuFP9i2SqmkzAclRxliJamptMWiXh/JGrqsbY2ljZGmECNFGMriafc/q5HgOCNYV9VGknUuOf33Ef6vBDj/LFtG3XZQ2rjhTWleFeaz34EXgtKCgWuXaV/JPzu4hhijRj+S12Z5sZU1LcEq/GAQZvsfkeMm5GBLbFqaV/0PBnSD' \
			b'GJGYDs9sIDPwODLM/YjQsLFQGmnO/4jMuEYmtbVpsfxnu/KfmAVFcrdZia/QZ9uTM4/i7cbQP5CFWt47lN3BdjdQlrGHx1oNaUSdGg/lmrIvbIofdIPw80Jq2/VRj9XIuHHcxS3kX3tcZQvOd40twh6qbKCmfdPBpmnaKNXJzLrutkJHxtaFwdxH343jToe7' \
			b'hy6K91xmk0vx4Esn26prfjXdrYNR+gZGzVd3Z2B97Sr2alNXy4Ch7oLN9TLyZnkKwHRz4/qsNrE4szaomzka00zE81hmOgMstNu3kAdx23Aw0O3AQPn3TnfvYKDfgYFebcXBwLADA2u1FQcD4529VTfsaXlKtdbhgNOVyYaOplfXS4myuHq0tK2y8Gp3DmWx' \
			b'f6MtnkTt3mG+VIk63VSUpnWNHH6hadni/7eMkKU=' 

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
		('LEFT',          r'\\left'),
		('RIGHT',         r'\\right'),
		('CDOT',          r'\\cdot'),
		('TO',            r'\\to'),
		('FRAC2',        fr'\\frac\s*(?:(\d)|({_ONEVARPI}))\s*(?:(\d)|({_ONEVARPI}))'),
		('FRAC1',        fr'\\frac\s*(?:(\d)|({_ONEVARPI}))'),
		('FRAC',          r'\\frac'),
		('VAR',          fr'\b_|(d|\\partial\s?)?({_ONEVAR})|{_SPECIAL}'),
		('OPERATOR',     fr'\\operatorname\{{({_CHAR}\w+)\}}|\\({_CHAR}\w+)'),
		('NUM',           r'(\d+\.\d*|\.\d+)|(\d+)'), # r'\d+(?:\.\d*)?|\.\d+'), #
		('SUB1',         fr'_(?:(\d)|({_ONEVARPI}))'),
		('SUB',           r'_'),
		('POWER1',       fr'\^(?:(\d)|({_ONEVARPI}))'),
		('POWER',         r'\^'),
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

	def expr            (self, expr_add):                      	             return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_mul_exp):                return _ast_flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2      (self, expr_add, MINUS, expr_mul_exp):               return _ast_flatcat ('+', expr_add, _ast_negate (expr_mul_exp))
	def expr_add_3      (self, expr_mul_exp):                                return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_negative):           return _ast_flatcat ('*', expr_mul_exp, expr_negative)
	def expr_mul_exp_2  (self, expr_mul_exp, STAR, expr_negative):           return _ast_flatcat ('*', expr_mul_exp, expr_negative)
	def expr_mul_exp_3  (self, expr_negative):                               return expr_negative

	def expr_negative_1 (self, MINUS, expr_diff):                            return _ast_negate (expr_diff)
	def expr_negative_2 (self, expr_diff):                                   return expr_diff

	def expr_diff       (self, expr_div):                                    return _ast_diff (expr_div)

	def expr_div_1      (self, expr_div, DIVIDE, expr_mul_imp):              return ('/', expr_div, expr_mul_imp)
	def expr_div_2      (self, expr_mul_imp):                                return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_lim):                      return _ast_flatcat ('*', expr_mul_imp, expr_lim)
	def expr_mul_imp_2  (self, expr_lim):                                    return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_lim):                       return ('lim', expr_var, expr, expr_lim, '')
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, PLUS, CURLYR, expr_lim):          return ('lim', expr_var, expr, expr_lim, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, MINUS, CURLYR, expr_lim):         return ('lim', expr_var, expr, expr_lim, '-')
	def expr_lim_4      (self, expr_sum):                                    return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER1, expr_lim):           return ('sum', expr_var, expr, _tok_digit_or_var (POWER1), expr_lim)
	def expr_sum_2      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER, expr_frac, expr_lim): return ('sum', expr_var, expr, expr_frac, expr_lim)
	def expr_sum_3      (self, expr_func):                                   return expr_func

	def expr_func_1     (self, SQRT, expr_lim):                              return ('sqrt', expr_lim)
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_lim):    return ('sqrt', expr_lim, expr)
	def expr_func_3     (self, LN, expr_lim):                                return ('log', expr_lim)
	def expr_func_4     (self, LOG, SUB, expr_frac, expr_lim):               return ('log', expr_lim, expr_frac)
	def expr_func_5     (self, LOG, SUB1, expr_lim):                         return ('log', expr_lim, _tok_digit_or_var (SUB1))
	def expr_func_6     (self, TRIGH, expr_lim):                             return ('trigh', f'{"a" if TRIGH.grp [0] else ""}{TRIGH.grp [1] or TRIGH.grp [2]}', expr_lim)
	def expr_func_7     (self, TRIGH, POWER, expr_frac, expr_lim):
		return \
				('^', ('trigh', TRIGH.grp [1] or TRIGH.grp [2], expr_lim), expr_frac) \
				if expr_frac != ('#', -1) else \
				('trigh', TRIGH.grp [1] or TRIGH.grp [2], expr_lim) \
				if TRIGH.grp [0] else \
				('trigh', 'a' + (TRIGH.grp [1] or TRIGH.grp [2]), expr_lim)

	def expr_func_8     (self, TRIGH, POWER1, expr_lim):
		return \
				('^', ('trigh', f'a{TRIGH.grp [1] or TRIGH.grp [2]}' if TRIGH.grp [0] else TRIGH.grp [1] or TRIGH.grp [2], expr_lim), \
				_tok_digit_or_var (POWER1))

	def expr_func_9     (self, SYMPY, expr_lim):                             return ('sympy', SYMPY.text, expr_lim)
	def expr_func_10    (self, OPERATOR, expr_lim):                          return ('sympy', OPERATOR.grp [0] or OPERATOR.grp [1], expr_lim)
	def expr_func_11    (self, expr_fact):                                   return expr_fact

	def expr_fact_1     (self, expr_fact, FACTORIAL):                        return ('!', expr_fact)
	def expr_fact_2     (self, expr_pow):                                    return expr_pow

	def expr_pow_1      (self, expr_pow, DOUBLESTAR, expr_func):             return ('^', expr_pow, expr_func)
	def expr_pow_2      (self, expr_pow, DOUBLESTAR, MINUS, expr_func):      return ('^', expr_pow, _ast_negate (expr_func))
	def expr_pow_3      (self, expr_pow, POWER, expr_frac):                  return ('^', expr_pow, expr_frac)
	def expr_pow_4      (self, expr_pow, POWER1):                            return ('^', expr_pow, _tok_digit_or_var (POWER1))
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
	_AUTOCOMPLETE_SUBSTITUTE = {
		'SUB1'  : 'SUB',
		'POWER1': 'POWER',
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
			return False

		sym = rule [1] [pos]

		if sym in self.TOKENS:
			self.tokens.insert (self.tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

			if self.autocompleting and sym in self._AUTOCOMPLETE_CLOSE:
				self.autocomplete.append (self._AUTOCOMPLETE_CLOSE [sym])
			else:
				self.autocompleting = False

		else:
			self.tokens.insert (self.tokidx, lalr1.Token ('VAR', '', self.tok.pos, (None, None)))

			self.autocompleting = False

			if self.erridx is None:
				self.erridx = self.tokens [self.tokidx - 1].pos

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

		rated = sorted ((r is None, -e if e is not None else float ('-inf'), len (a), i, (r, e, a)) \
				for i, (r, e, a) in enumerate (self.parse_results))

		# rated = list (rated)
		# for i in rated: print (i)

		return next (iter (rated)) [-1]

# if __name__ == '__main__':
# 	p = Parser ()
# 	a = p.parse ('sin (x) y')
# 	print (a)
