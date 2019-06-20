# TODO: derivative explicit parentheses

from collections import OrderedDict
import re

import lalr1

def _fltoint (v):
	v = float (v)
	return int (v) if v.is_integer () else v

def _ast_num_or_var (text):
	try:
		return ('#', _fltoint (text))
	except ValueError:
		return ('@', text)

def _ast_negate (ast):
	# return ('-', ast) if ast [0] != '-' else ast [1]
	return ('-', ast) if ast [0] != '#' else ('#', -ast [1])

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
				return None # raise SyntaxError #

			ds.append (n)

			if not cp:
				if i == len (ns) - 1:
					return ('diff', None) + tuple (ds)
				elif i == len (ns) - 2:
					return ('diff', ns [-1]) + tuple (ds)
				else:
					return ('diff', ('*',) + ns [i + 1:]) + tuple (ds)

		return None

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
			b'eJzlXWtvGzcW/TMLxAIoYPicob/l4XaNdeLUSbooDCFIG3cRoMkWadItUOS/732RMxxxZMmWbCmBGPFNXt5zeIePkXN0+eDs9OkD9eDFK/x+evrs1QuM/XDxEryzZ/h1/j18v7w4/f6fmPPT0+c/YerJd1ji0cML+H7+8OLk2RkETr9/dn5x8vrxq4szLPTd' \
			b'xcPH4mnxDfiUjcWfUac/Uhv/uPrwNuXlNjHwCGr96+QlBlEG7PX5+b9PqMwZSfv4yTmmvnhJDb149Qi+n5y/enR2IklUniR4+Pjl+cXpQ+z8yemPp09O+g7OuC4We35x+vQEW355Dl8nP7x6eIaxPz7//OebjxD4dPXXp9ccvPrr94+vP3x+n4Kfrj7m8O9v' \
			b'Pl59SJE3P/+R0//7vxT89c0vn3L484dfUvj9599ev3v/e4q+ffdnH/z119zv1X/efHr351Vu4eOb3MIfvUwDSX97937YBQSyfG/fSvDBQl0ezbWam5kC36ujTkUFCcaoOEtplJKjcx0wZOifcWpuZ4N4H4UA+Fi3oZoNf1noTeuZJGEQQ5a/bDOT6Fw7DLXq' \
			b'SENTusV/s5RiB7FUDlOwKsiB2SwFx6yhIeki2RUxrww00Y7SbNlSGMWMHVeBtFgkFNkYhJBTRw12h7qEPlCjSkM1N5vKhY5A0deXKYrMCSZL/4xP6RIPfXxOCtSav0DO2awPQqhTRyA6w99hAHM7xSzQAeBoqH+BLiCHJMkMU6FFLWNNaXOGzPGX6fre+ySz' \
			b'nIhqL1NiigJBMYTdDRQURMUmq2eqACOaysw7ahYpV0gORXwKaCrjMRaVBQlkyJICUUidFWVG+RKFGE0cmCdZMOmwTwOl1dIw1qdbohk0DlMCJvgl5Cmvgmpx8sFkAFpDTdQtSNMo1ykXlW9QDbZVaAFwnjokFowQsQbNNDiBEFHiIhAKOISQGuWsck45r1xQ' \
			b'DtpVEFc2KgdNa+WAlRZmqUjqQRSjvFXeKe+Vh5RW+U7ZTgW7QF6DQbgEcNAuePqGfnAYMJcwZjkLhsGpFrPvWWhQKEltWETQLHlRRPQk8uFg4A2rWLBwPBzHwzlynOsbLtRyIS6TRqwl09HA7xwOLyRiODTJtv1+AO/AHeg07LiznlihJvVkGARj2XM769fv' \
			b'qmXNI3A8AufY4xnvglBNyCVFmzTlD2s6OR6EjQcmtpZZROq+rrQOUtqtVZpx9mI3PaPvJZVnlefZ62n2+qhCo4JWweAEZ2sTUnUFC5W9V+glrg4PQk4QEQTdY/nMPsuHKxIjqwHDqwHDqwGDNs1rznWc7Dj58igSOe5JYscyaZa4f56RjIdjsrToVsdyHNj/' \
			b'bMMHHzW1k0eqGQlnNxfO7Uw4XwrnLLOUO7zzme78hrrBpQNPvoNi7iUubg5J4CPmhY1izPRBSU+LGrPGMkXsoicfFyZmtBS5xEWL4dUK23EfeW3CC/bAE+komLRUsZU9bKikYtRy1MrTxPLTxPLTBLyR2Lx501zecUE3VRCfOPb+9mi6k2E16O/ElLH+hnZ2' \
			b'Vz25YU9oMxkBSr77dTtzzDD8DYPM34y4E8VwomfhvWehPT86Q8Mezesqe4CPjvnomI+OHxgcdymuKb6jLbEb4euGKDgWjMXhstgLjjXyWAMrJ5A+RtMahud5eJ6H5w/KvjmW2x2a3JrlTiAaHkVDno+EXmAsA2FJQAUGKjBQIfEwsAIC2V+NTVDpdn+3Dpc4' \
			b'jJaH0aZhtDyMlvQBAvJgOy7Vianv9nlQjuTcVA9xn4cEMu2xfMiIOGPN77OYeFDeyEl5I0fMDfG+UZeNQvGgY1zyaDRbLCULDk30vUa22yqAnQNzAK3DfNGqbVW0KjoVQZoG+4L2UT4UEEeK57V4wonn9iiLbaDvALZyDmKTj3crdBVj4V+n5tDtPFjKG37o' \
			b'6sljvRbyDfh02Qg+pnsuA/ZrDsZrjrKmzwKN3f2NFc/pGxqthCbGy7nL7rpxp/b7kZcNLOgJDcNHHnklfCSiDXmE5xDMxCBkvkZJBrmZqY40dGnx0kzoz6jWqtap1qMuWzBZRnVOdV51oNpGRT1UMAqPg0HFDRUO6Sg+yr+kfMjDY/shCEh8vGbBpT+u+y0a' \
			b'F5pPeA1pcW4hOHMoM3eoXvBhrHgPi3rFm1+8ysW7ZRwwfOPXBIhOPnO87sSbSk1V6KYXLyKhEZCtw6vhkIou4avwWhTv8K2gjTXxBQLsHC+ToQR4NhY8wFvJOV6uOiympW0QCwUvCQIaw7ZwecnFEEaIY2G8vo0LWs8CZxzxha+Vb0KSsDlJRsQIW+PG0sRs' \
			b'FTuCH81quwQ3Jjn6npq1beES5lSjBJ2aCoOilXmNyQOkqcpaYKcmq3CXMiK27qvHNip2Gdu4jG0kbOM0trFwGdu4jG1kbHPRGrblLKYq62ErTdaxLWRc0IX+V44trpzIJWzNspnGJEffE9jmRqQpwZZqlNhSU2FQtIItIdZjS1XWwjY1WcW2lHFBr2l87djS' \
			b'O2SoyoStXsZWE7Z6GltduIytXsZWM7a5aA1bXWKr18ZWmqxjWzjEtv3qsTWKXcbWLGNrCFszja0pXMbWLGNrGNtctIatKbE1a2MrTdaxLWREbLsatnknONwG3hhn3gCG9dDWBLhdhXmM24LdK3YZdk+wG0a+z04U8EQBP00BX7hMAZ8pQE1zR1LGFR1ViCDy' \
			b'aPaEDn6KDqbCCGm7zohC5AW9xSU7MrdqT1aliN9ki7Y+Uewa27Wb8MZuwJ11tm5kLXDvhgHL79nW929UgLRFREsuEQ1xCcS16UOIop4VT/gWer4F5ltgvvHujiuBdkzt7GK8x5MuDMuUCBgmCRgKAqJGiYQywDoJA235+vE4VtFg26f+1v4Yt71tPJ7HLzN6' \
			b'8Xhd07U+Lw/JenWKXbZeHZOqY1Ll7EQqLiFvWk+QqitcJlTXE6pjQnVMqI4J1fdVMWCcYzR7wp9ukj/dsgGTtuvcKURe8PXBN/xMo/fcTb+9NLy9RM8E1WenZxptNc30VjPXkHqJEv1W0/DKhjzuyBUdVSghlTR7QonJbaeJy5SQtuuUKEQmSpjdU6J21D24' \
			b'VrwnboQRP+BZxC7xw/IWFT0o3GcLP+jZxQl1fuQaUk/4YfvtqmQYk0M+hVzR4zJRUgXNHhPFTu5hqVBJlNR2lSgj2S3tZHX1ePGb5IpR7DJXeFuEHnIlZyeu0BbJTm+Rcg2pl7jSb5Ekw+QixqeQK3qscEUqaPaEK5P7Jio04oq0XeeKGTniSvW48pvkilXs' \
			b'Mlcsc8UyV3J24oolrthprpQuc8X2XOEMY3LIp5AreqxwRSpo9oQrkxcYVGjEFWm7zpWx+MSV6vHnSq7wpW1+cWOSNLa/kt2YOmHAnuYeCQS9qv7Cg+87WuKO5Ahx6NqjRdH56qOtsqdNHyjQqf72o7/8oLAx4nv2Xcg1h7SJITOHi2v6ZtpM3oS0S6ThdquU' \
			b'afsPkaV6nrrasKzDlNtzZCOChC0bmaDYZSPD+2jL++g+OxkZ2kSnNPEqpiYULpuafhstGcbkkE8hN6pcszZSR7Mn1mZyB60b7ntscaT9usUJI0ckqh7c7gmJAvGouzcqtYpdphKbHMs2p89OVCK7k9ICexUqtYXLVOrtjmQYk0M+hVwoK4+oRMLqQb7R7Amh' \
			b'Jg1RKj7ik3RS51M7cgv+KeUlv6px3YsabWWZk1/LGB7/I0O29h7GFAno8C6ODuv4pG6eVizrvWMxn36/YvhexfjAH5Hd1csUEwDieRoeo41enQChbgmh2xKKZtUlTiAjWAcUgcb30doBuJZeG7kbkNt2Zzjj4Ffet4sSKpj31k5n/JPFq/AAGt7FVHbbms3u' \
			b'AGZ0rN3K3n5Sa5Js04kNfdy9bW6+MfMc78BCg0z3+pDtOtXFbwDLMZB8Heh2AKi9HlC9hwunIIjqbaCKG4N4QEsofF+XXmKTq8kxrupvY4+Bql/4728c5rK4mUAW4dj7+XrzeYrLxam56mH0hwdkDUQc9L0hiAcFzZ1vbmAsXw16+j7R04r6v2P0Wvz1jaZ3' \
			b'SvkgJuDhTovaoANu0EXb8OluA27BP4W75LOt1eCuhrXdAo74QJSTJHreddeCsrYx1NvTffncigPlrV6B7F5/uNAY6zBgT/uoRjxTLFQJU3T/eOibdYyD54t6lIvclPJS7qTqUgFWHAZr9NPdMWLrwAPkvD5G4Lw7Rux8e0y/QTLHiFSHiXgO0BzTHzhsoCwe' \
			b'9GiI6+4L/8kE0fqaNn4NBLZi1AcgkDY3tNabrJS2a5sX/CcnLjVZXf6xlaXfNYwsMsjcarbFoDauB8tgKUXKLPUReHDRi9xllz5XTVDIqX+7pFZRUqGEdG/SLTUcphruNmo4lg3L382lH27yq3bDH2bKpQT+1gePS/H1VUdnJbyzNun8ckF/sPP6VvDv6o4+' \
			b'VNUOq8oFTbUBmAX04fXL4EPNuEozSz827S9aai+dweTPH14eDT+1Fc6M/uip3E5p/vFxvpIK6SbKLN07xXTXxBdNfMs0uGKS+16+U7J4lZQujsbyjy+EAJwbfYCisY/h0fVSGRptuL2agTzXf6izdrVqN1Fqoct1FEnmcAPX8bdN0Xa9ivj2tURoyN3t9YtG' \
			b'/CaO+o9J5beSwKYf0W/sSIj+nehbSeHUTR1LoVdIETYRxKspB7RckUuOZTGDqTBJ/67ke7hOrqDY4W81Q911XhXFcMVQKcdC2k3nq5WZuv40LeTvVHa4IkrLoWH60PGKaJye1kIdL4MqFXlw7m4HhwvAnTse2TVPsK2PzKndOx5ZuOORtWr3jkd2zaPxZquO' \
			b'TZ+RuDeZdvyqzOoyIwc7lPVKshK6vVCCU/fkWAlxr9aflv4rh3t1vCFpSJa804NdU6TXLmDbM/s/5G/rkg=='

	_PARSER_TOP = 'expr'

	_GREEK     = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\pi|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'
	_CHAR      = rf'[a-zA-Z]'
	_ONEVAR    = rf'(?:{_CHAR}|{_GREEK})'
	_ONEVARDI  = rf'(?:{_CHAR}|{_GREEK}|\d|\\infty)'
	_ONEVARDIP = rf'(?:{_CHAR}|{_GREEK}|\d|\\infty|\\partial)'

	TOKENS = OrderedDict ([ # order matters
		('IGNORE_CURLY', r'\\operatorname|\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('TRIGH',        r'\\?(a(?:rc)?)?((?:sin|cos|tan|csc|sec|cot)h?)'),
		('SYMPY',        r'simplify|expand|factor|\?'),
		('SQRT',         r'\\?sqrt'),
		('LN',           r'\\?ln'),
		('LOG',          r'\\?log'),
		('LIM',          r'\\lim'),
		('SUM',          r'\\sum'),
		('VAR',         fr'\b_|d?{_ONEVAR}|\\partial\s?{_ONEVAR}|\\infty|\\partial'),
		('NUM',          r'\d+(?:\.\d*)?|\.\d+'),
		('SUB1',        fr'_{_ONEVARDIP}'),
		('SUB',          r'_'),
		('POWER1',      fr'\^{_ONEVARDIP}'),
		('POWER',        r'\^'),
		('DOUBLESTAR',   r'\*\*'),
		('PRIMES',       r"'+"),
		('LEFT',         r'\\left'),
		('RIGHT',        r'\\right'),
		('PARENL',       r'\('),
		('PARENR',       r'\)'),
		('CURLYL',       r'\{'),
		('CURLYR',       r'\}'),
		('BRACKETL',     r'\['),
		('BRACKETR',     r'\]'),
		('BAR',          r'\|'),
		('PLUS',         r'\+'),
		('MINUS',        r'\-'),
		('STAR',         r'\*'),
		('EQUALS',       r'='),
		('DIVIDE',       r'/'),
		('CDOT',         r'\\cdot'),
		('TO',           r'\\to'),
		('FACTORIAL',    r'!'),
		('FRAC2',       fr'\\frac\s*({_ONEVARDIP})\s*({_ONEVARDIP})'),
		('FRAC1',       fr'\\frac\s*{_ONEVARDIP}'),
		('FRAC',         r'\\frac'),
		('ignore',       r'\\,|\\?\s+'),
	])

	def expr            (self, expr_add):                      	             return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_mul_exp):                return _ast_flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2      (self, expr_add, MINUS, expr_mul_exp):               return _ast_flatcat ('+', expr_add, _ast_negate (expr_mul_exp))
	def expr_add_3      (self, expr_mul_exp):                                return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_lim):                return _ast_flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_2  (self, expr_mul_exp, STAR, expr_lim):                return _ast_flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_3  (self, expr_lim):                                    return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_lim):                       return ('lim', expr_var, expr, expr_lim, '')
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, PLUS, CURLYR, expr_lim):          return ('lim', expr_var, expr, expr_lim, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, MINUS, CURLYR, expr_lim):         return ('lim', expr_var, expr, expr_lim, '-')
	def expr_lim_4      (self, expr_sum):                                    return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER1, expr_lim):           return ('sum', expr_var, expr, _ast_num_or_var (POWER1 [1:]), expr_lim)
	def expr_sum_2      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER, expr_frac, expr_lim): return ('sum', expr_var, expr, expr_frac, expr_lim)
	def expr_sum_3      (self, expr_negative):                               return expr_negative

	def expr_negative_1 (self, MINUS, expr_diff):                            return _ast_negate (expr_diff)
	def expr_negative_2 (self, expr_diff):                                   return expr_diff

	def expr_diff       (self, expr_div):                                    return _ast_diff (expr_div)

	def expr_div_1      (self, expr_div, DIVIDE, expr_mul_imp):              return ('/', expr_div, expr_mul_imp)
	def expr_div_2      (self, expr_mul_imp):                                return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_func):                     return _ast_flatcat ('*', expr_mul_imp, expr_func)
	def expr_mul_imp_2  (self, expr_func):                                   return expr_func

	def expr_func_1     (self, SQRT, expr_fact):                             return ('sqrt', expr_fact)
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_fact):   return ('sqrt', expr_fact, expr)
	def expr_func_3     (self, LN, expr_fact):                               return ('log', expr_fact)
	def expr_func_4     (self, LOG, SUB, expr_frac, expr_fact):              return ('log', expr_fact, expr_frac)
	def expr_func_5     (self, LOG, SUB1, expr_fact):                        return ('log', expr_fact, _ast_num_or_var (SUB1 [1:]))
	def expr_func_6     (self, TRIGH, expr_fact):                            return ('trigh', TRIGH.replace ('\\', '').replace ('arc', 'a'), expr_fact)

	_trigh_rec = re.compile (TOKENS ['TRIGH'])

	def expr_func_7     (self, TRIGH, POWER, expr_frac, expr_fact):
		is_inv, func = self._trigh_rec.match (TRIGH).group (1, 2)
		return \
				('^', ('trigh', func, expr_fact), expr_frac) \
				if expr_frac != ('#', -1) else \
				('trigh', func, expr_fact) \
				if is_inv else \
				('trigh', 'a' + func, expr_fact)

	def expr_func_8     (self, TRIGH, POWER1, expr_fact):
		is_inv, func = self._trigh_rec.match (TRIGH).group (1, 2)
		return ('^', ('trigh', f'a{func}' if is_inv else func, expr_fact), _ast_num_or_var (POWER1 [1:]))

	def expr_func_9     (self, SYMPY, expr_fact):                            return ('sympy', SYMPY, expr_fact)
	def expr_func_10    (self, expr_fact):                                   return expr_fact

	def expr_fact_1     (self, expr_fact, FACTORIAL):                        return ('!', expr_fact)
	def expr_fact_2     (self, expr_pow):                                    return expr_pow

	def expr_pow_1      (self, expr_pow, DOUBLESTAR, expr_func):             return ('^', expr_pow, expr_func)
	def expr_pow_5      (self, expr_pow, DOUBLESTAR, MINUS, expr_func):      return ('^', expr_pow, _ast_negate (expr_func))
	def expr_pow_2      (self, expr_pow, POWER, expr_frac):                  return ('^', expr_pow, expr_frac)
	def expr_pow_3      (self, expr_pow, POWER1):                            return ('^', expr_pow, _ast_num_or_var (POWER1 [1:]))
	def expr_pow_4      (self, expr_abs):                                    return expr_abs

	def expr_abs_1      (self, LEFT, BAR1, expr, RIGHT, BAR2):               return ('|', expr)
	def expr_abs_2      (self, BAR1, expr, BAR2):                            return ('|', expr)
	def expr_abs_3      (self, expr_paren):                                  return expr_paren

	def expr_paren_3    (self, PARENL, expr, PARENR):                        return ('(', expr)
	def expr_paren_4    (self, LEFT, PARENL, expr, RIGHT, PARENR):           return ('(', expr)
	def expr_paren_5    (self, IGNORE_CURLY, CURLYL, expr, CURLYR):          return expr
	def expr_paren_6    (self, expr_frac):                                   return expr_frac

	_frac2_rec = re.compile (TOKENS ['FRAC2'])

	def expr_frac_1     (self, FRAC, expr_term1, expr_term2):                return ('/', expr_term1, expr_term2)
	def expr_frac_2     (self, FRAC1, expr_term):                            return ('/', _ast_num_or_var (FRAC1 [5:]), expr_term)
	def expr_frac_3     (self, FRAC2):
		v1, v2 = self._frac2_rec.match (FRAC2).group (1, 2)
		return ('/', _ast_num_or_var (v1), _ast_num_or_var (v2))

	def expr_frac_4     (self, expr_term):                                   return expr_term

	def expr_term_1     (self, CURLYL, expr, CURLYR):                        return expr
	def expr_term_2     (self, expr_var):                                    return expr_var
	def expr_term_3     (self, expr_num):                                    return expr_num

	def expr_num        (self, NUM):                                         return ('#', _fltoint (NUM))
	def expr_var_1      (self, text_var, PRIMES, subvar):                    return ('@', f'{text_var}{subvar}{PRIMES}')
	def expr_var_2      (self, text_var, subvar, PRIMES):                    return ('@', f'{text_var}{subvar}{PRIMES}')
	def expr_var_3      (self, text_var, PRIMES):                            return ('@', f'{text_var}{PRIMES}')
	def expr_var_4      (self, text_var, subvar):                            return ('@', f'{text_var}{subvar}')
	def expr_var_5      (self, text_var):                                    return ('@', text_var)
	def subvar_1        (self, SUB, CURLYL, expr_var, CURLYR):               return f'_{{{expr_var [1]}}}'
	def subvar_2        (self, SUB, CURLYL, NUM, CURLYR):                    return f'_{{{NUM}}}'
	def subvar_3        (self, SUB, CURLYL, NUM, subvar, CURLYR):            return f'_{{{NUM}{subvar}}}'
	def subvar_5        (self, SUB1):                                        return SUB1

	_partial_var_rec = re.compile (fr'\\partial(?={_ONEVAR})')

	def text_var        (self, VAR):                                         return self._partial_var_rec.sub ('\\partial ', VAR)

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
			self.parse_results.append ((None, self.pos, []))

			return False

		if self.tokidx and self.tokens [self.tokidx - 1] [0] == 'LEFT':
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
			self.tokens.insert (self.tokidx, (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.pos))

			if self.autocompleting and sym in self._AUTOCOMPLETE_CLOSE:
				self.autocomplete.append (self._AUTOCOMPLETE_CLOSE [sym])
			else:
				self.autocompleting = False

		else:
			self.tokens.insert (self.tokidx, ('VAR', '', self.pos))

			self.autocompleting = False

			if self.erridx is None:
				self.erridx = self.tokens [self.tokidx - 1] [2]

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
# 	a = p.parse ('tan^{-1}x')
# 	print (a)
