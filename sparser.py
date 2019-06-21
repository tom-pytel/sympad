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
			b'eJztXGlvGzca/jMLxAIoYHgOx9+cxM0a68SpY3dRCEaQNs4iQJMNcm2Bov+970XOIY51WLKseiF6eJMv3+chh9f4YPbo9OT5I/Xo1SU+n5+8uHyFvh/PL8A6fYGPs2fwvDg/efZPjPn5+cufwT57eXx+dHF2jgmOf8DEj4/Q8/Lo/PjFKThOnr04Oz9+/eTy' \
			b'/BTT/3B+9EQsLbYBm6Ix+Quq/ycq4x/XH9+muFwmOh5Drn8dX6ATxcFaX579+5jSnJLgT56eYeirCyro1eVjeD49u3x8eixBlJ4kOHoC4p8cYeVPT346eXrcVnDKeTHZy/OT58dY8sUZPI5/vDw6Rd+Xb798f/MZHF+vf//6mp3Xv3/6/Prjtw/J+fX6c3Z/' \
			b'evP5+mPyvPnlSw7/7/+S892bX79m97ePvyb3h2+/vX7/4VPyvn3/vXW+e5frvf7Pm6/vv1/nEj6/ySV8aWXqSPrb+w/dKsCR5Xv7VpyPrtTsYKrV1EwU2F4dNEpXCkKMBcckhXJYGzDVAV2G/gz47aTjb73gALuB9BXlrPhhIUbriQShE12WH1YiLEQ4dNVQ' \
			b'P3pq/JukENfxac82hmBWkAMzsBTss5ZaZXrBrufzykRFpXTDbD9RGPiMG2YJyla9gH507PrQCS6nDiqsXEPpUGMgUaEQNxmNdaj2xWl6SaYEmqU/E1K4+OvWPyW1a80PkHMyaZ3giuoARG8m7AYHxkLdrPwA4GiqX4AMxCotrOqEggK0tDWFTbkMxw/TtLW3' \
			b'QWY+EEHohdgqeadMDqyuo6BaVGyzekYSCL4pzTRSsUjAnuSQxCeHpjQefY2y0DkkkYRMsVo/6aUZxIsXfNSNoNdkwSSyDYMaS2Hoa8MtIwowxAl0+VmltPIqqBq7InQNIDnkBN2CPqxWrlG+Ul6jGmxUUdGoYIlYUDZi3ZByqEchqEzHgDQCpAFY55TzygXl' \
			b'auWgaGUVhFTKQekQC6MLGAc9F+X1RnmrvFPeKw/eWvmoPEjTqOCukNowQswAHxwoPD1BEGwJdC70QSvIshJqKXjncoNaSXBEBcQD/ZKUlUjpSeq9QsJbboLmhjlukecWHTiO9QyUjZyIG99Io3XFkQTjTkAJwiamjibxNl8PoC4V6NTyZms1sU5NqslwdzAM' \
			b'h3Fbq9dvreSwrZI168Y5tng0cYGtWngszJWkSa1277qrjD+u2j/JjfRSUvqi1Dr1abdUagbdi3a8eJkDnnut51HLU58NlQpaBaOCxQGEB72QsiuYFO2DTmc4Xd0XUUFKkPV+i2jvuYg4DTIy/zA8/zA8/zA4ynnDsY6DPQfPDsi7Q6E9i6VJ+M7rkxqxV4MY' \
			b'FMlNafpNQREmK74QqaitvGrNQDi7unBua8L5gXCh73dUM77GzU5mkzOcOqymLpxlcK/cNz7PcCq0ZzIfWCZIJWPdHipdUxMWjjWOW+i5x3giWW/iMsMpjuG5DY/0gdcNgddrwfDsN9g0sbGFpXUohKLXstfK+8by+8by+wasgdi8mjSc3nFCP5YQ30l2p4tG' \
			b'HaVlJOJWRjpNTewOw9uqyXVrwiGUQSC8dzLXZ04xhxzrwbKnYoujNAd6JqYPLHegro0kNkxiM8IhYKVjVjpmpeNXCPt98mtKtqVluhtA7LpAeJaPnlgDtxytUElbWTmB9DHo3NA8z83z3Dy/bwOdY9H9HoquWfkJSkM+KMozeI4J6hg7J2NkYLgCwxUSGwPr' \
			b'INBYTCVR6vperzVm2JKaW1KnltTckppUAjJyeyOnijLyx3veLk+irqqK5p63CsS63yIiNZoJ6/+eS4r7+pVs7FeyHV5RH6jUDOgPEkLFKL7BgYwFZdmhiFwr9nkLJapQqwCdB3JqVVtVgyK8aoJqUHooG5uAkuGuF2794r4vtgzlQBmsgbqDwvMiKA9tOqzy' \
			b'4Hfw16gpVDvFigY/Oi/zeJYVId6CTUeUYGNeSQPD2RTGsim+eNLvCse+3bUVE1bUWnGNtJdj582idkuqTsv7BVzRaxuajzzypIRGiNblEe5gMBPrxOcblQQ0BG5mtiMNfZrRVPziL6nQqRpkgHdnjeqMWkWnYlARxALtGtXYjo4rbAvqDbXT1TmEo+wo/Jz+' \
			b'IQ4PFXo4aMQC/rDrQJz1gAt1KTw+hRBH+Ewh3dShZsGG5uL5MaoWT6zxCBrPxLHN8MTHCI7pN8VjWjxhhV6PqfGMGQ9QoRC8lAAdPkL52MU5+RzMCo908TaCFdAxN16HQAHwD6PBqnp0wBPVqcFw8CNOVDaUicLrHk9QS5ghJhFwtgl+bAsylqhjkTqOaIOq' \
			b'X48r9VpcGfAjbowic120VmyIBTjA1nOoY5Cj51j/rXsmQU855rGn4rrJC72cTspbwCnLUpinIouo9+VEiN1DgLhRbDLEzTzEDUHcjEPc9EyGuClD3DDEOXkJ4n6fpizLQSxFliHuyXlF9xL+/hDTpRK6UyQQm/mxm24c0XME4lyIFCUQU455iKm4upO8ADEB' \
			b'10JMWZaCOBVZhLgv5xVdOnkAEGvFJkOs5yHWBLEeh1j3TIZYlyHWDHFOXoJY9yHWS0MsRZYh7smJENcPAWKj2GSIzTzEhiA24xCbnskQmzLEhiHOyUsQmz7EZmmIpcgyxD2DEMeHALFVbDLEdh5iSxDbcYhtz2SIbRliyxDn5CWIbR9iuzTEUmQZ4p6cV3TZ' \
			b'rABx3hkYbAusjThvCNRL424Jen8z+npTDAiKTWZAIAYYJkGORn8iRCBCjO8XdDNRcUKIkAlBpRu2hBaBadFWVqCFiKXZEnKEMXKYAj+k7DI/emLTXkWVVuvupvX6GGPCKiv4lXjjl1jNr0UjvwKVllna0ziCa3vDy3tTj63vDS/00DKUPJvEuyDXzzlshHrd' \
			b'fFYsoV+7/KNKDFtCP14EcsaGoxZuA0g1CHvd8nF0bWjqHh9RscRJEa3MyZp2Bdo2OZG+3RlQf2h/iLsjUR9Omz/5eGGFcW15lu7b0NYoNnlo44UmWrz52KZIFOOPCeSTghGKNf2siV7t0tPwG48soRcvQDv1FUY3yajZEjaNLkNNMz+6SdllJvXEptHN/P/1' \
			b'Z+nbDtuuVC2vVNGCxDmavtVhjtC3IBxQJkg3k20XrrZduFLphi0miOXla6eyeYJIDN4AqDJB7OgilhL1CZLKLhKkL/YVH6TfBUFKZyadQ+sdMiUO2aIVm8wWXvSihWzRrclsoTWwHV8DdzPZdg1s2zWwRCBhxCWcYZ+ru7UWaCOZxBLajC6MKdGANlJ2mTZ6' \
			b'YIg5xY3Mh8wc+rTQtgstywsttJA5tjWZObTusuPrrm4m2667bLvukghjskuYwz5Xd2stMEcyabaEOaOLMUo0YI6UXWaOHRhiTnF/9CEzxyk2mTmOmeOYOa41mTl0LmbHD8Zs32TmtIdjEmFMdglz2Ofqbq0F5kgmzZYwZ/SkjBINmCNll5kzbAIxp7jtupA5' \
			b'dFUg3x4apZBrbwGsQ6TY4ZLZJZ1geaja0zVec/GSK/0Si2ipVaP0vNyqi1TK+UD0SrWrrXaxRW7QPdtMI3K7bp0th5qWRpxFq3Z1Nbq4qucYxOUW+dNWTKduuribu5A5y9BmI4RZhS2gvQ2PP7Vik8cfJo1l1tiOyeMPUSeFcdLSKDTInUahljoSgaOQuGQU' \
			b'Yp8bVl8YiCSfZksGolEW6arhhIPBSMovD0b1wFzx56L3nVKRWFXtjlhRscnEikysyMSKrcnEikQsCeOkJWLFfu5ErNgSiyOQWOISYkkdw+r7xCKZTSce6RVbesXR95wkH7BLKimzKw4MsatRM75DtOgGUSxMjdr7QoMTCbPJC0JjdHCyU9jdJeQtwmma5Cx3' \
			b'+Wc6Pr/pXvgpnUEgwNu65TOCI+7i4ebd4E4PZL4lkn5zYLob8KwiDY5FXHFcw4EN7zgkjPGbb7x5cSdY181W4UYF3HgDRBRRgL4dAm2mQRoGS3TQ2+rYYVN9O+xJ/25Ka9rbd3Fs8Brd3OxmwDYPcMzGWcr2x227+zdwpRr9QDAd4skHldvA1S3GVd/LyRW+' \
			b'gAlYuwlw8Ra/3rNpFl44pzuXCG0BXvWHcYfAWjwiBQl33n/X7blmBGBEZS967/q9VlPV5Z4bQAN7iWcJS2z3ToHEzQZ998uh+m8Fotk1iEaRDHcMYsTPyjRdiOb9nBrXUA1qhLbRQR+14d1jA+aKv/ec8U7ZzRgvRLfZAJz4spQ9KQQHW7wAm5VGSLM5CHrv' \
			b'NECg1eHNk5Q7USPORQaqBD2ExUzflTZxo7KvUX0/Wen1MiOG5ysEvmPGVJhiRxWYErD60Fnioo6HiLJrDhFDbw4RQu8PEUWPcaAfiMMP7kDHAFsMh4gcaOAQIQItHCJMoAHIGv/k/yAiECz5FlgSjk0M+x1ESK8rjuerzqw2O3pf8T9imWmg/Ew+MHT06c5g' \
			b'zAa5a8ujNaiODulB9JmkIoX2dVJXlBr0SHIPqgw5a4JDzheaOdWKonpKkHOa/ne2VHA9UrCuqpVKHmhJ/vU1fbTMtwa7HyXL8Qd+1oZbsXgxN+C2iyzOXdoYRQmnZnEp+G+xBz/KartZ+TioXIBV/ONpjm1/VIybL2b+Q+t8pFO8MQd9Kv94FtUNKU2EJvRf' \
			b'iuU4DIGo+2dgdTr6ssODLjzi4sMtOtmSM63OgRafOssJlseDq3RMNdeG4fET/kOA9X7IVOBU8uLW+NyPGh1ur20Ymhb/qLJ6oYZX0W1Xpcvpk84AVzPR0tMnb7NcRrxkLh5qeby9mnF8X8dQ/fkrkltJYNO/k1jZkBD8qcKtpXBqXcNS6HEpmHPLCuLVmIl6' \
			b'NCoZlsV0esSoOFWf83GRXEGxcVFl98DAlKKXDCcRhXQspF2j27rUYZfvrb02RJUNzpU6E6VuVNfwXGkYnmZJkSdIhYzcRnf3bTT03/63b7iBi99um2+gV3diuIFhBw2M6k4MN3Dx23Ot+cnqr1Fc0dxo+BrPwmRdA+ua5VKyLuK90YVXuzOsi+bezVtxjbN7' \
			b'w+uZisTJK0VYdTV0HQRWTZO/AKortNU='

	_PARSER_TOP = 'expr'

	_GREEK     = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\pi|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'
	_CHAR      = rf'[a-zA-Z]'
	_ONEVAR    = rf'(?:{_CHAR}|{_GREEK})'
	_ONEVARDI  = rf'(?:{_CHAR}|{_GREEK}|\d|\\infty)'
	_ONEVARDIP = rf'(?:{_CHAR}|{_GREEK}|\d|\\infty|\\partial)'

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
		('FRAC2',        fr'\\frac\s*({_ONEVARDIP})\s*({_ONEVARDIP})'),
		('FRAC1',        fr'\\frac\s*{_ONEVARDIP}'),
		('FRAC',          r'\\frac'),
		('OPERATOR',     fr'\\operatorname\{{({_CHAR}\w+)\}}|\\({_CHAR}\w+)'),
		('VAR',          fr'\b_|d?{_ONEVAR}|\\partial\s?{_ONEVAR}|\\infty|\\partial'),
		('NUM',           r'\d+(?:\.\d*)?|\.\d+'),
		('SUB1',         fr'_{_ONEVARDIP}'),
		('SUB',           r'_'),
		('POWER1',       fr'\^{_ONEVARDIP}'),
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


	_trigh_rec    = re.compile (TOKENS ['TRIGH'])
	_operator_rec = re.compile (TOKENS ['OPERATOR'])

	def expr_func_1     (self, SQRT, expr_fact):                             return ('sqrt', expr_fact)
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_fact):   return ('sqrt', expr_fact, expr)
	def expr_func_3     (self, LN, expr_fact):                               return ('log', expr_fact)
	def expr_func_4     (self, LOG, SUB, expr_frac, expr_fact):              return ('log', expr_fact, expr_frac)
	def expr_func_5     (self, LOG, SUB1, expr_fact):                        return ('log', expr_fact, _ast_num_or_var (SUB1 [1:]))
	def expr_func_6     (self, TRIGH, expr_fact):
		is_inv, func, func2 = self._trigh_rec.match (TRIGH).group (1, 2, 3)
		return ('trigh', f'{"a" if is_inv else ""}{func or func2}', expr_fact)

	def expr_func_7     (self, TRIGH, POWER, expr_frac, expr_fact):
		is_inv, func, func2 = self._trigh_rec.match (TRIGH).group (1, 2, 3)
		func                = func or func2
		return \
				('^', ('trigh', func, expr_fact), expr_frac) \
				if expr_frac != ('#', -1) else \
				('trigh', func, expr_fact) \
				if is_inv else \
				('trigh', 'a' + func, expr_fact)

	def expr_func_8     (self, TRIGH, POWER1, expr_fact):
		is_inv, func, func2 = self._trigh_rec.match (TRIGH).group (1, 2, 3)
		func                = func or func2
		return ('^', ('trigh', f'a{func}' if is_inv else func, expr_fact), _ast_num_or_var (POWER1 [1:]))

	def expr_func_9     (self, SYMPY, expr_fact):                            return ('sympy', SYMPY, expr_fact)
	def expr_func_10    (self, OPERATOR, expr_fact):
		o1, o2 = self._operator_rec.match (OPERATOR).group (1, 2)
		return ('sympy', o1 or o2, expr_fact)

	def expr_func_11    (self, expr_fact):                                   return expr_fact


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
		n, d = self._frac2_rec.match (FRAC2).group (1, 2)
		return ('/', _ast_num_or_var (n), _ast_num_or_var (d))

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
# 	a = p.parse ('\\operatorname{test}x')
# 	print (a)
