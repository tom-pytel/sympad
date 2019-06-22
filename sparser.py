from collections import OrderedDict
import re

import lalr1

def _tok_digit_or_var (tok, i = 0):
	return ('#', int (tok.grp [i])) if tok.grp [i] else ('@', tok.grp [i + 1])

_var_diff_start_rec = re.compile (r'^d[^_]')
_var_part_start_rec = re.compile (r'^\\partial ')

def _ast_is_var_differential (ast):
	return ast [0] == '@' and _var_diff_start_rec.match (ast [1])

def _ast_is_var_partial (ast):
	return ast [0] == '@' and _var_part_start_rec.match (ast [1])

def _ast_neg (ast): # negatives are only represented as ('-', ast), not like ('#', -1)
	return ('-', ast)

def _ast_flatcat (op, ast0, ast1): # ,,,/O.o\,,,~~
	if ast0 [0] == op:
		if ast1 [0] == op:
			return ast0 + ast1 [1:]
		return ast0 + (ast1,)
	elif ast1 [0] == op:
		return (op, ast0) + ast1 [1:]
	return (op, ast0, ast1)

_diff_or_part_numer_rec = re.compile (r'^(?:d|\\partial)$')

def _ast_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
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

			# if n [0] == '@' and _diff_start_rec.match (n [1]):
			if _ast_dv_check (n):
				dec = 1
			# elif n [0] == '^' and n [1] [0] == '@' and _diff_start_rec.match (n [1] [1]) and \
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

def _expr_int (ast): # construct indefinite integral ast
	if _ast_is_var_differential (ast) or ast == ('@', ''): # second part is for autocomplete
		return ('int', ast)
	elif ast [0] == '/' and _ast_is_var_differential (ast [1]):
		return ('int', ('/', ('#', 1), ast [2]), ast [1])
	elif ast [0] == '*' and _ast_is_var_differential (ast [-1]):
		return ('int', ast [1] if len (ast) == 3 else ast [:-1], ast [-1])
	elif ast [0] == '+' and ast [-1] [0] == '*' and _ast_is_var_differential (ast [-1] [-1]):
		return ('int', \
				ast [:-1] + (ast [-1] [:-1],) \
				if len (ast [-1]) > 3 else \
				ast [:-1] + (ast [-1] [1],) \
				, ast [-1] [-1])

	raise SyntaxError ('integration expecting a differential')

#...............................................................................................
class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJztnftv20YSx/+ZA2IDS4D7JvNb0rg949IkdZMeCsEI0jY9FGhzRfq4AkX/95uZ75LcXZGy5MiR7BpmxOVyHzOzHw73JeVk9eD82csH6sHT88/p88tX/Pn5+bNXX/LVFxdy6xl/PP+MPl9enH/2T77z9ecvvqbz8xdnF49ePr/gBGefcuLHj/jixaOLs2dP' \
			b'KXD+2bPnF2evP3l18ZTTf3rx6JN00uls6Cy3Ofkzqf8rKeMfb999N9wby+TAY8r1r7OXHGRxuNYXz/99diHyP8Ynl/7k+avHT8++fAmJOIXU+egTEvj8EVf35Pyr8ydnXMmT51zMkPapqJ/q4YQvLs4/P+O4l8/p4+yLV4+e8tUvv33z+5v3FPj17R+/vkbw' \
			b'7R8/v3/97refhuCvb9+P4Z/fvH/7brh4880vY/x//zcEv3/z7a9j+Ld33w7hn3778fUPP/08XH73w+9T8Pvvx3rf/mcI/jKJkAn24w8/5SVSYBTnu+/Get+/Gev94d0gzoNLtTpptGrMqaJzUCe6VZqutTKOAqdjtMRNEY2OHHLyzzrV+NPserqkAGdoKYOW' \
			b'kMaH5fLMaRVl80gOcsjhw7an6bLRUqglqfii43+nQ4zPrnTAmWM4K93nDPZ0urJedLVFtC+ugjKkr63jYhFRXxlfZ6G4vojoiqviHmnJIaNO2lR5Kg/GyeP7MjLOpYx1sjHcSD3cvlyeJi2islFMQg0QThfvem70q9MUSRppBS//rBni07WdrhtpNm3wMZoF' \
			b'QQr16oRNBB56CfH9XqVmjiSMEQkSSxFYm4R1Hm1FZFZ3iGukDu3xYbJWmqLseiRbvYzph8sGHHbqxGQ26pKVuWmg+VICNOiQpumlWEpcSk534hDQkiZyE7fKkuVTohRDlxR7WqSp7qdLuhJQ6BEdBUs3pziqcS6Or6Z4I8JR4SQbOZ0VBVh128pzbxgAIsqr' \
			b'oEj1XrlWOc1PJ0lvxRg+KB+V75RzynnVKWpv8VXOKGe5QiKAyue6DD/R3NKe7cn8d9z81NpeK2+UpwBVRnepKam4qByV2ytPBZLb8+Q5WAnfq9CqoFUwKlgVnAokYFCOhNSX/CCxT9P8uTohZfjKItJqnAxOlk+3XV3fQlMSnJXy8kk5uT3JvYmiMIJrU6yT' \
			b'pMcgvEvNZCG2DTjFJKgXwW8/kiHh10FbDzU91DzxHZrH4y6u0GR6aDINcp2Qe5CWspBOQzzdH0gQeqTbw1WNVjAmtYqxuMajZ/zhBAuHqzoerurE4tAcGs3h0UoeXt6nSJcetvSU4abrUlZ7NxyNg3Iu3hF1+uR0RK+rUuuYUvutUsMJh/QGCgAigJaAJzqk' \
			b't6kkDVGFToVexZZFQ/Y49TMM+hl02kVFahYjb0CNAsiyePXx5S1ppxWPvG6RtFYa69ildO3xS8ldSZM6cAYdOIMOnBFn2+OuR7SPCW48LFoUPKDsBmJ0EFKLVLffaZoW+hi9oy9accfGHKZ7aZIbNG53of3BhAbWXD66IYAdntwfypYr7vLs+Bby6TE2d+IR' \
			b'WHG/7i4ociINyd05aR13NzyU9OfMFj00D7UD/HSQTEUvbMX9NYOOGt4sATMeASOD0KPTH9uxl2bRS7Po9Wu+3q3vYDjLrW8BD0NUE0NhJpYvLS5tetNbvOkt3vR0qmqBS+mR3iOhX0rIvQF7yKmNFXdE7CE7IjqZygDHQ7zJTJLAHUwCYOV1osYcShAqhgUx' \
			b'gLID5biIOIFXLaZi52QxbhS5A/oCocNJHPYs9ORB3K6up+Ust971kOi3Xw1+D7jkDh3coYM7dBi+49oP11ra7qBODsAd4tGWBmff4tAvlivYo8NJZOOHBw8RnrogD1r1widu/B2gp2Ut+FHwCSIPiDwg8neim+ehj78b+vAT5IVcD3I9kHXw9w7ECttUUGrW' \
			b'gGYNaNYw+IYAs/A1ZxogiMc+37NiZSKUiYMyEcpE6SySmFC5Q6ou9QG741fNi7S7WqM/fsVIsqOXkhnpT9EKxy8sL1S3aaW6TUu5rTwPrVqRj0sCssfT7OhGXeDrqP70TjMqOhXpyaeCO9Vp1XFJJElLorRcCykr22QojpfaWB/ev8CbF2xHNZIj5Z0vocVZ' \
			b'tp8EuuYtPnQmiZuolU1/svOF1GlInya2simMN+twDG/+sWr6a8i5NSRnE/pL2VGxhWZoIqqULLs3Lekf3ef1cV7Y4jU7z32BXvEfay7nBc376q+2QL9mgSztZIEp9lLeAUdmC176lIPNkUILBhmTVkdtGL3ORp0jM09561IGTWIjvOW7ZCt+FrPnjOfexyd1' \
			b'7B5stCS/eLPnmJ1DXz6mcdnURnVWdU51ns3eUWtSc3vVk+9hCUm+1sy3BkvNMrPQ7HF4K0DeQrzRiHcZ8RajtdZi52LKVuOlTXY6vFjNK9XeUivSS5Rs3rKyvM2LukRRGrThbWfkABu+wTvJqEUdbyeUfXB0y3NCxx8LjR7TX0Om7KlAZ2SPpuwlo39cFm9I' \
			b'48xG9SyFG3JUWPA9xfsGSbOGNBNGeCMjlcib4kihhlqHN8e5WNCD0rDRrTG8C5W3OvZjPVwIRXQFV2wuSsqdIyTjDgddswB8FRk1N6AWB8xi9lpYfydsR1qNWSek6a1hA2DkYYxg5gbS4naw+Q8Abs099GwMRiuFgoQYIkSMR86UpJDPJVdS5U1USTGowFic' \
			b'JrhEDpdlqt0OHHImEPIktuT2LF6lFiViWW2zlJWKXMo+unukNiLFZmgFqRQKOBFSpi2OHClJIZ8LSNV5E1JSTCrN4jQhJXK4LFOFlIGXygRCnoSU3J5FqtSiRCqrbRapUpFL2ZR5j9RmpLDB3aMrr4EUXnWIGI8CKS1I6WWkqrwDUhpIaSClS6Q0kBoz1Uhp' \
			b'IDUJhDwDUosvwVKLCqmptnmkCkUYqXiP1BVIGTaDIIVQkJAgZYqjQMoIUmYZqSrvgJQBUgZImRIpA6TGTDVSBkhNAqVTQsosIlVoUSE11TaPVKEII9XdI3UFUla+mcRIIRQkJEiVR4GUFaSWh2V13gEpC6QskCo76iKHyzLVSGEIlwmEPANSdhGpQosKqam2' \
			b'eaSK7Jeyl/0eqc1IOSUGblUKBQkJUq44CqScIOWWkaryDkg5IOWAlCuRckBqzFQj5YDUJBDyDEi5RaQKLSqkptrmkSoUucTewXumNjPVydfkmCmEgoSEqa44CqY6YapbZqrKOzDVgakOTHUlUx2YGjPVTHVgahIIeQamukWmCi0qpqba5pkqFBGmZIbTjHNW' \
			b'ccOs1SJn3UbUzFVTWZuBa7eb07oWf3qeQR4QjxzSPf6myUYefcbkNnNe8v1b+b6l54kuJ19m7GXyy/Rzs18G8xa84z47cohDSoTv9s5z3NiyCJ4YM9MUhsEUhsEUhimnMAymMJCRrWrWpzEkTT1PlkmLUgbCFyc1UnJrxowT5Wx7IZ0TsJn0kGiGeLFlSusz' \
			b'QXhrdl/Mp6k/dXzIU4xd/7BhOhxdtX9hh+tuTnfzw3A3/a7F1+g9tMYg1mIQi4jxKJDtkQhfwV9Yw6myJ1QtxrEW41hbjmMtxrFTpnr9B+PYTCbkSWDaxXFsqUjperPaZl1vqYi4Xnv/Or8CKyPfzmesEAoSEqxMceRYSQr5XGKqyjswhYGsxUDWlgNZi4Hs' \
			b'lKlmCgPZTKB0SkwtDmRLLSqmptrmmSoUucQGvb0xpTdiFQey5paMF/lqr4tYt2fMQo2alR9+YNQQChIS1MqjQE0GuHbDEvR69oE2jHGHMqfSM+aSTC7LXWOXkvS5fAanRN7ieHdNrwq+qc55+OoShL89LiH8vfjz8gMwzB9CQULCny+Ogj8v/Pll/vxa9oE/' \
			b'D/5SmXYMZfwlmVyWu+YvJelz+QxOiT+/yF+tV8XfVOc8f7Vqwt8e1xv+XvwF+XUWLz/SwqGAn2th/kJxFPwF4S8s8xfWsg/8BZV+EkZCdgxl/CWZXJa75i8l6XP5DE6Jv7DIX61Xxd9U5zx/tWrC37UXJ4btofkmsFkQeeOW/gAcbUZkPG4ouWAst6ZQwMnZ' \
			b'FDEexQq+LLdqmTfQWHSV08xSfllIF1TXIXta08cC7FCFHUPZyn4S0ZXiZJjqNmKNP6Xsc6kh4bDMv7gmu6ZttdI/1Tu/0t9WxyW+AnxNVLfjdD+Efgie8WP4zZ61F7+JUJCQ+M2+OAq/KTM1KV5HnGa8Z79WyOA9MVUzlGzHUOY9k2SuLKB2oClVIajBKTnQ' \
			b'5c0nZkbJyolO9c470fq4xO/s3CYyg8DZHSefrD1caAoFnIhP1xZHzqekGOJJFjfvP6sS3OQ5HTznULIdQxOfg2SuLKDic7rh+0pcgxModYu+c0bICtKs8llI10qQ3bCtWplpo+fGXZ5M5+y8eDeAWG3ojCVnu+/gHGe2a5aG2ewNs9gyg91XM9aNzueqeaJ6' \
			b'yz2azfJSXSPD4WmNbm5bJvNRM3HdvZiNzKSst/8wkbxhCrmRYUyo92BSQXuBoN0rB3ZLFox48M1MuMQF3ed9/yMfVraoflxOunijqGjZhHQ1LoNxNmDDdmrEnuyX9YjQ4JvnUDI360/0jbiU9ha7FdbwJl2LlvWKD3Iv9pDvGH3/mllngXtoh3nVuCPpb/Q8' \
			b'nmzveZj3Ddg70H4kJvzVTJgtsLDbkhH7j9oZDYkMvQ86AoY4DMLVfHTttRDh8dxH7p1qGdT1MvSbw0T9acJDeip4LwNJv+Kv+mnZkm1lmBa5EdiYPEjG1GLkiUH5AhWHLvFrX6vZPJaHzrFDag5J6o7uMI6bybvaD8Ut2KqZmh0gMyseg19hwF/JwE5+Ybv2' \
			b'rdt1drBZtlc/GPLKp3jLh3dvFuWnMrNqwM4O1mOzYbvdbMuTI3u1L0+TFDYm1Y4X1uC2eqEdElb/kBr+L/yuBwy5ZX9kq57Ili+YuZfLVbZlzXbsOOzcYdja98/5/XmT4/dyydLX7Qbe3JzT1q2w9DrnWcqwr17eNV7fTn7s4Bqv7q2bb6knR3a5u026t477' \
			b'dZo0Sv2HaFLHTXr94dpxNGq7qWH3OSj7mPPA27ctT3Quta/nr5iTKbzsPLHct0bvWBqmfOlEnxacAySvHHoc8w7tOrWWqd9fIVkst8S4IhfXyu42lG13Krt6EaX/sGsla8r4PZD8Fz/SmhUv4/MEN+/j1zKpNMwf2GFamcVspl8XWS+q02rmF0IuZfBLPePi' \
			b'T0abw8iSd30r2RjZpM22WFGMa2uJUufMOqFPy4NpbRBLgqNcWAAc1/0cL/fNrukVv2uyuFan5v+o455f9jzk71O4S5FcW56Ia1z/428iSEhM4q5jcjLI8p8U66tiYdKtCifbpj/4tbD+J1WE2SrWf3VmviI1v9uYnGn+B5c68zfnEE/l/6i6mjAr29525Sza' \
			b'bK25WwfuQ6CTyZmbPgx8TRXNC1DbliAW7m6i2Vm4PRwiYH8jAjq1j0MEHL5CGPcto+eujVx+4AEx9Q2JGdSeDohpNotpakn7dhdho9pwkBOoI7mZN+WBzFu9CNe9Uzf4pUydNUe0jQMqVOzUeKz3dvO7+TH2cKvs8tW9rGM7xnPvdr4smMQdkUl4VHCwA+bw' \
			b'x2QO+T9PD3TAHOGYzBHV4Q6YY5tuzscyB4+cD3bAHN1H6PXta4Bh5T9I3nxgj+M2KfODJxh2zVMesGZ/m6wp/73wUR4YUbe3ckDCM2DHfsC+WoQdF0NjwMwKs3x5+n8zGrKJ'

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

	def expr            (self, expr_int):                      	             return expr_int

	def expr_int_1      (self, INT, SUB, expr_frac1, POWER, expr_frac2, expr_int):  return _expr_int (expr_int) + (expr_frac1, expr_frac2)
	def expr_int_2      (self, INT, SUB, expr_frac, POWER1, expr_int):              return _expr_int (expr_int) + (expr_frac, _tok_digit_or_var (POWER1))
	def expr_int_3      (self, INT, SUB1, POWER, expr_frac, expr_int):              return _expr_int (expr_int) + (_tok_digit_or_var (SUB1), expr_frac)
	def expr_int_4      (self, INT, SUB1, POWER1, expr_int):                        return _expr_int (expr_int) + (_tok_digit_or_var (SUB1), _tok_digit_or_var (POWER1))
	def expr_int_5      (self, INT, expr_int):                                      return _expr_int (expr_int)
	def expr_int_6      (self, expr_add):                                           return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_mul_exp):                return _ast_flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2      (self, expr_add, MINUS, expr_mul_exp):               return _ast_flatcat ('+', expr_add, _ast_neg (expr_mul_exp))
	def expr_add_3      (self, expr_mul_exp):                                return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_lim):                return _ast_flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_2  (self, expr_mul_exp, STAR, expr_lim):                return _ast_flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_3  (self, expr_lim):                                    return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_lim):                       return ('lim', expr_var, expr, expr_lim, '')
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, PLUS, CURLYR, expr_lim):          return ('lim', expr_var, expr, expr_lim, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, MINUS, CURLYR, expr_lim):         return ('lim', expr_var, expr, expr_lim, '-')
	def expr_lim_4      (self, expr_sum):                                                                     return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER1, expr_lim):           return ('sum', expr_var, expr, _tok_digit_or_var (POWER1), expr_lim)
	def expr_sum_2      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER, expr_frac, expr_lim): return ('sum', expr_var, expr, expr_frac, expr_lim)
	def expr_sum_3      (self, expr_neg):                                                                     return expr_neg

	def expr_neg_1      (self, MINUS, expr_diff):                            return _ast_neg (expr_diff)
	def expr_neg_2      (self, expr_diff):                                   return expr_diff

	def expr_diff       (self, expr_div):                                    return _ast_diff (expr_div)

	def expr_div_1      (self, expr_div, DIVIDE, expr_mul_imp):              return ('/', expr_div, expr_mul_imp)
	def expr_div_2      (self, expr_div, DIVIDE, MINUS, expr_mul_imp):       return ('/', expr_div, _ast_neg (expr_mul_imp))
	def expr_div_3      (self, expr_mul_imp):                                return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_func):                     return _ast_flatcat ('*', expr_mul_imp, expr_func)
	def expr_mul_imp_2  (self, expr_func):                                   return expr_func

	def expr_func_1     (self, SQRT, expr_func):                             return ('sqrt', expr_func)
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_func):   return ('sqrt', expr_func, expr)
	def expr_func_3     (self, LN, expr_func):                               return ('log', expr_func)
	def expr_func_4     (self, LOG, SUB, expr_frac, expr_func):              return ('log', expr_func, expr_frac)
	def expr_func_5     (self, LOG, SUB1, expr_func):                        return ('log', expr_func, _tok_digit_or_var (SUB1))
	def expr_func_6     (self, TRIGH, expr_func):                            return ('trigh', f'{"a" if TRIGH.grp [0] else ""}{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func)
	def expr_func_7     (self, TRIGH, POWER, expr_frac, expr_func):
		return \
				('^', ('trigh', TRIGH.grp [1] or TRIGH.grp [2], expr_func), expr_frac) \
				if expr_frac != ('#', -1) else \
				('trigh', TRIGH.grp [1] or TRIGH.grp [2], expr_func) \
				if TRIGH.grp [0] else \
				('trigh', 'a' + (TRIGH.grp [1] or TRIGH.grp [2]), expr_func)

	def expr_func_8     (self, TRIGH, POWER1, expr_func):
		return \
				('^', ('trigh', f'a{TRIGH.grp [1] or TRIGH.grp [2]}' if TRIGH.grp [0] else TRIGH.grp [1] or TRIGH.grp [2], expr_func), \
				_tok_digit_or_var (POWER1))

	def expr_func_9     (self, SYMPY, expr_func):                            return ('sympy', SYMPY.text, expr_func)
	def expr_func_10    (self, OPERATOR, expr_func):                         return ('sympy', OPERATOR.grp [0] or OPERATOR.grp [1], expr_func)
	def expr_func_11    (self, expr_fact):                                   return expr_fact

	def expr_fact_1     (self, expr_fact, FACTORIAL):                        return ('!', expr_fact)
	def expr_fact_2     (self, expr_pow):                                    return expr_pow

	def expr_pow_1      (self, expr_pow, DOUBLESTAR, expr_func):             return ('^', expr_pow, expr_func)
	def expr_pow_2      (self, expr_pow, DOUBLESTAR, MINUS, expr_func):      return ('^', expr_pow, _ast_neg (expr_func))
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
		'POWER1': 'POWER',
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

		if not self.parse_results:
			return (None, 0, [])

		rated = sorted ((r is None, -e if e is not None else float ('-inf'), len (a), i, (r, e, a)) \
				for i, (r, e, a) in enumerate (self.parse_results))

		# rated = list (rated)
		# for i in rated: print (i)

		return next (iter (rated)) [-1]

if __name__ == '__main__':
	p = Parser ()
	a = p.parse ('\\int x+y dx')
	print (a)
