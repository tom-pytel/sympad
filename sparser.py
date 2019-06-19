from collections import OrderedDict
import re

import lalr1

#...............................................................................................
def _flatcat (op, ast0, ast1):
	if ast0 [0] == op:
		if ast1 [0] == op:
			return ast0 + ast1 [1:]
		return ast0 + (ast1,)
	elif ast1 [0] == op:
		return (op, ast0) + ast1 [1:]
	return (op, ast0, ast1)

def _negate (ast):
	return ('-', ast) if ast [0] != '#' else ('#', -ast [1])

class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJzlXHlvGzcW/zILxAIoYHgNyfznJG7WWOeo43RRCEbgJu4iQJMNcu0CRb5730EOyRnKkl3JkhOIHnJ4PL7jx5vjg8W9k+Mn98S9Fy/p+fPpGXgnT/Hx7DE8z06PH/8TU3598vxX8J8cP335AlOPfsKcDw5P4fn88PTo6QkEjh8/fXZ69Orhy9MTzPzT6eHD' \
			b'6MnoK/ApGbP/QqWfUtX/uHz/JqUNNDHwAEr96+gMg8gL1vr82b+PKM8J8fLi5YMU+eKMGcIwVXn48OzZ6fEh1vbo+JfjR0dYx6NnSOXs+MnRi1zBCVPCUs9PY9LZM3gc/fzy8ATfPn357evFRwhc/v/Dx1fvv7xLwQ8XHy/fp5eL3z4N8f/9Xwr+fvH6cwq/' \
			b'+/LHq7fvPqTXN2+/vn1zOZC9/M/F57dfh/ffP168HsJf3r8uiUAgvX6+/Diw8ylzVvD7x9sh9uLNmxi8dy4WB3Mp5momwLfiwIsgIEIpEWYpjmKG17nsMaToTxkx17P87vIrBLCA5IcCIn4WY+aS69P8UDFBQ4LBUBAHEgj04GbpXeeXlGlOjHhxoBJtCmtF' \
			b'EsgiUhdhI5Ql2kWMLjPYKqwgKdQxrngt6MxlhwEQqsMqUFVAGRUmZEh6aaVCFaDHlXlclWVu0Xf0p7sUH99lfgf2ULeKH6Dk2SwHMdSJg0EgeAH7UAhqcxToQfkdsdDNUoQXMUqVsWBZGcVNcfNAAcMPNWhriEHt1jEuvQLYMAQAlIU2+qhPNUBtWQZNVk55' \
			b'5iQNclmyCBlM9Flc4ALY1lg7c8oR8AaRszJHnRrfuG1IxGFiKCljiEPVNuLwbRTfpzetZ9BSF52QwooekACaBAUoj+3K9MI4YTzCACwP8AeWsBJPauiwKaChCGVAFgAFSsKGDrAHScGUYDmjhNHCGGEA4QJCQgNFoN4JA+oCohoaHvJqgrCdsMCKElYLa4S1' \
			b'woJK3DkCF+CzAIMgiiw9gRngHkBGKZoid8fh4kD1xJZy7Hlib3EAhZCxfVew7ZjtwOo0LIxxrGRpY7SnaM2ZteRU5Jysw4Wk27UppN85B4HV2UUUKEauUuzp3fJ3YCRbDMeHnTKiIrA0Qyc1GtaeZjVt1DDaMEaTYSQbxrBhjGbPMLBN5I4TdYhl9J1o0SZq' \
			b'1t8NblMPT7pe0bj0qjwHks1sI84tW9CyeW1M5HHEEvSsE9YLG0TfiV5ipxYHFpBqtrdqW8AouMfs4aisZjw2Kh4bFY+NippX4FTDqcZR9AKHlz0WaoHj3h7zh8MwqVWStve+5Usf2SU0rJhjETJ2OV7JCGhFjKw/OdS7Ztww4363fCxwUFd5AEaf+wC1a8aM' \
			b'vo5JcY7ASLgLjWyBk5c7wOcBg0PHLsF0d4FpmrSs6LpwzqLiTETxFERNJx0LnKEonprwUGh5NWl53WV5XtzHttOn5bCm5bCOI63mkVbzSAtezQ8PvDoOvJoH3lYuVC2v8jSv6nTspvVue7IuSqp2zYgmxXjWoWKP4/hFB/b4GfOxUiXnsNHTLJLl+ZH17FGT' \
			b'nZil74Y5lWFLG7a04f0GjsbWwQscSt/l+B6YQcUePTXHISUUNELLsoosqW3aNkBgywJbFtjehb7BMNfG3QV2ES2kXHpCccvmMYxKw9YxEX49W6Nna/QJfj2Li++Y28bcbn+nzAsUw7EYLonhWAx8R/Y9C+s5l4/dp99noQyxu1LwsM8yAE97zB9CIMxY1fvM' \
			b'Jm5Kd3FXuov7uh0BvROLbuiSfKybedEuVW9TP6xFD+0b2nYQTosgRVAiIK8W/kA8Yhr4wv1iFBf3O3GPEbf5FNoTKIk58km+hD88S3H0Xv7mwP/c4oEa5AHR5iDV3OLRSyrr4M/DX8ilznFgvV15Ap5rgjzsZ3nC6HeVPJye5Rl+59QTgzyGJEJm2No9oigK' \
			b'qJbKCNhDOGhEQZbXViI76MqAgy7LHtw1xEd+yKEO8BR3iMgpeORWaGaao1VGTzSWUlSlu4KBrMCa2jlNwfZai0awG7Roxm6ixUmOVpmGFmPKSIuZgUKLFTXUotlvLfKJp81anLiJFluZJmUaWowpIy1mBgotVtTOabm211rsBbtBi/3YTbQ4ydEq09BiTBlp' \
			b'MTNQaLGidk7L3b3WohfsBi36sZtocZKjVaahxZgy0mJmoNBiRQ216FCLPK9ATfo468jziiumLGmuM9U0TFHKeQvOhDzNTyaTk7zCG1mgE06SHaxwPVrDBTSIl8Ir4bXwRnjg149NFCAGBO1UNlaHhkPJwtRwKBwe1VYGRINCPM6V8Dhcd2BQg3LNAUQi9tJ4' \
			b'8YguYoBqQQOGU2BOBk+8CIT3RfBaDXa2aChLyWLak1OctuwDT3RFhKgwLU7Hka8jEibVNcYC3z7CuQXd2+HSVAavrACbYJM5GAUv+egpYpAilFWYqYs1gMh44aqenqCa8GpXPwhNTOPFGYW1uHPaFGk3z52ASW8PQJOWDwF2qeXnCEPXiRI6yMvooAz0HOEj' \
			b'FtYDGcllsaezhBLyuGzECREzRdWNfoNKcda18EFkMkAS4SZElC3dufhTyfvz8G2Gd/5u3uHYTcNEbrzb6a7R9azT7Si6dTbn1Uzf7Hk4BRMRX33GV1/hC63SE8SmA3gsr20Kyeh5JhjpctkEsZ4hRjm94/yreiQiw2XXw1w/YA71SLiLrLVx11O/VKiEvaJv' \
			b'KrAou2t2UhsH4C77KS/YDf3UEIE48hlHvsIRWsUTjqZTmFheJ2KEI8848owjzzjyGUeecTTU3uqqPMPGrwsbX3dVkXAbMr50FTzkDzuGBcFuwMYQYfjKdcJGPcOhDPQcA4ML60SJgBEYGIGBERgYIQMjMDCGqlvACAyMsC4wQg2MSLgNjMpVwFi2J7NBYLR2' \
			b'8qoTkR3CAzc0ySV45AiAB3oRHtTrZ3hQBnqO4BEL60QJ4UGeZ2oyxSsuHhGS6jQFAw2QUMFYfh2QEJkMkkS4CZKhYnIVSJZtOf0oIJGC3QCSIcKwl0Aia5BIAomcgoRL6USJQCIZJJJBEuly8QSSWKcpGGiBRDJI5LogkTVIIuE2SGTpKpAs21H7UUBCX9Xg' \
			b'hzUJJEOEoSOTASSqBokikKgpSLiwTpQIJIpBohgkHK+4eAJJrNMUDLRAohgkal2QqBokkXAbJKp0FUiWbRiuAokK+expihY8RJITzLjrwMYUyPG3Ah49AhDULfJWZXwDsfIyqF4F0QqoJ+bFdB3EuWHpp4QzMQc/Pb8pGX0j8kqI6zSx9noZFPQAHl76rLvy' \
			b'6SvkMNkmbvr8q0CzbH90Zc+yHDEbxooiuJj1EKM3CBoUi9zQ6wwR2OvkDTwMlr0O7eDlzOO+h2O1HdLTB18pQskhFPPG7idWXhDX9QYfCI84olxhINKxtwpPmKnnvGVvFCtp90Zm5CpsuT3G1vqd0EYhxef3edcvRyCk8q6frnf9dPoUM2YeQ4pji3SmgJDi' \
			b'CCWHEH/SmSAVaRfEdXsfUPM+oF5nH1B2EUr1XmAi3oaSHbkKSh5Wm0KPdgJdC0SuBo4nsPSEEZWg4a/czQurxqQCCMsAEOJGXblJxzt0rb05NP6S04D5tAOZRwujeeeKZ7LJnmjJ1ftraMj1xpfSfEsMN48baKOdfSh4c5N1m7GaD0sNxyBtGxDSsbPC3mow' \
			b'ZkenGds1qtNbsysKfZVtk/ANG+ed6Gzv1Ks17A4sbLipqo20VrnHLdY39jM30GhRyOs3XODv9vpa9yN0t8HdSo8LhXY2SFrh++/Sdg3D8fGd3IIBdcuA/d5OdHS0oL+2FW3XMiRqaO+nPHgXhC7JILGGHWHWqu8DJHHaClzerWmrW2JJtNHetsebt0NJxNpt' \
			b'0eIlZLqXByL1uNgzqAjeDePNCXSUtxcLXuJuyrR6A+bEBhhXma221m/MRiZs1Cp1C3JJtRvsBjehXez2Cg1b2VSy31cl4/5ErWh/tzCMerleP0Mlbg/C6j4hwICnv/F/zLkbCkYpN9+Rb0HDHai2/8b/ZmixnSF2+3tCxZCKOtn+iHqb20DiTynvw0zhG38e' \
			b'/F0YSX/XRlL4rQ7eY6ZPEIDFxWgCZOhQhhzlMHROwpbAL6KqrgVKgeZJIuSvaL4z+p8vC6YcSw9mspMeqh/NCrPQuBc/JtwvI9xfi3BfE47/q5I+G+NvB8rvw+KZAN7px+1LvDOqcHsjroxD2lJEBudqNRVoEOMfFdVl0WUfq+UPEJqn6YJ/cQFBbUcXv1Yj' \
			b'4H8vGI9zqq8oZOKFD21Gn1DQ+Uw8nNHpTKY4kOEj1PgVha4/nlh2iOLEzX6Aq9BTCLd/J+kko/376gVZVv+osn4bCmVVrqNHbArLHZ+WjSKdv6pIWJak3PBCgru/r2VqwzdwVL9vKr7FTfMboCt0XLGocPyCZzmEyZYrR64hMo1WrlmG5AhXA2gqyhLcrCuQ' \
			b'E9dyvivCZs1SJFi+cr1dCwWxNcdyyFuRAydR23Ish7odOej/Jm/HsRz6ui3mxqIoMXX433xa8dd3LM2KEXmD0mixTcfS2FuTxohtOpZmxeC+QWmc2KZjadxupyq4ILxtx4L7tJbg5Q+sKAJdEYD1wOwvJQTcLw=='

	_PARSER_TOP = 'expr'

	TOKENS = OrderedDict ([ # order matters
		('IGNORE_CURLY', r'\\operatorname|\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('TRIGH',        r'\\?(?:a(?:rc)?)?(?:(?:sin|cos|tan|csc|sec|cot)h?)'),
		('SYMPY',        r'simplify|expand|factor|\?'),
		('SQRT',         r'\\?sqrt'),
		('LN',           r'\\?ln'),
		('LOG',          r'\\?log'),
		('LIM',          r'\\lim'),
		('SUM',          r'\\sum'),
		('VAR',          r'\b_|d?(?:[a-zA-Z]|\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\pi|\\rho|\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\infty)'),
		('NUM',          r'[0-9]+(?:\.[0-9]*)?|\.[0-9]+'),
		('SUB1',         r'_[0-9]'),
		('SUB',          r'_'),
		('POWER1',       r'\^[0-9]'),
		('POWER',        r'\^'),
		('POWERSTAR',    r'\*\*'),
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
		('TIMES',        r'\*'),
		('EQUALS',       r'='),
		('DIVIDE',       r'/'),
		('CDOT',         r'\\cdot'),
		('TO',           r'\\to'),
		('FACTORIAL',    r'!'),
		('FRAC2',        r'\\frac\s*[0-9]\s*[0-9]'),
		('FRAC1',        r'\\frac\s*[0-9]'),
		('FRAC',         r'\\frac'),
		('ignore',       r'\\?\s+'),
	])

	def expr            (self, expr_add):                      	             return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_lim):                    return _flatcat ('+', expr_add, expr_lim)
	def expr_add_2      (self, expr_add, MINUS, expr_lim):                   return _flatcat ('+', expr_add, _negate (expr_lim))
	def expr_add_3      (self, expr_lim):                                    return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_lim):               return ('lim', expr_var, expr, expr_lim, '')
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, PLUS, CURLYR, expr_lim):  return ('lim', expr_var, expr, expr_lim, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, MINUS, CURLYR, expr_lim): return ('lim', expr_var, expr, expr_lim, '-')
	def expr_lim_4      (self, expr_sum):                                    return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER1, expr_lim):           return ('sum', expr_var, expr, ('#', int (POWER1 [-1])), expr_lim)
	def expr_sum_2      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER, expr_term, expr_lim): return ('sum', expr_var, expr, expr_term, expr_lim)
	def expr_sum_3      (self, expr_mul_exp):                                return expr_mul_exp

	# def expr_diff_1     (self, VARD, DIVIDE, text_var_diff, expr_lim):       return ('diff', ('@', text_var_diff [1:]), expr_lim)
	# def expr_diff_2     (self, FRAC, VARD, text_var_diff, expr_lim):         return ('diff', ('@', text_var_diff [1:]), expr_lim)
	# def expr_diff_3     (self, expr_mul_exp):                                return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_lim):                return _flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_2  (self, expr_mul_exp, TIMES, expr_lim):               return _flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_3  (self, expr_func):                                   return expr_func

	def expr_func_1     (self, SQRT, expr_func):                             return ('sqrt', expr_func)
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_func):   return ('sqrt', expr_func, expr)
	def expr_func_3     (self, LN, expr_func):                               return ('log', expr_func)
	def expr_func_4     (self, LOG, SUB, expr_term, expr_func):              return ('log', expr_func, expr_term)
	def expr_func_5     (self, LOG, SUB1, expr_func):                        return ('log', expr_func, ('#', int (SUB1 [-1])))
	def expr_func_6     (self, TRIGH, expr_func):                            return ('trigh', TRIGH.replace ('\\', '').replace ('arc', 'a'), expr_func)
	def expr_func_7     (self, TRIGH, POWER, expr_frac, expr_func):
		return \
				('^', ('trigh', TRIGH.replace ('\\', ''), expr_func), expr_frac) \
				if expr_frac != ('#', -1) else \
				('trigh', TRIGH.replace ('\\', '').replace ('arc', 'a').replace ('a', ''), expr_func) \
				if 'a' in TRIGH else \
				('trigh', 'a' + TRIGH.replace ('\\', ''), expr_func)

	def expr_func_8     (self, TRIGH, POWER1, expr_func):                    return ('^', ('trigh', TRIGH.replace ('\\', '').replace ('arc', 'a'), expr_func), ('#', int (POWER1 [-1])))
	def expr_func_9     (self, SYMPY, expr_func):                            return ('sympy', SYMPY, expr_func)
	def expr_func_10    (self, expr_negative):                               return expr_negative

	_derivative_var_rec = re.compile ('d[^_]')
	def expr_negative_1 (self, MINUS, expr_func):                            return _negate (expr_func)
# ('*', ('/', ('@', 'd'), ('@', 'dx')), ('@', 'y'))
# ('/', ('@', 'd'), ('*', ('@', 'dx'), ('@', 'y')))
	def expr_negative_2 (self, expr_divide): # here we catch and convert the two possible cases of derivative forms
		if expr_divide [0] == '*' and expr_divide [1] [0] == '/' and expr_divide [1] [1] == ('@', 'd') and \
				expr_divide [1] [2] [0] == '@' and self._derivative_var_rec.match (expr_divide [1] [2] [1]):
			return ('diff', ('@', expr_divide [1] [2] [1] [1:]), expr_divide [2] if len (expr_divide) == 3 else ('*',) + expr_divide [2:])

		if expr_divide [0] == '/' and expr_divide [1] == ('@', 'd') and expr_divide [2] [0] == '*' and expr_divide [2] [1] [0] == '@' and \
				self._derivative_var_rec.match (expr_divide [2] [1] [1]):
			return ('diff', ('@', expr_divide [2] [1] [1] [1:]), expr_divide [2] [2]) if len (expr_divide [2]) == 3 else ('*',) + expr_divide [2] [2:]

		return expr_divide

	def expr_divide_1   (self, expr_divide, DIVIDE, expr_func):              return ('/', expr_divide, expr_func)
	def expr_divide_2   (self, expr_mul_imp):                                return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_fact):                     return _flatcat ('*', expr_mul_imp, expr_fact)
	def expr_mul_imp_2  (self, expr_fact):                                   return expr_fact

	def expr_fact_1     (self, expr_fact, FACTORIAL):                        return ('!', expr_fact)
	def expr_fact_2     (self, expr_pow):                                    return expr_pow

	def expr_pow_1      (self, expr_pow, POWERSTAR, expr_func):              return ('^', expr_pow, expr_func)
	def expr_pow_2      (self, expr_pow, POWER, expr_frac):                  return ('^', expr_pow, expr_frac)
	def expr_pow_3      (self, expr_pow, POWER1):                            return ('^', expr_pow, ('#', int (POWER1 [-1])))
	def expr_pow_4      (self, expr_abs):                                    return expr_abs

	def expr_abs_1      (self, LEFT, BAR1, expr, RIGHT, BAR2):               return ('|', expr)
	def expr_abs_2      (self, BAR1, expr, BAR2):                            return ('|', expr)
	def expr_abs_3      (self, expr_paren):                                  return expr_paren

	def expr_paren_3    (self, PARENL, expr, PARENR):                        return ('(', expr)
	def expr_paren_4    (self, LEFT, PARENL, expr, RIGHT, PARENR):           return ('(', expr)
	def expr_paren_5    (self, IGNORE_CURLY, CURLYL, expr, CURLYR):          return expr
	def expr_paren_6    (self, expr_frac):                                   return expr_frac

	def expr_frac_1     (self, FRAC, expr_term1, expr_term2):                return ('/', expr_term1, expr_term2)
	def expr_frac_2     (self, FRAC1, expr_term):                            return ('/', ('#', int (FRAC1 [-1])), expr_term)
	def expr_frac_3     (self, FRAC2):                                       return ('/', ('#', int (FRAC2 [:-1].rstrip () [-1])), ('#', int (FRAC2 [-1])))
	def expr_frac_4     (self, expr_term):                                   return expr_term

	def expr_term_1     (self, CURLYL, expr, CURLYR):                        return expr
	def expr_term_2     (self, expr_var):                                    return expr_var
	def expr_term_3     (self, expr_num):                                    return expr_num

	def expr_num        (self, NUM):                                         return ('#', float (NUM) if '.' in NUM else int (NUM))
	def expr_var_1      (self, VAR, PRIMES, subvar):                         return ('@', f'{VAR}{subvar}{PRIMES}')
	def expr_var_2      (self, VAR, subvar, PRIMES):                         return ('@', f'{VAR}{subvar}{PRIMES}')
	def expr_var_3      (self, VAR, PRIMES):                                 return ('@', f'{VAR}{PRIMES}')
	def expr_var_4      (self, VAR, subvar):                                 return ('@', f'{VAR}{subvar}')
	def expr_var_5      (self, VAR):                                         return ('@', VAR)
	def subvar_1        (self, SUB, CURLYL, expr_var, CURLYR):               return f'_{{{expr_var [1]}}}'
	def subvar_2        (self, SUB, CURLYL, NUM, CURLYR):                    return f'_{{{NUM}}}'
	def subvar_3        (self, SUB, CURLYL, NUM, subvar, CURLYR):            return f'_{{{NUM}{subvar}}}'
	def subvar_4        (self, SUB, VAR):                                    return '_' + VAR
	def subvar_5        (self, SUB1):                                        return SUB1

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
		sym  = rule [1] [pos]

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

		return next (iter (sorted ((r is None, -e if e is not None else float ('-inf'), len (a), (r, e, a)) \
				for r, e, a in self.parse_results))) [-1]

# if __name__ == '__main__':
# 	p = Parser ()
# 	a = p.parse ('1/2 x*')
# 	print (a)
