from collections import OrderedDict
import re

import lalr1

#...............................................................................................
class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJzlXGlvHDcS/TMLWANwgObVZPubD8UrrHxElrMIBoKh2F7AQOw15Di7iyD/PfWqyG72MZc9oxl5IaqbR5Gseq94NLulk8W987On99S9l6/4+uPFJd3On+Hy/AldLy/OnvwdJT8/ffEz3Z+ePXv1EqWnP0Dy4YMLur54cHH67JwiZ0+ePb84ff3o1cU5hH+4' \
			b'ePAo3XS6G7pzMcR/4trPuOu/vfv4Npe1bSLykGr94/QSUeiCXl88/+cpy5yzLi9fPcyZLy9FIcS5ywePLp9fnD1Ab4/Pfjp7fIo+Hj9HK5dnT09fdh2cS0uo9eIiFV0+p8vpj68enCP1+csvv1/fUOTdfz/dvP745UOOfrq+efcxJ65/+dzm//s/Ofrl4/XN' \
			b'/3LiX9dvfsvxD19+ff3+w6ecfPv+9/dv37WCN9dv2viXj2/KShTJyd/e3bS6fO7UKpT99X2be/32bYreu1KLk7lWczNTdPfqJKpGUYYxqpnlPM5pk3NdI2b41zg1t7MuHbokRVChkotBI3qWshBFzMjFxFlKzrVDrFEnSNQUZjltu0QWmrMmUZ2QrDTBcWvY' \
			b'BF1k2iLulPHcdpFjSwHfixsqavo5oUgW7ZBliFh1UqELYEUtAzGlmwzMVCl1QUCulQk9kbnHPfCvrbIWKa27NEWArZYLgTyb5agwRM0GjtSEcsV9VbOcEVXKMmUu1dbJrpw3bzji5GJqbr6XBRz7OSEnya8QI1/Thd11Qs60XrVMwDKfWWbO5kDNUkcScOme' \
			b'7CWYQ6emZWwoRtqRPRZaCYaSQSnKnJUS/dKUkuGh4YlZ0YxSmwfMJ/KQGuTXOWXtjAbrolJaeVWTLxDEBIyJGFrOKeeVq+EIxD0NAFIJnUSGp8JgAIPsZ9QsRjm5PNnoK+U1OCZKXaUcXY1yJKesYoQteRP1ToOOGrU09KCrC8pF5RrljfJWeWrHK0/C/gqu' \
			b'S4N7QURhjHu+kjKkPaHNJZ4ldt/z4sTU3J0Jcovc7eLEcfrogXNR1G4EJtINSecFPO1TtthoK7lpKYXmjLqUarH4YLaQIvHgGjQCZ5W8wIhHGiM3e1j9Tmyi2bhDA2VkkObRIrBZwWenHXlhQFfJZ13yWcl24tEupYwIOZtgEq1CUtLejREtutv6TmhrY+KD' \
			b'sV4zuOw6mROd5q/k514Y9FZuUujF9TwD5IPyUflG1ZWqNRRKUx5tuWZHC9uCVrcjVg+rrZnJ2mhkbTSyNhoeXkFKSWUji42R8cW1DokqAXdQDbCUMjSaITr60atjUrfBfc2Mf2B2sRaLUxpWZPOlyh5acSeKM9h7dH62s10pdRrDju/76NDpbYjA6iz83YWh' \
			b'scC24Q7oeSKk2zTv2HgXlObtwpoJB7sFk/YARhZ/M17uF9gbGNkUyCLk5TnOy3ORl41pncZEnR8wLT9g2rTGWVnjrKxxdOvrI0ueTUuelSVvSgrQyvOVlecpmyZXe9j5p0qWmkMrYkWRKDDt/GkBc52VxwHmUroRYq1chWwrGmiR8OmWtPOy2/FRbrw0jqiu' \
			b'ux2SE+9x4j1OTg8cpzHiOK25/JArfSMKGrnx1YrSNvLNJ3f1go1nrx2PNzLYi8FeDPZ3Yb4hbbzwcQfUhbcwuHy1kvBClk9kMZ3MRi1s1MJGnd2vFnORhrRP0uF4nzoWMCOIGSGbEcQMpKF+FGOjSMU0JcdjNopUiWv31kE1x2wD6XTE+sEFmplAfcxq4oi5' \
			b'SmfMVTqlrdjRK7Wo2ikpJg2sT91g1pIZ2KqaBjwN9kYFqxqtGqMa6rhCS2QYq0ta49wXhuLcEmeFOK0zgXqiltScNJR7o+Ye70C8Kn/mpPXc43WXJplAcUO/eF1SpXLkRfptulpXWE5vy4oGLxwduGp6VjTFzyorpLyzov254lk3WQE1hNca/pKMMiO72C3g' \
			b'ZREe09noe2YGmq6o56qztwlbmAxNLBuN96mSKgO/ESugGEv0pe0IoFxielB1VQq8+q1d8e7qKEFzimFJoLlhGIE2kuhLT4CWSgagtVVK0HqtATR3nKClN5AJtFEYgbYyTIKWSgagtVVK0HqtXfGz21GCVkONFrR6GEagjST60hOgpZIBaG2VErRea1f8qHuU' \
			b'oEXo0IIWh2EE2kiiLz0BWioZgNZWKUHrtQbQAkCT5R7QxbQZ6Jb7FTuJvAUZQ4unLUE3b03ShkEP9wzdg9cA+EoFzfDTvrgGCaEBD1GraFS0KtKOmPSNQ2YayiFDK9NxVIEvWNaM+YJxeB/a4w08Uj62MHjnbCvi0cGuOXmNSpMtf7iDOQS8Gc7HNz8NrviO' \
			b'BpQSQfy5BIiyXFGNJ2TOo52YlNV8jdyK5qu0i1Wr4ibavoa+IB/vYBuAz16s1OY6+A4ETkjZDjpRGA8ztEhaGXyhFFMP1BaSoedFgAmfRtVZEcdXfI1i0AtPYRGO5cbjkZ3pazypHaebeE8etqt9pe8lSzxkNKIpIiEP6i6D2E+xAfUszdcB+Vm86lopmhPS' \
			b'ubIp8icmgUKplSRzszHLjrntqwAim2+YIfyuJwm983mi2mKu2GSe4A+8MFHA8npyqpASFMJfap4ucBv4jJfC9M3YwG2kPtxGYjrdojSo5SZ1sxvV4kYsGUP6FG3NFMLNSF1wWq/1r7qdRYAj+1pSbXIu4YbrAhInOheTifrDVPdpOo3m/jz+KS9/tphbNvTB' \
			b'45leopLQTi9tBtxFYgNXAfCRXWW8ocg1qq6hosXkGlFco82fmmE6vVZ7QGJdZCcY76nAj9T6+10rGiWhJbPNsG1suFY0zGQzZjKJV10rRXOJyUaYbPOnmOyUWs1kI0yK7ASTvXAl7xr2wmQ1IjMchk+csHHIfHYZxGeKDfhkab4O+MziVddKGTKluUNTFE2w' \
			b'Wqi2klVuOWbZMat9LZhV+72zqpWEltU2A6xKbMiqZlb1mNUkXnWtlKFlNXVoiqIpVjvVVrOqhVWRnWC1pwWz6r53VvkPHvA3D5nVNgOsSmzIqmFWzZjVJF51rZShZTV1WBZNsdqptppVeRZLshOs9rRgVv3XsGqa7t3BmF480+qC5LAZz66gOu6FbTtgnPpS' \
			b'3QFVSpH2fB9umUB0zYqq8f5aatCzhVHBpZa6n8y29Ga6/ILqxrZsZ7VWUl0z0yw45rnonEmuv2roLmd4B9waptetY9h+M8lQnUM7rNsMDGuJDYc1H710gsPBnSpVncggtOM79Wz6pSXvjnlnqdCXWu4AKK0r6Shm8YnhPtTrSr7AOSJn2GSU78AHvJLQ+kCb' \
			b'AR+Q2NAH8t+MpeKhD6RKVScyCK0PpJ5Nv3Rqmu/UXEq9rhL3cjCT5Ce4H+rD3Ed6xFB2cCwTpo5iQp/syKcudX6LK9TGlUcrzbpDleLkddkpSpNOTcoTEzkumTooAZlLzlLn41EM7ubp79HmfEDZjVuwtf6wAycdm52VlielS0425uk0Y3AuShW/nrJqN6zF' \
			b'Zilx4pDTBFI5ZhdMLy2ZFZ8F75fUYPfGK4xexW02foLj7liw4zvPUhO8kwo7HqpmJ6NVH/GIjRMnUTsYtDBy+4FL+t3eXBv+H6bbJtzKjEuVDrZIehXr75K7CeLkXco+CLRTBNZHu9GxicG4NYu+miISCB39lgdv0vkTAzQ2waP6w9j75JJ4gUNa3q1ta1jC' \
			b'JGA62vH49eNQc2PTY9Hj+0r+ZolMqrGDcgBCjojkNACBZWu1kGfSwKQuYXSCQruULeFpxBFGVXoUZOTxxFqvRnsJssB0DYB26r1W38FDtry+BeMx1RQAeN1hEG8VAzyt93GIm3nA5Dj+VieANauHHEvswQ/0fQL/T/mPFa39m0xuS4FYPn1tiIXdZiZaNfMA' \
			b'l/VzzDQ08t85EiK7nfR3N90XyMH+/c/le5rFr+SP9O4Q2vauo23wCTu+FeSlkrRYDJZJx2flHFjC8XG2gIqx3MOFahGIrDRUGPTlpWqmpEPcD+EFUr29Q/GRaOVHDdfLGq63arjuN5z+nxp/oSsf5JZ/KpFOgfG5LA658JmXwUNwen5q8sETFJyb9a2Qbw9/' \
			b'uKotq47/YqP7qnfyfaKSH9lg2uJnanMo//Mqncz3Pkeucv9yBD/4Fnlw5i6n7cVRu7yRak/YcZgeJhQfnpgH9XU/5E5NneI4HRxJsKH+W3AlU1b/cBf1PrBsUdwEQjj/8iBvQQaZIa6q0qxo0IQ2weaHb0GYh+xWgfuM0ufEt/Qrv59PH8xPQdpTChm9tUYX' \
			b'QdYXRHiJafPzghJ60jmw2s1qTxnrvsRBVntHz5SgtgqxKuJu84psnq72S0ujdh1Ebb2d2nZrzUHxxiGaDSVFebOtT7UOtb03Gf4XnYOA/wwxlb8iLK8iNtlJm7Y0aL01BltK7DY3DrSZ3ExS7Fizyu6WG6v2HMQmf5s2ObXnIDatWcF3a1NQew5iUzj4rgQP' \
			b'bgcIYn7MzwryeENPDA2/KKb9/uwvjLfIoQ=='

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

	def expr_add_1      (self, expr_add, PLUS, expr_lim):                    return expr_add + (expr_lim,) if expr_add [0] == '+' else ('+', expr_add, expr_lim)
	def expr_add_2      (self, expr_add, MINUS, expr_lim):                   return self.expr_add_1 (expr_add, '+', self.expr_unary_1 ('-', expr_lim))
	def expr_add_3      (self, expr_lim):                                    return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_lim):               return ('lim', expr_var, expr, expr_lim, '')
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, PLUS, CURLYR, expr_lim):  return ('lim', expr_var, expr, expr_lim, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, MINUS, CURLYR, expr_lim): return ('lim', expr_var, expr, expr_lim, '-')
	def expr_lim_4      (self, expr_sum):                                    return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER1, expr_lim):           return ('sum', expr_var, expr, ('#', int (POWER1 [-1])), expr_lim)
	def expr_sum_2      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER, expr_term, expr_lim): return ('sum', expr_var, expr, expr_term, expr_lim)
	def expr_sum_3      (self, expr_mul_exp):                                return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_func):               return expr_mul_exp + (expr_func,) if expr_mul_exp [0] == '*' else ('*', expr_mul_exp, expr_func)
	def expr_mul_exp_2  (self, expr_mul_exp, TIMES, expr_func):              return self.expr_mul_exp_1 (expr_mul_exp, '*', expr_func)
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
	def expr_func_10    (self, expr_divide):                                 return expr_divide

	def expr_divide_1   (self, expr_divide, DIVIDE, expr_mul_imp):           return ('/', expr_divide, expr_mul_imp)
	def expr_divide_2   (self, expr_mul_imp):                                return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_fact):                     return self.expr_mul_exp_1 (expr_mul_imp, '*', expr_fact)
	def expr_mul_imp_2  (self, expr_unary):                                  return expr_unary

	def expr_unary_1    (self, MINUS, expr_unary):                           return ('-', expr_unary) if expr_unary [0] != '#' else ('#', -expr_unary [1])
	def expr_unary_2    (self, expr_fact):                                   return expr_fact
	def expr_fact_1     (self, expr_fact, FACTORIAL):                        return ('!', expr_fact)
	def expr_fact_2     (self, expr_pow):                                    return expr_pow

	def expr_pow_1      (self, expr_pow, POWERSTAR, expr_unary):             return ('^', expr_pow, expr_unary)
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
