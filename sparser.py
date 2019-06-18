from collections import OrderedDict
import re

import lalr1

class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJzlXPtvGzcS/mcOiARQwJJD7sO/pa3bM8551HF6KAyhcJscEKDNFWnTu0PR//1m5iO53NWuLNuSHwlEi48dDufx8b3y4uLJ6cmzJ+bJq9fy/ezk+etXkvv27Jyj0+fy9eIb/j4/O/nm7/Lk+2cvv5fS46+F4ounZ/z98unZ8fNTTpx88/zF2fEPX74+OxWi' \
			b'r8+efhkjG2PHsT4W8u+09nNt+m9v379JzzJPSXzBtf5xfC5JkUFaffnin8dKcwppX3+RCl+dQyBJa5NPvzx/cXbyVFr76uS7k6+OpY2vXgiX85Nnx6/6Bk7BSWq9PIuPzl/w1/G3r5+eSu63jz/+cfmBE2//++uHH95//CUlf7388PZ9ylz++Fsu//d/UvJf' \
			b'Hy5/yumP73P64/vLD//LDy5/+j2lf/n48w/vfvk1Zd+8++Pdm7flQ06k7O9vP2RZfuvFKoT9+V0uvXzzJiafrM3FYmXNyi0Nx8EsWtMZLnDOdMtUpiU5u7K1pJz+OW9WtCzyfZYTHLf655gFGLSSEEYVvly7jNmVhRBkFpZr1xyWuYCKnPUxsVJBmHjBaYt2' \
			b'kSOnSthBMYvKVVMuGBe0lUEZ0aCgHuWcPh4XNoOCQW4FYVmFStoT83lDYkRju2SrqafcEtv2apoBySpI3OgfsUVh25i3fZ4THHf6x6ZfLmPKqtSNsY0majZ8pQ2BRApaE4tcWWqtCiZKpTKxvKQ8vlyt/AdFhddSUZOyjDRJMfpsoXYdDScmR805AlLfJpqV' \
			b'KiSCllIygY9x1NiahevltGocTrF0rBGJVDAhCjjHhcuSYvg05tBhmHiRBU12ymVi9YkyyY3K65QjWnL3vaiMNcHUphEbs2GcdjfvjQ/G14IDdj13COnZDG/WIlQmWPGjuK3Wpls1WiVdRjyr4OPGfGW8Nd4ZL1AjoxYmBhO33hnGt3ZHkdU3xrfGdyY4E8gE' \
			b'biWYwMRhLchlZF2wowRgQb+5WZaeO4s+CUpx13JdLFytwrgGUatCXSy85h+8WX0LsTsYkWWTrA8wrQ2xGDpShchGHVl0ySeVOzwlVfwOPRAACmlShCboYG1EDGS38MeudqFoEKv22RtWAFwPO3rI7V20n4UBXRXzDs8drOxor5L4/XFbeIKxICg1CR6PowdA' \
			b'dqofhbTURlyqrbf72NJVNAsb+3tEe4AHAyHCwwDQBjVQaExoTehMXZnaikBxiOC10PLBmu1CllgPVzyZu9wSc4nDXOIwlzgZ0HyDpyyyw+Ds0L+01n1alQ13zxKIie5PfVKHpInHVsjWcJdVtz30EUWnODc/KXlV6u6l8gqt3UdxF43eSXzF3Kcq7W0mtdvM' \
			b'59xe26K9cvNbJX8c6KVH0csWGCkoDg3UPgahdZVxRW+SRYaLSweHNYPbXCVcyJLCYS2BuStguxSw/QhY+dZxIK3TLo90l0dxaiRMjYSpkaOhPJgpKc6UhJlygkonTir2LWLnIqus73wbI9MFoTcSeiPF8Yz22OOr1MbMWDXzdJ8D2KwACzRPsAMICV4n+MSC' \
			b'IsSIYKKA1VLANBZ0AthARt2vsDxg5AEjj1nOa166HrZi+vwaHaVD/VnDzj5d4BlBIGo1ChHHAXoHBcFmp2JlApQJUCY8hkGFpQmw9SMQV5CgxtVvQibAWSE6S32v3qjhjRreqBO0aqgreaEOkbp5uDuSC1GjgRpNUqOBGo2itjYtlG1B1cZxt33ISrEo7ZWr' \
			b'w8Z0D1kHlukByycQ6JYw9UMWU45rq3heW8UTz0qBXpmLKg9JbZSPQmzG5xGYTM0dnjt7ZxoynTWdMx03XAknVkGVYW3kDFVUkmM8OXWTM0DXcEssjFkJP407swpy2xBM+Vmx1Ksgl0yWaRpOO/6Ti4kqPpeylv+6vtZapsq70qKTyz4vnuwGWnTFZ5sWeN5r' \
			b'kT9rHXVZC3hZdGkTQgovi1Ct4sT3aGNsjTSWiVUxk1HYw6NShIRidmWrhMIwlWmsmKfhwY/l4JGxM21lWkYwD3gsF6tf9cbrOMtQrFxvxkrgJuJ3myYVsMvR78C0YmouF3jK2TxVbGoviqxYbP6IyVdyJap3QWJyNqlYki2sl0wSc14uKEVruTDyuHgsnKRl' \
			b'rL9HSm8u5WquVtpWqzFfuQR1PlHJrWnpUFyBilvlvlDvCDnLSS/VOJaLNAlyn+UGzl/JzaOTe9428mYukm0GmBCjCK86ieD1W27wnLSliCfBCnAiFr5LfNDeMbHRzfRGVW/zxPHxYm/G2UqFm7+huyMHuSnL7Aqfp7vCZuD1nnTseB8FurarE79JZ+f2NIhn' \
			b'/aft2c4gZM/Od2Ol0u+xZ8FBPJvZlZ7t4i3w0LOZdMqz3Y08G/lNe3YQ1rrD/5Q96/T1ETF29KwkZzyrVHjbZOjZyCFUpmdXeFZrtKjee7YnnfCs0l7bs4nfpGdzexrWemrzSXvWGYTsWTfvWaeedZueBQfxbGZXetbBs27o2Uw65Vl3I89GftOedWUQzzaf' \
			b'tmfJIGTP0rxnST1Lm57FM/FsZld6luBZGno2k055lm7k2chv2rNUhrUegG7xbNyM5Z3YbVycdmKDE60tvrbqbjqQx/UtPhd6j4cNj0tRQUeI9Hvs+li/Mj196foA1wd1vbK1iQz725iZwkDIGFDyCtFuSIhcp5EQyiBI6Hbdd41REQ4ADLvzfmwnnFTX2Jnt' \
			b'sivTtxJlWyaa15MbMykeI6oGomIdEmU1hbccR6AClYCqTpkSVHiNUKujMQEVymNXrcUgSnfV5k25RJTVQFm9C8rEiIq0KM800mrdxfVaeOhb7OTMn5aOeCfbNEer9i/crl9jWDoEAO9tZGoNQh6Z2k0ctcBRpCMRWFP6PcYRqEJletYljlrgqAWOWuAIBc4X' \
			b'daYGp37Pr+SQYsfBKXKdhkxbhjVe7Pss56nOIGQ0bO4THRYniY4Q6fcYCiARKGS+JRSwYXTYMCpbm8icL+pMQaHfOSp5hWg3KESu01AYhDUuBGeh0OwVDfYAgGhujQk5SdeQMCHJAhM6pncauZBJCZF+j2ARSULiqwx6WGiNNjNy4GxTgfNFtQlkaCUgQ8lj' \
			b'rVlk0BAcifEkOKgqg4Jjy4ngZwEOaxAyOIbHD4QxQyIXMikh0u8xOEASKtOzLsGBo4jEyIFzpnS+qDYFjv5YgrDL0WgeHHYIjsh4Ghy2DAqOLYeKnwU4nEHI4BieYEhWwOEAjkiKX0V5/DZqBA6QCDgy6xIcOM1IjBA5mwqcL6pNgaM/2VDyCtE8ONwQHJHx' \
			b'NDhcGRQcW84lt4LDdf3l5iZK2J756nIbVmgeLr5ATHsnoKERcLhtU2fUDDc2tWIGOxtQkX5LhlAyQo2WseaNM42SmeHWBjsb8HKInY1xoh/uajrKoOl3MtjIbN3H1APAgOskXOr+s8bbvjccSOaBsmeIOEWJ3w0otEesiFoa8iDjh4OMxyDjMchEUkJk+trj' \
			b'oQalMtRkknKowd1lYudSytmcKpjT8EaTlRf4aM0m84gjj8fI4+dwJE9qEJSDT2xkevDxo7DGb5UeLqZ2H3P2CqVgEDKUhqd0khUo4aAukRIi09ceQykyqgqSEko4rkvsXEo5m1MFc5o+t6P+3I5wbkez53a2ihAKQwhF5tMQCqOgEGp5x2hol5cmmiFg2gIh' \
			b'XX8iv68XIuYc38XjtfJoDedq13zVYbU5YIh/S7eKT8uj90O90jDjsFU8+Rq9wMAVb+6yaj9ea7tZxwGc0w7k5yKoSJqdWelLG4d1akMH86sovfWmOyo/4eP+/Lj3dxrNJvzO7e65q7q99Fb7gHtsO3EKuYdOK0pev+OyTHc61rafw3Db3ejNoms6zt3fJBlM' \
			b'W3+qvhs7Dpdu9gAOpN0c6A7gwx2O+accSNGJ7T4cKSv3eldXBpzKSZ2JE7htfgwpzDgwPZx0n9VXDjtd00+50fzpqiNBpO+OBG0hHAnYQnukA707EhS1/kiA1HEhW61jSufkcpApHtcyt5lxu1j1wfbfm/dbqxym+26QV+D13TFWrZYVlxdD6CEZtyCHFxKU' \
			b'tjYX2Ar7q5y63aN0+w4sP8JIm1B1TOqL1VafpE6IexPZdU/fkeQ+VyWimT4XH86Z/pb9qpky+Nwweniby4A5Z3cnxxW7mB4Hz0HDVtNnohnTx4dbUO9uaf52Z7xfOYjRbUetwu4yJO02BinljkNQYfpbjzjy/ggbNdi/8F+Nohn3OCnsbzooDesPPc6LSl7b' \
			b'2eP4vsY/hYpG3u/kexg7u7uYUw80m67xv7cekbXpsVvbyS9v5KdXugwh0pf6y+UKC8Lm06AUXm89YFT5Hd3ALlyLjahCiwijtgKqJpf0Fg9j84qlBmu4Xi85YR8zrucY19diXA8Zx3/7qT8zxI8My18VxpN++X2LHE7KS5xOTi7ivrdLB4Yi4MpdzUX+Lejo' \
			b'o1WprLr548b+d4yTl+AGHyz0qfhMLdKX+o8Y48WMJfy7xXQJUxfXL5Ai37e06Y4FFyy4XSmuVnD3yR1P7lJIr02aCcHHNyLcUW/0YTh1dUzLqe4GhSoabmNXdvP2jzZRH8KW2Yq7mFDAPx9w6zX3tLUThd0Whq7JGVW/uY2FtcteK2ib7USbsO3uLTszCpg4' \
			b'NsuHQdvvZtv31xGBzGRg5889SkGl6N8otjQvS9WL00yBaSCRNwjyM3J/dZghg3T59dZdRLtCLp39bZgNPNdveWoDJHJ7t1dt9hEgHW0fR+ZGkI3hY/vYMRC/NTn4xpTZucArqm0E1TQXKDiYdHbRbl617XrJ8jEFWSnqMrEsHIW8oy8LsUCcooc24c608eaQ' \
			b'AdrUd6ZNYw4ZoE1z71Oy7FruIUD9Ni2Usbbn5XKnt9u82F3+H1I+3k4='

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

	# def impr_sympy_1    (self, SYMPY, expr):                                return ('sympy', SYMPY, expr)
	# def impr_sympy_2    (self, expr):                                       return expr

	def expr            (self, expr_add):                      	            return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_lim):                   return expr_add + (expr_lim,) if expr_add [0] == '+' else ('+', expr_add, expr_lim)
	def expr_add_2      (self, expr_add, MINUS, expr_lim):                  return self.expr_add_1 (expr_add, '+', self.expr_unary_1 ('-', expr_lim))
	def expr_add_3      (self, expr_lim):                                   return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_lim):               return ('lim', expr_var, expr, expr_lim, '')
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, PLUS, CURLYR, expr_lim):  return ('lim', expr_var, expr, expr_lim, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, MINUS, CURLYR, expr_lim): return ('lim', expr_var, expr, expr_lim, '-')
	def expr_lim_4      (self, expr_sum):                                   return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER1, expr_lim):           return ('sum', expr_var, expr, ('#', int (POWER1 [-1])), expr_lim)
	def expr_sum_2      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER, expr_term, expr_lim): return ('sum', expr_var, expr, expr_term, expr_lim)
	def expr_sum_3      (self, expr_mul_exp):                               return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_divide):            return expr_mul_exp + (expr_divide,) if expr_mul_exp [0] == '*' else ('*', expr_mul_exp, expr_divide)
	def expr_mul_exp_2  (self, expr_mul_exp, TIMES, expr_divide):           return self.expr_mul_exp_1 (expr_mul_exp, '*', expr_divide)
	def expr_mul_exp_3  (self, expr_divide):                                return expr_divide

	def expr_divide_1   (self, expr_divide, DIVIDE, expr_mul_imp):          return ('/', expr_divide, expr_mul_imp)
	def expr_divide_2   (self, expr_mul_imp):                               return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_fact):                    return self.expr_mul_exp_1 (expr_mul_imp, '*', expr_fact)
	def expr_mul_imp_2  (self, expr_unary):                                 return expr_unary

	def expr_unary_1    (self, MINUS, expr_unary):                          return ('-', expr_unary) if expr_unary [0] != '#' else ('#', -expr_unary [1])
	def expr_unary_2    (self, expr_fact):                                  return expr_fact
	def expr_fact_1     (self, expr_fact, FACTORIAL):                       return ('!', expr_fact)
	def expr_fact_2     (self, expr_func):                                  return expr_func

	def expr_func_1     (self, SQRT, expr_frac):                            return ('sqrt', expr_frac)
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_frac):  return ('sqrt', expr_frac, expr)
	def expr_func_3     (self, LN, expr_pow):                               return ('log', expr_pow)
	def expr_func_4     (self, LOG, SUB, expr_term, expr_pow):              return ('log', expr_pow, expr_term)
	def expr_func_5     (self, LOG, SUB1, expr_pow):                        return ('log', expr_pow, ('#', int (SUB1 [-1])))
	def expr_func_6     (self, TRIGH, expr_pow):                            return ('trigh', TRIGH.replace ('\\', '').replace ('arc', 'a'), expr_pow)
	def expr_func_7     (self, TRIGH, POWER, expr_pow1, expr_pow2):
		return \
				('^', ('trigh', TRIGH.replace ('\\', ''), expr_pow2), expr_pow1) \
				if expr_pow1 != ('#', -1) else \
				('trigh', TRIGH.replace ('\\', '').replace ('arc', 'a').replace ('a', ''), expr_pow2) \
				if 'a' in TRIGH else \
				('trigh', 'a' + TRIGH.replace ('\\', ''), expr_pow2)

	def expr_func_8     (self, TRIGH, POWER1, expr_pow):                    return ('^', ('trigh', TRIGH.replace ('\\', '').replace ('arc', 'a'), expr_pow), ('#', int (POWER1 [-1])))
	def expr_func_9     (self, SYMPY, expr_pow):                            return ('sympy', SYMPY, expr_pow)
	def expr_func_10    (self, expr_pow):                                   return expr_pow

	def expr_pow_1      (self, expr_pow, POWERSTAR, expr_unary):            return ('^', expr_pow, expr_unary)
	def expr_pow_2      (self, expr_pow, POWER, expr_frac):                 return ('^', expr_pow, expr_frac)
	def expr_pow_3      (self, expr_pow, POWER1):                           return ('^', expr_pow, ('#', int (POWER1 [-1])))
	def expr_pow_4      (self, expr_abs):                                   return expr_abs

	def expr_abs_1      (self, LEFT, BAR1, expr, RIGHT, BAR2):              return ('|', expr)
	def expr_abs_2      (self, BAR1, expr, BAR2):                           return ('|', expr)
	def expr_abs_3      (self, expr_paren):                                 return expr_paren

	def expr_paren_3    (self, PARENL, expr, PARENR):                       return ('(', expr)
	def expr_paren_4    (self, LEFT, PARENL, expr, RIGHT, PARENR):          return ('(', expr)
	def expr_paren_5    (self, IGNORE_CURLY, CURLYL, expr, CURLYR):         return expr
	def expr_paren_6    (self, expr_frac):                                  return expr_frac

	def expr_frac_1     (self, FRAC, expr_term1, expr_term2):               return ('/', expr_term1, expr_term2)
	def expr_frac_2     (self, FRAC1, expr_term):                           return ('/', ('#', int (FRAC1 [-1])), expr_term)
	def expr_frac_3     (self, FRAC2):                                      return ('/', ('#', int (FRAC2 [:-1].rstrip () [-1])), ('#', int (FRAC2 [-1])))
	def expr_frac_4     (self, expr_term):                                  return expr_term

	def expr_term_1     (self, CURLYL, expr, CURLYR):                       return expr
	def expr_term_2     (self, expr_var):                                   return expr_var
	def expr_term_3     (self, expr_num):                                   return expr_num

	def expr_num        (self, NUM):                                        return ('#', float (NUM) if '.' in NUM else int (NUM))
	def expr_var_1      (self, VAR, PRIMES, subvar):                        return ('@', f'{VAR}{subvar}{PRIMES}')
	def expr_var_2      (self, VAR, subvar, PRIMES):                        return ('@', f'{VAR}{subvar}{PRIMES}')
	def expr_var_3      (self, VAR, PRIMES):                                return ('@', f'{VAR}{PRIMES}')
	def expr_var_4      (self, VAR, subvar):                                return ('@', f'{VAR}{subvar}')
	def expr_var_5      (self, VAR):                                        return ('@', VAR)
	def subvar_1        (self, SUB, CURLYL, expr_var, CURLYR):              return f'_{{{expr_var [1]}}}'
	def subvar_2        (self, SUB, CURLYL, NUM, CURLYR):                   return f'_{{{NUM}}}'
	def subvar_3        (self, SUB, CURLYL, NUM, subvar, CURLYR):           return f'_{{{NUM}{subvar}}}'
	def subvar_4        (self, SUB, VAR):                                   return '_' + VAR
	def subvar_5        (self, SUB1):                                       return SUB1

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
