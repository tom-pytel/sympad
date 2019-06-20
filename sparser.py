from collections import OrderedDict
import re

import lalr1

#...............................................................................................
def _ast_negate (ast):
	return ('-', ast) if ast [0] != '#' else ('#', -ast [1])

def _ast_flatcat (op, ast0, ast1): # ,,,/O.o\,,,~~
	if ast0 [0] == op:
		if ast1 [0] == op:
			return ast0 + ast1 [1:]
		return ast0 + (ast1,)
	elif ast1 [0] == op:
		return (op, ast0) + ast1 [1:]
	return (op, ast0, ast1)

_diff_rec       = re.compile (r'd|\\partial')
_diff_start_rec = re.compile (r'^(?:d|\\partial )(?!_)')

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
			b'eJztnftv3DYSx/+ZA+IFuID4lJjf8nB7xjmPOkkPxcII0iY5BGhzRZr2ChT5329mvkM9NqK9fux6nQZLSyI1pIYzH1KkqF0frO4cHz26Y+48e8HbR0ePXzzj2Hcnz2l3/Jg3T76l7fOTo2//yWd+ePT0B049/IYl7t87oe3TeyeHj4/p4Ojbx09ODl8+eHFy' \
			b'zELfnNx7oDure0d7Oc3ij+Wi30sZ/3jz/nU515fJB/cp178On/Mh68BXffrk34cicyzaPnj4hFOfPZeCnr24T9uHT17cPz7UJJEXDe49eP7k5OgeX/zh0fdHDw+HCxwjL4s9PTl6dMglP39Cm8PvXtw75thvv//4x6sPdPDxzZ8fX+LwzZ+/fnj5/vdfyuHH' \
			b'Nx/6419ffXjzvkRe/fhbn/7f/5XDt69++tgf//7+p3L8y+8/v3z3y68l+vrdH+9evxlib9/2l37zn1cf3/3Rn3v74VVfyG+DWiNluWg6KNGf3/VCr16/1sM7p2Z1sLRm6RaG9tEcdCYbSnDO5EVJk5Q+urSJj5z8uWCWfjGKD9Fl4D3nbSRng42nq1m70CQ+' \
			b'5COPjW8WGl1ayd6aA0tF2Zb/FiXFj2JFjlM4K+nhixKIeCc1suPUMI5E4yh/O03yk1LSNOL8mjwl5XF8fJKqw0dUxYYvxCak4tmQxvaZ5s7SVci+58tMRJbinSB/LpZ0jachvhSlrMWG9FwshkM66swBqQ6vd3zAZzsD59tEXmjk+uqxxOhokhunUolW61rS' \
			b'lvBUwMZR6TYu1pLcQElJZJtPU3KJcgF0xJcbGSipiQfX1ATG7qTETopl0iaak0gsB1ZkIsey8aSBVllTKEqpi4nM2nmNUkzaCzWPXjG94JBGRptL49iQ7uHRbKglULte0TkTTTIttzlqBEQ05WTbkjaNCZ0J2cSGzeBbww2fm2dgsKiG7GuyTMMNhz0qLBJQ' \
			b'xBC71JngTQgmRBOSCVSuobjx2QQq2ppAVHpqnKppJFWcid7EYGI0kVJaEzvjO5P8KXNN/cCKnMPdQZQtXYeqcUBayynP8ZvVckXNmjXzUJNMyhquxB8UJ8vKLmtyFLHb44PoUC31RUB1AqpzEHA2NhBqIQSZUmOrJ4NUfNf6+6gQwR1WdNtXa5Oaeb/1c3Cm' \
			b's4VyAOA8dmHPtY97rl8CpMW6FtYNsG4I2KEnDNoVBm10KtpoVn+7upmg/Xm+ZWpb7V3E3OdJ26TSYSNp+DnqrS7C+1FTQUpErxalV4vZpMYka5Ljjg+9cCrZjdtn8tM+q8fDDCd42n1Wc8WDj73WjzXDmMhhTOS4B4sW1g1IDkheHfD+xjweRBfbQjUrqt2e' \
			b'fslm6M3XW1zQR3vNOA84UDN/8ZqF/a5ZBHKlNXi0Bih9tXYX4gWNxaMLmPlWcb/i8c9tUvgATvbaXIO9VdrLuMdtMJIJqF5EpxqFrcloZcXjGocBDTr/mDF8wXwjYUR8kHS+abw8C/CYd3vMu/0CtxiPW4zHLYZ2a2phXmshHyAYaoJ8G/I3N321nVar4f2+' \
			b'gsA3Da+98l6rGeBsr76X6E1NHQCxg0YNIMMWxAWAbZEYoXqMUD1Kj8HNw6F5uAq95IuA9hDQHoI0r4B4KHEr8f11XAP1Pe/EceHm2qSD6aASZ2e/ZPglwZFJfLfWxZF1I1wR4Yp4q/r6AL3D7dKbyRZzQ/lGdjGL0xJcmCyooiok+CfBP6k0lYR6J7kFWS5C' \
			b'pNv9bTErrkaLarSlGi2qwXFWv0NlO0h1ejfs9rlSQfS8qB3yPleJdNpj/ZiIvIDl91lNXmZpdJ2l0QWKRrhvzKoxrB50UoUS14M7L68aoxJUHGsgl+fKOb6YdOAm0QF1EHQ9akHWtFSkNZ03mUIwOZrMl2Q1aM+qs+5sBH6kzw+eeUGI1fQNqZWo91xS8Wn0' \
			b'kVVQWevz9NeZJWmzTH4iM8gGkuEyWpJxtLeaznn5XCyS1NktqadbJjvkP+WBxV4ahleLGjENjsahZqDPJae5PjdVOTMYaxAf2Wta0qncRshojGo0irywPEZ1Ys4e/KRtp2raQj01hb5lKfLjQV1TsbozrTdtMG1kD7RZnODYD10wXTRda3Jjsl1zC9eL68nm' \
			b'jiM3UTrXjKv2mcvoHC/7jF3HzY6XCHkRlFdAPXdt0pqXXpbRg7h0STLLwC6gPVWd3yFgk5Mtgn6W/DoCvx8RJJMkVdwu58iG2Ad5IYS3WYpxsuWldDIEFRBSucJnPBhe3udXUDzoWKIEK1tWgq4b+K0JCnlCjSzx0x8LsKDVK5CCXIUpTWRDLo1H5BBjP1Oc' \
			b'hUkq5FOZAhBgYWtwpbP4qsI1C1S6TqY24YnrLqGCEp/Re08vOaKJo0G2tW4EMj6N8itWkiujRIcdyGKsBum5nkb1sNiBJlFlFigRAlEi1Bcwj5SIj+sbYIYRU+YvG+9yK2vz3SW7x90lVj/xPfIralXUOoNQQ60Dat0QJqh1glpXR02LSKP8BbUOqHVArZui' \
			b'1kvPoaZ6WOwUta6KWjeg1gE1LXoetQ6o9RoEvdwmqMWvqFVRywahhloGankIE9SyoJbrqCELo9bnL6hloJaBWp6i1kvPoaa58LJiQS1XUcsDahmoadHzqGWg1msQYIaNUEtfUauhxrWWUEHNYSjWi4nLBtQ4GmRbQU2z8Gp5n19Rk1wZJTrsBtQG6RnUih4W' \
			b'O6AmqsyiJkJATYT6AuZRE9F2pEGAGTZCrf2KWhU1ebeaX6+uoGaBmh3CBDUrqNk6avrudhrlL6hZoGaBmp2i1kvPoaZ66E5Rs1XU7ICaBWpa9DxqFqj1YgFm2Ai17gZRO2vauSe0RYNQoy2CtlGY0BaNvhdfow1ZmLY+f6EtgrYI2mJPmxQ6zjAHnKoC6QJc' \
			b'rAIXB+AigNOi54GLAK7XIMASGwGXy4OOcOFHHXE75PmLP/PYCER/3TDKFwj4uQcftbKtYJmAZRrCGMskj+P0Gxo1MpHLj4soZCaQmUBmGsjE0xBIk3Xc3OPE9WciRT1kL6imKqppQDWJQQVXFFLBNQHXvh4BFtoIV9tcpoPcEqn72Ud2BqEGI6a0vZibTmmp' \
			b'Xk5mta4+q9VcPo2KKDBiVuswq3XDrFYKHWeY6yZVG0gX9qoTWzdMbB0mtqXoee4wsR00CHq5jbizX2/MZ0En37Ny1cmtw+S2F3PTya2YX7Y14vR7XGmUvxCHya3D5NYNk1spdJxhjjjNCOlCXHV+64b5rcP8thQ9Txzmt4MGAZbYjDi3U+Iq626jVxtuEL10' \
			b'Dn6UgFDBz2PC24v56YRXMsi2gp9mYUP2+RU/jwlvKdT1R4BQY2Gcc4bDksliBw59dfLrh8mvx+S3FD3Locfkd1L9AKtshuJuFytuN4rOINRQdEDRDWGCohMUXR1FZGFD9vkLig4oaqFD8YoiYmGccw5FzWSxUxRdFUU3oOiAohY9j6IDiuPqB1hlMxR3u5hx' \
			b'u1H0BqGGogeKfggTFL2g6OsoIgsbcogoih4oaqGuP1IUEQvjnHMoaiaLnaJYXaQVIUXRA0Uteh5FDxTH1Q+wymYoXmmxA+/W9K/VncWkH16euTCZaQRns2d8kiamusiLNd5WP2MuZXm35dphibedhVPkfEJ+2qFE0IlFXpTrdA8wUXoarjuiMqceTGSxZljp' \
			b'rS70Duu8WOZFqbNAYo23v3QQlTdD8WqLIRtyeHUCL4Rf2kEPmQxCrYfEg5tezE8f3Hh5aqPpVncz/STOTEop/SSe3ZSiXX+k/SRiIU1VmOsqNZ/FTrvK6mMb2+DapbtM6C61+PnuEo9tJooEmGgzRq+2irJLRpNg2u0Vqa1BqJGK/rIX89M+00unqek2YTdD' \
			b'KgTUtBpRUtFplqJdf6Sk6jXSVIU1UkV/O1bRYqe8VnvRIq64oist15jHFb3pRJsAO22Ga2dWeP9vHtcB0XZmWMlACocMoR8t5Z39WNtVX+L7jK4aVUJUXqNHn1Mvq/iUt/PGzCzrb+QtR13YUl8rGK++bfTq3XK0+FZx+/pLdxVfs6PZuWuv2JFiV3RhuCYv' \
			b'ujMc2STpjecdyo7mx+rtyLleXi/cjZPbdmt+5sqf5etihBmfD92n7f1fus8ZDqjgbTTlcF2tOdyCFp3nVtKv3qitdZdo2HSN3ffNzd+se8476KFJrxu9yXad6fLfwJfrjsRieNiCQ/05Dm32c+CU1KP2ql6N+GYDW+rWDKH4mx7yOqauzK/71fzlPA2S3Sf8' \
			b'8tftHBY3Fc+yO/a+vV6+nfJwsdZWI9V+m47cycyGFAvVtw+37bsdT2ioFl+Ix6rLY1+ax1r+CijbJxs8nkn8VKjlb83JY31+mNzggXVD4RRf1V5tzcNb9u35TmXnXXcPugNfTu6BueqgaxneXJ+PqsOZcwYxcBWbY89dZfXd17PcRfX8QtsTW3UbI5LdtCd3' \
			b'lyD7hF92+pIcJCbd8phxJx6y4e6y+4Tf3FpZuWfhq8tevs22dj8jS7QWdzIyuz3F7/asVEqcMbIn/zQCKp+j1qlXR7LGPmtxpS62tGvFiCHZiBMDlWWu7rOCU63g7kIF52nB+q8U5JcW8NsK/DsyZYFJ14L4W4D8UJlfcQ/yRAnPH1x5ynsqP+Z+fin8rxbW' \
			b'PpLVI+vMDz2c+bMO+jsOebRmlc3nP9ng+VsCo9bG8fFszWs78/LpGxb/WAjHZxrQQv4ZwbnVpZ5u/SNZ+xcwbJyrcyPrheOaJ6k8FgWxIoi1wNFCoL4rkNUoXeqX99yMedKaicifl/oQ1XmI8ZrAjJTUOW3VxQTjZT6iWXu2Ny7ih4n5N7W9dNoXCB22vkTb' \
			b'jfPy6qxGpObdVn3CN6JrDqJ17v21Jb0936G5S73OIKoP3wLZlu7BbCFAd7uh7qmqfmkVZ9Ygmk0CtbTqWW518+dQEXfRBj+ty0aNfFKlZBD46/DpwmEtV6UQVM3vuGo80N16QNXCrqvmzfYDqnbOeKBSNf52zeVrF8wlAs1ELpgFFUw3UMHW7CSggueMIS43' \
			b'orvMYIJnm/WAF8bOllkLNOHcWBi26PbGFsHcXIAt8t6N9L38D7abDpgwNqJOPxOnWW2Wl4doWrr4P6duL9o=' 

	_PARSER_TOP = 'expr'

	_GREEK    = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\pi|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'
	_CHAR     = rf'[a-zA-Z]'
	_ONEVAR   = rf'(?:{_CHAR}|{_GREEK})'
	_ONEVARD  = rf'(?:{_CHAR}|{_GREEK}|\d)'
	_ONEVARDP = rf'(?:{_CHAR}|{_GREEK}|\d|\\partial)'

	TOKENS = OrderedDict ([ # order matters
		('IGNORE_CURLY', r'\\operatorname|\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('TRIGH',        r'\\?(a(?:rc)?)?((?:sin|cos|tan|csc|sec|cot)h?)'),
		('SYMPY',        r'simplify|expand|factor|\?'),
		('SQRT',         r'\\?sqrt'),
		('LN',           r'\\?ln'),
		('LOG',          r'\\?log'),
		('LIM',          r'\\lim'),
		('SUM',          r'\\sum'),
		('VAR',         fr'\b_|d?{_ONEVAR}|\\partial\s?{_ONEVAR}|\\partial|\\infty'),
		('NUM',          r'\d+(?:\.\d*)?|\.\d+'),
		('SUB1',        fr'_{_ONEVARD}'),
		('SUB',          r'_'),
		('POWER1',      fr'\^{_ONEVARD}'),
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
		('FRAC2',       fr'\\frac\s*{_ONEVARDP}\s*{_ONEVARDP}'),
		('FRAC1',       fr'\\frac\s*{_ONEVARDP}'),
		('FRAC',         r'\\frac'),
		('ignore',       r'\\,|\\?\s+'),
	])

	def expr            (self, expr_add):                      	             return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_lim):                    return _ast_flatcat ('+', expr_add, expr_lim)
	def expr_add_2      (self, expr_add, MINUS, expr_lim):                   return _ast_flatcat ('+', expr_add, _ast_negate (expr_lim))
	def expr_add_3      (self, expr_mul_exp):                                return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_lim):                return _ast_flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_2  (self, expr_mul_exp, STAR, expr_lim):                return _ast_flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_3  (self, expr_lim):                                    return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_lim):                       return ('lim', expr_var, expr, expr_lim, '')
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, PLUS, CURLYR, expr_lim):          return ('lim', expr_var, expr, expr_lim, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, MINUS, CURLYR, expr_lim):         return ('lim', expr_var, expr, expr_lim, '-')
	def expr_lim_4      (self, expr_sum):                                    return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER1, expr_lim):           return ('sum', expr_var, expr, ('#', int (POWER1 [-1])), expr_lim)
	def expr_sum_2      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER, expr_frac, expr_lim): return ('sum', expr_var, expr, expr_frac, expr_lim)
	def expr_sum_3      (self, expr_negative):                               return expr_negative

	def expr_negative_1 (self, MINUS, expr_diff):                            return _ast_negate (expr_diff)
	def expr_negative_2 (self, expr_diff):                                   return expr_diff

	def expr_diff       (self, expr_divide):                                 return _ast_diff (expr_divide)

	def expr_divide_1   (self, expr_divide, DIVIDE, expr_mul_imp):           return ('/', expr_divide, expr_mul_imp)
	def expr_divide_2   (self, expr_mul_imp):                                return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_func):                     return _ast_flatcat ('*', expr_mul_imp, expr_func)
	def expr_mul_imp_2  (self, expr_func):                                   return expr_func

	def expr_func_1     (self, SQRT, expr_lim):                              return ('sqrt', expr_lim)
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_lim):    return ('sqrt', expr_lim, expr)
	def expr_func_3     (self, LN, expr_lim):                                return ('log', expr_lim)
	def expr_func_4     (self, LOG, SUB, expr_frac, expr_lim):               return ('log', expr_lim, expr_frac)
	def expr_func_5     (self, LOG, SUB1, expr_lim):                         return ('log', expr_lim, ('#', int (SUB1 [-1])))
	def expr_func_6     (self, TRIGH, expr_lim):                             return ('trigh', TRIGH.replace ('\\', '').replace ('arc', 'a'), expr_lim)

	_trigh_rec = re.compile (TOKENS ['TRIGH'])

	def expr_func_7     (self, TRIGH, POWER, expr_frac, expr_lim):
		is_inv, func = self._trigh_rec.match (TRIGH).group (1, 2)

		return \
				('^', ('trigh', func, expr_lim), expr_frac) \
				if expr_frac != ('#', -1) else \
				('trigh', func, expr_lim) \
				if is_inv else \
				('trigh', 'a' + func, expr_lim)

	def expr_func_8     (self, TRIGH, POWER1, expr_lim):                     return ('^', ('trigh', TRIGH.replace ('\\', '').replace ('arc', 'a'), expr_lim), ('#', int (POWER1 [-1])))
	def expr_func_9     (self, SYMPY, expr_lim):                             return ('sympy', SYMPY, expr_lim)
	def expr_func_10    (self, expr_fact):                                   return expr_fact

	def expr_fact_1     (self, expr_fact, FACTORIAL):                        return ('!', expr_fact)
	def expr_fact_2     (self, expr_pow):                                    return expr_pow

	def expr_pow_1      (self, expr_pow, DOUBLESTAR, expr_abs):              return ('^', expr_pow, expr_abs)
	def expr_pow_5      (self, expr_pow, DOUBLESTAR, MINUS, expr_mul_imp):   return ('^', expr_pow, _ast_negate (expr_mul_imp))
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

	def expr_num        (self, NUM):                                         return ('#', (lambda f: int (f) if f.is_integer () else f) (float (NUM))) # float (NUM) if '.' in NUM else int (NUM))
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
