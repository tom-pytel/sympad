# TODO: complete derivatives

from collections import OrderedDict
import re

import lalr1

#...............................................................................................
def _ast_flatcat (op, ast0, ast1): # ,,,/O.o\,,,~~
	if ast0 [0] == op:
		if ast1 [0] == op:
			return ast0 + ast1 [1:]
		return ast0 + (ast1,)
	elif ast1 [0] == op:
		return (op, ast0) + ast1 [1:]
	return (op, ast0, ast1)

def _ast_negate (ast):
	return ('-', ast) if ast [0] != '#' else ('#', -ast [1])

class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJztnWtv20YWhv/MArGAEcC5ksy3tHW7xjqXOk4XhREUbuMuAmyzRdp0Fyjy3/ec854hhxJF0YlkS2kgmuQM53Iuzww5nJF8cvXg/OzxA/Pg+QvePz578uI5h769uKTD+RPePf2G9pcXZ9/8na98//jZ9xx7+jWn+OLRBe2fPbo4fXJOJ2ffPHl6cfrDly8u' \
			b'zjnR1xePvtSD1aOjo1zm5N9J7idS9d9u3rzK17oy+eQLyvWP00s+ZRm41mdP/3kqac4h7YsvcuTzSwjE51Lloy8vn16cPeLavjr77uyrU67jq6dcyuXZ49PnfQXnKIlzPbvQS5dPaXf67YtH5xz67d2Pf1y/pZOb//369oc3737Jp79ev715kwPXP/7Wxf/n' \
			b'v/n05+uffu/O317/1J2/e9Od//Lu3z+8/uXXHHz1+o/Xr2760M8/d1Xf/Ov699d/3JQZ6SQHf79524n2Wy9lIfu/X3ex169e6emDl+bqZGnN0i0MHZM5aUxrKMI50y5ynMR0waWt+czJnwtm6RdFuA/SCR05byU5K+wcx9iFRvEpnwXsXLPQ4NJGOfPmxFJZ' \
			b'VG1adBG+CNmgJxTFJySHz0Ig4J1oZMvYUAaicVGqKKP8oJQ0DDi6aFcSuLoMl4ElZCTJK67JUmXB+MhS2TanG7tK1ZCBt6cZJFmK4Wr581WO17Dtw8tGxLPYkZyLRX9KZ405IdHh9oZP+Gpj4H1L5Yn7jKsWOYIuVgpPEUslWtU1x5Ht5Cxi5xgqdWgf5XpO' \
			b'cqRYfRhV5yCXQGcUbwsTJTVy75xNCXxBAF0SLYn9geiUIOjRivUIW2oRnnFFCkRQiCIXZYrhVQ1BZEp80gmUjdTFkbnG4ji0Ep9yyPsFteurylgTTTI1a+8abnnEQ2hMaE2smAVqGYQ52cDXhhs+uc8LV1xpI2apuOGwQwVFJ55hjzoTvAnBhGhCMoEqMBQ2' \
			b'vjWB6rAmEJTcOEXcZCKJ4kz0JgYTo4kUU5vYGN+8ZKapE7git3BfEGVPlZAO1IrkiufgPUp4deJEkhOyohxaEe/qJIrMR2JmusLCezV3gC4BujCYEh0rpII3vMNVkl+C6hBkzVawmiWIMe5UJx+VHfjHimCH7QcStj0GKR286qx62QEfBxJcOHwdToIDHS4e' \
			b'vrAkZQLD2eAWBg8weAg4oH8M2kEGbZCatNKs/oi6paB9fHtMMlvtdsTQW1p72JaGHzLk1ue1C4aro8YCi4geLkoPF1uTKpOsSc4kz/1go1mNO3zQ0+ELyY8cboEbv8ON3+HG77jZUVan91CHe6hDu7OHr9oV39SPQEq26f24PohTbQ0fW/HxkXRMtlVsKz5u' \
			b'ud8cAaz81AGFvHhh/s00HINyEaTl3sSjN4HoH9F0QryNsfhhAjY+HtCv+FnnaKQ9gWO9Ns5gj0d0ecbZ0pXwI47TBxeHJxa3/oxyxQ80Dk8yuFvGFmN9DDQSRpxJR5zJ6+sAL68DvN6MPW7GHjdjOgzlwb3Z673Z4948lspLKr4VSuIWoXsYwdpGdav4eNgw' \
			b'8C3Da298BMIGAOCVBwney2gBEDuIUwE17MFdAIwWkRFyxwi5o/Qa3EocWokbwTnl22RtAlpIQAsJ0tICwiGHrYQP3X8VlPB8EP+Fe2qjDtaDPJyX3dPCPQn+TOLC9T6PbBzhkAiHxOPp+QOEDkckNJMthobklRxiKx5L8F+y4IkUSfBMgmdSbioJSie5DVku' \
			b'QlLXh95irliZGsrUWZkaynCYlWigcoNUjd4om8NXLYi0W9VvD18TkuzgpWQo2gXMfvjC8rRMpfMylc5pVNIAKnNVSbfFcxQiEwvkRKFWZBdxoYFvskyN1BdyZ04nySTqL6g5VaYOpqlM40xLmzdtMG0yLVfJYtCR5WbB2QL8rp9fP/MEEovpKxKL5DfLyBOc' \
			b'pEbxkXnMyFO4jVmSNHHkI5PjpP6S9F8mTms1ns/5Gs9lu5ya+r4labFMti/jJT9rHKRhWl59oIZpi8+qYdqRz5hhED80jKYuDNOV8VLuHGQYZpGNIzPaoLWEsTfYCtpdM1mzH3MNEwrs2ogAdUl0u8G01tSODVyTWHQrasTSlo3deNOQ4ZNpSINq3fakQEUa' \
			b'VKRCFQtfsGIUz6qt+YWu8XRP6R9uWzx1yBODPCvo+fEmsGpLUgde4+UGPMEdedkBL4/gVQZG1nmQLYJ8ltSwaS9z/pQlSGa5sOJjiSP74cjXJSnJx9lRCGNPRuCZ85TLX8NAJvYjr3zgP17TIHmt7LlySkS9EC+d8Ou4cCKSn9cHBE5stRYSksWvBiSRDblE' \
			b'fgpXZRspgBNTqiCEeSYs7I2vOInYJr4myIo7hmsOWGwB2Sa44qt6q0FSvmXUA7QkFsslhnBpDp+K7MpYXlxRC2VyAGbMWJ96pLfJgGkKnjmtO8RElI2USUJgJgltV80oZ5K8LlWHOQrQzJ82PuSmVzcPl+wq95AAfs93x8/8beevMdim+GvAX5eU+WuG/DXC' \
			b'X7POn2ZPRfbMXwP+GvDXDPnrUk/xhxTMX9Pz10zy1/T8NeBPqxnnrwF/vepa5Rz+4mf+tvPHq7tkWd8Efy3465IGLAQs+WuxpmydP+Rg/rrsmb9WF5eBv3bIX5d6ij/NjeWNmb92kr+2568Ff1rNOH8t+OtVhzlm8Zc+87eVP9Zdtgn+HB7r+qTByaHgT2Jl' \
			b'v8Kf5uBZ9i678iepW5SkBfb89akn+NMU7Lyq409E2cifJAR/ktB21YzyJ0nrUnWYYxZ/9Wf+tvPnDLYp/hz465IGHEr+nPDn1vlDUuavy575c+DPgT835K9LPcWfZrM4KH9ukj/X8+fAn1Yzzp8Df73qMMcs/pr75G9iiHtoCCaDbQrBBAS7pIxgGiKYBMG0' \
			b'jiBy+FRkzwhiCbmUpAUCQSmszDBFIVI45MoUpkkKU09hAoVazTiFCRT22sMisyhs83uWDyMx7RpGd/tXLnOp9Lsmk8eF/NrFyTbFJ4bIrksa5A1fySfPK8oo2a2PkjWTT0UJGVGMkh1Gya4fJUthOUODFFtfyWjZDtkzq5MjZtePmNlY0j/bXNAGXjFqLqwB' \
			b'C83i1VYf3m3uHNYD7zlbg22KTAxe+qRM5nDwwh6T8YtbH79oJiazKyGTifGLw/jF9eMXKazMMNV5agHIlYGcHMK4fgjjMITJ1YzDiCFMYQAYZR6M9vM9fA6JFIFtgkSPYUyflEj0w2GMxMp+BUPNwRbssiuGHsMYj2GM74cxUliZYQJDTeGQSzH0kyMZ349k' \
			b'PEYyuZpRDD1GMoX2sMg8DN09YLg2BXg0MFqDbQpGCxi7pAyjHcJoBUa7DiNysB277BlGCxgtYMS1zKNWVGabQlIz60GRtJNI2h5J3KZzNeNIWiDZiwa7zEPyPmZXjhdJZ7BNIYlhdp804FAiKcNsvz7M1hxsxy57RhLDbI9htl7LSGpFZbYpJDWzxUGRnBxv' \
			b'+3687THeztWMI4nxdmED2GUekvcx4XK8SHqDbQpJDyS7pEHWoQyQ9IKkX0cSOdiOXfaMpAeSHkjiWkZSKyqzTSGpmS0OiuTkRLMkVCQ9kNRqxpH0QLK3AewyD8ldzMGUK4DW2ax4Bc84odU8SGPPaWrvC9W0BVeS0Ey+IsIbIk1GJhm+HZKXQ0nUNeuviCSO' \
			b'rFp7U3dlKKx4RSQxzukRqKKmZPKn5LSNa6giqzX9S6LJd0T9KyK8IUINo4ji9VAnRhBjzONzF3M0E3DuFksvZMZbwhnvhE/WXLap7jSiO+2Scncah91p/sURTbHaqSKWbdwlyZ1qRKeKSOe6M+1XtcYipx8ucmuTICsqWJSsfawWhMjcx8ZN8HrtZmPfzUZ0' \
			b's1rleDcb0c0OzAOTzSN5F7M9+yf5Q3rXOwI4GWxTAKOT7ZMywMOOVmKLFKsAI7a77vuO1uvvuSDSue5MAdYai5x++sV8zm9xUG43drq2qgFu3/N6dL25qnFw0fsOhAow1TxwG3PFr+c3YutsgWozxLPNPLaCYTf1OP163U6tZVyjbBNdQla7QhHel89YpMjo' \
			b'lNws1xcmLgs4lrpMopwjnLUCkd0/Y/Xh6trDDc5e6tvslZWGJNxH+dDuyI122pNVEsjHPcqe5hXjdeFdL8ss9+/lOuzN0az4NmdnI4w4ve9HbQdA7kdHQKCCd9+Y/Q7bczjwNt2OvafdTbO21n1A06Z67rh7rtu/Vg/d3lEnTbLd542Wqm0+fWeuehKT8mFP' \
			b'HvXbPFod5tNTUpfaj3Vr9J1n2YtH8RzF33qRtaW6rGXVseZPF+hR2b3Hr58d6cNxtcG17L+DbrEf11L5mXFTa438hTxZRswv6vgbcTV/tUleYJINUotN0iZztTef39VQaL6P2T+7cvEdj34GrbWe8trH98V7cNzGHnhG3xt6/7VH4T9+EbTVh81fpuXFHXeu' \
			b'd9/y/EOi7z2+kP3Jeo2Nt8974p27zVJja97jF4I/Ka+xze7oQebunWYfEpTv8YvNn5bXwl/Ca46/7MzPm418N9zLd//KB1GSjj3A20v8/hFP6sEvbPDeqDwdXbMfRCuWsRdEskZkzV7tZ8nrlWLElAMT9Yrz9M5qwWlTwc2tCm6HBes/p5AfqsBSWZ5CztNX' \
			b'Os3EX5bkN9Xyi0vykkreaLQ2vzdmAZdueyn8zytWPpLVI+vIj2RM/jCG/hJG+esXY7944fkbEEXb47CO/qTBeW1v+HSti39ohcMjrQj/WkAnHW0cExzziaX4UTTAvCEmDWW6sJwrxCIEnRx0PCfIM4CttvRVHdOKntR1fNCH0CSIcoinCkZSic5xr34itT/k' \
			b'I5KlfXij9MNcJ3BfvHnDfPB6fLM5S+umCuTN9wGxRb1XL8mNZrebSN3sV2pndr2J1G3H3Z7k9vzwwP37LjcRvf+2zb5kD2YPG2S3M2WPG8XPjXpSg2jmbNRRbLzKncb4NSjipjuubbrM6qMGKiWDLeSTW21hMpg3qOY/QLWxrvjWOjr5V1S32qh0PUm3zQtl' \
			b'tzwO7NyPPNTY+wbV4l2rFsz+N6i25bFhg2qx/hjt5F+h3XZrwm2zQMH6HhRszJ1sULA5lAc/Huzf2wZbtHmIiFEtDRRbHhgSCi8X/we+fkol'

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

	def expr_add_1      (self, expr_add, PLUS, expr_lim):                    return _ast_flatcat ('+', expr_add, expr_lim)
	def expr_add_2      (self, expr_add, MINUS, expr_lim):                   return _ast_flatcat ('+', expr_add, _ast_negate (expr_lim))
	def expr_add_3      (self, expr_lim):                                    return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_lim):               return ('lim', expr_var, expr, expr_lim, '')
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, PLUS, CURLYR, expr_lim):  return ('lim', expr_var, expr, expr_lim, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, MINUS, CURLYR, expr_lim): return ('lim', expr_var, expr, expr_lim, '-')
	def expr_lim_4      (self, expr_sum):                                    return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER1, expr_lim):           return ('sum', expr_var, expr, ('#', int (POWER1 [-1])), expr_lim)
	def expr_sum_2      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER, expr_term, expr_lim): return ('sum', expr_var, expr, expr_term, expr_lim)
	def expr_sum_3      (self, expr_mul_exp):                                return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_lim):                return _ast_flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_2  (self, expr_mul_exp, TIMES, expr_lim):               return _ast_flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_3  (self, expr_negative):                               return expr_negative

	def expr_negative_1 (self, MINUS, expr_diff):                            return _ast_negate (expr_diff)
	def expr_negative_2 (self, expr_diff):                                   return expr_diff

	# ('*', ('@', 'z'), ('/', ('@', 'd'), ('@', 'dx')), ('@', 'y'))
	# ('*', ('/', ('@', 'd'), ('@', 'dx')), ('@', 'y'))
	# ('/', ('@', 'd'), ('*', ('@', 'dx'), ('@', 'y')))
	# ('/', ('^', ('@', 'd'), ('#', 2)), ('*', ('@', 'dx'), ('@', 'dy'), ('@', 'y')))
	# ('/', ('^', ('@', 'd'), ('#', 2)), ('*', ('^', ('@', 'dx'), ('#', 2)), ('@', 'y')))
	_diff_var_rec = re.compile ('d[^_]')

	# def expr_diff       (self, expr_divide): # here we catch and convert possible cases of derivatives
	# 	if expr_divide [0] == '*' and expr_divide [1] [0] == '/' and expr_divide [1] [1] == ('@', 'd') and \
	# 			expr_divide [1] [2] [0] == '@' and self._derivative_var_rec.match (expr_divide [1] [2] [1]):
	# 		return ('diff', ('@', expr_divide [1] [2] [1] [1:]), expr_divide [2] if len (expr_divide) == 3 else ('*',) + expr_divide [2:])

	# 	if expr_divide [0] == '/' and expr_divide [1] == ('@', 'd') and expr_divide [2] [0] == '*' and expr_divide [2] [1] [0] == '@' and \
	# 			self._derivative_var_rec.match (expr_divide [2] [1] [1]):
	# 		return ('diff', ('@', expr_divide [2] [1] [1] [1:]), expr_divide [2] [2]) if len (expr_divide [2]) == 3 else ('*',) + expr_divide [2] [2:]

	# 	return expr_divide

	def expr_diff       (self, expr_divide): # here we catch and convert possible cases of derivatives
		def _interpret_divide (ast):
			if ast [1] == ('@', 'd'):
				p = 1
			elif ast [1] [0] == '^' and ast [1] [1] == ('@', 'd') and ast [1] [2] [0] == '#' and ast [1] [2] [1] > 0 and isinstance (ast [1] [2] [1], int):
				p = ast [1] [2] [1]
			else:
				return None

			ns = (ast [2],) if ast [2] [0] != '*' else ast [2] [1:]
			ds = []
			cp = p

			for i in range (len (ns)):
				n = ns [i]

				if n [0] == '@' and self._diff_var_rec.match (n [1]):
					dec = 1
				elif n [0] == '^' and n [1] [0] == '@' and self._diff_var_rec.match (n [1] [1]) and n [2] [0] == '#' and n [2] [1] > 0 and isinstance (n [2] [1], int):
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
		if expr_divide [0] == '/': # this part handles d/dx
			diff = _interpret_divide (expr_divide)

			if diff and diff [1]:
				return diff

		elif expr_divide [0] == '*': # this part needed to handle \frac{d}{dx}
			tail = []
			end  = len (expr_divide)

			for i in range (end - 1, 0, -1):
				if expr_divide [i] [0] == '/':
					diff = _interpret_divide (expr_divide [i])

					if diff:
						if diff [1]:
							if i < end - 1:
								tail [0 : 0] = expr_divide [i + 1 : end]

							tail.insert (0, diff)

						elif i < end - 1:
							tail.insert (0, ('diff', expr_divide [i + 1] if i == end - 2 else ('*',) + expr_divide [i + 1 : end]) + diff [2:])

						else:
							continue

						end = i

			if tail:
				tail = tail [0] if len (tail) == 1 else ('*',) + tuple (tail)

				return tail if end == 1 else _ast_flatcat ('*', expr_divide [1], tail) if end == 2 else _ast_flatcat ('*', expr_divide [:end], tail)

		return expr_divide

		# if expr_divide [0] == '*' and expr_divide [1] [0] == '/' and expr_divide [1] [1] == ('@', 'd') and \
		# 		expr_divide [1] [2] [0] == '@' and self._diff_var_rec.match (expr_divide [1] [2] [1]):
		# 	return ('diff', (expr_divide [2] if len (expr_divide) == 3 else ('*',) + expr_divide [2:]), ('@', expr_divide [1] [2] [1] [1:]))

		# if expr_divide [0] == '/' and expr_divide [1] == ('@', 'd') and expr_divide [2] [0] == '*' and expr_divide [2] [1] [0] == '@' and \
		# 		self._diff_var_rec.match (expr_divide [2] [1] [1]):
		# 	return ('diff', (expr_divide [2] [2] if len (expr_divide [2]) == 3 else ('*',) + expr_divide [2] [2:]), ('@', expr_divide [2] [1] [1] [1:]))

		# return expr_divide

	def expr_divide_1   (self, expr_divide, DIVIDE, expr_mul_imp):           return ('/', expr_divide, expr_mul_imp)
	def expr_divide_2   (self, expr_mul_imp):                                return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_func):                     return _ast_flatcat ('*', expr_mul_imp, expr_func)
	def expr_mul_imp_2  (self, expr_func):                                   return expr_func

	def expr_func_1     (self, SQRT, expr_lim):                              return ('sqrt', expr_lim)
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_lim):    return ('sqrt', expr_lim, expr)
	def expr_func_3     (self, LN, expr_lim):                                return ('log', expr_lim)
	def expr_func_4     (self, LOG, SUB, expr_term, expr_lim):               return ('log', expr_lim, expr_term)
	def expr_func_5     (self, LOG, SUB1, expr_lim):                         return ('log', expr_lim, ('#', int (SUB1 [-1])))
	def expr_func_6     (self, TRIGH, expr_lim):                             return ('trigh', TRIGH.replace ('\\', '').replace ('arc', 'a'), expr_lim)
	def expr_func_7     (self, TRIGH, POWER, expr_frac, expr_lim):
		return \
				('^', ('trigh', TRIGH.replace ('\\', ''), expr_lim), expr_frac) \
				if expr_frac != ('#', -1) else \
				('trigh', TRIGH.replace ('\\', '').replace ('arc', 'a').replace ('a', ''), expr_lim) \
				if 'a' in TRIGH else \
				('trigh', 'a' + TRIGH.replace ('\\', ''), expr_lim)

	def expr_func_8     (self, TRIGH, POWER1, expr_lim):                     return ('^', ('trigh', TRIGH.replace ('\\', '').replace ('arc', 'a'), expr_lim), ('#', int (POWER1 [-1])))
	def expr_func_9     (self, SYMPY, expr_lim):                             return ('sympy', SYMPY, expr_lim)
	def expr_func_10    (self, expr_fact):                                   return expr_fact

	def expr_fact_1     (self, expr_fact, FACTORIAL):                        return ('!', expr_fact)
	def expr_fact_2     (self, expr_pow):                                    return expr_pow

	def expr_pow_1      (self, expr_pow, POWERSTAR, expr_abs):               return ('^', expr_pow, expr_abs)
	def expr_pow_5      (self, expr_pow, POWERSTAR, MINUS, expr_mul_imp):    return ('^', expr_pow, _ast_negate (expr_mul_imp))
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
# 	a = p.parse ('d/dx**2')
# 	print (a)
