from collections import OrderedDict
import re

import lalr1

class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJztXPlvGzcW/mcWiARQwPDm5Le0dbvG5qrjdFEIQeE2WSBAkw3SprtF0f9930FySM1Qhz2S7WZhWsOb773v4z3SYv3gxfdPnn//QDx4fP4EPl+8xM8n509fvsDQtxeXmPQUP559A5+XF+ff/B1DZ19jyhePLuDz+aOLs6ePwXP+zdNnF2c/fPny4jFW+fXF' \
			b'oy/jQ8angiclY/bvqPRTavJvb96/Tmm5TvR8AaX+cXaJXmwbW33+7J9nlOcxS/nyixT54pIFQj81+ejLy2cX54+wta/Ovzv/6gzb+OoZ1nJ5/uTsxdDAY64JSz2/iEmXz+Dj7NuXjx5j6JdPP/529RE8b/774eMP7z+9S94PVx/fvE+Bqx9/yfH//k/y/uvj' \
			b'1U/Z/+l99n96f/Xx95xw9dOvyf/u088/vH33IQVfv/3t7es3ZSJ4UvDXNx+zLL8MYhXC/vw2x169fh298IAWoMjv7z78/uCVWC9WSqz0UixW0olFEL2ACKVEv0xxFJODK+nRp+lfGbEyyyGshyB44NnTv4IqZLfkCPRhVZI/VFjG4EqyGEYsJMjkwS1zhC5C' \
			b'0kTPikSBtAX4JbfMIa1IDVlFWwjZHHJCWWqlitO6ivAbIUXJm5F1rq4MoRd8qAK2h2Wt0Balk32y1lSqIuvuzKOrLCuHz0D/GuRg1GJYDmHwoHgdf4Dxl8vkVeQLgmGWHprtqC3GDyMgsYssKWIBQRn1SnGriJTlD+Wo/ipKDwilKJ+CQDf0AQVVobmLtkOr' \
			b'c8lWBk3wpjyrgE8UtJQSMtj4lJQBqLfQg5yKrAM+kA7Yr5FoXJIjIASRyzJHnRpDrIokdsSq0YNP6CNZ+GS7HAdWnIrD0Ea8SyGtl9Cv152wXljASljhhEfrg8lUwN5ojDBWGIckAV5Ab8GOD9wH/SwUlIgwAupIgEDm7LA/qcRMaNJ0wkhhlDAQA0w0aHvt' \
			b'hQaygXhgY2CnQYmNFyYI0wurhNXCQitWWMhsX6FFwMDrBUiLhkbSL0HosvKoADVRqlE2l1Uq283qZQFQz5EQh2oOQqNhUWpJQlv6hCJg+YWP+pBep7bmeqEc2zGaM5BQ64XxbNc7TgYTWOyejWiIDQtj2bTSxmjWUXf8kFFHEB3DSeWeUzUpfkIELJMCm0Sh' \
			b'NesgZWQMyy4Zj33toqNBJNlnNq4wcQ3b0bDcRkX7STag6mJYcbpiKys9nyQLo1k9rlr7BOj94CzLrt29kFankYtsvZ0fUu/Ks5Cxh0Z+WkbQan5womWaWTKQ7YXrhJPCKeE0ChQ7NY/8M2kJs4mKlapphvOsSTSzmOeuArbGlerdFQ/nObY0iYnzjuJ5R+Hg' \
			b'ZyIOJuJgKXqNQzeEb9OqYLhblgBNdHvqawIkTVKy46BjuCTBdtfHMpoOG92b1jyk1OmlMkSt/ecPFY3e43PHjE0qzTb/y23mU2rWtvSstd0Pfup70Y8WPBbo2Pl1uA9C0wpmR3/BBYyKyxLF6xE1XoGscbmieJ3Cs5Plla/jfuG4XzjuFwun83ql2XlgSaFp' \
			b'R6jj1Kh5atQ8NcKjlpZnSh1nSs0z5UQumjh1scdBFIogVX3yLQ9OF5pNodkUOo5nesYe36U2GmNVI3XOAawpwIKb12wHzqgZdc2YSM5h40OziSwN+Ug0xURTE8xwKq+wDNPIMI0Mz3KGwtgxedtG6Qd0o57LNw3bTF1wmmaBdKCH7Vk1x3g5IsO4y4EylpWx' \
			b'rIy9D0MOSGPZ1vdAXGQCGZc+NQcsow1oGEbHRGo5RsMxGi5Ry7G6jkY+iVVQbn93dyRrVMOzGj6p4VkNT6x1IrCygXOFOO6Gu6wUiBJ2rg696O+yDiDTHZYPKdAv2dR3WUw82u3i2W4XT0c7Inon1tAoDEooHdZnB4lQHLomGY7PSXxNVyZ4gp6lc0X7pNwg' \
			b'haOhHAdx4WDMgIGiF74TXgmvhYceJUXQIkBfAiFACil6JXqwK5jUiR4lBrE60LMDwTqQkgwHlkNxUX80AMqNp4949Ijn2agpHglrCVoqMhm5FQiJN0XoBTFXdD2DT7yztJCsORd94oUhaLQCHVZ0f2ZSLaDkUCXdAOJNmONSgavAC0VZZMO7PTDICnBZgTFW' \
			b'dBUahYLSBq938K4HktDR1Rfkxn8IO0VXOCuFl68h1+kF3caiSJAIY/TKFW2SeyX+0P1D0O5PXFQw3og2otoPeDKY0NyAVQbKl2gkBHZZHYZUwQbn52BIX/xVJjG+UpjTB71yqVc0R51MEyIbOlQm+QZ1cvKQb4tSKcegVl34FS0HSTdDywXqmV3V2U/aRWEq' \
			b'tGg434vQHaO7QhpeDVRm79D08I9KQ5o2AAOIhsqsYMkBf9ST6T0B7LaIBNi4b/ZqLIAfE32aagObOPYV3dlRb3a5M8ccUz0ZvYw1XqPj1Xm4Tr/m+id7NZoHBXZJDEMK4a22wrZs1dHN5zCw0512dGlkl20OUC76nGBBrAUvYXOVBRWoVOAqmAxDtsbITnkP' \
			b'ZkCqc5IDpcKyrwC3nwPguDxKLgGO3gbglCu+1DMCPNZiu6LKAnAqFbgKBnzI1gCc8h4MeKpzEnBVuQpw91kArkV2GXDdBlwT4HoacE5HwHOVJeCaAdcD4DlbC3B9LcBjndOA69JVgPvPAnAjssuAmzbghgA304BzCgKeAyXghgE3A+A5Wwtwcy3AY53TgJvS' \
			b'VYCHHYDzXtG0YfeHIB82ztx2UcASC/zRiOBEdpkIbkQEjFKcgnSgZZ4ar/Mom0nVISNy3SUjeMGneMVHZaQoBVGN1Z/xXIipQQU7fuxHkFjzNEGq9iuC9IfsE0q2uOMQxhyyf9iTP+YADu2zi1Dx9VvcR0T/xE5Cjc8HaKFtuYBGjcnHlW2QzTPZuHYkW26q' \
			b'JBufFSg+K6AycsiJB3OS8+yz21DDKQLV1PFjJ/vQlsTAaJVpBnradgxaGFa72npI+xC2X8xNQPnhKvzJbwvsP4YdiZW3O4zRy+zs8jA23qIontIok0apycfvwW+Qq2dycRkkV66+JBdvVxRvV6iMFKUsqr1vUcO+hQp2/NhvJIs1T/Ooar8+l5Kf81yHZ8TJ' \
			b'5RPKbkQSjFKcgueUHZ1TdiOGUDaTqrNl3eVRZcdHlR0xhMpIUQpCGRpnll1mCBXkzHueXMaap08uq/ZrhqgtDKkOz2chiT0GT+QcXJEiu8yVegusI10k00UyXWgvrMd7YcpmUo22K6ov6cLb4dSu4mKFLDGlxZhha6x57UyPJmOoqoI0sfJp0lSuJo3+P2mI' \
			b'NEpkl0mjatIoJo1i0igmjSLSqDFpFJOGa0TS5OpL0igmTWyXH0qKUhzK0yCNGkijmDRqK2k2RpoYM02aSoSaNNvOTj8n0miRXSZNffaCQU2aE2k0k4YOYfT4EEYztLFGJE2uviQNn8OkdhUXk6IUR7fPZPRwJkMFO360SaNr0sTKp0lTiVCTZtv56zbSpOvh' \
			b'bezR8S55B4d8g0a+YJI8IZn8BqGC4L9EplBxKRCVAjEpEJHwEz6c41IbbAoEOaWAObwTPtdfsCkQmbhVxU8lRSj+SiL1vuLScIUTiElhG5FCxSOueZJFReM1hbad6G6j0E7+zMscR7v5sB9//LwU0vRNVnZ5TLL1mGR5TLI8JsVLfUtjUi66OTLF2/1YWVfk' \
			b'LEcmyyNTrFUln5KilCs1UdAqZFpRSZ/riAOV5YHKtviFKU5xtcVYFRuaHqs2Jaq5tu0w+fa5dtAQNTfFnMguU6w+eMSg7vmLw5yIFKOzx6HoJsX4BDImIsVyzpJifAKZWlfJp6Qo5UpNNKbA4ShS81Gkbh5Fyi4wtVxNrdjANLU2JampFcCGdCa5z3sLoSYT' \
			b'fzNXFezR6VpixtcSmpzQ8dCwPDBc2RCPCw985WA1cSthfTzAqzfjiHm6hDjm6wUNQFeKXydovUwANayvByhCaWZCU285dfFE5GlgEXBIx4EtgYz3/fhlvjHYswHdoTrHwhiV3voSQVR+Au9h8FMZ+zQAbnKAv8t7A+jHuNv5OrK9TmeeEd8WuH1jRztDH0Yl' \
			b'D+zHiKGcF8OdAKrjDcYnwG9v8HDNcdxBmL88f1rwCuRCL/rur4vfJnZ82WiPgKHeE0MztSa6+YJon4uLSRh9hFLNASfA4boWoHaMqeVNlrUjRCnzFkCtja6BZEqcxBFfSKV37eK153hhpBRdclr9EGlncZkEm2MI4XmEe0gnBeEhMwqyogU7TFW4loI81+zP' \
			b't7oylg0GoMVn6dB3b1WMq8RdK2NQaI2dhH5ZyyIOsA5Fs9CRHaz28dgEHQ0DTqx5s+1247wDZD9H9+6xC8ctLmGVeqppdtOIUuqi/O6UHb8xZXkrmnukia7VI2NiC4wb9zo/Zfr2cHsS6+PA2kLA4eFICwRXg8AnBXZ8IGBdDYKLrgVCTNzSI9yNgQgH9IHd' \
			b'Y52/+eBWIEBG3XuoKiDYOVIVKNx4YMKXbcDMYJZiHOqTWeedS+acRQpD4+P400M8iAyzTgvV8A/Tzro/zix+LMufbHI+0rRc21/eO/v7v5T9FX4JB9Sz6hX/jMR6YyFkAxkUHeUwdIfDZu7DhpGgFNiUNEBZikaX9Ktfa645lk4A9P2mrWmCLMxRfv2u60cV' \
			b'u0bFsusOqRmBKWum38rF99rwm0rY0Cp/Z5G/sVh+RTHeV+D9A56C43e7DJ6W4VkK78J1OsakqvQ+VRkx8UfFTV18/JXJfH8y+WoATJXxj3cb5d/UPmFJP2mab5z4a1rxhXtf3Cv5dJGUbpGsSjdHdG00vjOK976Sbog8XgbxTdCm9Ju3PGDT6/71RAwO4Mnz' \
			b'KAOp625mYUw42FHD/ih2zhbez7w4BrYd3/VtyRDsRGRv2kXwNe8YICOEG1pfi8MdNdxPNcxmPqB5I8aOp6PJpMKREOmt6ykpGOx9BeGfD55yQTaTkmNZZMXHlkDAvixTmGJYJZYT2eHvSLrdrpGNRSxeLd1Hvh3CeVyB4A/e+KaDFcWWVOlZLH0EywUxk2MR' \
			b'zdbBZsswMxpjdgww1Tv1nSgdrKM2YiYdLOG2pOLKbSqB1aznrr103KbgVuUULlGVig7XpykIy9IcX7p8ClFGpmXpVAlWyp1QKSuO7Fglf0KVgjiyY5XCXZjOcfd0O46N0KcVOm8qYJ3e080+LLKX/wN+ZqLZ'

	_PARSER_TOP = 'impr_sympy'

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

	def impr_sympy_1    (self, SYMPY, expr):                                return ('sympy', SYMPY, expr)
	def impr_sympy_2    (self, expr):                                       return expr

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

	def parse_error (self): # returns True if fix made to continue parsing
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

	def parse_success (self, reduct): # returns True continue parsing if branches remain
		self.parse_results.append ((reduct, self.erridx, self.autocomplete))

		return True

	def parse (self, text):
		self.parse_results  = [] # [(reduct, erridx, autocomplete), ...]
		self.autocomplete   = []
		self.autocompleting = True
		self.erridx         = None

		lalr1.Parser.parse (self, text)

		return next (iter (sorted ((r is None, -e if e is not None else float ('-inf'), len (a), (r, e, a)) \
				for r, e, a in self.parse_results))) [-1]
