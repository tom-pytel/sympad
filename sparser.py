# TODO: Proper function ordering and parameter capturing.

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
			b'eJztnWtv3DYWhv/MAvEAHEC8Ssq3pHG7xjpx6iRdFIMgcBt3EaDNFmnSLVDkv+855z3UZSLJ8mXGVhKMLIkUL+fykBJFzvhgc+/46PE9c+/ZC94/Pnry4hmHvj99TofjJ7w7+Y72z0+PvvsnX/nx8dMfOfbwW07x8MEp7Z8+OD18ckwnR989OTk9fPXNi9Nj' \
			b'TvTt6YNv9GD16Ogolzn5E6n0BynjH+dvX+drTZl88pBy/evwOZ+yDFzr05N/H0qaY0j74iHtH528eHh8+Ow5JOIUUueDb56fnB494OoeHf1w9OiQK3l0wsVoWq3gGCVxpqenR48PueTnJ7Q7/P7Fg2MO/fHhpz/P3tHJ+/O/3r/C6flfv7979fbDb/n0/fm7' \
			b'5vz3s3fnb3Pg7Kc/mvj//i+f/nL28/vm/MPbn/P5bx9+ffXmt99z8PWbP9+8Pm9Dv/zSVH3+n7P3b/4872akk6bMd2dNmX+0UnZk//VNE3v2+rWe3ntpNgdra9ZuZegYzUFlakMRzpl6leMkpgmubeIzJ38umLVfdcJtkE7oyHkLyVlg5zjGrjSKT/nMY+eq' \
			b'lQbXNvBZMgeWirIl/61yjO+EcjqO4awkh89CIOCdaGS7saEbiMaRWqkf5XulpH7A+a30FFV2w90AqcNnpGLBFbEJg/FsSGPrnG7oKtVC9r04TS/JOvKxlD9f5HgN2za8rkQ8ix3JuVq1p3RWmQMSHV6v+ISvVgbOt+yFQuovVjmCLhbKTieWSrSqa45bo4yA' \
			b'nWPfxdVWlGspyZFs835MmYNcAJ0Rq7ZjoKQmbl0zlqDrTroEkshmfcmpmJBPrJhPBKmNJwlUZY2hIMWuemm2rmuQQtJeqHk0gmmFbRwZbSiOQ228F8yocGoJ1K43dM1Ek0zJBnAVtzwCIlQm1CYWDAO1DMKczOBLww3fstAMFmnIvibLFNxw2KPCItVMvmGX' \
			b'OhO8CcGEaEIygSowFDa+NoHqsCYQlZ4ap0oaSRRnojcxmBhNpJjSxMr4yiT/krmmfmBDzuHuIMqe6iE1qCXJFc/B2xVyc+BEmAOypRxqkXBzEEXs5RibLrL8Xo0eoE6AOgfBIToWSAWfeIerpIIE1S3Img1hNUsQe+xbLR8VInjJimx33hskb70QQR3c66y6' \
			b'24EjByRcWIoacSmCJoCc7W1h7wB7h4ADesug3WXQhqlJC83ql9VDBe3064WJbbUHEnNflNomTR1mpYafo9feGd6PGgtSInq+KD1frE0qTLImOe4c0VOnnN24RTSBtAg5+enErfCA4PCA4PCA4LhNUm6nN1qHG61Do7SL0G7DN/9lCMqWvTUGgnjXlnC2FWcv' \
			b'p++ytSJciNyXuk8tg2N+XoGK/vIqhoWoGAFh7nE8ehxIf722FeIlrcbPJLD3olrChp+aliTwAZzstQEHuyjp5WnJzXj+CVAvopuNwlbvGWfDT0MOj0G4wcYaDz0YtyQ8Rx8kp28ZvLxl8Hrj9rhxe9y46bAlCIbOFukDEobRhF4S8p1T0tcI3c7A2FaqZMHH' \
			b'O08E30+89tPLkDcABq9sSPC2hiDA2kGiAthhDwYDwLSIjBA9RogepQ/hBuPQYNwg3dJeAtpLQHsJ0uACwiGHrYQX4MECeng+iAfD7TVXBxtCJM7ODqrhoASPJnHiVu9HZo7wSYRP4qJuAwFyh2XJzYiLuSF8IYdYi9MSXJgsqCJdEvyT4J+U20yC3knuTpaL' \
			b'kNTlAprOhvUpoU+Z9SmhD4dZjwpaV0hV6f2zWoR2QQS+rEHqRehGwi1BUIalXsEXi5CX54cKnSAqdGalkLZRmE0h/RpkUoESK8QaeJUYSlBxLAHEqqXKiN7eJDqh3oTqo1ZmTRlNZU3lTU1bMHU0NVfJYtCRRWfZ2Qg818Dvv3kmi8X0BYlFKpg1F9/5yDwt' \
			b'z0ZGnlKuzJqkWSffS9OmDZSG0pMZ1iTdmg0k8ZyXrzUpqWdcU7e4TrbN/5IfR+6kYWpeDEHF153PmGHqgc+QYRDfGkZTdgzT5H8p9xUyDOPIxpEZdgDb5bFns4bupC1l1H5FNmHZtiPluvu8V4yY1pnSs4FLulFRl1+LpR0buwqmIsOXpi5MbbdsTwoUpEFB' \
			b'KhSx4wtWjOJZtU/8Qtd4rqnrH25bPIHJ05M8N+m5R5MmuyZ1xGtrXv4Q2Oq8DIKXc/CqByPLTsgWQT9rWYBAyYJklKgRH8s1siGOQdalyAy+FONkz9iTIaiAkHINn2Agyw0ir8bgP15nIXmt7FkIqpc8w8s5fB8XWWlAf5yAE1qtgQRkFYoeSWRDLo0f1pGM' \
			b'/UxhTkypghDmmbCwS77SFGKjfE2QlW4SrjlgWXRM5RRXfFXvNk3qDlqyekT2I3BpFp86+ZUxyVWjRIcDMGPG2tQDvU0GLMtjcQBiItIgZZIImEki21QxyJkk7+odYI4OaOZvG+9z0yvr+2t2lbtPAH/ku+NX/i7mrzLYpvirwF/Vbj3+KuGvGudPi0id/Jm/' \
			b'CvxV4K/q89eknuJP5bE4KH/VKH9Vy18F/rSKYf4q8NdIErS6OfzFr/xdzF9tsE3xV4O/ut16/NVY2TbOH7Iwf03+zF8N/mrwV/f5a1JP8ae5seQy81eP8le3/NXgT6sY5q8Gf40kAeaYxV/6yt+F/LHusk3w5/BY1yQV/7X8cTDIfoQ/zcJT+U1+5U9y1SjR' \
			b'4dDy16ae4C/LY3EAfyLSIH+SCPxJIttUMcifJC07kgSYYxZ/5Vf+LuZP1o/zEvIJ/iz4s+3W488Kf3acP12jnjr5M38W/FnwZ/v8Namn+FN59KD82VH+bMufBX9axTB/Fvw1yQLMMYu/6nb5mxri3ikE5VsKLk4iGIFgZ+shKIvL3fjLHc3CCDb5M4IRCEYg' \
			b'GBsEpdBuhikKVSTkyhTGUQpjS2EEhVrFMIURFDaSBFhkFoV1fs9yBRLjbmD0l3/lMotKf9Nkytco1qVYIU3ymcBnarcun0le+a31KyEjiCKX7xaREU1ANAHR1CKKlzFITdaRhBe9ksniIXtmNY2ymlpWkxhUeEUhI7wm8NroEWChWbza4ord5o5gvcs9Z2Ww' \
			b'TZGJwXOT1PUHz6Shk/GzGx8/ay6fOkVkMjF+dhg/u3b8LIV2M0x1nioVcmUgR4fQrh1COwyhcxXDMGII3UoStLpZMNqv9/BZJNYG2xSJGEY3SV1/GC2+wJcoRzBEFsawyZ8xxDDaYRjt2mG0FNrNMIWhFoBcGcPRkbRrR9IOI+lcxTCGGEm3kgRYZB6Gbt8Y' \
			b'jkwEdhZm3DqP6QImKQLbBJMeQ+smqe8PrSWT7EeY1Cxs0ia/MukxtM6FuuYMZGoodHNOwJkzWxwApx8dZvt2mO0xzM5VDMLpMczumSHAOvP43PtUy+fApzPYpvh04NO1W49PJ3y6cT6RhU3a5M98OvCphbbFK58IhW7OKT41s8VB+XSjfLqWTwc+tYphPh34' \
			b'7JohwDrz+Nz7VMznwKc32Kb49ODTt1uPTy98+nE+kYVN2gaUTw8+tVDXnCmfCIVuzik+NbPFQfkcnYyWRMqnB59axTCfHnx2zRBgnXl8XneqBouG2rVCg6Da7cVAl8Y1dYgt7iS0JKGZHKljoJ700xsKMatJ9BReh4mVeLJsGUzZlKLIYpiOcp0eQauch9TW' \
			b'20G1Tp/QiqzWtOPz0eF5OzpPwilKH6QUo/JGhCDGmMfntadyLoTzprC8ApNpD31pMtim+lKg2ST1fTy98KnxVg8DPSqu9ErJPSr4zEW75kx7VIRC6osw1alqfouDdqqjqNoCMuSOFcDmaoY7VjDbEyjAVPPAvfYc0D7BDcJuuoP4lgbbFL5YJdQk9f1VQl5W' \
			b'CWm8TTgM4IsEamQNKL5YK5SLds2Z4qt1pL4IW/iKDhbFKsRaCiIzxKMLiHJyZRhriHJdwwxjDVFPqgB7zWO4Mht+fz9KcEttOfCgyowKmsyl78xNTr9/d6OLHT9BbQwxwaveQgkv1GesYuzCsx5fubjudHBrXUfRnUSctURx3Zk7HPH79uLEEWezp9m7W0sR' \
			b'SbDr+tDdkBvdhCeLJJ30sEfZ0zwBUHa862Ud5n68XMadOZqVn3J2NsKA09vO1DYA5M50AAQqeCeNOdxUew4LaNP10JKA6zdra90VmjbVcQvdc/GF9dD1Hjppkut2b7RVZar6C3Dmticxcx924FF/kUeLu/n0lNSl9rpujfgaCJtqMc9R/LUYWXyq6wi2HWv+' \
			b'dp4eld1H/DbbQh+OixHXsj/ufIu9ekvlZ8ax1hr5G3uyzhgDycQ+LfnrT/LqkkQqC9GJXz4WkiWZzS5dv5cR0TxXs0tv2tN7HAT1Gm055bUb6ZJv2nGjHfGMLhj+Y9ssxH9WFxxO+rD6Iloem3oXfex+W567TwR+xBe3P1uviZ13fGvcq9tsuL+uPuL3jD8r' \
			b'r7Ex9vg8s1+n2fsE5Uf8vvTn5bX4RXjN8Zei+ZkT3yH38h3BredRskpp8SRKjrAv8ZNKG00l7unYlqelYYU6qnKNPJI1Nlmzc3Vqp9wqRizK1uxZKs+uVZ8UnMYKri5VcN0vWP+1hvyuBX7Jgn/iJ09q6cwTf7eSX1rzlHmQ91V4ueHyW+SX8uP+F5fC/3pj' \
			b'6yNZPbIO/KzG5I9o6K9mdH8sY+gHMjx/YaLT/jisA0FpdF7bnJdP08j4p1k4PNCY8E8RdDbSxiHBC5lo7IqfRAPMJmIqEZOInRlELETQyULPc4R5RtAN6Ji29CRlrvQhNAmiHOKJg4FUonPcqZ8Iqqt8RLI07Y3L+KFn/rm25574MltlZe9zsJyd17cB0bzc' \
			b'qU/k7nKzm0hd7VZqZ256E6nrhrIdye35cYF785vcRPT2qzi7kj2YHWyQ3c6UPY2Kn9vypAbRzNmofxi9yn3F8DUo4i7bTfV1mdU19VRKBhv/tkG69LaVa6QQqOb3rBo/de98g2oX3OpvXjVvdr9BtXgl1firTFfXLpgrbDQgumQWKHjpB4MbUBC/CLrzDQqW' \
			b'u3gOvcojEA99xzesj5tOs7XRuHd2YtiiujO2COb2NtiivnPjEx6+3v6GsWoh4jQvAWhAXcu6KBoRr/4P6tGspQ=='

	_PARSER_TOP = 'expr'

	_GREEK    = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\pi|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'
	_CHAR     = rf'[a-zA-Z]'
	_ONEVAR   = rf'(?:{_CHAR}|{_GREEK})'
	_ONEVARD  = rf'(?:{_CHAR}|{_GREEK}|\d)'
	_ONEVARDP = rf'(?:{_CHAR}|{_GREEK}|\d|\\partial)'

	TOKENS = OrderedDict ([ # order matters
		('IGNORE_CURLY', r'\\operatorname|\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('TRIGH',        r'\\?(?:a(?:rc)?)?(?:(?:sin|cos|tan|csc|sec|cot)h?)'),
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
	def expr_add_3      (self, expr_lim):                                    return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_lim):               return ('lim', expr_var, expr, expr_lim, '')
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, PLUS, CURLYR, expr_lim):  return ('lim', expr_var, expr, expr_lim, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, POWER, MINUS, CURLYR, expr_lim): return ('lim', expr_var, expr, expr_lim, '-')
	def expr_lim_4      (self, expr_sum):                                    return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER1, expr_lim):           return ('sum', expr_var, expr, ('#', int (POWER1 [-1])), expr_lim)
	def expr_sum_2      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, POWER, expr_frac, expr_lim): return ('sum', expr_var, expr, expr_frac, expr_lim)
	def expr_sum_3      (self, expr_mul_exp):                                return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_lim):                return _ast_flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_2  (self, expr_mul_exp, STAR, expr_lim):                return _ast_flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_3  (self, expr_negative):                               return expr_negative

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
	# def subvar_4        (self, SUB, VAR):                                    return '_' + VAR
	def subvar_5        (self, SUB1):                                        return SUB1

	_partial_var_rec = re.compile (fr'\\partial(?={_CHAR})')
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
# 	a = p.parse ('d/dx**2')
# 	print (a)
