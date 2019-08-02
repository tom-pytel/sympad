# Builds expression tree from text, nodes are nested AST tuples.
#
# Time and interest permitting:
# sets
# var assumptions
# importing modules to allow custom code execution
# Proper implementation of vectors with "<b>\vec{x}</b>" and "<b>\hat{i}</b>" variables
# systems of equations, ODEs, graphical plots (using matplotlib?)...

import ast as py_ast
from collections import OrderedDict
import os
import re
import sys

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

def _raise (exc):
	raise exc

def _FUNC_name (FUNC):
	return AST.Func.TEX2PY_TRIGHINV.get (FUNC.grp [1], FUNC.grp [1]) if FUNC.grp [1] else \
			FUNC.grp [0] or FUNC.grp [2] or FUNC.grp [3].replace ('\\', '') or FUNC.text

def _ast_from_tok_digit_or_var (tok, i = 0):
	return AST ('#', tok.grp [i]) if tok.grp [i] else \
			AST ('@', AST.Var.ANY2PY.get (tok.grp [i + 2].replace (' ', ''), tok.grp [i + 1]) if tok.grp [i + 2] else tok.grp [i + 1])

def _ast_func_tuple_args (ast):
	ast = ast.strip (1)

	return ast.comma if ast.is_comma else (ast,)

def _ast_func_reorder (ast):
	wrap = None

	if ast.is_fact:
		ast2, wrap = ast.fact, lambda a: AST ('!', a)
	elif ast.is_pow:
		ast2, wrap = ast.base, lambda a: AST ('^', a, ast.exp)
	elif ast.is_attr:
		ast2, wrap = ast.obj, lambda a: AST ('.', a, *ast [2:])

	if wrap:
		ast3, wrap2 = _ast_func_reorder (ast2)

		if ast3.is_paren:
			return ast3, lambda a: wrap (wrap2 (a))

	return ast, lambda a: a

#...............................................................................................
def _expr_lambda (lhs, expr):
	if lhs.is_var:
		return AST ('lamb', expr, (lhs,))

	elif lhs.is_comma:
		for var in lhs.comma:
			if not var.is_var:
				break
		else:
			return AST ('lamb', expr, lhs.comma)

	raise SyntaxError ('invalid lambda function')

def _expr_piece (expr_ineq, expr, expr_lambda):
	if expr_lambda.is_piece:
		return AST ('piece', ((expr_ineq, expr),) + expr_lambda.piece)
	else:
		return AST ('piece', ((expr_ineq, expr), (expr_lambda, True)))

def _expr_mul_imp (lhs, rhs, user_funcs = {}):
	last      = lhs.mul [-1] if lhs.is_mul else lhs
	arg, wrap = _ast_func_reorder (rhs)
	ast       = None

	if last.is_attr: # {x.y} * () -> x.y(), x.{y.z} -> {x.y}.z
		if last.args is None:
			if arg.is_paren:
				ast = wrap (AST ('.', last.obj, last.attr, _ast_func_tuple_args (arg)))
			elif rhs.is_attr:
				ast = AST ('.', _expr_mul_imp (last, rhs.obj), rhs.attr)

	elif last.is_pow: # {x^y.z} * () -> x^{y.z()}
		if last.exp.is_attr and last.exp.args is None:
			if arg.is_paren:
				ast = AST ('^', last.base, wrap (AST ('.', last.exp.obj, last.exp.attr, _ast_func_tuple_args (arg))))
			elif rhs.is_attr:
				ast = AST ('^', last.base, ('.', _expr_mul_imp (last.exp, rhs.obj), rhs.attr))

	elif last.is_var: # user_func * () -> user_func ()
		if last.var in user_funcs:
			if arg.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg)))
			elif arg.is_attr and arg.obj.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg.obj)))

	if arg.is_brack: # x * [y] -> x [y]
		if not arg.brack:
			raise SyntaxError ('missing index')

		ast = wrap (AST ('idx', last, arg.brack))

	if ast:
		return AST ('*', lhs.mul [:-1] + (ast,)) if lhs.is_mul else ast

	return AST.flatcat ('*', lhs, rhs)

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast.numer.is_diff_or_part_solo:
			p = 1
			v = ast.numer

		elif ast.numer.is_pow and ast.numer.base.is_diff_or_part_solo and ast.numer.exp.remove_curlys ().is_pos_int:
			p = int (ast.numer.exp.remove_curlys ().num)
			v = ast.numer.base

		else:
			return None

		ast_dv_check = (lambda n: n.is_differential) if v.is_diff_solo else (lambda n: n.is_partial)

		ns = ast.denom.mul if ast.denom.is_mul else (ast.denom,)
		ds = []
		cp = p

		for i in range (len (ns)):
			n = ns [i]

			if ast_dv_check (n):
				dec = 1
			elif n.is_pow and ast_dv_check (n.base) and n.exp.remove_curlys ().is_pos_int:
				dec = int (n.exp.remove_curlys ().num)
			else:
				return None

			cp -= dec

			if cp < 0:
				return None # raise SyntaxError?

			ds.append (n)

			if not cp:
				if i == len (ns) - 1:
					return AST ('diff', None, tuple (ds))
				elif i == len (ns) - 2:
					return AST ('diff', ns [-1], tuple (ds))
				else:
					return AST ('diff', AST ('*', ns [i + 1:]), tuple (ds))

		return None # raise SyntaxError?

	# start here
	if ast.is_div: # this part handles d/dx
		diff = _interpret_divide (ast)

		if diff and diff [1]:
			return diff

	elif ast.is_mul: # this part needed to handle \frac{d}{dx}
		tail = []
		end  = len (ast.mul)

		for i in range (end - 1, -1, -1):
			if ast.mul [i].is_div:
				diff = _interpret_divide (ast.mul [i])

				if diff:
					if diff.expr:
						if i < end - 1:
							tail [0 : 0] = ast.mul [i + 1 : end]

						tail.insert (0, diff)

					elif i < end - 1:
						tail.insert (0, AST ('diff', ast.mul [i + 1] if i == end - 2 else AST ('*', ast.mul [i + 1 : end]), diff.dvs))

					else:
						continue

					end = i

		if tail:
			tail = tail [0] if len (tail) == 1 else AST ('*', tuple (tail))

			return tail if end == 0 else AST.flatcat ('*', ast.mul [0], tail) if end == 1 else AST.flatcat ('*', AST ('*', ast.mul [:end]), tail)

	return ast

def _ast_strip_tail_differential (ast):
	if ast.is_differential or ast.is_null_var: # null_var is for autocomplete
		return None, ast

	if ast.is_intg:
		if ast.intg is not None:
			ast2, neg = ast.intg.strip_minus (retneg = True)
			ast2, dv  = _ast_strip_tail_differential (ast2)

			if dv:
				return \
						(AST ('intg', neg (ast2), dv, *ast [3:]), ast.dv) \
						if ast2 else \
						(AST ('intg', neg (AST.One), dv, *ast [3:]), ast.dv) \
						if neg.has_neg else \
						(AST ('intg', None, dv, *ast [3:]), ast.dv)

	elif ast.is_diff:
		ast2, neg = ast.diff.strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			return \
					(AST ('diff', neg (ast2), ast.dvs), dv) \
					if ast2 else \
					(neg (AST ('/', ('@', ast.diff_type or 'd'), ast.dvs [0])), dv) \
					if len (ast.dvs) == 1 else \
					(neg (AST ('/', ('@', ast.diff_type or 'd'), ('*', ast.dvs))), dv)

	elif ast.is_div:
		ast2, neg = ast.denom.strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('/', ast.numer, neg (ast2)), dv

		ast2, neg = ast.numer.strip_minus (retneg = True)

		if dv:
			return AST ('/', neg (ast2) if ast2 else neg (AST.One), ast.denom), dv

	elif ast.is_mul:
		ast2, neg = ast.mul [-1].strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			return \
					(AST ('*', ast.mul [:-1] + (neg (ast2),)), dv) \
					if ast2 else \
					(neg (AST ('*', ast.mul [:-1])), dv) \
					if len (ast.mul) > 2 else \
					(neg (ast.mul [0]), dv)

	elif ast.is_add:
		ast2, neg = ast.add [-1].strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('+', ast.add [:-1] + (neg (ast2),)), dv

	return ast, None

def _expr_intg (ast, from_to = ()): # find differential for integration if present in ast and return integral ast
	ast, neg = ast.strip_minus (retneg = True)
	ast, dv  = _ast_strip_tail_differential (ast)

	if dv:
		return \
				AST ('intg', neg (ast), dv, *from_to) \
				if ast else \
				AST ('intg', neg (AST.One), dv, *from_to) \
				if neg.has_neg else \
				neg (AST ('intg', None, dv, *from_to))

	raise SyntaxError ('integration expecting a differential')

def _expr_func (iparm, *args, strip = 1): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	ast, wrap = _ast_func_reorder (args [iparm])

	return wrap (AST (*(args [:iparm] + ((_ast_func_tuple_args (ast) if args [0] == 'func' else ast.strip (strip)),) + args [iparm + 1:])))

def _expr_func_func (FUNC, expr_neg_func, expr_super = None):
	func = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC

	return \
			_expr_func (2, 'func', func, expr_neg_func) \
			if expr_super is None else \
			AST ('^', _expr_func_func (FUNC, expr_neg_func), expr_super) \
			if expr_super.remove_curlys () != AST.NegOne or not AST ('func', func, ()).is_trigh_func_noninv else \
			_expr_func_func (f'a{func}', expr_neg_func)

def _expr_mat (expr_mat_rows):
	return \
			AST.MatEmpty \
			if not expr_mat_rows else \
			AST ('mat', expr_mat_rows) \
			if len (expr_mat_rows [0]) > 1 else  \
			AST ('vec', tuple (c [0] for c in expr_mat_rows))

def _expr_curly (ast): # convert curly expression to vector or matrix if appropriate
	if not ast.is_comma:
		return AST ('{', ast)
	elif not ast.comma: # empty {}?
		return AST.VarNull

	c = sum (bool (c.is_vec) for c in ast.comma)

	if c == len (ast.comma) and len (set (len (c.vec) for c in ast.comma)) == 1:
		return \
				AST ('mat', tuple (c.vec for c in ast.comma)) \
				if len (ast.comma [0].vec) > 1 else \
				AST ('vec', tuple (c.vec [0] for c in ast.comma))

	return AST ('vec', ast.comma) # raise SyntaxError ('invalid matrix syntax')

def _expr_num (NUM):
	num = NUM.grp [1] or (NUM.grp [0] if NUM.text [0] != '.' else f'0{NUM.grp [0]}')

	if not NUM.grp [2]:
		return AST ('#', num)

	g2  = NUM.grp [2].replace ('{', '').replace ('}', '')

	if g2 [1] in {'-', '+'}:
		return AST ('#', f'{num}{g2.lower ()}')
	else:
		return AST ('#', f'{num}{g2 [0].lower ()}+{g2 [1:]}')

def _expr_var (VAR, var_tex_xlat):
		var = \
				'partial' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_')) \
				if VAR.grp [0] else \
				'd' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_')) \
				if VAR.grp [1] else \
				var_tex_xlat [VAR.grp [3]] \
				if VAR.grp [3] in var_tex_xlat else \
				AST.Var.ANY2PY.get (VAR.grp [3].replace (' ', ''), VAR.grp [3].replace ('\\_', '_'))

		return AST ('@', var + '_prime' * len (VAR.grp [4]))

#...............................................................................................
class Parser (lalr1.LALR1):
	def __init__ (self):
		self.TOKENS_LONG.update ([(v, self.TOKENS [v]) for v in self.TOKENS_QUICK])

		lalr1.LALR1.__init__ (self)

	def set_quick (self, yes = True):
		self.TOKENS.update (self.TOKENS_QUICK if yes else self.TOKENS_LONG)

		self.set_tokens (self.TOKENS)

	_USER_FUNCS = set () # set or dict of variable names to be translated into 'func' ASTs if variable followed by parentheses

	def set_user_funcs  (self, user_funcs):
		self._USER_FUNCS = user_funcs

	_PARSER_TABLES = \
			b'eJztXWuP3LaS/TMLZAZQA3qQEjnfHMfJNdaPXNsJdjEwDMdxLoK1k6zt3LuLYP/7VtUpUhSlnmH3vLqnG6NpSUWKj2KdI751cv7Vv73/7eevqq8ePn/y/Bmdf3zwgn6fPPr2FZ2+f/Di0bMndPH4u2fPXzx68/CHF0/+k26/ffHgoZ4aPbd0/vrRd28ePnj5' \
			b'6KVeP33wSq++Hi9/HC+/x6WEyrE8ffzsB3mWwvt3Frx8xYl5+cPX9Pvsh6eckGevvuP0PX4qDvL79xccyhNO/ZPn7PrtD884eV9LVh4+f/r0QcjLixDdixANX7x4/N3fOIgHT7+n32++fvLyyYOXf6PLR8++0Uzw1dfj5Y/jpWbi0d/558nLRyoOeuDQXiEh' \
			b'lAD2+fTB9y9fPefoXkn2Hv3HwyfBmbX5zeMfH3/DwTz85vkrUYI8/viZRPH9E1HR42/pR0Ih7fBT795+ev/lze+f3vz804fPX95+ItH7//nj05vPf/7xPt789v4fb37587d3o+NP4fLj2y9v3v3+Ib399Pu/stvP4f7d28/vP39+N739Y3ob7t7+NF5++RLT' \
			b'8svbd1/C9R9jTNPkfQyXH36Nl7/+9uUfMV1/fnjz68cY8W/jAz//+s9w+eX9p0T8yy/h+qdPb9/91/sviXJiBv789OF/0zjoIlFFzM7PP0+yPKbw/X/H/FAkMZu/vn/3Pt5Qgf02BvrH5y+/h7t/jsX34e3Hn35+G+5isEFA5f3+4x9fYlo/f/h1jOHd7x8/' \
			b'vp3cfP7qdXV+sjJdZdrTChcdX9hq1fO566qTrmqHatVUXUsXp0EK2ShYNTVfNRY/tiUJHIOIjkTEl/xkix9jT/WWAuOrtuaYm15j7prTIFVZFKxaSXtjqhNPT5vKwIkEqwa5MPxjq86c6i3dyVUveeXka/xBgDsbnqMH+iDiS45Z/ltH90gJX3C0KkcaKHUq' \
			b'xL2j9BtJfx0ElAd5nv0i6x1+DLshXYmIdTdK+ZKuONlD1VH+oeCeLzi5DX6Mpp7i6JAgSj7rkdMCrbBkSO+cnlnEkXkqdJQIaYQCUjWrfGXauSi5NXMfZnpL+TL1XNTORcltP7+dPLDqYJadmiWlu4Hymk4u2Rtpj+1IYm+jhyAeb1etKHWgf8dl2ASzIb15' \
			b'8UNOVI5UqKxYV1kjyuJA/Ol6D4w7AkyRvyYPb9VKQXnOUl0Zw8iFYNU0ktFekUTOq46sxCaAYscoHyUNJP0oaSEZRkkHiQsSsmWxMY+fBFSer/jC4UfwhAx0Ti75agiOp3pLd8EBcQz4MT7mP4hsnYr4kpVj8UNFd3o6XrIfSqNwkD5CAbaiK9PAQQ3IMCYR' \
			b'lqkQqNG8mJAo4SkTCNJHoYiSeytFaSPwOcWAYgNrtKywio1QlZzKg4QEopMaP2Svp3pP4JYrSRvDU35OpzK91SwwmTpJht5a4IGKqW1H45Pyq7qADrU8F1RDwpMEdHLbjaEStwtqKETSYrhyetEENxiPq9pTeiWd1xUVFiGO7JuIhJVf1/RPiKiJmHzl66pj' \
			b'MyJbtoQOXzWU1J4OW/mm8m3lu8qbytNtX3m2Us4F5ZBKlPRJcOIXUl8Nlat81fdVP1S9q3pfDXU1NNXgK1dXrmF+JxZxpnLkn1LZsU5IFU3D/5QeFpK0w1uqq5yrHCWR4qCk9ZWlcOuqb6q+rXp6uKZg6r5irXQMVkMlTrcDMzvZNdkxURRxgad0EYZ6Qlwl' \
			b'UZGJ2ap/XZ3QzSm9tEk/XN6kIzlR0KQ45lRxFXWdMrQbcWBJKxJSnvjs4LGTB046q95Im/IcZ+30WAjrCoEzK2pSffdQYw/d9hZS30CKMmpQAEY17dujhi/QsFcDbd1RTRepSQ3Qgw48TI3yCCPrRHvI3TxfyE7MSJ4LSjwpkiIxjZKFv5bQlMGslPCJBXQG' \
			b'sFNgK8kOvcrpJUT1IH4/+Ko93GJuei1m6AonV6u2nKgQ6aVkjsm6uTRNNJ4q+orWcc71yiPg11oCvWoEKQMlfqgGVw2mGmw1tNXQHbBO3FEnM534o05ynQz1USfZm2VAHdXh1OqbBbWJULvt0Jjo4KdrUcuVNEsluNVzaFPgxe5EvFdvnxOH5o/TnFjowcrb' \
			b't6k54UYLORbpvXjtnthBGzIo015bLlrUfaetSbWLWqsjRps0cDYGauIUU7g1aaiv3LBzmaV0Ix+m35sEo3psYJ7Gp/a4D+m3MCsrZoVEpsnewQTDsr3LLERa7iDJrg+NrEFREXhRyeNYj73oXcyaQc9Ve3rUy6gXVkWrXXd0PnBtULZJCQeWbe6FbbVbkc4H' \
			b'WvRe7P9IoGsbeD14oj2q6SI1maN6Luo/bsE0Xl7Dh6qFVvnWo07i+wNWhgwatFfu5j+fDHu9jkOKPIjQavc/ne9jY/r8ZJCs3bNMufuXKR5nEmNstAmH9nXb6Gh6q6PpaPC1YbxlEBO+Fxo451Gk+5IZHgiT4sSQ4sLw+2uM0cvsJWb6fsADA6QDzGAIY/QD' \
			b'+okGfXRAP1fv8KxYAfcpSxCdVFe5d5TVuY/K06qAtWiRT/o8LCqb2Sht3aU9v9cKzDrMrEBruId2+1YmCElPZKs9kC2KkxMw1vPw6kZtT1/gSZ1vfJmj9nfPX+ncMwttidXvaiehmNwuJ89dv5V7WLnrdzfnJ07HBozdXevhvnyY+LDLidS6r3E7nEirLzTb' \
			b'7HAiPd7BnfaB4CURe5S7MAey047Ujl8aTvvtDdzptdAdbCuPuxY71JFEGZT2DvWh4wB5NvWqFc2ounDjxcS426DTboMO3QZiZ52KLXxN60wDZPkMrgUpN046bZy0aJVwveyQ58FJU6xFU+xwe2jYTjrYSYe6r0K306ZMizYMN9cPGbrn3HA7YDPpwSo9rGWo' \
			b'YR9dA+PZv9k559y47vaycS2t6u5+dndKN0CrbfUObfUObXU6xcaTTe5MqzWz6ZoU06l40FodKnkOjGbwljV4gxoYt0Vc4U1JVT5z4GPmXK81qNkZrdmZ0NOF6oyR6oxBPcZoBcYc3ih7C9tpvL44UcWLnX2t8iUUtpd8aaVcsxpoX8MgGpw4e9qjZrRHzexs' \
			b's48BbmHcVo3bhroPjNuKcYsfq37wSN/gJF4OlBvAw4ebfzZuiyGBXk2jh2n0MA06UbIVDj18DupzuCejJOec3wH5HQQ1GN3SsS5K9ZB1/3PuHfTk8JwLXt19Uoq/P5lp701mxMy8zkmvdVJ6LW+yuuKF4kRmHD3YCAniILB2sOa1g20YGOoC7yH1aSrHbPec' \
			b'Yc5t0BKRJBSF7jBSKb0aiRd9GFRixXlNPOWFM8zR87AxjxnzcDIv0OaJR7xsm9ds87JWXifBC695IjHrkhdr8hJLXiDJeuP59DxTnaep8wRwnkTNM6h5bjIvnuS5+qwUVggXIC9C5qXHPODJHXm8KopXAfGqFx7J5DUeXI3hwQbu0+dqN9WTGx4n5XWk3Kda' \
			b'm6rl3lTKS9sQEZ5jiwne+4I3NKh5G4hKdkHh7K6s7DLBe07QQUIKZkWakY0TeCcDK3uwVLwZBZX4ysl+CnS22HpEdrJo5Id3Fmg4aPqnol853qWAQuplaxnedIR8eC97TshGCLybg681HbxFgUMyKIcr22toRhLNjpwo3h2E9zKgpzzvO8G+eP8YiYKTh/1j' \
			b'Vj3ngrcrIE/0CpRNKngXhqGSfT8o4oGD5MhJ2nMqSd5zJmUfBtmoY8UUumIOXTmOmHeV4ERwWI3s5sGptxwFZ5tTzVqpOXG8zwPvqECXugVKzwrmCGvemofc+/Y1110DAswiBoxs+7GEBO663BYMVOhKHB3XGYDsddgwd4cPrtlcGSOuFCdcmoqTPtjSRUip' \
			b'9X89Ytj5ulEjqUT0DSM7JuMyJLGHUjSxRq8RTBzS1QHFIReAqvrLngnPuTMOr6/PoCvD0ub/pKJEmHMBZRFi0i+PtepkAuOEU3nLpe/gy0FnE9zJKxe17mUMtlp11xeslxp4G4ZuwkgOGQZqAwzPfoLQJkFpn1b8Zq9k2e5C0Nsrgl2GYkZpnSB3yBDLnNTN' \
			b'kcvrmnhR0wzB3NQgf7wAj1eo8e4kxYgmGU/riYi2C4gmOW80oahuvAeyuQOKO59IB1OUs0LqCGS946dl4yqc1ItgGD7SoxDRfKOA5ssU05PQMnzP48ujDyDP5S7kKMBePNeaNZOGUHv4G+AGrwZCqyoZCSEoSSmA4R+hH1QyJQCVJjSQRt6FyxJKkJjjE1YF' \
			b'EzYIoYEPJOJphCk3ECmwAk17xpRL+DlDadnujKmKjI3OLbNEd2SJu2CJu2UHztDIDrijpwfZCw+nGl6EHVzwFI9CdmBjV3bgy5QdXHLM2KG76Bi6kR1cFhDYwY2VAvHMBoFKNrxB6OFvkJPBUwZCKjk+peygSlpkB1VJxg6QJuwwJpPZoYwXOvCC6s8iWVNe' \
			b'QDzKCw5VhTSq7XjBTHihG6lBK+h3TgrrGKEvJIUjISSEYGQLPSUEjhYCb2KFv4n1fbilR2ldwYx1BZPVFdLQcjaYxTfxHSsKmdyJyax63KRNBLEFg9qChlF7eBvggIcMhBaZT8lAtbNIBqqRjAwgTasKSeSlZGBABqolFUzJQHOmlQSDSkIS1QVkMOcAu1g3' \
			b'2HUCOKJ/U/Rb7Hms1QHcpdC3Efo2P0qhb0fo2wz6aWg59GfxTXxH6GdyFzKygHsL3GsAtYe3AQ54yEBokfMU96qaRdyrOjLcQ5rifkx9Me4tcK8qUsEU9xAG3FvgPolqI9z39xf3x6ZAhn1+cMQ+7lLs+4j92VGKfT9i32fYT0PLsb8U5eg7Yj+Tu5CR2D/g' \
			b'FfkeyB9DqPWJAW7wajQxyHoKftXNIvhVHxn4IU3Bn0ReCn4P8GuyVDAFP9wC+D3An0S1XQtgOLLAobAAd/Q0kQX0LmEBcRQWgFt6FLIA+1QW4MuUBSahZSwwj2/iO7BALnchI4EFxLMMhggLJCGIMoQFxA1eDYQWWU9YIOhmiQWCPqYsoNKEBdLIC1lA4uyi' \
			b'jlQwYQF1UxaQKKdRbccC7sgCB8MCLRdqZAHcpSzQRhZo86OUBdqRBdqMBdLQchaYxTfxHVkgk7uQkcgCrbJACxYYQ6g9/A1wg1cDoUXWUxZQ3SyygOojYwFIUxZIIi9lgRYsoDpSwZQF4BZYoAULJFFtxwL+OEpweHRgqnbsFNQ7jxNlTE41vIAUTH6UksLY' \
			b'L9hm/YKT0HJSmMWXRx95IZO7kKPIC0Z5Ab2CSQi1h78BbvBqILTIfcoLqqRFXlCVZLwAacoLSeSlvICOwaAmFUx5QTOnvICOwTSq7XihqY/EcHjE4LkUIzHgjonBgxg8iCH2HLSzo5QYxp6DNus5mISWE8MsPi6HyRORGbJ0uZClyAzae9Ci9yAJodYnBrjB' \
			b'q9EEIfspM6iWFplBdZIxA6QpMySRlzIDeg+CnlQwZQa4BWZA70Ea1ZbM0ByZ4eCYgctvnHakd97gm1wNTupFmAE+0qOQGbpx2lGXTTuahJYxwzy+PPpADLnchRwFYuh02lGHaUdJCLWHvwFu8GogtKqSkRiCkpaIIahkSgwqTYghjbyQGDpMOApqUsGEGNRN' \
			b'iaHDhKM0qi2J4Tgv8QCJoZFPcQZiwB0TQwNiQAdDF7sZ4SM9Solh7Gbssm7GSWg5MVx2jMSQyV3IUSQG7Wns0NOYhFB7+BvgBq8GQovcp8SgSlokBlVJRgyQpsSQRF5KDOhpDGpSwZQYtMCUGNDTmEa1JTEcpyIeIDG0XHiRGHDHxNCCGFoQQ+x5hI/0KCWG' \
			b'seexy3oeJ6HlxDCLL48+EkMmdyFHkRi087FD52MSQu3hb4AbvBoILXKfEoMqaZEYVCUZMUCaEkMSeSkxoPMxqEkFU2KAWyAGdD6mUW1JDCYnBnsvuIHXB3ZHjrh8jgJHEjmC12h6EXh5Rch6hh6TFfpAE3gkPUonK4wzlptsxvIktHyywiy+PPo4XyGTu5Cp' \
			b'OF+hr3SmUlhIgnkLY0g1ss96xczlBjOXG8xcbrKZy3BfnregqsnmLUCazltIIi+dt9Bj3oKqSwXTeQuacp23gJnLaVRb0sWF0xa7HSCKnZi5mC9S3JQdbosZqNj4CzPElpf0Sg5coLFXEnfJ6CVpWtzRJTnkxxYrGPmpCUFIuYz/s37JWaSTBMQ+yUweZjNi' \
			b'uGJw1TibkZ25wEKEwTqEG8Kip7DqKSx7ytY9BU2N/DBMOidVO1nnJKTZCkjJRXHX5ICuyUHWQA5OEzbtm0Q0oW+Si54TTSlFL+WouyWu8P5MCNURZ1gr1NCvW9WwczWJ7uorHI71iIwhHBdnXOUgi8tlta+Rk2lwquELPOHyo3Towo004fJ1kSYJLueIWYTZ' \
			b'0Sd1iTxpvOShF/Zz4wCGU6pwGMCInmUAw2EAw2EAw2EAw2EAw01pQnW1OIChmsk4AtJ0ACOJvJQlHFhClaWCKUnALZCEAzUkUW1ZjVie/7hzRHHsjrhGiuASGgcw9I6eNhjAMBjAMHEAAzfpUcgPZhzAMNkAxiS0jB7m8eXRB27I5S7kKBCD0QEMgwGMJITa' \
			b'w98AN3g1EFpVyUgMQUlLxBBUMiUGlSbEkEZeSAwGAxhBTSqYEIO6KTEYDGCkUW1JDMtTIq+fGGY7Gh3p4a7poeFyivSAO6YHDGNoS8PEYQzI0qOUHsZhDNkYhPsCeE8j2f8q8IQEKFuJzgc05jHnCYlEkcldyFskCh3QMBjQSEKoPfwNcINXA6FFslKiUHUt' \
			b'EoUqJyMKSFOiSCIvJQoMaOhjVgVTotCiU6LAgEYa1ZZEcZw1eYAU0VVm3FtB75gisLeCwd4KJu6tAB/pUUoRY0eEyXZTmoSWE8Msvjz6SAyZ3IUcRWLQXgiDvRWSEGoPfwPc4NVAaJH7lBhUSYvEoCrJiAHSlBiSyEuJAXsrBDWpYEoMcAvE0IEYkqi2I4Z2' \
			b'edbk9S+quIEuyYB/X128T9oN4XtrbF8Z15ZVG3GNu6R70cRF0nBLj1JEj4ukTbZIeobiWRyT+CKEM7kLiZ8sjDZYE726bMu0kOlFnGpGM5xCmuI0ei2CKFY+6xN2tuw5BKX4xLLnRA2bLXtul6csHmG5y7AcuJ0UYYm7FJaxyx9u6VEKy2GE5XAJLGdxTOKL' \
			b'sMzkLiR+CsuhEJaa6UVYakYzWEKawjIKi2CJrnt9YgGWGpTCcgAsRzVsCMvlCYNHWO4yLD13XERY4i6FZVwcYGZHKSzHxQHGXwLLpWjG+CIsM7kLiZ/C0hfCUjO9CEvNaAZLSFNYxrQUwRKT/fWJBVhqUApLzPRP1LAhLJen692LlcHHBu0IZdb/2OeldwmU' \
			b'beztglt6FELZjr1dYskJlCehZbCexzfxHWCdy13IyHx3IIsurhBA7eFtgAMeMhDCMlPAB9UsAT6oYwp4lSaAT1Jf2oy16N8KKlLBBPjqpsC36N9Ko9oM+LPpeEfg30vgt6z/CHzcpcCPk3Lhlh6lwB8n5dpsUu4ktBz4s/gmviPwM7kLGVkAPubkhgBqD28D' \
			b'HPCQgdAi5ynwVTWLwFd1ZMCHNAX+mPpi4GNCblCRCqbAh1sAPmbNpFFtBvzjfoCHAfyOlR+Bj7sU+LHzGm7pUQr8sfPaZp3Xk9By4M/im/iOwM/kLmRkAfjouw4B1B7eBjjgIQOhRc5T4KtqFoGv6siAD2kK/DH1xcBHx3VQkQqmwIdbAD46rtOoNgP+Pd4Q' \
			b'8Aj8BPimsuOOH3qXAj/u9QG39CgF/rjXh832+piElgN/Ft/EdwR+JnchIwvAx1YfIYDaw9sABzxkILTIeQp8Vc0i8FUdGfAhTYGfRF4KfOzzEVSkginwNWcKfOzzkUa1GfCHi75clU6fTT/cs7OEcJNbg7cL3wYa9PtAKVf01zT9fhvOIH+km2Xu6Bf4o9mG' \
			b'Q3z5Z7gYF56Ppa8L2dhFaGfHFpP1bdZHOAkuYxt8S4z7z+qFyG3SZZjLeQbuIJzjlzgHXYchjFqfGeCAh4ymqIZeRs7hYpx9Aoz99Dhd+O2ioLaMlCDNZvHH5BWyUvicUeMxJY8f1iWCCGc2MY8/bKSxBKJCZ2Si4IyoSEY0JY5ngn75bfiXeUs+oSUuzF7W' \
			b'C3m56vx2Prq3c1/cu9UvivGXqXbto3s7+8E9UdImqLrSR8IYBX49CsyNfH2SsrxjcNgICs2VPkJZ+OZbhcVpt/sRStbkbuJioxeNG9bAogwSpMi1kJjXZq/lg6z1jUDC3CIsSiBBcj+M0KC8tbK9835BxN4kRFiRO/S9VtTnuwiVUKefQabZrC51lc+2zr9h' \
			b'TOW3r59q7QqhY6/8RrkAKtstb97qs8asuSlc2sJpTDfwVuGW7YZvFl8IG7f8dqn+IhOR77LKtxXb22qBoOJ12TeOtwSNbKBJbl17y1Wxq7RKdvpb4NK/oP83865BPbaTDp+7/kY4s1vZJ42peM8oDYKdjlqWN4sahUkbkNJUpKhN8XKLTZSAiYF7Oepstl4R' \
			b'JnYEBuMn+7rxvcHx5CN0ReZ/iw0QtXAkth0tfYO2h7kts64rKjK17PqGjXuh4/pKBk73vCHIPTJ0ts12NHYeMLI3a/DtfOH1lYx+JV+R4YfN1sZvS42fB42uaP9oOfirG3/J6M3CqM3WAGjviuXdzQEgGj63RIbrMH5O7WaMP/TbA4DrnQKCKxh/X8z89fUY' \
			b'/2j53W1Va65k+PfU6FODZ+XcWhXnKgZ/VWMfio29uW5jN0dj3xVjbw7D2F2xsRdOgSk3dns09l0x9nxe+T01dn9bDditui/voDsmWrTZtIuy4/lrO9NI3b4D8vZ7YILh8ty0TSZEVH8NZ8Qm3MFIWj0a8rIh72s3y7VZME+PvCULLqXe6i+ygTOClthuc0u2' \
			b'SzmedCTekBGvmfx6HX2Ie2/UjWxB5tL+wxuj6Ga4wX7Dzesa5HQjZr5mVnlO1246S/wWWbt0Vvcicy9VP3o19m53DB5T7af/l7G6+JlMqb7NCkr5jOgljp/XUHhfe/nyAQc353trz4gUhO5vaCz0iIOdwIGb/V+OA3evcNAqDtwlODDVeVyFGNcfWrF6K/Ye' \
			b'jT1snz9ZpCcmt2BqQ754zrE5NFC+qURjZiz78DUZ+TyqmRU0F3Iss3SJmLxhF3Sat2H6Xl5+doPMToA7AKwMxJLcC4CWlg9OtcCmt5kWGnnzpxY8WmyZZuxcOSbqp99EP/2yinZDTfUC2IOqAnSvrK5hE3Vd/GaQd8JGL4QSBReT/VIhhNp8d9XC4Jxk/8ts' \
			b'3MNtQwYuKcYNVl7NSzt8Tan2U+p0y8V/R90ba5dOX0cL8KKKwNpW34U2s/yW9/3VW3fbt+gWFx9f02S+9a/s9d0TnTujao/Ymj/a2ta2xpaze/1jibHxcururo2t5a4wLs6zFb9R6rOVY8ujZB8tb2vLM7tueUbSuJuW1yxZ3l2OIOyP8XFn+86ODOzWa5Yt' \
			b'rd1pS7uJ8akSa8s+E1loecNtWp7Eto3hyTSDG7E9DnnZ9Hj15vilxYwE519WpLJMrXI3BlF3wjAvNUa2vL0YJE2p8CaWEG1Hh6Y6Z7Nz2vJntcPBykcbLMvRT9G8PqXrk1XY5l82L2qxm1BYOkctefZfkRp5H4O6kg6adrIIzjkOf9VeGgyZf/4nT3YLT9b5' \
			b'w4SX+MfL8vRPAjDLATSTMMjN81bcVfrHi/vitZOeoZWdhGbyTZvmgWObJYki7IUWh3B1vyJew4e9g3hPoAp/ZHJWZq2Fg4W81BB/WNDeY5UtqZ48MLIGx1cyeYxXJWKVuSS8L034bIuo8rTTQ2v+eIRjvSv9SRqH0jQu7WR1aTJ5G6eY1KFa98cDMutdBxkg' \
			b'obMk2KUJ5m9VNZLs2V5ezNp22lN46ZempltycUnGBd1hQJD31eK3CO+7xXtu8X5bbr0SJnthMY27UTFCzTbZw8qn+1a95hcW/vgVY3B21VSYHm7hb+4rCWyNy8LTDX/ozZlJaiZBSNH427MlX13hTxLb1Hlqr25CC/aT2M62dlNsL1LXGA/5yHYuyY7MQ4n/' \
			b'uXAxnMxpfi0HiqK5PcPhAripA5lpb8WurpGXyu1rqG78sH1y07fXFTCKprtFO+O69g0dyIzZ2xdhscFxGy0cnCxbpZKtD25wXUtABQfK6pIqrLGXM8CF5pdqNZogt23XH6zsCz1wk3TZwbXpPXLYH4A12mrPDxTVJVX+EmNEeWxhkn11xSN0khT4RW73t71Q' \
			b'bJjcd7XfB4pq1n6YF1KxbaJINrTQJd2aKj2oHDJJ+RH69Er85v1y0qFTH4Ap22rPDxTVrEWzC6bcV3d6QDPtARjxUO35gaKaNZd2wYhddacHNHMAbS+qZ+35gaKaNb2ubMT+ssaYKbRlAwO5voNLetnBNRc8B0XNRivWWfO16mqNaa7XmakuPvxwiYfyIwtq' \
			b'KWSobtai2k3V9dUuHVCd2w/VuWqXDqiuoLm0ZwMYPLWi4MCkivG/8LGLgtg0uEV/GDy/f+NKPN1lzw4URUErbN+Koq/27UBR3M6o2K0WxVDt24GiKGjW7VtRuGrfDhQFtSNbnkw1oLHCG5DKvdN3Sc/3rCSW8cxFLUKqcKblRZpkD152UjS861Yz6FQut+ST' \
			b'9+caD3j0M49cKOy5qdKj0bTy/jRh/hovt2tQF+atP1LDudAInJXJb3Y6RTJObVyY1ug1lnYaC1lLXF4nMUpMGkuDvgUyGTxL9t/4XoYXKe+vT/8fPc/NTg=='

	_PARSER_TOP             = 'expr_commas'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	_VAR_TEX_XLAT = {
		r'\mathbb{R}'  : 'Reals',
		r'\mathbb{C}'  : 'Complexes',
		r'\mathbb{N}'  : 'Naturals',
		r'\mathbb{N}_0': 'Naturals0',
		r'\mathbb{Z}'  : 'Integers',
	}

	_UPARTIAL = '\u2202'
	_USUM     = '\u2211'
	_UINTG    = '\u222b'
	_LETTER   = fr'[a-zA-Z]'
	_LETTERU  = fr'[a-zA-Z_]'

	_TEXGREEK = '(?:' + '|'.join (reversed (sorted (f'\\\\{g}' for g in AST.Var.GREEK))) + ')'
	_TEXXLAT  = '(?:' + '|'.join (reversed (sorted (x.replace ('\\', '\\\\') for x in _VAR_TEX_XLAT))) + ')'
	_VARPY    = fr'(?:{_LETTER}(?:\w|\\_)*)'
	_VARTEX   = fr'(?:{_TEXGREEK}|{_TEXXLAT}|\\partial|(?:(?:\\overline|\\bar|\\widetilde|\\tilde)\s*)?\\infty)'
	_VARTEX1  = fr'(?:(\d)|({_LETTER})|({_VARTEX}))'
	_VARUNI   = fr'(?:{"|".join (AST.Var.UNI2PY)})'
	_VAR      = fr'(?:{_VARPY}|{_VARTEX}(?!{_LETTERU})|{_VARUNI})'

	_STR      = r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY - AST.Func.PSEUDO)))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LETTERU})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\$?{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LETTER})'),
		('LOG',           r'log\b|\\log(?!{_LETTER})'),
		('LN',            r'ln\b|\\ln(?!{_LETTER})'),
		('LIM',          fr'\\lim(?!{_LETTER})'),
		('SUM',          fr'\\sum(?:\s*\\limits)?(?!{_LETTER})|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?(?!{_LETTER})|{_UINTG}'),
		('LEFT',         fr'\\left(?!{_LETTERU})'),
		('RIGHT',        fr'\\right(?!{_LETTERU})'),
		('CDOT',         fr'\\cdot(?!{_LETTERU})'),
		('TO',           fr'\\to(?!{_LETTERU})'),
		('MAPSTO',       fr'\\mapsto(?!{_LETTERU})'),
		('BEG_MAT',       r'\\begin\s*{\s*matrix\s*}'),
		('END_MAT',       r'\\end\s*{\s*matrix\s*}'),
		('BEG_BMAT',      r'\\begin\s*{\s*bmatrix\s*}'),
		('END_BMAT',      r'\\end\s*{\s*bmatrix\s*}'),
		('BEG_VMAT',      r'\\begin\s*{\s*vmatrix\s*}'),
		('END_VMAT',      r'\\end\s*{\s*vmatrix\s*}'),
		('BEG_PMAT',      r'\\begin\s*{\s*pmatrix\s*}'),
		('END_PMAT',      r'\\end\s*{\s*pmatrix\s*}'),
		('BEG_CASES',     r'\\begin\s*{\s*cases\s*}'),
		('END_CASES',     r'\\end\s*{\s*cases\s*}'),
		('FRAC2',        fr'\\frac\s*{_VARTEX1}\s*{_VARTEX1}'),
		('FRAC1',        fr'\\frac\s*{_VARTEX1}'),
		('FRAC',          r'\\frac'),
		('IF',            r'if(?!{_LETTERU})'),
		('ELSE',          r'else(?!{_LETTERU})'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))('*)"),
		('ATTR',         fr'\.(?:({_LETTERU}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"({_STR})|\\text\s*{{\s*({_STR})\s*}}"),
		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
		('CARET1',       fr'\^{_VARTEX1}'),
		('CARET',         r'\^'),
		('DBLSTAR',       r'\*\*'),
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('CURLYL',        r'{'),
		('CURLYR',        r'}'),
		('BRACKL',        r'\['),
		('BRACKR',        r'\]'),
		('BAR',           r'\|'),
		('PLUS',          r'\+'),
		('MINUS',         r'-'),
		('STAR',          r'\*'),
		('INEQ',         fr'==|!=|\\neq?|<=|\\le|<|\\lt|>=|\\ge|>|\\gt|{"|".join (AST.Eq.UNI2PY)}'),
		('EQ',            r'='),
		('DIVIDE',        r'/'),
		('EXCL',          r'!'),
		('AMP',           r'&'),
		('COLON',         r':'),
		('DBLSLASH',      r'\\\\'),
		('COMMA',         r','),
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('ignore',        r'\\,|\\:|\\?\s+|\\text\s*{\s*[^}]*\s*}'),
	])

	_VARPY_QUICK = fr'(?:{_LETTER})'
	_VAR_QUICK   = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK = OrderedDict ([ # quick input mode different tokens
		('FUNC',         fr'(@|\%|{_FUNCPY})|\\({_FUNCTEX})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
		('SQRT',          r'sqrt|\\sqrt'),
		('LOG',           r'log|\\log'),
		('LN',            r'ln|\\ln'),
		('LIM',          fr'\\lim'),
		('SUM',          fr'\\sum(?:\s*\\limits)?|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?|{_UINTG}'),
		('LEFT',         fr'\\left'),
		('RIGHT',        fr'\\right'),
		('CDOT',         fr'\\cdot'),
		('TO',           fr'\\to'),
		('MAPSTO',       fr'\\mapsto'),
		('IF',            r'if'),
		('ELSE',          r'else'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR_QUICK})|({_VAR_QUICK}))('*)"),
	])

	TOKENS_LONG  = OrderedDict () # initialized in __init__()

	def expr_commas_1      (self, expr_comma, COMMA):                              return expr_comma if expr_comma.is_comma else AST (',', (expr_comma,))
	def expr_commas_2      (self, expr_comma):                                     return expr_comma
	def expr_commas_3      (self):                                                 return AST (',', ())
	def expr_comma_1       (self, expr_comma, COMMA, expr_slice):                        return AST.flatcat (',', expr_comma, expr_slice)
	def expr_comma_2       (self, expr_slice):                                           return expr_slice

	def expr_slice_1       (self, expr_or_empty1, COLON1, expr_or_empty2, COLON2, expr_or_empty3):  return AST.VarNull # (expr_or_empty1, expr_or_empty2, expr_or_empty3)
	def expr_slice_2       (self, expr_or_empty1, COLON1, expr_or_empty2):                          return _expr_lambda (AST (',', ()), expr_or_empty2) if expr_or_empty1 and expr_or_empty1.is_var_lambda else AST.VarNull # (expr_or_empty1, expr_or_empty2)
	def expr_slice_3       (self, expr):                                                            return expr

	def expr               (self, expr_eq):                                        return expr_eq

	def expr_eq_1          (self, expr_lambda1, EQ, expr_lambda2):                 return AST ('=', '=', expr_lambda1, expr_lambda2)
	def expr_eq_2          (self, expr_lambda):                                    return expr_lambda

	def expr_lambda_1      (self, expr_var, expr_commas, COLON, expr):             return _expr_lambda (expr_commas, expr) if expr_var.is_var_lambda else _raise (SyntaxError ())
	def expr_lambda_2      (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr_eq):                    return _expr_lambda (expr_paren.strip (), expr_eq)
	def expr_mapsto_2      (self, expr_piece):                                     return expr_piece

	def expr_piece_1       (self, expr_ineq, IF, expr, ELSE, expr_lambda):         return _expr_piece (expr_ineq, expr, expr_lambda)
	def expr_piece_2       (self, expr_ineq, IF, expr):                            return AST ('piece', ((expr_ineq, expr),))
	def expr_piece_3       (self, expr_ineq):                                      return expr_ineq

	def expr_ineq_2        (self, expr_add1, INEQ, expr_add2):                     return AST ('=', AST.Eq.ANY2PY.get (INEQ.text, INEQ.text), expr_add1, expr_add2)
	def expr_ineq_3        (self, expr_add):                                       return expr_add

	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                  return AST.flatcat ('+', expr_add, expr_mul_exp.neg (stack = True))
	def expr_add_3         (self, expr_mul_exp):                                   return expr_mul_exp

	def expr_mul_exp_1     (self, expr_mul_exp, CDOT, expr_neg):                   return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_2     (self, expr_mul_exp, STAR, expr_neg):                   return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_3     (self, expr_neg):                                       return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                return expr_neg.neg (stack = True)
	def expr_neg_2         (self, expr_diff):                                      return expr_diff

	def expr_diff          (self, expr_div):                                       return _expr_diff (expr_div)

	def expr_div_1         (self, expr_div, DIVIDE, expr_mul_imp):                 return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2         (self, expr_div, DIVIDE, MINUS, expr_mul_imp):          return AST ('/', expr_div, expr_mul_imp.neg (stack = True))
	def expr_div_3         (self, expr_mul_imp):                                   return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                        return _expr_mul_imp (expr_mul_imp, expr_intg, self._USER_FUNCS)
	def expr_mul_imp_2     (self, expr_intg):                                      return expr_intg

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add):           return _expr_intg (expr_add, (expr_sub, expr_super))
	def expr_intg_2        (self, INTG, expr_add):                                 return _expr_intg (expr_add)
	def expr_intg_3        (self, expr_lim):                                       return expr_lim

	def expr_lim_1         (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                           return AST ('lim', expr_neg, expr_var, expr)
	def expr_lim_2         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):   return AST ('lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg):  return AST ('lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                         return expr_sum

	def expr_sum_1         (self, SUM, SUB, CURLYL, expr_var, EQ, expr, CURLYR, expr_super, expr_neg):               return AST ('sum', expr_neg, expr_var, expr, expr_super)
	def expr_sum_2         (self, expr_func):                                                                        return expr_func

	def expr_func_1        (self, SQRT, BRACKL, expr, BRACKR, expr_neg_func):      return _expr_func (1, 'sqrt', expr_neg_func, expr)
	def expr_func_2        (self, SQRT, expr_super, expr_neg_func):                return AST ('^', _expr_func (1, 'sqrt', expr_neg_func), expr_super)
	def expr_func_3        (self, SQRT, expr_neg_func):                            return _expr_func (1, 'sqrt', expr_neg_func)
	def expr_func_4        (self, LN, expr_super, expr_neg_func):                  return AST ('^', _expr_func (1, 'log', expr_neg_func), expr_super)
	def expr_func_5        (self, LN, expr_neg_func):                              return _expr_func (1, 'log', expr_neg_func)
	def expr_func_6        (self, LOG, expr_sub, expr_neg_func):                   return _expr_func (1, 'log', expr_neg_func, expr_sub)
	def expr_func_7        (self, LOG, expr_super, expr_neg_func):                 return AST ('^', _expr_func (1, 'log', expr_neg_func), expr_super)
	def expr_func_8        (self, LOG, expr_neg_func):                             return _expr_func (1, 'log', expr_neg_func)
	def expr_func_9        (self, FUNC, expr_neg_func):                            return _expr_func_func (FUNC, expr_neg_func)
	def expr_func_10       (self, FUNC, expr_super, expr_neg_func):                return _expr_func_func (FUNC, expr_neg_func, expr_super)
	def expr_func_11       (self, expr_pow):                                       return expr_pow

	def expr_pow_1         (self, expr_pow, expr_super):                           return AST ('^', expr_pow, expr_super)
	def expr_pow_2         (self, expr_fact):                                      return expr_fact

	def expr_fact_1        (self, expr_fact, EXCL):                                return AST ('!', expr_fact)
	def expr_fact_2        (self, expr_attr):                                      return expr_attr

	def expr_attr_1        (self, expr_attr, ATTR):                                return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1])
	def expr_attr_2        (self, expr_abs):                                       return expr_abs

	def expr_abs_1         (self, LEFT, BAR1, expr_commas, RIGHT, BAR2):           return AST ('|', expr_commas)
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                        return AST ('|', expr_commas)
	def expr_abs_3         (self, expr_paren):                                     return expr_paren

	def expr_paren_1       (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):       return AST ('(', expr_commas)
	def expr_paren_2       (self, PARENL, expr_commas, PARENR):                    return AST ('(', expr_commas)
	def expr_paren_3       (self, IGNORE_CURLY, CURLYL, expr, CURLYR):             return AST ('{', expr)
	def expr_paren_4       (self, expr_frac):                                      return expr_frac

	def expr_frac_1        (self, FRAC, expr_cases1, expr_cases2):                 return AST ('/', expr_cases1.remove_curlys (), expr_cases2.remove_curlys ())
	def expr_frac_2        (self, FRAC1, expr_cases):                              return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_cases.remove_curlys ())
	def expr_frac_3        (self, FRAC2):                                          return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4        (self, expr_cases):                                     return expr_cases

	def expr_cases_1       (self, BEG_CASES, expr_casess, END_CASES):              return AST ('piece', expr_casess)
	def expr_cases_2       (self, expr_mat):                                       return expr_mat
	def expr_casess_1      (self, expr_casessp, DBLSLASH):                         return expr_casessp
	def expr_casess_2      (self, expr_casessp):                                   return expr_casessp
	def expr_casessp_1     (self, expr_casessp, DBLSLASH, expr_casessc):           return expr_casessp + (expr_casessc,)
	def expr_casessp_2     (self, expr_casessc):                                   return (expr_casessc,)
	def expr_casessc_1     (self, expr1, AMP, expr2):                              return (expr1, expr2)
	def expr_casessc_2     (self, expr, AMP):                                      return (expr, True)

	def expr_mat_1         (self, LEFT, BRACKL, BEG_MAT, expr_mat_rows, END_MAT, RIGHT, BRACKR):  return _expr_mat (expr_mat_rows)
	def expr_mat_2         (self, BEG_MAT, expr_mat_rows, END_MAT):                               return _expr_mat (expr_mat_rows)
	def expr_mat_3         (self, BEG_BMAT, expr_mat_rows, END_BMAT):                             return _expr_mat (expr_mat_rows)
	def expr_mat_4         (self, BEG_VMAT, expr_mat_rows, END_VMAT):                             return _expr_mat (expr_mat_rows)
	def expr_mat_5         (self, BEG_PMAT, expr_mat_rows, END_PMAT):                             return _expr_mat (expr_mat_rows)
	def expr_mat_6         (self, expr_curly):                                                    return expr_curly
	def expr_mat_rows_1    (self, expr_mat_row, DBLSLASH):                         return expr_mat_row
	def expr_mat_rows_2    (self, expr_mat_row):                                   return expr_mat_row
	def expr_mat_rows_3    (self):                                                 return ()
	def expr_mat_row_1     (self, expr_mat_row, DBLSLASH, expr_mat_col):           return expr_mat_row + (expr_mat_col,)
	def expr_mat_row_2     (self, expr_mat_col):                                   return (expr_mat_col,)
	def expr_mat_col_1     (self, expr_mat_col, AMP, expr):                        return expr_mat_col + (expr,)
	def expr_mat_col_2     (self, expr):                                           return (expr,)

	def expr_curly_1       (self, CURLYL, expr_commas, CURLYR):                    return _expr_curly (expr_commas)
	def expr_curly_2       (self, expr_bracket):                                   return expr_bracket

	def expr_bracket_1     (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):       return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_2     (self, BRACKL, expr_commas, BRACKR):                    return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_3     (self, expr_term):                                      return expr_term

	def expr_term_1        (self, expr_num):                                       return expr_num
	def expr_term_2        (self, expr_var):                                       return expr_var
	def expr_term_3        (self, STR):                                            return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_4        (self, SUB):                                            return AST ('@', '_') # for last expression variable

	def expr_num           (self, NUM):                                            return _expr_num (NUM)
	def expr_var           (self, VAR):                                            return _expr_var (VAR, self._VAR_TEX_XLAT)

	def expr_sub_1         (self, SUB, expr_frac):                                 return expr_frac
	def expr_sub_2         (self, SUB1):                                           return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1       (self, DBLSTAR, expr_neg_func):                         return expr_neg_func
	def expr_super_3       (self, CARET, expr_frac):                               return expr_frac
	def expr_super_4       (self, CARET1):                                         return _ast_from_tok_digit_or_var (CARET1)

	def expr_neg_func_1    (self, MINUS, expr_neg_func):                           return expr_neg_func.neg (stack = True)
	def expr_neg_func_2    (self, expr_func):                                      return expr_func

	def expr_or_empty_1    (self, expr):                                           return expr
	def expr_or_empty_2    (self):                                                 return None

	def caret_or_dblstar_1 (self, DBLSTAR):                                        return '**'
	def caret_or_dblstar_2 (self, CARET):                                          return '^'

	#...............................................................................................
	_AUTOCOMPLETE_SUBSTITUTE = { # autocomplete means autocomplete AST tree so it can be rendered, not necessarily expression
		'CARET1'          : 'CARET',
		'SUB1'            : 'SUB',
		'FRAC2'           : 'FRAC',
		'FRAC1'           : 'FRAC',
		'expr_super'      : 'CARET',
		'caret_or_dblstar': 'CARET',
	}

	_AUTOCOMPLETE_CONTINUE = {
		'RIGHT' : ' \\right',
		'COMMA' : ',',
		'PARENL': '(',
		'PARENR': ')',
		'CURLYR': '}',
		'BRACKR': ']',
		'BAR'   : '|',
	}

	def _insert_symbol (self, sym, tokinc = 0):
		tokidx       = self.tokidx
		self.tokidx += tokinc

		for sym in ((sym,) if isinstance (sym, str) else sym):
			if sym in self.TOKENS:
				self.tokens.insert (tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

				if self.autocompleting:
					if sym in self._AUTOCOMPLETE_CONTINUE:
						self.autocomplete.append (self._AUTOCOMPLETE_CONTINUE [sym])
					else:
						self.autocompleting = False

			else:
				self.tokens.insert (tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, ('', '', '', '', '')))
				self._mark_error ()

			tokidx += 1

		return True # for convenience

	def _mark_error (self, sym_ins = None, tokinc = 0, at = None):
		self.autocompleting = False

		if self.erridx is None:
			self.erridx = self.tokens [self.tokidx].pos if at is None else at

		if sym_ins is not None:
			return self._insert_symbol (sym_ins, tokinc)

	def _parse_autocomplete_expr_commas (self, rule, pos):
		idx = -pos + (self.stack [-pos].sym == 'LEFT')

		if self.stack [idx].sym != 'CURLYL':
			if self.tokens [self.tokidx - 1] == 'COMMA':
				self._mark_error ()

			if self.stack [idx - 1].sym == 'LEFT':
				return self._insert_symbol ('RIGHT')

			return self._insert_symbol ('PARENR' if self.stack [idx].sym == 'PARENL' else 'BRACKR')

		# vector or matrix potentially being entered
		if self.stack [idx - 1].sym == 'CURLYL':
			if self.stack [-1].red.is_null_var:
				return self._mark_error (('CURLYR', 'CURLYR'))
			elif not self.stack [-1].red.is_comma:
				return self._insert_symbol (('COMMA', 'CURLYR', 'COMMA', 'CURLYR'), 1)
			elif len (self.stack [-1].red.comma) == 1 or self.tokens [self.tokidx - 1] != 'COMMA':
				return self._insert_symbol (('CURLYR', 'COMMA', 'CURLYR'))
			else:
				return self._mark_error (('CURLYR', 'CURLYR'))

		if self.stack [-3].sym != 'COMMA' or self.stack [-4].sym != 'expr_comma' or self.stack [-5].sym != 'CURLYL':
			if self.stack [-1].red.is_vec:
				return self._insert_symbol (('COMMA', 'CURLYR'), 1)
			elif self.stack [-1].red.is_comma:
				if len (self.stack [-1].red.comma) == 1 or self.tokens [self.tokidx - 1] != 'COMMA':
					return self._insert_symbol ('CURLYR')
				else:
					return self._mark_error ('CURLYR')

		else:
			cols = \
					len (self.stack [-4].red.vec)             if self.stack [-4].red.is_vec else \
					len (self.stack [-4].red.comma [0].vec)  if self.stack [-4].red.is_comma and self.stack [-4].red.comma [0].is_vec else \
					None

			if cols is not None:
				vec             = self.stack [-1].red.comma if self.stack [-1].red.is_comma else (self.stack [-1].red,)
				self.stack [-1] = lalr1.State (self.stack [-1].idx, self.stack [-1].sym, AST (',', vec + (AST.VarNull,) * (cols - len (vec))))

				return self._mark_error (('CURLYR', 'CURLYR')) if len (vec) != cols else self._insert_symbol (('CURLYR', 'CURLYR'))

		return self._insert_symbol ('CURLYR')

	def _parse_autocomplete_expr_intg (self):
		s               = self.stack [-1]
		self.stack [-1] = lalr1.State (s.idx, s.sym, AST ('*', (s.red, AST.VarNull)))
		expr_vars       = set ()

		if self.autocompleting:
			stack = [s [2]]

			while stack:
				ast = stack.pop ()

				if ast.is_var:
					if not (ast.is_differential or ast.is_part_any):
						expr_vars.add (ast.var)
				else:
					stack.extend (filter (lambda a: isinstance (a, tuple), ast))

		expr_vars = expr_vars - {'_'} - {ast.var for ast in AST.CONSTS}

		if len (expr_vars) == 1:
			self.autocomplete.append (f' d{expr_vars.pop ()}')
		else:
			self._mark_error ()

		return True

	def parse_getextrastate (self):
		return (self.autocomplete [:], self.autocompleting, self.erridx)

	def parse_setextrastate (self, state):
		self.autocomplete, self.autocompleting, self.erridx = state

	def parse_error (self): # add tokens to continue parsing for autocomplete if syntax allows
		if isinstance (self.rederr, lalr1.Incomplete):
			self.parse_results.append ((self.rederr.red, self.tok.pos, []))

			return False

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

		if pos == 1 and rule == ('expr_func', ('FUNC', 'expr_neg_func')):
			return self._insert_symbol (('PARENL', 'PARENR'))

		if pos and rule [1] [pos - 1] == 'expr_commas':
			return self._parse_autocomplete_expr_commas (rule, pos)

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_intg': # TODO: Fix this!
				return self._parse_autocomplete_expr_intg ()

			return False

		return self._insert_symbol (rule [1] [pos])

	def parse_success (self, red):
		self.parse_results.append ((red, self.erridx, self.autocomplete))

		return True # continue parsing if conflict branches remain to find best resolution

	def parse (self, text):
		if not text.strip ():
			return (AST.VarNull, 0, [])

		self.parse_results  = [] # [(reduction, erridx, autocomplete), ...]
		self.autocomplete   = []
		self.autocompleting = True
		self.erridx         = None

		lalr1.LALR1.parse (self, text)

		if not self.parse_results:
			return (None, 0, [])

		rated = sorted ((r is None, -e if e is not None else float ('-inf'), len (a), i, (r, e, a)) \
				for i, (r, e, a) in enumerate (self.parse_results))

		if os.environ.get ('SYMPAD_DEBUG'):
			rated = list (rated)

			print (file = sys.stderr)

			for res in rated [:32]:
				res = res [-1]
				res = (res [0].remove_curlys (),) + res [1:] if isinstance (res [0], AST) else res

				print ('parse:', res, file = sys.stderr)

			if len (rated) > 32:
				print (f'... total {len (rated)}', file = sys.stderr)

			print (file = sys.stderr)

		res = next (iter (rated)) [-1]

		return (res [0].remove_curlys (),) + res [1:] if isinstance (res [0], AST) else res

class sparser: # for single script
	Parser = Parser

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
# 	p = Parser ()
# 	a = p.parse (r'Piecewise ((1,True))') [0]
# 	# a = sym.ast2spt (a)
# 	print (a)
