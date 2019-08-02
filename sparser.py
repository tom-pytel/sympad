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
def _expr_slice (start = AST.CommaEmpty, stop = AST.CommaEmpty, step = AST.CommaEmpty):
	if start.is_var_lambda or (start.is_mul and start.mul [0].is_var_lambda) or \
			start.is_comma and start.comma and start.comma [0].is_mul and start.comma [0].mul [0].is_var_lambda:
		raise SyntaxError ('this is a lambda function, not a slice')

	return AST ('slice', None if start.is_empty_comma else start, None if stop.is_empty_comma else stop, None if step.is_empty_comma else step)

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
			b'eJztXW1v3baS/jML1AZ0AIkvkphvaZr2BpuX3iQtdmEUQZqmF8U2bTdJ7+6iuP99Z+YZSiSlY0u2j318fGD6SBpR5HA4z5AckdTJ2Rf/9v63n76ovnj04umL53R8+vjr13T49uHLx8+f0smTb56/ePn4zaPvXj79T7r8+uXDR3po9Gjo+OXjb948evjq8Ss9' \
			b'f/bwtZ59OZ5+P55+i1NJlXN59uT5d/IspffvTHj1+iX/fvcl/T7/7hn9fv+QKU+ev/6GuXzyTG7L799fclpPhfsXfPfr754zk1/KE49ePHv2MJboZcz0ZcyMT14++eZvnMTDZ9/S71dfPn319OGrv9Hp4+dfaVH47Mvx9PvxVIvy+O/88/TVYyVHaXBqr8EI' \
			b'McAxnz389tXrF5zdaynk4/949DTeZpl+9eT7J19xMo++evFaRKEllyy+fSqCevI1/UgqJCN+6t3bj+8/v/n945uffvz10+e3H4n0/n//+Pjm059/vB8ufnv/jzc///nbu/Hmj/H0w9vPb979/mt6+fH3/ykuP8Xrd28/vf/06V1++Ud+Ga/e/jiefv488PLz' \
			b'23ef4/kfY045ex/i6a+/DKe//Pb5HwNff/765pcPQ8b/HMv92/jsT7/8M55+fv8xIf/8czz/8ePbd//1/nMip6Esf3789f/S7OgkkcpQsp9+yko/Mvv+v4eiUSZDiX95/+79cEF199uY6B+fPv8+lPvthx9/ehuvhrQiger7/Yc/Pg8Mfvr1lzHZd79/+PA2' \
			b'u/j0xQ/V2cnG2cqZ0wonlk98tWn5aG11YirTVZumsnxyOlCFNhI2gU8ahx9v6G57mpIoJCQ+5QcNfpw/1UtKS6IEzrjxmrFtTiNVaQNhYxo5I556etpVTm8RT42XVJkD6yvrTvWSruSslaIy95p/JODKx+fogTaS+JTOjPwbzvIU1xswrnTwQNwpEdcd8W+F' \
			b'/zoSqAzyfE1xJbIx+HGUtgFfCYllN1L5lM6Y7a6yJAzUR8snzG6DH6fcEz8WDNENliPzAv6Z0qZXnR6ZxJlxhVipEZIIkVXMSt84MyUll24aw+WXlLCrpyQzJSWX7fQye2BDcuZiGFVLLg60oDFyytFIeix9yd0MESJ5vNwYkQlVWS8UqkzTVFSFLEYqjnci' \
			b'G34G1b8lBsOMALIsInGdR9wYyb2n/1A5F1WXlKVBWb0ih0tPSuFT/NC9SB4ITQ1KO1IaULqRYkDpI4U0VzQq4CeBUOAzPunxI+gJp0riUz7r4s1TvaSreAN5tPhxYSh8JPk6JfEpS8bjhyrq9HQ85TjEiFgcfYRhJZJyDW6oujhGK7BIYpdEnZbFKVNilGw0' \
			b'hiHShDJeOqlFHzHOBYCJqqF3Xu6yuqmAU3qkEEHkUeOHNPNUrwnGciZ8MRDl5zSn6aWyT4mIpdGC1pUXOlmvEzIio9pJ5VU2AkF1ro9yIeJJgi+5tGOyZJ9EKQwL0g5nTs9g8UXN5YQYDafU/pzVFVUW4YuUmyRP9BCqpq7pv6n6vupJvViLSJN9X7W2ailG' \
			b'XYWmCqYKtgp0SdreVqxPgeVKNUmyJAyRopKGdFVPYGh91bZV21UtJRKqrq66vupC1ddsxclW9Lbq6RHDwgDqmpoYobpoCBBNwygSLFE8khjF6ok/qjbii5SyqzxlUldtU7WURk1J1VTLJBTLMHV0TtrcsQ0nnSYdJmNEViB0VSC+iXtKk7OqCP1V+0N1Qhen' \
			b'1DqTbLi+ST5yIN5IaGw95S6L6pQxXAv97ISFxhQSnES0iGcl/on1oPoe5FZun7SgtjHRGlTkzBI5Fa2WDIKkf6yxmRoLRqusP4pom4hUHwP0MUDFQqvKZUVyKOG0bCjSUJiyJCgAZeIaVfpwLakpED2w4sF5B5RF1Ek52JBSotQWUKKhot7DvazjptU6hqB6' \
			b'HIKKqhcxgmdidWRtdzxlUk+FfUXVOOPO/BHps1pAbYuoQeerjsrQVZ2tOld1NLAw91Ug3VEguUD6o0BygYSjQNKWpENHtMfBoEHp0QA32lm1uGnR7bUGXVnhm2M1tR4bPWofzaI174V8p1qdk77TomgRtEQefSkvZrepuQBWK36o5oNodk98pyVGHbc6XGl0' \
			b'FGN0SKR6UnvEdjqOgdScg5hIWjVzTQ21r/p27wpLfKNeXXtnGIZ+OnT8XEj18S7w76FPXkwDmEzZ3kOGodmhKzREhuuoBTuMsNR41Gondajkj/3YbY0ySwWeFzocZSIyITEYdTvR8T5LgspMErhfZW4FCvezvoNo/NFSzuoFLCVlfBTRFhG5o2i2eYYbFs0Z' \
			b'O9HvqXHh9wZGneMGzvF7Kgl5EWCu7Lo/y15h8cuwAAF7acAOcWx8dtJJ0Q6sUP3hFYrfGYkyNjoiw0DNqBfDqFengY/DxPe7nYjiICRwxi+FDqUw/F5LqlNfbE5fof+A9+wyA4zNO+UjD3SI0+FmZ2NF63tG1YcOY/y2w7M9DmrPrLSd7Pxkcd5F4Wnj7wUT' \
			b'hQvDi6DKN661SR261wrM2g7+RQP/ooF/0cC17LSmDbq7EtuOvTq01+jbUauddO/QgKOTdw+acXayQlKi8fvq7xN122f2uuvXcJ3/0/v9LflJr/MInN9f7WG3PFS822cmtZ1w/R4z6WttA5o9ZjKg/bWt+j/lMDiIrU7Js+obtdxe9OqBd0JuJRb3DyQycWLR' \
			b'Fzi++E2nEBkRC0RGpZUDaMSw1UGyxSBZpGyV7CHfvLPQgVbORJqhcq/caq/coDvOHZJ7O5lLBiAGA5B76oxgDbHQEIvuniLWau/doNvOI9R7i9gzHqjcVwVpYV9a6EkboBkWZusOzjA545GkvZMjSRlC2sP07cmY1+jA1GJgajEwpcMwWnDJlTPaF8kXBTir' \
			b'5NiNQWPXw5Y59EkctNpBqz202Q99HHef3/ty/81p/81FXw76LU76LQ4dFqc9FXe/XhFzt0kUTE1hp52y6Mtq1EJCWnfSQnpUfN7P9AHaUONATESHkVOHkdvfkQ3ljYGJV8X2sZsDxfai2BLHIY7HI22NQ8OH+2gNYHXvaeFZqz1c3a0qRQulaKEUdKCuoeKg' \
			b'RcxOY3YH4v0/4/J2KG8neMFbG32HQ1x3hVubS99DTj2e62PU/pCEEg6nMM3BFEbULOjU6VrnTtfShNUVr8clS8bZwyJxApIfL26rZX2bvNsYJACjB+5TLsdit1xgLu0gpV6lRF0DFqkX2yhSwDThTplvxII1zAC/KOW3pPxKlF+T8itSXg/La2F5lSxbQp7/' \
			b'z1P7eb0rL3blea8sU15YyHLjSeCyqp7u8zxl2VGB0uM5vzytnBfG8rRyFgwLhSuRF8ny0lh+mceOOu7GdBSXPUc8+Z5XtLEjnf3VLGF+98dTOHhyJPewuXctb7KwfL+VpdYb7pPzCm3eUoJy5T0bKJNN4K00ZFsD7EjgZa+MileRU/1uet4mgs57JvPKel4p' \
			b'XssScz6T/Roa2UWD4siSbz4hAhVu0/Ki7przo5PQy5J+2eKBF8v3vDEAp2yFF9LqjW81NSf80gM9c8b/vFCcMgy8cJ9jMVu8FLxmHrEPx6blonDqdB144ww68hp33kChkk0ESIKbLmAfipYFwEyyLJiXRvY/2LDV3LA+bHreEYH/6Zw3x+DdHJTxwEXmUtJ1' \
			b'4GtZQM9r4zdBt55oudycV82s0f22+YG7qKzvrtB2I+CZ03mqvSuq/WgfnAJ4DgJmIQyuGwLtMhhkEGD1d0shQLVFCUJHJsrPVSnVuR0E/U6BEBko/7cBg+8tAQfbjWvEBae0CBsZLmoktgwXhnEREih0DAU4wknrFA3DREZpd9JW8WJw+AQf0giiLzyPFaMd' \
			b'am3yeukXN/FFibw3QTusSHIjmOT9e8QT2uN0OUfZRgJnTrHWFnjrEoy5HFu82pzXik8wRunw4p0J1rgZp3i8rnxV02MS7DUz+GN6GDDY8DRCwSFVGU9dqH2BSVZ8LicHhl4nW3zgIH0RxR5n0mRhDRL5dgpEvk6xSNdDKHF5fmBGbcgSkMwEr3IGyHaSkxXG' \
			b'XYwGYo94iO70EMBKLYcUzM2IX8bugNsolBy9Sk0wPPLIirkIyZInKyd48uApQ7Tmo5iWaHlWI76rv1zzgE1j6B9I5ZBCPmDLQopFR/Mvfl+pBqBJbEC/T+ifhb5bhP4j8hX5rCssWC69QburbW5jIuxxLw1rYC+tZAL7pmiCs3RL2E9yzmLbCW+Mee5HtLhI' \
			b'W2pRAHRlNa6ogBHUyw09BHACCaSoN9tQrzIpUA9qgvqRy+WoN0C9SkcJOepxT1Ev0fKsZlA/g3ZXNvf7D/UjzpfjXJpCLrbNQW4HkNsyrAJ50cmW/c9SkKfpliCf5JzFthPetGGXswnCLRCOM6l8C4RbINwC4RYItznC7TaEq0AKhIOaItyOOS9FuAXCVTRK' \
			b'yBGuxVKEWyA8yWoZwv1BIvzYj09Q3gkuOMkc5d2A8q4Mq1DeFSjvCpSn6ZYon+ScxbYT3iLKuwHlUgyu/A4YH2JK7XeAeQeYd4B5B5h3Ocy7bTBXiRQwBzWFeZLzUph3gLnKRgk5zHEvwrwDzJOs1nXf2yPcDx3uQQDCj+RwDwPcJ2EV3EMB91DAPU23hPtc' \
			b'5mNsOyUp3MMI96Bwh4ttjCm1HwD3ALgHwB1+NxFHAvewDe4qkQLuoKZwT3JeCne4pKNslJDDHfci3APgnmS1Du7dEe4HDnfei7qVSq0zuMse1QJ33EvDGrhz9BTufJ3CPUu3gPs05yy2nfCmcJczwF2KIYUXuI8xufYlHuI4PQTwoeIY4S6Xc3CPEsnhrtQE' \
			b'7mnOC+EueZpBNkrI4K73FO4SLc9qHdz7o3f+3uBefHRcqXDQGXjnDbzzZnDTIUYaVqG/cNOZwk2XpVuif5JzyYidsBcNwOimMzqEN3DSjTHFAMBPZ+CnM/DTGfjpTO6nM9v8dFEohQEANTUASc5LDQD8dFE8SsgNAO5FAwA/XZrVOgMQjgbg3hgAGdZzLWJY' \
			b'zwc2AB0MwDC4R4w0rDIAxeDeFIP7LN3SAExybkpO7IS/aAHGAb7RAb7BAH+MKRYAA3yDAb7BAN9ggG/yAb7ZNsCPUiksAKipBUhyXmoBMMCP8lFCbgFwL1oADPDTrNZZgKY+moB7YwJkigxXYQ8T0MME9DAB/WAC+jKsMgF9YQL6wgSk6ZYmYJJzyYidsBct' \
			b'QD9agF4tQA8LMMQUC4ApNnJPDwGsQASpBei3WQAVSmEBQE0tQJLzUgvQwwKoeJSQWwDcixaghwVIslppAZqjBbg3FkCcffRr4OzjA1uAAAswuPzMJKyyAIXLzxQuvyzd0gLMZZ49YKcktQCj18+o18/A6zfGFAsAr5+B18/A62fg9TO5189s8/pFoRQWANTU' \
			b'AiQ5L7UA8PpF8SghtwC4Fy0AvH5pVistwHGW3r2xAFb8f1x58P/JV7oaHECEBUCMNKyxALbwAtrCC5ilW1iAac4lI3bCnloAOzoCrToCLRyBY0xWAwtHoIUj0MIRaOEItLkj0G5zBEah5BZAqYkFSHNeaAEsHIFRPErILIDeUwtg4QhMs1ppAexoAexhGAFe' \
			b'ktIcjcH57/4wyc2xeBusGsGXDHGoq2aYMY9Pr6Zh1UvAYtZuU8zazdItXwJOci4ZsRP24nvAcdaulIQVQdZJehQwfUI0ArN3G8zebTB7t8Hs3aaYveu2vQ9U4RTvA0FN3wcmOS99H+jwPlDFpIT8fSDuxfeBmL2bZrXSLmyZ0NfsjUW4zTl9/opm4GZMQMOf' \
			b'xeOPOoT+otGBl26055C+G+yEGIcGvgxXWkjDz2eWQGpl/J+MDybZZ6zYCYPRFDCESGJdOs9PvgPsxryGE/lWBzwEOAZlpsYxHSL4zBBw+uMoQeVTjBJALVbjiIQXjxGwKEdKbDhPcJUPEhAtDhK4srnY1UZfGgzs5UYhEPhlmhRZBe/FCPiZOfz72TkwV5rP' \
			b'f+waJLaA14uxfLlGWzgLsJRODrUc1CK0ZVjlLGgLg9CWBsEkCZfWYJJ1EVq1CQV/PMEfxm5ciicFqrWYLoksPoMWPgOszTNYnicMQRKpQWi3+QxUNoU1ADX1GSQ5L7UHLeyBCkkJuTlQttUctDACSVYrewaTmYH7aRGOPoNr8BmI15BH3fAaWngNLbyGdvAa' \
			b'2klY5TMovIa28Bpm6ZY+g7nMswdmSOozGL2GVr2GFl7DMab4DOA1tPAaWngNLbyGNvca2m1ewyiUwmcAauozSHJe6jOA1zCKRwm5zwD3os8AXsM0q5UWYDJZcEcWYLLNxdEO3I4dcOI75EqC79DBd+jgO3SD7xAXaVhjB1zhOwx4fyh7QshmKA3sAVKmu27q' \
			b'Q5xyUDJkJ2yqPXCjD9GpD9HBhzjGlO/3wYfo4EN08CE6+BBd7kN023yIUTi5PVBqYg/SnBfaAwcfoj7mlZDZA72n9sDBh5hmtdIeHGcT3h9LILMJuWIwm9BhNqHDbEI3zCZEjDSssgTFbEJXzCbM0i0twCTnkhE7YS9agHE2oVNHgcNswjGmfsFzgy34xAJg' \
			b'NqHDbEKXzyZ022YTRqEUFgDU1AIkOS+1AJhNGMWjhNwC4F60AHAMpFmttADH6YQ3agHUk327lgCQsRzEEsBtKIdaDmoJbBlWWYLCa+iKlcFZuqUlmORcMmIn7EVLMC4OBuK0fC6JKZYAq4MdVgc7rA52WB3s8tXBbtvq4CiUwhKAmlqCJGcTTxfZA6wRjkJS' \
			b'Qm4PNDW1B1gjnGa4zh6YydzCHS0nutbXBct3zdoFri+L5SvjWNxhLNXc9+8Gxz/upWEVgn2B4MLvP0HtJLcsZzvhJ0LWV9l6fgcX/+airbWc34ZLLWqBS1BTXA5RF4ERDnx9YrqvVkxKkYjNtcYslq7WN5O5fUcE7i0CZYI+ezu6HIHD1HzcS8MqBBZT8113' \
			b'AQInuWU52wk/EYFdgcBuIQK3zbePRS0QCGqKwIGRRQjEVHt9YgaBmpQiEPPsxywWI3Ayt+6IwL1FoPi5uesWcgQOHm43CasQWHi4XbgAgXMZjjnbKUkRGAoEhoUI3Oa3jkUtEAhqisCBkUUIhMtan5hBoCalCIS/esxiMQLtQS5q36eB6G0OQL1sO8nCbzLQ' \
			b'+mHDSdxLwxrQyryRBLSiuwlos3QLAE9zzmLbCW8KYJ2rkm9K5bHfpEbkypdoiO30EMAGip9A22/bbDIKJIe2UhNojywudkB5bDYZRaOEDOJ6TyEu0fKsFkL8uO/cQUNcvM0seZNDfPAz414aVkG88DP7ws+cpVtCfJJzFttOeIsQN3MQh5tZIwrE4WP28DF7' \
			b'+Jg9fMw+9zH7bT7mKJAC4qCmEDdjzkshDh9zFI0ScojjXoQ4fMxpVgshfpgbzx0hrhAHKCyHDOKDAxn30rAK4oUD2RcO5CzdEuKTnLPYdsJbhLidgzj8xxpRIA7nsYfz2MN57OE89rnz2G9zHkeBFBAHNYW4HXNeCnG4jaNolJBDXIulEIfbOM1qIcQPc7O5' \
			b'I8QV4rLYhGXucogPa0xwLw2rIF6sMfHFGpMs3RLik5yz2HbCW4S4m4M4lpZoRIE41pV4rCvxWFfisa7E5+tK/LZ1JVEgBcRBTSGe5LwU4lhXEkWjhBziuBchjnUlaVYLId7NfxconVne3pFFJrvbI76e/zBRZhXsNa1BuYx1qLdYCDNjJbrLWIpw0feNWPMD' \
			b'h7lvvPjBXecn4UprVXzhr8sSLiwKPtKE7wpN2fBw35UknpYu8+59mLMrcONpXLErmJPqMSfVY06qh2PP53NSufZmv63kE6ff7GdkouAKwwNqsYhl4G2h5WHpsJ6I+QlV/MiM8DSZv8rfmtEMoh2CT3AU4MQOCf2BwFt+hcKGSZS8lQOZJx/+hW/Cn93MN8v2' \
			b'64Nl7cqeQcT8Frxv/WoTV8y+fbNsH79XJvJZCp/Zj5at+EBTmNN5sxu1RxPb7ZXyL1T8ttui/EsU/6Kv9emWbLf2xb5Gd1XYKxQsbz/sPAiWAYCKPgOAaVf0GgEQrh0Azc2AYBEAiM77CAxAaGTh6V0DhNkRIFiG+/EpS6wNDwMwYl98ApBmaa/o6l+1LD7m' \
			b'SgK+xJSEW+4iyacdlgCluWRrcQ4wVu7WeeXvuzbJDFmkaBbO9tlBi8GD0BWthl8GEjffclR/kVI84CqSr9yZmxo5XPzN10tChJSuIdE3Jtxcp+pKo4m9/gSyjP71/9rbEemMipmprwiZK7UnbMGWdLIIKr17QNkLUiyNA3eLEQZFHVuQIB8/X4eOGxxaCAL4' \
			b'2Bbz2BYhYE+UXp2OQ5tA+XXl6+1Fyn6DAwfZR4kZbars08YLBw3uJrSYCkrlVEXud6vLcz7jy+ozXXfuQPSajff4oYFGlgK43er3zPdFLq3jG8NFZynZS+u6v1jXqZm7BqMNRe+uqutL3pPMvh+5TC+mv1kbvtP+fdqvZx1vr0PXmeV19rzzl9P3psd7zKvo' \
			b'ertA1/vr0/VB0Zub6qNcUs8PUMdT/W7KRSu77K9cVr+vqtvdAt0OO9Btc9Tt29Xt/vB1u1/QH181aWShbtujbt+ubpcTJQ5Qt8ONeEwu40a8aUdJVOB6ravQ8sSufRhPXt4ReLO+kainTb9uRkH1F8/1k21jSaxHvc319g46QK5NYXm64A0o7FLDWv1F1f6A' \
			b'UCSq2tyIO6/LPHq70dmtE0Cv6sy7wzrMgtmQIBNH3s4McNPtyIG3vuNAt3ai1VvmUGfGuE3nRN+kSV44j3lilue6EkbnK4f9Ue+5/3NMNhAR1Zxr4iY7G8unAZcGfNrb4C8YyCct6llj7v0DQr7Y8h29YDxq/W1qfTv5P1fr24PR+l61vr1A6111FpI1c1Z0' \
			b'3Ip2p6otes1tera8rJ9Xra5Y9hUcT+K2Vbp6S+q600rGJ2amlTtUbLkztrSYM3JkyaQSab00aH5FIUd4eulkNWFZoSNOSnxI4VnBLlt45mBQ1lE5lwnET2XiBrG0a8TSTiWzH9Ip4BwlFMF5ZSl1a6R0jrWHnV9u5JeIdY0Bn4g+LqsKV60CKUn+P7Gy2AN1' \
			b'rWVdUnnr7GZRx9oNpqdys9iXlX5rTodt63l34mSYqsdMWz6jKvONdtiiODfoTJhdErsb58FUq2ZaXts+oK6MqFg4qtgKFeOq31OHVaJjvMq3uW0dM+4Bf3iRVY0rsnuw6VnhiO2jwq1QOHMnFM4Io/upcE2ucLfrvN93nev23jG/X20pK5jZWwW7iTdCc335' \
			b'tvhk53kK529c4STLy+gbP7gbleu2apyRDwbFz14WJm/6tUsaiqky7snbyj3Qx606yAp3d95IpobvBt5CLjR+Tj6i0XQyfBcN6Hu54WVXfm+JHkJFw/tTOjvZyJbu2C7HyD4cw2owGkHzR715hT0xzvUnW8mMC7v6lhPemAtSMFXxJ0/ZyVN1+SAhQ/94iZme' \
			b'y8Nu7uEme56XhPEmzNX4x4vUhvMebPgkJVPuCjQmPNnER3KQqeHxDSlPqWqxEA1b1PDWMxX/ke56md4VAxOxWg4RGIYN/PWkghSBp6RQy8944alWHBULoYXndqc8U+z1f8JXt4yvuT2RzmWNZ2YN7HXV/B+//dh2r5P3EfQnbPY3wSb1wS/3JyyGnMXJdlVO' \
			b'vmiRuRXP33Iq32+K+wSy/jluK8VtA2UoW0nxNlLtfCnTLZ5iidnWy3ZNUnLdjmnYiomNTYU/bqmq5KIIYeZvLtaUNp/weFGkJAJu6ptQApbp9QcUoNm5igyr5KOWtDvWFO6q7DbY9CJcS5KoDXMj6tRWOwgoQNIcc28xXJNSNXuhV3yDA77WNlxeKXD/+VoS' \
			b'uiCgetx5+uX8xdjeqmWpJAdN4zHKlkA94HPu8lYANKqYoVKfOLlGqfwBKx2P8e5qQO2c281conOogpWa56qrhDicvSgiStgdsP6xd+GuBtROf1EPZ7EKohZWKOKcPE01hN5W6eWqEJ0sF0YsvSQik3DIGmurOxvgCKn3S2NddUsB0mgOWVd9dWcDasfsl662' \
			b'1S0FSOOQhz/8VuGuBtSOu3u1E7+mvbyW+mqfQ9MR0319fizUlr9myxLOG702Cw0MK8f1Ba7qGSpV8vaHIJx2mdvu2uSzzWBslZOrzgkU/fwIC0ORzlyyEFe37+Jqq/0IENeFQ6bbFldf7UeAuA7pNQvPDrgoyMSA5H/JMxcksSq52Uh4G3zh0OkuVYWv7k6A' \
			b'+Hf/NukGxd9WdydA/BcOxu6S+Lvq7gSI3x6S+Pvq7gSIn4Z3huf7dFodPl7r/ZavWTxM44WEcLfxDmRpLZEMeeJFJ9vfGd5MqWk1hX42Zl8lARHDJCJXB0cOVRqaDoaTdyUZZlW1XKUgN/Il6UFdzq36vpGpAjafsxfn2s3NswtoNHlFfrG0TGZ6YuqB05w0' \
			b'Fx44e/Yq6wwq0vkmyASvQEboh9P/B3BsNc8='

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
	def expr_commas_3      (self):                                                 return AST.CommaEmpty
	def expr_comma_1       (self, expr_comma, COMMA, expr_slice):                  return AST.flatcat (',', expr_comma, expr_slice)
	def expr_comma_2       (self, expr_slice):                                     return expr_slice

	def expr_slice_1       (self, expr_or_empty1, COLON1, expr_or_empty2, COLON2, expr_or_empty3):  return _expr_slice (expr_or_empty1, expr_or_empty2, expr_or_empty3)
	def expr_slice_2       (self, expr_or_empty1, COLON1, expr_or_empty2):                          return _expr_slice (expr_or_empty1, expr_or_empty2)
	def expr_slice_3       (self, expr):                                                            return expr

	def expr               (self, expr_eq):                                        return expr_eq

	def expr_eq_1          (self, expr_lambda1, EQ, expr_lambda2):                 return AST ('=', '=', expr_lambda1, expr_lambda2)
	def expr_eq_2          (self, expr_lambda):                                    return expr_lambda

	# def expr_lambda_1      (self, expr_var, expr_commas, COLON, expr):             return _expr_lambda (expr_commas, expr) if expr_var.is_var_lambda else _raise (SyntaxError ())
	def expr_lambda_2      (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr):                       return _expr_lambda (expr_paren.strip (), expr)
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
	def expr_or_empty_2    (self):                                                 return AST.CommaEmpty

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
