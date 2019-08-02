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

# def _raise (exc):
# 	raise exc

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

def _ast_pre_slice (pre, post):
	if not post.is_slice:
		return AST ('slice', pre, post, None)
	elif post.step is None:
		return AST ('slice', pre, post.start, post.stop)

	raise SyntaxError ('invalid slice')

#...............................................................................................
def _expr_comma (lhs, rhs):
	if not rhs.is_slice or rhs.step is not None or not rhs.stop or not rhs.start or not rhs.start.is_var:
		return AST.flatcat (',', lhs, rhs)

	if lhs.is_mul:
		if lhs.mul.len == 2 and lhs.mul [0].is_var_lambda and lhs.mul [1].is_var:
			return AST ('lamb', rhs.stop, (lhs.mul [1], rhs.start))

	elif lhs.is_comma:
		for i in range (lhs.comma.len - 1, -1, -1):
			if lhs.comma [i].is_mul and lhs.comma [i].mul.len == 2 and lhs.comma [i].mul [0].is_var_lambda and lhs.comma [i].mul [1].is_var:
				if i:
					return AST (',', lhs.comma [:i] + (('lamb', rhs.stop, (lhs.comma [i].mul [1], *lhs.comma [i + 1:], rhs.start)),))
				else:
					return AST ('lamb', rhs.stop, (lhs.comma [0].mul [1], *lhs.comma [1:], rhs.start))

			if not lhs.comma [i].is_var:
				break

	return AST.flatcat (',', lhs, rhs)

def _expr_colon (lhs, rhs):
	if lhs.is_ass:
		l, wrap_ass = lhs.rhs, lambda rhs, lhs = lhs.lhs: AST ('=', '=', lhs, rhs)
	else:
		l, wrap_ass = lhs, lambda rhs: rhs

	if l.is_var:
		if l.is_var_lambda:
			return wrap_ass (AST ('lamb', rhs, ()))

	elif l.is_mul:
		if l.mul.len == 2 and l.mul [0].is_var_lambda and l.mul [1].is_var:
			return wrap_ass (AST ('lamb', rhs, (l.mul [1],)))

	return _ast_pre_slice (lhs, rhs)

def _expr_mapsto (args, lamb):
	if args.is_var:
		return AST ('lamb', lamb, (args,))

	elif args.is_comma:
		for var in args.comma:
			if not var.is_var:
				break
		else:
			return AST ('lamb', lamb, args.comma)

	raise SyntaxError ('invalid lambda function')

def _expr_piece (expr, expr_if, expr_else):
	if expr_else.is_piece:
		return AST ('piece', ((expr, expr_if),) + expr_else.piece)
	else:
		return AST ('piece', ((expr, expr_if), (expr_else, True)))

def _expr_mul_imp (lhs, rhs, user_funcs = {}):
	last      = lhs.mul [-1] if lhs.is_mul else lhs
	arg, wrap = _ast_func_reorder (rhs)
	ast       = None

	if last.is_attr: # {x.y} *imp* () -> x.y(), x.{y.z} -> {x.y}.z
		if last.args is None:
			if arg.is_paren:
				ast = wrap (AST ('.', last.obj, last.attr, _ast_func_tuple_args (arg)))
			elif rhs.is_attr:
				ast = AST ('.', _expr_mul_imp (last, rhs.obj), rhs.attr)

	elif last.is_pow: # {x^y.z} *imp* () -> x^{y.z()}
		if last.exp.is_attr and last.exp.args is None:
			if arg.is_paren:
				ast = AST ('^', last.base, wrap (AST ('.', last.exp.obj, last.exp.attr, _ast_func_tuple_args (arg))))
			elif rhs.is_attr:
				ast = AST ('^', last.base, ('.', _expr_mul_imp (last.exp, rhs.obj), rhs.attr))

	elif last.is_var: # user_func *imp* () -> user_func ()
		if last.var in user_funcs:
			if arg.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg)))
			else:
				ast = wrap (AST ('func', last.var, (arg,)))

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
				if ast2:
					return (AST ('intg', neg (ast2), dv, *ast [3:]), ast.dv)
				elif neg.has_neg:
					return (AST ('intg', neg (AST.One), dv, *ast [3:]), ast.dv)
				else:
					return (AST ('intg', None, dv, *ast [3:]), ast.dv)

	elif ast.is_diff:
		ast2, neg = ast.diff.strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			if ast2:
				return (AST ('diff', neg (ast2), ast.dvs), dv)
			elif len (ast.dvs) == 1:
				return (neg (AST ('/', ('@', ast.diff_type or 'd'), ast.dvs [0])), dv)
			else:
				return (neg (AST ('/', ('@', ast.diff_type or 'd'), ('*', ast.dvs))), dv)

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
			if ast2:
				return (AST ('*', ast.mul [:-1] + (neg (ast2),)), dv)
			elif len (ast.mul) > 2:
				return (neg (AST ('*', ast.mul [:-1])), dv)
			else:
				return (neg (ast.mul [0]), dv)

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
		if ast:
			return AST ('intg', neg (ast), dv, *from_to)
		elif neg.has_neg:
			return AST ('intg', neg (AST.One), dv, *from_to)
		else:
			return neg (AST ('intg', None, dv, *from_to))

	raise SyntaxError ('integration expecting a differential')

def _expr_func (iparm, *args, strip = 1): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	ast, wrap = _ast_func_reorder (args [iparm])

	return wrap (AST (*(args [:iparm] + ((_ast_func_tuple_args (ast) if args [0] == 'func' else ast.strip (strip)),) + args [iparm + 1:])))

def _expr_func_func (FUNC, expr_neg_func, expr_super = None):
	func = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC

	if expr_super is None:
		return _expr_func (2, 'func', func, expr_neg_func)
	elif expr_super.remove_curlys () != AST.NegOne or not AST ('func', func, ()).is_trigh_func_noninv:
		return AST ('^', _expr_func_func (FUNC, expr_neg_func), expr_super)
	else:
		return _expr_func_func (f'a{func}', expr_neg_func)

def _expr_mat (expr_mat_rows):
	if not expr_mat_rows:
		return AST.MatEmpty
	elif len (expr_mat_rows [0]) > 1:
		return AST ('mat', expr_mat_rows)
	else:
		return AST ('vec', tuple (c [0] for c in expr_mat_rows))

def _expr_curly (ast): # convert curly expression to vector or matrix if appropriate
	if not ast.is_comma:
		return AST ('{', ast)
	elif not ast.comma: # empty {}?
		return AST.VarNull

	c = sum (bool (c.is_vec) for c in ast.comma)

	if c == len (ast.comma) and len (set (len (c.vec) for c in ast.comma)) == 1:
		if len (ast.comma [0].vec) > 1:
			return AST ('mat', tuple (c.vec for c in ast.comma))
		else:
			return AST ('vec', tuple (c.vec [0] for c in ast.comma))

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
	if VAR.grp [0]:
		var = 'partial' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_'))
	elif VAR.grp [1]:
		var = 'd' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_'))
	elif VAR.grp [3] in var_tex_xlat:
		var = var_tex_xlat [VAR.grp [3]]
	else:
		var = AST.Var.ANY2PY.get (VAR.grp [3].replace (' ', ''), VAR.grp [3].replace ('\\_', '_'))

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
			b'eJztXftv3baS/mcWqA3oABIfeuS3NE17g03S3iQtdmEEQZqmF8W2aTdJ7+6iuP/7zsw3lPjQsSXbxz4+PjB9RFEUhxzONySHD52cffFv7z/89EX1xaNvn377nK5PH3/9ii7fPXzx+PlT8jz55vm3Lx6/efT9i6f/Sbdfv3j4SC+NXg1dv3z8zZtHD18+fqn+' \
			b'Zw9fqe/LyfvD5P0OXkmVqTx78vx7eZfS+3cOePnqBf9+/yX9Pv/+Gf3+8JBDnjx/9Q3n8skzeSy/f3/BaT2V3H/LT7/+/jln8kt549G3z549DCV6EYi+CMTY8+LJN3/jJB4++45+v/ry6cunD1/+jbyPn3+lRWHfl5P3h8mrRXn8d/55+vKxBgducGqvkBHK' \
			b'AMd89vC7l6++ZXKvpJCP/+PR0/CYefrVkx+efMXJPPrq21fCCi25kPjuqTDqydf0I6kQj/itd28/vv/85vePb3768ddPn99+pKD3//vHxzef/vzj/Xjz4f0/3vz854d308Mfg/e3t5/fvPv91/j24+//k91+Cvfv3n56/+nTu/T2j/Q23L39cfJ+/jzm5ee3' \
			b'7z4H/x8TpTR7vwXvr7+M3l8+fP7HmK8/f33zy28j4X9O5f4wvfvTL/8M3s/vP0bBP/8c/D9+fPvuv95/jvg0luXPj7/+X0yOPBFXxpL99FNS+imz7/97LBoRGUv8y/t378cbqrsPU6J/fPr8e7gb3x5T//3X3z9MN7/99ja5+fTF6+rsZOOaypnTCh4rnmrj' \
			b'+Wqb6sRUpqs2TWXZczqGStgUsOnY0xj8eENP3Wkc1Lg4iL38Yo0f50/1ltKSKB0TbrwSpsAQqmFjwKYZxEd56ultUzl9RHlqpDCWc2BtZUGdbulOfE6KSo82+igE4M6G9+gFF4LYyz6JSTQ0Lm6DPwpvcNnIW0b+TR8ec1YksxqOnFcbo4G495SglVLXIYBK' \
			b'Lj5KydSSUo0fxyGa+BTEzJ9C2Us+SnbTVnaoNu0p7snDMQb8OASTjyqGfRTOlJmxKCkFtNFNhwsH8HtchVbqkFjKHBlOo/CNq4ug+NaVMVx6SwnbvgjKX/LpbVvcpi9sqBKYsbUKMhfWnGoQezkaiQmzkam7eowQgqfbjREUUR5OTFORsHI1GkrVCU84rvJ4' \
			b'PgYDkqC0LGKTp7gxUp0t/XeVc0HIqcgoolWIcf36it0ENHoWgscAZgCHtFNIg5BuCjEI6UMICasAoMNPhLVOMWFb/AjMVJ+04mWfDw9P9ZbuwgPQcPhxw1j2EOTrOIi9zBiLH6qf09PJy3EoIxpPbwlfQmvAA5USRoyR3HFNSAzRVjZoSUSjMAmZbp1Umgsw' \
			b'JgaI6uohXJ6e+YrlCfTjYA2geyHb44eE71TvCaWSNXrSSLp65yGAVDKSlUlquAgQFxeJTBvKRYEnzowFllsbUqU7B+XDfGhGn1Ef2Mwe8IjoDqfUzpzVTNCCRT2xpSLWE0hIUokyQc9ytij1tqvavhpMNdhqcNVAEtpWQ1cNPbVOLMiO2NRWnko3sPxSRXUV' \
			b'vVC1pILqqmuqzlSdrTpX9abqbdWLjif56ikeKUPDbGC40Ls13deUDHG6IXFmUaOcUGpUtRSx91XfVi1lqqlaU7W2al3V+qpt6TVKpKbcdKxhSfxI3LzglaqMYOl95SmXlG9KviamcStbCZ2Knlbt6+qk5ubh7MTK9YR4wxdiTkMMOyEOyVODRsQ4XDp5esaa' \
			b'Te5bvhxZaZWVwrQTVyuX2k7uW7C07RGLOCKhiNzgzukrgyR1lNWMwYNTDh/ZM8ser6IleDwZIHdDr0LlhGsoYlk4lGksTV4UlICIuBZEnLuW1DTLXlBx4oEGZDzku5E43HJQPVNjxtq8ol7OPazhRpkPNvVQGr1VRvXCN2Raekmat11mKuF7zO4rSsYZjzeO' \
			b'IC9E4Oykk5a6G6q+rnrKeFd1fdX5qmvvJzuaIztidpgjO2J22CM7puajQ/+9x8XqHZreJvSt0Ke36ENYdPVPJOMcq9b+alPrtdHX8LyXt+9WU3MyNFoWbU+1kW1RxFaeNjVdaqNVP1b0YTS2J63RImOc10IyWq9Dllbr3upVRcWhn+ZQ9W4An1jKuazEmaEa' \
			b'6v0rLfU2UbO+uTs5hmh61IB3sUjejQJArXgRJeQyzvc+5liHT7lYS9+0hgSxzRNjK6PQUHWpWtEfu7BzrTJxxMDKZI52I5jXDMxrR368lgkTo4Y0ut6fgoupkEp8/6pczKHmqCpnJEIwwPbhI3tm2OOObJkzBFso0MHdT3XCEwRGLeEGlnDmwz3jglj8zZVt' \
			b'9GfJHBXb7B2Y66X7dpAD4rMTkZiDK1V/gKXi+SGRxwYDtgbmCNPoFLaaNhoIsQmzsr20qIfBgjOeAzqY0vA8llQorFAzE+WvMZsua9JYv3c1Xuh0XgyD8y4sU+ggEZ2aszq8SzmTdw0u2mJYtBgW+L+T3FM4tMKUzHDRaqHTCdY6GEDleq3YrCfLooFl0cCy' \
			b'aGBWVra7Dt1czPlNPTq02ejXoeXOenf3oSFn0yq4BP29rzY+kbW9zl97/fLdQb77YY+LfjLoKi9f77EAsT0eHUuz17kM3V+717nUVsC3+5zLAdYNh1apgVnYB+MwLxEndc8Xagf4Qk2ARZfAnmJgYtH8Hyd5pzVCwhzqPAmnwL4Bd9aCb1R2i2GxlQGdBnuw' \
			b'PO0cgOPFUqOZUO6IW+2IG/TAuQNyT9dqyYjDYMRxP40wPQSxhwg2NmDValfdoI/ONoR7itUzHpPcT+GgvFqMvixGX1ZHX/aOriI54zGjvZtjRhks2gO15cnw1ugY1GIMajEGpcs4NLDRnetC36Pc9cCDMNFntddOCywGPRSaF0ZyF9ZivYbFqge5hM6L086L' \
			b'C7YLNNtOmm2H9tppQ+3u0wwo9xmEuYO2EqiI0XKjHQzKkbuzaoLy64peFuXdQTQdRNMF84hT84jb4148ZUEl2ocmHhLtRaL5lyTWKwY9CupRUH8fmz8onHtZdJZlD3tuqwLRQiBaCARdSF+r9LeI2WnM7lBs3Gdc4A4F7gQsaGN0rqKWoia2Wy5+D0b1eK8P' \
			b'UfuD4spwQKXxh1MakbRBFwfXujq4lsarrs6oE0O6DBmAYuKkvOzaEgOAMWy5n+z6QjTmCfQgisPZ9sKCISkz6T4wjXLOOs6LohQtCb51mnXOM91zBjgHPCXI8388J8jzgdyx414db2/lHa+WC09hzAdWkLz4nVe+8xZO2dZOz3n3HHORFz3LcQash5mrdM+7' \
			b'11gv84pxXi7Oy6l5KTWziuetuP/Cs048McU2EzaY8CJ83rDF/OX1CTwTQvVuak8sxQkRfAqDbPSuZGO0HlhAPmoqNlTyzcAbsPn8APJ72Xxe8eEHVKmbXk6MoCtv2XayI37DVbthBm0aOUlA9s5zUnKcAlHsOW26trzvvOYTOPhwi5r3aBucusD7tXGqAIVx' \
			b'8p1kqOeDGxpNUrbB17wFnCLz6QV8QIDn7A5ySoAcYyAbxuW8BXqT47KfN3jznnzeb07PycsZpjd7zhxvZad/Et9Nx6d9UFjHbzEDpGBSRM4Npckb7/kIENm73vK29s0gu/uJHD0auDxGzi0Y+H0O5pwwDaqJDdXcpvWvuSvKwp0IdhOQUog3ceWqEt4HIQ8K' \
			b'YU7UzUJxvy4x95cU9WahuHsusc8k3HPIdin3u5RzH/1tk3O/UNKvRcJZZi8l5F29VNANCzo1TJGAt7rrlmW8CTIeTb5iXnaFyLtI6re0axMC0oaRJEIbLmm1YDIkCdPurg/dZoGINI5mbEzjnQZ5+ya7fgQ9ThHUZihqIwTZFDm864m3+xcIorR4a3OBJIrH' \
			b'u054O8diRNUTqniBQ4EsesZblkZ0GUUYaSW2fBAfUrRxwQVl6iGusaRRXuXiJRAgY9TWiVsDOo4WY47vY9j1kSsgmNHNnOQ0TaEfYSo+IJXjQRIErYiGwA75q0EdufWaF49nE4qFTwpgBu8IXH2WwTfwagLxlEc2Ry3GcoPstbikgFYiCmmJltKZ4F395eoH' \
			b'rAOH/oFUDUnjA9YrJFl07f7Fk0Mj/utIBXT7BP5Z5LtF4D8Cn4DPhWaAMAX4uX3VtpVvgXo8i90a1EuyEeqFZIT6JN0C9ec6hnweRKUXIcdN3A8VIUB/VOOKGDQCeiGueXC4gAUx6JttoFfSGeiVVRPop1yuA73Wk+YgBb0yAqCXaCmdGdDPgN2Vjf3+I/0I' \
			b'82Uw5xGuIAKeGONmxLjJ3SqMmwzjJsN4nG6B8YJ0Et25IgjNuvgKgBsAHD4RAAOAGwDcAOAGADcpwM02gCvdDODKpwjgZqK8BuBaQ5qDFOBaJgW4AcAjOssA7g8U4MdOvIK85eHZRn4F0RHI2xHkbe5WgbzNQJ6NmpN0C5AXpJPozhVBCvJplC3lYAFoAfEx' \
			b'pkhAC5S3QHkLlLdAeZuivN2GciWXoVwZFaE8orwG5coyzUGKcmWDorwFyiM66/ru7RHth432ns0wDA94YrT3I9r73K1Ce2YgE3ox2uN0C7QXpJPozhVBivZ+QnuvaO+B9jGmSEAPtPdAew+090B7n6K934Z2JZyhXRkVoT2ivAbtWkWagxTtygZFew+0R3TW' \
			b'ob07ov2w0T5wbTI84InRPtq/m8KtQvuQoX3I0B6nW6B9jvoU3bkiSNE+TGgfFO0D0D7GFAkYgPYBaB+A9gFoH1K0D9vQroQztCujIrRHlNegXatIc5CiXdmgaIe1PaazDu390S5/P2DPVSnmOfUQ1/jiWlxwB/AjRuzWgN9kFjqTWeiSdHPwl6TznDhXBAH/' \
			b'ZrLQGR2+G9jnppgsCgYmOgMTnYGJzsBEZ1ITndlmoguEU/wHXk34jymvwH+oK81Bgv/ABuDfwEQX01mH/+GI/3uC/5arbyO/BkN6+TgE7hzuFP9t7lbhPxvYm2xgn6Rb4L8g3eRZca7InSqAaXBvdHBvMLifYooCwODeYHBvMLg3GNybdHBvtg3uA+FMASiz' \
			b'IgUQUV6jAJRtmoNUASgbVAFgcB/TWacAmvqoAe6JBujkQ0eowQ4aoIMG6KABulEDdLlbpQG6TAN0mQaI0y00QEE6z4lzRVAfyjUqgE4VQAcFMMYUBYA1NUIdUb3DBTyIFUC3TQEo4UwBKK8iBRBRXqMAtK40B6kCUDaoAuigACI6KxVAc1QA90QB9PJlrrZS' \
			b'DysArH6TC+5UAfS5W6UAMmufyax9SbqFAihI5zlxrghSBTAZ/Iwa/AwMflNMUQAw+BkY/AwMfgYGP5Ma/Mw2g18gnCkA5VWkACLKaxSA1pXmIFUAygZVADD4xXRWKoDj2rz7ogAGrjUGCjysAAYogAEKYDQAmsKtUgCZAdBkBsAk3UIBzFFP3nCuCFIFMNkA' \
			b'jdoADWyAU0xRALABGtgADWyABjZAk9oAzTYbYCCcKQDlVaQAIsprFIDWleYgVQDKBlUAsAHGdFYqABsrAHMYOoCXLzZHXbB9GoALIXZzy9xlP3/hyYo6kAvudD7A5m7VfIDN5gNsNh8Qp1vMBxSk85w4VwTplICdpgSsTgnwIffe4b2oXJgasJgasJgasJga' \
			b'sJgasOnUgN02NaAZyKYGlGfR1EBEec3UgFab5iCdGlB26NSAxdRARGelWti6jK/eG4Vwmyv5sn0uq7XATWgAnhriOSN/Uc/AcU1yCwpPNCnYSWDoFrjcXWmfjMnW7KNSpv+yb1DQT/LiyiDVBIymXgozre6TN4aJWBAL0QG1rgaodTlAresB6mx84BI9wOlP' \
			b'PQTNQdZDULalW3DM2rX7BltxWBrqcoSg7NAOAksA10O1wYK/iTupThi6B6Iru5autegAP7tufz+7BuZKa/iPHQNVBZ7rkdfxi8dgn5yBQpAL7lQh+NytGif4TB/4XB+YKOFCGRS0M9dif12eQV7ULyWUGx0ueNUJ2Hg3RZbhgsdwwWO44DFc8BgupBvy5HZ2' \
			b'uKC0M2WgLIuGCxHlNepAa01zkGoDrT7VBh46IKKzsl8wsx5wPxXC0V5wNVXA9SIGQ/UMXi6uxQV30AOIEbs1eiDvF9jMYJikm6uBknSeE+eKIHQL7GQwtGowtDAYTjFZFCw6BRZ9AosugUWPwKYdArvNYBgIpwog8GpSADHlFQog1JXmIFEAgQ1QABYGw5jO' \
			b'SgUws0RwRwqgvfioiqMa2LkaGCrZZl6ph9UAzIYWZkM7mg1t4VapgcxsOEANCNjl9JJG1YGkPIjQlOpgLhdJjpwrglQdTOZDq+ZDC/PhFFPUAcyHFuZDC/OhhfnQpuZDu818GAhn6kB5FqmDiPIadaB1pjlI1YGyQdUBzIcxnZXq4LiG8J4oAq4OWUOoHj4D' \
			b'CGsIHdYQunENIWLEbo0icNkaQpetIUzSzRVASTrPiXNFEBSAm9YQOjUSOKwhnGLKByWxhtBhDaHDGkKHNYQuXUPotq0hDIRTBRB4NSmAmPIKBRDqSnOQKIDABigAhzWEMZ2VCuC4iPCGFYDasG9PERiuFgYMPKwIDBSBgSIwoyIwuVulCEymCEymCOJ0C0VQ' \
			b'kM5z4lwRpIrATIrAqCIwUARjTFEEBorAQBEYKAIDRWBSRWC2KQIlnCkC5VWkCCLKzViCpepAa0zzkaoDTUrVAWyEMbV16sDMrCjc0Q6ia50oWH7y1S5gfQkoXx3GjtnJ4g5PZPV3o8kfz2K3CsDZKT0us/iXoC3IJaRnghSx07E8I+ElJ2g5tw2WmnoGS+VA' \
			b'BMspb0uxqGwvDtEK6SgQcebOlP7S3flmZkXfEYB7CcCWTRwb+XXpPns3Lsd3be5WATBbju/aiwBYkEtIc/VnQQrANgNguxCA29bYh9QzACoHIgBOeVsKQGVDCUBNRwGItfVT+osBOLOi7gjAvQRgz9ZFll54YgCOtm08i90qAGa2bddfBMCCXEKaqz8LUgD2' \
			b'GQD7hQDcZrEOqWcAVA5EAJzythSAyvYSgJqOAhCW6in9xQC0B7qJfZ8Gobc1+GSWywmT6okw68ezJfEsdmswK8lGmBV6EWaTdIvjXQvSSXTniiDgV5eopCdQeRwtqRFZACRvShk59Q4XlD9Ctt92rmSgmyI78GlC9pTFVbanUEOagwThgQtAuERL6SxE+PGM' \
			b'uQNGeMMsZ0jAEyN8tDDjWexWITyzMPvMwpykWyD8XCcIz4IU4c0cwmFg1oiCcFiXPazL2mp7WJd9al3226zLgW6GcOVThPBmorwG4VpDmoMU4coFRTisyzGdhQg/1EPmjggnhBvmN0MCnhjho+kYz2K3CuGZ6dhnpuMk3QLhBekkunNFkCLczCEclmONKAiH' \
			b'2djDbOxhNvYwG/vUbOy3mY0D3QzhyqcI4WaivAbhWkOagxThWiZFOAzGMZ2FCD/Ug+WOCCeEW2Y2QwKeGOHjthI8i90qhGfbSny2rSRJt0B4QTqJ7lwRpAi3cwjHbhKNKAjHVhKPrSQeW0k8tpL4dCuJ37aVJNDNEK58ihBuJ8prEK41pDlIEa5cUIRjK0lM' \
			b'ZyHCu9mP98RLyf2tbiopvpB0O2fB1zNfD4oVgrmmLSdrFUO/UDm4yyiI/oKPELX4Ip1a5bLvtPjROoc4sbvSlhSfmeeShMsvFpnkq0VlXjwsdnkQL0EXw7/v59QJLHcaV9QJFqB6LED1WIDqsQDVpwtQuebyDyD5yMQ3+4WYkK1M1Sg7060qY7YW6hoWEdE3' \
			b'/fjxGF8sUeXvxwR2qdKB8W/iWap0/AMKI80jD+V34N9WQlgV8aXjWP/C997PbuIbYvv1ATG/ov3fZlF31TlfVhr27xtie/j9MDmtZWGjfNnPKw0z8t3sRMSnlrPbG0FfIuR+RtCXCPkFX8qz5rYkPWp3Gj0VYV8kflmzUJcSv0zaqeSltJfdyeuV9uFapb2+' \
			b'AYm/QNqpWho5CBdS33B5huEuSr9trl/6mX23+81IdKHbEQWhG12goVnYt7mGD0gWn0jlXRrrlw/cVkenW4CK/nLtwDkosOsMl9fz1dQmWsKqyZrbaAt4wLiwPTAXI6KZbxOqv0gGHlDNyKfmzM309aem4byvqV4GDtyg03Oqh9v5iPDS/v/ef0RYhuf6f50N' \
			b'BHqTnVhIbuHjwo2w7OKuEsGibx4QWYGFrc52CQcW/jq0CkNF3FyJgpscDLDEk79zlxoQ7IGUy5lHw6Ts+RCBS0n2zXX45fgiyai/VKff7Vx+u76i1kpFuN+pFM+abS8ryRRGlXEIEs1q1kxSzSvt+91KtinXQV1eR8sJ/Mym7tJS7i+Qcmpmr0FRQ8S7K0v5' \
			b'gkmK2cmJy0h6e2N6u1+3lugSkj5KOM/v1dch5X2zWocPl5P0Rki5K0l5e5GUd9cn5aOINzfVI7mshB+YdMeS3eTbQ3baO7mkZF9VqruLpLrfgVSbo1TfolR3hy/V/UVSvWp5xkKptkepvkWpzhclHKBUD7u3hlzGFHjTRpCwqqdfbfqrRLRuecR4eYvezdo9' \
			b'goTyEqk1U/vVX90DUhVsv6MqP0rsHTZuXJuo8nK825mR3GZktuYB4UeEtNm9ka5L7HQ7Ms9tW1l5VRPdXZVe5sqmScxzO1O6Tbcjs9z6bgJx4Prlecuq5EQBt/ES45tUw2v2DFwwZygLTBpZw7AXgo312en/eWpanicLc2+ya7FqLf8Fywb5IwDyTQgpUaHA' \
			b'vXtAoBf9vYtJwqO835a8t8X/+fLeHoy8e5X39gJ5d9VZX00bz4wIuBHRjuVahJrH+8kerW5ertpsi8TQUP1zLqI9UFLZndYy1/Bc7Y41mx9SJa3kDB+ZMzFH2kEaMb+ikBM2vfSqBGxLCu3KgjM4pPAsYJctfCOftVdhbUfhXMYQX/LEjWxp17DFl5zZD+70' \
			b'KZwDh9x1calbw6VzVD2U/AoNv4Cta7R3obVDl7u9ahVISdL/Us22Gr5OtS6pvXWKM6vk8LGoukv1Yp/X+u0ZGGI5uMmVb1uHZDOyMt9sD1sk5yaNB7M7S3djLCjFaqbttbw51IuMDUcZWyFjNzgVcBUh4+2yzW0LmbEP5KOFJGtszGkfbGQXICV/lLgVEmfu' \
			b'hsQZyel+SlyTStwt2+r3XOhY2PbcFr9fzSlLmNlbCbvprQpBymyVfvTyPIk7t/+2G4kTmpcROH5xNzLHKW8ZGLCRqgkfjsyUXvm9SEpapXFfpif3QSC3CKHM492dachY9d3A1ONC9efkaxRN1zFfZTje44GX8+29oXAqxTC8PiXfyUbORsfxMziwY9y9RaNy' \
			b'/i4272snYnyWiZzLMm3G6ltOeGMuSIGkPf2Tt/RE2vg93UCWvm15R5nVv7A1TO8lIZck1OQn5UzppqfayOZMXq89Tm3qITE4uIXPQq7wR2LsZA1WcAhmc7v6ePcy8ZceschTTfM2Yl4JhS3Fkk1/uWzyUTMX5pRiXvjHMwJZmOSrXZqvuXOBtmaNn43ZI2W1' \
			b'5Y+nLbY+I8zTVTLZ5ZksDkRy8imCxN52/llm6XFG3D7Kbt0wK8bqkqWaLYoUxicUzZUzPkVoPBVoqMbTfwYTn/jzmhuD8c9X6U3m5v7mYpVh8wnHj6aowt5+9zJAGudyf5LB4Qbqf9ywHUSg3aEYcGK7dmwMnm76qycpVdHUuxcW7rRcv0P2mzj7XJ/9NQlU' \
			b'c+sy1VWjw8e94pDLO3tdCZ3nUDnmfNnSg8PORfVWCQt8HKWMe+LbnXRSz3PcfZ4JpeoPNyiTPViB43HMXXWomwv6jkvkDRWwQupsdUUXxmznxkL5/MHKHo+e76pD3RQd77JWFosf6mChEM5xs6liR2PXLGS5C1aEC2JlNgDhSHe40mqqO+tQN8UQ4Tal1Va3' \
			b'5MCL4XDl1FV31sEWVYxOblNOfXVLDrw43KEOW8rvqkPdmLtYN+E7y8vqqKv23DUd//fnREFd2WvXKcN549R6gWphsbhWx/U8E0qZ3vIGWFMMoLYJ8HVxZ05VbOeSrc53/J3ui+IscXE6c2mCWcUUwH4xy1f74cCsBcOj22RWV+2HA7MOZ36E1dACJ3Pc0f/C' \
			b'185LYnlyszFQEQuGSXekInitwZ1xYP5NzBLdEPN9dXccpvMXDLzuCvPb6u44ML85HOZ31d1xYD4fr8zbljq9t+G+x73je2YNh/HyqAbh1B2Ma4j4x+sDOjmXzVRy5LpWbzsbs68ih4hdEZGrgiMPVeyaDl1SPstoXBTUcnUieMBXhYOonFvt3cBzj7z2LF5z' \
			b'Nq4Vm1kn1oNRfIBHtkFKdorKDDBTFEpKhScJPQsJBh58rkLTC+WBivL69P8BNkujdw==' 

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
		('COLON',         r'{:}|:'),
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
	def expr_comma_1       (self, expr_comma, COMMA, expr_colon):                  return _expr_comma (expr_comma, expr_colon)
	def expr_comma_2       (self, expr_colon):                                     return expr_colon

	def expr_colon_1       (self, expr, COLON, expr_colon):                        return _expr_colon (expr, expr_colon)
	def expr_colon_2       (self, expr, COLON):                                    return AST ('slice', expr, False, None)
	def expr_colon_3       (self, COLON, expr_colon):                              return _ast_pre_slice (False, expr_colon)
	def expr_colon_4       (self, COLON):                                          return AST ('slice', False, False, None)
	def expr_colon_5       (self, expr):                                           return expr

	def expr               (self, expr_eq):                                        return expr_eq

	def expr_eq_1          (self, expr_mapsto1, EQ, expr_mapsto2):                 return AST ('=', '=', expr_mapsto1, expr_mapsto2)
	def expr_eq_2          (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr):                       return _expr_mapsto (expr_paren.strip (), expr)
	def expr_mapsto_2      (self, expr_piece):                                     return expr_piece

	def expr_piece_1       (self, expr_ineq, IF, expr_eq, ELSE, expr_mapsto):      return _expr_piece (expr_ineq, expr_eq, expr_mapsto)
	def expr_piece_2       (self, expr_ineq, IF, expr_eq):                         return AST ('piece', ((expr_ineq, expr_eq),))
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
# 	a = p.parse (r'lambda x: y') [0]
# 	# a = sym.ast2spt (a)
# 	print (a)
