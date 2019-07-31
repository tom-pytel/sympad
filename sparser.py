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

def _expr_func_func (FUNC, expr_neg_func):
	func = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC

	return _expr_func (2, 'func', func, expr_neg_func)

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
			b'eJztXftv3baS/mcWqA3IgMSHKOW3tE17g03S3iQtdmEEQZqmF8X2tWm6D1zs/74z8w0fomRb5/jYPsc+sHwkUhRnOJxvRA4fOjn/7F8+/PbjZ81n3z9+Sb/Pnnz1mk7fPn755MUzunj69YtvXj55+8V3L5/9OwW/evn4Cz11ejZ0/vzJ12+/ePzqySu9fv74' \
			b'tV59ni+/z5ff4lJyZSrPn774Tp6l/P6VI169ZmZeffc5/b747jkz8uL118zf0+dyQ37//pJz+eq7F8zTsxf88w0n+lyK8sU3z58/lvOzb17EMr2MZF9Gcnzx8unXf+OsHj//ln6//PzZq2ePX/2NLp+8+FILw1ef58vv86UW5snf+efZqycaHeXBub0GQ8QA' \
			b'p3z++NtXr79hcq+lmE/+7Ytn8TZL9cun3z/9krP54stvXosw5PGnL4TEt89EVE+/oh/JhaTET71/9/HDp7e/f3z74w+//Pnp3UeK+vA/f3x8++dff3xIgd8+/OPtT3/99j7f/CFe/vru09v3v/9SBj/+/t9V8M8Yfv/uzw9//vl+GvxjGoyhdz/ky0+fEi8/' \
			b'vXv/KV7/kSlN2fs1Xv7yc7r8+bdP/0h8/fXL259/TYR/yw/8+PN/xctPHz4W0T/9FK9/+Pju/X98+FQIJxXgr4+//G9Jgy4KUaTi/PjjpMiZww//mcpDRFIxf/7w/kMKUIX9ljP9489Pv8fQf+Xq++Xdrz/8+C6GUraJ7O+//vpuEvjzszfN+cmZ6xpnThtc' \
			b'WL6wzZmTc9ecmMb0zVnXWL44TbESlyPOBr7oLH68obv+tIzqXBnFl/xgix+HG3RFeUmSgQl3XglTZIzVuBRxZlq5Ms0JBSit01vMAgph+Mc21p1qkEJy5aSodOvMnk4iELLxObrvYhRf0pWRfxPio5ypkNV48EDcaSTCPfFvhf82RlAZ5GqktFJ00+HHcdk0' \
			b'8xzFYsyxfMn1Rv++sZQF5Oj4glOM+HGoJroiEQs1kjvLkWVkTmNMX4aCnjmKnw1UIagRkghRtuNpimd1acuoMzMUD1U3JaoMunkKNw0y1WEWVT/kZ1xpsOtULYnvzsYovuS0JD2WPhPgHDVBjM7BMyNC9fQP5ecHThF1JuIiDk5M23Sh4VruG+9EWpwpFGI5' \
			b'AeOOELMqHdX/NN0ZYZCuqMBnQ+NcZInqYJRyOgUSl5B0xJdwonsxOkVwlXNMn2M6xIQcYxAzxBhSZIFHwE+BqKC4sD1+BEzIiUJ8yVc+3jzVIIXiDdDw+HFjKnuM8m0ZxZcsGIsfqrfT03zJaYhH4VgfIQY7kRTBR26ozjCaDPIi+Yk6i02y0RYiGcVJTA46' \
			b'qTMbIU5K0gnmRmidl5usaJB5Ga0RFBa6A35IK081TBAW3tgOBslYgx54JyGTVUhqw2WA/rlCZ/pYMIo8cRmLErQpVwo6lJ+eNSZe9XrRpQtJ1DfdKb1MztuGdJJIEAJJ5oQasZ9Uj56YHJuuHZveNb1vhrEZ22bsmtE0o21G14ysUcwzUxaJkNpTlZKRDM1A' \
			b'Ctz3TR+afmj6sQlkobomjM3QNoNgkazb4JqB0psG7xsqeNdSuCXmWpJJO7DlYv23zTA0g2kGokGsEcAo37bpu6Y3TU8Pt/wovxbphciocqR6PcmDTTDpIOmcF8yOfTOSvpOoOf+GKtI1vunfNCcUOKWXK0mDK9P0OFkRE9s3DlqksRrykOEJiYrDwvfpUZ6Q' \
			b'JxdWhDJCaD2EBr076T1iB6TqIW7m/FQQKXId26M8kzypZFDQ4SiULBQDoYyCzJMROjZGYFqRFUo3LxeKkwpSl4KYJ0ESEaeSt+NOclND48GyB8tBfgfluxN08GuBMqWsKdOxIdP9UKu567WaISuchlalNYgIwS+xmdm6OZ4mEi8FfU3tOOfuxhHeWu/00hBc' \
			b'BGI+NGFogmuCb4Jpgn3AMhmOMpnJZDzKpJZJaI8yqd4jocObAyej7xG0+Dunb/kWjXuksQbtVeFZmrNBz4Mmx2t8kIbIQb1rTgZ0Wwbt1XiU0Mu7dqS6HbWKU4Xei1fsiQ/aIUFF96joXiu6t1q/rZ618ee0awIhORFS11Jky0UlwRDDYe8Ke84OAqlVczAM' \
			b'axu+lrDcA/jccDCFgYnxUCbfZWgdAvcjxG372J2Ktk9tokLDH1us+a3LcoDjiE4PVgpUbCr+Ays2+wGNurq48h9m1VMBzdEcpI5JL+aAuDkKJQnFHYWRPZgtbAaV8OG+MNipbdSPa+DHfbjCELe1ubaj+XwyqPImDU+xG9uoA5rO97GLd34SpGj3rFDD/SsU' \
			b'j3SIMnbatYBLgsfEZdhVh3c6dKNM9PgHUeF7IYFzHse4L4XhoRipTvThFwZ332AEWKZVsaXvAx4IiA1QgxBHgAPcLUEfDXBm9AOeFS1gP6dkYeUNyh47FuchCs+oYRZMVK4Pj4bkdJxwjBMP5LxLXsY4at9C1JBtzxy+gXfMqFfMoDKZfm7T4cWNlt0De32z' \
			b'bxCykWrcV9+OqNc+s2d3rdLsacOck35/S34yqHfa2f3VHvYmG/hooelhj3l12rVw4x4z6Ts1/e0eM2nVl4FXQvJz8nRRtvenmAlnH6jni71+Fo0eEQXxbtHAOY7CVrN5jEgG4qKSyqmTkxkgvBFqNXIa1jyN9oieNoIC4upJQQux3Nuw2tsw6GZwQ+shT62S' \
			b'vpVB3+rhulxYTyz0xKI5q9C12jcx6JRw//shQ/ece2IPWE16WJUe2hJa6IeF7TrAKSDn3Fu2B9lblm6yvZ/+S+7XG+19W/S+LXrf9jR3kNoi5PBKNfCbcNdT7Fir3fMWzpYBhszBvDm8OB2U2YMUHiRcOzRlnDZlXPTV4P3t5P3t8OJ2+sZ2D2/E16BmOm3z' \
			b'BbRpkrvKqIGAwA7SQBC7btbkItYd9NJBL130Cjn1Crm97cVQvl6V2seXPJTai1LzL6mqV/x5lNOjnP7BvvtgcR5u+VmpPZzZvapGD9XooRp0IrYVBj1SBk0Z7ol//5zLG1DeIKjBuIyO0rRS0onjmks/QE4Dnhti0uE+CWW8P4Ux96YwomajzvFtdZJvK2+w' \
			b'tuGVr2TMwADsEbMkFHnZVSsrrzA3JcoAlg/8l3xywZ0UeZCSuiinQYyaEeE5sYkiAUCkF2Y7EQQxyGVh8jwUyuOgPNrJA6G8BpUX/bH141npPCWdZ53zKlRegsrTM3lpGi8skwXndJ+nKfMcZZ4wy7NleW43T+zmuc+8WpUtN89/ZsGwULgSeYEmr6PgMTce' \
			b'jmOnCTdZeH44L7FizzQvQiT+DTcoW+oPt56EiQ0EeJUyVr3zcnAu3ZnnpdH0guDl9/SGOKPaPRu9LIuXBc5eFqI3vII68I4UvD8CXQ/8PGfFa6BbyUzWTvOGApQ91e4Z8XRGZTnrZfkzZ0fpR167zik5n8gDL6km7pkFKsyZ7zUnJxd0g4p1xttfUM2c8RYO' \
			b'vOeAlZuNrELnBfA9585huj86bD3AC8DpUV4uztsJMBnZjIBSM2MU33O5ZIcMyln44e0bWi4C0+L9ASglr5DnJfGUwHP2nWyKcUY1djaM2PKBqXNquuxZlCIXXtpNaXvzhhugrM49lNgIJLwuH4R3yxhV5TzrSiBUAvwy5bZZv0s845WebAKaBMkscLugj7jt' \
			b'1HMCB6h21oAKm4HBA5o8476YHF2DWxYUJ8wYxY1T7PQFfuger+ZO2DEVZigdLxCdYYdtiptjiOdy80RunsXN0+l5AecqXDGm2owr9kkKtroCX3SPh6USxozijKqO5GG4IzfBHBm5hC25picGQRZ2xRgisobibyXKhoSxYYoyuUWiAcGMtmHhL6GviAIOh4RE' \
			b'zmVsAMb0lJMEQWgDloMAE9AcEjjBhIKSAZnAiKJOASlxBSiV3KjnVfAcVQLeC4sjkA6AIhcAdBCIpgJloDb/7B+JXFz7iE3ZGB6JwEm9HrGVIBWhs/k/aVIdAX2rgL4rIEuhE5Q1RE/xi4MKELAXiCQBnq0mSsdaVOdXZ/321ChGNq4KbF9yhLZAuZ0cEeo2' \
			b'YZ0T86SSDmiXVMjAIVkAWwp5C8xbgN4m1EcBLeE+imOKfI0tsZ+4HDeAfgc+GPy2Rr/SiPi3MACJzJY2wBY2oCvMwHD3BuBC9NtVBuAIfgU/FyqBv5cQR3BDWRvJcl+Q35n6WIl8TqnI58sS+ZoPC0gpF8if0cuEI+zreKr83oghM1V7exxBqc9ZOKQK4ArA' \
			b'lzRg2QsLCfjK3yLwVRoV8BFbAD/zuRHw8Yj3YHcKfJUfgC/k2omYLgb+AuDd0kt/n9F+hPp6qFvZ4yu+5xEqcW4Tzm19rMV5fsN31Rte83EuUS5wPqOXCSecV/F4vXd2AeQWII/PY3c1FlN+u3d4u3d4u3fF212ZWwS5iqICOWJLkCcmNwK5ysyD3SnIVXgK' \
			b'crzdSxltBHJ/D0F+bNAXQA8NtvoD0BEqgR4S0EN9rAV6yEAPFdCRD0tHKRdAn9HLhBPQq3gFekhAlzxHEOknGTgkQzAiPQDpAUgPGenK3SLSVRYV0hFbIj1FboR0ZdCD3SnSVXqK9ACkF2Xcqh3fHxF/vxE/Nl32dGuoRPyYED871iJ+zIgfK8QjH5aOUi4Q' \
			b'v0QysauIr+IV8WNG/AjEj0B8kYFDsgCeFPEjED8C8WNGvHK3iHiVRYV4xJaIT8Q3Qjwe8R7sThGvBVPEj0B8UcatEB+OiL/XiOeKbBPiNVQgXm4K4nGvPFYinlMq4vmyRLzm41yinBE/p5cJR8TX8UC8XAHxBr46IdJPMnBIFsATEC/JwLAXBiLiI3dLiI+y' \
			b'mCJeYwvEZ+KbIF4f8R7sThAfpQfEC7mpkLZC/HD01z8Q6BuuywR9hEacXNfo7vkmee2QojzWGoDstTOV107zYQOg9AsDMKM3oZ1sQBWvNiB77STbEXT6SQYOyQLYUhsAt52B285kt11kcNEGqDgqG4DY0gYk4hvZADziPdid2gAVoNoAuO3KMm5lA8ajDXgg' \
			b'NiDIh0SiDUBoxNdF2AYE2IDU0UeK8lhrA3JH31Qdfc2HbYDSL2zAlBhXwIR4MgIVU2oEcmffoLNv0NkvM3BIhmA0AujsG3T2Te7sRw4XjYDKozICiC2NQIrcyAgogx7sTo2ASlCNADr7ZRm3MgJde7QCD8QKDPJFmWgFEGIrgHk4+BAIksAKDPWx1grkCTmm' \
			b'mpGj+bAVUPqFFZjRm9BORqCKVyOQZ+kYOPYN5umUGTgkC2BLjQBm6xhM1zF5vk5kcNEIqDgqI4DY0ggk4hsZAWXHg92pEVABqhHA1J2yjNsZgeN8vIdiBEautmQEEGIjMMIIjDACyQNoZsdaI5A9gKbyAGo+bASUfmEElkhm2skIVPFqBLIT0MAJaOAELDNw' \
			b'SBbAlhoBOAENnIAmOwEjg4tGQMVRGQHElkYgEd/ICOAR78Hu1AhowdQIwAlYlnE7I3Ccw/dAjABXWHYHamjEB+JcF7/nZZNTECnKY6URsNkpaCunoObjXKKfjcCc3oR2NAJ1PIyAzX5BC7+ghV+wzAAfuSOB2ewXtPALWvgFbfYLRgaXjEAUx9QIaGxhBDLx' \
			b'TYyAPuI92J0YgShAGAELv2BZxu2MgJ0aAXvYdkA2Lm+P5uDy8UBmLI8HiqA5YpSXgH4UUgYG0/oXPFIeawcGXR4YdNXAIPJxKcdyYHBGb0I7jQ1W8To26PLYoMPYYFwP4TBGWGSkDwawp2OEDmOEDmOELo8RKqOLY4QqlmqMELHlGGEu7yZjhHjEe7A7HSNU' \
			b'QeoYocMYYVHG7SzDJbP9ugMeJ9yVFahXuG1oCW7FCvBoPI8h+6t6Cb7BgjT0EhAqxguD3kcXwdfHFqvj+KmJMZA60ZlB8brsJ8yIZuqpk1DFR2uAXkLwysUoKcUORELQDJ0d1BbTg1qdH9TqBKG2cBqqlLItYAq5t6CSqXoLiK1W30k+m/QVvKzBY3Vo525D' \
			b'kIidBa567iM0ZzqKUIhtwS6MdJZZVHz2Ygf8BdP896qF0F53yv+xgVCYgx6faNdp/7bRiBGfbme/QQ+/QZ+MQl8fa/0GfbYJfW0TlJBLDBQGYUawPPpibnDNF68BkK8Zm7zmVjIfQa1MK+6DHu6DPrsPsBRXYsBitAma06L7QKVSGQTElu6DRHwjk4BHvAe7' \
			b'U4ugHKtFwArdsozbtQ8Wpw3ulVE4ug924z4YuG6S+wAh7IQg7gMMJNg0kIAU5bHWfZAHEmw1kKD5sPtA6Rfugxm9Ce3kPqji1X2QBxIsGgcWAwllBg7JAthS9wEGEiwGEmweSIgMLroPVByV+wCxpfsgEd/IfaDseLA7dR+oANV9gIGEsozbGYHFmYQ7NwIX' \
			b'bNdxNAW3bgpGrp5kChBiU4DhBIvhBJuGE+zsWGsK8nDCiJkF3IrVvVxgEZAdW4RR0pQWYYlyZiFZhCpeLUIeVbAYVbAYVSgzcEgW5BQtAkYVLEYVbB5ViHJatAgqlcoiILa0CIn4RhYBj3gPdqcWQQumFgGjCmUZt7MIx5mGD8QWcH3knQE0RE+JzwAh1Jra' \
			b'AsSVx0pbwCnVFvBl2SyIdFyin43AnN6EdjQCdTyMgFzBCEi2I+j0kwwckgWwBSMgycCzRzo1ApHBJSMQxTE1AhpbGIFMfBMjoI94D3YnRiAKEEZAyLWTMm5nBBanGu56gcFkJ6trOwsz2Pvm8n2vbgrMWwD5+iC2LNIEYoQKz59Ly35xrzzWwjd7/Vy17Lfe' \
			b'FmtOIxNLeK3iFa/VUl+HZb5nV22hFUu8iEotZYVKxJaoTLysRqSKws/gqPkoHLGUt5TBxXBc2qRnca7fEYZ7CEPfuOyA11AJw+R9x73yWAtDn2Hor4DhjEYmlmBYxSsMfQVDvxKGWuJFGGopKxgitoRhSroahki+AEPNR2HoAcNCBpvBcHG23RGGewjDwF6G' \
			b'BEOEShimKfO4Vx5rYZinzLtwBQxnNDKxBMMqXmEYKhiGlTDUEi/CUEtZwRCxJQxT5GoYIvkCDDUfhSFmwJcy2AyGi/PdDnzV67EzqsgdWfIJuQiVyE0uKTc71iI3u6RcNcNV82ElUMoFipdIJnYVxVW8onhsZtvXOLii0vMOqQJY0i4o/FAOfiiX/VCRuUV4' \
			b'qygqeCO2hHdicqMuKB7xHuxOUa6lUpTDD1XKaDOU2yPK7y3KWeZ5IquGCpT7NIUV98pjJcp9nsLqqymsmg9JJ1LOKJ/Ty4Qjyut4oNy3c5R7zGBNzzukCmAJKPeYvuoxfdXn6auRuSWUR1FMUa6xBcozk5ugXB/xHuxOUB6FB5R7TF8tZbQZyo9b0d1jlBsW' \
			b'eEI5QiXK0+J13CuPtSjPi9d9tXhd82GUK+UC5TN6mXBCeRWvKDcLKMfa9fS8Q6oAlhTlWLjusXDd54XrkblFlKsoKpQjtkR5YnIjlOMR78HuFOUqPEU5ppyVMtoM5fdxL7ojyhXllqWdUI5QifLkeca98liL8ux59pXnWfNhlCvlAuUzeplwQnkVryi3CyiH' \
			b'Jzo975AqgCVFuQXKLVBuM8qVuUWUqygqlCO2RHliciOUq8w82J2iXIWnKIeXupTRZijvL/rWSTnbtN/7uec3trU07/WVPrbCpsBW5qDbzZT0jc0C5UECWWce3DYmIqz6bgvxwfWlrrrqAy4+ueyQpjy2mLfuK5+dZuQyC9mO4LszfoGwLzx4dTxPT4UxCQvG' \
			b'BI68lAXKNyAYjQnmrHtMWfd5xjpXWvxkjJQBp0s/HBMFVRkZxFbT2KME1loZ1ivZ5V651EZFqM0Nf1wmyllNDlyBpTCnJofiyODITfkd+JdtD5/I9Pgglic05zf+jaU9+cCS2wDT4yUudddc/KEl/j7QHn1jaZ++r8Ri2fobS1MoXPadJWLw5jWaWOzbfdHr' \
			b'bXV6jT7v4UfDunKTtH1Q7Jv8cJg0Hg1M9bis2OYGdNsfmm77m9Rvs9yuulEdHw5Tx1nyW34gj0S2qN/zzs/19TvsUL/5M5f7YL9J0h1VctTzjvteskXsIeh7ucnFzvSdRXb3dh2dvD7pfezozfS/W99woVrc1RdPqQa3mPJyV+3ysAIHww21ZdZvCnmtj6B2' \
			b'xcRr5GZWzl3Znb1nB8YGNt9cjYHuovYN1T+1cJx8Tc3cUtM9urN29BIgxSPV6mQfz7tqzK/toO5hgx5OIv3f6UsA7cIgPro7auSzOVrX0Kc6fESkBQi2Ob8FjwyVWd8Bg3zfezME3EX3la6D26aZvyfanj/WNWRzz1vm1KMmqzT99ruvYNZs1bx3t6PT1LQf' \
			b'olqHm9XspYGF62g3v3fNvdJyNuomazrrpb9ZbV/4ZMX1bLnhAvHD22u+X6f59PrbiYudCnRdzV8ztLY0pLat9vd3Zd+HG/e5s3DOQtiF5oeNWzGhv44rpwMCrqH5/UrNH3ak+Unt29tqzVxH6++pxpfa3tXLoW6yZXMdbb+upoeVmj7uWtO7o6bviaZv1Vs9' \
			b'PE0fVrbjV05FWq/p5qjpe6Lp9bSce6rp4630WLdyP97h3IEwbOpytA2UeT96pdt7Fu9uugBPGtxkHkzzT55bKpuXklSPWnydGTB75lTZmfp2opB7NtuFdOAR4UoUt7sdh2E/8RnekAZfNA95F+7CQ9foThR0KF2FN2ac+RvxN+Yi3LyJQbd2r+MXzeivDbUv' \
			b'J+nfprneZHL9inFOmfjSyRyLvVF2rHSY/l9lziVNOdX9Nlslm0xZXzE7lzfdl08xMPcLrROy8g5W/iaGOo8I2AcE+Nn/1Qjw9wgBXhHgr0CAa851gaePWm9F361oelLzTvV3ugiyX1azvlqBNHasCiJzrn/mo1hpKHUetLLxxZRJJcskhlhf5VI8eacuCJTl' \
			b'U8ql7+V151cXdQJYJw0yQeCaott58RktlQhY5zYTAXMwVd2oqqyFa8Ti55JxSTj9euG4Rfnsh4yWIB7lFBF7bVmF1bK64l2At8AGr4AVwt1kUfHMpMdWe3/dipCSTP+X7a/e28zmrjICay3qQj3HTzm1/dRYDksVf0fui4vWou+ik3fZW//Cjt2l6rL8Sh/t' \
			b'9Ttw23faFld176Zzdskb+mL3g+0fURtHFG08Ktp2isY1t3/Or0LTeL16e9eaZtwj/qigpRP7hvyjs4HVjrI8qt12atftu9p1wuN+ql03V7u7HBg4GM3jCV176/Dfr7crq5nZXzW7iTGnNapmqw9UrlO7Wx1nEmrbaJ2Mvd+I4nHOF/QYuNfRxW89VuZv/m1H' \
			b'6hIWKrkXo6L7oJVXaiJX3kGMepZG8AZGOrc0hK455xHYANGyH8BLvJfvUXhL8fwt7+HNKV2dnOn26dgLysjuL2kRG8mNv2jNG1LwTkCBV3Riw6S8Lg25n5krszHN7E+etJMnTb3pFDaLqraJEi+wLO7V0c+46xJ2QeJvaTX4o5qwPMUrHVZW2OEmFlh3slCU' \
			b'bvHWSoysEZOssOpZeHSreJztZgU2zRWsEsYX/3g8YBLuqxTCml/D2uJeW5dyx1tOJQ7J7Cz+8ajFRfe8jCHQWbjsSy7ZHI3C62yLMXwURR1r8Kpd/rmp6U5ho81rjW2TvyoVdD8wIi97gPUXF3yyVxel4Q+bp/23xibts8Wfa817a71hU4+/IM70Hj/TyPLo' \
			b'Z3/zNEVWF9xZeJqgLzOp+iJR8ZBUR7gFpQnNln/C4VBzeD1VmevJVEm2VJBVijE28Y9f2GWgOsbZ31KaeVz16CxtlZPId7wFDeBmyO4PYb9rb1o/dmlHVqkJN9Ru9ujKQNhJlqiM7jaUqW9u4AD/5iDfTuu0iqfU6sEcmaaM2fKwO8nl6gO1c0UD0V0F7Et1' \
			b'LAoy6Rn3zy4++PvkF9/lTtXyjZCfQ6Hc/VU57t4e6oHKuaJNfaXGoQY21DvXXOeIffmrEqKAh9kcX6V97FY51AOVM2ucz6tlk7bMBmq4JE7TlMcwDa4/on/p6oSVg0hEMtxjfbXNwR6onFlX4k711TV3dMAN1t5jTfXNwR6onFk/5U41tW/u6IAw7nGnhwdS' \
			b'DvVA5cz6PNfT1PGKXlAp3Qul6qALOzq4VpdvENcXPATZzJzxF6jsDsWzoIAXi8k0lx+juyLByqPMZylPSGvWl9kzablmPw5Iq99zafXNfhyQ1oqeyqE46dkarTjwaZn8v/KxC5/fKK/FRKiJezRcwlMdDuaA9Ff0gA5G+q45nAPzB258KOgWpe+bwzkg/RV9' \
			b'qoORft8czgHp87bWzHrQsI1h9CN4Z1QWj+XZQLy7io7/876RZRWR/CgBCYV3t+t4P6Su1xz7xZShKQ4kDLOEXBWceGjKowvwG8luT3FCkufqRPQo3xtPunJp1YdRhpmNTnnT6W5pqtrCNDXlVrYumS7fkmmSGLa2SqlTar0oESkLnu14WE0oj1SUN6f/D6YM' \
			b'yOM=' 

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

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY - {AST.Func.NOREMAP, AST.Func.NOEVAL})))})"
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
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
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
	def expr_comma_1       (self, expr_comma, COMMA, expr):                        return AST.flatcat (',', expr_comma, expr)
	def expr_comma_2       (self, expr):                                           return expr

	def expr               (self, expr_eq):                                        return expr_eq

	def expr_eq_1          (self, expr_lambda1, EQ, expr_lambda2):                 return AST ('=', '=', expr_lambda1, expr_lambda2)
	def expr_eq_2          (self, expr_lambda):                                    return expr_lambda

	def expr_lambda_1      (self, expr_var, expr_commas, COLON, expr_eq):
		if expr_var.is_var_lambda:
			return _expr_lambda (expr_commas, expr_eq)
		else:
			raise SyntaxError ()

	def expr_lambda_2      (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr_eq):                    return _expr_lambda (expr_paren.strip (), expr_eq)
	def expr_mapsto_2      (self, expr_piece):                                     return expr_piece

	def expr_piece_1       (self, expr_ineq, IF, expr, ELSE, expr_lambda):
		return \
				AST ('piece', ((expr_ineq, expr),) + expr_lambda.piece) \
				if expr_lambda.is_piece else \
				AST ('piece', ((expr_ineq, expr), (expr_lambda, True)))

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
	def expr_func_10       (self, FUNC, expr_super, expr_neg_func):
		func = _FUNC_name (FUNC)

		return \
				AST ('^', _expr_func_func (FUNC, expr_neg_func), expr_super) \
				if expr_super.remove_curlys () != AST.NegOne or not AST ('func', func, ()).is_trigh_func_noninv else \
				_expr_func_func (f'a{func}', expr_neg_func)

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

	def expr_cases_1       (self, BEG_CASES, expr_casess, END_CASES):              return AST ('piece', expr_casess) # translate this on the fly?
	def expr_cases_2       (self, expr_mat):                                       return expr_mat
	def expr_casess_1      (self, expr_casessp, DBLSLASH):                         return expr_casessp
	def expr_casess_2      (self, expr_casessp):                                   return expr_casessp
	def expr_casessp_1     (self, expr_casessp, DBLSLASH, expr_casessc):           return expr_casessp + (expr_casessc,)
	def expr_casessp_2     (self, expr_casessc):                                   return (expr_casessc,)
	def expr_casessc_1     (self, expr1, AMP, expr2):                              return (expr1, expr2)
	def expr_casessc_2     (self, expr, AMP):                                      return (expr, True)

	def expr_mat_1         (self, LEFT, BRACKL, BEG_MAT, expr_mat_rows, END_MAT, RIGHT, BRACKR):  return _expr_mat (expr_mat_rows) # translate these on the fly?
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

	def expr_num           (self, NUM):                                            return AST ('#', NUM.text) if NUM.grp [0] or NUM.grp [2] else AST ('#', NUM.grp [1])
	def expr_var           (self, VAR):
		var = \
				'partial' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_')) \
				if VAR.grp [0] else \
				'd' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_')) \
				if VAR.grp [1] else \
				self._VAR_TEX_XLAT [VAR.grp [3]] \
				if VAR.grp [3] in self._VAR_TEX_XLAT else \
				AST.Var.ANY2PY.get (VAR.grp [3].replace (' ', ''), VAR.grp [3].replace ('\\_', '_'))

		return AST ('@', var + '_prime' * len (VAR.grp [4]))

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
		'CARET1'             : 'CARET',
		'SUB1'               : 'SUB',
		'FRAC2'              : 'FRAC',
		'FRAC1'              : 'FRAC',
		'expr_super'         : 'CARET',
		'caret_or_doublestar': 'CARET',
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
