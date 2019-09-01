# Builds expression tree from text, nodes are nested AST tuples.

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

def _ast_from_tok_digit_or_var (tok, i = 0, noerr = False):
	return AST ('#', tok.grp [i]) if tok.grp [i] else \
			AST ('@', AST.Var.ANY2PY.get (tok.grp [i + 2].replace (' ', ''), tok.grp [i + 1]) if tok.grp [i + 2] else tok.grp [i + 1])

def _ast_func_tuple_args (ast):
	ast = ast.strip (1)

	return ast.comma if ast.is_comma else (ast,)

def _ast_func_reorder (ast):
	wrap2 = None

	if ast.is_fact:
		ast2, wrap2 = ast.fact, lambda a: AST ('!', a)
	elif ast.is_pow:
		ast2, wrap2 = ast.base, lambda a: AST ('^', a, ast.exp)
	elif ast.is_attr:
		ast2, wrap2 = ast.obj, lambda a: AST ('.', a, *ast [2:])

	if wrap2:
		ast3, wrap3 = _ast_func_reorder (ast2)

		if ast3.is_paren or ast3.is_brack:
			return ast3, lambda a: wrap2 (wrap3 (a))

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

	elif lhs.is_ass:
		if lhs.rhs.is_mul and lhs.rhs.mul.len == 2 and lhs.rhs.mul [0].is_var_lambda and lhs.rhs.mul [1].is_var:
			return AST ('=', '=', lhs.lhs, ('lamb', rhs.stop, (lhs.rhs.mul [1], rhs.start)))

	elif lhs.is_comma:
		for i in range (lhs.comma.len - 1, -1, -1):
			if lhs.comma [i].is_mul:
				if lhs.comma [i].mul.len == 2 and lhs.comma [i].mul [0].is_var_lambda and lhs.comma [i].mul [1].is_var:
					ast = AST ('lamb', rhs.stop, (lhs.comma [i].mul [1], *lhs.comma [i + 1:], rhs.start))

					return AST (',', lhs.comma [:i] + (ast,)) if i else ast

			elif lhs.comma [i].is_ass:
				if lhs.comma [i].rhs.is_mul and lhs.comma [i].rhs.mul.len == 2 and lhs.comma [i].rhs.mul [0].is_var_lambda and lhs.comma [i].rhs.mul [1].is_var:
					ast = AST ('=', '=', lhs.comma [i].lhs, ('lamb', rhs.stop, (lhs.comma [i].rhs.mul [1], *lhs.comma [i + 1:], rhs.start)))

					return AST (',', lhs.comma [:i] + (ast,)) if i else ast

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

def _expr_mul_exp (lhs, rhs): # isolate explicit multiplication so it doesn't trigger imp mul grammar rewriting
	if lhs.is_curly:
		lhs = lhs.curly

	return AST ('{', AST.flatcat ('*', lhs, rhs))

def _expr_neg (expr):
	if expr.is_mul:
		return AST ('*', (expr.mul [0].neg (stack = True),) + expr.mul [1:])
	else:
		return expr.neg (stack = True)

def _expr_mul_imp (lhs, rhs, user_funcs = {}): # rewrite certain cases of adjacent terms not handled by grammar
	ast         = None
	arg, wrap   = _ast_func_reorder (rhs)
	last, wrapl = lhs, lambda ast: ast

	if last.is_mul:
		last, wrapl = last.mul [-1], lambda ast, last=last: AST ('*', last.mul [:-1] + (ast,))

	if last.is_pow:
		last, wrapl = last.exp, lambda ast, last=last, wrapl=wrapl: wrapl (AST ('^', last.base, ast))

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

	elif last.is_var: # user_func *imp* () -> user_func (), var (tuple) -> func ()
		if last.var in user_funcs or arg.strip_paren ().is_comma:
			if arg.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg)))
			else:
				ast = wrap (AST ('func', last.var, (arg,)))

	if arg.is_brack: # x * [y] -> x [y]
		if not arg.brack:
			raise SyntaxError ('missing index')

		ast = wrap (AST ('idx', last, arg.brack))

	if ast:
		return wrapl (ast)

	return AST.flatcat ('*', lhs, rhs)

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast.numer.is_diff_or_part_solo:
			p = 1
			v = ast.numer

		elif ast.numer.is_pow and ast.numer.base.is_diff_or_part_solo and ast.numer.exp.no_curlys.is_pos_int_num:
			p = ast.numer.exp.no_curlys.as_int
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
			elif n.is_pow and ast_dv_check (n.base) and n.exp.no_curlys.is_pos_int_num:
				dec = n.exp.no_curlys.as_int
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
	elif expr_super.no_curlys != AST.NegOne or not AST ('func', func, ()).is_trigh_func_noninv:
		return AST ('^', _expr_func_func (FUNC, expr_neg_func), expr_super)
	else:
		return _expr_func_func (f'a{func}', expr_neg_func)

def _expr_mat (mat_rows):
	if not mat_rows:
		return AST.MatEmpty
	elif len (mat_rows [0]) > 1:
		return AST ('mat', mat_rows)
	else:
		return AST ('vec', tuple (c [0] for c in mat_rows))

def _expr_vec (ast):
	e = ast.comma if ast.is_comma else (ast,)

	if all (c.is_brack for c in e):
		if len (e) == 1 or len (set (len (c.brack) for c in e)) == 1:
			return AST ('mat', tuple (c.brack for c in e))
		elif e [-1].brack.len < e [0].brack.len:
			return AST ('mat', tuple (c.brack for c in e [:-1]) + (e [-1].brack + (AST.VarNull,) * (e [0].brack.len - e [-1].brack.len),))

	return AST ('vec', e)

def _expr_curly (ast):
	e   = ast.comma if ast.is_comma else (ast,)
	kvs = []

	for kv in e:
		if not kv.is_slice or kv.step is not None or kv.start is False or kv.stop is False:
			if ast.is_comma:
				return AST ('set', ast.comma)
			else:
				return AST ('{', ast)

		kvs.append ((kv.start, kv.stop))

	return AST ('dict', tuple (kvs))

def _expr_num (NUM):
	num = NUM.grp [1] or (NUM.grp [0] if NUM.text [0] != '.' else f'0{NUM.grp [0]}')

	if not NUM.grp [2]:
		return AST ('#', num)

	g2  = NUM.grp [2].replace ('{', '').replace ('}', '')

	if g2 [1] in {'-', '+'}:
		return AST ('#', f'{num}{g2.lower ()}')
	else:
		return AST ('#', f'{num}{g2 [0].lower ()}+{g2 [1:]}')

def _expr_var (VAR):
	if VAR.grp [0]:
		var = 'partial' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_'))
	elif VAR.grp [1]:
		var = 'd' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_'))
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

	_USER_FUNCS = set () # set or dict of names of user functions to map to AST ('func', ...)

	def set_user_funcs (self, user_funcs):
		self._USER_FUNCS = user_funcs

	_PARSER_TABLES = \
			b'eJztXWuP3LaS/TMLxAOoAfEp0d9sx8k11o9c2wn2wjAMx3Eugk2crO3c3UWw/31ZdYoU9Rqp2z2PnhGG0+JLIlmsOqSqSOrOq6/+7f2Hn76qvnrw7PGzp/H6+OE3L+Plu3vPHz59HD2Pvn367PnDNw++f/74HzH4zfN7D+Si5Krj9f6jp8+epKtKHk55+O2b' \
			b'B/dePHwh/if3Xorvfuf9ofN+B++TR0+/p1tePL734m/3Yyn/TpXJHo7mOlEoe168fE6/39+Pvw+ffPfyHy8e0sMePX35bbw8/Z6q+MM9yvP40RPOyb9/f065HnPzn1HOb75/+iA99/6951zGsydP7iXCPE+Jz1Ol2MNPfv7o27/R4x7+Pf7ce/Jd/P36/mOu' \
			b'MMU+/VpIQL77nfeHziskePj4xUOJSQSkB73kUh7EajCd7n334uUzKuklt/3hfzx4nJKpH75+9MOjr+kxD75+9pIpxLc/esrV++4xE/nRN6Aa3cAP68hLmd+9/fj+85vfP7756cdfP31++zFGvf+fPz6++fTnH+9z4MP7f775+c8P77rEH6P3t7ef37z7/Vfx' \
			b'ffz9vzvfJ37yp/efPr3Lvj+yLz3m7Y+d9/PnXNrPb999Tv4/+KmI7lXgt+T99Zfs/VdX/Q9dhl8+fP5n8n9+/zHH//bnr29++e2PFHz358df/zcFfvrlX8n748e37/7z/ecu5eefc3nv3xUUys99+7ksInpyEdT63OKffspF/PLh96K67/8rNzmWnSnxy/t3' \
			b'73Mg9tqHrsA/Pn3+PYXy3bnU33/9/UMX+O23t73Ap69eV6/u7KypbDir2ONq8hhLP66y+kyCMcQ+T9kqq6qdPetFIOTSffEGn6LIy7l2eIap7ujKtNVOVSZEz1mKjf8U11bp3hhuyKM0flyIGVBwilK+jCIv3ajx46T+VB3DWVR1hwqmgsxZigllSNXioTjy' \
			b'BaquytVtzlKsxOWInVbsiy2h2yPVLNrGxaHtTAdKPCuCyV/EK1x23BzN/9wLZwjvUDWJRyGxfIlEJsX1DlJvb3KsxPkuW92P2Gk8PrZPMzViBv5xsTM1aFpEURd0seSNPuIEX9kYxmMdeahNCj9OWkpt5hsiQWMepjsIEiN8EWhwoQgqiHolcLfY2AXxF/kk' \
			b'fkccOIzqgqYe5eCoIkgcPhGlx1FFUI+DvaidAXPVws7EQCCcqtlL2aLsxX+UrnOGFN0Fd5pJopuY0FRaV0x8X3nNNCHaSY9O52BxDyszxj7uZ9zp9oy7+M6uqVzm3JiH45UTqSGhjP0TH1EIT0zM8V2MQYztYixiXBfjEONTzE4BICx+XFfHHNWUUeSlBmj8' \
			b'RDqenXVeyhNbpIqnkJdbZBUSpDcJAjWjpnaVZuFuGNcSTqDSMQ4xOWiZuDaJW6wdP6UFE/iYFvGzSWJTRkvEDghlavzsEkhHr2HZiJxzhxoUziTkITLxWfG/611bJ0ZhPpOubVO7YuQd28kNBV2dnxq5F9gUm4fms8+LD1BIHp08jCmxWORRkRSqKQGUAlxw' \
			b'pB7/FKNMECQ0LX54gEFNaCAxuK9JiWcSjKGUcHYWx7pXNaFoHJJio6N0xvGF2D3SJPZXTFJVLDRS31eNqRpbhRihq2CqEP2uCr4KkfdCHCSJ452uvK28Yy4PRNQInZGJI5cpYonY0KpVVaurNj7NVU18bFM1bdWEqq2rNqY2laIbFI+o1DGxQpYaR0My4xoN' \
			b'hoF6qrVVG4uq4y11LK+O2Bf5QkW89FFOm8q3VaBwrFTEyrpqVNVEAazpP8p5dJawOgpIFIgIPFHyPXEGybiPLYy3B+I725KsKyqmotFQv67u1DQcvbpjLA9LkXx8iU+ONKVBm1MjJSk6UpNTFae+YpA+Y3iNl43aK6gdQE8LMkfygJANJgVKyN5YZAuKoxvk' \
			b'1hrURl/QQ/newNEb6x/QGcLdJmwUPJCCiVHBocHj0ghrWiZsSQU0ftzm1Nrc1LKFU21Dk2IVnEYVXH0JZSmU5QGWHq1WIrxWWq0YJY9fupbSVbig58tQoNCsFuDTamlWy50L5oxMmXkR/Jd57chM1hO1UsIutKfj0MZEiA2smipWt/IbAkwigIbIt2miYDYo' \
			b'PYiQcQ7AlFQk3SSJ1E7KQQ0niVQbB84RrtkIdxjh2o1whxEubIQ7ZLBoawwWjUw01DZaHEhJpWTmbTFLs3g3JGUevUDqlIqJasuXmzZFM+3GPYdxjxU5lPeXOmkUWrlCrcP14Wt67cFcz2O8ral/CgJl0tyOV4Q7HtQKiUjyHupBvAbRjRKNjhbSpqvMlx3e' \
			b'HR3k1DlQNoZq4o1IyLZqw+kRJzYMvOKam9Mi9LdD//q6JwQ3oYEeQ4lnFkUrynadYosgXaEdMCGrTdGPNuuqBPygkiXzhcxRtkHmwFlyJJqGLUFv1oF1JCMqwc6ykWyl/ikQqdiiEq8bbfrvqWbjo7W0ioTQG9AfxmYOqKU3Ch46VDYb6Q4kXfRvpDvMeKsx' \
			b'dAYeJTYaTdHIyPQiAOIiHeJlI9SEHFqm1AW/0E2shHnNK9e0mOWpCrdUIfWKFiLE9t++Ztvb2Wy8JB5dr6kE8lqeEN8Warb69rSWlvJwF4uCf36Z4WtZk1jRehi+BRo1qKslRyuqbGgPxQDFUERrGlCQEpOCTtrypHZTSvRuvOqILVvQHDdQhTQtLsyUbDHE' \
			b'6z53F9m7qNduZB+J9qyVsY0pOdBhetBotACtTlTm6+XVmVXhYgTRMIJoGEE0d20tM04H7sBiodBN3jGxwhQe06vhRH6bbWEhokijw9B3qhYHZueTrr+7bAHzELC2PWHC3WllGbzzJ8y+ZNuEELan3AovL08unHQrlAyT+pRbETDZsTKse5nzJDMabbKKAyJd' \
			b'4khJlzhIGkzgzBlejw1mXdvytENsSSCxAYljAtMWkQGUps1/og8y0AcZmtlYiY6EMlMTMtw8XFGv7EQ0vddJrEGswfTbYPrNEyr63dakz+qioKzzm1pzltNNAgqTXs+0vJbRW8aGEudaHJTbOGuOsxqAZwMQawLwEADIr+3mxq5HtdzIG6mMMK2MbwwYt1XD' \
			b'zooVLfoNA/2GgX6DqJLeCXURcibN2sb7p+ntHRMNqHrobZKuLWaBjmlNbxcGyw4NFudBoNK8z8q8zyZtG+YxFvMYi3mMxQTGyszFbgtlBqAFEqfBUOZ/nUZSUiyT8IaiV2yPnZi6xtZZcLoFp9ukybOiybOn+76lFEQjFiVi5NKsCGLkIEYOYkSX4JA30sWB' \
			b'Lg50cduMYHaFht6oM6vJNWCgOFYKW3mwlQdbxUusvoicR85Gcja3xWD1igjSgCAN4w+GU1miHZvVDGwjRJ4WhGxxX5uytreKauEWtVbdntYyJwfZZ1TLRqOaR+y6ehXL5KMLSEVExxcEAU6qNqqkqTCqFYxrWDqXCibiMeUA2Gg1NY3bRbRyRCVQBjidSUuQ' \
			b'3FA16VgaaoBUnM26rI2M8bQ9kQ4OoPkwHR5EE2I6cogOIaITiGJlFNmfaTsjHZVD5+TQRg0iPp0pQmd90FkcRGXaQUXbp2inEW3RoV0stIWF9n7QOR00iNCONTpih87VISs3KUhp1zhtgKa9vNQTNGDQgTB0pAltGAlEqNhzZLOMHKJpkh7bo0kdS2oSPv6K' \
			b'es5FotNRiTgNkc45owPT6DCtamfphDFd7WLBu0D/TbWLld7RmWqeztujg8bodDjHh3bt4mi2i5XZtXReFp1oxieR0VUOjWvpVLSaUms+LIzPzKMHKHpijAocoCLp2K9Y8V0kxC5QXeiGho8ulIPAYj0od7y2Us8oKjvfyDMdl0W1opx0ahkd+BfLCXQwH5+8' \
			b'VvHxi3RiXOymXUMl8eFd8Uonj8Wrt3IiI13jfXHU3rV0D7WYjoCM+WJX7GJX7BpujcGRZXT0l6Obav6J2VuKidnpZD06LJIOsAuGT7DbeY/jBQPRC6fP8bF7cWqxc1QMHVFIj6+JNDGhUa9pUkey0pOTYpoxKy11EpimLzN6f7EpQYkRCbOjWN15QXIrhemi' \
			b'BEkfKEz1HgLliChuKEOOo9bJkcuS5May5I4lTQ51ilzh8t+5UuVWytVFyZQ/WKwav160qr/sXT4I9C4hoW/vRsT5P56xvSIStIWcYTDFWFlM1DFiDpZ/YGVIt9Z7pfzVQxEcj+8DccwThCyONGrj3QIKL55TYK6Bt98kqX4grbqT2GyEKwxzLMFGpNiJJDeQ' \
			b'ZjperyfRoZDk5hwJjum0/zZJMm1Zpf2qkxLtIdW0m5m2Lq+RbFp8kKW7OUfCYx9GenRSrkXSCVKpr/VA6olofFZqJb5YAjF3bBxfFF+0XCDvtHitzlKP+7JLEACh7jBAblrCgDAHA0F1bggJgyqMHTel7h5A4cgS8jQBDfYCNzi9Ro2dK2+KxOV8fDNBCVen' \
			b'xgWPKzCFCSpQYsMshAjlBEgkNIQTqWwUv8AVqVeiipLKoeIz0CJlCrhw/lDQewA06i4heuyuu9xxkavvEthFDo1XQ6hjMurUBfBgdNfXGGxKpClhRq1Gmg1lplCGiMVCRlMZBGhSkSYUxWRCUhO4qJ7L4KL64CKpS+AyO8folTEEF7XgCFm6gAq5rr7i52uE' \
			b'ynk+Y4tibEm3EW8BWBSARQFYFIBFDYBFrQMWIaYAC0JDYJFo00pFVgOLkMtLd0wDizQUwKIALAW1JoFljCd2PIs5XTDZkOQLkETzEei4kG8ORpCaYET3XIYRPYARpC7CiJ6DkbKMIYzoBccwkgM8YUVdfWruBIZoYIjcQ1ylgSEaGKKBIRoYovsYotdhiFBS' \
			b'MAShEYYgmjBE74UhQisvfTGNIUIfwRANDOlItRJD3C3EkO29Zw5HPD51oivxzeEIUhOO+J7LOOIHOILURRzxczhSljHEEb/gGEdygBhA6pqbm3CE02vUw7nyplpuCUhDVu5XAInvA4lfByRCSgEShEZAgmjTSkVWA4kQSxowAyRCIAESDyApmr3nW47fEGVD' \
			b'lIwoLb5qBDNUO48oSE2I0vZcRpR2gChIXUSUdg5RyjKGiNIuOEaUHCAGkLr61NyMKK0gSgtE6W4i1mqBKC0QpQWitECUto8o7TpEEVIKoiA0QhREm1SR1YgixPLSGdOIIgQSRGmBKEWz90SUZkOUDVEyogR8b4w4hH1ziILUhCih5zKihAGiIHURUcIcopRl' \
			b'DBElLDhGlBwo6upTczOiBEGUAETpbiLWCkAUGHW4IjUuuKFElLAOUYSUgigIjRAF0aaViqxGFCGWl86YRhRpjyBKAKIUzd4TUdrz7T/XGVfqDVouClooEgpZ8cUSNMw+Wo0ARvIIwCCUXQIYPdDJSuoSwOg5nWyvjAHADKow6QhjuoDYOjtrj+50slqsPRoa' \
			b'2eImoimUshpKWQ2lrIZSVveVsnqdUjZRExgjoSHGSDSdRbCXUjbRy0t/TGJMIhAwRkMpWzZ7T4wJG8ZsGDPGGPpIIWQNPsIYA4wxY4xBnoQxfZcxxgwwBqmLGGPmMKYsY4gxo1qMHWNMDhCvS3V9anfGGCMYY4Ax3U1EUwOMMcAYA4wxwBjTxxizDmOEmoIx' \
			b'CI0wBtGEMWYvjBF6eemPaYwRAgnGGGBM0ew9MUbVG8hsIDMGGVvhM76V+AIuTuMyABkkJpCxPZdBxg5ABqmLIGPnQKYsYwgydtkxyOQA8bpU16d2Z5CxAjIWINPdRDS1ABkLkLEAGQuQsX2QsetARqgpIIPQCGQQTSBj9wIZoZeX/pgGGSGQgIwFyBTN3hdk' \
			b'1LZabkObc9CmoR5nqYMv8HlZjDYNow1/ylsugjnImTCn6bmMOYPV55K6iDnNHOaUZQwxZ4VjzCnDxP1SY58IkGGnEdhpADvdTbVHvoA0qU6NC24oYadZBztCUIEdhEawg2iCnWYv2JE6eumSadgRGgnsNICdotn7ws62SHeDnXNgh7oY2hrxxRIMtDUG2hqD' \
			b'eY7ppjqSU2AHoewS7JiBzkZSl2DHzOlsemUMYGdQBe68MKqYq/thFXKVfaJAwh0jehsDvU1xU6Sugd7GQG9joLcx0NuYvt7GrNPbJIoCdyQ0xB2JJvnbS2+TaOalTyZxJ9EIuGOgtymbvS/umA13Ntw5B3c0dTFLHXyEOxq4AzMU70WTi+AO0hLu6J7LuDNY' \
			b'eCepi7gzt/CuV8YQd/SyY9gpwwQ7UmOfCJBhRwvsYPFdcVPtkS8gDVl9jQtuKGFn3fq7RFCBHYRGsINoEr+91t8lknnpkmnYERoJ7GD9XdnsfWFnYjXvBjsb7GTYMdS/LHXwEexAcWygOKaLlovADnIm2Om7DDsD9bGkLsLOnPq4V8YQdka1GDuGnTJMsCM1' \
			b'9okAGXZEg2ygQS5uItiBBtlAg2ygQTbQIJu+Btms0yAnggrsIDSCHUST+O2lQU4k89Il07AjNBLYgQa5bPa+sDOxAHiDnQ12MuxY6lyWOvgCLk7jovii5SKwgywJdmzPZdgZKJQldRF25hTKvTKGsGOXHcNOGVYh19gnAmTYEZ2ygU65uIlgBzplA52ygU7Z' \
			b'QKds+jpls06nnAgqsIPQCHYQTeK3l045kcxLl0zDjtBIYAc65bLZ+8LO7Crh8piDa4g212H7UnsknLlMjKFFGLT8xS0pkz11O+tS4SuW97X9ExYkQ9Ih+57LOuTBLgRiTL1iG4Ke3YbA3df9jxTJfsGxFjkHiOWlwmkrAvYicOXSliYtmxFSmdjUpGRXk5Jt' \
			b'TUr2NSnZ2DRYiNPfkMDPn9ElC2FFl4zQ3EEOeq8dCUx6w8ecnbcURwglqmRatkOlxjxQKnfU6+FOJNddLI+08eoZZybWDm/Tm216k6c3TWVguxJf4LOveHoD25WB7cp0tivJmaY3Tc/l6c3AdiWpi9ObOdtVr4zh9GaF4+lNGabpjdTYJwLk6Y3YrgxsV8VN' \
			b'tUe+gDSpTo0LbiinN+tsV4mgMr1BaDS9QTSJ3162q0QyL10yPb0RGsn0Brarstn7Tm/ayaMeTg551Lngs/78hw1/5vCnpu7mMyBMJQGCoBoQVAOCakBQ3UEQciYIqnsuQ1A9gCCkLkJQPXsehCsKGWJQvewaUe6UdVUh15qPZGUkqjskkgkQU6IsnpGoBhLV' \
			b'QKIaSFQDieo+EtXrkEjoKkiE0AiJEE3iWO+FRFI5Lz0zjUTIlJCoBhIVzd4XicKGRBsSrUAi6keYtRocTwzLloVly+INzMKyZTvLluQUJEIou4REdmDZktQlJLJzlq1eGQMgGlRh0jVQ9/QeExkjVdpzBiUhAJEV+5aFfau4L1LZwr5lYd+ysG9Z2Lds375l' \
			b'19m3ElkBRBIaApFER2m0e9m3EuG8dMwkEEkmASKLN6+y2XsCke4tVdYnC0QHvIzR0Gk3KFq/xdNUCjOBeKGSYe1SsHYpWLsUrF2qs3bJbWnHZ9/lHZ8Da5ekLu74nLN29coY7vgc1WLseNNnGSaukBr7RIO871OsXYpOW25QK+fKm4n/YPVSsHopWL0UrF6q' \
			b'b/VS66xeibAAIwmN9n8imvZ/7mX1SqTz0jXT+z+FVgAjBatX2ex9wWhb0rwh0HmToaayUAuJj2ZCUAtZqIUs1EK2UwtJzjQTanouz4QGaiFJXZwJzamFemUMZ0IrHE+DyrAKucY+ESDPgUQtZKEWKm6qPfIFpEl1alxwQzkHWqcWSgSVORBCozkQomkOtJda' \
			b'KJHMS5dMz4GERjIHglqobPa+sHP1S5rP/brABj7XAnzaiiVYV+Ij8GkBPi3ApwX4tB34IGcCn7bnMvi0A/BB6vIBoYOVzWz+4TNLraAQP4iBqh3DULvsGIbKMMGQ1N0nUmQYagWGWsBQdxPBUAsYagFDLWCoBQy1fRhq18GQkFZgCKERDCHapIqshiHc4L10' \
			b'zjQMCY0EhlrAUNHsfWFoW+G8AdB5ABQqiyN2xIcvyjAABQBQAACFDoCQMwFQ6LkMQGEAQEhdnP2EudlPWcYQdsKyY9gpw6qrsU8EyLATBHYCYKe7iWAnAHYCYCcAdgJgJ/RhJ6yDHSGowA5CI9hBtGmlIqthR0jmpUumYUfaI7ATADtFs/eFnSs8r/jiFvkI' \
			b'qCx+BeWCQWNvwDgWWBCtYcES38x5XJKavopS91z+RMrAZCWpSwDh5kxWo8+k1Atu1wuokOvnUxP7X1GBWWq39BkVt878lGgEmZfQUOYlOsqBWyvucss5X1FJrYesO5idCkKsPE1Yb6uJt5nFeWChqZtYkuCLJThYmAQyHCxMrrMwSVoCDt1zGTgGFiZJXQSO' \
			b'OQtTr4whiOhlxzhShglKpMY+ESBBiRPbkoNtqbgpEtfBtuRgW3KwLTnYllzftuTW2ZYSQQVlEBqhDKIJZfayLSWSeemSabQRGgnawLZUNnvfmcXEauINdq4X7IjF4mrhh7+wydIHH8EPrEoOViUHq5LrrEqSM8FP32X4GViVJHURfuasSr0yhvAzqsXYMfyU' \
			b'YRVyjX0iQIYfsSo5WJOKmwh+YE1ysCY5WJMcrEmub01y66xJiaACPwiN4AfRBD9iTUoNWwVCQjgvHTMNQvJAASHYlMrG7wtCV3hM8fZ6c2GvN7ZyWAwivrnXG6QmmLA9l2FisOdJUhdhYm7P0wga7IJjXMgBAgWpn09N7L/e2JWvN+u2MSUaieQjNJJ8RJPk' \
			b'27XijlvOe72R1ousY/tSQYi1rzcT5wZvIn7yIu7JIMb8D9+ciCM1ibjvuSzig/1Gkroo4nPbjUYi7hcci3gOkIhL/XIT+yLuV4q4XyfiQiMRcYRGIo5oEnG/VsRxy3kiLq0XEfcQ8Y4Qa0V84tjeyxLx096VeON0FS11CMsMfHOwgNQEC23PZVgYmF4ldREW' \
			b'2rkXhLKMIUS0C44hIgcIIqSuPjV3/FE1B2NruofeDGBpdbC0OlhaHSytrm9pdessrYmSAh4IjcAD0SZVZLViQmjlpS+mQUToIyACS2tBqpUgYiaO5d1A5FaCSKDeYKmCbw5EkJpAJPRcBpGB+VRSF0FkznzaK2MIImHBMYjkgOrq6lNzJ0AEptN0D4EI7KYO' \
			b'Ew8Hu6mD3dT17aZund00UVJABKERiCDatFKR1SAitPLSF9MgIu0REIHdtCDVWhCZWKO6gchtBBHqB5hYxTcDIpIqIIJQdglE/MDEKqlLIOLnTKy9MgYgMqjC2BGIdAEVcl19au4YRDxsrumeSEnOFpCABqbqIHcBIn6dITZREiAioSGISHSUMFRkLYikynnp' \
			b'i0kQSfQBiHgYZAtSrQWRiRWnG4jcShBR1A8sVfDNgQhSE4ionssgogYggtRFEFFzIFKWMQQRteAYRHKAQETq6lNzJ0BEAUTkHgIRnKbicZiKx1kqHkepDHQhHFwBIkJJARGERiCCaAIRtReICK289MU0iEhDBUQUQKQj1VoQmVgvuoHIrQQRX3mRKvjmQASp' \
			b'CUR8z2UQGahKJXURROZUpb0yhiDiFxyDSA4QiEhdc3MnQAS603RPLXcEJKCBvsYFuUsQWadQTZQUEEFoBCKIJhDZ6zSmRCtpwAyICH0ERKBYLUi1FkRs9SpiQhVfWytfRYGsAgOJS1hSHvwGIAFylLAxiRnn2EkiQYAETRb9UuzXWD1oiyhtOaT9iU0h3n7F' \
			b'YWwi3nOHr9EWijXivGjxsIUIN0ORpd1RZEqnUYZmv5HdwNO7RsyZoemE2PfPWEsinGR2dJbaoriuM2vsNCn+oFXYFR897QvdGkPFjs+Fpj11MXNTLEkIHoLm7aywJTGbPeyMqbhKtOiUs/PMFbvgskyRQPXkiMTFTYiLuniJaURoYnWvr9wsyYyekZu1MrOL' \
			b'NT9PaIy/PoLDB4NCeIjI112AFoWHempSgPYRHj8hPGZ/4Zmbpa6Rn3YsP3V7BBmylyhHar0c1bTMsu7kSbV8aOMVyJVZMYc8RLbcpGwRIb9cvojMlypj7WoZw0uBz7KWXgxGMtfsPb+rZ14OD5W5UuDotSe2/rCVLlc957N7yF174Bi2Vs5M98LG/ksYx4Zy' \
			b'xkT1g7VpXJkrH88Uk3BJ3qjn1submh7Xqr8i89yN3clvU+2EtNUXPz30U9KmDpshmiueJfqLnSVSH16bSaKfFTCq5kHzRJoeXPFckfroi+eK4Qr0EnmWWKgtj/q6RdBkCQ/olVFfsmB9qcriWEPXJb56QcKK/6O/huGtlmYGjrHrkkVtSsxo8rFa1Kq/IhPc' \
			b'jbWg4St2wKtTUwRe1TBVSpM/WKKyJDX19ROk4yn/rm4sKgWEjCoHKf6qv5q7EepYRNRViwhxW+QyPnDwpKQl3hv0F03srve4M/ua5NmMuKMeOjnZkZq7L5rMxRKvWmhsFesYwhWIjj+O+NDZobEtt1iMiEnZKL+jlQCXLU7+aKMR0ZhubI4gWGYvwVIXI1vt' \
			b'0QSrt1Jjj3GJV2ocKlzmmoxP+HLUVUkXpXONjiRb+M7VAeMVnZfwRcqHGmJ2HAGzewmYvhgBK6XrCt6Rvki6brtkDaRKjdY9Xsok8AuF6ogC5fYSKHPxAmU2gTptgboSjcT1ESi/l0DZixcouwnUaQuUud0C1Vy1suK01Hq3TA9xHNGgvQBXZB7aQ+sdmehu' \
			b'FGLWe7dXLRWxKdDiXZ54DPaDHEV9d8vERfFJWqS5u8QxxRxfXfclA0q4eNGZ3Y81PbjUYbDL6goHmbW7p9auXeAlr4oXR157KcL5oP3/tYMQ5+1tfLpie9L6DU5rd2FoqgfxBDd1NDx5fTfCEI1O7hIWLmwidqIiFkb/60Us3HwRcyJiYUHEVPWqrYZ7jFsW' \
			b'ppbFyIwEiKUHktHbgMv8ex7fNsKPAx5UsUqvGlVN7m9l/qmFb7TwyyyvZD5J3d7b9Nku9Af1BRF5SNjG0YAfa3YYqQAoAiUa2GH0gbSbkWGmITP48YhIlWRZSsRkrQJn8wdSdo5thcLmUArPEPlkCK064BoRO8HPRRDcHkjwuVGzoz8PlHsMkvv20erBb27Q' \
			b'S29k/gL6kxvb/+8NTkUfi5Zur4Fob07YY4CZYxh5E4rV7Y8fboqDjqcw+CIF2qrTIS5j/fXs2/8c383NnJg1jvyK/+WasBUnK1yU1muGTSfmPCbcjfNO5lm/8ezxeZZ67LK0UkdlWTqspr2GDKvdXf7Quo2MS/upXR2vlhm42Rj4Ahg4nCoDszspBm77DHwB' \
			b'lobbxcPEs1dhHrgVcwdi2HBCDHvVuw0T00LTS6qoFQxsrw0DU1UOw+FLMfqieudysOZFHzFp0vqrIgxTXwcbr2wFju0S7r5I2+/NY/A5pqbOvWrD7XGR+QrWM+yBzrHmr/hs49gHUDhpjtb8EToV0Dd0tErNaq9Iq1eqpdjYp6/P4vXOjs//xombdFRKQ+cR' \
			b'xeqUe8aVolsUndYV25nPPGnldIX+JvDQUEk7vfaxsXJTf/wQORF0/Bg5lFNNPM+Q+coUf92u9aaL5cfb8vG6GZ0pem5pJEAEG7T6Ja+swAmbcuIlfeO8wl+ISCHLCbt/O/HHJy/R6S0xnffhyirEoMVMVXPN3RfWnKR+sfLx9pV/ZNUb/HE1/X7VnDljda6m' \
			b'tOioq23Mes4f2SHnU8kSGK9c56ZXZz9TbT62Sz5wkvXBi4fF5pNi+ZhYPiCWTwtq5DDYWCYfAkvqxhjHB79OtDsf2NoWh7A2VT5olQS+O1z1NY1x+Itc1Pb+OIIWIxWunfwbZJq6cXj7KOfgOUzu9hJZJFRf9Mf1DZfMHqrPIvzx1YtiE5oIXZrzoQgQen/p' \
			b'I7l7VH2J/ESZLtChQapsEB+Ic2y2q68B5zVVdvhKcRlzBGeP+7hphw7TazhQzoFewoNZPhTKdrxI5FxyNAVezmTbqdhgcwDNNBN8qfjz1xfHnf7KGJTPKO85fD17HH8sR294F/Z0dOGq+e9KTkUP7cGvrjqWS+/E5+ZCi93tYtq2ukEOPehXzb/2ZFvpoHXM' \
			b'O0XoUGUX39jK4MEuaXcWMg50MUyj5lZxOSnobo5DD7bXkctJDXrFDtQJt4u/2+oGOSgH62vJ36G6agfqTL3y3Vz+JqPKzXHoQX2B/J20hpPE9yv4nLjlYhx1/kRsZIGZO0Ct2/UqSebDm+PQg3YvrehxWX5M/3Nob6tFR/bHNflWut7jJp8NEt6uV1Oynt8c' \
			b'hx70N6UHY8kqFr2yJ311ck7RtvtwXhb06H62wKuDNVp8cr0c6LfuNfYa0M9V18yBfpdtbLwMWzRtPV7tsDSq+9/r5tmnrH/iZA4sTVn3CntafUOr1k7PoT/UTewP7PA8MYf+WPcKfGL9YasTdOgPcxP7w1Un6NAf9KHihhYliby4FJb+oo9L0ppeWtNI09UW' \
			b'ykH6AF7ZaZGQlKGVo3QNDixs5aHtZOZQFQ4ZwygjdQutzOBzEAf/AfM7+r5KXn5K+57FAEUflSgZ6FxGCA0vXvX9JdB5ufJ4qbKuMQLTKfyD7diKl0jy0hwqkotK/AYNsJblC3TSuK6pgVpFWr0++3/PMYNR'

	_PARSER_TOP             = 'expr_commas'
	# _PARSER_CONFLICT_REDUCE = {'BAR'}

	_UPARTIAL = '\u2202' # \partial
	_USUM     = '\u2211' # \sum
	_UINTG    = '\u222b' # \int
	_UXSECT   = '\u2229' # &
	_UUNION   = '\u222a' # |
	_USYMDIFF = '\u2296' # ^^

	_LETTER   = fr'[a-zA-Z]'
	_LETTERU  = fr'[a-zA-Z_]'

	_VARTEX   = '(?:' + '|'.join (reversed (sorted (x.replace ('\\', '\\\\').replace ('+', '\\+').replace ('*', '\\*').replace ('^', '\\^') for x in AST.Var.TEX2PY))) + ')'
	_VARTEX1  = fr'(?:(\d)|({_LETTER})|(\\partial|\\infty))'
	_VARPY    = fr'(?:{_LETTER}(?:\w|\\_)*)'
	_VARUNI   = fr'(?:{"|".join (AST.Var.UNI2PY)})'
	_VAR      = fr'(?:{_VARPY}|{_VARTEX}(?!{_LETTERU})|{_VARUNI})'

	_STR      = r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY)))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LETTERU})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\$?(?:{_LETTER}|\\_)(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
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
		('EMPTYSET',     fr'\\emptyset(?!{_LETTERU})'),
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
		('FRAC',          r'\\frac(?!{_LETTERU})'),
		('BINOM2',       fr'\\binom\s*{_VARTEX1}\s*{_VARTEX1}'),
		('BINOM1',       fr'\\binom\s*{_VARTEX1}'),
		('BINOM',         r'\\binom(?!{_LETTERU})'),
		('IF',            r'if(?!{_LETTERU})'),
		('ELSE',          r'else(?!{_LETTERU})'),
		('INEQ',         fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)(?!{_LETTERU})|{"|".join (AST.Eq.UNI2PY)}'),
		('EQ',            r'='),
		('NUM',           r'(?:(\d*\.\d+)|(\d+\.?))((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))('*)"),
		('ATTR',         fr'\.(?:({_LETTERU}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"({_STR})|\\text\s*{{\s*({_STR})\s*}}"),
		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
		('COLON',         r'{:}|:'),
		('CARET1',       fr'\^{_VARTEX1}'),
		('CARET',         r'\^'),
		('DBLSTAR',       r'\*\*'),
		('CURLYBARL',     r'{\|'),
		('CURLYL',        r'{'),
		('CURLYR',        r'}'),
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('BRACKL',        r'\['),
		('BRACKR',        r'\]'),
		('SLASHCURLYL',   r'\\{'),
		('SLASHCURLYR',   r'\\}'),
		('SLASHBRACKL',   r'\\\['),
		('BAR',           r'\|'),
		('PLUS',          r'\+'),
		('MINUS',         r'-'),
		('STAR',          r'\*'),
		('DIVIDE',        r'/'),
		('EXCL',          r'!'),
		('AMP',           r'&'),
		('DBLSLASH',      r'\\\\'),
		('COMMA',         r','),
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('ignore',        r'\\[,:;]|\\?\s+|\\text\s*{\s*[^}]*\s*}'),
	])

	_PYGREEK_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.GREEK))) + ')'
	_PYMULTI_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.PY2TEXMULTI))) + ')'
	_VARPY_QUICK   = fr'(?:{_PYGREEK_QUICK}|{_LETTER})'
	_VAR_QUICK     = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK   = OrderedDict ([ # quick input mode different tokens
		('FUNC',         fr'(@|\%|{_FUNCPY})(?!\w|\\_)|\\({_FUNCTEX})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
		('SQRT',          r'sqrt\b|\\sqrt'),
		('LOG',           r'log\b|\\log'),
		('LN',            r'ln\b|\\ln'),
		('LIM',          fr'\\lim'),
		('SUM',          fr'\\sum(?:\s*\\limits)?|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?|{_UINTG}'),
		('LEFT',         fr'\\left'),
		('RIGHT',        fr'\\right'),
		('CDOT',         fr'\\cdot'),
		('TO',           fr'\\to'),
		('MAPSTO',       fr'\\mapsto'),
		('EMPTYSET',     fr'\\emptyset'),
		('INEQ',         fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)|{"|".join (AST.Eq.UNI2PY)}'),
		('VAR',          fr"(?:(?:(\\partial\s?|partial|{_UPARTIAL})|(d(?!elta)))({_VAR_QUICK})|(None|True|False|{_PYMULTI_QUICK}|{_VAR_QUICK}))('*)"),
	])

	TOKENS_LONG    = OrderedDict () # initialized in __init__()

	# grammar definition and implementation

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

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr_colon):                 return _expr_mapsto (expr_paren.strip (), expr_colon)
	def expr_mapsto_2      (self, expr_piece):                                     return expr_piece

	def expr_piece_1       (self, expr_ineq, IF, expr_eq, ELSE, expr_mapsto):      return _expr_piece (expr_ineq, expr_eq, expr_mapsto)
	def expr_piece_2       (self, expr_ineq, IF, expr_eq):                         return AST ('piece', ((expr_ineq, expr_eq),))
	def expr_piece_3       (self, expr_ineq):                                      return expr_ineq

	def expr_ineq_2        (self, expr_add1, INEQ, expr_add2):                     return AST ('=', AST.Eq.ANY2PY.get (INEQ.text.replace (' ', ''), INEQ.text.replace (' ', '')), expr_add1, expr_add2)
	def expr_ineq_3        (self, expr_add):                                       return expr_add

	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                  return AST.flatcat ('+', expr_add, _expr_neg (expr_mul_exp))
	def expr_add_3         (self, expr_mul_exp):                                   return expr_mul_exp

	def expr_mul_exp_1     (self, expr_mul_exp, CDOT, expr_neg):                   return _expr_mul_exp (expr_mul_exp, expr_neg)
	def expr_mul_exp_2     (self, expr_mul_exp, STAR, expr_neg):                   return _expr_mul_exp (expr_mul_exp, expr_neg)
	def expr_mul_exp_3     (self, expr_neg):                                       return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                return _expr_neg (expr_neg)
	def expr_neg_2         (self, expr_diff):                                      return expr_diff

	def expr_diff          (self, expr_div):                                       return _expr_diff (expr_div)

	def expr_div_1         (self, expr_div, DIVIDE, expr_mul_imp):                 return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2         (self, expr_div, DIVIDE, MINUS, expr_mul_imp):          return AST ('/', expr_div, _expr_neg (expr_mul_imp))
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
	def expr_abs_2         (self, CURLYBARL, expr_commas, BAR, CURLYR):            return AST ('|', expr_commas)
	def expr_abs_3         (self, expr_paren):                                     return expr_paren

	def expr_paren_1       (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):       return AST ('(', expr_commas)
	def expr_paren_2       (self, PARENL, expr_commas, PARENR):                    return AST ('(', expr_commas)
	def expr_paren_3       (self, IGNORE_CURLY, CURLYL, expr, CURLYR):             return AST ('{', expr)
	def expr_paren_4       (self, expr_frac):                                      return expr_frac

	def expr_frac_1        (self, FRAC, expr_binom1, expr_binom2):                 return AST ('/', expr_binom1.no_curlys, expr_binom2.no_curlys)
	def expr_frac_2        (self, FRAC1, expr_binom):                              return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_binom.no_curlys)
	def expr_frac_3        (self, FRAC2):                                          return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4        (self, expr_binom):                                     return expr_binom

	def expr_binom_1       (self, BINOM, expr_cases1, expr_cases2):                return AST ('func', 'binomial', (expr_cases1.no_curlys, expr_cases2.no_curlys))
	def expr_binom_2       (self, BINOM1, expr_cases):                             return AST ('func', 'binomial', (_ast_from_tok_digit_or_var (BINOM1), expr_cases.no_curlys))
	def expr_binom_3       (self, BINOM2):                                         return AST ('func', 'binomial', (_ast_from_tok_digit_or_var (BINOM2), _ast_from_tok_digit_or_var (BINOM2, 3)))
	def expr_binom_4       (self, expr_cases):                                     return expr_cases

	def expr_cases_1       (self, BEG_CASES, casess, END_CASES):                   return AST ('piece', casess)
	def expr_cases_2       (self, expr_mat):                                       return expr_mat
	def casess_1           (self, casessp, DBLSLASH):                              return casessp
	def casess_2           (self, casessp):                                        return casessp
	def casessp_1          (self, casessp, DBLSLASH, casessc):                     return casessp + (casessc,)
	def casessp_2          (self, casessc):                                        return (casessc,)
	def casessc_1          (self, expr1, AMP, expr2):                              return (expr1, expr2)
	def casessc_2          (self, expr, AMP):                                      return (expr, True)

	def expr_mat_1         (self, LEFT, BRACKL, BEG_MAT, mat_rows, END_MAT, RIGHT, BRACKR): return _expr_mat (mat_rows)
	def expr_mat_2         (self, BEG_MAT, mat_rows, END_MAT):                     return _expr_mat (mat_rows)
	def expr_mat_3         (self, BEG_BMAT, mat_rows, END_BMAT):                   return _expr_mat (mat_rows)
	def expr_mat_4         (self, BEG_VMAT, mat_rows, END_VMAT):                   return _expr_mat (mat_rows)
	def expr_mat_5         (self, BEG_PMAT, mat_rows, END_PMAT):                   return _expr_mat (mat_rows)
	def expr_mat_6         (self, expr_vec):                                       return expr_vec
	def mat_rows_1         (self, mat_row, DBLSLASH):                              return mat_row
	def mat_rows_2         (self, mat_row):                                        return mat_row
	def mat_rows_3         (self):                                                 return ()
	def mat_row_1          (self, mat_row, DBLSLASH, mat_col):                     return mat_row + (mat_col,)
	def mat_row_2          (self, mat_col):                                        return (mat_col,)
	def mat_col_1          (self, mat_col, AMP, expr):                             return mat_col + (expr,)
	def mat_col_2          (self, expr):                                           return (expr,)

	def expr_vec_1         (self, SLASHBRACKL, expr_commas, BRACKR):               return _expr_vec (expr_commas)
	def expr_vec_2         (self, expr_bracket):                                   return expr_bracket

	def expr_bracket_1     (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):       return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_2     (self, BRACKL, expr_commas, BRACKR):                    return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_3     (self, expr_curly):                                     return expr_curly

	def expr_curly_1       (self, LEFT, SLASHCURLYL, expr_commas, RIGHT, SLASHCURLYR): return _expr_curly (expr_commas)
	def expr_curly_2       (self, SLASHCURLYL, expr_commas, CURLYR):               return AST ('set', expr_commas.comma) if expr_commas.is_comma else AST ('set', (expr_commas,))
	def expr_curly_3       (self, CURLYL, expr_commas, CURLYR):                    return _expr_curly (expr_commas)
	def expr_curly_4       (self, expr_term):                                      return expr_term

	def expr_term_1        (self, expr_num):                                       return expr_num
	def expr_term_2        (self, expr_var):                                       return expr_var
	def expr_term_3        (self, STR):                                            return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_4        (self, SUB):                                            return AST ('@', '_') # for last expression variable
	def expr_term_5        (self, EMPTYSET):                                       return AST.SetEmpty

	def expr_num           (self, NUM):                                            return _expr_num (NUM)
	def expr_var           (self, VAR):                                            return _expr_var (VAR)

	def expr_sub_1         (self, SUB, expr_frac):                                 return expr_frac
	def expr_sub_2         (self, SUB1):                                           return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1       (self, DBLSTAR, expr_neg_func):                         return expr_neg_func
	def expr_super_3       (self, CARET, expr_frac):                               return expr_frac
	def expr_super_4       (self, CARET1):                                         return _ast_from_tok_digit_or_var (CARET1)

	def expr_neg_func_1    (self, MINUS, expr_neg_func):                           return _expr_neg (expr_neg_func)
	def expr_neg_func_2    (self, expr_func):                                      return expr_func

	def caret_or_dblstar_1 (self, DBLSTAR):                                        return '**'
	def caret_or_dblstar_2 (self, CARET):                                          return '^'

	#...............................................................................................
	# autocomplete means autocomplete AST tree so it can be rendered, not necessarily expression
	_AUTOCOMPLETE_SUBSTITUTE = {
		'CARET1'          : 'CARET',
		'SUB1'            : 'SUB',
		'FRAC2'           : 'FRAC',
		'FRAC1'           : 'FRAC',
		'expr_super'      : 'CARET',
		'caret_or_dblstar': 'CARET',
	}

	_AUTOCOMPLETE_CONTINUE = {
		'RIGHT'      : ' \\right',
		'COMMA'      : ',',
		'PARENL'     : '(',
		'PARENR'     : ')',
		'CURLYR'     : '}',
		'BRACKR'     : ']',
		'BAR'        : '|',
		'SLASHCURLYR': '\\}',
	}

	_AUTOCOMPLETE_COMMA_CLOSE = {
		'CURLYL'     : 'CURLYR',
		'PARENL'     : 'PARENR',
		'BRACKL'     : 'BRACKR',
		'SLASHCURLYL': 'CURLYR', # normal non-latex set closing, latex closing special cased
		'SLASHBRACKL': 'BRACKR',
	}

	def _insert_symbol (self, sym, tokinc = 0):
		tokidx       = self.tokidx
		self.tokidx += tokinc

		for sym in ((sym,) if isinstance (sym, str) else sym):
			if sym in self.TOKENS:
				self.tokens.insert (tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

				if self.autocompleting:
					if sym not in self._AUTOCOMPLETE_CONTINUE:
						self.autocompleting = False
					elif self.autocomplete and self.autocomplete [-1] in {'|', ' \\right'}:
						self.autocomplete [-1] = self.autocomplete [-1] + self._AUTOCOMPLETE_CONTINUE [sym]
					else:
						self.autocomplete.append (self._AUTOCOMPLETE_CONTINUE [sym])

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

		if self.tokens [self.tokidx - 1] == 'COMMA' and (self.stack [idx].sym not in {'CURLYL', 'PARENL'} or \
				not self.stack [-1].red.is_comma or self.stack [-1].red.comma.len > 1):
			self._mark_error ()

		if self.stack [idx - 1].sym == 'LEFT':
			return self._insert_symbol ('RIGHT')

		return self._insert_symbol (self._AUTOCOMPLETE_COMMA_CLOSE [self.stack [idx].sym])

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

		if pos and rule [1] [pos - 1] == 'expr_commas' and rule [0] != 'expr_abs':
			return self._parse_autocomplete_expr_commas (rule, pos)

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_intg':
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
				res = (res [0].no_curlys.flat (),) + res [1:] if isinstance (res [0], AST) else res

				print ('parse:', res, file = sys.stderr)

			if len (rated) > 32:
				print (f'... total {len (rated)}', file = sys.stderr)

			print (file = sys.stderr)

		res = next (iter (rated)) [-1]

		return (res [0].no_curlys.flat (),) + res [1:] if isinstance (res [0], AST) else res

class sparser: # for single script
	Parser = Parser

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
# 	p = Parser ()
# 	a = p.parse (r'\left\{1')
# 	# a = sym.ast2spt (a)
# 	print (a)
