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
			b'eJztXWuP3LaS/TMLxAOoAfEpyd8cx8k11o9c2wn2YmAYjuNcBJvYWdvZvYtg//tW1SlKlFqalnq6Z3pmhOG0KDZbrCpWHZLFh+6df/Vv7z/8/FXx1cPnT54/o+uTR9++osv3D148evaEIo+/e/b8xaM3D3948eQfdPvtiwcP9WL0aun69eNnz5+mq0kR+ebR' \
			b'd28ePnj56KXGnz54pbGvu+iPXfR7RF8+efDyb1/T0/+diWgjkiy08F0befr42Q9cwMtXL/jzh6/p89HT71/94+UjftizH5i2Hx/wl4+fvfqO2Xz8VHLK599fcK4nwv5z/vbbH549TM//+sELKev506cPkmBepC9fJOIkIgW8ePzd3/hxj/5OHw+efk+f33z9' \
			b'RAjn1GffqAg49nUX/bGLqggePXn5SFOSAPlBr6SUh0QGZ3r64PuXr55zSa+E90f/8fBJ+prr4ZvHPz7+hh/z8JvnIlf8/PsnP+jzQOHDB0pneu7zJNLHz4QR+grsPfyBcz7+lj6kXBK26VUMZ3r39tP7L28+fnrz80+/ff7y9hMlvf/XH5/efP7zj/ftzYf3' \
			b'/3zzy58f3nVf/kTR399+efPu428a+/Txf7rYZ3ny5/efP79rY3+0sfSYtz910S9f2tJ+efvuS4r/IU9Fco+A31P0t1/b6K8fvvwzxX//87c3v/7+R7r9+df/TtH/7pj80D3m519/+SXFv7z/9HvGeoq++/PTb/+bP58i6fanT2/f/ef7luy3P//cFve+pfqn' \
			b'tx/aZBJUm/yvjy1FIqD2iy79p18/fMz4fP9frVSo4FZYv75/9769oYr90JX2x+cvH9Nd++u21I+/ffzQ3fz++9vezeevXhfn9zY+Fr45KyQSSo64ij/qwtszvaU7iTWcrfCm2PizXgLu6vQ7+kGTkjgquTZBUmJxzxacbgr6OT04pTonaXXhYkrbVBwxNT4C' \
			b'/ciWZ3mSLfMkjvIPAz6C0h+IhihZIj5CQyWh4JQUyzyJoxwzxT0mlAlzZymlye9MqRFO45jFRyR+DYTUJoU8iaMca1gcpkriqM5Sqqa1CRtrJObxEblICKpNsnkSRznm6FGUl2rRK3/MDupC6oW/PMtuUzxLN7hshGQr/86nr7m25bmajkKIXk1EJiN8pmqP' \
			b'TZuqabFLaPoJGyuPt1SgFX2wFT4CCdSCpyxJVKJN5SjFWCNIz+krPDZwhHny+AjKKTMloqEK4OpiIUMglBCzmwoXTuDfkUxsI9XoC7YXr/aB9I0P20ndrSu3ckhSdssW57aTwnZSdmu3b3s/2DjUW6n6yXoBkzGlRFmErJ9RSw+tjaTk7nbjYHv0MBK7pbpm' \
			b'lSXDgkwor1VzHM8h8FPPzEh13M+4cVIPbMykBK3mUh4YclArY8MjLSBuMmOjL9v0LsUhxXcpHimhSwlIiSllY6CgJT5CR2ObVOVJHOVYjQ+S49lZF+UYa0vZ/YTItGKE3uMLpc+z4uJZZAGSoxKcTbgCoikNKe2tF+H6ZG5EnZRbQwkiMRAKXyWzyZM1YQME' \
			b'dA4fGxUPRx0opW+YbrBGdxFtCQNCndUuGycUhfUsVa1JfFHiPd/ZDd+Gsn0qgT2wiYq1oY1FjQE6OWJTBJhCqiS5STXuCe63SsHoi4bL4qNr9bh9A2sGH5IAgiUXCC7Tl2d6S3fpi7MzanvPRRGp6oh8PIW4J/TgJrBheTTEFUNabYuaQLgs6Z+bHJJZyfdU' \
			b'eWWgf7EcatSoEaNmoXJF5Yllli1zSnHSCeK0YtCm1pCEStZPNVT7oqanx6Kuirou6oYBmqqDFMtwxdCvyQxI70m1ua5Ij4goCqZoSCCRNcNTe98UTSiaWBjD/2Rl/Bh6jmGFp+wcM2yWwRLSFg0FX1ShqGJRVUVVF1VT1GVRE2/cpDIWCRxRI0qNZhTLjzU1' \
			b'GkVVFhVxyAKgYsqaTYxMisvl+4J/bl8X90puss7veTRd3uNCX5Lc75Gg5VuSNieTxOXbUr6l5BrJDV/WGjlQjTSQeUBVkAgh7FrqgvFXqqZ2yCaSpfQa2S2qxKPCTKopkf3ZakRHqjKRkZhRvYr5mGJuld6rfge9RlX0IBWQiwnSGRGKyqIVQc75GM9gmMiI' \
			b'Ri20uYKyFJ8r4HOlVg62beLaCkWHL916lG7tkZ6v9WnRsDiDi03tixRPxlRQUQXpzGo7e9uOC9qUQ5EM2gkmCRrUrMB1NOFT4y3SN9w6s6Qdc0SZWO/Zxkgiq3D3F25chXs84VarcI8n3HoV7rEavFrHURbjI6Ptnk8jIvRp1hbvSF311LUz6Ko2qIXGqPgb' \
			b'SQbVROGVkbZViXnFHbcr71QEaahYrfp3PP3zDYStfhCTrpVetftrGnWq6DAroI4CBiJBfS1NypUGfsCSRi63UlcbHfhVsN4KPaySf1V2KtFqwp2y46pS2UCHKihHXapfzqhmpauae4T7LkJ1osjXsCRZlCzLqmjqmyoTYg+KEuNt4wuAEVHXsenZwe1hswLu' \
			b'VaK04CXn7ubypU7zshroJZziqNXQOg+1dcD9PaOGblbf+TEHQSRYizknu84iHU6sJEmLObtVrAd0o9YsTpmdo+sqv+UuD7vq4yHlycKya+t0PH0VQ5cFOKuUj9cHiKt4jwoSq3iPuSzBoFPAwqLIKsm9vXZ1EiRQl+VE11Wce9p9EHkeeYw9svKMqpIqwurC' \
			b'FSahlX2SeifjO+1NPOe1PNwhXuUylEtc5TIqF/hJDr8Wy8JgnTx/FbeK29lVHNkcplclAdbDaawTHzo3Bkd5mmWXBuhuC+2cV9ndeSnwCkPu0tVBu3jaXzA2Ta62OqOrQWUJjPjhdblrDY9mXeGS+orSwbiTMj3n5Sx3lXlZwSMa0Mjo9i7xfs4Lae4Yz7xk' \
			b'SAeHOqc3ufHltW6TKXiRDdz1Ii5e0MFSu8UycjrqElkN5jsr4OfWSriyyRfDXKEBm7S5QaCcV1JYrKSwUoVG3SrRwgUr5DWdGwtuATiz4BwYuLRWX8F810vUnl1Ec3qzlzMY6PiN58JftUHqJpGmuvHiu9fogCSGG6/QvKwKxlndAl7UMRjrm89LVWpza24+' \
			b'L0yWxWooi0VQcjFpcQ4fA8DtK2fxcqE212lHzJ3BEewwwls3NRyplSZqHXq5kLxejF5RIb5GfbAgnc6iOPHJ6xckSTe2izSgkk1/F6aNI8nshnTqLnQj+wmdHUlm9xF+hP6ezO2suzovNcMjkozrtOPl5sdhVlsjo2YkmcchCnMuObKsOrB4zLVi3KVrw/pV' \
			b'ny+19Q2ITXw5OEqdOkrdyE4s40eSxbmmyQ7JDu4Up+4Ud6s3wJyzq8jdZleR+IjcnZ+VYOeXVR+Ugw/KwQfFsknjcJPdRZu6wttHIrH3RFoMTErICJ6vDbrWER2sCLuMWqJ2oFIfjojXzrRP0yXo+Hl0/Dw6fl47fD719Py6HHk5UqIm2pZcu9XdxJP2V4PI' \
			b'+VbjHXHlR7pAFfSO+PQwC59cs15ds/7GD3yNGhMpoVpeSP07WF6A5QVYHi4emSt8S/IJkE9YOy6X6fpRbJXgZdz4FopID1D1jFDPCPWkC8lHTTgiZ6U5q7s1oXjOYqkglkpQDe6QtOnP8Je9KTQWUg1x1vhdnbLWd1B2zV3jmdi4YzyLbje6y73Ube6l9AzK' \
			b'4rwsrJzOxj48PqGtUcjkhwmYMmFA4YrLVhSWGVo+DdhkWxIygnLRcjsgKM/MZqJr5VbLyEW22YuZVi0PsmxIPNAkOF5BykegcX+dzyvlDjufcsrnnvKhp0SC4bUDfOQDn7zJx27yvmCuCz5TkM/647P4+Ow/3srP+/h5szvvD+fN4bwznGuRz+njQ/r44AQ+' \
			b'NYEPC+CDAlh+LDtWCT71hyuF6ebxNp8Iwl1LPnSBFznwLoKST2wnGfJAggcR7I4n3iwvqGPZsmS5aePlibwnkXiyvqR60ZOrC5y9y+c9NwUfv81HgPPZzTUfa1zKRyw2fDY6H+he8ZHh/M9nAfMp9nwSPMVrPnFYjriWo9ALOUG64SfzU+WYb/ngM4DleHI5' \
			b'kpx/IUcOyw0VQRW5Ie42JI1NLSeF0yMqPoSd+NzwSc/8BD45G0foUxoXzGchK9kkn00VtQA5Mp6poV7nho9YJulvKiaTjGjDZ0kzVXzAMB+STNW5qaUsPnFYzmGmn/IR+ZWcgSxnKsvx6ThDuZDDzYUbJoL+Scc2NZ+QzeSnY+45j1DIjPKTuWgWJ38pOThL' \
			b'wydC8xnqfOUimXuq4E1gCaSD00s5iV0O7MaJ4tTD2fAh9TULTeRK2SompXzN3U+2vZ7dma7DMmV9bPkwwNi3Qbu/GeYIVvUh8CLD9DON86oNs9rTOMMCAw0srjC0ycBJs+0ytJYZtm0zHMU6A0gkVkL7d6GVhrl2evU2Wl3CTOuwwFSLv/x9BuFwn2G4MnSp' \
			b'/k/6mOdcdXVmt2jwMQrJRzAyfEGj3Q5fnB+udFpgxiGzZLOrX+K2rLrUQdmgh9F5D3F4iPZmcEyKyWAgDqDAZHCQZomzmWOBB6sQ4RUmokJFPYCLOoOJqLDAcMDiDRkcUDqfdDIbFigfD0N5peEseHAZRNhpmBCINh1UcEULXFA+Pr2Bj27oQQcLUxrjIsVK' \
			b'GcsyXMillAvJswZmcB6WWNkLjB0ma9TFDBQ8OH0ResiPmXu+5giCkVP3v4UoA6q2AzPB8J49RPjafvZWWQpIiAOUagEjCCD63hNNEoIee8NYhWujpJe45rgF+StcyQt3jKCSFqGYlCQ+A5l6DLBfeiZG6UlEDFOaeRyqEu/AKvykHpTaw67g7nPbQFV+Xyqf' \
			b'jOE+wycpN10tA5lrgazMsAwdEHvC+JWB1yzkSk6AOei1ItcIcrEgxSRFS3HDvZ3U0dFODqe7lKMNAlgmB6wOr8xivFK4GqJVVtwWUpkdATCVbqydzkiSrhI2DUY10DgFJ/CrvAosKSopKCkmDSDJTECS0qWQpDKdBUldZc3HIxViUB4m0Ai5WjRSMOpYH0Oi' \
			b'bQDy2z2p24c+K/JcAnnY8wWD09gY7FjAju0FgR2bwY7tYGepC0RGR14uPdjJi9uCHbsjCOy0N/aCjKk/NPSkiJ5ZYI6KRxllZbTAHAvMscAcO8AcO4E5SpRijgp0DuZkNTUfc1SCQXmYwBzkSphjgTldeTMxJ6yYs47VduIOMwWj09gY7kTgTuwFwZ2Y4U7s' \
			b'cCcuxZ0I3IkD3MmL28KduCMI7rQ31k5nTLgTW9wB0aVco8+yGuWUNTICeOAxEhJLlWEGPHECeJQqBR6V6Bzg6UhZADwqwqA8TACPMqPAEwE8GesLh11xRaAVgXYiUI23yNoixcYQqAYC1b2wwYqIDoHqDoHqpQhUA4HqAQLlxW0hUL0jCAK1N9ZOZ0wIVHcI' \
			b'VCsC1UCgNqtRThvcRmSNEEVVqgwzBKonEEipUgRSic5BoI6UBQikIgzKwwQCKU+KQDUQKGN9IQJVKwKtCLQTgZoCkFCk2BgCNUCgphcEgZoMgZoOgZqlCNQAgZoBAuXFbSFQsyMIArU31k5nTAjUdAiURl6Yy+6yGuW0qfEdskYlsVQZZgjUTCCQUqUIpBKd' \
			b'g0AdKQsQSOkLysMEAiFXQqAGCJSxvhCB6ovn0E4Zh9wKRVcNRVYWSm3kmYhxUUbQyPYBycIHjXxtYECymQ/adj5ou9QHbeGDtgMfdK+4ISANyBkNjEndjbXTGRWTbOeDFt74nFh4oLusRpltanyHrBHSqEoVZodJdsIJnagCJiWhzsCkjJT5mJSkGJSHcUzS' \
			b'XIpJFk7onPWFmNSsmLRi0nxMcoWACdZ66Lo8ix6SXDJMcsAk1wuCSS7DpG4en6PLMAnT+HYwi98rbguT3O4gmNTeWDudMWFSN2UvbLGZOmBSm9Uos4xJmK63mK23mKy3g7l63I9gklKlmKRCnYNJHSkLMEmlGJSHCUxSHVBMwix9zvpCTDLlCkorKM0HJc/6' \
			b'IIaosVIWogko+T4oeYCS7wUBJZ+Bku9AyS8FJQ9QGixO7BW3BUp+dxBQam+snc6YQMl3oKTriEQYeVajzDIoeYCSByh5gJIfgJKfACWlSkFJhToHlDpSFoCSSjEoDxOghFwJlLDUMWd9KSiZdQXkik57oFNkfRCL1BgXhQXTcinlArURjMIMG3K3QTAqm2Gz' \
			b'3QybXTrDZjHDZgczbL3itjAq7g6CUfm9tdN5E0x182xW59ks5tm6rEb5ZZjCPJvFPJvFPJsdzLPZiXm2RJXClMp1Dkx1pCyAKRVkUB4mYEqZUZjCPFvO+lKYWhdqrzC1B0yxDmChdopRUXylipQLUnnHXikw5bBQG7nbwDDlsoXakgsw5Zau05bfobwcpnrF' \
			b'DWFqQA5XM58tNiAyNP17a0d+qN8pTkkUOCX8GXwbfZbVKMNNje+QNUIiVRJrh1NuYj12ogo4lQQ7A6cyUubjVJJkUB7GcUpzKU7JD+oe60txyq04teLUHjhlWAfEIjXGOAWvuINXnC+MUwY4Bd84crdBcCrzjbvON+6W+sYdfONu4BvvFbeFU2Z3EJjK762d' \
			b'zptgqnOPO3WPO7jHu6xG+WWYgnvcwT3u4B53A/e4m3CPJ6oUplSuc2CqI2UBTKkgg/IwAVOqBQpTcI/nrC+FqZHV2itMrTC1E6YsK4BYpMYYpixgygKmLGDKAqawntvZXhCYytZzu249t1u6ntthPbcbrOfuFbcFU3Z3EJjK7+0FeRNMdau6hT0DcUSfZTXK' \
			b'L8MUlnU7LOt2WNbtBsu63cSy7kSVwpTKdQ5MZZU3H6ZUkEF5mIAp5EowhWXdOetLYWpkgfcKUytM7YQpx7UvFqmxEleGKczn8YVhygGmMKuH3G0QmMpm9Vw3q+eWzuo5zOq5waxer7gtmHK7g8BUfm/tdN4EU93EntOJPYeJvS6rUX4ZpjCx5zCx5zCx5wYT' \
			b'e25iYi9RpTClcp0DUx0pC2BKBRmUhwmYUmVQmMLEXs76UpgaWQW+wtQKUzthKnK9i0VqrJQ35whMwYfu4EN38KE7+NCRuw0CU5kP3XU+dLfUh+7gQ3cDH3qvuC2YiruDwFR+b+103gRTnQ/dqQ/dwYfeZTXKL8MUfOgOPnQHH7ob+NDdhA89UaUwpXKdA1Md' \
			b'KQtgSgUZlIcJmFJmFKbgQ89ZXwpT1egZATcOqbYOVTv4wQErYE1M+jWsEHJ4QCzSDZfWYN6vwbxfg3m/BvN+WFWO3G2Qeb9sVbntVpXbpavKLVaV2+GqctCg5W1N/DW7Q6Vzfznd1k5mlyMFdE60W2JudYm5xRLzLrdRtpsa3yFrVHJLFW42/TexxDwRptN/' \
			b'Kt45038dKQum/5S+oDyMQ5fmStN/WGKes74UuuoVulbougx0cU3Dc0VkphsqzcN55eG88nBeeTivPJxXyN0Ghi6fOa9857zyS51XHs4rP3Be9YobIteAnNHADwtN/zl2OrsgVyXS8Z0Ly6sLy8OF1eU2yjUprIcLy8OF5eHC8gMXlp9wYSXCgFxJujOQKyNl' \
			b'PnIlcQblYRy5NJcil4cLK2d9KXL1VqLbG4tcBxwectPsVuiav3mPhSDGyaeklbgpkRgNLkhlkcKhZeDQwk/bIHv5ModWftzcUodWOm1u4NDqFbe1l8/tDrKdL7+3djpv2tHXObSMOrSMbPjFffTZT4zyzWoLx5aBY8vAsWUGji0z4dhK1OnOPpXvDPDKSFmw' \
			b's08FGpSHcfDSXGlnHxxbOesLwcuOrFifs7k4XDdg3aRznTitugRMXRFE8bnF3H135S6vVsOVLg4cjY3sNXYYFSJHG3AeZq2/V29WNzJ0S0eG6UBdNxwaSiV2/9surWZHEH9We2PtdMb22AN0rKSU9sQn1yg6KR0Ap1LRqVR4KhWfSgWo4XqriYEhCBBlL7tT' \
			b'EJKkZyAVo4FbNjwU0VgUeuG6K1CRfFusV0wA5YGXqxVfH7NIcPdlUF3yNQhGrQvY1wHhPgPCiqtVhjwa49FghdFghdFghdFghdFghdFg1QsyGqyy0WDVjQarpaPBCqPBajAazIvbGg3OCDIUzO+tnc6reCVRHQdWOg6sMA5ssxrll8eBFcaBFcaBFcaB1WAc' \
			b'WE2MA5UqHQeqXOeMAztSFowDVZBBeZgYByJXGgdWGAdmrC/tSl3/Avaq97aSFaxuEljVhZzFb4sUY7CqAVY1wKoGWNUAqxpgVfeCgFWdgVXdgVW9FKxqjP8s1rGLabLMsDU2Ecpfc84t2Kp3B4Gt/N7a6bwJtuoOtmqFrRqw1WY1ynmD24isEaKpSpVvBlv1' \
			b'BGwpVQpbKuE5sNWRsgC28IsqKA8TsKU8KWzVgK2M9aWwta5nXwFrH8BquELFIjXGgIVpQo9pQo9pQo9pQo8BIXK3QQArGwz6bjDolw4GPaYJ/WAs2CtuC6aa3UFgKr+3djpvgqluftDrUNBjKNhlNcpvU+M7ZI1KaKlSzWBqYhiYqFKYUrnOgamOlAUwpfQF' \
			b'5WECppArwRTmB3PWl8LUup59hak9YCrIO0HZIlOM3+mHbTcBHquAbTcB224Ctt0gdxsYpkK27SZ0227C0m03AdtuwmDbTa+4rVdCmd2BYap3b+10XoWp0G27CbrtJmDbTZfVKL+kowHbbgK23QRsuwmDbTdhYttNogowleQ6A6YyUubDVBJkUB7GYUpzKUwF' \
			b'bLvJWV8KU+t69hsLUzqddL1wZbk+xTI1xnCFFQwBKxgCVjAErGAIWMEQbC8IXGUrGEK3giEsXcEQsIIhDFYw9Irbgiu7Owhc5ff2grwJrrq1C0HXLgSsXeiyGuWX4QprFwLWLgSsXQiDtQthYu1CokrhSuU6B66yyksszgUtFWdQTiZASx+poAWHei6ApaB1' \
			b'nWecX/msX4Kkprj4hZjHhpylMHMwiAmFvgwzxUZm7zjdBc3RBoGV7DWYIXsT5tJXYfIPGtGFHS/D3KJiSFRoshtrpzM2Ldv9t2fOfX0mhDWCFFq0IoWKag5StLlnwgMyX/SSzPQ8xYYAbGjLmfveFXudh46vkHDVkFAVATNlKTYGCZgdQ442CCRks2Ohmx0L' \
			b'S2fHAmbHQrULEnYFgYT2xtrpjAkSqgEkVHMhYWLCKxWtkKCimgMJLWkzIQGZL4QEfZ5CAia6unJmQ8LIKeArJNxaSGh4IlFsQ2NjkACXLnK0QSAhc+mGzqUblrp0A1y6odkFCc2OsOndWDudMUFCM4CEZi4kTHhpU9EKCSqqOZDQkjYTEpD5QkjQ5ykkwDvb' \
			b'lTMbEkYO4b4ySLgTSwdvuvuVawnu1xQbgZEIlytytIFhJGYu19i5XONSl2uEyzUOXK694oaQMiBnOzCkdDfWTmdUSImm2H4lZIS7NYlHGSVljPC1RvhaI3ytceBrjRO+1kQUwCYJdAbYdEQv8LUmCQblYRx0NJeCToSvNStvJui4PZcsr6BzZ0DHci2JxWls' \
			b'DHTgOI22FwR0Msdp7ByncanjNMJxGgeO015xW6BjdwQBnfbGXpAxgY4dAx04TZN4lFEGHXhMIzymER7TOPCYxgmPaSJKQUcFOgd0spqaDzoqwaA8TIAOciXQga80K28u6IysQV5BZwWdDHRcEbGHK8XGQAebtpCjDQI62aat2G3aiks3bUXsh4iDTVu94rZA' \
			b'x+0IAjrtjbXTGRPouDHQwUatJB5llEEHu7QidmlF7NKKg11acWKXViJKQUcFOgd0WqKXgI5KMCgPE6CDXAl0sEsrK28u6IysKF5BZwWdDHR8EfEGkRQbAx28OwQ52iCgk707JHbvDolL3x0S8e6QOHh3SK+4LdDxO4KATntj7XTGBDp+DHTw6pAkHmWUQQfv' \
			b'DYl4b0jEe0Pi4L0hceK9IYkoBR0V6BzQ6UhZADoqwaA8TIAOciXQwXtDctZngs7IeuAVdFbQyUCn4QoRi9PYGOjANYwcbRDQyVzDsXMNx6Wu4QjXcBy4hnvFbYFOsyMI6LQ31k5nTKDTjIEOfMVJPMpoU+OLiItSWKoIM9CZcCAnohR0VKBzQKclegnoKH1B' \
			b'eZgAHeRKoANHclbeXNDxxTkhSUFwUJBlE/g0AjwhYU+Z4CcI/NRpE7pAjuLNHLAZm1BiXBEIYWtq0SFHhjkTQYyU9Dsq3xABHQIEoAApoAmMDI0iAv2GpAZkGG4Qn4sI1Uwk2DE5JOCu1i+Wn1s7T2/IqTd0ld3OpJNQ/U2dRjmmjB0AVL4FgY3FnPFGj1rd' \
			b'sA0n20+Gv9+G74ungzaO/7HBaGM7Z0jfVGdN52w8Wx+fE8ZNfO75MGWAfVbMKdtFVFvlfys2uxFOOqudvStb5D3PUje6ZGzSSOm/6xiwgfbsks0vjJifuUILLNUIiaSbaIcX26Chihu3w7k2uPH+QiP0aRXX6Rmid60xGl30eUMNcqcxWvnpqEEuMsY4Yoxu' \
			b'uTHO7H5faI9Ur0N7DAeySXcCdhkX2CWls7Rb+3RyoMX12OnStZb72KrfslWW66HsleV+GjbrltgsBkemtd00QNqy4Wppf5ZH1P1zlQ7VpsKAGz4npploV+cudjrNPq5pmgV27PZsY+fbrQ+d7fpstfRVtbPJbkXWVTXR1vq5q56vqb1ln8Uc+43L7DeOt7vF' \
			b'X6Rp96nuZTRaj1hveXXd4c7d1R+Wuj27xPYku8VWm4GjdYuljk+0VxxGLVZOaa337Rhzf+aEO8f1QTrHzXU6itphau6APux4lY+PJHIM0WOIoNMw1Mv6kA7Xtl7X2BUWm/0ffhzLbgJ0ZUrBxpMx3XGztVI1c023+Is05j4Rxu0racH5Dfb0nlozmlun2dtC' \
			b'W8us3Mkb5gG9u6fYVvYMjufm9vTsFn9RlzbA5MwJmBypgZx0zCdb3yrrYz9SdamO7I1qF7fGmUFmsjdcgbfSFpU7f8nOK/WATsAIfcE+ExLv9dni2KHYh7RHkmIZVruURUmy0GTDq1mu0T7j8ZtLzs1PiAexVLfIUsujdVLL8vCm2lugtE/TWR5wCqY+mSZU' \
			b'TjO/XnuVnzfHsFacKH+ZJpXPbjqoPyio4R7KZP0ikzXHM9nMXEt/Aj3dw5nraqppxNk3U5bvaXR8D2ylh7XQsMhC7dVYaFgt9E5YqFstdLeFxkUW6q7GQuNqoXfCQv1qobsttDoBF9L1m+MxJzbvhnPo0KbG242u2017CdMq/iJFvM94IbMl9QlYGVWM+mqv' \
			b'3NzSTrWr8NHeTfMzsrGf3bPX0+a5K/TJXq7Ba67SFCf2n043fvVg/+gpNoJz94vOXeHj1SLNTbNKbOnt/89uJCVzb5fn6c5qLtjmOX/zmBUyvApiq/2M1HxWspkzXOnyntVkb7fJ1lv/C0y2vuMmK2N8r4K4yGRNcV5vHfVQiXFWYpZuyyDFGtXARs87GFP6' \
			b'SpRclHeosDbybmOvijc4TkB0rW5Ux5gtvEVqQq86nUq+hpH99OOVxLnxvlE7It3ac6eE2N1PXMCmhEoeKOTNngKcOtCBBSk2cEBJMpVib533JmWL+4t3SoFVzG5fMccJSd8caZcdwm1JPMHUkaTu95X6RFOcVQI3vksa3oUVNbvhnKzMNNo0x6hU5nbw32/L' \
			b'sprGlwvbrX0UYn6zM6k3OnwjkvuNSrhIkS7vLLmkM3K2bh1558S0h2Oe/i3pcEn6Qs/FARyG8/XyGE7ACXUd6RCF8j51SUV346q7x9ddgbZjet2uUHdxvlh5bbrr6vsbGWazG5urP9LViy5Xqy5fhS6bW6TLBvycni7X07p8oDmYY6jzNW7MbI/1q8WDxy6B' \
			b'PVRc1OhKJkrG/DhS+OXUHMdAVkftdiidF6u7lcUX9NXoJKRp7rNRU43SVeYiSR6jGn/YicdDK/2J7EreD9O5jq90cvAI0M6Hn1bXNOs+F+hJu0nyq3ZfsXbXt0C7a2Hj5LV71K1+hHUjB1Twk1iDdWlF54q+lnUeB1Z2PsnanMBCqiVKPzo5sir9FSi9vSVK' \
			b'b4WVG6X0g6mqYy4SXPVe9Z4V4NoX9h28d3Mqa2eXaL+/mdp/KkvO97eA6vZZgPB0E40grEZwPUZQ30IjuKktQTtveiX7JVY7IDvgVYontdfh0F2ik9pStMQYquI88GojrS5+yRK+qOkLfoUgpWNlkJFkPty05MxU+6/P6HpvI+8dxZu4+IjwyOf68/nA2Qmk' \
			b'xnp+jrw8w3QHfQc9+bfqHSjaNFzSxs59LJE/9icP0TeFjTwGB6X6kec5Xpbtsr/uBNTYpcrjfe/xceulYxeWxibI55rzYTdpP5O+cUvfePWaV6njjwzA62bj7t+P/MlrC/hIcvpe3h4QJCp7efGGAKE8XJJyPg10J/GEgTP/eK36IE3IjMvInHj32iSlLJiW' \
			b'WvrBBX+8un76W17HTlehudpJM7+ADo1G6C9J3PkSufYNche+Pi7qgfn6ijh5PRxJQV4Lx6+Eq0elkb/CrX01G7+WrX39WpW/cu01N6Njf4xWtbZ22//Tv1nyf/Evxp9b974f/EZqrr5CbWuKS/0Jvc1JaFrZ1zbeAnE0jePKusZQ5zfcZbrsI6UaSZpXp3fc' \
			b'6B4xgCGTM8RKUh9aPd3JamhVtIGpDEWecoDAI4HDPnFWQMXag2hqHWcqK0cuHXjcNP01+HIjCss70Y6otjTeOS3NlWFcLzCJ5TDxgIFHscd7+lZAVS/ss+9qH2cqcigOEtL4fzoLmAyrPp9zwm0OqOnDjJAGjelMpa6LA4bkzprOAoarVbXP2T95mwNqetZw' \
			b'LIR9BzMTOt7WQqvn7AreFdhxOCdf7zfqtN3+ht2t6QayaFatP2d//G0OcHvOGgzur/WpFudrf10cL6S5iQtzQS5jY8q7ZgE8F3WbA2p69yBTa/fSRpAqcp4xjFWIKS4OPP20M9Pup+i03cW5hhNwIsx1ZEu15IpbHVDTuwe2p2M2vji9ACmuI2eqnlDc6oCa' \
			b'jre6pg17nus4t8ZjcQuCJTnyCwans6DmZ8/QXj9S8hKjkwuQ4u7h+aGlmCa2RyVp50jTFVcW2Bi3U9kUJ34BqS6c070CwY60HtMC9sWcwKu4ZmbdI/SePloU1gbtHmmftKhjcfIBcjY3W851cfIBcp49br7xC494je3sgPW13f+iHy947vwyRnOgDt3dqcNQ' \
			b'3IqAeps9+L759RaLWxFQb7vXwd6aequKWxFQb7unvW9NvdXFrQioNxp6y3G0DYY7JCW91z457y/gWVFeiC/7T5Duqa+e1y+JltfaybtnPV6Rxy/halAKv0p+LLcpBv/Ibbdyc3XJL2wx/LclkIPfv9tukOBDY3XWml/ymavbRQpCFS/bK3jfT7b/p92TM7If' \
			b'R1cx8YsKB4fZMhE4FVaKlKJUD3lDEeubTibzO9Qstk7woorXZ/8P8iJg7Q==' 

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
		('CUP',          fr'\\cup(?!{_LETTERU})'),
		('OMINUS',       fr'\\ominus(?!{_LETTERU})'),
		('CAP',          fr'\\cap(?!{_LETTERU})'),
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
		('DBLBAR',        r'\|\|'),
		('DBLCARET',      r'\^\^'),
		('DBLAMP',        r'&&'),
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
		('CUP',          fr'\\cup'),
		('OMINUS',       fr'\\ominus'),
		('CAP',          fr'\\cap'),
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

	def expr_ineq_1        (self, expr_bor1, INEQ, expr_bor2):                     return AST ('=', AST.Eq.ANY2PY.get (INEQ.text.replace (' ', ''), INEQ.text.replace (' ', '')), expr_bor1, expr_bor2)
	def expr_ineq_2        (self, expr_bor):                                       return expr_bor

	def expr_bor_1         (self, expr_bor, DBLBAR, expr_bxor):                    return AST.flatcat ('||', expr_bor, expr_bxor)
	def expr_bor_2         (self, expr_bor, CUP, expr_bxor):                       return AST.flatcat ('||', expr_bor, expr_bxor)
	def expr_bor_3         (self, expr_bxor):                                      return expr_bxor

	def expr_bxor_1        (self, expr_bxor, DBLCARET, expr_band):                 return AST.flatcat ('^^', expr_bxor, expr_band)
	def expr_bxor_2        (self, expr_bxor, OMINUS, expr_band):                   return AST.flatcat ('^^', expr_bxor, expr_band)
	def expr_bxor_3        (self, expr_band):                                      return expr_band

	def expr_band_1        (self, expr_band, DBLAMP, expr_add):                    return AST.flatcat ('&&', expr_band, expr_add)
	def expr_band_2        (self, expr_band, CAP, expr_add):                       return AST.flatcat ('&&', expr_band, expr_add)
	def expr_band_3        (self, expr_add):                                       return expr_add

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
