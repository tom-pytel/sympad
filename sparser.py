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
			b'eJztXWuP3LaS/TMLZAZQA6JISuR8sx0n11g/cm0n2IVhGI7jXASb2Fnb2Qcu9r8vq06RotgttTTumZ6eEUyP+FaxWHVIFR999uqbf3n/4Zdvqm8ePHv87Gl4Pn743cvw+OHe84dPHwfPo++fPnv+8M2DH58//vcQ/O75vQfyUPJswvP+o6fPnsSnih5Oefj9' \
			b'mwf3Xjx8If4n916K737v/an3/gDvk0dPf6QiLx7fe/G3++Et/0rEJA+TQ54XL5/T3x/vE6lPX34fHk9/JEp+ukcJjx894WT++/fnVPNjbuUzyvndj0+pMfc564NnT57ciy1/Ht/xPL6VPM8fff83quLh38Ofe09+CH+/vf+YSaTYp99K68h3v/f+1HuldQ8f' \
			b'v3goMZE3VNFLEBIIYBbc++HFy2f0ppfcyIf/9uBxTCYWf/vop0ffUjUPvn32klnBxR89ZfJ+eMz8e/Qd2EMFuLJ3bz+9//Lm46c3v/z8++cvbz+FqPf/8+enN5//+vN9Cnx4/483v/714V2f+HPw/vH2y5t3H38X36eP/937PnPNn99//vwu+f5MvljN2597' \
			b'75cv6W2/vn33Jfr/5FoRPSDgj+j9/bfk/a+e/A99ht8+fPlH9H95/ynF//HX729+++PPGHz316ff/zcGfvntv6L3509v3/3H+y99yq+/pve9f5dxKNX79kv+iuBJr6DWpxb/8kt6xW8fPmbkvv/P1OTw7sSJ396/e58Codc+9C/88/OXjzGUSqe3fvz944c+' \
			b'8McfbweBz9+8rl6dbYyuTHtewdORRxv6YyvtzyUYQuxrKVulXbUx54MIhGwsFwq0MYq8nGuDOnR11lRaVRtVheJancdYiUsRGyZGNfhj25CKt8YoNYgiLxVs8McI8SFBa86iqrNAuNL0/zzG+DykavFQHPk80apcpNWex1iJSxGbRrEvNIOKB5YZSaPXoeHM' \
			b'BEo8z4LRn8UrPDbcnIb/cyvOEd6ANInHS8L7JRKZgoeIChSaGLFpUC4Q3nAzmxp/bKiyQT1ZFPG2jyVv8FH/BjZ01Qa9a8lDxCr8sfW5BAPfyRc4FfIwQ9HSENFmgQ4PiqAXEbs75neQqVDQIJ/Eb0yzHZUF3XYONwyGN5l6O6rZjuqDut4ODgpsNKSmFjml' \
			b'Bku31OylbEGjmkbe3qQMMboPbhpmSWjaWWOr0G0sW21lPfMkZFBg/UgOUuKgKfMyqjLjpnHn3MVnm64yLspc6DGOV1bUgbQtSEFoTaYVITHF9zEaMaqPMYhp+hiLGB1jNgqab/DH6kRjijJ5FHmpAQ3+BD6en/deyhNaxGAhRcjLLTIKCUKfITXxXDZwjPWl' \
			b'Y7SKAAASQxxiUtAwc01Ut8BJrsVBCGwI28qYqDZ5tERsAD26xp+NsIe8mnUj8PqMtBioFkKWGxAk/Cz0ad+7pJwQFJYz6VoX2xUiz0zWYAp2qdYgvVDE0LzGJl8rPsGN4EGu8F6wN3Ag/M8AkQL8vjAU8J9syPCCbNrhD48WAtaOveTrYuK5BEMoJpyfh4Hr' \
			b'VU2tpNGmJXgM40UQ4NDQoJGBawGCfEUDmqk6VXVN5Xzl68qH6KbyuvKm8qFLWMqND8BVtU3VahZuHxrKHA3B0LFBEoJrq85Xrq5cqE1XXajWVl2I7KrOVc5UzlYq9KkKWBcaFESP2GRIRYJQBcYGukNzXCAk1FqHzHUb/gewq13Vmqq1VdtWLry99lXbVW2I' \
			b'DfAYKqzpf4BWRagcVCGIfoCYoONBfKwjbW4D8aFdbeVDc0KjWlJsRVVXNKY1r6uzmgaVV2fa8OASmMaPoMuBk2daI5Wg95xBk1MVp74iPOQw17HyeJTHHlw0GMCNEfZ1isNKmN01yObA1Q65mwaZainkmdmrfM/mvRIB71a+LeKbSKOHGHrgg7cihobZmbdd' \
			b'mrzV0tjG1EC0q2wRGhJebAWRjLuqNxjRxxaq1aKFSh5ROxW//1DvbEQMlT9orcIrBdjugBwuYoXjToOoBRFLkgWZSjJ0YOEZKE6uL1fQl69oAkt6XYVqqkBe1a5anGlxIJ8lQqSv0SsILmBfGKJZgxQlUAo1k9pG+kbDdmjqyq6cXXZl1xJ2tSu7lrCrW9k1' \
			b'H/o7fKw5K1MEtX44LOIfkYUvB8yqTI0HPn7PGiPTVEwiHT9uw5TqTIvgyHy4tvJs5dnJ08ksGl8GLWfzrvK+l4LU/7d5DnrWyiTLCWPi5wUY1SK69fKVX0uu+BQpszAGWIiTZearOoRqEv7AviDq3amwJDQHUmHtqbcDfWvRl9ZlQn7CjQKitSyCoD1vzcm0' \
			b'o4XO+LYQMraTocdMMlgIfLVQQ9XFYXEdFRdNwgKrGliIm9XmO8Uo4g1s5iujJk0UnhjE1vHwXDmChYFVZiY55FhoVtieL1IaaNSsfFvEt+BfGbZk2agGmnuGsJUzPWd0J5yBJnqeR63sSZpmmD9X8p2QL6XT+p9DT7QMhnfLWPGK1jlpnnVHGmvuUmPxqXEg' \
			b'q5aSeXnHz9vNOVff9jbSXgDuTiwD7Npk9Fq2ImFTKFu+YUJBTuQQoy9swmJLaTCidfENSkwtSizF/ZYK2aeg4pYnJZsuOosaWjzw5ayUzCUMP8nyTp10i7qkkXGIGVfYr1qwpNyV4qORmZ9XTaHvTdkNTNkNTNkN914tHWQVPi6YVt/PljG7wZwZc5xi5nyn' \
			b'pzxk5Af7WA5OzIbM4nqCVOvr0BuyomMvZ3tyTDpzYhq35uTEktaboFLtCdIunyW2O0HaZbLY1qdHu8esw8iA28rkIy5z0FmPMGzRI4xn9AhDmcYUSp/j61Jj+rPuTplv9QdjQww9vDzAWN2BsR6MDZzR/Nku0a0ULffrSjcUe2CV2RFNn0oSqxGrMe3VmPby' \
			b'LJT+rvtJCysNlKRdjXuFOCcM0PETqJFPH5rarwCww7KumlWKii17FlLU4oFBRwEj+TNY36qdZq/ok17fpk96/pbXd82mTEaJRswEGmYCDTMBsSJ+eNVZyKo4rdo+Vkifw5gaNMDQGuOxA6RajOcWOmLljbWoSpyYGZmYmWiXwpTDYMphMNcwMskw67YDRh9w' \
			b'NI5gRliaTHWNwBAz7lbBUGiF2TGjDG0yEGcDcTbR6mXE6mVO7VsnvMuKatg4X4FqWKgGPbxGptB+i/ZbtN+uw/VwClPXK08Km6aCYIWRTUSohQi1EKHwCNIqatQiZyc5u9u9BPOK2NCBDR0jCUY/2YgaGtMVqwDEFAf2OZRzMau7A7zyt76N/ra3kWXVyymI' \
			b'Wo5B1Dy61tWr8CY+uUtWFjq96wUGiVgQ0tAriBYsGmEPlhswC9iLhlJruCnEHk2MATMAuYmbBLCGhm1aBSVTfaScv9NbGO/obDWti9JBHzpGS5NVmqnSbRc0VaU7Muh+DGo9nQ2ig0F0GIhueaArHmjnOfGeTsrTWXY6dU6nO+hoB50qoCMFdJ6ANuPTTnw6' \
			b'LkJcIg5RR9PtEHQlBC3Rkm2RzlaS+YqWFMhETxcb0OF8OplPx/JpEk5T5sD9hswONJyoNnCaruLCbVt04w5dwFRXdLMS3TpD1/KEl2w8/Q9ZLF0wE9JautyFrryhe4osXx+zCQPSJkjAxvG9TVQP3Ssj18nQ/SyOrr6pKbWma3RquuolULNpqTBfZBMKdFRj' \
			b'EOBNS1fW0JU0lLfji7HkNpoQR7nD0wmJQSE2rZXq+NKf0GsbR7fkENEUGXJ7ur2GclF76Yafju8y2nT0pppvEtp4opduqWrkvi96Qyjf0dvoNitqLJUJ8YHjmyD4m44aomrc0UR3YhFIbwilN6EzNnTjEF1BRpf2tDXutAqdw1cGtUQmsYkLhPhQxhIfw7Nl' \
			b'/oTIlnjkX9MEjHRioA/Z5GBUK+qoGN1X6EYONow0mM2Mq4qaqS5XoSrtJdWlmakyzAlbaonlqHmaYpOuXIm2WBATet9G/5TO2JlacxUaQ+25nNJQjXMUp/qnueA75i4I2tr2IuDI//HMKmiTrVymRRgIMc5lgxhGu2JzAvYt9Ft/92qXKxVse1Qulc0Nlc3E' \
			b'gTaZjXgmgBkCvjRZD/VQF2kzSNJHna075WtRXnRUiZ5q0VVb6KvN9LSZ0M+QTmcWk54SRtkRfQ356LIV+uyZrbcq0916h/6GNDrjlXRYix6HbiXLMm1zHOg0TVz41r1KfKE2UtHQEHqENtEjsIcf0GaexiSdRrnkooJzrZmGk/JOKLgb03Hnelfqe/HqwjH9' \
			b'WekOUCBVCSCwF5hA6XyCkWEhK1ODehIzxyjBD1RjucIcLpiJghKEECPoINwSjIi8K5Cib7l3C/ACJQkxmO4haMirBDY4X5e9qIAQdUHQHLrpgrspCO4FwVcQwvBUhCc64UmdQQpG5ebmwUiOITmAuPkYsuJHhh/EHNakDt2vMBmIE4FsEiCpETaGLsGGGsIG' \
			b'e8dhg5J3wsag7hI2tt4+yG1cFlA++oK0dIKUqph7e85EqBFL1aDcdUhAuyzotcidQ4aaBxnCQIEM4VsBGT3pyyBDOCV0F5CBRIEMztflPNoJGdtIYbZnHicHEytGXAIjGr4AFw/VjAMEUiNANAOXAKIpAGL6w4GSdwNEXncJEM2UY4BIAe5d9smMYuvL3HMO' \
			b'RgcpUoNs1yEBjbIg1iJ3jg7NPHQQ7gk6CNNKdOj7YBE6CJuE7gIdkBjRoQE69AyaiQ72DqHD+hVSIESLu+n5GnXyjSEEUiNCtAOXEKItEKKdRoh2DCHyukuEaKccI0QKUO/CFxGiTQjBbeV0xoe+TA26XYc05LSg1qJADhHtPIgQ9glECNdKiEhELIMI4ZPQ' \
			b'XUAEEiNEtICIrLULvznaFSvuLlY4/MAELtZ341iB1IgVbuASVrgCK6atFGrMSjGou8QKN+UYK1KAehe+iBW9fULJXALG/qxMDbpdhzTktEi0KJBjhZuHFcI+wQrhWokViYhlWCF8EroLrBDCBStgn8hbuxAruhUr7i5W+Ip/1oXqYN8YViA1YoUfuIQVvsAK' \
			b'P40Vfgwr8rpLrPBTjrEiBXpfxArfY4UHVnhgRV+mBt3MYWCFB1Z4YMVw6YODM7BC2CdYIVwrsSIRsQwrhE9Cd4EV0kTBCg+syFq7ECvc9NrIDUSMbgWNQ4MGLYHBpCk+zz7CDXoU0CF5BDqaoYvQ0RRWzWbaqtmMWTUHdRfQ0Wy9vSTGuCwga30qoUfTWzW5' \
			b'0R6N1nmZGqS7DmnIaUGwRYEMPZp5Zs3IQaBHZFyBHj0Ri9AjskroHqKHJAp6NDBr5q1diB5+RY8VPWjpXEOh4PPsY/TQ2+iBPBE99MAl9NAFeuhp9NBj6JHXXaKH3uMYPVKA5Bm+iB66Rw8N9NBAj75MDdJdhzTktCDYokCOHnoeeggHBT2EcSV6JCKWoYew' \
			b'Sugu0AOJET2wAyNv7UL0UPUKHyt8UB+LRsHn2cfwYbbhA3kifJiBS/BhCvgw0/BhxuAjr7uED7PHMXykAMkzfC41NsGHAXwYwEdfppYSHdKQ04JgiwI5fJh58CEcFPgQxpXwkVKWwYewSugu4AOxET4M4CNr7VL4UOu+rhVHehzpqINZteDz7GMc6RhH+OdL' \
			b'FR6CJsgZ0aQbuIQmXYEm3TSadGNoktddosk+x2iSh5WPvggoXQ8oHQClA6D0ZWpQ7xC0yGlBs0WBHFC6eYAiTBRAEd6VgJKIWAYowi2huwAUaYYASgdAyVq7FFDWjaIroPSAQj0Kq4j4PH6U3HJnE6DQo0GaAIrkFEDRQxcBRRe2ET1tG9FjtpFB3QWg6K23' \
			b'U0cNShg3DCsffYIourePaNhHNOwjWZka5LsOachpQbRFgQxR9Dz7SOQiECUyr0CUnohFiBLZJXQPEUUSBVE07CN5a5ciil4RZUWUHlEa6lFWLfg8HoQoDRClAaI0PaIgS0SUZuASohRbxPT0FjE9tkVsUHeJKM0ex4CSh5WPvggo/UYxbj3aS4DSl6lBveuQ' \
			b'hpwWNFsUyAFl3k6xyEQBFOFdCSh9tywCFOGW0F0AinSwAAp2iuWtXQooO3aUroBydwFFU3eyasHn2ceAAtOrxrE0fgigIGcEFD1wCVAKA6yeNsDqMQPsoO4SUPQex4CSh5WPvggovQ1WwwarYYPNytSg3nVIQ04Lmi0K5IAyzwYbmSiAIrwrASURsQxQhFtC' \
			b'dwEoSIyAAhts3tqlgLJjE+oKKHcXUAz1JasWfJ59DCgwxvLxbIWHAApyRkAxA5cApTDJ6mmTrB4zyQ7qLgHF7HEMKHlY+ehzqdUJUGCV1bDKZmVqKdEhDTktaLYokAPKPKtsZKIAivCuBJSUsgxQhFtCdwEoiI2AAqts3tqlgDK6U7W+kSs6N+HYiz4QglwH' \
			b'eoT+C+raBJ7sMce21MtsmIQv24jmmuGaDjJEK2w7cMkKW+xx33d+vhnd5M7d1f/fMsW2U47tsClAYg1f2ugOm4lrQAWbYWWre3wfjsrBDMtPPiwHQyyeHs/cFDvc7s7Vj1hjhZlijRUe7jiP3yzd786tZ0UB9YUxFm+KxljaC0NFQzrMsj3PBogSOu0CW30D' \
			b'pLSGEWTH/tV1SnJ3pyQddSEPzvB59vGUBOs6Gus6ul/XkZxxStINXJqSFOs6enpdR4+t6wzqLqck+xxPSfKw8tEXpyT9uo7Guo7Guk5Wpgb1DkGLnBY0WxTIpyTz1nUiE2VKIrwrpySJiGVTEuGW0F1MSaQZMiXBuk7e2qVTErfzwP6pYIqbhJUFp/hXZCmQ' \
			b'pabe5ZP8qpIAgUsNcMFchR6NwkPABWkRXOqBS+BSXAZC4SlwqUdnK9krttCl3uM6WebJCVQ++hxfVckYU/cYUwNjcCdIVqxGI1yHNOS0IN2iQI4x9TyMEV4KxggLS4xJRCzDGOGZ0F1gDBIjxtTAmKy1SzFmsBW2OTWMWT5vqWmSWq8os/9Ejq4UbLSKb1FU' \
			b'MNMqmGkVzLQKZlrVm2mlWDygowcuHdApzLRq2kyrxsy0g7rLAzp6j+MzOnlY+eiLX0W9mVZpOf5LyoGgHZSt0QrXIU2ygHYLRuXHdeaZayMzATORh+VxnUTEsuM6wjWhuziug8R4XAfm2ry1C2Gm2bNl9nZhzIote7CFOglGFvF59hGw0CO0iR6BPfwAsEhO' \
			b'ARaEkovAYgprC4UngMWMGVsGdRfAUrx62xGwDMLKR58AC3sBLNx6tDd0XVamBvWuQxpyWtBsUSADFNPOApTIRABK5F0BKD0RiwAlckvoHgKKJAqgcL5u0NqlgHLMTbSTFxevsHI8WOkqA5OL+HBBNMMKTC4GJhfTm1wkZ4SVbuASrBQmFzNtcmFPjisRW9iG' \
			b'yfjC1VM+s218MfscA0weVj76IsD0xhcD44uB8SUrU6MdDkGLnNbhgQI5wMwzvkR2CsAIF0uASUQsAxjhltBdAIw0QwAGxpe8tUsBZsem2u7Kj/dczQJQAo62mr7r+CqB4TKg8NWA4CqDG0jEN3KrgKRGEHADl0CguIHETN9AYsZuINlSdzflNoMAKTp8UdH7' \
			b'W0fSW+dclWzm3S0SGSPqLPwo1TmRN1+VhT/b67qxJtFjXCqSMWDmHWXNuoN1nRlkF6LX1DekMOLz7NtICF1HiGB7e6mkxQvR64FLt6MX9lI7bS+1Y/bSQd3lZen1HkcYMQgrH30CE7Y3lFoYSi0MpVmZGtS7DmnIaUGzRYEMQOw8Q2lkIgAk8q4AkJ6IRfOB' \
			b'yC2he4gjkig4YmEozVu7dD6w7mC9iYAi5rjjAQv/lA2rGHyefRt0HAMLDtvYfrYhOSOwDF0CluKwjZ0+bGPHDtsM6i6BZevtJTHGDcPKR18Elv6sjcVZG4uzNlmZGtTjZ+YYWHDWxuKsjR2etbHzztpEJgqwCO9KYElE+NiQBfAiPBPqC3iRygRecOImb/NS' \
			b'eDnKparr58ZBPzfIMIRzMuIb+dyQ1AgAzcAlACjOxtjpfWN27GzMltI3U441PgVI3eGL6t4MPzdsM+9zw8477xIZI0ot/CiVOpE3X5WRf8fnRqxJ9BibvjIGzP3cOMo9p6v6HlZ9DRl1WczhG1NfpEb1NQOX1LfYOG6nN47bsY3jW+prphyrbwqQ+sLnUruG' \
			b'6mtmqu+8zeCRMaK+wo9SfVPKfPVF/l3qKzWJ+mIXeMaAuep7l64evYnT+KNN31vqBVYN+MZUHqlR5duBSypfLD7a6cVHO7b4OKi7VP92yrH6pwCpP3xR/dtq6wcPLBYeY5EaZLsOCWiUBbEWuXNcmLfqGLknuCBMK3Eh0b3MCCBsEroLeEBihAesOmYMmgsP' \
			b'O24bXeHhLsBDR13AqgPfGDwgNcJDN3AJHopFRDu9iGi7MXjI6y7hYdIxPKQAwQN8ER66HfCAZcNYpAbZDkGLRlkQa5E7h4d5a4aRewIPwrQSHhLdy+BB2CR0F/AgzRB4wJphxqC58LDjOtEVHu4CPDjiP6sOfGPwgNQID27gEjwUy4t2ennRji0vDuou4cFN' \
			b'OYaHFCB4gC/Cg9sBD1hujEVqkO06JKBRkmiRO4eHeWuQkXsCD8K0Eh4S3cvgQdgkdBfwIIQLPGApMmPQTHjQO/Y+rvBwF+DBE/NZdeAbgwekRnjwA5fgwRfw4KfhwY/BQ153CQ9+yjE8pIBKvggPfgc8eMCDFKlBtuuQgEZBRDeRRRk8+HnwINwTeBCmlfCQ' \
			b'qF0GD8ImobuAB2mfwIMHPPQMmgsPvJMx6Pvwh9PzE1/2xhxF727Ub7U2tK+eNqsTp2i7vi7QRFWHPai+EFUCW+Yhi70EupA1LDR2w1fcEC7Q8nmV/957cNRzYsic+NF3ySUAhFByEYDawqC57yB7O2bRHFReINBGk82EaKER35e0SCHjsoCKufhcGJZfWrON' \
			b'RS1snbFULWU6JKB9FmRb5M7PaxCg8FVcRCtBjUKWevaPzEcmA6cib3f94Lz02VygIhEisGLOYMFy5BfoJUUQq4W1NOPkALHsBW20VBecyH85pm0veNG95oejEKNYU73awrAx6AJoAaWmIWpivYPRiIDHpAlKvogxZwGjhI4lsBHhYhdMtAsmHWOLFzaDAleq' \
			b'/qTa79P2qOdRsRdp9bxFiqi+G9mzGOcIQ6Wcs/JQKt0SjYu6tlPLmHmzJwJRsXZpVdQnUqaBDpFa6B1qoa5YM+JQHWi6mfoxZ+hsd+jHHN3YMybyAHMDFCQb44ivN1lRZg5COxRlrpKYHUoyMfM9rJLYwyuJ9tenKHuVJHCOLnGPylJ7vuHm5JXG1FekNMTR' \
			b'a1ScfUqDD4EuKU/8GNhSIrt4AlbP/lKco0eZEpH81c0ld5UceVIWxHefTim6HOtSg89cHdL9ojL7r1aXSj0CH0tzjm6PPBDRp/PcwUjP0Ktm94BU/TPIykXoQf6saa/7sybpU7KwHHR0otP+dP1Ad73TuUt/6hxKo65nVIL5Qv4ffHTiSTHhU+eve3pXahNB' \
			b'4KzpXdAm31yEt7M2ddWrkzIQHOnjJ9cWZvYyjUma0robpSiHMwoc7zsnVwSy1y4yCFT/7C4CerEquKOqQqAyEE9zmZPSCbI42ksZBW7s6DE6B1O8DrFR2SVEJ6MhQnlzOXOAP65qqCqIReDldSuIOpCShLggkndLWUIBx2t3GzqqeN1K0x5sZCHiKGQurz7h' \
			b'hUvUR12BBtlDqc/Stdx8DfeyhufuyGONYuk6gg5RrXzP94E0iBtymbGHZOSrTNENlOnr1EgtUqPmCtQo6pA/xqfLV6jQXVSfQnXU1lGLa5m1faXmHEBrmkVao69Qa4iyVW1OTW26u6k2epHamCtVG7WqzcmpjbubamNWe/JB9gjcDjPAYVSAduvegHX/sdUU' \
			b'2kju2YQc2nBUO1ktprLrU4Nyq/YhrGS3Xy2IdxsSsuscI/ThrWKXGSDaK1aR0RMTI4OFLQ5BHGvQWHIsat+yfS2a0t1obcEhk+H/uYMK583PEhxxDWbR+aV925bpJxH5Bx64gVuDDR1WankfjLnqlftVkU5HkezW//mKZG+rIrWiSHaPIrnqlavKI8COVcax' \
			b'sjQDNYGOQP6Hp2Tbael0w3NmQbLo4Iivdh5Cjb9XytJBkqHdbolI0hA7d3BA0+1hOzEyZ2CneZD2l2EJ4EGAwQMJWMsX8ChqZqGR4BXL7EGYRXSxZkSm8Rc85SDhXsTBKI6lGIKTgdLLcHKEmTeZoRncbDE1osYhGasuw9ixMS3js104hC3oiyVD09aQFL9+' \
			b'usP2G7dv+H8wdGR9yWnLhollWLQI/kuxkG8ORWNzhu6hwh1ycqBP8K8zPeWSc4xNvqPf02PSNTZ74b463Efz19uQZtxRcBX2oh3iuGPmof1FmO6xbOpVNg8km+567DkHFU26k8HeIMFs7AX/XKQxFxs+7EdhtmuGd6yCeiBBbU9QUFsm+xQE1Q4F9dA297sh' \
			b'q9zB12sov9VjPglmeyqCeawjZ1E4DZtAyXozQ1DVTRBU3nVwKVxV1yGqbvxjiY6eb4h/O9c16/aCf2fZdeEJeO2iFF/ZqubtEeQx4aXePOKS5GGR9ppX5OeireMfGrSOfjSdf/3TcbTnXwdSznF3kPnDt6/PQ+Bsw1e+4X43OoXPlzClA7+hG6gmvr7FprP0' \
			b'fFGISad3vaF3bJr9FQXpKP9xUfmBvKKwnD/2ZS2almF0+tcfLE5xXKnJKw2KUt5MN/IOEnUuY7NVflL8dDEa/ZhjhX+ejmPTtujoTPGP798Ib6BUzcv8tK/N2XgZBlNqL00pncLdS2woNeMfrT8VcUxcu4C4XffxjdJHN9ElGrtq/B+tlI2meUtPprQbUNru' \
			b'JtbwDz4OzKGT5Pd3CfJFgnx/IN8foWXptpM7Aul+wBBH9wLuam1+Z1+8g4/v32MO4GqN/n691zTcyD9fueE/v+V2/duVazvO7yySJ/VZmcnuWsTBV5f+x1T66xKFdJ1IFAd7hSJBL7gG1+o84L++Su4SVV+L5FAHXIlDI1TeCJqVuYOJV5glHF/Cuio5/Fpj' \
			b'HvNVjqamh6pr1KGTmr2SJrd2Tur6qLxFbiaZo2+BSaf4o24yh9G7Yl2XAmia3iF/in/r8yqkUB9NEOnbaujwa6Hb8V/v6CvpKuplh27bPxedI5HolQVyaauvd/FbcjIXWmnvinC66lY49Fo7a640WzylU+YJ6S7m+io5gj//VS5aP/ZkLGwWzJfujkgz2a1u' \
			b'g0OvuZslzWQRPJoDR/xdkWNX3QoHY1p9w+TYV8dz4MiuT6/bKMe0dnAbHHqtuRI5jla4nQxXM+SZZOPQjrp6R2ygd6QEOHRXPuloNew2OPSamW9hPKBo7+L5KL91tdfRktecfMsq2lkr2HZXPhFp0fc2OPRae/q9xj8UY+f2nq1OyCnn+G7W8SzoxQXrY8eC' \
			b'LF/dGAeezfucPCbPaCfJTXHg2bUtvl3LOiwdCJ3n8Htx/f/5JUermF/dzhzYXDHvU/JU+oP2TJ2SQx+o29UHOKl3Mg59MO9T9GT6oKlOyqEP9O3qA12dlEMf0E9c8SYbwSYbw6In9DsjtDe0pjhihfRdmD/mHRVYSBks7gStcVtbhyV4ulJ+R962yhwy+q2M' \
			b'1B+Uuatypxy+RfhK4bTD0VKnIj4gbC4xk53vqWm8sTbfUBs3wO7a/OphlqU7JYujtIo3bfPWE36l719DO3RbkhUhkX6Ar655w0BozOvz/weHKW3b'

	_PARSER_TOP             = 'expr_commas'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	_UPARTIAL = '\u2202'
	_USUM     = '\u2211'
	_UINTG    = '\u222b'
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
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('CURLYL',        r'{'),
		('CURLYR',        r'}'),
		('SLASHBRACKL',   r'\\\['),
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

	_PYGREEK_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.GREEK))) + ')'
	_PYMULTI_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.PY2TEXMULTI))) + ')'
	_VARPY_QUICK   = fr'(?:{_PYGREEK_QUICK}|{_LETTER})'
	_VAR_QUICK     = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK   = OrderedDict ([ # quick input mode different tokens
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
		('VAR',          fr"(?:(?:(\\partial\s?|partial|{_UPARTIAL})|(d))({_VAR_QUICK})|(None|True|False|{_PYMULTI_QUICK}|{_VAR_QUICK}))('*)"),
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

	def expr_ineq_2        (self, expr_add1, INEQ, expr_add2):                     return AST ('=', AST.Eq.ANY2PY.get (INEQ.text, INEQ.text), expr_add1, expr_add2)
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
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                        return AST ('|', expr_commas)
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

	def expr_curly_1       (self, CURLYL, expr_commas, CURLYR):                    return AST ('{', expr_commas)
	def expr_curly_2       (self, expr_term):                                      return expr_term

	def expr_term_1        (self, expr_num):                                       return expr_num
	def expr_term_2        (self, expr_var):                                       return expr_var
	def expr_term_3        (self, STR):                                            return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_4        (self, SUB):                                            return AST ('@', '_') # for last expression variable

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

	_AUTOCOMPLETE_CLOSE = {
		'CURLYL'     : 'CURLYR',
		'PARENL'     : 'PARENR',
		'BRACKL'     : 'BRACKR',
		'SLASHBRACKL': 'BRACKR',
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

		if self.tokens [self.tokidx - 1] == 'COMMA' and (self.stack [idx].sym not in {'CURLYL', 'PARENL'} or \
				not self.stack [-1].red.is_comma or self.stack [-1].red.comma.len > 1):
			self._mark_error ()

		if self.stack [idx - 1].sym == 'LEFT':
			return self._insert_symbol ('RIGHT')

		return self._insert_symbol (self._AUTOCOMPLETE_CLOSE [self.stack [idx].sym])

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
# 	a = p.parse (r'\[[1,2,3],[')
# 	# a = sym.ast2spt (a)
# 	print (a)
