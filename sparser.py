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

def _expr_curly (ast, forceset = False):
	e   = ast.comma if ast.is_comma else (ast,)
	kvs = []

	for kv in e:
		if not kv.is_slice or kv.step is not None or kv.start is False or kv.stop is False:
			if ast.is_comma:
				return AST ('set', ast.comma)
			elif forceset:
				return AST ('set', e)
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
			b'eJztnX2P3DaSh7/MAesB1ID4Ksn/OYl31zjbySbO4haDIHASZxFc4uQSZ28Pi/3ux6pfUaReulvs6e7p6RGG0xLVlEQWqx5RxZd+cvuH/3j3/rs/VH/4+NOXn74O25fP//gmbD579vnz1y/Dzh8/f/axbJRsddh+9OL1p6/iVsUd/ub5n77++NkXz7+Q/VfP' \
			b'3sjeR2n3r2n3M+x+8fLZF3/+KFz9P+mu/Q4f/vjLz1/+jWL9zqsXr7+kG3zx5nP6/PKj8Pn81Wdv/vbFc7rY6y8pb399Rl++eP3mT1SuF684JX/+5XNK9ZLL+yl9+8cvX1MpP+IzPv701atnUQafx9x8Hu9PO5+/+NOf6RLP/xI+nr36LHx+8tFLziwdff2J' \
			b'FJv2Pkq7f027UuznL794Lkei0OhCb5CRkAFK9OrZZ1+8+ZTu9IbL+/y/Pn4ZvybZf/Liry8+oct8/MmnLEuc/tlLyOj5myiucGlk9uNnkuV4i09jkhevuUzhKxHGl5TyxR/DB2chyFoN6oUSffv213cfvv7516+/++bH3z68/TUcevfPX379+rfff3nXR96/' \
			b'+/vX3//+/tv05Tdh96e3H77+9ucfZe/Xn/837f3GV/7t3W+/fdvv/dLvxcu8/SbtfvjQ3+37t99+iPu/8FVxeJCBn+Lujz/0uz+8//D3uP/T7z9+/cNPv8Todz/8I+7+IxXyfbrMdz98/33c//Du15+yosfdb3//9cf/y68fdmL0m1/ffvvf7/psv/3uu/52' \
			b'7/pcf/P2fX84CKo//M+f+xyxgPov0vFvfnj/c1bOd//TSyXcuBfWD+++fddHQsW+T3f75bcPP8dYf3Z/159//Pl9ivz009tB5Lc/fFXdPtlYX9nmpsJOSzumoY+2svWNREOM9zpKVoXNxt4MDiDWxvPCCf0h2uVUG8dHfPVEV0ZXG1WFKxt9E4/Ksf7AhnOl' \
			b'Wny4cEAjQ/GQ6iaHXJMfol26lsOHk/K4kCfPSTw+XEiq2pvBoS4/RLu0p6on4QbK0P9NPNLmsU62dIj2ND48nQKZ9Ydsfoh2aa8j6fAdWTruJh6VY/2BjVa8Z/Hhg8yVvxkcUvkh2qU9Ey5F9dNUVr6jrKFquJrCWSiNRON+dlxhs+Esa/43Jn6taYeuK8dx' \
			b'k5BfOYhEisvZSDl92x+VYz4daIcHNpovr0ORNGuIbvDhQha0XCgdYlH1R2k37JFC+IqUE5d1tENlsvhwUupwD8OiCRVAIiSJ4qtwwGURjw0doPOCTHTL1RiMI6SzYi44vrEzh7JoN03RDaImVKA100NueiiLqml0cMLGoN5q0U9SShgjKYzi+tOkn07u7noT' \
			b'iYdTdGNgeuFi2leh2tgcfeUhEzJmMfT5FESjYPLLEoY6HibcGK4HsuWg511UzZAGduzEyqhCA63swNjCl/3xdETjiE5HDI6YdMTiiI1HNgoKWuPD2T6P/SGXH6Jd2mvxEeR4c5N2aS9UHCu0nBIypdkIrcUXcm9LiotruQr20jB2I1eQLBzDkRjd8F1aVLkP' \
			b'eXOVddFI8sNyIMRZ4gYfQSVuJB5shzMSviGbRUFCzLNEDJl/k9UlmSLUwiaJkIqiFOHgE9uk4lG07a8ayI6yEgBcv+dlDw8B2lFxB8mDMgG6QQ5cW70KEIPw1NL4SI88q4V7VuGDnnaiFlbxLu3V8csbiYZY/OLmJjx4b0lRSLr02NVBjbheWroTNLIj5Qgm' \
			b'0JqqDRiug6zqoLR1QFpNcRf++TkV0B9QH8y1sVUTqltXVERbUdWHIgYxtwShIFzDnA5Ua13Vhis3VdtWbVd1NZlQUECqkHC+ChcI6h30OYglmEmw52BUoTq6EHTVmdBiCG0FsixXV52vuiaYEpkTbQP4wtUUaTflOVw7XNZpgnGwgC4EVzW+apqqaaumq9q6' \
			b'alXVhtsGs1N4WIaHY9CzYOGeHg6V76qmrhpVNaGUJIBwn5qf9uHRTTcNnzVZs9JfVU9qekDdPrGWH1RBxLwJ1w9yf2INvg3SpsNB4vyt4m/D4Q5xvsZaI0eqkQ4yd6iKIEIIu0VTQknVtBbJWLLheIvkWqoEFUZX5ZNZ9jerEZ2oylhGqA0rgneyjdXnuGJy' \
			b'UUFCM4IRefQyyIs+V2gpcciH18iGr89xM4WbNShyIwrosWmk3JqzdILba4fba3OqG4iFaVDPaGxMhB/fPyhmFW5XBdVZ7edg+zFenjNiPYCYjvQy9Qqvkwk/PFlY+or0nB4fJG2yYjJhsoEgmFW4hwu3WYV7OuG2q3BPJ9xuFe7J2vjy2qXReFfStpfHn4ut' \
			b'dr222k/Zatex1Y42a4fK6LSIv+PDyLY7Y9YGlZhX3Ikb9EbKL1Kx7ap8J8Sr7Vbxns62XQ1dFj+IWDhnjretbDtxqgiPHUzA4V3P4V3vCReAk8krrwOoO95cHwg6ebVuILUGTdg6JKOcZUrR68LjgWTTimygOS00o1XildOiV/JcV9Ehgwe8h954lq8iSZIo' \
			b'gyy7tuq6BymQUDZoiW+uqlAAhEctN/XAAq6kjA2UtGEdRUHyoj3QQklTuh6rI9zgqFYXvZNOngONgF6MG+a7PptP1fQJhUcvk177jY4n1iBJjV66VaxH9E13JE7ujwvbVX7lfiSz6uMx5UnC0uvT6XT6yoZOPemrlE/YBmhW8Z4UEqt4TzneQ6NRQILSMt4j' \
			b'bFd5HqiujmF76nfDmTFSNI6lRl02XJWpAqLok6AftefrlgcU36xymcqlWeUyKxe8359gZJaBxRq+wSpvkbcxqziy3kwnSgLYw9UpXnrpxYGLN3a28yPocQvtlsbcPXop0HhDatS1Xhp5MgJU6dhb2OuMlv5EHivKQwqgVC1ccW2LjbiQFBvo4xPoLY1seawl' \
			b'd4+z5Dx4ibW+Y3fVoyn4LQ0gekwFpnFS8jIsXW9q24yUr2T+Cs9I4y6g6FxnkdGAC5LctcrJyosmy2vUNdngibFtJGDd5QNWzmnGqFUe8KAx4EFjwIPm6lQKhfIGnU+cukueJ7hE4H+CY2TkhVr9JMv9Tl7atB6P0wc89kBB0R92EezZbVEGZnXtwxbek04m' \
			b'OXr/sBWZRj3BItsHXpBGvKC+e+gFkQdSox94QShPGoOVNMYo8UbFsTO0UgE9SymJ4014vhppgJkb+LsN3mPXiRwneiJTdtG6heRlo1EBJD0j3UOGmkuuwxcNjk8my3rUqh5ONdXNzGFyrxrxgpq5SZNm5jB5xXASaxGr1Dp19W5dVyxJPMdWKR7cXw072vL6' \
			b'o+vt39Irh1DORG+dFi8dvWatiLtz3Wi7avddHhIt+B3KZuANNuINNjOzzpSdP+xmDrOTTQ4bHDZwrhg4V4w4V8z1zla5Ja+RuVqvEbuLzKPvkiEHmBY3lIEbysANRbKJL+R5zJvYQlaTpYvIgcIPFPTI8Ks8bTs8OjyaYR5m5HHHRppZqm9jW2lj29hXhPag' \
			b'RXvQoj1oYzvQroOHy8kprzfxyY56yXrbrBDOsLivlnChSHZ766iBzrU1NqSY4pm14pm1D/xFOCid2JqLLT3YmoOtOdgaNhaJG3zb4nDLl1ibMIc3AtUqwbv57g0U0dH6p6yeHurpoZ5hoyothuuRspGUzSPqTrwlmTSQScMggwMjzsyjo9Wg84wk1EKWLc5r' \
			b'Y9L2sQmue1wFVo+qwKzSncw6r2Xaec1tgLq6DaDk5ejIn0dL0nWcUcO05NwTSpE/ZrBwFwxGhyz30qZJA1m+knQdS6QbSi+KLgiYFrxiOWkpTCyIhQua3M/kyaSRsrTuG7XMaSFRWkWU1h2lNUdpNVJaipRQTWsx0EIMtOYCrYlJC2LS/F2qFFpUkdY6pOn1' \
			b'NLeeJtbTdHSatk1ztmmGM01vpuqkZQppjUJa1IBWNKCJ/DSJn2RJeaa1pGjJI37shPPoFZuWQqFGZVAmHR5rmjzy5ICn1wZ6ZaDBPfQkoucUyZXmDNG4w1AubZpQL7TgMlaOpgV/sVAyLX1NC7TTKsktLZRd07rC4fIbWkWaFiJvaFlf+qc1kGlReF/x8tod' \
			b'rXpMy2prOoMO0mrBYd/RVWkdXl74XPEeLThMqxyTBm0cnVXzytRhj9ZWDkXaBBFsWlq5mrLScC7CESzwXmFdZF6SPuSK7hwSdJLvIJRN08gdPC/uHT46ioSjQfSbhu8YIrTKPOWI1gKm1fFpFeeW70V3rmmB5HBaY3lpYyw7Til5ie2K15/nRZxpnerw39Ky' \
			b'1CFNS1nvZHl5EiKloxM7EgktO0wlIEmTTHk5ckpJSTtayZykTVu6tcZi5bQkekPlq2nddFrDmHJOMgstmw0tSt+SzHjh8pCipdyor6jJSbY3sDu1x/TIoR9bPQMD5BERh5thDjEjLS9QcJdhmoXGeR+G6Q8wTl1goI7E5cY26Qqs0vV26aaW6ejgKazT4dKh' \
			b'blz/t9NK3VI7vR8bpawcYKZ0q8WmWv3LPiUIu6eE4aZ+GvD2b25a3pIOtNFu4wsGmW58ASHrxcsLv7n0z24y496Gm3Iztpklx0bE1qaJHlu1NGy0vI6N2xrcCsrfy3j9i34VE+KAG7Ggznjgsn7irO+YlgljRhjhhBNWNCNeNMIJAy4wD0KcFinueUDH2wO4' \
			b'ENJRY44WxV7EB5Uxot7CCfquzVhhhRcE7hAPZR2yg4TIRotNAEbIFuGCN4o3QYi8sZyGxFQPArEDFwE4WF8FHpKiDB98Aap22uYIQcM3/U+QMsrZKHCZ6sEVuGBmcuG5/4gk7ANLLf9ACMro3eCq0EvFpOIt6QnnuZatXDYnFypBg1XMJxdFKFSSWAmbBoUg' \
			b'01lGKRXz6eOZU1jFooNWSD6+4YBeTj+lh0Oo+Kdc+8ESnhI7g2aHrSGUmR5l/ZsKN0Gk/XGZBMvxtZRdqoBfK7tm2EUCZJOkrCpp78SmjjRzmEX8wy95YGSpHFmJWEhQSiwB1phX2S0nrFK7AkAVI9rsTBvIRA0b3HH4YgNVEzqhzAoZZS4JloRKAqURk9QM' \
			b'k5AsMgmxMib12VkOJJGjr7biSEQXcSQ0SiWfQ9GUQHbUmLpO/KxNpzvih94jYXR2C3ss2GMHgdljM/bYxB4kKGQP3rVoM2BPfssJe+yuwOzpI9rsTBtbRbYHDxdOoZDeZUlZ3yzIY0EeC/JYkMeOyGNnyCNiFfIgVkSelJ3l5BEpejlvhjwiOCGPBXmykhc2' \
			b'gtyKoBVB+xHk8dORGps5BHkgaBgYQT5DUPL2SKwQQR4I8iME5becIGiSq0FyrqsY0WZn2i7JICLIC4I8ENQnVXCLMII8EOSBIA8E+RGC/AyCRGCCIMSKEJSysxxBIsV43gyCRHCCIA8EZSUvRJBfEbQiaD+CKFMwv2YLghogqBkERlCTIahJCEKCQgQ1QFAz' \
			b'QlB+ywmCml2BEdRHtNmZNiKoSQhqBEENENQnVbAkRlADBMGPzRslcswQ1MwgCIcjghArQlDKznIESU69nDeDIBGcIKgBgrKSFyKo2e7VvmgQ1SuL7oVFXQU4YEMDujrGEW8yInUgUjcIGwzWSkTqEpGQoJBIHYjUjYiU33JCpG5PYCj1EW12po1Q6hKUokcI' \
			b'Xd4pKSteByihZ42zh5SNEoFmUOpmoIRzI5QQK4JSys5yKIkgvZw3AyUpkkCpA5SykhdCqV2htEJpOZSo4xVeai0uao0eNq0GUNJwVCN5HwhK+XAZnRzVkqAMShqOaj1yVA9uOYbSKEvTQFBKEW12phUo6eSo1tKJpuGmTkmVQk4DlDQ81Rqeag1PtR55qvWM' \
			b'p1ouJVCSWAmUsuwshlIUpJfzplCKggOUNDzVeckLodStUFqhVAAlHubJdqgFShpQGr67sRH5Csn7wFDSGZR0ghISFEJJA0p6BKX8lhMo6T2BodRHtNmZNkIpDTji8imU07ssKUNJA0oaUNKAkgaU9AhKegZKuFSEEmJFUErZWQ4lEaSX82agJIITKGlAKSt5' \
			b'IZRUvY5KWvF0CJ4s6QRbpHSt0dYjGkrKwxcdNkhKp9pBYEhl3Ww6dbNJgkJIoZtNj7rZBrecQMruCQypPK7NzuSRU6mzTUtnm0ZnW0rKnEJnm0Znm0Znm0Znmx51tumZzrYoXOEUYkWcStlZzimRpZfzZjglshNOobMtL3kpp9TKqZVTh3CqJVVgi2yFUy04' \
			b'1YJTLTjVglMYcI2T+sCcajNOtYlTSFDIqRacakecym854dQkUN0NTvH1MK7NzFlZoXwvlgiqVkDVAlR9UgZVC1C1AFULULUAVTsCVTsDKlwqggqxIlCl7CwHlQjTy3kzoBLZCahagCoreSmo1mHeK6gOAlVHesAWKZ5xDc+4hmecNqQxHUAF/zhO6gODKvOP' \
			b'6+QflwSFoIJ/XI/844NbTkDV7QnMqTyuzc7kkVPJRa7FRa7hIk9JmVNwkWu4yDVc5Boucj1ykesZF7lcKnIKsSJOpews55TI0st5M5ySIgmn4CLPS17KKbNyauXUAZwiDcB0FCPTUWjrEQ0lpQ1NS66ZUwbTUXBSH4hTJpuOwqnAKUlQxim+JO6Zc2pwyzGn' \
			b'RlmaBuLUIK7NzuTCKd4Fp7iISi7msqSkgZyuw3dI2khGlUg2ccrMzDmRSwmnJFbCqSw7izkVZenlvCmnouzAKU48uFUxp8YjvVdOrZxaxClFGsAWKZ16Bp16Bp16Bi503ljekJKoQWBOZV17JnXtSYJCTqFrz4y69ga3nHBK7QnMqTyuzc7kkVOpd89I755B' \
			b'715KypxC755B755B755B754Z9e6Zmd49uVTkFGJFnErZWc4pkaWX82Y4JbITTqF3Ly95KafGw8FXTq2cWsQpS3XPFimOdANHuoEj3cCRbuBIN3Ck46Q+MKcyR7pJjnRJUMgpONLNyJE+uOWEU3ZPYE7lcW12Jo+cSo50I450A0d6SsqcgiPdwJFu4Eg3cKSb' \
			b'kSPdzDjS5VKRU4gVcSplZzmnRJZezpvhlMhOOAVHel7yUk756dzdB4cqdTCt1Eqsu3uqGlIKntTrsEfOqgbOqgbOqgbOqgbOKgwvx3l9YGdVNrxcp+HlkqDQWYXh5Xo8vFyb7J4Tb1WzJzRY8GSQ8fyK08BTfR18VmmsuZax5hpjzVNq9llhrLnGWHONseYa' \
			b'Y831aKy5nhlrLpeKPivEinxWKTvLfVaSUy/nzfiskCL6rDDWPC95KbualV0ru+7ELqpteK9osVtxYFk4sCwcWBYOLAsHloUDC+f1gdhlMweWTQ4sSVDGLgsHlh05sAa3HKNrlKVpaDBHb3ARbXadwehCs8smN5YVN5aFGyulJlW0cGNZuLEs3FgWbiw7cmPZ' \
			b'GTeWXErQJbESdGXZWYyuKNGoAlN0SQpBl4UbKy95Kbp2DEl/GNw68ushSUGv4FoOLkXVzZYp7iwLd5aFO8vCnWXhzrJwZ+GkPjC1MneWTe4sSVBILbiz7MidNbjlhFpqT2Bk5XFtdiaX10Sb3FlW3FmKlo5ukT/vslOYW3BrWbi1LNxaFm4tO3Jr2Rm3llwq' \
			b'cguxIm6l7CznlsjUy3kz3BIZCrfg1spLXsqt8aj1JVOMzX3j6pTj1Y8Np/HSlYdC6hyAohHHNDa52efTaqji2Xsjr4fjGccGr4RI2AcsU+fkZPFlpddCSXTYQpdm8l7YDf6nDq1mV2BvVh/RZmfaOMuvBaR4qct+6SeDN8I+H6yGMopByTAGJeMYlAxkUOOR' \
			b'DGbmrRA3h7a75NlC4tKVM03RuyFXk8G9t41oiHIUz1bQKXa8hzTwcfXSG0Ir1PVTfqGum7D1/8avzq2Nq/Vt8IBGlad65eaDLM5isRIvbxRvtMPG8sbwGXngRlW2UItNC7VIgsJGFRZqsaOFWga3nDSqJrkaZ9LXw7g2O5N3SSqxUSXLtVgs15KScmMKy7VY' \
			b'LNdisVyLxXItdrRci51ZrkUuFRtTiBU1plJ2ljemRJbxvJnGlMhOGlNYriUveWFjSt//IHYvPzSw0uoB0qqpLFpVVlpVFk53C6e7hdPdwulu0cLCSX1gWmWtK5taV5KgkFZwuitZQoEbXCQoHbHFF6Wv7Yz3fZS5aWBu5XFtdiaP3Ep+dyt+d4tWVkrK3ILf' \
			b'3cLvbuF3t/C725Hf3c60sORSkVuIFXErZWc5tySnXs6b4ZbITrgFv3te8lJurWPaV2IdRKyWapQtUibfWEy+sZh8YzH5xmLyjcXkG5zUByZWNvnGpsk3kqCQWJh8Y0eTbwa3nHBqX2BO5XFtdiaPnEpzb6zMvbGYe5OSMqcw98Zi7o3F3BuLuTd2NPfGzsy9' \
			b'kUtFTiFWxKmUneWcEll6OW+GUyI74RTm3uQlL+XUOqZ95dQhnKKKRK+gky5Bhy5Bhy5Bhy5Bhy5Bhy5BnNQH4pTLugRd6hKUBGWccugSdKMuwcEtJz/XUu8JxKlBXJudyYVTLnUGOukMdOgMTElJAx06Ax06Ax06Ax06A92oM9DNdAbKpYRTEivhVJadxZyK' \
			b'svRy3pRTUXbglENnYF7yUk6tY9ofNqfQr3SPvFKVQ2egk85Ah85Ah85AB0e7Q2egQ2cgTuoD8yrrDHSpM1ASFPIKnYFu1Bk4uOWEV2pPYF7lcW12Jo+8Sp2BTjoDHToBU1LmFToBHToBHToBHToB3agT0M10AsqlIq8QK+JVyk4dYwupJRL1cvYMteRqQi10' \
			b'BeblL6XWfS54fv6+v8ikttr9c3XnYE4pZ47CGEs1wNYk49LHfXgOY9GRsA/MlWwsuktj0SVBIVfQfedGY9GnLLG7AoOkj2izM22kSBp5zplzGHa+2fvjdm5meLlcOqICsSJUpKIs4gPSbvsJu3gpgQOGladbLP0ZFn2fK5CvTDg7E3wlP1/p/BYmoI/MDQMz' \
			b'Iesjc6mPTBIUMgF9ZM7vY8IkJ4Nc+TqLaLMzbZfKPWCCX8qEmW4vuXRkAmJFTEhFWcQEpN3KBLmUMAHdXekWi5kwXhJ8ZcJVM6GtHHy8rt3CBPh1kbAPzITMr+uSX1cSFDIBfl3X7mPCzsBM6CPa7EwbmdCOmNAuZcKMq1YuHZmAWBETUlEWMQFptzJBLiVM' \
			b'gIs23WIxE8bDn8/JhOsfQ3gNPliqJvhgfT3PEQ+/KxL2gTjiM7+rT35XSVDGEQ+/qx/5XQe3HDNllKVxDgcRbXamFab4upr+SKSHzzVKSiGXXYcvGmRNcqhEjIk2fsbhKpcS2kishDYp48sdrlGIXs6bUifKDdTxcLhmt1pKnUMGL6/UeVTUUVRNbHFqC3Xg' \
			b'PUXCPjB1Mu+pT95TSVBIHXhP/ch7OrjlhDpqV9iIBiKizc60kTpqjjrwnEZJKeSSqAO3qYfb1MNt6kdtHD/jNpVLReogVkSdPuMF1BEhejlvhjoiN6EOHKbZrRZSx4xHI6/UWakzoo6mOmKL01uoo0EdPQhMHZ1RRyfqIEEhdTSoo0fUyW85oY7eFZg6fUSb' \
			b'nWkjdfQcdTSoIyJSyCVRR4M6GtTRoI4eUUfPUAeXitRBrIg6fcYLqCNC9HLeDHVEbkIdTH7IbrWUOuOxxSt1VuqMqGOogtjizBbqGFDHDAJTx2TUMYk6SFBIHQPqmBF18ltOqGN2BaZOH9G700bqmDnqGFBHJKWQS6KOAXUMqGNAHTOijpmhDi4VqYNYEXX6' \
			b'jBdQR4To5bwZ6ojchDoG1Em3WkodHhkcSFIFHFTBsgN/umx1DiMcIj0Fikykkb/vmaPqiFgqWZrjEDSFdJbGCYV0QQQqyCDhSguyaBBROO488BUMRwU5nGayaSnO6oVI84dgjewkGE8QziYIiqI0ZRFWvgkV2XCtA3hUdT31aJUeId8mVIuHn3oT7uDbQSAC' \
			b'bjSu3VMw+aslUSEF4a/2I3/14LYTCvbfBM0Y5VG+IL3vI9rMp4qlYp3f4K4zMIQfWxIzDFvAsAUMW8CwBQzbIQyp4jeWIEjHwn5rJA03hBwo2ZDoCU2NEJP+Dcgp9yWWZj4qHC0iaF/gkp+H6zPQeDl3StENESEKXlAKF3l2zyFKn26CQQtQfRti4epd2AQ1' \
			b'DXQlo5+hrKluJ4zdRldGq7AUIAVFl/BzrhsNqCQqNlkbLIfckt6vEbwWg2sMrFJQ+YWA2tUj5jMYdWP4dD14NrwUzoA8+5kTgRMJ0+MlsuXA2e67+8BIzwghG3FIxzbRkAGL+rDGJr7cvseWXTwlnYW+yJppLvrWLi424mi+ZLsDkyXzszPmt6N9c2wLTO2V' \
			b'9sHa4X4bVJ0f2eFSG8yf/nNGGOd2X6IhWtsbo5Lxrg/YIBc+WscGWWSMrvRZGEo6frU4kj3CGDt6Gdhmk0tHh1z281F17QLbrA+0z+W2KcstsH3may6czUajfbLAKZezdmqXDgq7R1uld7Cl9moW2CtV/azNVv8KWhYauIpbsv4ILdnl/oAF1pvMNuSBJuJc' \
			b'0SN1v8nSNCOdmW3Ni/Ccyny3PlrJYMpXSjncfPsFmUSg1/iYXWKy5Fppe7ON7pXJI7e5x9fP1PjN3HRHbgWHDKmQHWWpEVZfsAmXvJmewWxPbq6RC/H/+K1jeuug1o2i5bfrOELqUs2Y2ljLW8vVv4LGPA154ydvW90+YP/RhT9g6+4gC+0ts9GXb5hH9Bk9' \
			b'hOemVrucvjuMrnkaOMsm112AyQV1oHUk6/oKjS8YWb2klbvH+B7EY3HyAqq5625D/YrXaopSQHsHd1Go4QuwQVWF8odC3oslzvX7nsIaqcvKPHarJOXjfvWNwm/b3Id1+rM9Kyl7dBF/ZztVJXYaKvxUptoc206LxmnMjc84RVdLc+92qvj3b+/XWDnj3SlM' \
			b'tf/B3oOepkoXjnAo6XzRx7FXXWSv3cnsNRlrre65iXsaY10NdWSkJOT7b/Ge0EaPYp+mqN1bn8M+9Wqfj8I+yepW+9xjn7bIPtU57NOs9vk47FOt9rnXPt0F+I2uz2P7CH1CxzQ1mkRxIb7ZA02r+peiwe8BGdRDEizj/q0saAcctOc1t21Tck7pmn2E5kfC' \
			b'3ljyyp7/mWfO74o9/IHXnNMUt0zO2/7wa0aT6i71Ibh0QtySUT1KLLJ9cFaJiY7D/8UPSU48mIh22V2ZyyeVLZuGQj+xSVYKOUyen94+DdDjp+dZh/SsJnvlJttM/gtMtnnkJtuIyTZ7TLarbtvJ8hyOjdORWZJNDg0S1igGNlmfYk7pXa/gE2XVJigimkym' \
			b'Gq/+wHrW1aJfpFv4dYstOpX0qfczjNY+mK8gnVXGRKqto8ZIuO9hYgKTIo006GPrYsGxxc9ZOguQ1f6YEqQsso0lj01M1xwkVrVFYUW86lDxunkJm4chZaJXpNlE0hFJx5e2PlTaWx65ufCbsgdsaQUtfTjOPhTjG2V7ksrkdTSG/8PnVVbD+LLw2XQIzRY/' \
			b'Vmb1RV7PFEkse2iECtulQHd2htzR2bhIp84xG2KrB2OZ7pU0qFh7Sj0TR3AILtPJEzn5tqjrTIPHdk9Dk5N11666e3rdZTU7qVftTLqLVZXwf0+6a/zTDf8UG7mpqdrNU7KmUP1hy17roIirTp9Bp7tr0en0f7k67bfr9JH6XI6t1vc9+TKqt2OPHbkADlB1' \
			b'9iCcp2Nkzm/Ddz9c3bEgnj1HMwRZ3aH2msfchq9mOx1V+5RsO9Rm2PLsrFCmVePPBHT2bt6jlvs7arnHNc6h5eVwn9Ptdl63j9uJfkT1vqhZ9QepeXf2ju4jN19oiVN7fyNIluo7afcWJ/qq3afTbvfQtdtxGR6AdvvZvo8TjIE6loJfynjCOyt6e29jlo6o' \
			b'7LRedXsZgwJLlH62R2pV+jMofXcNSs/hwSn9sGPwpANeV70XvaeRJvc/SPWorZtTjZI5sfabh6f9lzR94nALsFdmAe2FTYYoMQK7GsH9GMFFzFU4phG4h2sEfX/qWeb+rHYQ7ICq4bLm7RyzSXRp0+NKjMFXt45+KklGzVHtNvxFE76gH4YMxzHer+bDbYh2' \
			b'XTgYav+rm7B9suGfAiS9aGjNe6yXHdLlK+gqHmLJPynRr19P87+t/NiUH6yI23m61UYvvW5Qx7k/vojB7xROLyMr/ZqZ6xmaY2Cyv7SEr0tH+fI2Xd5OfmFswd2wYFM/O4/26ceo+EepvqL5FvTX0WLImDSf/u3sHy+xH77tDM/BU/xTWC4uvc1ZdnfJMiFj' \
			b'b64D9xb90YSL0THOoS/L4dzPqm3NZK2yjIakO/5obsi272gORthydpvd2TWN5JgeEnY4zHb3L1b2vwu390fhnPz2g5P5TzRImkYgh2P8I2/NrDDyH1frfzCNfyxNfhSNypN+CO0rem5O/4ivcTv3v+2c0v/dZ81fux18PzqHK689l66FCjz8j7PaXYSeqW6k' \
			b'a80J9Y0HU99foPHoKdLd/ZJcj6o+l87RM/ZUAUVRfVHoWe6PrZn1RSunqxAom7rqo0cK5uhXXBhQs/ruSsrms0hPSfx3C/yDsdsCSmRGukqvLUdnaa6x/gKVll50s0B5bKrRwSMGelc93dXnAuq6sF2+87G4TIfpBfjOIb7ib0+C4rlVlYPEXXXVAVV9hJeh' \
			b'0TN0oT776lghOqu2J0FRm1Wrq1tyPV5zQFUveu1y9qA3ly3q3VdBr+Lk4t0XyNW4JF06Qbyx02/IfxojkEK3KnyoBVdddYAvc9E734EKn1fjcuX31YlC3uewMyUkM36FfJxG0FZXHVDVe94pU/Xe3Q5iTS6zh7ka6aodgfrzdqdYGGKH3O5U4641lub6Pks9' \
			b'JLq66oCq3vM6e1GGQ93kFxcgxvW1merHVlcdUNX+uqtateTvdEur3FVXEHRNPopuRxJU/eL+2EuAZVddXoAY97yin0KMsR97VpRqgTjJgs8VyBynR8kYt5wBsRb24p5DsnNPkK0SNtWSQGO1FiY9IAyuPnsrjP3Z89J98bJ21cUHCFo9cEE31cUHCHrxG/TD' \
			b'H2vkump5wBja9F90csF1l99jNgUq0TyeSqSR0NcQUHGLX8OvoOJcdRUBFbdnzOtVVZyvriKg4vb0fl9VxTXVVQRUXHgJ11SqDgNyTBvjCvGO4iQ1OkYiwusR/YB6XsdBtJQgyJR+b5V+05FGtXe4Cf2K80zitsoCEupJQqooStxVedA1SE+/Z9nPfqAZQtJj' \
			b'S7+jlyvZLq0Itc0jWO1wck+cbDMz0UYrNBDo18BGqzFTJrC0Md+SbyXKZ8TPIF3r9CNHWpNYNQ0h+erm/wHlemNW'

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
		('SETMINUS',     fr'\\setminus(?!{_LETTERU})'),
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
		('ATTR',         fr'\.\s*(?:({_LETTERU}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}})'),
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
		('ignore',        r'\\[,:;]|\\?\s+|\\text\s*{\s*[^}]*\s*}'),
	])

	_PYGREEK_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.GREEK))) + ')'
	_PYMULTI_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.PY2TEXMULTI))) + ')'
	_VARPY_QUICK   = fr'(?:{_PYGREEK_QUICK}|{_LETTER})'
	_VAR_QUICK     = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK   = OrderedDict ([ # quick input mode different tokens
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
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
		('SETMINUS',     fr'\\setminus'),
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
	def expr_add_3         (self, expr_add, SETMINUS, expr_mul_exp):               return AST.flatcat ('+', expr_add, _expr_neg (expr_mul_exp))
	def expr_add_4         (self, expr_mul_exp):                                   return expr_mul_exp

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
	def expr_paren_3       (self, expr_frac):                                      return expr_frac

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

	def expr_curly_1       (self, LEFT, SLASHCURLYL, expr_commas, RIGHT, SLASHCURLYR): return _expr_curly (expr_commas, forceset = True)
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
					elif self.autocomplete and self.autocomplete [-1] == ' \\right':
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

		if pos == 1:
			if rule == ('expr_func', ('FUNC', 'expr_neg_func')):
				return self._insert_symbol (('PARENL', 'PARENR'))

			if rule == ('expr_paren', ('PARENL', 'expr_commas', 'PARENR')) and self.stack [-2].sym == 'expr_mul_imp' and \
					(self.stack [-2].red.is_attr or (self.stack [-2].red.is_var and self.stack [-2].red.var in self._USER_FUNCS)):
				return self._insert_symbol ('PARENR')

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
# 	p.set_user_funcs ({'f': 1})
# 	a = p.parse (r'f(')
# 	# a = sym.ast2spt (a)
# 	print (a)
