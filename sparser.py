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
			if len (e) != 1:
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
			b'eJztnWuP3TaShv/MAnEDOoB4ldjfnMTJGOtLxnGCHRhB4DjOINjEydqe2V0M9r8vq94iRd1a0nHfTrdguiVSlEQWWY+oKornwavP/u3tu58/qz774vmT58/i9smjr17GzTcPXzx69iTuPP762fMXj3784rsXT/4Wo1+9ePiFbJRsddx+/vjZ86dpq9IOH3n0' \
			b'9Y9fPPz20bey//ThS9n7vNv9vtv9BrtPHz/7jk759snDb//yebzLv1Nh8g4nc5kolne+ffmC/n73efz76Ok3L//27SO62ONnL7+Om2ffURG/f0h5njx+yjn5719fUK4nXP3nlPOr755RLT/nrF88f/r0YRLJi3S7F6k4tPPi8dd/oUs8+mv88/DpN/Hvl58/' \
			b'4UJS6rMvpdq093m3+323K9V+9OTbR5KShEYXeomCxAKwbB5+8+3L53Snl1zfR//xxZN0mGT/5ePvH39Jl/niy+cvWSp8+uNnXLxvnrBgH38FSdEJfLFOpJT5zev3bz/++Mf7H3/+6bcPH1+/j0lv/+fP9z9++Mefb3Pk3du///jLP9696Q7+FHd/f/3xxzd/' \
			b'/CZ77//4727vA1/5w9sPH97kvT/zXrrM65+63Y8f891+ef3mY9r/k6+K5F4Bfk+7v/2ad//ZFf9dl+HXdx//nvY/vn2f03//x28//vr7nyn65h/vf/vfFPn513+m3Z/ev37zn28/dkd++SXf7+2bQkL5uq8/lreIO/kWVPtc459/zrf49d0fRXHf/leucrx3' \
			b'lsSvb9+8zZHYau+6G/754eMfKZbPznf947c/3nWR339/3Yt8+OyH6tWDgzWVbc8q7ATaMZb+uMqqM4nGGO95ylbZujrYs14CYi6dF0/wKYl2OdcB1zDVA13FvwdVmTbunKVUScsJh4Z2lMYf18ajuGtKUr5Mol06UeOPk8LHA/GSlEVVD+gadBfcg1JCGVO1' \
			b'7FAa7QUqq2pTWZuzlCppOeGgFe/FatDpUWRWjtHtUHEWAh08K6Jpv0hX2By4Opr/cxOcIX5A0SQdN4n3l0RkUlzuIOX2OqdKmu+y1f2Eg8blY/00SyNm4D8uFkHLhbokaoIulXbjHnUDX5l4K1zW0Q7VSeGPwwmG6swnRIHGPCx3CCQm+CLSYEMJdCNqlcDN' \
			b'YmMTxL/IJ+kHq8dJXdTUoxycVERjOexEkh4nFVE9jvaSDgadq5buHMutIAdV8y5li4oX/+PuOmdIyV30oFkkuokHmkrrioXvK69YJiQ7adHpHKTrUaHWZYxt3M940MwL0v2mcnXqmjEPpysnWkNKGdsn1qRQnngwp3cpBimmS7FIsV2KQ4pLKQcFQFj8cS6X' \
			b'MSf5Mol2qQIaf6Icz866XcoTa6SKU2gXZFQ4IK1JfNNMSu0qzcrdMNQSJ1DEmIaUHLUsXJvULUqSr9KiE7jYSSI8fVKbMlkSDiCUqfHnICKkXcO6EXvOA6pQOJOYhxLHa8X/XeuScqKjcD+Tpm1TvWLiA9t2FaZoyFeNvZchoWP1UH3e87IHFNKOTjvI7ivk' \
			b'UVEUqikBShE8egL+FI+YICQ0Lf7w0wUliTHapb0mHTyTaIylA2dn8UH3qiaKxudRrLThBxB19yiTUEXxRW2ON2XpN6ZqbBVigq6CqULcd1XwVYh9L1B3d0SwytvKO+7lgYQa0Rk7cexlirpErGjVqqrVVRuv5qomXrapmrZqQtXWVRuPNpWiE+IZsULUMLFA' \
			b'lnSFHsPMNepJLInWVm28VR1PqeP96si+2C9U5KWPetpUvq0CxWOhIivrqlFVExWwpv9Rzw2BOmpH1IZInaj2sUf5mhTcxzNiDePp8T6xei3puqLbVPQ01D9UD2p6HL16YCw/lqL4eBOvHGVKT2w+GiVJyVGafFTx0VcM6TPGa9zs0l4h7QB5Wog5igeCbDAo' \
			b'UCL2xiJbUJzcILfWkDbagi7K5wZO3rv+EY0hvduEXYJHSjB1VPTQ4LFppGtaFmwpBVR+XOdU21zVsoZTdUOVYhGcRhFcfQ33UriXByw9aq1Eea3UWjElL//uWu6uwhVdXx4FCtVqAZ9WS7Vablx0ztgpc19E/8t97ZI7WU/VSg270paOjzYWQqxg1VSxuJXf' \
			b'CTBJAA2Vb9NAwewoPUqQcQzAklSk3aSJVE/KQRUnjVR7D5wTXLML7jjBtbvgjhNc2AV3zMOirfGwaGSgofanxZGSVEpG3hajNIt3QzLm0QukTkcxUG15c9eGaKbde89xvceKHsr7S50sCq1sYdbh8vA2vfZgrOfxvK2pfQoBZdHcj1eEBx7SCklI8h7qIbwG' \
			b'yY0Si44W0aatjJcd3h0d9NQ5SDbGauobUZBt1YbTE06sGPqKa+5OjdDeDu3r654S3IUKejxKPHdR1KKs1ynWCNoV2kEnZLMp2tFmW5XADyZZcl/IGGV/yBw5So5C0/Al6N07sE5kJCX4WXaRrbQ/BRIVe1TidpdN/z3V7P1orayiIPQO+uO6mQO19C7BYx+V' \
			b'zS66I0UX93fRHee81Xh0Bn5K7DKakpGR4UUA4qIc4mYX1IQeWpbUFb/QTcyEIbd8jUby/MJxXw1Sr2giQqz//au2vZ/Vxkvipds1lSCv5QHxfZFmq+9PbWkqDzexGPjnpxn+IHMSK5oPw6fAogZzteRoxZQN66E4oBhFNKcBN1LiUtDJWp7MbkqJ3Y1nHbFn' \
			b'C5bjBqaQpsWGOyV7DPG6z81F/i5qtTvZRmI9a+XZxpIc2DA9ZDSagFYnKfP2+srMpnBxgmg4QTScIJqbtpYRp0PvwGSh0A3eMbDCEB7Dq+FAfh9tYSKiaKPDo+9UPQ7cnU+6/O66FcxDwdr2hAX3oJVp8M6fcPcl3yaUsD3lWnh5eXLhpGuh5DGpT7kWAYMd' \
			b'K491L2Oe5Eajj6ziA5E28UlJm/iQNBjAmTO8HhuMuvbpacf4kiBiAxHHAyxbJAZIOhbSiD3IwB5kaGRjJTkKykwNyHDycEa9shPJ9F4nqQapBsNvg+E3D6jo7z4nfdYWBWOd382asz3dJFCY9Hqm5bWM3jJ2SlzocVBu71lzPasBPBtArAngIQDIr+3mzs5H' \
			b'tVzJO2mMMK083xgY99XCzoYVLfYNA/uGgX2DpJLeCXURcyaN2sbfT9PbOwYaMPXQ2yRtW4wCHcua3i4Mph0aTM6DQqVxn5Vxn03WNoxjLMYxFuMYiwGMlZGL3SfKDKAFEaeHoYz/OoukHLEswjtKr1gfOzF0jbWz6OkWPd0mS54VS5494feteA/RH5eGQ9Af' \
			b'B/1x0B/aBIe8USAOAnEQiNuHArNTM/QunVkTrkEHig9J6VYe3cqjW8VNLL7omkfORnI298VT9YoE0kAgDYMHz1GZmx2r1QycIiSeFoJscV6bsrb3SmrhHtVW3Z/ack8O8oFRLV8Y1fyorqtX8Z68ZgHZhmjdgiDgpGKjSJpuRqWCVw1z5tKNSXgsOQAbtaaq' \
			b'cb1IVo6kBMmA01m0hOSGiknr0VAFpODsz2UzZEyn7xJpxQAaCNOqQTQSprWGaPUhWnooFkaR45m+Y6Q1cmiBHPpCg4RPi4nQIh+0CAdJmT6dou+m6BMj+jaHPl+hb1foow9aoIMeIvSpGq2tQwvqkHubLKP0uTh9+Uwf8VJLkPmNHhq0GgytZ0JGWBrn17H1' \
			b'yGEZe4mu48iaJhqSSZZEyGtf2Sh0WiARayDSAme0cFVd0UJ2tMgXrYIWb3wI9L+pDrHQh1j4QywYFuKjZeEcr9Z1iE+zQyzMoaWFsmgpM16CjLayWlxLi5/VdLTmVcJ4sTy6gKIrxqTAEbolrfcVC32IgjgEKgud0PCahbICWCwH5Y7bVsoZVeXgG7kmL7RW' \
			b'U6koZ0yNCnGg5eICrRhGuajStKoarc0XMzd0J1rzjZYQoyXHaGVAK0sx0jaeF8V8aOkcqjGt/RjzxaY4xKY4NFwbg7XKaM0vWouQsH4grh9aSonZaYVIWizNa6wlGAwvX3eIGn4IJC8sO8fr7cWhxcHRbWhtQrp8TaKJBxr1Aw3qSFd6elIMM2a1pU4K0/R1' \
			b'Rm9XmxJKTCSMjmJx5xXJrVSmq1IkfZQyqRA2KJQjobihDjlOWqdHLmuSG+uSuyxtcihT7BUu/7tQq9xKvboqnfJHq1Xj16tW9S97ziuAnhMJfXseifN/PGJ7RSJoCz3DwxTPymKgjifmYN4HpoR0k7xX6l89VMHx832gjnmAkNWRntp4t4Cli8cUGGvgtTdp' \
			b'qh9oq+40NnvfCo8ca7ARLXaiyQ20mdbV62l0KDS5uUCD43H68DZpMn2rSh+qTmq0h1bTZ8z0zfJazaaZB1m7mxkNp3UwXaHlCppOTc1YVQOtJ6HxIqmV7MWrU+eOleON4o2WDfSdZq3VWetxXg4JAVDqjgFy0hIDwhwGgurCEAmDIowDV6XuLkDxKBK5mkCD' \
			b'd8ENPl6jxM6VJ0XBcj4+mVDCxamxweUKprBABSU2zCJEJCcgkdgQJ1LYqH6BC1JvoIqSAqLwE2iRewpcOG8o5D0AjTonosfmOueGi736nGAXe2fcGqKOydSpC/Dg6a5vMWxK0pSYUatJs1NmijIkLFYyGsogQoOKNKAoBhNyNMFF9UKGi+rDRY4uwWV2jNG7' \
			b'xxAuaiEQWbqICrmsvuLra8TKcT6zRTFb0mnUtwAWBbAogEUBLGoAFrUOLCJMAQtiQ7BIsmmlIJvAIiKTEk2ARSoKsCiApZDWJFjGPLHjUczpwmQnySeQRPPa59jQ3hxGcDRhRPdCxogeYARHFzGi5zBS3mOIEb0QGCM5wgNWlNWn6k4wRIMhcg71Kg2GaDBE' \
			b'gyEaDNF9huh1DBFJCkMQGzEEycQQvZkhIi8p0QRDRD7CEA2GdKJayRB3Dxmyv/fMccTjN050JXtzHMHRxBHfC5kjfsARHF3kiJ/jSHmPIUf8QmCO5Ah1AClrrm7iCB+vUQ7nypNqOSXgGLJyuwIkvg8Svw4kIkoBCWIjkCDZtFKQTSARgUmJJkAiAhKQeICk' \
			b'qPbGtxy/E2UnSiZKi58zghuqnScKjiaitL2QidIOiIKji0Rp54hS3mNIlHYhMFFyhDqAlNWn6maitEKUFkTpTqKu1YIoLYjSgigtiNL2idKuI4qIUoiC2IgoSDapIJuIIgKTEk0QRQQkRGlBlKLaG4nS7ETZiZKJEvBDY9RDeG+OKDiaiBJ6IRMlDIiCo4tE' \
			b'CXNEKe8xJEpYCEyUHCnK6lN1M1GCECWAKN1J1LUCiAKnDhekxgYnlEQJ64giohSiIDYiCpJNKwXZRBQRmJRogihSHyFKAFGKam8kSnux/+c2c6Xe0XJVaKEEGGRlL15dw+2j1QgwkkcAg1gOCTB6YJOVo0uA0XM22d49BoAZFGEyEGO6iPg6O2+P7myyWrw9' \
			b'GhbZ4iSWJzNGwyirYZTVMMrqvlFWrzPKJmmCMRIbMkaSaRGCzUbZJDMp0ZgxSUBgjIZRtqz2RsaEnTE7Y8aMoV8nhK5hjxhjwBgzZgzyJMb0Q2aMGTAGRxcZY+YYU95jyJhRKcaBGZMjJAkprk/1zowxwhgDxnQnkTwNGGPAGAPGGDDG9Blj1jFGpCmMQWzE' \
			b'GCQTY8xmxojMpEQTjBEBCWMMGFNUeyNjVL1DZofMGDK2wu/3VrIXsHEamwFkcDBBxvZChowdQAZHFyFj5yBT3mMIGbscGDI5QpKQ4vpU7wwZK5CxgEx3EsnTAjIWkLGAjAVkbB8ydh1kRJoCGcRGkEEyQcZuhozITEo0ARkRkEDGAjJFtbdCRu2z5XbaXECb' \
			b'hlqctQ57gRfKYto0TBv+DW/ZCHOQMzGn6YXMnMHsczm6yJxmjjnlPYbMWRGYOWWcRCIl9kkAGTuNYKcBdrqTao98AcekODU2OKHETrMOOyJQwQ5iI+wgmbDTbMaOlFNKNIEdkZFgpwF2impvxc4+SXfHzgXYoSaGtUb24tUNrDUG1hqDcY7phjqSU7CDWA4J' \
			b'O2Zgs5GjS9gxczab3j0G2BkUgRsvjArm6n5chVxknySQuGPEbmNgtylOipI1sNsY2G0M7DYGdhvTt9uYdXabJFFwR2JD7kgy6d9mu02Sm5RozJ0kI3DHwG5TVnsrd8zOnZ07F3BHUxOz1mGPuKPBHbih+Fs02Qh3cCxxR/dC5s5g4p0cXeTO3MS73j2G3NHL' \
			b'gbFTxgk7UmKfBJCxowU7mHxXnFR75As4hqy+xgYnlNhZN/8uCVSwg9gIO0gm9ds8/y6JTUo0gR2RkWAH8+/Kam/FzsRs3h07O3Yydgy1L2sd9gg7MBwbGI5po2Uj2EHOhJ1+yNgZmI/l6CJ25szHvXsMsTMqxTgwdso4YUdK7JMAMnbEgmxgQS5OIuzAgmxg' \
			b'QTawIBtYkE3fgmzWWZCTQAU7iI2wg2RSv80W5CQ2KdEEdkRGgh1YkMtqb8XOxATgHTs7djJ2LDUuax32AjZOY6N4o2Uj2EGWhB3bCxk7A4OyHF3EzpxBuXePIXbscmDslHEVcol9EkDGjtiUDWzKxUmEHdiUDWzKBjZlA5uy6duUzTqbchKoYAexEXaQTOq3' \
			b'2aacxCYlmsCOyEiwA5tyWe2t2JmdJVwuc3ALaXMbPl9qL4kz18kYmltCkzDskjHZU7OzLRV7xfS+tr/CgmRINmTfC9mGPPgKgTqmXvEZgp79DIGbr/s/MiT7hcBW5BwhQUiB06cI+BaBC5c+adLyMUK6Jz5qUvJVk5LPmpR816Tkw6bBRJz+Bwl8/RlbsghW' \
			b'bMmIzS3koDd/kcDiN7zU2dxUHBGUmJKpv5BwYx4YlTvp9bgTxXWO6ZE2bj1zZmLu8D682Yc3eXjTVAa+K9kLvPYVD2/guzLwXZnOdyU50/Cm6YU8vBn4ruTo4vBmznfVu8dweLMi8PCmjNPwRkrskwDy8EZ8Vwa+q+Kk2iNfwDEpTo0NTiiHN+t8V0mgMrxB' \
			b'bDS8QTKp32bfVRKblGhieCMykuENfFdltbcOb9rJpR5OjjzqQvisX/9h588cf2pqbl4DwlQSIQTVQFANBNVAUN0hCDkTgupeyAiqBwjC0UUE1bPrQbjiJkMG1cuhEeNOWVYVcql5SVYmUd2RSAZALIny9kyiGiSqQaIaJKpBorpPonodiUSuQiLERiRCMqlj' \
			b'vZlEUkAp0QSJkCGRqAaJimpvJVHYSbSTaAWJqB3h1mqwPDE8WxaeLYs3MAvPlu08W5JTSIRYDolEduDZkqNLJLJznq3ePQYgGhRhMjQw9/QuEwWTCu05g5IYQGTFv2Xh3yrOixK28G9Z+Lcs/FsW/i3b92/Zdf6tJFaASGJDEEly1Ea72b+VhCclGoNIMgiI' \
			b'LN68ympvBJHuTVXWJwuiI17G6NFpdxSt/8TTVAojgbihO8PbpeDtUvB2KXi7VOftktPSF5/9kL/4HHi75OjiF59z3q7ePYZffI5KMQ780WcZp14hJfZJBvm7T/F2KVptuUGpnCtPpv4Hr5eC10vB66Xg9VJ9r5da5/VKggWMJDb6/hPJ9P3nZq9XEp+UaAyj' \
			b'JCvASMHrVVZ7K4z2Kc07gS4aDDWVhVlI9mgkBLOQhVnIwixkO7OQ5EwjoaYX8khoYBaSo4sjoTmzUO8ew5HQisDDoDKuQi6xTwLIYyAxC1mYhYqTao98AcekODU2OKEcA60zCyWByhgIsdEYCMk0BtpsFkpikxJNjIFERjIGglmorPZW7Nz8lOYLf11gh8+t' \
			b'gE9bsQbrSvYIPi3g0wI+LeDTdvBBzgSfthcyfNoBfHB0eYHQwcxmdv/wmqVWKMQXYlC1Ywy1y4ExVMYJQ1J2n0SRMdQKhlpgqDuJMNQCQy0w1AJDLTDU9jHUrsOQiFYwhNgIQ0g2qSCbMISTvJRoAkMiI8FQCwwV1d6KoX2G8w6giwAUKosldmQPvyjDAAoA' \
			b'UACAQgcg5EwACr2QARQGAMLRxdFPmBv9lPcYYicsB8ZOGVddiX0SQMZOEOwEYKc7ibATgJ0A7ARgJwA7oY+dsA47IlDBDmIj7CDZtFKQTdgRsUmJJrAj9RHsBGCnqPZW7NzgesVXN8lHoLL4KyhXDI2jgHEZsCBZw4MlezPrccnR9KsodS/kn0gZuKzk6BIg' \
			b'3JzLavQzKfVCOPQiKuTy+VTF/q+owC11WPoZFbfO/ZRkBJ2X2FDnJTnqgdui7nLazK+opNpD1x3cToUgVq4mrPfZxPvI4iJYaGom1iTsxas7eJgEGQ4eJtd5mORYAofuhQyOgYdJji6CY87D1LvHECJ6OTBHyjihRErskwASSpz4lhx8S8VJUbAOviUH35KD' \
			b'b8nBt+T6viW3zreUBCqUQWxEGSQTZTb7lpLYpEQTtBEZCW3gWyqrvXVkMTGbeMfO7cKOeCxuFj/8C5usfdgj/MCr5OBVcvAquc6rJDkTfvoh42fgVZKji/iZ8yr17jHEz6gU48D4KeMq5BL7JICMH/EqOXiTipMIP/AmOXiTHLxJDt4k1/cmuXXepCRQwQ9i' \
			b'I/wgmfAj3qRUsdUQEuFJuSYgJBcUCMGnVFZ+K4RucJni/fXmyl5vbOUwGUT25l5vcDRhwvZCxsTgmyc5uoiJuW+eRmiwC4G5kCMEBSmfT1Xsv97Yla836z5jSjISzUdspPlIJs23W9Qdp8293kjtRdfx+VIhiLWvNxPrBu8qfvIq7skhxv0fe3MqjqNJxX0v' \
			b'ZBUffG8kRxdVfO5zo5GK+4XAKp4jpOJSvlzFvor7lSru16m4yEhUHLGRiiOZVNxvUXGcNqfiUntRcQ8V7wSxVsUnlu29LhU/7a8S75ytoqUGYZ3B3hwWcDRhoe2FjIWB61WOLmKhnXtBKO8xRES7EBgROUKIkLL6VN3xj6o5OFvTOfRmAE+rg6fVwdPq4Gl1' \
			b'fU+rW+dpTZIUeCA2ggeSTSrIJsOEyEtKNAERkY9ABJ7WQlQrIWImluXdIXIvIRKoNVirsDcHERxNEAm9kCEycJ/K0UWIzLlPe/cYQiQsBIZIjqiurD5VdwIicJ2mcwgi8Js6DDwc/KYOflPX95u6dX7TJEmBCGIjiCDZtFKQTRAReUmJJiAi9RGIwG9aiGot' \
			b'RCbmqO4QuY8QoXaAi1X2ZiAiRwUiiOWQIOIHLlY5ugQRP+di7d1jAJFBEcaBINJFVMhl9am6Y4h4+FzTOVGKnC3gACqYioPcBUT8OkdskiQgIrEhRCQ5ahgKsgUiqYBSojFEknwAEQ+HbCGqtRCZmHG6Q+ReQkRRO7BWYW8OIjiaIKJ6IUNEDSCCo4sQUXMQ' \
			b'Ke8xhIhaCAyRHCGISFl9qu4ERBQgIucQRLCaisdiKh5rqXgspTKwhXB0BUREkgIRxEYQQTJBRG2GiMhLSjQBEamoQEQBIp2o1kKE54tGKlRxzFn5KqpkFfrfE7uElduxfFOs5ma4rP+G+Ci+0JdK9LkZfb5E3zk1A+b4S17c6Rj2+A38MccwiKx+sU/z8ojU' \
			b'6+nZF3UIinpAM1EjihE2NB2ifH/xJ8mVMOV7IWNqYvEnv8Ia6+essb2bDDh1MFQ78m+QDSMMy9SdR7jKERVymT3Vnonlp4gFQ206rZaTAg6grr7GBrl7Px1L0iYs0cdG8S6NQRahWPAgmbfzNBOBC80Qm1oUysO06zetC0V9ipGGtaEOqROMmXYIuSyJa7D1' \
			b'FjLtcc2d0xRXdc4H+W/Df9tz1hE+TLDDglGxAV+NSDcHOKANLCtBNkmxC9w5DCwCU5OHOSWC1jhnBmjZhBXBydwacfSlx9qhy4WOGVOgwg/R0FyEhSUaJA4kxR9p/aLKr/O+JN0+yOzQNMboq+saf8pQG7eoYlLC2TXZWIqrhxFJ4ea0LekZKVlPt0hd3IS6' \
			b'qKvXmPyU97dYb9bojB7pzXqdWXiW8gPptihO8WAkId92BVqlPNRaIwXaojx+QnkuGE/PKc/cuHmN/rRj/anbS9Ahe816tEKHakoPnS7xT+a2N6FTZsUY9Bi9cpN6RUL8dN0iEV+zfq3RLbx0uKxj6cVjpGvN5nFdPfOaeqyulYpGr1Wx5sdNxLkNYz27Uuea' \
			b'I59da3XMdG97vH8Nz6+hjrFQ/WDqHBfmxp9jikW47gWsXqlv9fTzrPpX7DznsTn5Laq9gbeo/EwrbD6XOjgkgcayKUsDXH0Dg8VPecG6LIW7xoEiLCrF/0sfNGL8TSxzbP66gUHkUOkImasHkVHpQjiPpWClC9WrUzNb3OSrV6lN/iiNyprU1LdPkS7PVHGz' \
			b'b1mlgpC5ebOZovpXcx5RRyoSRXvDKkI9LfYwXsXt5LSFXnn10caK2/3cmR3ceXayHKiFTlJ3pPTuaDNFFPZNK42tYhlDuAHV8ZenPrQoY6zPPVUj6qTssjwo/jGP61Unf6lPI5IzxZpPVCy9SbHU1ehWe2mKtdmfXfqxP0W5zC14PuHneG5Ku+g4l+iSdAu/' \
			b'zHPE84o+Qv9ks3qAmn26gplNCqavRsFK7bqBd6RP1q77rFkDrVKjyWTXMgi8BKW6JIWymxTKXL1CmV2hTluhbsQicXsUym1SKHv1CmV3hTpthTL3W6H8TRsrTs+sd4/sEJejGjRD+hbNgZhzDVl/HpWY7d7NTWtFrAaseNenHoPZ8pdmvrtH6qJ4eSKy3F3j' \
			b'M8Vcjbnu2AdKe/WqM/s9y/TDpQ6D71Nu8CGz5bu2NXMXaJIea5C7/VqERRf7/9c+hDhv7wOPG/Ynbfv0bM2cca2gVajq6PHk9XnEED+drmHiwq5iJ6piYfR/vYqFu69iVlQsXKxiUTyv2mr49XfLytSyGpmRArH2QDN6n0Zz/72o3zbSFwd9UNWxfzWqmvzy' \
			b'WMs8Tu43WvrLbF/J/SQ1e+9z3HahPagtSMBDwTaOHvixVMeJCkARlGiww+gjZKem5Uc6zDLkDn55QqRCsi4lYbJVgbP5IySbuu9UtxUJ62MlPCPkkxG06sA1EnbCz1UI3Bwp8LmnZid/flBueEhubaNND7+ph156I3NX0J5c2f7/3sOpaGOx0m16EG3vCdse' \
			b'MFMdRt6EYnH7zw871YMuz2DwSQa0Vet2XMf869m3/7l+Nzdy4q5xya/4n24JW7HmxVVZvWa66cSYx4TzOO7kPuv2Pnv5fZZa7LqsUpfaZWmlj/YWdljtzvnXq23suPT1p6vj1nIH9nsHvoIOHE61A3M4qQ7c9DvwFXga7lcfpj57E+6BezF2oA7bnlCHvemv' \
			b'DVOn1WzpJVPUig5sb00HpqIcx+Frc/rSnS7owZonS8RDk95fFTFMbR1s3LIXON5BevdV+n7vXgef69TUuDftuL1cMt/AfIYNdI6lf8ULxsY2gMFJc7LiX/ZSASYexatj8gEd87WUGtv0h7O4fXDgRZWxbiEt8NBUWLGs/GZcsa1I0dpCsZ55pQbqqWb0EXho' \
			b'6E4HvfaysXBT//gi8rPc48vIcqlq4nqG3Fem+Nd9td50qXx5W15eN6M1GS+8GykQYYNmv+SZFVh/UNYBpB+OrvAvRFLIdMLuv534x+vE0JoT8Th/gyuzEINOy7Vwyd0nlpy0frHw8fSV/8irN/jHxfTbijmzQOVcSWnSUVfamPWCf+SHnD9KnsC45TI3vTL7' \
			b'mWLzIkPyqxHZHry4jG9eZpPX2OSlNXmNk0aW0Yz35OUznSybGabrnZezbIulKZsqLz/JK8DklV9+oGcc/sVe1Pb+cQJNRipCO/lvkGnqxOHpo5yD67C422vsIqH6pH9c3nDN3UP1uwj/ouVVdRMaCF1b8KGIEL0/9ZLcPKq+xv5Ema4woEKqrBCvXHrZ3a6+' \
			b'BT2vqXLAT7+WKZcQ7OVebjqgwfSaHihL3i7xYLYfimS7vkiiXAo0BF7OZNup1GBzBNU0E/1S8W8KX13v9DfWQfl1pxfwk8Tj9MsK9IZ3ZVdHE64a/67sqWihDf3VVZcV0jvxhblQY3e/Om1b3aGAFvSrxl8bu6000LrOOyXoUOUQ39jK6NEhWXcWMg5sMSyj' \
			b'5l71cjLQ3Z2AFmxvYy8nM+gNB0gn3K/+3VZ3KMA4WN/K/h2qmw6QztQr393t3+RUuTsBLaivsH8nq+Gk8P2Kfk695WoCNf5EauwCM2dAWvfrVZLch3cnoAXtJqvo5Xb5sfwvkL2tFgP5H9fkWxl6l5u8NkR4v15NyXt+dwJa0N+VFox3Vo1a25K+Ormg6LP7' \
			b'cFEWtOg2X+DNYY0mn9yuAPmte429BfJz1S0LkN91OxuvwxdNnx6vDpga1f3fdPLsVdZfcTIHpqase4U9rbahWWunF9Ae6i62B77wPLGA9lj3Cnxi7WGrEwxoD3MX28NVJxjQHvSzqg1NShJ9cSku7UU/hUdzennikqPVlpAex6Rlo0VBUoZWltI1WLCwlYu2' \
			b'k5lDVQRkDKOM1Cw0M4PXQRz8Dxjf2XL6KX33LG5WWh+/7EAXdoTQ8ORV358Cnacrj6cq6xqjc1osfPA5tuJfs+OpOXRLvlXqb7AAx/6Dkw1NmWjJd0dzZn84+3+FY/rx'

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
		('EMPTYSET',     fr'\\emptyset'),
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
	_AUTOCOMPLETE_SUBSTITUTE = { # autocomplete means autocomplete AST tree so it can be rendered, not necessarily expression
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

	_AUTOCOMPLETE_CLOSE = {
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
# 	a = p.parse (r'\left\{1')
# 	# a = sym.ast2spt (a)
# 	print (a)
