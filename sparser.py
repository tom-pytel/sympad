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

def _expr_mul_exp (lhs, rhs): # isolate explicit multiplication so it doesn't trigger implicit mul grammar rewriting
	if lhs.is_curly:
		lhs = lhs.curly

	if rhs.is_mul:
		return AST ('*', (('{', AST.flatcat ('*', lhs, rhs.mul [0])), *rhs.mul [1:]))
	else:
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

	while 1:
		if last.is_mul:
			last, wrapl = last.mul [-1], lambda ast, last = last: AST ('*', last.mul [:-1] + (ast,))
		elif last.is_pow:
			last, wrapl = last.exp, lambda ast, last = last, wrapl = wrapl: wrapl (AST ('^', last.base, ast))

		elif last.is_minus:
			last, neg = last.strip_minus (retneg = True)
			wrapl     = lambda ast, last = last, wrapl = wrapl, neg = neg: wrapl (neg (ast))

		else:
			break

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

def _expr_subs (expr_commas, subsvars):
	if len (subsvars) == 1:
		return AST ('func', 'Subs', (expr_commas, subsvars [0] [0], subsvars [0] [1]))
	else:
		return AST ('func', 'Subs', (expr_commas, ('(', (',', tuple (sv [0] for sv in subsvars))), ('(', (',', tuple (sv [1] for sv in subsvars)))))

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
			if len (e [0].brack) == 1:
				return AST ('vec', tuple (c.brack [0] for c in e))
			else:
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
			b'eJztXf+P3LZy/2cKPB+gA1aUSJH+zXGcV6O2k8bJQwsjCBzHrwiaxKmdpC0e+r+Xn/kMJUor7Up7u3t3e8LxlhI1EofDmY/4ZUg9evOXf3r/649/Kf7y9MsXX76K8YtnX3wTo6+efP3s1Yt48MXXT55qVGpsYvzZ81dfvkxxmQ6MPuDzL/GMV/L72bO/fv/0' \
			b'yetnr/X45ZOU+ll3+Lfu8Csevn7x5PU/fxZz+xdw0R5I8tNvv37x7zhrD15/8zV+v/0s/j57+dU3//76mXDwLXj82xNcfPn81bfg4fmrb/4KNp+/lDvk91+/BvULKf+XuPrFt69Q6s/kzqdfvnz5JMkECV8//+s/f5Oy/zqxh4Nn/xp/nrz8Kv5+/tkLYRap' \
			b'rz7XYuPos+7wb92hFvvZi9fPNCUJDQ/6hoxEBkD08slXr7/5Ejl9I+V+9m9PX6TLqIvPn//t+ed4zFNWhN7+1QsRQBRNksW/vX72VAg+f/7FF6AXzr999VxU4cmrzyEvXPgS90uWUcZlrx5U8DGPp/8SDz/98cOnP99+/PRndvwpHr97+/H9799/+Pj9jz/8' \
			b'/On3tx+zy/EwRm+F7P3//Pbx+09//Pb+Yzr59f1/fP/3P3591138IR7+8vb37999+FmPPn747+6IuX16/+nTu/bot/YoPebtD93h77+3uf397bvf0/Fv8lQm9xj4JR3+/FN7+NOvv/9HOv7lj5+//+mX39Lpjz/92R3+/e9ZwdLhn2+74nZPx2PiQTr9/f3H' \
			b'9tLbH39Mh+/++Pjz/6aT//n0vuP/h49v3/3n+/b0U575n+/b8vzx608ffm3zfNvSv+tKIKJrOfzQPfKPTIq/tiz98NOvH1pWP3Syjfy0sv3p/bv37UnUjYyD3z79/iGdvf8vPWpZ+fBzx+27D7/88rZ38ukv3xVvHl1bU9ThqpADu8FBXeInJpsrPY1nclTh' \
			b'p5CEq14Cz0y6L16vUhIOheraSrwpHpmiiqdlUTXx4CqlalqbcN3gwNT8sb64Nu4qTzJuK8mGPAmH8ag0/HHIgI+PZziMR1Xgj2Vh41HMW0iiFJpIVeH/KqX4/CxojCTkWKJopU9FC1cpVdPahGsjN5Q2XoKEyqL2V5pyXUq5S4cfXzhwqhedHIJLEWh8DlnR' \
			b'03ScpZeMrqWoRv4rmy4bHOC5ms5MInOaSKJKChW0UC60qZrmO7JNP+HaSI1XMbkiIyV/LFhQeXdJqM4uFYdQyvjvCmgDa9XiABSeP1ZLGgVcSXXE6kQ1o1IokJhgsxPHCAm4L0o58pfqJwqK3Gv6dT2SlJ2W2xRl/xS122wnhe2k7LTaPu3dcF2JilSQeaMZ' \
			b'QPGp2ym5O72uqOrRSIwvjClQU/HI4cYCsjOs1gkKgQY/kzBWY5/wuhI1gD43hW2VMxZDdLls1GpgaXUEkyozHlxs07uUmil1l2KZYrsUxxSXUq5L0Q/j+GNdy2Ob1ORJOEQBDH+iHK+uukPQRM0y2VNiDVTET88LWmE1dJNAFKUmmqmMQ1HlQqwuI1VUbvjj' \
			b'YOq0hXIjhyI9IGdCFxYspjElnV4L114fE8ViC+gHL+fJmhDPpVgNf6IiXel5NCrhbcMfB2QgS1LnfCOAJ4NM9cyxTgEPmxbik57YFh0EVYkO0cKj6BLFRpRHtFkZsUl6NUy7swOcRvKUdURwglykN0175PXIlOnApANin1eYBVxtrjQJh6CKGi5MRqh7JCrU' \
			b'6iUY5CMNf9ymtTgIhNVZO/5kb0ynYFxb/sgbkrVTWznEUZ0uXulpPEsXiIN4O20osypJFcbFV7jFK8HW6QHx9JrisXW6IKSalO7asNCA28hubB682QAV43nNqowgEFWwQp3GiolQFMW+gVE3rmiaIvgihKLcRETdlPE/2vWmihUDeLdiYCHeEpW9lAqvotYX' \
			b'Ua4w/qguJV6pVRGivkTBhyKibYTTxhdNKPym8GXhTeHjSy3eWxrENv67mAf+41PlHRJtqZR/j0JGNBFcALpEe4s4EYGhRJ6SaWQ2irCM/Pi68LbwkT08NJ6EIsRiO1hPtOCoX74pfFSUUES5N5EvUzRV0dRFE2+Ib/Ey5hBBMrZAnBhLfHFHpYptjmht0Zwd' \
			b'bCOyGXnYRGFEQK3wVkXuKHnM87vi0QYv7DePosihW7WcPopyL2NdPIrC51XDZL7dYx3g6hs0n+TcIlpr6YS1FFgPltUTxcoKaJycIxNUV9OQLEi1PWoYGcuqZR3ioXJvkGeupna+ShTJoX5EfFIXqU5oWCEZlhXD6slRJUjZjUmN0mql1JPOiEQoiMiVVaWx' \
			b'9ox5OlXUhuVvtNxG5HK6fE3NfI05cT6sz1LhUzJabe2MtgaZryI/M7wZhbe6XkV/ZtFT2yOgCvBQGBRDW2gtbCpjXq62DOdnPqv6vLrP8xoK6XUgOB1vKWJpi8j5qp5HVU+jzddKexfa+jEmvfbdChhnfj02UiUlenToxaELh2pBRw+1FSWyCvyoAvebVeDn' \
			b'FXi5Cvy8AjerwM/5VvWV9i5Tb3OThg9KDvmsL9Rzdn5cGtvRMQ2jY6imSdXE4bhSa4tjpyiW1FldrVV23iqrrVYMB1E9K8SnCvHSQnpgPSK5CLUsVVnLoNrMNrunrILVVMospI4/r9Z8Ru2TavMZXpIvVHBeh/ocy9qwtbcBx2Hta2NuQkcoGg55N0TBptaZ' \
			b'C1WoUgfES323WaqhpVQdpQpZQphRmiHmYO6vVKK+0K6cubySsYYdIcLZnkFcVEGJek7gjaXJy3efS6YvgU090E5pZG5oszaN4lht2ARt93Qzy4ZTymadJD5tDyxK13CafhX1aduOcDDSCfkYrzI9zpikW/X21DKOAjRrN/O8ai0ihxvOKvnzSr42q8jP7Xax' \
			b'WUV+ZtfAwKYIpGfUqSzGq4iP+daUlglFsjpXzOw9WmkjnymzEV9X+BlatQ3pfK41N1OYRpDkhO6R7KeWfFnAVQ9RLfoCFybFM44tT/oyf6eOz1wWJEMNvMgbSKHDsryt9VuXfFcV2KECJetolc2I9srLAB401FNdFVHqagiZ9OY0rC6bkOlvUVd1gPLUe0+9' \
			b'9yYpPN8yq6i76SiTANwIgq8yEbWCKB5u8euHXXz7gIsPLwnBA08leFCFfwPfhAdXavhhSJXXDVuJ0ta77BI3LLELbIb3pt0abTOPexHJBOtVuxbjFt7Ym9DO8xvO8xvO8xtpAZXa2LE6KLp6fp95uMhttAJEue795HtJC7iActhbMtgyrcUsL0CQj4JRP6zy' \
			b'AtQbbkF8E1QXURrtzLn6IkrjtDTNJZQGjBl68xg68ajTDrYswQv5SrY+QRTfwxUH5qorjrxWHA5Zvf/PuabOithrVk3JqokSrdJcUKVzQdWVzmBU3Up7jM3rKSKj1PqUkqc1aYzWszbkZG5pXSF57BkmgcZHAimrZI/rFKdK3a42xVGVrZdBJ0QRrEoDukYH' \
			b'cmU8doWvUzgKmLAq+9GXhFHXPQHcm/Q2UPBPS5JKvjw4rF7tGE2o+JzBypiyHk+2I8kYsdPUiqmVDuZUF74k5A2GqqrLHqqSMapqnZdhC1pnoRu+XhoqfiOK3/by5VqJ+Wt1kmDrWeYUv5OFLmyB1TozznZB4Eyho107PtnRpFyTmuO1NsfrNDvJZmLNZmLN' \
			b'ZmKd2of16rd8rM1XNhQ5O0mpEaFt6nbu12jzomYFXTb0xXLV0++VhtoYC1zTQuo0Niw31aZd/FVfpebZfe9gx7yt2qdNjU3ap6V9Wtono5Ixz0VglgKzFJhdW05H3y9MZDxc5EQX4lXWxwRMqybgsTM2d8dzaENElrHxaPdyjJk7qr2j2oOsaKvLPbi50FKH' \
			b'e/BMxQeJK90HVPZtpeCahyacN9CThnrSyPuEvoHtwuIkMc/3M52tsMMt9r7Fxrd12SkfROipe57P9Cpofb3rPKvumyv3S6Z1WudcYa/+B1cF9cMrtWhFnbTCqDaYq1yZ4GVKNZIYBByX3RRvIq3sPYdRVew/hxwEyK2+NWJ+WgoH7vHC4Aw5p80zNilvvqso' \
			b'plwanYTlwxRRsIOq4OsNtWfkFeb1JVTzBYT3DcbzBai92kw8x36P2PoB+z5g0wfs94CdirFNMVYHYxE/VvBj+T7Wu2OxO1aHY004Fk9j5TQ2TMAWAdgeANLCzsbYzhh+v5hawPZZ2NEJmwyhsjDKgCEGbEiBpjT2X0CFYAtd7CoL3rEyYoMNy2OlY1EEOlXo' \
			b'UEF1RKYxDVLFdz1Q63ALBizAETkK08DjBEpkfawpfpME35WQvfUL2SU+yAbz8mmPBnu1b7AB/QY7n8czbPcf5KMIhXyaQr74YEARtfA6IBX798djj6tCYrAJ/wY34XEG+9LjSxJIlc3g5RklviVhcB9ywHVkEbCDuuNG9lEa11Ga1418hiI+2Mmu+1Z2bpe9' \
			b'9PHhCX6mIaZh13rsqF+xKB5PiLk1G2XYCdPILF7F10Gwm798L2DDDzDI5vSyf7/s8R5vBTHY3OC5rpAd31ECU/JLGdhfHsWrJA/sXh+JGmQcEzzKhqdu5JsEUsL0XRQ8B5vWx+OoA9fe8mMUVr6vIZ/hQL3EB+DjAdhiH59gkU9FxNxcYEYB++3jTskE/9jG' \
			b'HkIT+SIVyQ3qNT6iqb+D0cJUe2ZaTltq3eFIz2TrztmlZ7juOLY7wLTdplzOM+d7YcrlQnMWgW1ZsJ1hw1aoYqZ225JtZ8t2zJrtqexZmKpqifm316rtbLu+PzaNzJbZdfGP+jHg3D4GoDcuRtX/SbPxDUTkk5G3napGWx7atOjbObpzpZh6cl5Tj7aQDL7u' \
			b'NYv2W3vZGTxbQaNtKBj/VoNGR2EbbY5xAAXGhN3m0ZYCcukmJW37Rts2XeczAwxZlJBAI5/n147bWFsa25oJoNgBqNQEEwGRAYCgrYd9lFoAQffZ9oFEQGQHgGD3LmxLBa+mfWCCgdu9gBLrFzNWAiq1AstmAC6RFoveWpAppYEK66MybtAIBq5I5CRCJ9wL' \
			b'uLTUGmOcoJFDjCFuegEwQ2In6IJjRZbQzAcX0MbcEeXwEs/bsAU15XQIWjKbjgACaJw3kwGwJBGRyUtmUlygE2kkUUsWDJnSyDLSUmeohQcArIBRA3xSCSo4JXnmECXoNA5MHeMY798PUZQKQEq438Yozd9qLXitvwyqNL8WsGx4jJdCNMnHVBbvHwMvow4/' \
			b'BiJGHX4cSwcUq1oUS/0kNlW0nXL3wYvIRRkcG7lW1JpArRK6Arv1Gx6hSZRaQ9oSaomUhOc4NKFoTzTJV0qsYFW2YMV754GVPEleyD2w6uW0BVblrgCkEpalqILTO4h9YJT3jLiZmWBVkoiWSnYBE6CSiBk5LXEOVOU0UKlAFaiUi5lA1fE9E6hUgMrRCFCp' \
			b'yLQGvJY2Ayql2AKqaXyqB62sewpOa5vqjOiEgtNW6wloShQbxtAtJgGa6l4QaKozaKo7aKoXQFNNaKoH0JTntAVN9a4g0FS3LahdlD4wIi5RKkxyWS4EpprAVBOYagJTTWCqB8BUTwOTilOBSdmYC0wdR/OAScWnHI0AkwpM5e+1tDkwkeKQFpRdEWpFqIUI' \
			b'hQLRat0EQiWKDWPoFpOAUK4XBKFchlCuQ6gFw0jyJC9RD6HynLYQyu0KglCuQ6gdlD4wUoRyilCOCNWSlRoHSs5pxGyc0uQI5aYRSsWpCKVszEWojqN5CKXiU45GEEoFpvL3WtocoUhxCEK5FaFWhFqIUGCWVttMIFSi2DCGbjEJCNX0giBUkyFU0yHUgrGo' \
			b'kmNR5WAsqpfTFkI1u4IgVNMh1A5KHxgpQjWKUA0RqiUrtUyBknMaMRun5c0RqplGKBWnIpSyMRehOo7mIZSKTzkaQSgVmMrfa2lzhCLFIQjVTI+l3xucalaouh2oAhM030CoQmwbRhlgJToSCGAxyQQ9aoMAVsgAK3SAFRYAFifmEPUAK89pC7C2mBnyBswK' \
			b'HWbtoPQaKWYFxaxAzGrJSi1WoAidRszGaZFzzArTmKUSVczS/OdiVsfRPMzSsihHI5ilAtMq8FraHLNIcQhm+RWzVsw6ELPwEA6gGx09R0x3tByzWjoSiHMak5Bl2QvALJONoZtuDN0sGEM3HEM3gzH0Xk5DzBpwsh2AWaZsMWsXpQ+MiFkUD5NclpFgluEg' \
			b'uuEguuEguuEguhkMopvpQfQkUWJWYmMmZmUczcKsJEHlaBuzksC0CryWNsMspTgEs8KKWStmHYpZeADN1yhmGWKW6WNWoiOBYBaTkKXpBcEsk2GW6TDLLMAsQ8wyA8zKc9rCLLMnCGaZDrN2UPrASDHLKGYZYlZLVmqxgnKkEbNxWuQcs8w0ZqlEFbOUjbmY' \
			b'1XE0D7OUUeVoBLNUYFoFXkubYxYpDsGscrM6Wq3odWP0wkUask4KIsblWtBLwIs06pyrE4RGJwjTxaBHbRAMyyYITTdBaBZMEBpOEJrBBGEvpy0Mq/cEwTBl3KTSTxL7wEhhTKcJDacJO7JSSxYoS6eRZaSlzmFsepow8aYwpmzMhbGOo3kwpkJUjkZgTGWm' \
			b'teC1tDmMkeIgGCsJY6pKVmCKGNUHKKCT24MkMCeYP0y3NVGappgQTQRqH4qzBPF+Xz1iV6C+MVBDF9g1rrRrXLFrXLFrjCg+XKKqaKlJBqDWJFWrLACoq6yDXHUd5GpBB7liB7kadJB7OQ2BesDJdgBQJ8ZNKv0ksQ+MCNSV9pEr9pE7slJLFihLp5FlpKXO' \
			b'gLqa7iMn3gjUiY2ZQJ1xNAuokxCVo22gTjLTWvBa2gyoleIgoK5WGFth7MYwZqEFYsi6ZAgxYMwSxixhzBLGEjXJBMaYBLWyvSAwZjMY65YM8d6ZMGYJY3YAY3lOWzDW5wQ1OWTOtkcJx+xkEByzHY5ZxTGuO+rISi1aoDCdRsqjFjvHMTuNY8qb4piyMRfH' \
			b'Oo7m4ZhyqByN4JjKTKvBa2lzHCPFQTg2dJ1dcWzFseU45qACYsjqqoYYOOaIYxz4k6gqWmqSCY4pTdCjNgiOZW5rVee2Vi1wW6votlYN3NZ6OW3hmNsTBMaUcZNKP0nsAyOFMXVeq+i81pGVWrJAWTqNLCOlyWFs2nkt8aYwpmzMhbGOo3kwpkJUjkZgTGWm' \
			b'teC1tDmMkeIgGBv6164wtsLYchhrUP9iyOrPhtgy1YpyCIw1hLFETTKBMSZBrZpeEBjLfNuqzretWuDbVtG3rRr4tvVy2oKxZk8QGFPGTSr9JLEPjBTG1MOtoodbR1ZqyQJl6TSyjLTUOYxNe7gl3hTGlI25MNZxNA/GVIjK0QiMqcy0FryWNocxUhwEY0Mn' \
			b'3BXGVhhbDmMelS+G7BXGuFy84nLxisvFKy4Xb6lJJjDGJKiV7wWBMZ/BWLexDO+dCWOeMDbYjaKX0xaM+T1BYEwZN6n0k8Q+MFIY0+XiknGWF2HME8Y8YcwTxjxhzA9gzE/DmPKmMKZszIWxjqN5MKZCVI5GYExlprWQSpvDmF46BMZ2eOquMLbC2DwYQ51z' \
			b'jL/WMf6aY/w1x/hrjvHXHONvqUkGGNMkE/SoDYCxOhvjr7sx/nrBGH/NMf56MMbfy2kIYwNOtgNgLDFuUukniX1gRBirdYy/5hh/R1ZqyQJl6TSyjLTUGYzV02P8iTfCWGJjJoxlHM2CsSRE5WgbxpLMtBa8ljaDMaU4CMb89rYX9xrJfB/MTrAXxopnO5pl' \
			b'NdRB9sMoeYSWGf1LKvqXVPQvqehf0t5AMmmZ6cWgR22QllnmX1J1/iXVAv+Siv4l1cC/pKzKLKutplm9J3idulTmRQDSQJu+RRponZtJpW4mFd1MOrJSCxgMr2lkGWnh8wbatJtJYk8baMrG3AZax9G8BpqKUjkaaaCRwGpleC1t3kAjxUHIFlZkW5HteC01' \
			b'hzoXZDM82si2vdJY4wxAzRmAmjMA7Q0kk8aa0gQ9aoM01rIZgLqbAagXzADUnAGoBzMAvZy2GmtuT/B0AE68S/mlyTZ9izTZunmAWucBas4DdGSlli9Qok4jy0hp8ibb9DxAYk+bbMrG3CZbx9G8JpuKUjkaabKRwGpdeC1t3mQjxSHAZlY34HE804+PPVxc' \
			b'c+PYhp2297sFNwV3XmWEvDkvYDgvYDgvYDgv0FKTTNyCmYTMm14Qt+BsXsB08wJmwbyA4byAGcwL9HLacgtu9gRxC1bGTSr9JLEPjNQtOK18l9WiLKPL8qR7MOcHDOcHDOcHDOcHzGB+wEzPDyQe1T1Y2ZnrHtxxNM89WIWpHI24B1dJTuIi3KiLcKrP3E2Y' \
			b'VAfBXLnC3Npsu2mzDRVLw7a6VstyrZblWi1E8eESVUVLTTLAmibFjHnUBsCazVZs2W7Fll2wYstyxZYdrNjq5bS1g7XZEwBrifG29JPEPjAirFldtGW5aKsjK7VkQZnSyDLSUmdwZqcXbSXeCGeJjZlwlnE0C86SEJWjbThLMtNa8FraDMaU4iAYu1trAba+' \
			b'FLKC2UnATFZqn2T5lisM+6FGO6GGnVDDTqhhJ9SwE9pSk0zaaUoT9KgN0k7LOqGm64SaBZ1Qw05oqQ01tMqBaqXsdF8mlkrNYKvF5vYEabFpEUySwySxD4y0xaYdUcOOaEdWahkDpeo0soyUJm+pTXdEE2/aUlM25rbUOo7mtdQcW/3sjJrxzmiSm/AmLbVh' \
			b'Z1QpDoK3dY3AwwK207TSKlSstFMqbaXxoyISOYnQSqvYSkvUJJNWGpPQSqt6QVppVdZKq7pWWrWglVaxlVYNWml5TluttGpPkFaaMm5S6SeJfWCkrbRKW2kVW2mdVLRkgbJ0GllGWuq8lVZNt9KUN22lKRtzW2kdR/NaaSpE5WiklaYy01rwWtq8lUaKg2Bs' \
			b'XSKwwtjNYcyiSsWQdamT5VIny6VOlkudLJc6tdQkExhjEmDM9oLAWLbUyXZLneyCpU6WS53sYKlTL6ctGLN7wnV3lGBsB7EPjBTGdKWT5UqnjqzUkgXK0mmkLGqpcxibXumUeFMYUzbmwljH0TwYUw6VoxEYU5lpLXgtbQ5jpDgIxtYlAhcEYxxWPj6cmQlI' \
			b'cwNYczm0OdSxGLd2Oy27nZbdTt32yLLb2VKTTKBNaYIetUGgLet22q7baRd0Oy27nXYw99nLaQva3J5wrarddTZ3EfvASKFNO5uWnc2OrNSSBcrSaWQZKU0ObdOdzcSbQpuyMRfaOo427aP2A5yKUvkaATh9UPvIxmuxFeMkLZPkYUh35K287dkB7mRbt90W' \
			b'rJW7oe0srTNsKQMFqPZ5cwRUs7gx6Fa5w129W4oNY7hvMMkEPWqDuG/km+TGuqu7jXLrBRvlpk9Y1sOdcqVKu/9tP44trnocwoOj2yp3FyVeQfr9yzLta073Dd0tN3EgWqrrn0pdAFXqCqhSl0CVwzVQ9fSOuUm86sKh3AzAjCyNAxqgop69Z65UkKedTayD' \
			b'SrLT6pDISA6RbNBqU9oWy6IuPOa+nfYxN7nssGu4dOCG2HUocJ0ZrFqgcsXub+ieq411W91E1AGdQ105Dj4txYZxWaakmJkrewHg4zJHf9c5+rsFjv6Ojv5u4Oi/hTOD3IfMRI1znVv/LkofGLG11JZ11nd23bTvfpITUSTlNbNJlJVjH3wo3Y4v6qYnqVC9' \
			b'VkeGGUqx5yNwAhnDPbZXyHhYkFFh6lZMqpqAjESxYQzIYBIgo+oFgYxsUNx1g+JuwaC446C4q/ZBRrUrCGR0Q+C7KH1glENGNRcypse5k5wUMjSvuZDRlWMvZJBuF2Tok1SoXqsjhwxSzIGM4RbXK2Q8LMiw8PMQk7ITkJEoNowBGUwCZNheEMjIBqBdNwDt' \
			b'FgxAOw5AO7sPMuyuIJDRDTfvovSBUQ4Zdi5kTI8pJzkpZGhecyGjK8deyCDdLsjQJ6lQvVZHDhmkmAEZ1dCz/JYgYx1RuR/zXagn+oy7ZgJiEsWGMSCGSYCYphcEYjI/cdf5ibsFfuKOfuJu4Cfey2kLbppdQeCm8xDfRekDowxuZOzE0Tc8iUOLFCg4pxFz' \
			b'cVrcHIimHcOTNBWIlIu5QNTyPW/IJElPORoBI5WXit9raXMwIsWC715XQz/wFZRWUNoFSr5w3BnG+QlQShQbxgAlJgGUfC8IKGW7wbhuNxi3YDcYx91g3GA3mF5OW6DkdwUBpW4fmF2UPjDaAiXuBJPEoUUKFJzTiLk4LW4OStPbwCRpKigpF3NBqb1/Jiip' \
			b'9JSjEVBSean4U2lzUNJLC0Bp6NW9gtIKSrtAKaCSxFAn5ptaig1jgBKTTNCjNggoZfNNrptrcgvmmhynmtxgqqmX0xYobTHTIwcoddNMuyi9RlugxFmmJA4tUqDgnEbMxWlxc1Canl5K0lRQ0uznglJ7x0xQ0oIoRyOgpPJS8XstbQ5KpFgCSkNf7BWUVlDa' \
			b'AUqoHjE9RiOg1FJoHPVKk0zQozYAlEhMUMKxghLvnQdK8iQvUQ5KvZyGoNTsDAAlYdmksk5S+sBoCEqSaUtVapECBec0Yi5Oi5uBktCOg1KSJkEpcTETlDq+54FSkp5ytA1KSV4qfq+lzUBJKZaAknhWR6ApImwUUTgRnkK2JUulMFX6hFTVGFhtEl5VY5C1' \
			b'SahVndiZp5kBX3URrfkU27McgGOom1j+MgqgtKbDtVjwEr4cgm9GMa6ewLlIh4Vcu/AOnzie4wS0CPeamdhnD11KB82P2owtILEpt3ybIKo/5+avY9mwIi4NnqMuW3wMTYuR19BcPEkn7I0OpSMOosgAy+tKUvIAwLxGzZs0rl5uGoHOa9S/6UbYzYIR9uRA' \
			b'ZAZD7L2chwB6XYHDeFzVQy67mywjqKuMjFcFCzB5h+H4u7EjiGo4CK9UpRYyGF7QSJlVAWSIeg2HnQprdgFGeq80zrDC1xFqITDoyib0IFezlOWI+Zcjld8cezcuAbDZ7XWUijHzI5LUitrvHNiP/2Ureq1Pr9LK1+6RokPkx5KC3wjO8beR48bhFziNyxGm' \
			b'JQKBgLSN1jCE6ClwdsBkADLRmPCbY68A737UHZ0gFIwFlhpBUa/wmE/wzZjc24K9KcjL4G4L5g6At32QNgfKBMLcALraJpvdBVf7gUoNEOYQ6haYWiQagaGEQYsBaPcEX0Kb67RsJBBLrv2wUzhrqm4ICJNokCPBFgYcaP37TX6WrcPKYeJ9+06WDSt1I1a6' \
			b'oxV1UkNN7aEoh4s11001YrJLzHVP8+I6bfp7X2y2ayWgjh6G7aLWt+x3ue02C96w9blsN+/F0Iiro9oxSheLF5kqI1d3xq5v/BreZ9f7bTr1Fu6aXQtj+b9NTf762HYu8LrBd3qddPbumN0Pbd7IZz8X2X3xj6hajyOX0sb2y9rYzT4EcEcCARq+TYZfhst6' \
			b'ibfG3ux5icfzyuqOiZG2Cn3jx7AW1n9Y9FrRM0Pfy+bLJON/OAo4iE2lHf7ng0N5FoBoAcG1gIA6ucyXfwIBY/zulz9Gm65hF9wKUQZth74v3QiUXEbeUsnykbjuOyRI3kibIRzeK68nxkWPiBiEiw1GNesRyJjph3trsFHPaP/bme3/8qRthfF2Qp3DQful' \
			b'j7O3FwZ9AKkTvxmBg3ru4p5bhQTU85w+gZnXJzD6HcjJfkFUjjeXMup2p9/+/ibN/c50G39zy72A0bZ78MK+0Whb8Y/mcURptNsjbt1JC40ix3yD7EB9MdaK/xsPul3s4DinY6XxOPaGve+2y6JB7DcebovEd9Noo5FE/qFEZzXe0Xn8UxgwNjwoFxqyHTHm' \
			b'1MHudawv2LDhIC2uFdeo//MauDvn+xlEeEa5xNRTx3rYnwZf3ZfvitRxjlwdZP32DADgjmz8uxx6dr296xNNmdV39C2OLd/uksVDZcvq2PYupTzsrQ4/sxNOopWLjX7n+70+zMLdGSw8s264Od5K2/xE1r1a9ow+dd+qUQ+311Q/qVEf1aDtYQbdnNmgy9Wg' \
			b'H7xBN6tBzzBod5hB+zMbtFkN+sEbtF8NeoZBN3dzSO1ixr7vksXeIWM9jmViJdHdGOW+oSUW/yix6C4CjUxO+TtplCF0Q91nGd6eWqp2yiHu1V7Hh7Kh4hjNPt879VaGsG/+Qg23ZLuTa1x3vFztYG3qXX3JzlhXOms9qc+cQi/GiLmMuP+/6CUsN/TWcd71' \
			b'Sed5SzJnrc+Swour59hkVOY5Uj6OaIm3s70t567Vwh+shdut/4UWbh+yhVu18GquhZfFG7+11w7N2Yghcyudpm+8Yrk0w/42M8lQRgxEjMNuK7Qor8Xa4KCKOdjEJdNF6KFP6gfBitKNKFyrbK2ahKLdvyTV4GjFGa2ioYwpTpmej0I4WGjEMUUwT7gSKMql' \
			b'aOdJcgoeWolysOjIIgW7YonZB/P0eaGY2idmt6yndDqXeXUDmZtxsd9D0TcdEG6JPyHZyaqgPrwKpl7oWY3Yhe/u5bU279079c71WZf4dDUsxe7/999/WbXz4sL33EHaMfMdNaFEwmfXm9z030B2rlYdPL6TKdkhYzlLFe2YY6hDeNk5JnOwQs5stXGlzqzB' \
			b'lRycDhxGWayop93hYs+gpsUGYrJhWBT8qtC3qtB69aijhbeg0Nxgjf/nV+g6KjR2e/PmMSwrasBjWFfUghjLpkuxUlZFv2VFLy9D0cv2/04qup+n6DebhTqzrp94C5JW36e+aHoT3RcVPNG00Ij+S3an1H95/k1bL/KUPTaATSDGPv45+dlPUf+wqv+tw70o' \
			b'+DlV3p9Y5f1RVN4fDPsjih6Lul/Rj+FwcD5dP9eOU0fVd6nyU0//n7edI0U612aM+ybu3d5B/+P51pxI1W95g7Vjqbuo5vlcXk6n85Lfre9Culfxd0/cHNuvbNX9Kd2Xqedb8Pk6IejfjX1491rA7mm0e2IBd2CLzeNYQX1hViA098QS+rOZZ3M2vrnvv7+D' \
			b'vv43sg5o7x3wPZo2lBu68gf5tMod9NxfbDPtXO3ZffRXs2nNBvV9x9z2Tmk6d3TVy2Lbcavt3AHbcavt3EPbaYo32Ka6dKxL+WCgXPDFG3z9DLtrieeY8ZKMjYc3II7qgYQouTemMkioIkWMH13LZ7mxEIqfjGqw5zB2G3a9zwqUVYln4zMh+LZAjY3G2z2D' \
			b'sdX48BsBQTi+NgueHrV4/E+epB/FHH2WbmkcRh5awVO+6v11exWbLlXyqEfyKIcfqtudJbdyahey8Rtr+l2z77CMoPuDa3XN5evZfz3yx2tGFqzJV7ewNJwbnQvf9oZ8A4T2su6KuX9YQDBIEzbdYjbHPtI3ySk+Mtdy2xS7/7DgYeoaFhbEWHhutnnWj66O' \
			b'sY3PFAb5EGHu6Lnze6lwKJv1eUFVr/Yzgnhp4fOB+HQglNqOSiX/XF/3Gb5QdJ/aq/mJPW5q/h3ezt1fyE/apO0wk2zrrj0P26Ic3CM15M+oVbEFcZM/4TfcJY1qt3hPWmVPqFmyScethlDmJ83NHyk1Gt/U51NBWR10usAClW2B8H53p9LU2Jq7u8pqCwYv' \
			b'K+3a0yMH9CVO9OjJwDo2R1Fa9F3m6S0q4MYB3a/JyyxXNdBd1PLJsJYaDFi5k0qMHmIWIp/4NOvmhAGd4pNmsBVY6yNN9x01vf8FOkunZd1eLwQ3TJkZMKAwfZlltKtmd5rti0sPrPSRTtPpFRsjcOcILGKz6nWr1xj4vPDASh/ptt1Irzc7hl/6ul0VRwwY' \
			b'9J2+zKKGVb87/Q7FpQcOfI70CW+s36jNWTqOWZOjBsxrTF9miYedxoes5pizuvDASh/pRR5Fzcu5cI6pwWMHzNZNX2bB125mpu11cemBlb6slxmrePlI7YTSt5XRKb4t5gfM2i6gjnxup2LeOZ1QHGuHNLOBprj0wEpf1iE9yAbyCp1vD744Xch9NnZSUkZr' \
			b'j7YzDDjrXHhgpfsHUeklNjsL1UTlm04Bapd9KRtOKHDZuohgMCMWxbuV7MeOqByLZ31vDJyp7ucB6Jjh1sX8AA+qRTf0blYPuN1U9Gnr/NnEK2hZN/tuyLUp7mSgQMt7KFBf3MlAgS7rIR9ToMllaBTRwxzBynvpbAGvme1UvGQm7qCARzwD57xrzyDjkabS' \
			b'pKzhtbwkwP1z6T2LnzuaCaW+rCt8Z6VuivsQKPIRN8/7KPK6uA+BIl/W2b0E909sO748yLqJ7P+wp+x64vynj1KwOh+eNy8WwFxIYBUumze+iCo0xaUEVuGd8oA+TxVWxaUELpRZ3O2+/1VYF5cSWIWxoy8rpAK7UbXR83LDFn6U3htI1nlJxFiWXohN/7yO' \
			b'S/pLb1A7WOwV7ynlE/KktuPUTTH4J7XbokadyR2+GP4bdcCvm3z9m0XtMx3r4jKV26UlsfbFu97013+26zH99lpM9V/DB6AGG7uX/DSJPLDSrFQZsaAUSldRPPi2jAynYuhUhkxlvR42JYl3GRtTtZ+Lb1SkxXsUFj7AYKoKKVpgfB4gPgUpOiqN3epTSqT5' \
			b'7ur/AX6oX2k='

	_PARSER_TOP             = 'expr_commas'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	_UPARTIAL = '\u2202' # \partial
	_USUM     = '\u2211' # \sum
	_UINTG    = '\u222b' # \int
	_UUNION   = '\u222a' # ||
	_USYMDIFF = '\u2296' # ^^
	_UXSECT   = '\u2229' # &&
	_UOR      = '\u2228' # or
	_UAND     = '\u2227' # and
	_UNOT     = '\u00ac' # not

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
		('LEFTDOT',      fr'\\left\s*\.'),

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
		('UNION',        fr'\\cup(?!{_LETTERU})|\|\|'),
		('SDIFF',        fr'\\ominus(?!{_LETTERU})|\^\^'),
		('XSECT',        fr'\\cap(?!{_LETTERU})|&&'),
		('MAPSTO',       fr'\\mapsto(?!{_LETTERU})'),
		('EMPTYSET',     fr'\\emptyset(?!{_LETTERU})'),
		('SETMINUS',     fr'\\setminus(?!{_LETTERU})'),
		('SUBSTACK',      r'\\substack(?!{_LETTERU})'),

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
		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)(?!{_LETTERU})|{"|".join (AST.Eq.UNI2PY)}'),
		('OR',           fr'or\b|\\vee(?!{_LETTER})|{_UOR}'),
		('AND',          fr'and\b|\\wedge(?!{_LETTER})|{_UAND}'),
		('NOT',          fr'not\b|\\neg(?!{_LETTER})|{_UNOT}'),
		('EQ',            r'='),
		('NUM',           r'(?:(\d*\.\d+)|(\d+\.?))((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))('*)"),
		('ATTR',         fr'\.\s*(?:({_LETTERU}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}})'),
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
		('UNION',        fr'\\cup|\|\|'),
		('SDIFF',        fr'\\ominus|\^\^'),
		('XSECT',        fr'\\cap|&&'),
		('MAPSTO',       fr'\\mapsto'),
		('EMPTYSET',     fr'\\emptyset'),
		('SETMINUS',     fr'\\setminus'),
		('SUBSTACK',      r'\\substack'),

		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)|{"|".join (AST.Eq.UNI2PY)}'),
		('OR',           fr'or\b|\\vee|{_UOR}'),
		('AND',          fr'and\b|\\wedge|{_UAND}'),
		('NOT',          fr'not\b|\\neg|{_UNOT}'),
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

	def expr_piece_1       (self, expr_or, IF, expr_eq, ELSE, expr_mapsto):        return _expr_piece (expr_or, expr_eq, expr_mapsto)
	def expr_piece_2       (self, expr_or, IF, expr_eq):                           return AST ('piece', ((expr_or, expr_eq),))
	def expr_piece_3       (self, expr_or):                                        return expr_or

	def expr_or_1          (self, expr_or, OR, expr_and):                          return AST.flatcat ('or', expr_or, expr_and)
	def expr_or_2          (self, expr_and):                                       return expr_and

	def expr_and_1         (self, expr_and, AND, expr_not):                        return AST.flatcat ('and', expr_and, expr_not)
	def expr_and_2         (self, expr_not):                                       return expr_not

	def expr_not_1         (self, NOT, expr_not):                                  return AST ('not', expr_not)
	def expr_not_2         (self, expr_cmp):                                       return expr_cmp

	def expr_cmp_1         (self, expr_union1, CMP, expr_union2):                  return AST ('=', AST.Eq.ANY2PY.get (CMP.text.replace (' ', ''), CMP.text.replace (' ', '')), expr_union1, expr_union2)
	def expr_cmp_2         (self, expr_union):                                     return expr_union

	def expr_union_1       (self, expr_union, UNION, expr_sdiff):                  return AST.flatcat ('||', expr_union, expr_sdiff)
	def expr_union_2       (self, expr_sdiff):                                     return expr_sdiff

	def expr_sdiff_1       (self, expr_sdiff, SDIFF, expr_xsect):                  return AST.flatcat ('^^', expr_sdiff, expr_xsect)
	def expr_sdiff_2       (self, expr_xsect):                                     return expr_xsect

	def expr_xsect_1       (self, expr_xsect, XSECT, expr_add):                    return AST.flatcat ('&&', expr_xsect, expr_add)
	def expr_xsect_2       (self, expr_add):                                       return expr_add

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

	def expr_lim_1         (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                          return AST ('lim', expr_neg, expr_var, expr)
	def expr_lim_2         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):  return AST ('lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg): return AST ('lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                        return expr_sum

	def expr_sum_1         (self, SUM, SUB, CURLYL, varass, CURLYR, expr_super, expr_neg):                          return AST ('sum', expr_neg, varass [0], varass [1], expr_super)
	def expr_sum_2         (self, expr_func):                                                                       return expr_func

	def expr_func_1        (self, SQRT, BRACKL, expr_commas, BRACKR, expr_neg_func): return _expr_func (1, 'sqrt', expr_neg_func, expr_commas)
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

	def expr_binom_1       (self, BINOM, expr_subs1, expr_subs2):                  return AST ('func', 'binomial', (expr_subs1.no_curlys, expr_subs2.no_curlys))
	def expr_binom_2       (self, BINOM1, expr_subs):                              return AST ('func', 'binomial', (_ast_from_tok_digit_or_var (BINOM1), expr_subs.no_curlys))
	def expr_binom_3       (self, BINOM2):                                         return AST ('func', 'binomial', (_ast_from_tok_digit_or_var (BINOM2), _ast_from_tok_digit_or_var (BINOM2, 3)))
	def expr_binom_4       (self, expr_subs):                                      return expr_subs

	def expr_subs_1        (self, LEFTDOT, expr_commas, RIGHT, BAR, SUB, CURLYL, subsvars, CURLYR): return _expr_subs (expr_commas, subsvars)
	def expr_subs_2        (self, expr_cases):                                     return expr_cases
	def subsvars_1         (self, SUBSTACK, CURLYL, subsvarss, CURLYR):            return subsvarss
	def subsvars_2         (self, varass):                                         return (varass,)
	def subsvarss_1        (self, subsvarsv, DBLSLASH):                            return subsvarsv
	def subsvarss_2        (self, subsvarsv):                                      return subsvarsv
	def subsvarsv_1        (self, subsvarsv, DBLSLASH, varass):                    return subsvarsv + (varass,)
	def subsvarsv_2        (self, varass):                                         return (varass,)

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

	def varass             (self, expr_var, EQ, expr):                             return (expr_var, expr)

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
# 	# p.set_user_funcs ({'f': 1})
# 	a = p.parse (r'\[[1],[2]]')
# 	# a = sym.ast2spt (a)
# 	print (a)
