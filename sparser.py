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
			b'eJztXf+P3LZy/2cKPB+gBVaUSJH+zXGcV6O2k8bJQwsjCBzHrwiaxKmdpC0e+r+Xn/kMJUor7Up3u3t3e8LxlhI1EofDmY/4ZUg9evOXf3r/649/Kf7y9MsXX76K8YtnX3wTo6+efP3s1Yt48MXXT55qVGpsYvzZ81dfvkxxmQ6MPuDzL/GMV/L72bO/fv/0' \
			b'yetnr/X45ZOU+ll3+Lfu8Csevn7x5PU/fxZz+xdw0R5I8tNvv37x7zhrD15/8zV+v/0s/j57+dU3//76mXDwLXj82xNcfPn81bfg4fmrb/4KNp+/lDvk91+/BvULKf+XuPrFt69Q6s/kzqdfvnz5JMkECV8//+s/f5Oy/zqxh4Nn/xp/nrz8Kv5+/tkLYRap' \
			b'rz7XYuPos+7wb92hFvvZi9fPNCUJDQ/6hoxEBkD08slXr7/5Ejl9I+V+9m9PX6TLqIvPn//t+ed4zFNWhN7+1QsRQBRNksW/vX72VAg+f/7FF6AXzr999VxU4cmrzyEvXPgS90uWUcZlrx5U8DGPp/8SDz/98cOnP99+/PRndvwpHr97+/H9799/+Pj9jz/8' \
			b'/On3tx+zy/EwRm+F7P3//Pbx+09//Pb+Yzr59f1/fP/3P3591138IR7+8vb37999+FmPPn747+6IuX16/+nTu/bot/YoPebtD93h77+3uf397bvf0/Fv8lQm9xj4JR3+/FN7+NOvv/9HOv7lj5+//+mX39Lpjz/92R3+/e9ZwdLhn2+74nZPx2PiQTr9/f3H' \
			b'9tLbH39Mh+/++Pjz/6aT//n0vuP/h49v3/3n+/b0U575n+/b8vzx608ffm3zfNvSv+tKIKJrOfzQPfKPTIq/tiz98NOvH1pWP3Syjfy0sv3p/bv37UnUjYyD3z79/iGdvf8vPWpZ+fBzx+27D7/88rZ38ukv3xVvHm2sKepwVciB3eKgLvETk82VnsYzOarw' \
			b'U0jCVS+BZybdF69XKQmHQrWxEm+LR6ao4mlZVE08uEqpmtYmbBocmJo/1hcb467yJON2kmzIk3AYj0rDH4cM+Ph4hsN4VAX+WBY2HsW8hSRKoYlUFf6vUorPz4LGSEKOJYpW+lS0cJVSNa1N2Bi5obTxEiRUFrW/0pRNKeUuHX584cCpXnRyCC5FoPE5ZEVP' \
			b'03GWXjLaSFGN/Fc2XTY4wHM1nZlE5jSRRJUUKmihXGhTNc13ZNt+wsZIjVcxuSIjJX8sWFB5d0mozi4Vh1DK+O8KaANr1eIAFJ4/VksaBVxJdcTqRDWjUiiQmGCzE8cICbgvSjnyh/qpC6l7cq/pm3okKTstdynK/ilqt9lNCrtJ2Wm1e9q7YVOJilSQeaMZ' \
			b'QPGp2ym5O91UVPVoJMYXxhSoqXjkGik2LIvVOkEh0OBnEsZq7BNuKlED6HNT2FY5YzFEl8tGrQaWVkcwqTLjwcU2vUupmVJ3KZYptktxTHEpZVOKfhjHH+taHtukJk/CIQpg+BPleHXVHYImapbJnhJroCJ+el7QCquhmwSiKDXRTGUciioXYnUZqaJyyx8H' \
			b'U6ctlFs5FOkBORO6sGAxjSnpdCNce31MFIstoB+8nCdrQjyXYjX8iYp0pefRqIS3LX8ckIEsSZ3zjQCeDDLVM8c6BTxsW4hPemJbdBBUJTpEC4+iSxRbUR7RZmXEJunVMO3ODnAayVPWEcEJcpHeNO2R1yNTpgOTDoh9XmEWcLW90iQcgipquDAZoe6RqFCr' \
			b'l2CQjzT8cdvW4iAQVmft+JO9MZ2CcW35I29I1k5t5RBHdbp4pafxLF0gDuLttKXMqiRVGBdf4RavBFunB8TTDcVj63RBSDUp3bVloQG3kd3YPHizBSrG85pVGUEgqmCFOo0VE6Eoin0Lo25c0TRF8EUIRbmNiLot43+0620VKwbwbsXAQrwlKnspFV5FrS+i' \
			b'XGH8UV1KvFKrIkR9iYIPRUTbCKeNL5pQ+G3hy8KbwseXWry3NIht/HcxD/zHp8o7JNpSKf8ehYxoIrgAdIn2FnEiAkOJPCXTyGwUYRn58XXhbeEje3hoPAlFiMV2sJ5owVG/fFP4qCihiHJvIl+maKqiqYsm3hDf4mXMIYJkbIE4MZb44o5KFdsc0dqiOTvY' \
			b'RmQz8rCNwoiAWuGtitxR8pjnd8WjLV7Ybx5FkUO3ajl9FOVexrp4FIXPq4bJfLvHOsDVN2g+yblFtNbSCWspsB4sqyeKlRXQODlHJqiupiFZkGp71DAyllXLOsRD5d4gz1xN7XyVKJJD/Yj4pC5SndCwQjIsK4bVk6NKkLIbkxql1UqpJ50RiVAQkSurSmPt' \
			b'GfN0qqgNy99ouY3I5XT5mpr5GnPifFifpcKnZLTa2hltDTJfRX5meDMKb3W9iv7Moqe2R0AV4KEwKIa20FrYVMa8XG0Zzs98VvV5dZ/nNRTS60BwOt5SxNIWkfNVPY+qnkabr5X2LrT1Y0x67bsVMM78emykSkr06NCLQxcO1YKOHmorSmQV+FEF7rerwM8r' \
			b'8HIV+HkFblaBn/Ot6ivtXabe5jYNH5Qc8llfqOfs/Lg0tqNjGkbHUE2TqonDcaXWFsdOUSyps7paq+y8VVZbrRgOonpWiE8V4qWF9MB6RHIRalmqspZBtZltdk9ZBauplFlIHX9erfmM2ifV5jO8JF+o4LwO9TmWtWFrbwuOw9rXxtyEjlA0HPJuiIJNrTMX' \
			b'qlClDoiX+m6zVENLqTpKFbKEMKM0Q8zB3F+pRH2hXTlzeSVjDTtChLM9g7ioghL1nMAbS5OX7z6XTF8C23qgndLI3NJmbRrFsdqwCdru6WaWDaeUzTpJfNoeWJSu4TT9KurTth3hYKQT8jFeZXqcMUm36u2pZRwFaNZu5nnVWkQON5xV8ueVfG1WkZ/b7WK7' \
			b'ivzMroGBTRFIz6hTWYxXER/zrSktE4pkda6Y2Xu00kY+U2Yjvq7wM7RqG9L5XGtupjCNIMkJ3SPZTy35soCrHqJa9AUuTIpnHFue9GX+Th2fuSxIhhp4kTeQQodleVvrty75riqwRwVK1tEqmxHtlZcBPGiop7oqotTVEDLpzWlYXTYh09+iruoA5an3nnrv' \
			b'TVJ4vmVWUXfTUSYBuBEEX2UiagVRPNzi1w+7+PYBFx9eEoIHnkrwoAr/Br4JD67U8MOQKq8bthKlrXfZJW5YYhfYDO9NuzXaZh73IpIJ1qt2LcYtvLG3oZ3nN5znN5znN9ICKrWxY3VQVOZOQzdgxGELDhtx8GI4eLSOZdxouMhttQJEue795HtJC7iActhb' \
			b'MtgyrcUsL0CQj4JRP6zyAtQbbkF8E1QXURrtzLn6IkrjtDTNJZQGjBl68xg68ajTDrYswSv4SrY+QRRfyxUH5qorjrxWHA5Zvf/PuabOithrVk3JqokSrdJcUKVzQdWVzmBU3Up7jM3rKSKj1PqUkqc1aYzWszbkZG5pXSF57BkmgcZHAimrZI/rFKdK3a42' \
			b'xVGVrZdBJ0QRrEoDukYHcmU8doWvUzgKmLAq+9GXhFHXPQHcm/Q2UPBPS5JKvjw4rF7tGU2o+JzBypiyHk+2I8kYsdPUiqmVDuZUF74k5A2GqqrLHqqSMapqnZdhC1pnoRu+XhoqfiOK3/by5VqJ+Wt1kvCphb27wRrGaNgeq3WenK2EwHlDRyt3zMfRwFyT' \
			b'Gue1Ns7rNFfJRmPNRmPNRmOdWov16sV8rK1YthQ5u0ypSaEt7HYm2Ghjo2YFXTYQxnLV02+ZhtoYC1zTXuo0Uiw31aZdClbf/352zNuqYdrU5qRhWhqmpWEyKhnzXCRlKSlLSdm1AXX0bcNExsO1TvQkXmV9TKS0agIeG2RzkzyHpkRkGfuPdu/ImLmj2juq' \
			b'PciKtrrcg5sSLXXUB89UfJC40u1AZftWCq55aMJ5Az1pqCeNvEjoItiuL04S83wx0+cKG91iC1zsf1uXnfJBhJ665/lMr4LW97pOt+r2uXK/ZFqn5c4Vtux/cFVQP7xSi1bUSSuMaoO5ypUJzqZUI4lBwOHZbfEm0soWdBhcxTZ0yEGA3OpbI+anpXDgHi8M' \
			b'To1z7jxjk/Lmu4piyqXRSVi+TxEFO6gKvt5Qe0ZeYV5fQjVfQHjfoL8iQO3VZuI5tn3EDhDY/gF7P2DbB2xYjN2KsUgYa/mxkB+r+LHsHWvesUgcS8OxhhoLqLFvAnYKwC4BkBY2OMauxnD/xQwDdtHCxk7YawiVhcEGjDRgXwq0obENAyoEO+lic1nwjgUS' \
			b'W+xbHisdayPQm0JPSuQZzyFRfNoDNQ7PYEACfJGjIA2cTqBA1sda4mdJ8GkJ2V6/kI3ig+wxL1/3aLBd+xZ70G+x+Xk8w47/Qb6LUMjXKeSjHAYUUQM3AanYwj8ee1wVEoN9+Le4CY8z2JoeH5NAquwHL88o8TkJg/uQA64ji4BN1B33so+S2ERJbhr5EkV8' \
			b'sJON961s3i7b6ePbE/xSQ0zDxvXYVL9iUTyeEHNrtsqwE6aRWbyKD4RgQ3/5ZMCW32CQ/ellC3/Z5j3eCmKwucVzXSGbvqMEpuTHMrDFPIpXSR7YwD4SNcg4JniUDU/dymcJpITp0yh4Dvatj8ex/jfe8nsUVj6xIV/iQL3EB+D7AdhlH19hka9FxNwi+GwC' \
			b'ttvHXZIB/rGLPQQmskUqkhvUaby9qb+DscJEe+ZZTlto3eFHz1TrztOlZ7DuODY7wLL9JlzOM+NbMeF6oRmXC01ZBLZjvXaG/VqhipnaXSu2nR3bMUu2p7JlYaqqJebfQYu2s236luwZ+S0zaeS1zKyLf9SPgeT2MbC8cTGq/k9ai28gIZ9svO1LNdrg0BZF' \
			b'38zRiyvF0pOzmi5/DMne615r6LCxl529s/Ez2nSC7e+0Y3QMttFWGMdNYEfYax5NKACXblHSNmu0SdP1OTO8kCUJCTPyWX7tr401obGpmeCJHWBKTSwRDBngB5p42EWpxQ/0mm0fRwRD9uAH9u7CplTwaTqEIxi2TViCyh3Fk1i/mK8STKkVV7YDbIm0WPLW' \
			b'Ykwp7VIYH5Vxi7YvYEUiJxH63l6wpaXWGMMDjRxizHDbC0AZEjsBFxwrsIRmPraANuaOKEeXeN6GHaQpp0PQktl0BAxAm7yZDEAliQhMXjKT4gKcSCOJWrJgyJRGlpGWOgMtPABYBYgawJNKULEpyTNHKAGncVzqGMdo/2F4olQAUML9LkZp/lZrwWv9ZVCl' \
			b'+bWAZcNjvBOiST6msnj/GHAZdTjGHuhVteiVukVsoWjz5O6DFhGLZT82Yq1oNYFWJXQF9uq3PEJLKDWCtAHUEikJz3FoQtGeaJKvlFhBqmxBivfOAyl5kryIeyDVy2kHpMp9AQglLEtRBZ/3EPvAKO8McQszwagkES2V7P0lACURM3Ja4hygymmAUoEqQCkX' \
			b'MwGq43smQKkAlaMRgFKRaQ14LW0GUEqxA1C7uFQPWlX3FJTWNtQZUQkFp43WE5CUKLaMoVtMAiTVvSCQVGeQVHeQVC+ApJqQVA8gKc9pB5LqfUEgqW5bTPsofWBEPKJUmOSyXAhINQGpJiDVBKSagFQPAKmeBiQVpwKSsjEXkDqO5gGSik85GgEkFZjK32tp' \
			b'c0AixZIWk12RaUWmhciEAtFa3QQyJYotY+gWk4BMrhcEmVyGTK5DpgWjRfIkL1EPmfKcdpDJ7QuCTK5Dpj2UPjBSZHKKTI7I1JKVGgdKzmnEbJzS5MjkppFJxanIpGzMRaaOo3nIpOJTjkaQSQWm8vda2hyZSLEEmdyKTCsyLUQmMEtrbSaQKVFsGUO3mARk' \
			b'anpBkKnJkKnpkGnBWFPJsaZyMNbUy2kHmZp9QZCp6ZBpD6UPjBSZGkWmhsjUkpVapkDJOY2YjdPy5sjUTCOTilORSdmYi0wdR/OQScWnHI0gkwpM5e+1tDkykWIJMjXTY+T3Bp+aFaJuB6LABM02EKIQ24ZRBlSJjgQCVEwyQY/aIEAVMqAKHVCFBUDF+TZE' \
			b'PaDKc9oBqh1mhrwBq0KHVXsovUaKVUGxKhCrWrJSixUoQqcRs3Fa5ByrwjRWqUQVqzT/uVjVcTQPq7QsytEIVqnAtAq8ljbHKlIswSq/YtWKVdfEKjyEA+NGR8UR06ssx6qWjgTiY8YkZFn2ArDKZGPjphsbNwvGxg3Hxs1gbLyX0xCrBpzsBmCVKVus2kfp' \
			b'AyNiFcXDJJdlJFhlODhuODhuODhuODhuBoPjZnpwPEmUWJXYmIlVGUezsCpJUDnaxaokMK0Cr6XNsEoplmBVWLFqxarrYhUeQLM1ilWGWGX6WJXoSCBYxSRkaXpBsMpkWGU6rDILsMoQq8wAq/KcdrDKHAiCVabDqj2UPjBSrDKKVYZY1ZKVWqygHGnEbJwW' \
			b'OccqM41VKlHFKmVjLlZ1HM3DKmVUORrBKhWYVoHX0uZYRYolWFVuV0epFbVujFq4SAPWST7EuFwLaglokUZ9a3XCz+iEX7oY9KgNgl3ZhJ/pJvzMggk/wwk/M5jw6+W0g131gSDYpYybVPpJYh8YKXzptJ/htF9HVmrJAmXpNLKMtNQ5fE1P+yXeFL6Ujbnw' \
			b'1XE0D75UiMrRCHypzLQWvJY2hy9SLIKvkvClKmQFnohNfWACKrkDCAIzgtnDZFvTpEmK6dA0oO6hOEsQp/XVk3UF6BsDNHSBXeBKu8AVu8AVu8CI4sMlqoqWmmQAaE1StcoCALrKOsJV1xGuFnSEK3aEq0FHuJfTEKAHnOwGAHRi3KTSTxL7wIgAXWlfuGJf' \
			b'uCMrtWSBsnQaWUZa6gygq+m+cOKNAJ3YmAnQGUezADoJUTnaBegkM60Fr6XNAFopFgF0tcLXCl83hi8LLRAD1hU+iAFflvBlCV+W8JWoSSbwxSSole0FgS+bwVe3wof3zoQvS/iyA/jKc9qBrz4nqMkhc7Y9SvhlJ4Pgl+3wyyp+cZlQR1Zq0QKF6TRSHrXY' \
			b'OX7ZafxS3hS/lI25+NVxNA+/lEPlaAS/VGZaDV5Lm+MXKRbh19DldcWvFb+W45eDCogBq6sZYuCXI35xYE+iqmipSSb4pTRBj9og+JW5nVWd21m1wO2sottZNXA76+W0g1/uQBD4UsZNKv0ksQ+MFL7U+ayi81lHVmrJAmXpNLKMlCaHr2nns8SbwpeyMRe+' \
			b'Oo7mwZcKUTkagS+VmdaC19Lm8EWKRfA19Itd4WuFr+Xw1aD+xYDVHw2xZaoV5RD4aghfiZpkAl9Mglo1vSDwlfmmVZ1vWrXAN62ib1o18E3r5bQDX82BIPCljJtU+kliHxgpfKmHWkUPtY6s1JIFytJpZBlpqXP4mvZQS7wpfCkbc+Gr42gefKkQlaMR+FKZ' \
			b'aS14LW0OX6RYBF9D59kVvlb4Wg5fHpUvBuwVvriMu+Iy7orLuCsu426pSSbwxSSole8FgS+fwVe31wvvnQlfnvA12CSil9MOfPkDQeBLGTep9JPEPjBS+NJl3JJxlhfhyxO+POHLE7484csP4MtPw5fypvClbMyFr46jefClQlSORuBLZaa1kEqbw5deWgJf' \
			b'ezxsV/ha4WsefKHOOXZf69h9zbH7mmP3Ncfua47dt9QkA3xpkgl61AbAV52N3dfd2H29YOy+5th9PRi77+U0hK8BJ7sB8JUYN6n0k8Q+MCJ81Tp2X3PsviMrtWSBsnQaWUZa6gy+6umx+8Qb4SuxMRO+Mo5mwVcSonK0C19JZloLXkubwZdSLIIvv7sNxb1G' \
			b'MN8HsRPsTbHi2J5mWA11kP0pSh6hJUY/kYp+IhX9RCr6ibQ3kExaYnox6FEbpCWW+YlUnZ9ItcBPpKKfSDXwEymrMstqpylWHwhepyKVeRGANMimb5EGWecuUqm7SEV3kY6s1AIGw2saWUZa+LxBNu0uktjTBpmyMbdB1nE0r0GmolSORhpkJLBaGV5LmzfI' \
			b'SLEI0cKKaCuiHa9l5lDngmiGR1vZLVcaZxzZrzmyX3Nkv72BZNI4U5qgR22Qxlk2sl93I/v1gpH9miP79WBkv5fTTuPMHQiejruJdym/NNGmb5EmWje+X+v4fs3x/Y6s1PIFStRpZBkpTd5Emx7fT+xpE03ZmNtE6zia10RTUSpHI000ElitC6+lzZtopFgC' \
			b'aGZ13x3HMf3k18PFMzeOadjY+rA7b1Nww1NGyJvj/Ybj/Ybj/Ybj/S01ycSdl0nIvOkFcefNxvtNN95vFoz3G473m8F4fy+nHXfe5kAQd15l3KTSTxL7wEjdedOKdFnNyTK6LE+69XLc33Dc33Dc33Dc3wzG/c30uH/iUd16lZ25br0dR/PcelWYytGIW2+V' \
			b'5CSuvY269qb6zN17SbUI3soV3tZm2k2baahYGrTVNVWWa6os11Qhig+XqCpaapIBzjQpZsyjNgDObLayynYrq+yClVWWK6vsYGVVL6edDaPNgQA4S4y3pZ8k9oER4czq4irLxVUdWaklC8qURpaRljqDMTu9uCrxRhhLbMyEsYyjWTCWhKgc7cJYkpnWgtfS' \
			b'ZvClFIvg62757u98iGMFsZOAmKygPskyK1cY9jeNdjYNO5uGnU3DzqZhZ7OlJpm0y5Qm6FEbpF2WdTZN19k0Czqbhp3NUhtmaIUDzUrZUL5MLJWawU4LzR0I0kLTIpgkh0liHxhpC007nIYdzo6s1DIGStVpZBkpTd4ym+5wJt60ZaZszG2ZdRzNa5k5tvLZ' \
			b'6TTjnc4kN+FNWmbDTqdSLIK11af/YQHaaVplFSpW2iWVtsr4zQ6JnERolVVslSVqkkmrjElolVW9IK2yKmuVVV2rrFrQKqvYKqsGrbI8p51WWXUgSKtMGTep9JPEPjDSVlmlrbKKrbJOKlqyQFk6jSwjLXXeKqumW2XKm7bKlI25rbKOo3mtMhWicjTSKlOZ' \
			b'aS14LW3eKiPFIvhaXfpX+Lo5fFlUqRiwLkmyXJJkuSTJckmS5ZKklppkAl9MAnzZXhD4ypYk2W5Jkl2wJMlySZIdLEnq5bQDX/ZA2HRHCb72EPvASOFLVyRZrkjqyEotWaAsnUbKopY6h6/pFUmJN4UvZWMufHUczYMv5VA5GoEvlZnWgtfS5vBFikXwtbr0' \
			b'XxB8cbj4+DBmJqDMDeDM5ZDmUMdi1Nq9tOxeWnYvdfshy+5lS00ygTSlCXrUBoG0rHtpu+6lXdC9tOxe2sFcZi+nHUhzB8JGVbvrVO4j9oGRQpp2Ki07lR1ZqSULlKXTyDJSmhzSpjuViTeFNGVjLqR1HG3bRx0GNhWl8jUCbPqg9pGN12IrtklaJsllCHfk' \
			b'LbPt2YHtZFun3Raclfsh7SytMWzxAgWoDnllBFSzuCPo1rTD3bNbii1juGEwyQQ9aoO4YeSb0sa6q7uNaesFG9OmL0HWw51ppUq7/11/jB2uehzCE6PbmnYfJV49+hnJMu0fTjcM3Z02cSBaquuUSl2oVOpKpVKXKpXDtUr19A61SbzqiqHcDECMLI0DGSCi' \
			b'nr1HrVSQp51NrFdKstPqkMhIDpFs0EpT2hbDoi485n6Z9nFEScGsoav/DTHruoB1ZpBqAcoV+z9Be6421QIAOlpXEPKnQ6crxwGnpdgyLsuUFDNzZS8AcFzmlO86p3y3wCnf0SnfDZzyd7BlkPuQmahtrnPB30fpAyO2jNqyzvpErZv2s09yInKkvGY2f7Jy' \
			b'HIIMpZv4Em16igrUa1VkGKEUMz6iZoZ7Wa9Q8XCgosI0rJhSNQEViWLLGFDBJEBF1QsCFdlAt+sGut2CgW7HgW5XHYKKal8QqOiGtfdR+sAoh4pqLlRMj10nOSlUaF5zoaIrx0GoIN0UVOhTVKBeqyKHClLMgYrhVtIrVDwcqLDw1RBTshNQkSi2jAEVTAJU' \
			b'2F4QqMgGlV03qOwWDCo7Dio7ewgq7L4gUNENIe+j9IFRDhV2LlRMjxMnOSlUaF5zoaIrx0GoIN0UVOhTVKBeqyKHClLMgIpq6Al+S1Cxjpjcj/kr1BN9vF0zAS+JYssY8MIkwEvTCwIvmV+36/y63QK/bke/bjfw6+7ltAM1zb4gUNN5dO+j9IFRBjUyNuLo' \
			b'y53EoUUKFJzTiLk4LW4OQtOO3EmaCkLKxVwQavmeNySSpKccjYCRykvF77W0ORiRYg4YDf22VzBawWgfGPnCcYcW5yfAKFFsGQOMmAQw8r0gYJTtyuK6XVncgl1ZHHdlcYNdWXo57YCR3xcEjLr9WPZR+sBoB4y4I0sShxYpUHBOI+bitLg5GE1vx5KkqWCk' \
			b'XMwFo/b+mWCk0lOORsBI5aXiT6XNwUgvzQCjoRf2CkYrGO0Do4BKEgOdmD9qKbaMAUZMMkGP2iBglM0fuW7uyC2YO3KcOnKDqaNeTjtgtMNMjxxg1E0b7aP0Gu2AEWeNkji0SIGCcxoxF6fFzcFoerooSVPBSLOfC0btHTPBSAuiHI2AkcpLxe+1tDkYkWIO' \
			b'GA19p1cwWsFoDxihesTkGI2AUUuhcdQrTTJBj9oAMCIxwQjHCka8dx4YyZO8RDkY9XIaglGzNwCMhGWTyjpJ6QOjIRhJpi1VqUUKFJzTiLk4LW4GRkI7DkZJmgSjxMVMMOr4ngdGSXrK0S4YJXmp+L2WNgMjpZgDRuIJHQGmiHBRRKFEWArZ1iiVwlPpE0JV' \
			b'YyC1TThVjUHVNqFVdWJnnGYGbNVFtOJTbJNyDfxCncTyl1EApTUdnsWCl/DFEFwzim31BL5FOiy02odz+CTwHCeeRXjXzMQ8e92lbtD4qMXYchGbXsue/1HtOc++iWXDirU0MI66bHExNC02bqC5eJJOvhsdJkccRJEBkptKUvIAoNyg5k0aMy+3jUDmBvVv' \
			b'utFzs2D0PDkAmcHweS/nIXBuKnAYj6t6yGV3k2UEdZVR76pgASbvMBxbN3YESQ0H2JWq1EIGwwsaKbMqgAxJN3C4qbCWFiCk90pjDCtvHSEWAoOubEMPajVLWS6Yf3lR+c0xd+sS8Jr9XkOpGDM/wkitqNk7Fd53MTj+l63ktTq9CitfWkeKDogfSwp+IybH' \
			b'30aOG4dfwDMuR3Q2VsDZRisYQvMUKDtgMYCYKEzYzTFXAPcw2o5O+Am2AkONoKdXWMwn7GZM1u3A3RTUZTC3A2/XgLVo5wfhbO/knVXocgPIaptodh9MHQYoNTyYQahbQGoRaAR+EvYsBp79k3YJZTZpeUcghmz8sPM3a/ptCASTKJAjwI7tX9PqpTYOmnuy' \
			b'80kjh3nDtvuGnUwaVupGrHRP6+mkhpraQVEO99dcD7U8qoG5LjHVA02KTdpg977Ya9cyQP1chN3OeEVv+3a73GabBW/W+lw2m/daaLzVUe0XpYvFi0yVkas7Y883evUesufDtpx6BnfNnoWx/N+m5n19bPsWSN3iG7dOOnZ3zN5zWzfyucxF9l78I6rV48ih' \
			b'tKn9sjZ1c8jy3ZGMnwZvk8GX4bJe2u0wQbPnpR3PK6u7FEa6KvSNvvayPsNY9EzR/UIHy+ZLGON/OAooiC2l3fPng0J5FmBogcC1QID6uMyXfdsRN376ZY/RpA3sgVsPymDs0HelG2GSy8hXKlg+stZ91wPJW2kjhOv3vuuJcc8jIgVhYotRy3oEKmb6z97l' \
			b'LvnWzmjnlydtG4y3C+ocBtqvZ5y9fTBo60t9+O0IDNRzF+HcKhRgBHlO298cbvsb/X7iVHsgqt/jqBRoD0QVeXMp42t3+r3vr9vA74y38Te33QsYU7sHr+prj6cV/2geR4wWyyzvpmVGcWMmQfZ6vhgrxf+NhtUuduibk6zSZBx7t953m2XRIPYbDahF4rtp' \
			b'rNE4Iv9QoLMa7ejM/CkMF1sQlAsM2I4YcepK97rQF2zQcGsWR4kN6v68hu3O+T4GEZ5RzjXx1IUe9pzBU/ftuCJ1kSNH17J6ewbDd0c2+n2uOfve1vWJJsHqO/jWxoZrd8nSoa5ldWw7l1Je7y0Ob7ETTouVi4x97/u8vp5luzNYdmbVcFS8lTb4iax6tegD' \
			b'fea+NaMObq9JflJjPpoh2+sZcnNmQy5XQ37QhtyshnzAkN31DNmf2ZDNasgP2pD9asgHDLm5m0NlFzOWfVcs9Q4Z6XEsEut97sao9Q0ssPhHieVwEVxkksnfSWMMoRu6Pstw9dRislMOWa92ujs0DdXG6PT53qG3MiR9sxdouCWbnVx9uudlagerRu/qS3XG' \
			b'is9DftpYvde6cV6M8XJxb/9/0UtXbuitrrzrk8bzFkoeXDklBRfnzLFJpczjo3wcERJvY3tbzlirZT9Iy7Y7/wst2z5Uy7Zq2dVcyy6LN35ntxuasRED5mY2Td9oxWJpfv2NXpKBjBiGGMWIMoviWqzWDaqUg21UMj2EDvqkehCqKNyIsrWK1qpIKNodRFLt' \
			b'jVaa0eoZypjilOn1KIRrC434pcjlCVMCQbkU7fUkaepMmhwEOrI4wapYYPaZOX1eKKZ2aVkmZ1HWTNbVDWRtxsV9z0TedMC3I/aEXCcRfX190U+9uLOasAvf0ctra9Y7dvTd6rOu7ulqVorc/++/57Lq5sWF77NracXMd9GI8giPXS9x23/T2LnadO3xmky5' \
			b'rjM2s1TBjjUWOoSTvWMs11bEma0yrp2ZNViSg9E1h0UWK+jxRieHwHdgcNJiiy5ZmRKFviryrSmyXj3qqN8tKDK3MeP/eRW5joqM/dS8eQxrijX/GBYVaz/Gsr1RrJBVwW9RwcvLUPCy/b9zCu7nKfjNZo/OrOMn3Oyj1fOp73zeROdF9U40nTOi95LdKfVe' \
			b'nn/TVgr5mtZ9bLkw9jnMvR/CjDmvan+b8C6KfU5V9ydWdX8UVffXgvkRBY/FPKzgx3AMOJ+On2Mvp6PquVT1qafpz9uekSKdwkFmkcZDvw8O1h/P9+VEKn6LW5YdS81FJc/nknI6XZf8zuoRtljh90+0HNvfa9X5MZ2XKeJb8MU6Icif3xdysebvn/a6J5p/' \
			b'y5tUHkf76wvTfqG5BxbQn308m9PvzX3v/R3ztb+RVUBr74BP0LSB3NCVPsgHSO6Y5/xiW2nnVs/uI7+ai5gL6vmOudGd0mTu4GqTxTbjVpu5ZZtxq83cM5tpijfY1Ll0rEf5dJ5c8MUbfA8MO1SJR5fxkoytercgjqqBhCi1N6YySKgiRYwfbeSD1Fh4xI8o' \
			b'NdilF/vzut7G+2VV4tn4gAZ236+xJXe7yy425R7uor+1yHBjFjw9avD4nzxJPw85+izdBDiMPLSCp3rV++t29zVdquRRj+RRDj/dtj9LbonULhzjV8f0S1/fwY2/+4N7c83l4dl/vfMnuwLLVSNLxORLVFh8zY3BhXN7Q84BPweZd8XcP7jwD9KETbeYzbEP' \
			b'101yig+vtdw2xf4/LDmYugb3/hgLz80uz/oB0jG28em+IB/ny10w9347FG5fsz65pwrWfloPryt8Ug+f04Na21Gp5J+w6z5NF4ru83M1PzvHjcC/w3u5+wv5SZu0G2aS7dx14GE7lIN7pIb8GbUqth1u8if8hrukUe226Emr7Ak1S7bBuNUQyvykufkjpUbj' \
			b'u/p8KihrdE4XWKCyLRDe8O5UmhrbcndXWW3B4GWtW3t65IBexIkePRlYx+YoSoteyzy9RQXcOKDjNXmZ5aoGuotaPhnWUoMBK3dSidE/zELkE58r3Z4woDt80gx2Amt9pPG+p6YPv0Bn6bSsoOuF4IYpMwOGEqYvs4x21exOs31x6YGVPtJpOr1iY+ztHIFF' \
			b'bFa9bvUaQ54XHljpI922G+n1ds8ATF+3q+KIAcO905dZ1LDqd6ffobj0wKHPkT7hjfUbtTlLxzFfctSAGY3pyyzxsNP4kNUcs1UXHljpI73Io6h5ORfOMSl47IB5uunLLPjazcy0vS4uPbDSl/UyYxUvH6mdUPq2MjrFt8X8gDnbBdSRz91UzDinE4pj7ZBm' \
			b'NtAUlx5Y6cs6pNeygbxC59uDL04Xcm+NvZSU0dqj7QwDbjoXHljp/kFUeoltx0I1UfmmU4DaZV+XhhsKnLUuIhjMiEXx7iT7sSMqx+JZ3xsDZ6r7eQA6Zrh1MT/Af2rRDb2b1fdtPxU92jpvNvELWtbNvhtybYo7GSjQ8h4K1Bd3MlCgy3rIxxRochkaRfQw' \
			b'R7DyXjpbwGtmNxUvmYk7KOAR38A579ozyHikqTQpa/grLwlwAF16z+LnjmZCqS/rCt9ZqZviPgSKfMTN8z6KvC7uQ6DIl3V2L8H9Ext/Lw+yYiL7v95T9j1x/tNHKVidD8+bF0tfLiSwCpfNG19EFZriUgKr8E55QJ+nCqviUgKXyizudt//KqyLSwmswtjR' \
			b'lzVSgd2o2uh5uWULH9+xh2Sdl0SMZemF2PTP67ikvzQ+Lo99qDH+WcrH2Eltx6mbYvBPardDjTqTO3wx/DfqgF83+Qo4i9pnOlbGZSq3T0ti7Yt3vemv/GxXYvrdVZjqv4ZPLw22XC/5gRB5YKVZqTJiKSmUrqJ48HUXGU7F0KkMmcqKPWw7Eu8yNqZqPxdf' \
			b'i0jL9ygsfArBVBVStMDYsD8+BSk6Ko195FNKpPnu6v8B19YBKw=='

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
# 	a = p.parse (r'x**-y[0]')
# 	# a = sym.ast2spt (a)
# 	print (a)
