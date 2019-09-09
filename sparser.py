# Builds expression tree from text, nodes are nested AST tuples.

import ast as py_ast
from collections import OrderedDict
import os
import re
import sys

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

class AST_MulExp (AST): # for isolating explicit multiplications from implicit mul grammar rewriting rules, appears only in this module
	op, is_mulexp = 'mulexp', True

	def _init (self, mul):
		self.mul = mul

	@staticmethod
	def to_mul (ast): # convert explicit multiplication ASTs to normal multiplication ASTs
		if not isinstance (ast, AST):
			return ast

		if ast.is_mulexp:
			return AST ('*', tuple (AST_MulExp.to_mul (a) for a in ast.mul))

		return AST (*tuple (AST_MulExp.to_mul (a) for a in ast))

AST.register_AST (AST_MulExp)

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

def _expr_mul (expr): # pull negative(s) out of first term of nested curly/multiplication for consistency
	mcs = lambda ast: ast
	ast = expr
	mul = False

	while 1:
		if ast.is_curly:
			mcs = lambda ast, mcs = mcs: mcs (AST ('{', ast))
			ast = ast.curly

			continue

		elif ast.is_mul or ast.is_mulexp:
			mcs = lambda ast, mcs = mcs, op = ast.op, mul = ast.mul: mcs (AST (op, (ast,) + mul [1:]))
			ast = ast.mul [0]
			mul = True

			continue

	# 	elif ast.is_minus or ast.is_neg_num:
	# 		if mul:
	# 			return AST ('-', mcs (ast.neg ()))

	# 	break

	# return expr

		elif ast.is_minus:
			mcs = lambda ast, mcs = mcs: AST ('-', mcs (ast))
			ast = ast.minus

			continue

		elif ast.is_neg_num:
			if mul:
				return AST ('-', mcs (ast.neg ()))

		break

	if mul:
		return mcs (ast)

	return expr

def _expr_neg (expr):
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

	elif ast.is_mul or ast.is_mulexp:
		ast2, neg = ast.mul [-1].strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			if ast2:
				return (AST (ast.op, ast.mul [:-1] + (neg (ast2),)), dv)
			elif len (ast.mul) > 2:
				return (neg (AST (ast.op, ast.mul [:-1])), dv)
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
		if len (e) == 0:
			return AST.MatEmpty

		elif len (e) == 1 or len (set (len (c.brack) for c in e)) == 1:
			if e [0].brack.len == 1:
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
			b'eJztXWuP3MZy/TMBrhbgAOwnm/om2/KNEVl2/LhIIBiGLOsGRmzLkWwnwUX+e7rqVD/I4cyQszOzs7vE9g6bZJNdVV112I/q7iev/vJPb3/98S/NXz7+4sUXL+PxxfNPv4mHL5999fzlixj59KtnH8tByVHH40efvfzi83RUKaLlBZ98Qe94yb8fPf/r9x8/' \
			b'+/r51xL//Fm6+lGJ/q1Ev0T06xfPvv7nj2Ju/0JU5Ahf/vjbr178O53lyNfffEW/334Uf59//uU3//71c6bgW6Lxb8/o5uefvfyWaPjs5Td/JTI/+5yf4N9//YpSv2D+v6C7n377krj+iJ/8+IvPP3+WZEIXvvrsr//8Tcr+q0QeRT756AVTSGT8a/x59vmX' \
			b'FH35ibBNsY9K9G8lKmw/f/H1c7mShEbv/AaERAIo0efPvvz6my/o9d8w38//7eMX6TaVxSef/e2zT+g1H6Mg5PEvX7AAomiSLP7t6+cfc4JPPvv0U0rP5H778jNWhWcvPyF50Y0v6HnOMspYDcpBBB/z+PhfYvTDHz98+PP1+w9/VvEPMf7m9fu3v3//7v33' \
			b'P/7w84ffX7+vbsdoPLzmZG//57f333/447e379PJr2//4/u///Hrm3Lzhxj95fXv379597PE3r/77xJDbh/efvjwJsd+y7H0mtc/lOjvv+fc/v76ze8p/hu/FZcHBPySoj//lKM//fr7f6T4L3/8/P1Pv/yWTn/86c8S/fvfK8bqByiSzv98XdgvuUmqdPr7' \
			b'2/f51usff0zRN3+8//l/08n/fHhb+Pnh/es3//k2n36oifnzbebvj19/evdrzvN1Tv+mcMSizBS+K6/8o5Lqr5mkH3769V0m9V2RdaQny/qnt2/e5pOoKxUFv334/V06e/tfEsukvPu5UPvm3S+/vB6cfPjLd82rJxtnGtvfNBxxLUWspp94ub2R03jGMUs/' \
			b'DV+4GVzAmUnPxfs2XaIop9o4PqrmiW5MPFWN6WLkJl2Va/nCpqOItvhxodlof1Nf0n7rkuvrSxSNMaXx4ykDvD6eUZQyavHjhAeiXXGSSFIXUxn6v0lXQn3Wy5EuUY7MmgqJtf4mXZVr+cJG8wPKxVskTN3YcCNXNor5Vp5+QuOJUrnpORpjLOgmvgekyGmK' \
			b'V9cVDhtmVfO/cem2pgi9V64jk0icXEQiw0z1wpTv81W5Fkqydnhho7nEDdHD7zQaP45IEBLLJSrOcpWipJTx3zekDShVRxFK0ePHyQORFsvKG69TMVOhQCDxgqtOPA50gZ7rot61qczoJeBPrm9cu3WpPlXbKdTwlEo3bF0aP6SHp2brdPjAxkALotLrDhlQ' \
			b'Ag3dTpfL6cagIKIwdWi0bqikYszTw7HAYgKY+o4UDA1hZsJYjMOEG8MyJ33uGpeVM5Y2c6E6sRqyNOuaCBnFeOhmvl6uWFyx5YrDFVeueFzx6cpGsbkyaCDW48f5TG2+1NWXKEqsGPxsBKIkSrGIIbq8hbTEsHrZHjek6Cy9C9Ydy4h1VFgglWUpxYLT/E7V' \
			b'4seT0QObVMtRliNhaMIZsEiawlfS6Ya5DPKaKKAojS7ZUX1ZLsRzpj7gJ6rUjZxH82LaWvx4wgiQxKXPJEUlfBLVYSOcRo1A6RJQtBnsk8Y4nXCC8RXqGTUkSjulUI0RvU5i9Ul68eITW4yVTildPnOAu8ib7nIsSEyrFNEpAhQMArgEXMiRYEGzUEjXmcgI' \
			b'ek9YmbKG0hcHr9T48cUUSSAozih5/qm+nZ3AsvX44U9PdyOXKEoxl27eyGk8SzfAb8y2ayEzm6TqCGSYKkdfxoiu8gJHRsqcOJducFK5lJ5SYJqAN96LFYVXLeFjTGxRlBEOYhkaKtNo47FsotW0ZN6db7qu6ftGtRFYWxX/o3m38VvUxu+zJaSPFhctrI8h' \
			b'ilVxiUfciF+wjnEgGoaKn8XeNn0snJikb6JJRWTtQtP1TWiboJqgmxDfqek/PhmtTEXbUS39U2ERDtGF+LyKL6BPbKyZxLqKI6CJBhchI2KE4gwjsVF+KtKiIjEhZkyvc02IwTchEto2vWqoHGIRRrFEKkIT4tekb6Lsu0iabjrTdLbp4mspA8VVllgf8Www' \
			b'8TMeFSvWQKLFRZOOcOljxm1M3EZhxO+foW8sEREDkfFd86Slz/erJ1HsVCaWT59E2atYHk9iAeCuxmV862M50N1XVJnic0eHtaTOXFI9ysKhiKJoUQid53OlUWRdh2Q9CrTjEnyiHYoX5Ugv5We5TG5Wm7twSbLwblj+qUCMHGFRfScF5Ph8IEoRIsQ3JTgI' \
			b'LAtqIKAJoUAikSonmuPcBfP0oq1QU5X41iyg8+WrLfLV+sz5SLkKjnJGq71d2N5I7qvY7wDmtMCctav470D8XCUgcGXxQx6QROZb+E1s1qxFNu6Q/loD6lK/zGepd/J5YNyOjzRdE7lpVjU9vZpqqdcaaXooqc6aVBXwK3jcwSez42JR1MSj9h21+agVSE1A' \
			b'KqkokVXoJxd6aFehX17oahX65YWuV6Ff+ksbjLRC0fp9wsyhH2j9yN5NA6lL/UDS/8EVzu94aE2KCt14SvoRpOCclJs1a7FdvtgsOlNV6rvij/ZjayIpJSqrREN1K0dpdQboaoCwAsYMnvSpt1oud+jvTB0FuGtx1Yak5sgicI4PVaBB2kFeOu5RFWzjGdG3' \
			b'NsxZSJ0oSod+8w6w2FkZ+xDDTGippJfXQVUdJOshWRImA02UYszB3GOxRKVBq9nrB8gaCtMDTrwbmMXD4hTo5xn9wE7N4L1mTT4WrRspKEYhwbjTadRL7LeXylAZo9YYnNbrcPP5m2hRwhqD/qu4z1+pJLclGd6Px1Wup+vI9Kv+XkLOPaPz2ha9tHoHRmli' \
			b'ZpX+xaVv9Sr2u/DnaFex34XbWos6CklQi9taPK5yPvWnlFs4kMrqtrGgmem4En2hzCZca8mj0YmNcBmupbdAoJTNWZ0xBbWUkiMfLOsMOUkJtqFHeqf79Hfia425SdwvgZt4ACnE3xOPZXd5hs9VDQ6oAQmI5LTKZ1qLuT1L/jnQV5mEoYx0fpvUi6ZkugYP' \
			b'qLPaim9VYD0kvwc+6KT4+Oqs4h6Oc0Her3hsluSzykXMlK30cYvAriJwj1wE5IPB9QdpGwUWyCMTwisa33+MbNsOdUj+NDxoXsn7Qot/gt4awutQpdjhpsTDtTd5QshdOKu02W9Aw29Aw29Ac8UI3zJ2FODO1NUb7g66l7wgqGMFu//D+WwiD4MRf1dmmyYz' \
			b'64cgySe9ERcv9RA0nLyN8EUwD4Md6bnz9mGwI+1W3z0IdogyDSchDd8g8QWidVXo23zD67PQIX6SDbrwzA36aQ06TNYZB5ee2+dY9BbFo1o5tCgYEquRYSRzIwMfpiwDQN35ckqHyJuR7lsc8W6k0QHvlIodD0ut0zXPMTgFM0Rzb5XuyZ3uxEby9FeKmWqy' \
			b'DjVOBM5M6v/V0u/L3ZMrlp3L6QDjN6tkTz4vDTofAOhBp6+DfAzSnCgFzUdPvNnV20BXDa4aXOWvBC4GnAV5kUUOD3peySvqnDIPvHOKe6XMOjhTKssyOtihhtVB/Tu2idyq54uK5hCK9wTMige8vuPpMqhnORkux8Bjjwq4h7V6vNnD2nyXat5Wat42DVWi' \
			b'NmhRG7SoDdpUC7Srx/MJ3bRihMWONlGqJkhduwwGSy3copAeOAj6Hko33UHdQSUjxxZmYlO3MD9kTZ5HZm9SDezet6hj5k6s1KUKJazUwUodrBQHOY3UOAEWB4k5SMytNaOzLFzGAh5PmMKY4zpAcVlgdWIogdb3xmJ+nuockStaKLV8SGPmHsbhYRyUrMkF' \
			b'6h/dQClrrIHsOoERPppOXJRCHp/rHp10XpGmdNCUjj88cC/Mk5mTyAK+5PDTohV7abneaP+KHBOT+pEMA7Qv4J1BJC0VARmLlaV++XnO1MrE/fhg/xjLwD5CtlkvbNILLfqgb2p1oi8FFImPlAC9tW3zqm00L49Hfa20RB7lwnju5OMR8xQuPFFP3w18pvDt' \
			b'qsiEwPHNgpxqaQxEbFi43aAs8JmLoqESNPwx64Vdh08RfXm4t78T41HgkkREK07QchO00gQtsEyrK9N0ZCotWjaA1gygOfY0wZ4mpNNsdJquTXO1qXxpXQJak4CERYKiVZjJd5gGHWhRL1pjipY8orKihTFoVQxaEoPWv6CaNy3+QGVCC//SWrg0mY5mW0Sd' \
			b'0DTZgiZaUDuM2mAsUlKOeI02KOFV5uP1+EHWhA2RHx0VWJNTCjk0uD4WFu91Qquw80r7tMi9a2iHCtoqgXYH6Wi5+ZZOWlq8PZ7RjgU9rU1PW5zQ+vm0eL/mLS9oBX5a7Z52GogXAt2lZCTmDX3uNxyh+7SWPG8pwo8r2hND8w4D8R1REJuedx6IiQLtJUA0' \
			b'8k4G8Tz+d7Q/C++rEVN63jzA8/YPvCUA7aSB7REaXlSeXtlbsBOVYBPluulaIZrWy6fh5E3UjQ1td0KbEvC2B63jnQJ4jX3e9kK2zuj4Jj0Whb/pO175nvd4gBBozxnelYK3YlC8FUl8pCPaKXcSDL22ZVEwm0F2eqH30Br7MR6IdV6IP76fdwxhfkn2RCRR' \
			b'TgQT/7IJh++RUU9Hx/u6YNOGlggnnlnSlA8R2VHhxpPOfkfGSyY7MFe122JtwZOB6dpS8xwYsD+ZDdfYRrW/vSatZ5r1fTBpPWHW7QHTdiS0LWt2M+zZcaqYsdu2alfs2k1ZtjunbTNhxvIRfwct3M228Xtk392EjbsDVt78wz4lhHdPCeO7Lh7M/3F18hUJ' \
			b'NiSTzy2uTiokUuEYWj219RQbfmpXSmOzT+ZvB7WlWbavi/nHkp+sWgkU9GMoQPMvBKmooROGa1AWtSziSxZMKRUfVHpK47SCD57qkCCk9g2QVt1UNZvWs2Z48SOIcQItehtOaFknWtMpwwnhrR/BijoAJ/F5WiqL3KEOQQv1AB+El1DBixOIUSOYIX1wFdwo' \
			b'rrqSDUIjFVWPCWH44PkQM+CDaXJqhSPVdwNHSfDtIBDgIHHHOENxwZg+LIMZSh8poEMNNPE8hy3QUbtDH8CdSzHKG6xsB4KmciIYFdj2waZP93Gxw0MGRGkcHA7CeYVfEDr24RkjlbxfYCoJtQYrxqlpiCok0+jBYbCCWAiumPxttJL8HV7aybtryJL8MnD5' \
			b'9il9H6JdPoXGhP4pIWdU5KeEjVGRn0buCM1MRrPUjEIFRmov9wHEBMG43E+OYCt67UAvakiz7QaJUSUp1Y+kbpQTyZG0C1HdSywHBi1VgZbKoIVn54MWv40zGIDWILct0FL7AiEWk83sbjIf42R9WzNUt5uwyhpjVpKKApM9+PYaB2TkhesasNQewBKpCmBJ' \
			b'/jMBq1A8E7BEgiBpCrBEZgFFEITdCrAkxRZg7cYpO6p13V+QWutYF0QpYh72andAVEqhcJQavQVE2UFgiLIVRNkCUXYhRFlAlB1BVJ3bFkTZfYEhyuYa1XSavq25AT6BdBx9fZ/V0gKgLADKAqAsAMqOAMruASiRqQCUEDAXoApJ8wBK5AeSpgBKJBZQAEHY' \
			b'rQEKKY6pUbkVqVakWo5UxBQs1+9AqpRC4YikygOp/CAwUvkKqXxBqoUdTfw2zmCIVHVuW0jl9wVGKl+QajJN39bcCFJ5QSoPpMr3WS09kMoDqTyQygOpRn1Xyu9BKpGpIJUQMBepCknzkErkB5KmkEokFlAAQditkQopjkEqvyLVilTLkYoIhuV2O5AqpVA4' \
			b'Iin3CPcSy4GRqquQqitI1S1Eqg5I1Y2Qqs5tC6m6fYGRqitINZmmb2tuBKk6QaoOSJXvq/QQuPYQokc2Xniukarbg1QiU0EqIWAuUhWS5iGVyA8kTSGVSCygAIKwWyMVUhyDVN3uPvd7hFelt32FrMtCFhECE+4BWQpd7aofAldKhwQKD1BU9xLLgYGrr4Cr' \
			b'DNLj2QXAhaE8NRrNG+S2BVxbBI3po5ItPezTafq2ZkiwK/Ww98CufF9hhIuxqwd29cCuHtjVj7Cr34NdIlbBLiFgLnYVkuZhl4hQeJ7ALpFYQBkEYbfGLimeI7ArrNi1Ytfx2EUvQpezll52jRoXHwp25XRyxAMafe2I5UDYpau+dl362vXCvnaNvnY96msf' \
			b'5DbGrhE124GwS6uMXdNp+rZmCNiVetrFU6ncJ/3U6GzX6GzX6GzX6GzXo852vaezPYkV2JUImIldFUmzsCuJECRNYFeSWEAZBGG3wi5JcQx29St2rdh1C+yil8CEtWCXBnbpIXaldEig8ABFCbv0IDB26Qq7dMEuvRC7NLBLj7Crzm0Lu/SBwNilC3ZNpunb' \
			b'miHBLi3YpYFd+T5jlwZ2aWAXfLL4IGzX2KX3YJeIVbBLCJiLXYWkedgllIKkKewSiQWUQRB2a+xCimOwS7Wro9aKYqdAMdvAKRsHyhOuoHzwfJA04u0rA4paBhTTzV5iOTCWVQOKugwo6oUDihoDino0oDjIbQvL7IHAWCbE6ySBiWR9W/MkcCbDihrDiuU+' \
			b'wxmGFTWGFTWGFTWGFfVoWFHvGVZMxAmcCQFz4ayQNA/ORIogaQrORGgBxRCE3RrOkOIoOFOAM6USYnUJq4ZAZXnazYGecwUM4JGYZKewT7Yj2Anpft9cJLBP/epZuwL2KQCb1AFNZiNNZoMms0GTmQ4xAz6YJqeWIx4zaDgjlgMBtqkazqY0nM3ChrNBw9mM' \
			b'Gs6D3MaAPaJmOxBgJ+J1ksBEsr6teQJgG2k7G7Sdy31SVIO2s0Hb2aDtbNB2NqO2s9nTdk7EAbATATMBuyJpFmAnKYKkCcBOQgsohiDsVoAtKY4CbLPC2Qpnp4AzR4rAxiyTkehIcOYAZw5w5gBnKTWSKTxmMCEJsRwYzlwFZ2UyEp5dAGcOcOZGcFbntgVn' \
			b'Q2qoNMcE5ksZz7bS8ATMtmZK8MwJnmFGU7nPeOaAZw545oBnmOYEKVd45vbgmRAneCYEzMWzQtI8PBMSQdIUnonQAsohCLs1niHFUXg2dsFd8WzFs6PwzJMWsDGLqxsdCc888Awdg3wwTU6NZAqPGbi9IZYD41nl9maK25tZ6PZm4PZmRm5vg9y28MwfCAxn' \
			b'QrxOEphI1rc1TwJn4vxm4PxW7jOcwfnNwPnNwPnNwPnNjJzfzB7nt0ScwJkQMBfOCknz4EykCJKm4EyEFlAMQdit4QwpjoKzsZ/uCmcrnB0FZx2pABuz+MPR0eGqY/1gOOsAZyk1kik8ZuAbh1gODGeVb5wpvnFmoW+cgW+cGfnGDXLbgrPuQGA4E+J1ksBE' \
			b'sr6teRI4Ew85Aw+5cp/hDB5yBh5yBh5yBh5yZuQhZ/Z4yCXiBM6EgLlwVkiaB2ciRZA0BWcitIBiCMJuDWdIcRScjZ15Vzhb4ewoOAtU/mzMQeAsAM4C4AxLX/DBNDk1kik8xjd7ieXAcBYqOAsFzhZOSzeYlm5G09IHuW3BWTgQGM6EeJ0kMJGsb2ueBM6C' \
			b'wFkAnOX7DGeYlm4wLd1gWrrBtHQzmpaO8x1wJsQJnAkBc+GskDQPzkSKIGkKzkRoOHSJ3RrO5NYxcLbH43eFsxXOZsMZFTvGAqyMBViMBViMBViMBViMBeTUcsRjFmMBiOVAcGarsQBbxgLswrEAi7EAOxoLGOQ2hrMRNduB4CwRr5MEJpL1bc0T4MzKWIDF' \
			b'WEC5T4pqMRZgMRZgMRZgMRZgR2MBds9YQCIOcJYImAlnFUmz4CxJESRNwFkSWkAxBGG3gjNJcRSche1lNu45otGqMDWonWHtjRXX9lTTLGkEr7+hEWvZE4BravBLMfBLMfBLyQ8gGdfU5GYvsRy4plb5pZjil2IW+qUY+KWYkV+KMrrKbquqZg+EAD+7xAAL' \
			b'YaP0dGKusBXWpMIm7ikG7inlPlfY4J5i4J5i4J5i4J5iRu4pZo97SqJPKmxCwNwKWyFpXoVNZAmSpipsSOACSiMIu3WFDSmOQrh+RbgV4U5ac/NU7IxwBrGWPZu48oaRAouRAouRgvwAknHlTdL0Esthk96ZKm9lpMAuHCmwGCmwo5GCQW5blTd/INCSkc5l' \
			b'+lkGm8zQmJm+rTmTKpyMF1iMF5T7XIXDeIHFeIHFeIHFeIEdjRfYPeMFiT6pwgkBc6twhaR5VTiRJUiaqsIhgQsojCDs1lU4pDgG4PTqTrwb1yJeGPWI8a2bxjhaCvywe3HXYC1YHChvjB9ojB9ojB9ojB/k1Eim8JjG+AFiObB7cTV+oMv4gV44fqAxfqBH' \
			b'4weD3Lbci7sDgd2LhXidJDCRrG9rnsS9OM2w59moEI+v07GbMcYRNMYRNMYRNMYR9GgcQe8ZR0hEipuxEDLXzbiQNM/NWKQJkqbcjE1WAxdQJORqnNiu3Y1x7Si4UyvcrdW4E1TjqGxh3E7mgDnMAXOYA0aHmAEfTJNTI5nCYw4zwZweBII3V80Ec2UmmFs4' \
			b'E8xhJpgbzQQb5La1trY+EAjeEvFZAhPJ+rbmCfDmZDKYw2Swcp8U1WEymMNkMIfJYA6TwdxoMpjbMxksEQdYSwTMhLWKpFmwlqQIkiZgLQktoBiCsFvBmaQ4Cs6ubm7BcGOTFdTOBmrtuaaF+Qar1eNA+aJxqtE41WicajROc2okU3hMo3GKWA5cb6sap7o0' \
			b'TvXCxqlG45SX1KeNGGgJfpI6HN2tZEi39UQzdUTXduAanLChkywmkvVtzZ3U4KSBqtFALfe55oYGqkYDVaOBqtFA1aMGqt7TQE3ESc1NCJhbcyskzau5eTQF0EjdsfdAEhwk3gVhua61IcVRMLfOOXh8AHeWWpuhsuU6i5Fam0GtzaDWZlBrM6i1pdRIpvAY' \
			b'3+wllgPX2kxVazOl1mYW1toMam1mVGurc9uqtZkDgWttQrxOEphI1rc1T1JrM1JrM6i1FckoMNoLURCrdzgI53WtzeyptQlxUmsTAubW2gpJ82ptQjBImqq1idACiiEIu3WtDSmOgrN1ysEKZyeBM0elysYsU6gcplA5TKFymELlMIUqp0YyhcccplAhlgPD' \
			b'WTWFypUpVG7hFCqHKVRuNIVqkNsWnLkDYVNiCc4mk/VtzZPAmcygcphBVe4znGEGlcMMKocZVA4zqNxoBpXbM4MqESdwJgTMhbNC0jw4ExJB0hScidACiiEIuzWcIcVRcLZOOXhYcIau59PDmtkBbd0I3roa4jwVMxu4NEcdmqMOzVFZbsmhOZpTI5nCYw7N' \
			b'UcRyYIirmqOuNEfdwuaoQ3PUjcZKB7ltQZw/EDai4aUROp2sb2ueBOKkEerQCC33GeLQCHVohDo0Qh0aoW7UCHV7GqGJOIE4IWAuxBWS2vzwYaATWYKwKaCTF2XquiB8C9bxtUqUxyHeiZcYd3cAdOdbOu6u4E0fgLhL1Nao/GkBIHvIC6SnkmbXB1m6d7za' \
			b'eE6hcERSi0V77TCw20e9aK9iRcquHwsX7k2bcNrxyr1crOV/2/9ji7IBleT5UZbunU7Tp7co2cFTVRsL8z1evTdRwJoqExGUzERQMhVByVwENZ6MYPes4JtkLK4fIt4RqIGmaWAjyLCz1/DlUgKTaseEhCQ8FGnHB007lJKT8agWJ2kzpkWFeIoFRP1TLFhX' \
			b'MGw8FeGWGHYLALswaM3eEfhSda67aj5SGcAWvZ4GoZxC4YikHuOWXg8CgZCvxi19Gbf0C8ctPcYt/WjccgtvRhSMCYrM+jJKOZ2mb2sOqq3tPIYoNwd3DPZ7hiKTsIAmKZeZVaSKkUMwIun27A2c3hQg1SBlUmGHpDiweR1Dx3jt7xU6Hh10WBrqZbOyO6Aj' \
			b'pVA4IqmHYz5iOTB0VI75vjjm+4WO+R6O+d4egg67LzB02AIdk2n6tuaghg47Fzr2ONknYQl0SC5zoaMwchA6kG4fdMibAqQapExq6ECKOdAxXnp7hY5HBx2+8ejR8X4HdKQUCkck9ejFQSwHho6qF8eXXhy/sBfHoxfH+0PQ4fcFho7SZzOdpm9rDmro8HOh' \
			b'Y0/HTBKWQIfkMhc6CiMHoQPp9kGHvClAqkHKpIYOpJgBHWbsqX530LH2uNyP8TEqJyz64MMOqEkpFI5I6rHQA2I5MNRUCz34stCDX7jQg8dCD3600MMgty3YCfsCw05Z4mE6Td/W3FSww30rHos8JJEocNiDaQ8ZeuTiheUakPas8JBEKoAk+c8FpPz8vC6V' \
			b'JD6QNAVKIjAcusRuDUpyaz8o1b0pZuxXvoLTCk4HwKmncmJj3dEFnFMoHJHUowvYDwODU9UF7Ev3r1/Y/evR++tHvb+D3LbAaYugQXICp9LzO52mb2tutsAJHb9JJAoc9mDaQ4YeuXhhuQanPT2+SaQCTpL/XHDKT8wEJxGfsDwBTiKwAPkHYbcGJymaBeA0' \
			b'9hJfwWkFp/3gRCXE5ofDBDjlFApHJKWo7iWWA4ETEgOcKC7ghGfngxO/jTMYgNMgtzE4dXsDgROTrRO/E2n6ATdjcOJM823SSH4GTHvI0CMXLyxX4ITzaXBKIgU4pfxnglOheB44JfGBpAlwSgILkH8QditwkhRLwGns272C0wpOB8BJUQmxsaod4JRSyBFJ' \
			b'KUrgpAaBwUlV4KQKOKmF4KQATmoETnVuW+Ck9gUGJ1XAaTJN39bcbIGTAjglUYDDHkx7yNAjFy8s1+Ck9oCTiFTASfKfC06Z4pngJOIDSVPgJAILkH8QdmtwQool4MSe2hFwmggfTSQ6wlRfLQVjBK6ijghimSnQahNumSnoahN6mfM7A4UZMOaaaNXnWBbm' \
			b'GDyL6SL/ytGHwVT4Fq9HzoFzRrDO7cC7mI73ad+He+1MJ6Il+BdmYqA/dqoeKX80N3IcofXCefuEaAHAxk3kL7AuAiKpLDNO9iFj5YaUl94kgKnFN5yOveNDLM2N4Tt12GDxFskCKwEEhtANlb8uLuN6oct4ckDSI5/xQe5jIN0YojLGjR1TWh5ywpBmVdn0' \
			b'lkS0AbcTyWmCX2F3jKwaDuRym+f3wXtcw3tcw3tco/tej7zHN7QmsqExeaowpftcWaM5KR0gl8YBqFBUO4BeydMwOWXaTKK0xuC2S0Cs93stJT5mboKJ1DbsHQCI/zrLHnrWBRFXPTcQKTIyu6d8hX4jSGuCL/7t6Jfwmm4rpNKUgMHaRZMYQ/UukPaEzQTM' \
			b'QGXAcI3BDMCz0HdyQJGxljDVMJomuKwHBOcMBo7hbxf0VbC3BXfHwNwBaJsDaQxl3QjCchXO74Otw4CVjFAzRiWAyog0AUcJi44Cov0Dggl1Nmk6Sg9M2fTjxuKsob0xMOxGhRoRtrDgSBQ4bPqzbJ6snUx9aOfJwsla/YS17qlVndtgU/0oiuLBmm00qG3T' \
			b'XWK2B6obm7QY8X2y3VJroHJ6JDZMRb9lx8ttuFvwxbUXtOGqdSPGbE9qz6Qr0dYiUSpSdTX2fevP8iH7PmzbqRVxjfbNxNX/LjUF3KntnaG2pWPHDcFrs/+x7WuifZn9N/+I+vU0Usl177Cs7t0dQgJ/MjAQAPAZANqH9VFPRq/Cno966lqI14yXVRxpdb12' \
			b'CAQytUQ7auxTs4zasr6ekhlLrz0JULBt2cVAoS4GFhkcugwOVDYPtEKQAEHrfRUC2UpAc7lZrIyheTnarV1SSncV3SZ1Ufwq3h3K5AFsuqy4LtEf33q3O/pRT4sggI+WekHdBITM9e+9KxhxM9oHfmb7QJ+1DjFdf7A1NOQdSu6kHjFqI3C5BDUBDfZ+wAMV' \
			b'9pw2g5nXZtCyEdzOdkPUkOvpqZu28mhRkRvSLuoP5SV5L1ZpmBqzOEfFgbqVY1xRfE7PQKpE+AnrT5WFM1QSrrElMUYA9hnjoaUN6cWGVyK8aE3BX7KyQInoHfxBb2egglQccqVhXFfopHowqhTEx15dBUicqDv/mpsP/W36DYqFd/39NfATd+Pfg9q+aW/T' \
			b'jd/8o3saEZ06AOJD12qpUeq3+4Zfo9XO/WbPtNp7/V3eVStv2c/jdt/i67Vh4W3O1/dQP37M+yjjdZex3+4E9fC5PkT77NidaVTOXak902p1V2fUdDQnqWbXpm2Ot2+1tfvdScfpuIo9u5590NLtcZbuL2PplZWzL8BdfK3PZOWrhc+z8JF1U1nc4cf7rMZ9' \
			b'UsN2xxl2d3nD1qthr4bN5bAa9gzD9scZdri8YZvVsFfD5jJYDXuGYXdX22P2YHrJrslyr8xoT2ShNMPpOvrDbmmRzT8UzQeMgMPd2eFqjTMKPQ9PX8JQd06jO+eQ9Gq4u4eaycuWRpsv+JG9k+Hl239h+7sz4p3zcPd8bf1o/uy1fnVnzH2dNee1r5xSH5Qx' \
			b'Y7rz8H/RV5kfGMw1vfrxqnnTRmfNHWPu2c10ylmkGnzWTyNs0uc6srxa+mrpd2Hpfut/oaX7R23pXizdzrV01bwKW+sEwaw1GzSWAeqGRswWDFscro+TrGXKShRbxJZWswb7qLGhFe0crT5TKSQpGxSxg/qx5k1oXda4vKVdvehKKsLJkqOLVEZjIUOe7EcX' \
			b'pXC01IBmgmM9QIsBqRajnynKHSCRRYr+pBPLVPGOLm0lW53e148EreYKe5dW10I3txC6mZb7PZR9KFi4Jf8EZucrA3t8Gez6sFdF4hd+w5cX26xv8M5vb181lc9XxMz28H/4DazKHTcXfuuOU4+Z36kdWsSElhamGn6F3Fy1uk3nT6Vox/TzLFW2M0483t9f' \
			b'c7RSLqjBYdbQrI6XGqWO7GJZrrDnXZHjQM+nowXQeMGzKP1Vsa9VsYcVxeU9io9Qse3TiAas2N2q2Fes2GZV7GMVO8xT7FsPRV1Yt8+8FErW7107tt5G11ndzjg0NKHvnOU59R0Z3Fbn+S0HdF7z9qnN1uamO7c1ZTPoVzO4BphnRb+06vfnVv3+JKp/PNxP' \
			b'KHzk9bDCn8gL4YI6f6GVsE6q91zql3AJuHA9h/m61KKRhwbz/cGO/5M63pxJ5e94AbhTqT2r52XdYc6o+5zhna+aetAA9o/hnMH5bLWBXTbAw9F35Bd2zo/AdawffNAS9g+s3R9LuIIlQU9jDe4hWgMnuicWMRzmvKSH8u0nDvRXOFHgVlZCGnwl/km7DeaW' \
			b'8wDIaCjj63P7X2w7eSz3Lhz8V/PJ5kNFfoUufmc1oSudOrPYhvxqQ9dhQ91qQ/fVhrrmFa21rToUKPlvBb4Rmle8iWi8zq5muufLtGByS4mjjtCFjlZVNYYumJgiHp9seFtymlWFPbE6WiuZVkn2gz0SFC/oy+/n/U8sbwLnq8WO2+1ND2hvMOMp441emEs8' \
			b'7vrj98mWoJNvxHqtoy3syqsNOd2bwV9ZhHVwnXOyEzmp8SZ9BzLmBaXyLDlCv7yh23c0LaH8kYu2lcny5d9O/PE9hgXNcZ6ITjJgqt0tqSZsOki4b+b+0VyE0TUm0y8lc3Jvwp2U0t56mdr48N4/mjux6x7NUYhHprnbplm2nZ0i2+K7pIe+ovu3i1UHdlWE' \
			b'OwTvqMhriqfpRPStol0T4zXeLdFPSqXepTDvPsjflLTDoMPOglienbzYm/IXcSuM/uKl7TBOtCPZ1lMHXraVcvRmLqFwQa2Kmd7mj+ntr0mj8kr1Sav8GTWLV/q509APTsLtX8klGvH4cipINeozBjCkMkOkQP5cmhoreNerrK5BCDxpL5+eOHh9tlfvDChj' \
			b'fRKlpSbNPL2lds+tA7XKdt4GX2aku7SQ9dmwFhpMsHKVSkw3qxDppN1o2zMGaiufNYOtgFKfqLjvKenDH9BZOk3t8WHou/GVmYH6GXbfBo9u1eyi2aF56AGFPtFoOr9iU9/cJQJY7Fa9znpNXaIPPKDQJ5ptt9Lrdk/ny1C3TXPCQH3Bu2+D1X7V76LfffPQ' \
			b'A7pAJ9qEt9ZvKs1ZOk7jKScNNNyx+zY4HjcaH7Oa02jWAw8o9IlW5EnUXM2Fcxo0PHWgQbzdt8H42systN02Dz2g0Je1MmmQbnFP7Q6lz4VRFN818wMN5i5IHencvkrD0ekE4lgbpJUNdM1DDyj0ZQ3So2ygLtD59hCa84XalWNvSshobdEWwyA3ngceUOjh' \
			b'URS6oiXTeruj8E1RANtVe36TWwo5cz2IoGmSQRTv1uV+KgblWDbqeznUJMe6Ow5w8VnWXiaLua2MknHMk9UUsnXN/EBObIseGDwsnoP7U8EXsPgBslzVPZRraK4yQKDLWrzXIdC+ucoAgU54911IoMmnalKo7QzB0lf7goG+w9tX6Su84wkIeFmrNVdGzi/j' \
			b'ybrkTlmrZlEgj9mlzyx+72QmkPqEU+Z9lLpp7kOAyJc1Ta9W5K65DwEif3z+sbTE+/LA802q/+Pesu+N898+mQLFuWxU9iEUJ00ceiABRXhV/sWXKULTPJSASSjL28L3vght81ACinB5s/veF6FrHkpAEcaGvlHkudyiHWVNvoAqfhTfK9rg0vd8kfYpkxux' \
			b'7l8XsoJHeUvFE9PzHC7yw5WM/HTq0Iz+kbrbSk2Fxk/0zfhfi0e/HcwZ9FT8uB6/FrXO7VOTWPw8/8AMJ87miawTk1gN5EHb8YxWz1fYB4ZfaCUr0UaaiUtaZyAe2uGDO5ypc5k7lXmOI00ojk9pR/OJUUC0q0Wa8Ahh0ZYL2li6IgzTBgDxLXTFCXGuXIlp' \
			b'vrv5f9PuKV0=' 

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

	def expr_mul_exp       (self, expr_mul_expr):                                  return _expr_mul (expr_mul_expr)
	def expr_mul_expr_1    (self, expr_mul_expr, CDOT, expr_neg):                  return AST.flatcat ('mulexp', expr_mul_expr, expr_neg)
	def expr_mul_expr_2    (self, expr_mul_expr, STAR, expr_neg):                  return AST.flatcat ('mulexp', expr_mul_expr, expr_neg)
	def expr_mul_expr_3    (self, expr_neg):                                       return expr_neg

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

	def varass             (self, expr_var, EQ, expr_commas):                      return (expr_var, expr_commas)

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
				res = (AST_MulExp.to_mul (res [0].no_curlys).flat (),) + res [1:] if isinstance (res [0], AST) else res

				print ('parse:', res, file = sys.stderr)

			if len (rated) > 32:
				print (f'... total {len (rated)}', file = sys.stderr)

			print (file = sys.stderr)

		res = next (iter (rated)) [-1]

		return (AST_MulExp.to_mul (res [0].no_curlys).flat (),) + res [1:] if isinstance (res [0], AST) else res

class sparser: # for single script
	Parser = Parser

_RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: # DEBUG!
	p = Parser ()
	# p.set_user_funcs ({'f': 1})
	# a = p.parse (r'x - {1 * 2}')
	# a = p.parse (r'x - {{1 * 2} * 3}')

	a = p.parse ('--1 * x')
	print (a)

	# a = sym.ast2spt (a)
	# print (a)
