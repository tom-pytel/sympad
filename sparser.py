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

# def _expr_mul_exp (lhs, rhs): # isolate explicit multiplication so it doesn't trigger implicit mul grammar rewriting
# 	if lhs.is_curly:
# 		lhs = lhs.curly

# 	if rhs.is_mul:
# 		return AST ('*', (('{', AST.flatcat ('*', lhs, rhs.mul [0])), *rhs.mul [1:]))
# 	else:
# 		return AST ('{', AST.flatcat ('*', lhs, rhs))

def _expr_add (expr):
	mcs = lambda ast: ast
	ast = expr
	mul = False

	while 1: # pull negative out of first term of nested curly/multiplication for consistency
		if ast.is_curly:
			mcs = lambda ast, mcs = mcs: mcs (AST ('{', ast))
			ast = ast.curly

			continue

		elif ast.is_mul or ast.is_mulexp:
			mcs = lambda ast, mcs = mcs, op = ast.op, mul = ast.mul: mcs (AST (op, (ast,) + mul [1:]))
			ast = ast.mul [0]
			mul = True

			continue

		elif ast.is_minus or ast.is_neg_num:
			if mul:
				return AST ('-', mcs (ast.neg ()))

		break

	return expr

# def _expr_neg (expr): # TODO: this looks broken
# 	mcs = lambda ast: ast
# 	ast = expr

# 	while 1: # propagate negation into first number in nested multiply if possible
# 		if ast.is_curly:
# 			mcs = lambda ast, mcs = mcs: AST ('{', ast)
# 			ast = ast.curly

# 			continue

# 		elif ast.is_mul:
# 			if ast.mul [0].is_num:
# 				return mcs (AST ('*', (ast.mul [0].neg (stack = True),) + ast.mul [1:]))

# 			elif ast.mul [0].is_curly:
# 				mcs = lambda ast, mcs = mcs, mul = ast.mul: AST ('*', (('{', ast),) + mul [1:])
# 				ast = ast.mul [0].curly

# 				continue

# 		break

def _expr_neg (expr): # TODO: this looks broken
	if expr.is_mul: # fall back to negating first element of multiplication
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

	# elif ast.is_mul:
	# 	ast2, neg = ast.mul [-1].strip_minus (retneg = True)
	# 	ast2, dv  = _ast_strip_tail_differential (ast2)

	# 	if dv:
	# 		if ast2:
	# 			return (AST ('*', ast.mul [:-1] + (neg (ast2),)), dv)
	# 		elif len (ast.mul) > 2:
	# 			return (neg (AST ('*', ast.mul [:-1])), dv)
	# 		else:
	# 			return (neg (ast.mul [0]), dv)
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

	# elif ast.is_curly:
	# 	ast2, neg = ast.curly.strip_minus (retneg = True)
	# 	ast2, dv  = _ast_strip_tail_differential (ast2)

	# 	if dv:
	# 		if ast2:
	# 			return AST ('{', ast2), dv
	# 		elif neg.is_neg:
	# 			return AST ('{', AST.NegOne), dv
	# 		else:
	# 			return None, dv

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
			b'eJztXX+v3LZy/TIFni+gBVaUSJH+z3GcV6O2k8bJQwsjCBzHrwiaxKmdpC0e+t3LM2coUVppV7t3d+/evcLlXUrUSBwOZ474Y0g9evOXf3r/649/Kf7y9MsXX76K8YtnX3wTo6+efP3s1Yt48MXXT55qVGpsYvzZ81dfvkxxmQ6MPuDzL/GMV/L72bO/fv/0' \
			b'yetnr/X45ZOU+ll3+Lfu8Csevn7x5PU/fxZz+xdw0R5I8tNvv37x7zhrD15/8zV+v/0s/j57+dU3//76mXDwLXj82xNcfPn81bfg4fmrb/4KNp+/lDvk91+/BvULKf+XuPrFt69Q6s/kzqdfvnz5JMkECV8//+s/f5Oy/zqxh4PPP3shHIKNf40/T15+hcNX' \
			b'n2uxcfRZd/i37lCL/ezF62eakoSGZ35DRiIDIHr55KvX33yJx38j5X72b09fpMuoi8+f/+3553jMU1aE3v7VCxFAFE2Sxb+9fvZUCD5//sUXoBd2v331XFThyavPIS9c+BL3S5ZRxmWvHlTwMY+n/xIPP/3xw6c/33789Gd2/Ckev3v78f3v33/4+P2PP/z8' \
			b'6fe3H7PL8TBGb4Xs/f/89vH7T3/89v5jOvn1/X98//c/fn3XXfwhHv7y9vfv3334WY8+fvjv7oi5fXr/6dO79ui39ig95u0P3eHvv7e5/f3tu9/T8W/yVCb3GPglHf78U3v406+//0c6/uWPn7//6Zff0umPP/3ZHf7971nB0uGfb7vidk/HY+JBOv39/cf2' \
			b'0tsff0yH7/74+PP/ppP/+fS+4/+Hj2/f/ef79vRTnvmf79vy/PHrTx9+bfN829K/60ogoms5/NA98o9Mir+2LP3w068fWlY/dLKN/LSy/en9u/ftSdSNjIPfPv3+IZ29/y89aln58HPH7bsPv/zytnfy6S/fFW8erawp6nBTyIFd46Au8ROT1zd6Gs/kqMJP' \
			b'ES+t6pteAs9Mui9er1ISDoVqZSVeF49MUcXTsqiaeHCTUjWtTVg1ODA1f6wvVsbd5EnGbSTZkCfhMB6Vhj8OGfDx8QyH8agK/LEsQzyKeQtJlEITqSr836QUn58FjZGEHEsUrfSpaOEmpWpam7AyckNp4yVIqCxqf6Mpq1LKXTr8+MKBU73o5BBcikDjc8iK' \
			b'nqbjLL1ktJKiGvmvbLpscIDnajozicxpIokqKVTQQrnQpmqa78jW/YSVkRqvYnJFRkr+WLCg8u6SUJ1dKg6hlPHfFVBB1qrFASg8f6yWNAq4kuqI1YlqRqVQIDHBZieOERJwX5Ry5C/VTxQUudf0VT2SlJ2WmxRl/xS122wmhc2k7LTaPO3dsKpERSrIvNEM' \
			b'oPjU7ZTcna4qqno0EuMLYwrUVDxyuLGA7AyrdYJCoMHPJIzV2CdcVaIG0OemsK1yxmKILpeNWg0srY5gUmXGg4ttepdSM6XuUixTbJfimOJSyqoU/TCOP9a1PLZJTZ6EQxTA8CfK8eamOwRN1CyTPSXWQEX89LygFVZDNwlEUWqimco4FFUuxOoyUkXlmj8O' \
			b'pk5bKNdyKNIDciZ0YcFiGlPS6Uq49vqYKBZbQD94OU/WhHguxWr4ExXpRs+jUQlva/44IANZkjrnGwE8GWSqZ451CnhYtxCf9MS26CCoSnSIFh5FlyjWojyizcqITdKrYdqdHeA0kqesI4IT5CK9adojr0emTAcmHRD7vMIs4IrvO4CBEaFAw4XJCHWPRIVa' \
			b'vQSDfKThj1u3FgeBsDprx5/sjekUjGvLH3lZsnZqK4c4qtPFGz2NZ+kCcRBvpzVlViWpwrj4Crd4Jdg6PSCerigeW6cLQqpJ6a41Cw24jXgZmwdv1kDFSFyzKiMIRBWsUKexYiIURbGvYdSNK5qmCL4IoSjXEVHXZfyPdr2uYsUA3q0YWIi3RGUvpcKrqPVF' \
			b'lCuMP6pLiVdqVYSoL1HwoYhoG+G08UUTCr8ufFl4U/j4Uov3lgaxjf8u5oH/+FR5h0RbKuXfQ+wRTQQXgC7R3iJORGAokadkGpmNIiwjP74uvC18ZA8PjSehCLHYDtYTLTjql28KHxUlFFHuTeTLFE1VNHXRxBviW7yMOUSQjC0QJ8YSX9xRqWKbI1pbNGcH' \
			b'24hsRh7WURgRUCu8VZE7Sh7z/K54tMYL+82jKHLoVi2nj6Lcy1gXj6LwedUwmW/3WAe4+gbNJzm3iJZaOmEtBdaDZfVEsbICGifnyATV1TQkC1JtjxpGxrJqWYd4qNwb5JmLqZ2vEkVyqB8Rn9RFqhMaVkiGZcWwenJUCVJ2Y1KjtFop9aQzIhEKInJlVWms' \
			b'PWOeThW1YfkbLbcRuZwuX1MzX2NOnA/rs1T4lIwWWzujrUHmi8jPDG9G4a2uF9GfWfTU9gioAjwUBsXQFloLm8qYl6stw/mZz6o+r+7zvIZCeh0ITsdbiljaInK+qOdR1dNo87XS3oW2foxJr323AMaZX4+NVEmJHh16cejCoVrQ0UNtRYksAj+qwP16Efh5' \
			b'BV4uAj+vwM0i8HO+VX2lvcvU21yn4YOSQz7LC/WcnR+XxnZ0TMPoGKppUjVxOK7U2uLYKYoldVZXS5Wdt8pqqxXDQVTPCvGpQry0kB5Yj0guQi1LVdYyqDazze4pq2A1lTILqePPqzWfUfuk2nyGl+QrFZzXoT7HsjZs7a3BcVj62pib0BGKhkPeDVGwqXXm' \
			b'QhWq1AHxUt9tlmpoKVVHqUKWEGaUZog5mPsrlagvtCtnrq9krGFHiHC2ZxBXVVCinhN4Y2ny8t3nkulLYF0PtFMamWvarE2jOFYbNkHbPd3MsuGUslkmiU/bA4vSNZymX0R92rYjHIx0Qj7Gi0yPMybpFr09tYyjAM3SzTyvWovI4YazSP68kq/NIvJzu12s' \
			b'F5Gf2TUwsCkC6Rl1KovxIuJjvjWlZUKRLM4VM3uPVtrIZ8psxNcVfoZWbUM6n0vNzRSmESQ5oXsk+6klXxZw1UNUi77AhUnxjGPLk77M36njM5cFyVADL/IGUuiwLG9r/dYl30UFtqhAyTpaZDOivfIygAcN9VRXRZS6GkImvTkNq8smZPpb1FUdoDz13lPv' \
			b'vUkKz7fMIupuOsokADeC4ItMRK0giodb/PphF98+4OLDS0LwwFMJHlTh38A34cGVGn4YUuV1w1aitPWuu8QNS+wCm+G9abdG28zjXkQywXrTrsW4gzf2OrTz/Ibz/Ibz/EZaQKU2dqwOii6e32ceLnJrrQBRrns/+V7SAq6gHPaODLZMazHLKxDko2DUD6u8' \
			b'AvWGWxDfBNVVlEY7c66+itI4LU1zDaUBY4bePIZOPOq0gy1L8EK+ka1PEMX3cMWBueqGI68Vh0MW7/9zrqmzIvaaVVOyaqJEqzQXVOlcUHWjMxhVt9IeY/N6isgotT6l5GlNGqP1rA05mVtaVkgee4ZJoPGRQMoi2eM6xalSt6tNcVRl62XQCVEEq9KArtGB' \
			b'XBmPXeDrFI4CJizKfvQlYdR1TwD3Jr0NFPzTkqSSLw8Oq1dbRhMqPmewMqasx5PtSDJG7DS1YmqlgznVlS8JeYOhquq6h6pkjKpa5mXYgtZZ6Iavl4aK34jit718uVZi/lqdJNh6ljnF72ShC1tgtc6Ms10QOFPoaNeOT3Y0Kdek5nitzfE6zU6ymVizmViz' \
			b'mVin9mG9+C0fa/OVNUXOTlJqRGibup37Ndq8qFlB1w19sVz19HuloTbGAte0kDqNDctNtWkXf9U3qXl23zvYMW+r9mlTY5P2aWmflvbJqGTMcxGYpcAsBWaXltPR9wsTGQ8XOS0uxOeGU6sG4rFvNvfOc2hhRJaxLWn36oyZOxqFo1GArGgr0z24mdJSB4Pw' \
			b'TEUPiSvdJVR2daXgmocmnDfQk4Z60sjbhp6D7bLjJDHPtzddsbD/LXbGxba40fpb5YMIPXXP85leBa0vf52F1V115X7JtE6roCvs5P/gqqB+eKUWraiTVhjVBnOTKxN8UKlGEoOAo7br4k2klZ3pMOaK3emQgwC51bdGzE9L4cA9Xhh8PfGdlbFJefNdRTHl' \
			b'0ugkLJ+tiIIdVAVfb6g9I68wry+hmi8gvG8w2i9A7dVm4jl2g8TGENgVAltCYDcI7GOMTYyxdhhL/LG+H4v7sRoeS+GxdhwrxrG0GuuqsZ0CNhDA5gGQFvY9xmbH8ArGxAM218J+T9iCCJWFMQgMQGC7CjS0sTsDKgQb7GLPWfCOdRNrbGceKx1LJtDlQncL' \
			b'qiMyjWmQKr76gVqH0zBgAW7KUZgG/ihQIutjTfGLJfjqhOy8X8ge8kG2n5cPfzTYyX2N7enX2Bc9nuFjAEE+mVDIhyvkexAGFFELVwGp2N0/HntcFRKDLfrXuAmPM9i1Ht+ZQKpsFS/PKPGlCYP7kAOuI4sge75zm/sojVWU5qqRj1TEBzvZk9/Kvu6y0z4+' \
			b'S8GPOMQ07GmP/fYrFsXjCTG3Zq0MO2EamcWr+HYI9vqXrwms+XkG2bpedvc3st3+qgEx2Fzjua6Q/eBRAlPyOxrYfR7FqyQP7G0fiRpkHBM8yoanruWLBVLC9NUUPAdb2sfjqAMrb/mpCitf35CPdKBe8GkP/KPoMVE+JBFzc4EZBezGjzslE/xjk3sITeSL' \
			b'VCQ3qNf4iKb+DkYLU+2ZaTltqXWHIz2TrbuWZs9w3XFsd4Bp2025nGfO98KUy01zxvDzVpMWoW1YsZ1hx1aoYsZ205ptZ892zKLtqWxamKpqifm307LtbNu+P3aNzIa2bXdYd/GP+jFA3T4GrDcuRtX/SePxDYTkk6m3XatG2x/awOhbOzp1pRh86j9qpzIk' \
			b's697jaPdNl92Zs+20GhLChCw0azRkdpGG2UcZIFJYUd6tKiAX7qRSdvK0RZO1wXNYEMWLiToyH0BtPs21qLG1mcCK3YALTUhRaBkACNo8WGvpRZG0Im2fTgRKNkCI9jhC1tXwfNpF6RgcHcnrDQZrNQKLesBvERaLIxrYaaUZirsj+q4RlMYyCKRkwhdcS/w' \
			b'0lJrjNGCRg4xzrjuBQANiZ3gC44VW0IzH15AG3NHlANMPG/DBtiU0yFoyWw6Agygid5MBgCTRMQmL5lJcYFPpJFELVkwZEojy0hLneEWHgC4AkoNEEolqPCU5JmDlODTODR1jGNOYDdIUSqAKeF+E6U0f6u14LX+MqjS/FrAsuExXgvRJB9TWbx/DMSMOvwY' \
			b'mBh1+HEsHVCsalEs9ZbYYNHWyuWDF5GLMjg2ci2oNYFaJXQFduvXPEKjKLWHtC3UEikJz3FoQtGeaJKvlFjBqmzBivfOAyt5kryQe2DVy2kDrMptAUglLEtRBae3EPvAKO8fccMzwaokES2V7BQmQCURM3Ja4hyoymmgUoEqUCkXM4Gq43smUKkAlaMRoFKR' \
			b'aQ14LW0GVEqxAVTT+FQPWln3FJyWNtUZ0QkFp63WE9CUKNaMoVtMAjTVvSDQVGfQVHfQVO8BTTWhqR5AU57TBjTV24JAU922oLZR+sCIuESpMMlluRCYagJTTWCqCUw1gakeAFM9DUwqTgUmZWMuMHUczQMmFZ9yNAJMKjCVv9fS5sBEikNaUHZBqAWh9kQo' \
			b'FIhW6yYQKlGsGUO3mASEcr0gCOUyhHIdQu0xkCRP8hL1ECrPaQOh3LYgCOU6hNpC6QMjRSinCOWIUC1ZqXGg5JxGzMYpTY5QbhqhVJyKUMrGXITqOJqHUCo+5WgEoVRgKn+vpc0RihSHIJRbEGpBqD0RCszSapsJhEoUa8bQLSYBoZpeEIRqMoRqOoTaYyyq' \
			b'5FhUORiL6uW0gVDNtiAI1XQItYXSB0aKUI0iVEOEaslKLVOg5JxGzMZpeXOEaqYRSsWpCKVszEWojqN5CKXiU45GEEoFpvL3WtocoUhxCEI102Pp9wanmgWq7gaqwATNNxCqENuGUQZYiY4EAlhMMkGP2iCAFTLACh1ghT0Ai1NziHqAlee0AVgbzAx5A2aF' \
			b'DrO2UHqNFLOCYlYgZrVkpRYrUIROI2bjtMg5ZoVpzFKJKmZp/nMxq+NoHmZpWZSjEcxSgWkVeC1tjlmkOASz/IJZC2YdiFl4CAfQjY6eI6ZTWo5ZLR0JxEWNSciy7AVglsnG0E03hm72GEM3HEM3gzH0Xk5DzBpwshmAWaZsMWsbpQ+MiFkUD5NclpFgluEg' \
			b'uuEguuEguuEguhkMopvpQfQkUWJWYmMmZmUczcKsJEHlaBOzksC0CryWNsMspTgEs8KCWQtmHYpZeADN1yhmGWKW6WNWoiOBYBaTkKXpBcEsk2GW6TDL7IFZhphlBpiV57SBWWZHEMwyHWZtofSBkWKWUcwyxKyWrNRiBeVII2bjtMg5ZplpzFKJKmYpG3Mx' \
			b'q+NoHmYpo8rRCGapwLQKvJY2xyxSHIJZ5XpxtFrQ69bohYs0ZJ0URIzLtaCXgBdp1EVXJwiNThCmi0GP2iAYlk0Qmm6C0OwxQWg4QWgGE4S9nDYwrN4RBMOUcZNKP0nsAyOFMZ0mNJwm7MhKLVmgLJ1GlpGWOoex6WnCxJvCmLIxF8Y6jubBmApRORqBMZWZ' \
			b'1oLX0uYwRoqDYKwkjKkqWYEpYlQfoIBObgeSwJxg/jDd1kRpmmJCNBGofSjOEsQHfvGIXYD61kANXWDXuNKuccWuccWuMaL4cImqoqUmGYBak1StsgCgrrIOctV1kKs9OsgVO8jVoIPcy2kI1ANONgOAOjFuUukniX1gRKCutI9csY/ckZVaskBZOo0sIy11' \
			b'BtTVdB858UagTmzMBOqMo1lAnYSoHG0CdZKZ1oLX0mZArRQHAXW1wNgCY7eGMQstEEPWRUOIAWOWMGYJY5YwlqhJJjDGJKiV7QWBMZvBWLdoiPfOhDFLGLMDGMtz2oCxPieoySFztj1KOGYng+CY7XDMKo5x5VFHVmrRAoXpNFIetdg5jtlpHFPeFMeUjbk4' \
			b'1nE0D8eUQ+VoBMdUZloNXkub4xgpDsKxoevsgmMLju2PYw4qIIasrmqIgWOOOMaBP4mqoqUmmeCY0gQ9aoPgWOa2VnVua9UebmsV3daqgdtaL6cNHHM7gsCYMm5S6SeJfWCkMKbOaxWd1zqyUksWKEunkWWkNDmMTTuvJd4UxpSNuTDWcTQPxlSIytEIjKnM' \
			b'tBa8ljaHMVIcBGND/9oFxhYY2x/GGtS/GLL6syG2TLWiHAJjDWEsUZNMYIxJUKumFwTGMt+2qvNtq/bwbavo21YNfNt6OW3AWLMjCIwp4yaVfpLYB0YKY+rhVtHDrSMrtWSBsnQaWUZa6hzGpj3cEm8KY8rGXBjrOJoHYypE5WgExlRmWgteS5vDGCkOgrGh' \
			b'E+4CYwuM7Q9jHpUvhuwVxrhcvOJy8YrLxSsuF2+pSSYwxiSole8FgTGfwVi3vQzvnQljnjA22I+il9MGjPkdQWBMGTep9JPEPjBSGNPl4pJxlhdhzBPGPGHME8Y8YcwPYMxPw5jypjCmbMyFsY6jeTCmQlSORmBMZaa1kEqbw5heOgTGtnjqLjC2wNg8GEOd' \
			b'c4y/1jH+mmP8Ncf4a47x1xzjb6lJBhjTJBP0qA2AsTob46+7Mf56jzH+mmP89WCMv5fTEMYGnGwGwFhi3KTSTxL7wIgwVusYf80x/o6s1JIFytJpZBlpqTMYq6fH+BNvhLHExkwYyziaBWNJiMrRJowlmWkteC1tBmNKcRCM+c1tL+41kvk+mJ1gL4wFz7Y0' \
			b'y2qog+yHUfIILTP6l1T0L6noX1LRv6S9gWTSMtOLQY/aIC2zzL+k6vxLqj38Syr6l1QD/5KyKrOsNppm9Y7gdepSmRcBSANt+hZpoHVuJpW6mVR0M+nISi1gMLymkWWkhc8baNNuJok9baApG3MbaB1H8xpoKkrlaKSBRgKrleG1tHkDjRQHIVtYkG1BtuO1' \
			b'1BzqXJDN8Ggtm/dKY40zADVnAGrOALQ3kEwaa0oT9KgN0ljLZgDqbgag3mMGoOYMQD2YAejltNFYczuCpwNw4l3KL0226VukydbNA9Q6D1BzHqAjK7V8gRJ1GllGSpM32abnARJ72mRTNuY22TqO5jXZVJTK0UiTjQRW68JrafMmGykOATazuAGP45l+oOzh' \
			b'4pobxzbst73bLbgpuPcqI+TNeQHDeQHDeQHDeYGWmmTiFswkZN70grgFZ/MCppsXMHvMCxjOC5jBvEAvpw234GZHELdgZdyk0k8S+8BI3YLTyndZLcoyuixPugdzfsBwfsBwfsBwfsAM5gfM9PxA4lHdg5Wdue7BHUfz3INVmMrRiHtwleQkLsKNugin+szd' \
			b'hEl1EMyVC8wtzbbbNttQsTRsq2u1LNdqWa7VQhQfLlFVtNQkA6xpUsyYR20ArNlsxZbtVmzZPVZsWa7YsoMVW72cNvawNjsCYC0x3pZ+ktgHRoQ1q4u2LBdtdWSlliwoUxpZRlrqDM7s9KKtxBvhLLExE84yjmbBWRKicrQJZ0lmWgteS5vBmFIcBGOXtRZg' \
			b'43shC5idBMxkpfZJlm+5wrAfarQTatgJNeyEGnZCDTuhLTXJpJ2mNEGP2iDttKwTarpOqNmjE2rYCS21oYZWOVCtlL3uy8RSqRlstNjcjiAtNi2CSXKYJPaBkbbYtCNq2BHtyEotY6BUnUaWkdLkLbXpjmjiTVtqysbcllrH0byWmmOrn51RM94ZTXIT3qSl' \
			b'NuyMKsVB8LasEXhYwHaaVlqFipV2SqWtNH5WRCInEVppFVtpiZpk0kpjElppVS9IK63KWmlV10qr9milVWylVYNWWp7TRiut2hGklaaMm1T6SWIfGGkrrdJWWsVWWicVLVmgLJ1GlpGWOm+lVdOtNOVNW2nKxtxWWsfRvFaaClE5Gmmlqcy0FryWNm+lkeIg' \
			b'GFuWCCwwdnsYs6hSMWRd6mS51MlyqZPlUifLpU4tNckExpgEGLO9IDCWLXWy3VInu8dSJ8ulTnaw1KmX0waM2R1h1R0lGNtC7AMjhTFd6WS50qkjK7VkgbJ0GimLWuocxqZXOiXeFMaUjbkw1nE0D8aUQ+VoBMZUZloLXkubwxgpDoKxZYnAFcEYh5WPD2dm' \
			b'AtLcANZcDm0OdSzGrd1Oy26nZbdTtz2y7Ha21CQTaFOaoEdtEGjLup2263baPbqdlt1OO5j77OW0AW1uR1ipanedzW3EPjBSaNPOpmVnsyMrtWSBsnQaWUZKk0PbdGcz8abQpmzMhbaOo3X7qN0Ap6JUvkYATh/UPrLxWmzFOEnLJHkY0h15K297doA72dZt' \
			b'dwVr5XZoO0vrDFvKQAGqXd4cAdUsbgy6Ve5wV++WYs0Y7htMMkGP2iDuG/kmubHu6m6j3HqPjXLTRyzr4U65UqXd/6YfxwZXPQ7hwdFtlbuNEq8g/QJmmfY1p/uG7pabOBAt1fVPpS6AKnUFVKlLoMrhGqh6esfcJF514VBuBmBGlsYBDVBRz94zVyrI084m' \
			b'1kEl2Wl1SGQkh0g2aLUpbYtlURcec99O+5ibXHbYNVw6cEvsOhS4zgxWLVC5YvuXdM/VxrqrbiLqgM6hrhwHn5ZizbgsU1LMzJW9APBxmaO/6xz93R6O/o6O/m7g6L+BM4Pch8xEjXOdW/82Sh8YsbXUlnXWl3bdtO9+khNRJOU1s0mUlWMXfCjdlm/qpiep' \
			b'UL1WR4YZSrHjI3ACGcM9thfIeFiQUWHqVkyqmoCMRLFmDMhgEiCj6gWBjGxQ3HWD4m6PQXHHQXFX7YKMalsQyOiGwLdR+sAoh4xqLmRMj3MnOSlkaF5zIaMrx07IIN02yNAnqVC9VkcOGaSYAxnDLa4XyHhYkGHh5yEmZScgI1GsGQMymATIsL0gkJENQLtu' \
			b'ANrtMQDtOADt7C7IsNuCQEY33LyN0gdGOWTYuZAxPaac5KSQoXnNhYyuHDshg3TbIEOfpEL1Wh05ZJBiBmRUQ8/yO4KMZUTlfsx3oZ7oM+6aCYhJFGvGgBgmAWKaXhCIyfzEXecn7vbwE3f0E3cDP/FeThtw02wLAjedh/g2Sh8YZXAjYyeOvuFJHFqkQME5' \
			b'jZiL0+LmQDTtGJ6kqUCkXMwFopbveUMmSXrK0QgYqbxU/F5Lm4MRKfb47nU19ANfQGkBpW2g5AvHnWGcnwClRLFmDFBiEkDJ94KAUrYbjOt2g3F77AbjuBuMG+wG08tpA5T8tiCg1O0Ds43SB0YboMSdYJI4tEiBgnMaMRenxc1BaXobmCRNBSXlYi4otffP' \
			b'BCWVnnI0AkoqLxV/Km0OSnppD1AaenUvoLSA0jZQCqgkMdSJ+aaWYs0YoMQkE/SoDQJK2XyT6+aa3B5zTY5TTW4w1dTLaQOUNpjpkQOUummmbZReow1Q4ixTEocWKVBwTiPm4rS4OShNTy8laSooafZzQam9YyYoaUGUoxFQUnmp+L2WNgclUuwDSkNf7AWU' \
			b'FlDaAkqoHjE9RiOg1FJoHPVKk0zQozYAlEhMUMKxghLvnQdK8iQvUQ5KvZyGoNRsDQAlYdmksk5S+sBoCEqSaUtVapECBec0Yi5Oi5uBktCOg1KSJkEpcTETlDq+54FSkp5ytAlKSV4qfq+lzUBJKfYBJfGsjkBTRNgoonAiPIVsS5ZKYar0CamqMbBaJ7yq' \
			b'xiBrnVCrOrEzTzMDvuoiWvMptmc5AMdQN7H8ZRRAaU2Ha7HgJXw5BN+MYlw9gXORDgu5tuEdPnE8xwloL9xrZmKfPXQpHTQ/ajO2gMSm3PJtgqj+nJtfxbJhRVwaPEddtvgYmhYjV9BcPEkn7I0OpSMOosgAy1UlKXkAYK5Q8yaNq5frRqBzhfo33Qi72WOE' \
			b'PTkQmcEQey/nIYCuKnAYj6t6yGV3k2UEdZWR8apgASbvMBx/N3YEUQ0H4ZWq1EIGwwsaKbMqgAxRV3DYqbBmF2Ck90rjDCt8HaEWAoOurEMPcjVLWY6YfzlS+c2xd+0SAJvtXkepGDM/IkmtqP3Wgf34X7ai1/r0Kq187R4pOkR+LCn4jeAcfxs5bhx+gdO4' \
			b'HGFaIhAISNtoDUOIngJnB0wGIBONCb859grw7kbd0QlCwVhgqREU9QqP+QTfjMm9DdibgrwM7jZg7gB42wVpc6BMIMwNoKttstltcLUbqNQAYQ6hboGpRaIRGEoYtDcAbZ/gS2izSstGArFk5YedwllTdUNAmESDHAk2MOBA699t8rNsHVYOE+/bd7JsWKkb' \
			b'sdItraiTGmpqD0U5XK25rqsRk93HXHc0L1Zp09/7YrNdKwF19DBsF7W+Yb/7226zxxu2Ppft5r0YGnF1VDtG6WLxIlNl5Opi7PrWr+Fddr3bplNv4dLsWhjL/21q8tfHtnOB1zW+0+uks3dhdj+0eSOf/dzL7ot/RNV6HLmUNrbfr43d7EIAdyQQoOHbZPhl' \
			b'uK6XeGvszfRLvB06iGmV1V0TI30V+gCAoS2sAbHouaJ3hv6XzZdKxv9wFIAQu0q7/M8HiPIsINGCgmtBAfVynQ2ABATG+C0NAN2iH6NOK9gHt0SUwduhD0w3EiWXkb9UtHwsrvseCZLX0nYIh/fO64nx0SMiB2FjjdHNegQ6Zvrj3hl81DP6AXZmP6A8aZth' \
			b'vL1Q55DQfvHj7O2GQV9A6sSvRyChnrvI505hAfU8p29g5vUNjH4PcrJ/EJXjQkbgxq07WlIsCrQKg5yy7e25GgmjcxCnaChgsWY8xoh2OaPn3zYa7IjVp8bBCRoFl9ZjGFq+OHvJNNEKOrGSnf/O2TJw52wcgAjPkHoMM9BAGwptI2HYNnDaHBg0AmLSm7sH' \
			b'h+MMz190N8HfZlygs+zG30/DPvKw/D1o1d9qWL74R/M4gjg6+PGmi7TQKPJbvbMv0lpnvqPnWuu9fQ9PvYOD+Gjc7t17sbbLos162+4al495H2S09gx2627f3p7t+7PNfusTza7VF2rH2B3ukowZ2lpWR2lOZyYtpTzMruGSdsL5NqmC2e3pnRZeH2bh7gwW' \
			b'nlk3PCLv5O18IuteLHtGq7pv1aiHu3tZn9Soj2rQ9jCDbs5s0OVi0A/eoJvFoGcYtDvMoP2ZDdosBv3gDdovBj3DoJvLHAm7mtGvS7LYCzLW41gmFh1dxjjXLS2x+EeJ9XkRaGR42l+kUYbQzS6fwz4nV7WdckZ5sdfxUWqoOCaLz/dOvZPZ4du/UMMd2e7k' \
			b'ctgtL1c7WMZ6qS/ZGUtQZy099Znv6NUYMVcc9//3egnLDb0ln5c+7TRv9easpVxSePEGHfPxyOaOy8cRLfF2jiVeLHyx8LNauN3439PC7UO2cKsWXs218LJ44ze25aE5GzFk7rrT9I1XLJdm2N+RJhnKiIGIcdhNhRbltVhGHFQxB/u9ZLoIPfRJ/SBYUboR' \
			b'hWuVrVWTULRbnaQaHK04o1U0lDHFKV5vUQgHC404pgjmCVcCRbkU7TxJTsFDK1EOFh1ZpGBXLDH7tp4+LxRTW8psl/WUTucyr24hczMu9nso+qYDwg3xJyQ7WRXUh1fB1As9qxG757t7/1qb9+6deuf6rEt8uhqWYvf/+++/rNp5cc/33EHaMfMdNaFEwmfX' \
			b'm1z330B2rlYdPL6TKdkhYzn7Ktoxx1CH8LJ1TOZghZzZauNinlmDKzk4HTiMsreinnYzjB2DmhZ7jcneYlHwi0LfqULr1aOOFt6BQnMvNv6fX6HrqNDYGM6bx7CsqAGPYV1RC2Is+zPFSlkU/Y4VvbwORS/b/4tUdD9P0W83C3VmXT/xbiWtvk99/PQ2ui8q' \
			b'eKJpoRH9l+xOqf/y/Nu2XuQpO2wAe0WMfSd08guhov5hUf87h3tR8HOqvD+xyvujqLw/GPZHFD0WdbeiH8Ph4Hy6fq7NqY6q71Llp57+P287R4p0rn0bd03cu52D/sfzrTmRqt/xXmzHUndRzfO5vJxO5yW/O9+wdKfib5+4ObZf2aL7U7ovU8934PN1QtC/' \
			b'jC17d1rA9mm0e2IBF7Ab53GsoL4yKxCae2IJ/dnMszkb397331+gr/+trAPaewG+R9OGcktX/iBfYblAz/29baadqz27j/5iNq3ZoL4vzG3vlKZzoate9rYdt9jOBdiOW2znHtpOU7zBbtalY13KtwXlgi/e4ENp2MhSPMeMl2TsTbwGcVQPJDTYyLQySKgi' \
			b'RYwfreQL3lgIxa9LNdiWGBsSu94XCLAA1Rh5Pr4qgk8R1NiXvN1aGDuTDz8pgC9sVRYZr8yeuUSNnvqT5+nXNEefqLukholHV/Cdr3p/3danJk+XnOqRnMrhd+52ZCzbO7WL2/iJNv0s2ndYWtD9wd265pL27L8e+eM1I4vY5KNdWC4eMVM0ZWVvyTVgaSfj' \
			b'rpj7hyUFgzRh0+3N5tgX/iY5xRfqWm6bYvsflkBMXcNSgxgLz80mz/rF1jG28Y3DIF8xzF0/t35sFS5ms75NqMrVfoMQrzF8exDfHYRS21Gp5N/6677hF4ruO301v8/HndC/w/u6+wv5SZu0GWaSbdy142EblIN7pIb8GbUqtilu8yf8hkvSqHZf+KRV9oSa' \
			b'Jdt23GkIZX7S3P6RUqPx3X0+FZT1QqcLLFDZFghve3cqTY3tu8tVVlsweFl7154eOaB3caJHTwbWsTmK0qI3M09vUQG3DuiQTV5muaqB7qKWT4a11GDAykUqMfqMWYh84ruu6xMGdJNPmsFGYK2PNNy31PTuF+gsnZaVfL0Q3DBlZsAQw/RlltEumt1pti+u' \
			b'PbDSRzpNp1dsjMmdI7CIzaLXrV5jKPTKAyt9pNt2K71ebxl86et2VRwxYBh4+jKLGhb97vQ7FNceOAQ60ie8tX6jNmfpOOZRjhow0zF9mSUedhofsppjFuvKAyt9pBd5FDUv58I5JguPHTB/N32ZBV+6mZm218W1B1b6fr3MWMX7j9ROKH1bGZ3i22J+wDzu' \
			b'HtSRz81UzESnE4pj6ZBmNtAU1x5Y6ft1SA+ygbxC59uDL04Xci+OrZSU0dKj7QwD7jtXHljp/kFUeontz0I1UfmmU4DaZZ/XhlsKnLiuIhjMiEXxbiT7sSMqx96zvrcGzlT38wB0zHDrYn6AT9VeN/RuVp+47VT0cus83MQzaL9u9mXItSkuMlCg5T0UqC8u' \
			b'MlCg+/WQjynQ5DI0iuhhjmDlvXS2gNfMZipeMhN3UMAj3oFz3rVnkPFIU2lS1vBj3ifAIXTfe/Z+7mgmlPp+XeGLlbop7kOgyEfcPO+jyOviPgSKfL/O7jW4f2Ij8v2DrKTI/g97yrYnzn/6KAWr8+F582JJzJUEVuF+88ZXUYWmuJbAKrwoD+jzVGFVXEvg' \
			b'Mpm9u933vwrr4loCqzB29KsSaxrYjaqNnpdrtvCj9N5Ass5LIsay9EJs+ud1XNJfeo3awbKveE8pH5UntR2nborBP6ndBjXqTO7wxfDfqAN+3eQr4ixqn+lYKZep3DYtibUv3vWmvyK0XaHpN1dnqv8aPgk12Oq95MdK5IGVZqXKiCWmULpKl25FS5LhVAyd' \
			b'ypCprODDNiXxLmNjqvZz8dWKtJyPwsInGUxVIUULjA8GxKcgRUelsX99Sok03938P8xScfw='

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

	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                   return AST.flatcat ('+', _expr_add (expr_add), _expr_add (expr_mul_exp))
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                  return AST.flatcat ('+', _expr_add (expr_add), _expr_neg (expr_mul_exp))
	def expr_add_3         (self, expr_add, SETMINUS, expr_mul_exp):               return AST.flatcat ('+', _expr_add (expr_add), _expr_neg (expr_mul_exp))
	def expr_add_4         (self, expr_mul_exp):                                   return expr_mul_exp

	# def expr_mul_exp_1     (self, expr_mul_exp, CDOT, expr_neg):                   return _expr_mul_exp (expr_mul_exp, expr_neg)
	# def expr_mul_exp_2     (self, expr_mul_exp, STAR, expr_neg):                   return _expr_mul_exp (expr_mul_exp, expr_neg)
	# def expr_mul_exp_3     (self, expr_neg):                                       return expr_neg
	def expr_mul_exp_1     (self, expr_mul_exp, CDOT, expr_neg):                   return AST.flatcat ('mulexp', expr_mul_exp, expr_neg)
	def expr_mul_exp_2     (self, expr_mul_exp, STAR, expr_neg):                   return AST.flatcat ('mulexp', expr_mul_exp, expr_neg)
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
	a = p.parse ('1 + {{-1 * 2} + 1}')
	# a = sym.ast2spt (a)
	print (a)
