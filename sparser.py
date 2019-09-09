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
			return AST ('=', lhs.lhs, ('lamb', rhs.stop, (lhs.rhs.mul [1], rhs.start)))

	elif lhs.is_comma:
		for i in range (lhs.comma.len - 1, -1, -1):
			if lhs.comma [i].is_mul:
				if lhs.comma [i].mul.len == 2 and lhs.comma [i].mul [0].is_var_lambda and lhs.comma [i].mul [1].is_var:
					ast = AST ('lamb', rhs.stop, (lhs.comma [i].mul [1], *lhs.comma [i + 1:], rhs.start))

					return AST (',', lhs.comma [:i] + (ast,)) if i else ast

			elif lhs.comma [i].is_ass:
				if lhs.comma [i].rhs.is_mul and lhs.comma [i].rhs.mul.len == 2 and lhs.comma [i].rhs.mul [0].is_var_lambda and lhs.comma [i].rhs.mul [1].is_var:
					ast = AST ('=', lhs.comma [i].lhs, ('lamb', rhs.stop, (lhs.comma [i].rhs.mul [1], *lhs.comma [i + 1:], rhs.start)))

					return AST (',', lhs.comma [:i] + (ast,)) if i else ast

			if not lhs.comma [i].is_var:
				break

	return AST.flatcat (',', lhs, rhs)

def _expr_colon (lhs, rhs):
	if lhs.is_ass:
		l, wrap_ass = lhs.rhs, lambda rhs, lhs = lhs.lhs: AST ('=', lhs, rhs)
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

		if last.is_neg_num: # really silly, trying to index negative number, will fail but rewrite to neg of idx of pos number for consistency of parsing
			ast = AST ('-', wrap (AST ('idx', last.neg (), arg.brack)))
		else:
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
			b'eJztfW2P3LaS7p+5wPEAakB8l/zNSZyzwTpONk4OdmEEgeP4LIKbxIGd5O7Fwf3vl1VP8UVqdbfU093TMyMMp0VRlEgWqx4WySL55PXf/te73376W/O3T7968dXLeH3x/PNv4+XrZ988f/kiej7/5tmnclFy1fH6yRcvv/oyXVXyaPnAZ1/RN17y7yfP//7D' \
			b'p89ePX8l/i+fpdBPivcfxfs1vK9ePHv1b5/E1P6dcpE9HPzpd9+8+C+6y55X335Dv999En+ff/n1t//16jnn4DvK4z+e0cMvv3j5HeXhi5ff/p2y+cWX/Ab//sc3FPsFl/8revr5dy+p1J/wm59+9eWXzxJNKOCbL/7+b9+m5L9J2SPPZ5+84BxSNv4j/jz7' \
			b'8mvyvvxMik2+T4r3H8UrxX7+4tVzCUlEo29+i4zEDFCkL599/erbr+jz33K5n//npy/SY6qLz774xxef0Wc+RUXI61+/YAJE0iRa/Oer559yhM+++Pxzis/Z/e7lF8wKz15+RvSiB1/R+5xkpLEa1IMQPqbx6b9H78c/f/z415sPH/+q/B+j/+2bD+/++OH9' \
			b'hx9++vGXj3+8+VA9jt54ecPR3v3P7x9++Pjn7+8+pJvf3v33D//887e35eGP0fvrmz9+ePv+F/F9eP9/ig+pfXz38ePb7Ps9+9Jn3vxYvH/8kVP755u3fyT/7/xVBA8y8Gvy/vJz9v782x//nfy//vnLDz//+nu6/ennv4r3n/+sCla/QJ50/9ebUvySmsRK' \
			b't3+8+5Afvfnpp+R9++eHX/5vuvmfj+9KeX788Obt/36Xbz/WmfnrXS7fn7/9/P63nOabHP9tKRGTMufwffnknxVVf8tZ+vHn397nrL4vtI75ybT++d3bd/km8kqVg98//vE+fzXXYM7L+19Kdt++//XXN4Obj3/7vnn9ZONMY/ubhj2uJY/V9BOD2xu5jXfs' \
			b's/TTcMDNIAB3Jr0Xn9sURF6OtXF8Vc0T3Zh4qxoToucmhUpYDtgE8miLH9c1G+1v6iDtt4JcXweRN/qUxo+nBPD5eEdeKnX89w0lh9cceSgDLX6clI3KpPjVmNUQ3zb0f5NCuvqulysFUU64yKpLRe5vUqiE5YCN5hdUzBTlMBLadjcSslFMD+Xpp2s8lUAe' \
			b'evZGH1dAE7+DrMht8lfhCpcNk0Dzv3HpsSYPfVfCkUjMnAQikuFC9VIo3+dQCetKtHYYsNHMCYbyw980Gj+OsiBZLEFUzSWUvOTr8ePkQUzTMvPGcKpmIj4KHgNcdeNxoQB6L0S+a1Pd0EdQDgnfuHYrqL5V2zHU8JZqsdsKGr+kh7dm63b4wsagtiPT64AE' \
			b'KIIGb6fgcrsxIHhkK901WjdUI9Hn6eVYMTECRH1HDIaGbmbEWF3DiBvDNCe+DY3LTBhrlUuhgkgHSZR1TYSMIiT0MIeXEIsQW0IcQlwJ8QjxKWSjWCwZNODr8eN8zm0OCnUQeakoBj8bgSjxki9ihS5fIS4xzF62xwOpOkvfghTHOmIelSIQyzKVYsVp/qZq' \
			b'8eNJuIFBqmUv05EwNOEJikicwiHpdsOl7OQzkUCRGiHBXB0sAfGec9/hJ7LUjdxH8eK8tfjxhAXIEtc+Zyky4ZPIDhspaeQI1C4BQpvBPnGM0wkPGEfBnpFDIrVTDNUY4etEVp+oFwOf2CKsdEvx8p0DrMWy6ZB9nfi0Sh6dPEC7ToCVAAopEixoJgrxOmcy' \
			b'gtsTZqbModTi4JMaP76IIhEE1Rkpzz9V2xkEfq3HDzcx4UaCyEs+lx7eyG28Sw9Q3phsaEEzm6jqCGQ4V45axoii8gFHQsolcS494KgSlN5SKDS1i/FZVBRet3RDLZIhoIxvxdqM0h1rhWq2a3pqDGIugm9CaPp420ZgbVX8j+Ldxjanje2zJUSPEhclrI8u' \
			b'kjUiRmQLhvlIWMKBKBgqNn+9bfr4/ZhQJHbkF9OErgl907VNp5pON138pqb/2MbR21F2VEv/8atRjOJvzES8qHiNmgqjAYlAZLkocBEyIkYoTpDixczGFljFKutiwvQ513TR+aaLGW2bPpY+EiSCQ0so1nVNF1uTvom0D6oJugkxg7YJ8bOUgGKVJeojngUm' \
			b'NteRsaIGEiUuinSESx8TbmPkNhIjtnORDIp4PwoLlV9/3zxpqZl+/SSSneokkp4ukfYq1scTK0+NRbDDpeOnMdjjPtBlrakz11SPulB8JX0HlRBQCUqjykJAtB7RQofYAdWLelTpXa6Tm1XmLlyTTDyuy1ZLhRi5ooL6IBXk+H5ASiEiyDdFOBAsE2pAoAmi' \
			b'gCIxV044x7kLpumFW8GmKpVbMz3Ol66WdLU9czpATNVJfSu1ytvF5Y3ovpL9DmBOC8xZv5L/DsjPKgGBK4Oc0IMpkcst5U3FrIsWi3GH+a85oK71yzRLvRO9l9Uj08RyNbE0jV/Z9ORsagQkjHQ9RBNiDYBVgW4FjztoMgP3HxT1/KjbR109qiGqHpKKSJeV' \
			b'6CcneteuRL880dVK9MsTXa9Ev3RL2xnpheo0DJS620qvGvqddJBCGgeS8Q+NoVWaopCqwjCeEq1IKs5JvVm3Vtvlq81iMFWlsStutB9bF0kpYVkZj+ZIfJVeZwde7TAC1nkwdp9GqyUYpOzTQAG+afFJl4apHSYnOn76UAnaich7GbiHKtjGO8rf2jFnIgVh' \
			b'lIDOYgAsBitzHzLamtAScBn5B2zlQFkPyhIxGWgiFWMK5h6TJTINJMTrB1g0VKYHnHg3EIuHVVJgo2dMRHHqAt7roklj0boRg2IWEgV3OuE9qpyHj79ni480R60xOa3X6ebzd9HIkAaT/iu5LzAM6onMPL0frytdTzeQ6Vf+vQSde2bctS96afbuGKWpMCv1' \
			b'L059a1ey34U9R7uS/S7M1lrRUSIFtZitxetK51M3pQzmoMpqtrGgm+kYji+U2IRpLVk0OpERrsO19hYQVANNzmeMiQ4tJYArXyz3D8hISrANI9I7zae/F1trXqjFr2C0AuNTmFF7IvaeGI/0yVyeUXNlgwNsoIQPVvpMczEU/tALv8raDCWLM3gaHZO6yZTK' \
			b'tMK2RuZRmG/J7oEvOjE+Wp2V3MN5Lp0GZkD4lS5JTFlKHzcJ7EoC98hJQDYYrD+IMtDx7SMjwmua33+MxbbcCpOlAknBQy4rWV9osU/QW1N4ASrFDjMlnq69yQtC7sJYpc12Axp2Axp2A5oVI7RlbCjAg6mryfkdDC95QVDHDHb/p/NZRB5GQfxdia3YR/b6' \
			b'IVDySS8GuF49BA4nayO0COZhFEdG7rx9GMWRfqsPD6I4lDMNIyEN2yCxBaJ9VahtvuFNoegSm2SDITxzg3FagwGTdcXBhZv0WAiDcVODbSdwaVExRFYj00jmRiY+TNkGgIbz5ZYu2uAufhxXfBuVbeSbotjR77pc8yyTUxBDdPdW6p7c6E5EIi9/VYntZbEO' \
			b'dU4Ezkwa/9Uy7svDkyuWncvoAPM9K2VPvi4N7UIHQO90ah2kMUhroqjsJo3Em12jDRRqEGoQyq0ELp1c5EMW+sKDXlfymganzAMfnOJRKbNOzhRlWWYHA5qTAJkILBO5V8+ByprMKBArnuf6npfLQM9yMl0uE+VQwD2k1ePLHtLmQ9K8rWjeNk1VQhu00AYt' \
			b'tEGbtEC7Wjyf0EwrepjsXBcuqQmiWJTJYNGYHdfDQwdB34PppgeogwbFDC7EoDIszC9Zk9eR2Zukgd37HnVM3ImUuqRQQkodpNRBSnHRuMbcOAEWB4o5UMytmtFZNi5jAo8XTFmz2r9eHlidCEpH+3tjMz9POgeVoKsb0pi4h3B4CAdFa3KF+kc3Ucoca0C7' \
			b'IDDCVyNL6U2X5+fCo6POa+KUAE4J3PDA6DAvZk4k69CSw06L9uil/Xlp517atjexH9GwA/d1+GYnlBZFQOZisbfvE36fE7WyzDK+2D/GOrCPsNjMFzbxhRZ+0Dc1O1FLAUbiK0XAaG3bvG4bzdvj0VgrbZFHqTCeO2k8YpoxOSqLp6xRAbjpQJOF5ksyG4js' \
			b'oDnoVFNjQGLDxA2DukAzF0lDNWi4MeuluA5NEbU8PNofRHgUSkmbqBCZaPMJ2nmCtp2gHSdoOTKtRKZtA2jPAFpjTwvsaUE6rUan5dq0Vpvql/YloD0JiFhEKNqFmWyHadKBNvWiPaZoyyOqK9oYg3bFoC0xaP8L0rxp8weqE9r4l/bCpcV0tNoi8oSmxRa0' \
			b'0IL6YdQHY5ISC8Uw4hDeZT6GR87QhA1kkERGzbE8mgwaXB8rC4ek0L7wtNc97bZPe/c3vLc+nQISaLv5ljZib2nz9nhHJxb0fB5Kw3vb8/EVmo+8oB346cgFOmYhfraj3fXpJBQi84aaez7QgJp53oCejw7h1/nUDiQZvxEJsen55IH4sY7yo+SciXiNFNkE' \
			b'Op+Fz9WIMT0fHuD5+Afe8562jcfJDw1vKk856C2KE5lgE+m6Ca1kmvbLp+nkTeSNDR1rQocS8LEHreOTAvhkFDqcg0+IocT5Ib0Wib/pA+98z2c80OkiirLKpzE0fGCI4iNHKMX4akepUxnoQUsU0FzMTk50oe/gLIlNR/98eEP8Pp8YwuUl2lMmKeeUYSp/' \
			b'wEEFvkdCPV1pe3/6GmeTtuOnHDClOY9EP6rceBPs9yS8JLIDcVW7JTahD1CliK5N0quGAuxPJsM1tpH2t1ek9Uyxvg8irSfEuj0g2o6I5sbS7GbIs+NYMWG3LdWuyLWbkmx3TtnmjEW5dvnvoIS72TJ+j+Q7TMi4OyDlzb/sU0J495QwPoR4cf+P1cko+rH/' \
			b'lEQ+97iCdBShloykPta0dPeGvUtCAIi/LYKfdaYDsq+L+Mean1StBAr6MRSg+9d1oqhhEIY1KAsti8olG6YUxQdKT+mcVvDBSx0ShNS2AdKrm1KzaR0Qw4sfQYwTaNHbcELbOtGeThlOCG/9CFbUATiJ79NWWWQOdQhaaAT4ILx0Fbw4gRg1ghniB1fBDemt' \
			b'gBlwpCL1mBCGL54vWi6uybEVrqTvduw1Sh5mR4CDyIFxRrUZY/puGcxQ/JgDutRA03fFbYHOKDe16zuUziUftJ3B98qH+7a6EYzqWPZRTJ+eIzDgJYNMaVwcLlLyCr9AdJzDM0Yq+b7AVCJqDVaMU9MQVbJMsweHwQpkIbjqp9FK0nf4aJBv15Al6WXg8u1T' \
			b'ah+iXD4Fx3T9U0LOyMhPCRsjIz+NpSM0MxnNUjcKCoxoL/cBxATBuN5PjmAreu1AL+pIs+x24iMlKelHohvlSHIl7oLXKPFlx6ClKtBSGbTw7nzQUlCNWDgq0BqktgVaWxkaRHdcGIKrDqWejta3dYHqfhN2WWPMSlRhvmTA4gcaFyTkpdQ1YKk9gIXHCbAk' \
			b'/ZmAVXI8E7CEgqDwFGAJzVAToZPiVoAlMbYAazdO2ZHWdX9BatWxLohSVHjIq90BUSmGwlU0eguIsgPHEGUriLIFouxCiLKAKDuCqDq1LYiy+xxDlM0a1XQcqpRSGuATso6rr58zW1oAlAVAWQCUBUDZEUDZPQCFTyaAkgzMBaiSpXkAJfQDfacASiiGegid' \
			b'FLcGKMQ4RqNyK1KtSLUcqahQkFy/A6lSDIUropLXKPFlx0jlK6TyBakWDjTx1/CFAVLVqW0hld/nGKl8QarJOFQppTSCVF6QygOp8nNmSw+k8kAqD6TyQKrR2JXye5AK0RNSSQbmIlXJ0jykEvqBvlNIJRRDPYROilsjFWIcg1R+RaoVqZYjFWUYkht2IFWK' \
			b'oXBFVPIaJb7sGKlChVShIFVYiFQBSBVGSFWntoVUYZ9jpAoFqSbjUKWU0ghSBUGqAKTKz1V6CaX2IKJHMl7KXCNV2INU+FRCKsnAXKQqWZqHVEI/0HcKqYRiqIfQSXFrpEKMY5Aq7B5zv0d4VUbbV8i6LGSxDR+LcA/IUhhqV/0QuFI8RFB4gbxGiS87Bq6+' \
			b'Aq4ySY93FwBXD+AazeYNUtsCrv6AY+wqI+zTcbh2coEEu9IIew/sys8VZrgYu3pgVw/s6oFd/Qi7+j3YhU8m7JIMzMWukqV52CUklDJPYJdQDFUROilujV1SPUdgV7di14pdx2MXfQhDzlpG2TU0Lr4U7Mrx5IoXNMba9dARdulqrF2XsXa9cKxdY6xdj8ba' \
			b'B6mNsUtvZWicP8flSdg1Hadv6wIBu9JIu1gqlefEnxqD7RqD7RqD7RqD7Xo02K73DLbLY8GulIGZ2FVlaRZ2JRKCxBPYlSiGqgidFLfCLolxDHb1K3at2HUL7KKPQIS1YJcGdukhdqV4iKDwAnmNEl92jF26wi5dsEsvxC4N7NIj7KpT28KuQ46xSxfsmozT' \
			b't3WBBLu0YJcGduXnjF0a2KWBXbDJ4osUu8YuvQe78HLCLsnAXOwqWZqHXZJTkHgKu4RiqIrQSXFr7EKMY7BLtauh1opip0Ax2yRhlklEDVNQvni+aLm4JsdGNIXXNCYU4cuOsayaUNRlQlEvnFDUmFDUownFQWpbWGYPOMYy+AoFJqIRnJUyCZzJtKLGtGJ5' \
			b'znCGaUWNaUWNaUWNaUU9mlbUe6YVU+YEziQDc+GsZGkenAkVQeUpOBOioTZCJ8Wt4QwxjoIzBThTKiFWSFg1BCpCKX9o5FwBA3gmJskp5JPlCHJCvN83F3FsU79a1q6AfQrAJnZAl9lIl9mgy2zQZaaLlotrcmy54jWDjvPIEWCbquNsSsfZLOw4G3Sczajj' \
			b'PEhtDNjbGRrnz+XyCGBPR+vbukwAbCN9Z4O+c3lOjGrQdzboOxv0nQ36zmbUdzZ7+s4pcwDslIGZgF1laRZgJyqCyhOAnYiG2gidFLcCbIlxFGCbFc5WODsFnDliBBZmWYxEV4IzBzhzgDMHOEuxEU3hNYMFScYNHMOZq+CsLEbCuwvgzAHO3AjO6tS24GyY' \
			b'G6rNcQZzUMazrTj0kPCsFErwzAmeYUVTec545oBnDnjmgGdY5gQqV3jm9uCZZE7wTDIwF89KlubhmWQRZJ7CMyEaqiN0UtwazxDjKDwbm+CueLbi2VF45okLWJjF1I1XHgdc8FDLBQwjZm9GzN4kyCjxZcd4Vpm9mWL2ZhaavRmYvZmR2dsgtS088wccw5mU' \
			b'zCYKTEQjOCtlEjgT4zcD47fynOEMxm8Gxm8Gxm8Gxm9mZPxm9hi/pcwJnEkG5sJZydI8OBMqgspTcCZEQ22ETopbwxliHAVnYzvdFc5WODsKzgKxAAuz2MPR1SHUMX8wnAXAWYqNaAqvGdjGwZcdw1llG2eKbZxZaBtnYBtnRrZxg9S24CwccAxn8CU4m4xG' \
			b'cFbKJHAmFnIGFnLlOcMZLOQMLOQMLOQMLOTMyELO7LGQS5kTOJMMzIWzkqV5cCZUBJWn4EyIhtoInRS3hjPEOArOxsa8K5ytcHYUnHVU/yzMncBZBzjrAGfY+oIvrsmxEU3hNd4XR4kvO4azroKzrsDZwmXpBsvSzWhZ+iC1LTjrDjiGM/gSnE1GIzgrZRI4' \
			b'6wTOOsBZfs5whmXpBsvSDZalGyxLN6Nl6bjfAWeSOYEzycBcOCtZmgdnQkVQeQrOhGi4hFTcGs7k0TFwtsfid4WzFc5mwxlVO+YCrMwFWMwFWMwFWMwFWMwF5NhyxWsWcwF26AjObDUXYMtcgF04F2AxF2BHcwGD1MZwZrcyNM6fy+UROJuO1rd1mQBnVuYC' \
			b'LOYCynNiVIu5AIu5AIu5AIu5ADuaC7B75gJS5gBnKQMz4azK0iw4S1QElSfgLBENtRE6KW4FZxLjKDjrtrfZuOeIRrvC1KB2hr03Vlzbo6bZxkCqOw1fy5YArKnBLsXALsXALiW/gGisqSFITAgqx5paZZdiil2KWWiXYmCXYkZ2KcroKrktVc0ecB3s7OR1' \
			b'jQC140VW2ErRRGET8xQD85TynBU2mKcYmKcYmKcYmKeYkXmK2WOekvInCptkYK7CVrI0T2ETWoLYUwobIjhUSuikuLXChhhHIVy/ItyKcCfV3DxVOyOcga9lyyZW3jBTYDFTYDFTkF9ANFbeEGSU+LLbpG8m5a3MFNiFMwUWMwV2NFMwSG1LefMHHG0Z6XKR' \
			b'COAMVLipyKzClZKJCifzBRbzBeU5q3CYL7CYL7CYL7CYL7Cj+QK7Z74g5U9UOMnAXBWuZGmeCie0BK2nVDhEcKiT0ElxaxUOMY4BOL2aE+/GtYgXRj1ifAvTGEdbgR82L+btxtm4VuYPNOYPNOYPNOYPNOYPcmxEU3hNY/5Adi5Pjs2Lq/kDXeYP9ML5A435' \
			b'Az2aPxiktmVeHA44Ni+GL5kXT0Yj8+JSJjEvTivseTWqRQbqeGxmjHkEjXkEjXkEjXkEPZpH0HvmEVImxcxYMjLXzLhkaZ6ZsVAT1J4yMzYmExA1w6bGqdi1uTHCjoI7tcLdqsadQI2jukXnzMkaMIc1YA5rwFj85OKaHBvRFF5zWAnm9MARvLlqJZgrK8Hc' \
			b'wpVgDivB3Ggl2CC1rb21DzmCN/EJvE1Hi9VUlQnw5mQxmMNisPKcGNVhMZjDYjCHxWAOi8HcaDGY27MYLGUOsJYyMBPWqizNgrVERVB5AtYS0VAboZPiVnAmMY6Cs6tbWzA82GQFtbOBWnuuZWG+wW71uFC66JxqdE41OqdpiWuKjWgKr2l0TuHLjvW2qnOq' \
			b'S+dUL+ycanROeUt9OoiBtuEnqsPQ3UqC9FhPdFNH+dp2rMFJGW2ixUQ00uBK6USDkw6qRge1PGfNDR1UjQ6qRgdVo4OqRx1UvaeDmjInmptkYK7mVrI0T3Pz6Aqgk6qnO6mJcKB46KTItdaGGEfB3Lrm4PEB3Fm0NkN1yzqLEa3NQGsz0NoMtDYDrS3FRjSF' \
			b'18hrlPiyY63NVFqbKVqbWai1GWhtZqS11altaW3mgGOtDb6ktU1GI62tlEm0NiNam4HWlp+z1magtRlobQZam4HWZkZam9mjtUnmRGuTDMzV2kqW5mltkmFQeUprE6KhNkInxa21NsQ4Cs7WJQcrnJ0EzhzVKguzLKFyWELlsITKYQmVwxKqHBvRFF5zWELl' \
			b'3MAxnFVLqFxZQuUWLqFyWELlRkuoBqltwZk74DbFl+BsMhrBWSmTwJmsoHJYQVWeM5xhBZXDCiqHFVQOK6jcaAWV27OCKmVO4EwyMBfOSpbmwZlkEVSegjMhGmojdFLcGs4Q4yg4W5ccPCw4w9Dz6WHN7IC2MIK3UEOcp2pmAZfuqEN31KE7KtstOXRHc2xE' \
			b'U3jNoTsKX3YMcVV31JXuqFvYHXXojrrRXOkgtS2I8wfcxuXyJIibjEYQV8okECedUIdOaHnOEIdOqEMn1KET6tAJdaNOqNvTCU2ZE4iTDMyFuJKlNr98GOiElqD1FNDJh7rkC52UW7COwypSHod4J95i3N0B0J1v67i7gjd9AOIuoa1R/dMGQPaQFUhPNc2m' \
			b'D7J173i38RxD4YqoFpv2wpcdm33Um/YqZqRs+rFw4950CKcd79zL1Vr+t+0/+n2OLT/K1r3Tccjmg31KTvBU1cHC/Ix37005YE6VhQhKViIoWYqgZC2CGi9GsHt28JVsJNMPIe8I1JCnaWDbpIqbZ/xBkVoI244FCYl4qNLAF00ngZKR8UiLk7gZ0yJDPMUG' \
			b'ov4pNqwrGDZeinBLDLsFgF0YtGafCHwpneuuuo9UB5jD9HoahHIMhSuiesxbej1wBEK+mrf0Zd7SL5y39Ji39KN5yy288Xsd4Y0vs5TTcWIlVCWA9pTLO+vEYL9nKlK+K2iSUpmpIlUFOQQjEm/P2cDpSyBu6KROKuyQGAcOr2PoGO/9vULHo4MOS1O9LFZ2' \
			b'B3SkGApXRPUwzIcvO4aOyjDfF8N8v9Aw38Mw39tD0GH3OYYOW6BjMg5BRylBDR12LnTsMbKX7ybokFTmQkcpyEHoQLx90CFfAnFDJ3VSQwdizIGO8dbbK3Q8OujwjceIjvc7oCPFULgiqscoDnzZMXRUozi+jOL4haM4HqM43h+CDr/PMXSUMZvpOAQdpQQ1' \
			b'dPi50LFnYEa+m6BDUpkLHaUgB6ED8fZBh3wJxA2d1EkNHYgxAzrM2FL97qBjHXG5H/NjVE/Y9MF3O6AmxVC4IqrHRg/wZcdQU2304MtGD37hRg8eGz340UYPg9S2YKfb5xh2yhYP03EIdkppKtjhsRWPTR4SSVTAOyi0Bw09UvFS5BqQ9uzwIJ9MgCTpzwWk' \
			b'nON5QyqJfCDvFCgJwXAJqbg1KMmj/aBUj6aYsV35Ck4rOB0Ap57qiYV1xxBwjqFwRVSPIWD4smNwqoaAfRn+9QuHf/lr+MIAnOrUtsCp3+cYnMrI73QcAqdSmi1wwsBvIgmBUw9w6gFOPcCpBzj1I3DaM+Irn0zgJOnPBaf8xkxwEvJJkSfASQiGagidFLcG' \
			b'J6maBeA0thJfwWkFp/3gRDXE4ofLBDjlGApXRCWvUeLLjsAJkQFO5BdwwrvzwYm/hi/U4DRIbQxOo9yMM+e4MAmcpuP0g9KMwYkTzY+JI/kdFNqDhh6peClyBU64nwYn+aSAU0p/JjiVHM8Dp0Q+kHcCnBLBUA2hk+JW4CQxloDT2LZ7BacVnA6Ak6IaYmFV' \
			b'O8ApxZAropLXKPFlx+CkKnBSBZzUQnDCvDkDUw1OdWpb4LSVoUF0x4XJ4DQZp2/r0myBkwI4JVIEvINCe9DQIxUvRa7BSe0BJzxO4CTpzwWnnOOZ4CTkA3mnwEkIhmoInRS3BifEWAJObKkdAaeJ8NHETEeY6qutYIzAVeQRQSwzBVptwi0zBV1tQi9zfmOg' \
			b'bgaMuSZK9Tm2hTkGz2I8qiJHDYOp8C2Gx5ID54xgnduBdzEen9O+D/famUZES/Cvm4mB/tileiRRNMtOShcNWRESRZmA4raJ5euYFwGRVJcZJ/suY+WGmJe+JEtdtNiG07V3fKFldWS96QZug81bJAnsBNAxhG6o/nUxGdcLTcaTAZIe2YwPUh8D6Yb3M6Tc' \
			b'+nFOy0sOF42mcdNbItEGpZ2ITgv8SnHHyKphQC6PeX0frMc1rMc1rMc1hu/1yHp8Y6gjT6kTlqXnrKzRmpQAyKV5AGIW1Q6gV9I0DLJl2UzKaY3BbUhArPdbLaVyzDwEUwja7p0AiP860x58FjohV702EDEyMrunHEK/EaSpQff8G+iX8JoeK8TSFIHB2kWR' \
			b'GEP1LpD2hM0EzEBlwHCNwQzAs9B3ckKRsZYw1TCaJrisJwTnTAaO4W8X9FWwtwV3x8DcAWibA2kMZWEEYVmF8/tg6zBgJSHUjFEJoDIiTcBRwqKjgGj/hGBCnU1ajtIDUzb9uLM4a2pvDAy7UaFGhC0sOBIFDov+LJknaSdRH8p5knCSVj8hrXu0qnMLbNKP' \
			b'IikerNi2dkJ0l4jtAXUDOsT9kt1Ka6B6eiQyTFW/JcfLZTgsaHHtBWW46t2IMNuTyjOtcCN+iXFirq5Gvm/dLB+S78OynXoR1yjfnLn636WugDu1vDPUtnQN3BG8Nvkfy76mlJfJf/OvyF9PYy5Z9+6W6d7hEBL4k4GBAIDPANA+rEY9CT2ReGejnoYWYhh1' \
			b'j3kXR9pdrx0CgSwt0Y6GAahbRn1ZXy/JjLXXngQoWLYYLRYBhbkYWGRwCBkcqG4eqEKQAEHrfQqBxZ4Ymg8RsNgZQ/N2tFunpJThKnpMrEKDfRvFp0OZPIFNwYp1if743rvdMY56WgQBfLQ0CuomIGSufe9dwYib0T/wM/sH+qw6xLT+YGtogJpxV3rEqI/A' \
			b'9dKpCWigbN4DeKDKntNnMPP6DFoOgtvZb4jccT0jddNSHiUqloa4i8ZDeUveiykNU3MW51Acop9GvhX554wMJCXCT0h/UhbOoCRcY09ijABsM8ZTSxviiw3vRHhRTcFfUlmgfNA3uEFvZ6CCKA5ZaRjrCkHUg5FSEEn++ipA4kTD+dfcfehvM25QJDz091bA' \
			b'Tz2Mfw+0fdPeZhi/+Vd4GhGdBgCisF2rpEaq364Nv0apndtmz5Ta+9wu79TKW7bzuF1bfL0yLGWb0/oeGsePXH+U8LrLyG84gR4+14Zonxy7M83KuSuVZ9qt7uqEmq7mJGp2LdrmePlWW6ffnXSejlXs2Xr2QUm3x0m6v4ykV1LOtgB30VqfScpXCZ8n4SPp' \
			b'prq4w8b7rMJ9UsF2xwl2uLxg61WwV8HmelgFe4Zg++MEu7u8YJtVsFfB5jpYBXuGYIerHTF7MKNk1yS5Vya0J5JQWuF0HeNht5TI5l+K1gNGwOHh7O5qhTMSPU9PX0JQdy6jO+eU9Cq4u6eaY0Rq4i7ZyN7J9PLtW9j+7oR45zrcPa2tH62fvdZWd8ba11lr' \
			b'XvvKKPVBCTOWOw//F7XK/MJgrenVz1fNWzY6a+0Yl57NTKeMRarJZ/00wiY11/Grq6Svkn4Xku63/hdKun/Uku5F0u1cSVfN625rnyCItWaBxjZAYSjELMGQxeH+OElapqREsURscTVzsI8c27XCnaPdZyqGJGYEIwawH3PeBNdljstH2tWbrqQqnKw5SpXq' \
			b'aExk0JPt6CIVjqYa0ExwrAdoMSDVZPQzSbkDJDJJMZ50YpoqPtFFV7TV8j3+5o7dbfYTexdX10Q3tyC6mab7PaR9V7Bwi/4JzM5XB/b4OtjVsFdV4he24curbVYbvLPt7auu8vmqmIs9/B+2gVW94+HCtu449pjZTu3gIs5o6WGqYSvk5rLVbQZ/KkY7Zpxn' \
			b'KbOdceHx/vGao5lygQbHmuC8gZcapY4cYlnOsOfdkePAyKejDdDA2H5l7Ktl7KGiuHxE8REytn0a0YAZO6yMfcWMbVbGPpaxu3mMfeupqAvz9pm3Qsn8vevE1tvwOrPbGaeGJvidkzwnvyOB2/I8f+UAz2seZGq2Djfdeawpi0G/isE1wDwz+qVZvz836/cn' \
			b'Yf3j4X6C4WNZDzP8iawQLsjzF9oJ66R8z7V+CZOAC+s5XK5LbRp5aDLfHxz4P6nhzZlY/o43gDsV2zN7XtYc5oy8zwne+a6pBwVg/xzOGYzPVhnYJQM8HX1HdmHnbASuY//gg5Kwf2Lt/kjCFWwJehppcA9RGjjSPZGI4TTnJS2Ub79woL/ChQK3khLi4Cux' \
			b'T9otMLdcB0BCQwlfn9n/YtnJc7l3YeC/ik8WH6ryKzTxO6sIXenSmcUy5FcZug4ZCqsM3VcZCs1r2mtbBVQo2W91/KBrXvMhojGcTc10z8G0YXJLkSOPUECgXVWNoQATY8Trkw0fS06rqnB4VqC9kmmXZD84I0Hxhr78fT7/xPIhcL7a7LjdPvSAzgYznhLe' \
			b'6IWpxOuuP/6eHAk6+UXs1zo6wq582pDRvRn8lU1YB+Gckp1ISY0P6TuQMG8olVfJEfrlA92+p2UJ5Y9MtK0sli//duKPnzEsaPbzQnSiAefa3TLXhE0HM+6buX+0FmEUxtn0S7M5eTbhzpzS2Xo5t/HlvX+0dmLXM1qjEK+c57CdZzl2dirbFu2SHtqK7j8u' \
			b'Vh04VRHmEHyiIu8pnpYTUVtFpybGMD4t0U9SpT6lMJ8+yG1KOmHQ4WRBbM9OVuxN+Yu41Y3+YtC2G0faEW3rrQMf24o5+jLXUHdBroqJ3uaP89tfE0exRlRzlT8jZ/FOP3fq+sFNd/tPco1GPL4cC5JGfUaHAqlcIGIgfy5OjQre9TKra+A6XrSXb0/svD7b' \
			b'p3c61LE+CdNSl2Ye31K/59aOemU7H6NcZsS7tJH12bAWHEywcpVMTA8rF/NJp9G2Z3TUVz5rAlsOtT6huO+p6cMN6Cyepv740PVhHDLT0TjD7scoo1s5u3B21zx0h0qf6DSdn7FpbO4SDkUMK19nvqYh0QfuUOkT3bZb8XW7Z/BlyNumOaGjseDdj1HUfuXv' \
			b'wt9989AdhkAn+oS35m+qzVk8TvMpJ3U03bH7MUo87jQ+Zjan2awH7lDpE73Ik7C5mgvnNGl4akeTeLsfo+BrN7Pidts8dIdKX9bLpEm6xSO1O5g+V0ZhfNfMdzSZuyB2zOd2KE1HpxuQY+2QVjIQmofuUOnLOqRHyUBdofPloWvO52pTjr0xQaO1R1sEg8x4' \
			b'HrhDpXePotIVbZnW2x2VbwoD2FCd+U1mKWTM9SCcpkUGkbxbwf2UD8yxbNb3cqhJhnV37GDis6y/TBJzWxol4ZhHqylkC818R0Zsi14YvCyWg/tjwRaw2AEyXdU9pGvXXKUDQZf1eK+DoH1zlQ4EnbDuuxBBk03VJFHbGYSlVvuCjtrh7VBqhXe8AQIv67Vm' \
			b'ZeT8NJ7UJXfSWjWLHFnMLn1n8XcnEwHVJ4wy7yPVTXMfHEi+rGt6tSR3zX1wIPnjs4+lLd6XO15vUv0f95V9X5z/9ckYqM5ls7IPoTpp4dADcajCq7IvvkwVmuahOCxCWd4XvvdVaJuH4lCFy7vd974KXfNQHKowdvSNIsvlFv0oa3IAVPxIvte03YXvOZDO' \
			b'KZMHUfevK1nBoryl6onxeQ0X2eFKQn46dteM/hE7bMWmSuM3+mb8r8Wi3w7WDHqqfoTH1qLmuX1sEquf1x+Y4cLZvJB1YhGrAT3oOJ7R7vkK58DwB60kJdxIK3GJ6wzIQyd88IAzDS7zoDKvcaQFxfEt7Wg9MSqITrVICx5BLDpyQRtLIVJgOgAgfoVCnGTO' \
			b'lZAY5/ub/w+qJSmq'

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
		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)(?!{_LETTERU})|{"|".join (AST.Cmp.UNI2PY)}'),
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

		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)|{"|".join (AST.Cmp.UNI2PY)}'),
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

	def expr               (self, expr_ass):                                       return expr_ass

	def expr_ass_1         (self, expr_mapsto1, EQ, expr_mapsto2):                 return AST ('=', expr_mapsto1, expr_mapsto2)
	def expr_ass_2         (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr_colon):                 return _expr_mapsto (expr_paren.strip (), expr_colon)
	def expr_mapsto_2      (self, expr_piece):                                     return expr_piece

	def expr_piece_1       (self, expr_or, IF, expr_ass, ELSE, expr_mapsto):       return _expr_piece (expr_or, expr_ass, expr_mapsto)
	def expr_piece_2       (self, expr_or, IF, expr_ass):                          return AST ('piece', ((expr_or, expr_ass),))
	def expr_piece_3       (self, expr_or):                                        return expr_or

	def expr_or_1          (self, expr_or, OR, expr_and):                          return AST.flatcat ('or', expr_or, expr_and)
	def expr_or_2          (self, expr_and):                                       return expr_and

	def expr_and_1         (self, expr_and, AND, expr_not):                        return AST.flatcat ('and', expr_and, expr_not)
	def expr_and_2         (self, expr_not):                                       return expr_not

	def expr_not_1         (self, NOT, expr_not):                                  return AST ('not', expr_not)
	def expr_not_2         (self, expr_cmp):                                       return expr_cmp

	def expr_cmp_1         (self, expr_union1, CMP, expr_union2):                  return AST ('==', AST.Cmp.ANY2PY.get (CMP.text.replace (' ', ''), CMP.text.replace (' ', '')), expr_union1, expr_union2)
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

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: # DEBUG!
# 	p = Parser ()
# 	# p.set_user_funcs ({'f': 1})
# 	# a = p.parse (r'x - {1 * 2}')
# 	# a = p.parse (r'x - {{1 * 2} * 3}')

# 	a = p.parse ('-{\\int x dx} + y * dz')
# 	print (a)

# 	# a = sym.ast2spt (a)
# 	# print (a)
