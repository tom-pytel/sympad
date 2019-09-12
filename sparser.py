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
	ast = ast._strip (1)

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
			return AST ('lamb', rhs.stop, (lhs.mul [1].var, rhs.start.var))

	elif lhs.is_ass:
		if lhs.rhs.is_mul and lhs.rhs.mul.len == 2 and lhs.rhs.mul [0].is_var_lambda and lhs.rhs.mul [1].is_var:
			return AST ('=', lhs.lhs, ('lamb', rhs.stop, (lhs.rhs.mul [1].var, rhs.start.var)))

	elif lhs.is_comma:
		for i in range (lhs.comma.len - 1, -1, -1):
			if lhs.comma [i].is_mul:
				if lhs.comma [i].mul.len == 2 and lhs.comma [i].mul [0].is_var_lambda and lhs.comma [i].mul [1].is_var:
					ast = AST ('lamb', rhs.stop, (lhs.comma [i].mul [1].var, *(c.var for c in lhs.comma [i + 1:]), rhs.start.var))

					return AST (',', lhs.comma [:i] + (ast,)) if i else ast

			elif lhs.comma [i].is_ass:
				if lhs.comma [i].rhs.is_mul and lhs.comma [i].rhs.mul.len == 2 and lhs.comma [i].rhs.mul [0].is_var_lambda and lhs.comma [i].rhs.mul [1].is_var:
					ast = AST ('=', lhs.comma [i].lhs, ('lamb', rhs.stop, (lhs.comma [i].rhs.mul [1].var, *(c.var for c in lhs.comma [i + 1:]), rhs.start.var)))

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
			return wrap_ass (AST ('lamb', rhs, (l.mul [1].var,)))

	return _ast_pre_slice (lhs, rhs)

def _expr_mapsto (args, lamb):
	if args.is_var:
		return AST ('lamb', lamb, (args.var,))

	elif args.is_comma:
		for var in args.comma:
			if not var.is_var:
				break
		else:
			return AST ('lamb', lamb, tuple (c.var for c in args.comma))

	raise SyntaxError ('invalid lambda function')

def _expr_piece (expr, expr_if, expr_else):
	if expr_else.is_piece:
		return AST ('piece', ((expr, expr_if),) + expr_else.piece)
	else:
		return AST ('piece', ((expr, expr_if), (expr_else, True)))

def _expr_cmp (lhs, CMP, rhs):
	cmp = AST.Cmp.ANY2PY.get (CMP.text.replace (' ', ''), CMP.text.replace (' ', ''))

	if lhs.is_cmp:
		return AST ('<>', lhs.lhs, lhs.cmp + ((cmp, rhs),))
	else:
		return AST ('<>', lhs, ((cmp, rhs),))

def _expr_mul (expr): # ONLY FOR CONSISTENCY! pull negative(s) out of first term of nested curly/multiplication
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

		elif ast.is_num_neg:
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
			last, neg = last._strip_minus (retneg = True)
			wrapl     = lambda ast, last = last, wrapl = wrapl, neg = neg: wrapl (neg (ast))

		else:
			break

	if last.is_attr: # {x.y} *imp* () -> x.y(), x.{y.z} -> {x.y}.z
		if last.is_attr_var:
			if arg.is_paren:
				ast = wrap (AST ('.', last.obj, last.attr, _ast_func_tuple_args (arg)))
			elif rhs.is_attr:
				ast = AST ('.', _expr_mul_imp (last, rhs.obj), rhs.attr)

	elif last.is_pow: # {x^y.z} *imp* () -> x^{y.z()}
		if last.exp.is_attr_var:
			if arg.is_paren:
				ast = AST ('^', last.base, wrap (AST ('.', last.exp.obj, last.exp.attr, _ast_func_tuple_args (arg))))
			elif rhs.is_attr:
				ast = AST ('^', last.base, ('.', _expr_mul_imp (last.exp, rhs.obj), rhs.attr))

	elif last.is_var: # user_func *imp* () -> user_func (), var (tuple) -> func ()
		if last.var in user_funcs or arg.strip_paren.is_comma:
			if arg.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg)))
			else:
				ast = wrap (AST ('func', last.var, (arg,)))

	if arg.is_brack: # x * [y] -> x [y]
		if not arg.brack:
			raise SyntaxError ('missing index')

		if last.is_num_neg: # really silly, trying to index negative number, will fail but rewrite to neg of idx of pos number for consistency of parsing
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

		elif ast.numer.is_pow and ast.numer.base.is_diff_or_part_solo and ast.numer.exp.no_curlys.is_num_pos_int:
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
			elif n.is_pow and ast_dv_check (n.base) and n.exp.no_curlys.is_num_pos_int:
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
					return AST ('diff', _expr_mul (ns [-1]), tuple (ds))
				else:
					return AST ('diff', _expr_mul (AST ('*', ns [i + 1:])), tuple (ds))

		return None # raise SyntaxError?

	# start here
	if ast.is_div: # this part handles d/dx
		diff = _interpret_divide (ast)

		if diff and diff [1]:
			return diff

	elif ast.is_mul: # this part needed to handle \frac{d}{dx}
		tail = []
		end  = ast.mul.len

		for i in range (end - 1, -1, -1):
			if ast.mul [i].is_div:
				diff = _interpret_divide (ast.mul [i])

				if diff:
					if diff.expr:
						if i < end - 1:
							tail [0 : 0] = ast.mul [i + 1 : end]

						tail.insert (0, diff)

					elif i < end - 1:
						tail.insert (0, AST ('diff', _expr_mul (ast.mul [i + 1] if i == end - 2 else AST ('*', ast.mul [i + 1 : end])), diff.dvs))

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
			ast2, neg = ast.intg._strip_minus (retneg = True)
			ast2, dv  = _ast_strip_tail_differential (ast2)

			if dv:
				if ast2:
					return (AST ('intg', neg (ast2), dv, *ast [3:]), ast.dv)
				elif neg.has_neg:
					return (AST ('intg', neg (AST.One), dv, *ast [3:]), ast.dv)
				else:
					return (AST ('intg', None, dv, *ast [3:]), ast.dv)

	elif ast.is_diff:
		ast2, neg = ast.diff._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			if ast2:
				return (AST ('diff', neg (ast2), ast.dvs), dv)
			elif ast.dvs.len == 1:
				return (neg (AST ('/', ('@', ast.diff_type or 'd'), ast.dvs [0])), dv)
			else:
				return (neg (AST ('/', ('@', ast.diff_type or 'd'), ('*', ast.dvs))), dv)

	elif ast.is_div:
		ast2, neg = ast.denom._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('/', ast.numer, neg (ast2)), dv

		ast2, neg = ast.numer._strip_minus (retneg = True)

		if dv:
			return AST ('/', neg (ast2) if ast2 else neg (AST.One), ast.denom), dv

	elif ast.is_mul or ast.is_mulexp:
		ast2, neg = ast.mul [-1]._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			if ast2:
				return (AST (ast.op, ast.mul [:-1] + (neg (ast2),)), dv)
			elif ast.mul.len > 2:
				return (neg (AST (ast.op, ast.mul [:-1])), dv)
			else:
				return (neg (ast.mul [0]), dv)

	elif ast.is_add:
		ast2, neg = ast.add [-1]._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('+', ast.add [:-1] + (neg (ast2),)), dv

	return ast, None

def _expr_intg (ast, from_to = ()): # find differential for integration if present in ast and return integral ast
	ast, neg = ast._strip_minus (retneg = True)
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

	return wrap (AST (*(args [:iparm] + ((_ast_func_tuple_args (ast) if args [0] == 'func' else ast._strip (strip)),) + args [iparm + 1:])))

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
		return AST ('mat', tuple ((c [0],) for c in mat_rows))

def _expr_vec (ast):
	e = ast.comma if ast.is_comma else (ast,)

	if all (c.is_brack for c in e):
		if len (e) == 0:
			return AST.MatEmpty

		elif len (e) == 1 or len (set (c.brack.len for c in e)) == 1:
			if e [0].brack.len == 1:
				return AST ('mat', tuple ((c.brack [0],) for c in e))
			elif e [0].brack.len:
				return AST ('mat', tuple (c.brack for c in e))
			else:
				return AST.MatEmpty

		elif e [-1].brack.len < e [0].brack.len:
			raise lalr1.Incomplete (AST ('mat', tuple (c.brack for c in e [:-1]) + (e [-1].brack + (AST.VarNull,) * (e [0].brack.len - e [-1].brack.len),)))

	return AST ('mat', tuple ((c,) for c in e))

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

def _expr_ufunc (UFUNC, args):
	args, kw = AST.args2kwargs (args.comma if args.is_comma else (args,))

	if any (not a.is_var for a in args):
		raise SyntaxError ('undefined functions only take variables')

	return AST ('ufunc', UFUNC.grp [0] or '', tuple (a.var for a in args), tuple (kw.items ()))

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
			b'eJztnfuv3DaW5/+ZBdoXUAHiW/RvjuP0BOM4mTwaMzCCwHG7B8EmcRAnvbNo7P++POd7KFEsVUlVt16+V7B8paIokTzk+YiPQ/LJ67/8r3e//v0vzV+ef/nyy1fp/PLFZ9+m01fPvn7x6mW6+OzrZ8/lpOSs0/mTz199+UU+q3yh5QWffknveMV/P3nx1x+e' \
			b'P/vmxTdy/cWz7PrJcPm34fIrXH7z8tk3//ZJCu3fKRb9BTs//+7rl/9Fv/qL7z777hVF85tvv6a/332S/r744qtv/+ubFxyT7yiuf3tGN7/4/NV3FJfPX337V4ru51/wE/z3P74m3y9ZDl/SXXntJ/zk8y+/+OJZlg05fP35X//t2xyNr3M06eLTT15yTCka' \
			b'/5H+PPviK7p89akkn64+GS7/NlxK8l+8/OaFuGTh0Tu/RURSBMjTF8+++ubbL+n133K6X/zn85f5NuXJp5//7fNP6TXPkSHy+FcvWQBJNFkW//nNi+fs4dPPP/uMxPnqcy4Mzznaz159SvKiG1/S8xxkkrEa5YcIPoXx/N/T5Yc/f/zwzze/f/hncf0hXb99' \
			b'8/u7P354//sPf//x5w9/vPm9uJ0u0+kNe3v3P78lLz/985d8/eHP3979nn/8+u6/f/jHn7++HW7+mC5/efPHD2/f/yxXv7//P8MVQv7w7sOHt/3Vb/1Vfs2bH4fLP/7oQ/vHm7d/5Ovf+K1wHkWgj+jPP/WXP/36x3/n61/+/PmHn375rUjacPmPfxQJy5f/' \
			b'fDMkd3g7vYYu8u8/3v1e38s//ywj+Obvf8+Xb//8/ef/m3/8z4d3Q+J+/P3N2//9rv/5oYzZP9/17/rz15/e/9oH+qb3/3ZIHsu1j/774ZV/FiL+tY/Sjz/9+r5PxvtB8Ck+veB/evf2Xf8jFaIiBr99+ON9/9Y+O/u4vP95iO7b97/88mb048Nfvm9eP9k4' \
			b'17j2rsGFogtr6I9trLqTn+kXXzn607DD3cgBv2x+Lt132Yku2dcGZ9080Y1xzUY1pksXd9lV3HqHTaALbfHHxWaj/V3ppMOWk29LJ7pMV0rjj6cAEPH0iy4p1em/byg4PObogiKg8MdJ2ihNmh9NN1LAytD/u+zSlb+inMmJYqIoyaqTJNv2LrvCbXDYaH5A' \
			b'pUhRDJOgbbwTl41ieSiPPz4lT3V34kSX6YozrknvQVTkZ74u3BVOGxaB5v/G59uaLui94o5AUuTEEZ4MJypKokLbu4pbHLy1Y4eN5pJgKBwOyBj8cSkKTt+J08Ygg6jAhP6G0/mGbfHHSVlMoVhOV2yekHBI/kh7cnDFD48TOVBIXSp6qslZkQJCUsR949S2' \
			b'U/FTb/vQ458k5rjlVD9kxj/t9s/RAxvDhSzpzBPdSQCURZBFdh5+bgynOmXyEx2blAmUKaZtPD2c8ib9kHIy7YPpEBd6TNk19rgxXHap6IaGc/AOvzdcbFUQBSGlskkbbaEndLN3H1wsXNzg4uDiBxcPl5BdNoqFppO75oCTjPiPC31se6eudKJLSorFn41Q' \
			b'Si7pSqGU5jSTrrG+uFaKL1LjSFZIdHoXl1FJFBVZziMSKr9TtfjjKeYo/arlS5YjYTRTFElMbnDJPzec3k5eQ9rV2C6TrnQWh/SbYx/xJxWpO/md1Ivj1uKPT3moESXKfc1RSoXwCak3FD398gAhMaHteZ9LjLMZCYxSSJFS0PY+TGOkXGexhiy95PjEDcrK' \
			b'P1UOOl05fh9/IWK+Mq1cIbp0YfIFQEhqo5otuYp7KdvklJ7j2Hf44wlsUmQ7vqQIp8TgG5RkwyWwL9b0PeNCpTX++EF/teZLkmKHP8U3txNs24A//GnClyD9oku68vnmnfxMv/INCCmVv6AgaJ+zwpECs1AcvcD1L2A08wtcyDfYqzjlpwwSTd/T9GCqYLxu' \
			b'yWf6bTk3E2CT0qRSkKiQcjPJONJHJMUihCYkArRt+p9w3CYgtOlD1aYPWJvY4+jrkAJKehnTAfCkOkAqT75JkiV6pG+mSoUpuiamt6eQUnalzDRNiE3XNp1qOt10punSO1OmK03ESeER/lsKOxK6kmtSQZWeVOlRqs8krSGMEJ6SmibQJLIoTS9Jlyn4Lp1S' \
			b'IlRKhUrlRKXsUyl6XboTmi7FlsKKTUw1A00KmFQjld0uuaRkp0M1QTchRdM2wTUhvZyCUUzcVKNJBSPpWypf6Zuf6jBJYRMREm19CrJNntsklfTxTMJI2UliS8+mAL9vnrT0oX/9JGUAlbSUCXRKuaBSzjyxctdYODucOr6bnD1+BzqteXaxPIvIFcVnqjsh' \
			b'OwLnA1ULOfNI7Oyt5Vx8EsQ7fFlkqcoPc+7crYp4tUxlKSK/jGRNziKoXcxq5/j3SKYiTchxQoIiuV5iI0kV0pkSDSSSYuikQDl/pfADwo8oyFSQWB6a5XWZOGiPOGh7wTCR/yrrMyv4qqnX0lTKgTUDropKLai0fs2Iq2aEMoJkRpQIhkXSC0ASntNbpjGl' \
			b'a0jDZSM/Kghl5l/8s5aEJ9VonavVXF9LRaNJkmlSmtYyfMYybJS0caTWpftqRbfC5aqf2Y71QFFzkxqk1BilFic1N6lBmvJhFf85xa9W8V9T/HoV/zXFb1bxX++j3Flp6+Ij/IRTiX4q1I7Wz/LV6vy5wsS1esobqbjSUB9u5KqUnKQby0kOWrdm4DUz0Eo3' \
			b'sfRkRc7OR9z8UloKqEYJfaJyJ1+HjrcO7bMuyG3pd+c38lnJGeW9A7Ji7o2H75i7LHDXxtyZi5d07OsxCPxJlEGlIMMSqGZyRNXaPbAlriAFJ6B0BRTWIGU1oGyqDFmmLBUrlDoPGXuRMQWV3puwGFMI9qHI6PUTj3FLbx56OpHNHmDyfqQ6DzjZYKlndiJt' \
			b'ZWofTjrly9L6qhxjhBZScCZ/OlAY+PND1a/8hUnRwBi+XkflL9lkTLLWsJJYBX/RHlxPAmd7iHReJXyGop2Eupbpy44xJ3HqtZl8zTLPOCF7qTUfrpkP1q4ZcGUUrRlwXctAJRWcJEotloHpvEr8bEU+iYoEzOJZrVqOass6bgZdIeAJO2cyHs2NBP6cr3l6' \
			b'lGg18+dCVq9oTVNgOPPJcjaSvZkQUTpM2l0m7t+LQTy1z/lNa3YvzQHTQsjoeJZ+Z4g0W4KjWy4PzaKqvAp2tmjz14Xsm1CIjQxymzyg2kvUyCCSyUVZpuB00IYOutGZrA34bK2C3yF4ZXqRgwWrhLZGQ7ksrcKAMOwqjEEYbhVGBol1qIYAwwp1lddsQrA2' \
			b'la9qtsf1w0dbMF+TlcrjFoDlblua368fUbrJgEiLVY3eGjoOwqlpgzyVW1EYQb5yFU2p3t5Fw95Fw95Fw/hKUOukd36dpHHVvkkvXZOei90DMztRsJF8cKkKt6Dm0oUQzYMT8ZNokTavH5xSkIkdFN4+wLRJH7F3DzBtQdLWPby0UTQ1LOM0DOLEAI4WHKLK' \
			b'wB0vOUenVAcw0mFs7jBYYNAVt872uVolQiNTrORUKyeFLCL5Ghn1NHcyOmeGBUBopEl+0kmL7yRlnPFuj5cZcZVZvtTHDXfUMrnpsE64Pm8bHX0naKivcj6j3YbOsOvEQrjLsDN53EHLeAN3hq+kO3+ewEh4lfEZ546C+B1I35n8FZGPRp6tqEyvBvJNmOod' \
			b'IVcDVwNX/po4eVSz89r9cDXTKI0M6TxOUpGIyB7HXUmPrSswpVs/sjmF3O1p1vHciaaRkhHvAI4FcCyw2vQdQuyo7FCA0CpiO4XveRYhqtJeTHECRr9QafbAp8ebPRTSd307y0o7y2aTB9T4LWr8FjV+m2v6dp3BcZ6VujSLGoDMny/j5cvXm5fIZ05LxqRk' \
			b'0dmpfnDB7h5HCAZB4NlAj0qPPT+EeedcuOxdrow+tI6ItnFS3F2uaaO4OxR3h+KOk8E5Rc2J0J2oqoMcHeTo1grjmddzZFHX8y3tOvPjqsxyUKLA2zFg3VNPn6l0m9aptr3WpcR4URwPxfFQHPLe9FnsH/G4OJdmA2kGgQ6fZeFvhZW/WYbhEcvpNZWegNIT' \
			b'+PMFi+J+lYUsvI6LJOZaK0uqlQKgpW1oTdK+aCZJdSiRHd7Ziczx/bX5QypfUpsbnVjYlCMTH3duuEctAC4rNpcVLWVE35VFjD4xKFx8Vtw5QbJrm9ct71RhuU+bFhONnDrDXwH+6qRwU5CULk/RpMTwNwcfO3z4JOKBMgCNaQitlEwtb8eSjkPG4AMJMaW8' \
			b'pK9chIxp2Rz+ZCn5bAVhvBGFot/pPrXmqWVL6x/Q0ge0DDotRU7LgtPCH7Q2Bi2MQati0IIRtFoErTFDC8zQIiq0gAqVEFomn77VtL4hLbJHK71RftF3kJb6oXV+aA0faj7TWjU0Qk0jurTGbcoXTZOwaAJW+q5rGnhqyY0kmb6/1NoiYVIpoWLCu9/QbiUk' \
			b'4+ROvX+0PgBxg+Y1JolqmpmS0qDJosXTN7xNmYcttWiDJ94NpuF9TWg/EN7dpdkE3omFttBI0djQTjS0w0bkHbAa3nqEdyvS5EPRhiu0ww7tkpKuO9pHRvN2VLS5TEsP0V5HvA0RbUBCm0XRazreEoluIVjyrekF6dnIO86ke5EiSeEnL0lcm0CxozfQbjue' \
			b'Hm4Db+XCW5bQliDYa4j3FOEtuKJDmpKWb5LQN0FJzD3vz0SBJV+0eQptRMNb3bSe937hDbF4HyFKEj3KNzlV9OKO9xrifX0o3rSXDm1zwttKcYroRvKUyuSmo9DTjY48tiwd8kJ+SYC8+Q7tH5T+dySbIFsqUTzJI0uNQooUUXKlSJMMOCMcdqkJLUIkwvCO' \
			b'M7T9GW9909L2Tizr5BJ47yneoorEmW4FcnXfk4KTWo9UWu3W6kwrUGhQb5s1XI2V3J9Sz3sWoi9mQu1dpfp+ofpfSvXVidRfTSCgXYABR5J0tea7Bbrv2FcqBW6bAG5ggJuigDs7Bzh2Kbdd/2+KBm7MA7eYCJekwQl50E0wwS2hQvMv+5S+Eu4pfSdCTCf3' \
			b'/7jamlCRdC8jom/+BWm2ot5TUSLlprQ9x21dIgZwYQdQoEa2FBe2IMZU9W2gh6rpkQob6n2EEe41Io3sG9tBmu9dVZ8yQz0rN5pHxDGFpUdh/dE3Midq9rSEHxOpragUhUa+IhDRJ72DamiZQDRTkYxORiRyCwjkmUKKNoOhboQ5GlGX7SIidRWRvFBJV2Si' \
			b'cuILQlGdGWRCidVUWSco8SnwKQmfT67pfYt3+mi1cONujNFBkGJfBCjKtLbnEj+k7RF8YkUjybYVoxCP4f8Ws6rYjY8W6fX9JSK39dZRCFHlh3sn4V1kzvFtYl6+HQV/eNpKPI2cvZwDziUSkTcKABzBrxe2kC+LvuQf0DeiHvsZsDdKg+JYzzEQ5WDAoMR5' \
			b'G4MSo0xBZFzMQRU07CPQU9Hrp/Q9Spr+FGUuhqdE6KQGT1OCCZGmR2Tf+ONalFShPiIyAou5IC/hoj2CjSsXF3JRNbx1J2cVX1GNLVfWpKLWe9I4K5OdjJKr/mAaqoKGaqCh4ow8AoYKLFQVCstgtzC4FbORd8fRIfwxOnb4Z/TFOoFl20/l4PvbKMPgngL2' \
			b'FKinAD1VMU/tYR5uZ+ZJ+HPMU2PmFTFbBDxVAU/t4J0IMvNOAXeqph28bbFuG3G2qgWekG9XgNta4bsy2Eg40Gy7g2rZh3iRgScLqtnRwVSzBdXsQLWjqncWRLMV0cogt4hm9x1MNDtU6Cb9RFWlCihD8nH2hRewzIJlaMnyCSERy2zFMruHZXhHZplEYI5l' \
			b'dsyyImaLWGYrltkdLBMRZpahEYtwSpbJrQPqbW6F2gq100GNEgv99jugln2IF4IanCgT/OhgqPkCan6A2jF9avQQidFXUCuD3IKa33cw1PwAtUk/UVWpEqh5gZoH1Pr7XGw9oOYBNQ+ooZMOoi2g5vdATeInUJMIzEHNj6FWxGwR1HwFNb8DaiLCDDUPqPka' \
			b'avB2CNT8CrUVaqeDGiUI+h12QC37EC8ENThRJoTRwVALBdTCALVwDNQCoBYqqJVBbkEt7DsYamGA2qSfqKpUCdSCQC0Aav19LrYBUAuAWgDUAqBWDT6oPOYwBTV4z1CTCMxBLYyhVsRsEdRCBbWwA2oiwgy1AKiFGmrwdgjUwu5BiI8Mbe1KtxuiG5tesqJH' \
			b'0I3OtEd9HDMu+xOPxDg4UVbE0cGMiwXj4sC4eAzjIhgXK8aVQW4xLs4cjLk4YG7ST1RVwgRzUTAXgbn+PpffCMxFYC4CcxGYixXm4h7M4ZUZcxKBOczFMeaKmC3CXKwwF3dgTkSYMReBuXpgVbwdgrluxdyKudNjjkboMY6gZRBBY3xVqxHmen/ikdZxhJNR' \
			b'ctUfhDldDCXoYSgB7zgQcxrDCLoaRhgFWWNOb8WqjqRDbARz035inTBgTsvwqcYAwnCfyq/GGILGGILGGILGGIKuxhD0njEEuS2YyxGYwZwejyGUMVuCOV2NIegdYwhZhII5jTEEXY8hiLdDMBdXzK2YOwPmqJBB0bVgDs1VPhWYy/7kTJjDpVFy1R+MOV1g' \
			b'Tg+Y08dgTgNzusJcGeQW5uYOxpweMDfpJ6oqYYI5GScVW9nhPmNOA3MamNPAnAbmdIU5vQdzeGXGnERgDnN6jLkiZoswpyvM6R2YExFmzGlgTteYg7dDMKfay5jOrXZzjxV45BkqL8OodCbgWQYenahYWWAv+xbvymQnipAdHYy9YkhVD0OqR1nMaQyp6mpI' \
			b'dRTkFvbszMHYw9UghglvcZy8nnwysKoxsDrcZ/JhYFVjYFVjYFVjYFVXA6t6z8Bqjp+QTyIwR77xwGoZs0XkqwZW9Y6B1SzFTD4MrOp6YDXfOoR8CuSDdKnshYy1MdMIaH4OO4IRQgWpea/OosZcf/dZjUgtYnPBg6dTXMhIeiX9IyU9FRO04I204A1a8AYt' \
			b'eMa0x8k1vW/xTjMM4YRTeRDpTdGON0M73hzTjjdox5uqHT8Ksib9dqzqSDqfr4T0095inTaQ3khT3qApP9yngmzQlDdoyhs05Q2a8qZqyps9TfkcP5A+R2CG9GbclC9jtoT0pmrKmx1N+SxFIb1BU97UTXnxdhDpzUq+lXznJJ+jAsIqL1PWDCas8Snwicjn' \
			b'QL7sW7wT+eBExc2NDiZfnrtGBXKYsmaOMYSmh4h8riJfGeQW+cb3KYvrWDqfrzL63MTB6BslTtDnBH2Y+DbcZ/Q5oM8BfQ7oc0Cfq9Dn9qBP4ifokwjMoW886a2M2SL0uQp9bgf6RIoZfQ7oczX64O0g9NU20Sv6VvSdFH2eSgervBgU8oz3DqfAJw0/GgVJ' \
			b'jAuNGBeKExU3PzoYfYVxoRmMC80xxoUGxoWmMi4cBbmFPj9zMPkkeTaLYcJbHCevJ5+YGBqYGA73mXwwMTQwMTQwMTQwMTSViaHZY2KY4yfkkwjMkW9sYljGbBH5KhNDs8PEMEsxkw8mhqY2MRRvB5GvNpxeybeS76TkC1Q0WOXF6pDORL4A8mEwh0+u6X2L' \
			b'dyIfnKi4hdHB5CssEM1ggWiOsUA0sEA0lQXiKMgt8oWZg8knqbRZDBPe4jh5PfnEDtHADnG4z+SDHaKBHaKBHaKBHaKp7BDNHjvEHD8hn0RgjnxjO8QyZovIV9khmh12iFmKmXywQzS1HaJ4O4h8tXX1Sr6VfCclX0flglVeVmeis4Or40LD5OtAvuxbvBP5' \
			b'4ETFrRsdTL68YBMVyG4gX3cM+TqQr6vIVwa5Rb5u5mDy4SqTb9JbHCevJ18n5OtAvv4+kw9LvvA9gxOS7oMIuyBft4d8Ej8hn0RgjnzdmHxFzBaRr1rvxexY7iVLMZOvA/m6mnzwdhD59phgr+RbyXdv8lFxwBCHlSEOiyEOiyEOiyEOiyGO3rd4T+omTkbJ' \
			b'VX8Q+WwxxGGHIQ57zBCHxRCHrYY4RkHW5LNbsaoj6Xy+EvJNe4t12kA+K0McFkMcw30qyBZDHBZDHBZDHBZDHLYa4rB7hjhy/EC+HIEZ8tnxEEcZsyXks9UQh90xxJGlKOSzGOKw9RCHeDuIfN328i4PAH6q4t/SBV9WBp6x9mcbA+Xv5KrlwsMVQNj0GNj0' \
			b'GNj09A/AG1cA4SS2FsWxye/MFcDBpsccY9NjYNNjKpse3hCgD3OrBmhnjg52PfK4hoPa8SDXA0dJlHqgmPYYmPYM97keCNMeA9MeA9MeA9MeU5n2mD2mPTmKUg+UCMzVA8emPWXMFtUDK9Mes8O0R17a1wNh2mNq0x7xdhAN40rDlYaXqRF6Kg9MQ4crqhRi' \
			b'CMRiCMRiCMRiCKR/AN64Uggno+SqP7hSWAyB2GEIxB4zBGIxBGKrIZBRkFuVQj9zdBj/lcc1F1uuGk555qrhKIVSNZSBEIuBkOE+Vw0xEGIxEGIxEGIxEGKrgRC7ZyAkR1GqhhKBuarheCCkjNmiqmE1EGJ3DITIS/uqIQZCbD0QIt4OgaFeLbznEZhkYtyK' \
			b'Qkah34PDdonFd6AixKbOMjCiMTCiMTCiMTCiMTDS+xbvZPENJ6Pkqj/Y4rsYGNHDwIg+ZmBEY2BEVwMjoyC3LL7DzMEW35JKm8Uw4S2Ok9dbfMvAiE6Q0C1++8IrLL8xQKIxQKIxQKIxQKKrARK9Z4Akx1MsvyUiM0TU4wGSMmaLLL+rARK9Y4BE274k9Nbf' \
			b'GCTRUpbGFuDwehAZ1UrGtXJ4xsohLYvLEMKpxZmyvmUS0ikJn0+u6X2L96R24pQihKv+IBKyJyEhXQsJ8Y4DSSiL2dOpJOEoyK217duZg0goV0LCaW9xnLxMQggBZ194YQLyc5CBNzgh6T6IsAcC4vc0AXP8QMAcgRkCsp+BgGXMlhAQOTQQEPHbJmCWotCP' \
			b'MydKOAX5xNtB5FvngqzkOyv5eC9AVnmxiHawiHawiHawiHawiO59i3ciH5yIfG50MPkKi2g3WES7YyyiHSyiXWURPQpyi3xu5mDy4SqTb9JbHCevJ58YRDsYRA/3mXwwiHYwiHYwiHYwiHaVQbTbYxCd4yfkkwjMkW9sEF3GbBH5KoNot8MgOksxkw8G0a42' \
			b'iBZvB5HvFueCFNu1rfy7FP9oIY/zznymH2gASr+gRr+gRr+gRr9gXvAh+xbvymQnipAfHdwOLvoF9dAvqI/pF9ToF+Rdf2gbKe5v99wlggYxv5du64kewipy2we3iCWhNgtkwltUVSqlRSx9gxp9g8N9bgmjb1Cjb1Cjb1Cjb1BXfYN6T99gjp+0hCUCcy3h' \
			b'cd9gGbNFLWHPvS3j1vCO/sEsydwSRv+grvsHxdtBRFyniDx6Fp63Lugpt7kSJBx04KADBx046MDB3rd4p7ognKgu6EcH1wULDrqBg+4YDjpw0FXjI6Mgt+qCfubYDFe5LjjpLY6T19cFhX4O9Bvuc10Q9HOgnwP9HOjnKvq5PfTL8ZO6oERgri44pl8Zs0V1' \
			b'wYp8bgf5shRzXRDkczX5xNtB5FuniKzkOyv5OspnVnkxlHYwlJblqR0MpR0MpXvf4p3IByciXzc6mHyFobQbDKXdMYbSDobSrjKUHgW5Rb5u5mDy4SqTb9JbHCevJ58YSjsYSg/3mXwwlHYwlHYwlHYwlHaVobTbYyid4yfkkwjMkW9sKF3GbBH5KkNpt8NQ' \
			b'Oksxkw+G0q42lBZvB5FvnSLysMknY4dnIaDZQ8GuImFX0jA2KMo4tTijODANI2gYQcPsW7wTDeFENIyjg2kYCxrGgYbxGBpG0DBWNCyD3KJhnDmYhrjKNJz0FsfJ62kYhYYRNOzvMw0jaBhBwwgaRtAwVjSMe2go8RMaSgTmaBjHNCxi1r9jnomxYmLcwUSR' \
			b'ZS4dSHTIAQoW2c0UUTkIjvUsElLQ5vhFX92VmHjeRV+vRUJ/o/XA5MdR4XBzBoORSgEbyAkF681Keh/ihSwE4UQWgnF0sIVgQT7KUzvQzx5Dv7yzua3wh/we/m+bCsZ9BxsJDvCb9hOLFFI+Ev0kyrIGrAX/+khghzmsAYtYGTl7OQfxWFoJ7mGgxCRbCYqY' \
			b'KwYiTpWl4JiDHH2X83CRrWDBQFZOu2M52CzQbCwIAnIPJGVs8ltVEeWBnoKpuDzFwrruKdadHehXr+9/T/rdE33XwJ2gjhFnBG1BkHa9it31m7OUMVBeb6fR1fsQL8pkpxQJXPUHocsXUz38MNXDHzPVw2Oqh6+memxRqopGHSuH4HWf0Ak/UVUpQRWtT7eX' \
			b'OW3EJOIRsYg4NGKQ3zNtQ94rDMqhzNTD/HjaxhC9WfD4asYGBzwFniwjAY/HlA1fT9kQbzu27GXK1Mvrr5RZKSOU8TQgzsrnd1Am+xAvRBk4EWX86GDKFEMEfhgi8McMEXgMEXg/Rxm/72DKDAMC036iqlJSUsYvpcyeXn95b6aMhDJHmXGv/xC9ecr4pZQR' \
			b'GWXKoMff1z3+4m0PZUw99WGlzEoZoUxHBjesfN0OymQf4oUoAyeiTDc6mDJFd7wfuuP9Md3xHt3xvpujTLfvYMoMne/TfqKqUlJSpltKmT097PLeTBkJZY4y4x72IXrzlOmWUkZklCmD3nVf966Lt32UqacRXJcya2fRxztgSJmHCQOhnaZS70O8JL0RpxQJ' \
			b'XPUHUSkUkwTCMEkgHDNJIKBfKFSTBEZB1oSqolTH0CEqQqhpP1FVqSoIxV1CARMEsmiUxBSJ9wYnBJR0JFSzA8Ke2QHySmFXDn+GXWE8O2CI+LJeoFDNDgg7ZgdkCQq/AmYHhHp2gHjbwa+y58fUkwJWjq0cO5JjqoGG4jTFsexDvBDH4GSUXPUHc0wVHFMD' \
			b'x9QxHFPgmKo4Vga5xbGtWI28O0Qlc2zST6xTtcUxBY6JaJTEFIn3BicERBxTFcfUHo7hduaYhD/HMTXmWBGzRRxTFcfUDo6JBDPHFDimao7B2xKO1Sb+K8dWjh3JMU05xyqtd3As+5AzcQyXRslVfzDHdMExPXBMH8MxDY7pimNlkFsc23swx/TAsUk/UVWp' \
			b'2uKYBseySCSmSLw3OCEg4lg1NoffOziGV2aOSfhzHNNjjukhZos4piuO7RiUyxLMHNPgWD0UJ96WcKw2zF85tnLsSI4ZyjZWabODY9mHeFEmOxHHzOhgjpmCY2bgmDmGYwYcMxXHyiC3OGb2HcwxM3Bs0k9UVaq2OGbAMRGNkpgi8V7ihYCIY6bimNnDMTyc' \
			b'OSbhz3HMjDlmhpgt4pipOGZ2cEwkmDlmwDFTcwzelnCMzewTm5oEmybJKxEtFiuzGSEbzeYC3MwU39qMODNFuTaDzlzE5qqdJ14q5TGecZW2Y9hHZr7JXxKAShIYWJjcvRMmBnAxyWBgo6746GcYac9orOUO4KW7z/RN0joCFPWtUa8/qVXSFPTPbVLaO3pc' \
			b'cKpaNzA1xp6rGyrV9CaBq5b57XSOeJ4oatilPDZYUxJPK2yaFxm3GwXf/ZTPY6a9ZyMvXc17H0Whhu6G1y6mKPs6usNDDjHSlsvPJrJukMimvdOkz1GyawprTIKX20rkGS1uQBIeYdKcz2oG/MaQ3RyJkt6b77M0yZCjA54JmVSgVCgwrTExVMIt10mSmJa8' \
			b'brse2nqL3Ho8a56llIvCoomixkokFoxrpP+mzwuBuHaycFIFcfHWQ9w9ZRf6m3hO1YKO/0b6S2iHtqUTg90nLamxvgvonjhOEAfBgeyS1wzrpaSeHFNlLhN/HcibyVqSdMlYaEXJXYTcomNBxcU0LEkY5um3lHo97bqKcn2NsNtHtnmmZf00jLHMsB5aE8TK' \
			b'uDqeVfvHQjOYNnmmZXRIT6z72hYNadbg2E2NmhgjVhxAiRIRxId5LhwAhB4FxIExBLL6k0aHCY3eU0u7gFL39a0wpdruxtVbH67i9MmbVPO6YhMWqPlMDQbVko9Q14uKCGXgpM7buk13o3qvtTlC97WpxgkH/d+qDFi7VP+7A77o9rL6X7S0BAT+pJ95R42e' \
			b'pLM0uSBF6LxcqBtBSz79+oSf/zkuzDMhN2hulgscw/K/MIJatieuGzCzqVGX1IoaqBeoK9jjmBF2MENTeTiiztD8S9NUkq7l9kA8rD0Q5ujhTwkQgUY3QEM/8PZB2F15GPWI0O8AWHDrVFXQaHlekfa0bhPlHIE/lJN70391EqiwClpzKFQuDJYMEh6dB0go' \
			b'sx5LQ0ObuKeyAdT2/Q4UOuUN9z5Q4mw9IDb0vPFtusPL3vO2SLZHDf3gOkoqYEf3OtgdfcUnp4wgpqWO3jCBmaVm2ddEjV7QVjHL2iqMGn32Osl0fcSW+LB53Op69ZKqrcIZ1bkJfFjz0SCEcn5J/aMaS9+DESoatpurfxAP1G31Qu4gQdKsVHQVD3ul3+rS' \
			b'lQ93mQoISZtWkGGRL+zJGFVGwgQhcqXjDJWNm229bFGCZnfycNtGYXPwKWScGxf+kpUOkgy9h/zUm4otrID0lY+6ztFJNaOuXOjm9a2A5FTDGR9DU6W7b3/GQIFOfdwQOPUwxsfUsrAnGMZo/hWepi8BdUgktbhlbW79PesCt6rZh3z7D9Dsj/77vvPb7tiG' \
			b'5n7f9NvWc0nf8q/4ovGK9MRRCu4up+PxBHX+hSZb+3SdzbTOVefXN67ztHbjbSo+R+ckVfpS/W17NAPIvvCsINAs/UPr9Mto4I6jgb8YDUoSUNSu8dU/JwlWChxTsx8TgDLnipWAswPgXMrvj1P+cB3lt6vyr8o/pfxXbel/tMofjlP+7jrK71blX5V/SvnN' \
			b'qvxHKH930718D6pn7xa1+xYV+0RaTDPdbqcP73Ra2/wrFemnxCjupo83rcApSf3w/cWUeWKm5dmH7FflXthrR2HTaPxlP9bmOsPvJ/xSJ7FfVdF3zene99Vuq2nYt/v1XjR9evG06VgZCD88hedp9NX/g77u/MBorvJHMVa3bM7xDsWfGpRnOQwmvzOD8+m7' \
			b'7yN99tO7VxqsNLgVGvD+buP/h9GAHlhpADkMNHBLaaCb193WMldQfc1Kj1WsAit6qeWs4tDX8cpOeVWnKUVyrDSsAHWh7+u3IRXoTkvhrdZLKsorlUwup7IcEgomtubeLpB9YczFaLRGkKwPNJ2xdMPmKtm2/Ifal+bKlrmXQAFDEWsrzCOe7Vw8a0bMu/gy' \
			b'Ejd6xc4hb8Xqpgu5a3kpe92xUNOCjNitDHWG2PtliNuRJx97vugBsVt5kxl5kfxx98ufHfWJMrvaw6oOR2Tp8s/+rs99rFr5Z85+lsH4//izW5QJ3Dzw83pk0Tngs7irhHF0q4axHn/0/NIid89+raIQHtOFdWhBvMQyN/NdUUcX2kMrlVxDXdanVBLuyN6j' \
			b'wwv0pRaaWdLx69XTVAfnwh/Wwn+7hX8nue/RofroC7/TTxNUuPB3a+G/5cIf1sJ/xsIflxX+U4zoXbr8X2iRv5EO7Np7+j76wKX/3CNsEzohIZxPJxDAyfSCX7dILzS/tNnanHnntsykKumZVVVu8HPBxf8a6qHP/MlAAKdTD3rdvT4bU0qhFijF6YxCLqkX' \
			b'F14r9uS6wSXyYhYaF65T8dsuv37rItsKPzt+cmpbqXOpxY0so3xK1UApuLwF0xn1g5N0Q4scL1OS/WNi57EpPIeeXNvm90y6woX3miZ/Z1IYDuMWbHWP05o9A5fnNMZdFWeR4vDdW7CXPdvXRn/MyjMeVb6wPfv9p6KwFt3q1JN7axNl/i1Zoe1WqnvOLKH8' \
			b'p8Te8kSS4/SrH0K/0pSRVcWmVYzK/K0ae55VzW5+wtZxehZWPbtNPYurnj0kPeua15TR2iOTqXx0fCM2rz3tK5zcYUFoyDnQcujK0oaF4kDrIVvDOxi239+l85ONoh04aZMKy1u+BVoJndZA96NtVXg7JVqanPbks1TIFG+75Hkvy65YzpwUqtouJdJy4bQQ' \
			b'GC3zHSgiG31kqOkN+/7xu2WP98m3yxLMeiYYQ/M8zOjfsLxyqO6waDd2IlRVb0e6JBK0jFs/x5OWZcCmMLJb5fc0MWb4RyXfytIRw387+Y/vEnRof1FemC3FhidtWE6Bu2cKiHuLE+Gbpf9oVsyEO0fZHxzlqa1ZZ2NNO2n2MQ/N/n80o2fffZo1k84c/7Ad' \
			b'fx13JiFBhz6CdmxPvH+TbTOzvawbby3Luw/kbWTJqpa2j6WtY5Mbbxk7LaFyq1ZswRqbYXtVz5s9yGYONHGiGf4RrbvqH6ZWT/+v/e73PTy1+9e+ELafmgiRc7K7QklM2Xvffxz3eHOlUFclsT1jaeSlN699xDj80LyawD0PzthUs7h8qaRGwNkPJE/1yaNF' \
			b'0/zZim974yXYNTgiT07tf574oLbRmV6970BW65OUZLaSOagwU1vu3ge1LGc8IZWmKtC09sb5qMzFmlqnN1uyqROhOFJco2sqx9Me1PI/awBTBzJ/ogWxJ8Pnv7gHFXSe7To6aLbYluOSgzpQ5jwhxW4t7uPi3jWP4EDeTzTdLlfaqTfycgcSHNbCPirs1B38' \
			b'8A/k/UTr8F6FnTL1sAJvmhMe1CU+5wkJj2uhHxf62DyCA128E43Pexd6ytSDCj6NNZ30oGGgOU9If906fexln8b8Hv6BvJ9orp6k7KsFAwXj8m+akx804jnnCWJY27OVCtjmERzI+8Oas5TTB/chz2hCnyeDNrhm+UFD4Af4TjHddY+G8/MPCGdt+VaKEZpH' \
			b'cCDvD2v5HqUYdb4epiRdc76jtJBZ4B8SW5vOY20hW6mHfyDvD2s6X15byGjtJg6Ia21wV6pimkdwwO6pfVx539LQiZooA2YoB67LZYE29qbyYJuHdGiyrk2CHbt1U1coI+pgW49TEDUXgeVknVLl0Cw/yBj1oAfq58Vyd9YjTHAH81uW8mHN/5uSMhlb3+4B' \
			b'8U5YeH404lXNDR8Q72Et91OLN5sh7v0EzIpZNxc+6LN02A0v5soTdreLPtWXlXhYInXTHHSQCfuhz5wqAMj+sLb4TcveNR/JAckfa/p8g5IPzUdyQPKHtagfitF5qp4dcWDS2PD/uLfMvHR5AJM+kKu3Z8R9iVylWYAP58BEosPGzR9MTrrmAR3IycMb2w8i' \
			b'J33zgA7k5OEN+geRk6F5QAdy0jSvjSLL/lbmbdreQfjryIGkx46OdsHEjdRYKPM6yZh90GxKWgCQZliSbzTrbJj0zZt9j/7Dd7flm/KNn0hxqf5rMRm3o3m/1JWK4kqbKZZFb19JSSWAnw6jyfHDRPWJSeoW/QS0SVu1s4ni+ep4YSdB5QIpvSM5ippmXnVU' \
			b'IMk3mfVrmYZqyO5foR+X+2+p31aTxqV36JReHSQCtp/ObFELon1atHU8wRnZS9topLeQi7S3aW+B7JL8fH/3/wErww/b' 

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

	_LTR      = fr'[a-zA-Z]'
	_LTRU     = fr'[a-zA-Z_]'

	_VARTEX   = '(?:' + '|'.join (reversed (sorted (x.replace ('\\', '\\\\').replace ('+', '\\+').replace ('*', '\\*').replace ('^', '\\^') for x in AST.Var.TEX2PY))) + ')'
	_VARTEX1  = fr'(?:(\d)|({_LTR})|(\\partial|\\infty))'
	_VARPY    = fr'(?:{_LTR}(?:\w|\\_)*)'
	_VARUNI   = fr'(?:{"|".join (AST.Var.UNI2PY)})'
	_VAR      = fr'(?:{_VARPY}|{_VARTEX}(?!{_LTRU})|{_VARUNI})'

	_STR      = r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY)))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LTRU})|(\${_LTRU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\$?(?:{_LTR}|\\_)(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
		('UFUNC',        fr'\?({_LTR}\w*)?'),
		('LEFTDOT',      fr'\\left\s*\.'),

		('SQRT',          r'sqrt\b|\\sqrt(?!{_LTR})'),
		('LOG',           r'log\b|\\log(?!{_LTR})'),
		('LN',            r'ln\b|\\ln(?!{_LTR})'),
		('LIM',          fr'\\lim(?!{_LTR})'),
		('SUM',          fr'\\sum(?:\s*\\limits)?(?!{_LTR})|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?(?!{_LTR})|{_UINTG}'),
		('LEFT',         fr'\\left(?!{_LTRU})'),
		('RIGHT',        fr'\\right(?!{_LTRU})'),
		('CDOT',         fr'\\cdot(?!{_LTRU})'),
		('TO',           fr'\\to(?!{_LTRU})'),
		('UNION',        fr'\\cup(?!{_LTRU})|\|\|'),
		('SDIFF',        fr'\\ominus(?!{_LTRU})|\^\^'),
		('XSECT',        fr'\\cap(?!{_LTRU})|&&'),
		('MAPSTO',       fr'\\mapsto(?!{_LTRU})'),
		('EMPTYSET',     fr'\\emptyset(?!{_LTRU})'),
		('SETMINUS',     fr'\\setminus(?!{_LTRU})'),
		('SUBSTACK',      r'\\substack(?!{_LTRU})'),

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
		('FRAC',          r'\\frac(?!{_LTRU})'),
		('BINOM2',       fr'\\binom\s*{_VARTEX1}\s*{_VARTEX1}'),
		('BINOM1',       fr'\\binom\s*{_VARTEX1}'),
		('BINOM',         r'\\binom(?!{_LTRU})'),
		('IF',            r'if(?!{_LTRU})'),
		('ELSE',          r'else(?!{_LTRU})'),
		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)(?!{_LTRU})|{"|".join (AST.Cmp.UNI2PY)}'),
		('OR',           fr'or\b|\\vee(?!{_LTR})|{_UOR}'),
		('AND',          fr'and\b|\\wedge(?!{_LTR})|{_UAND}'),
		('NOT',          fr'not\b|\\neg(?!{_LTR})|{_UNOT}'),
		('EQ',            r'='),
		('NUM',           r'(?:(\d*\.\d+)|(\d+\.?))((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))('*)"),
		('ATTR',         fr'\.\s*(?:({_LTRU}\w*)|\\operatorname\s*{{\s*({_LTR}(?:\w|\\_)*)\s*}})'),
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
	_VARPY_QUICK   = fr'(?:{_PYGREEK_QUICK}|{_LTR})'
	_VAR_QUICK     = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK   = OrderedDict ([ # quick input mode different tokens
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})|(\${_LTRU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LTR}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

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

	def expr_commas_1      (self, expr_comma, COMMA):                                  return expr_comma if expr_comma.is_comma else AST (',', (expr_comma,))
	def expr_commas_2      (self, expr_comma):                                         return expr_comma
	def expr_commas_3      (self):                                                     return AST.CommaEmpty
	def expr_comma_1       (self, expr_comma, COMMA, expr_colon):                      return _expr_comma (expr_comma, expr_colon)
	def expr_comma_2       (self, expr_colon):                                         return expr_colon

	def expr_colon_1       (self, expr, COLON, expr_colon):                            return _expr_colon (expr, expr_colon)
	def expr_colon_2       (self, expr, COLON):                                        return AST ('slice', expr, False, None)
	def expr_colon_3       (self, COLON, expr_colon):                                  return _ast_pre_slice (False, expr_colon)
	def expr_colon_4       (self, COLON):                                              return AST ('slice', False, False, None)
	def expr_colon_5       (self, expr):                                               return expr

	def expr               (self, expr_ass):                                           return expr_ass

	def expr_ass_1         (self, expr_mapsto1, EQ, expr_mapsto2):                     return AST ('=', expr_mapsto1, expr_mapsto2)
	# def expr_ass_2         (self, SQRT, EQ, expr_mapsto2):                             return AST ('=', ('@', 'sqrt'), expr_mapsto2)
	# def expr_ass_3         (self, LN, EQ, expr_mapsto2):                               return AST ('=', ('@', 'ln'), expr_mapsto2)
	# def expr_ass_4         (self, LOG, EQ, expr_mapsto2):                              return AST ('=', ('@', 'log'), expr_mapsto2)
	# def expr_ass_5         (self, FUNC, EQ, expr_mapsto2):                             return AST ('=', ('@', _FUNC_name (FUNC)), expr_mapsto2)
	def expr_ass_6         (self, expr_mapsto):                                        return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr_colon):                     return _expr_mapsto (expr_paren.strip, expr_colon)
	def expr_mapsto_2      (self, expr_piece):                                         return expr_piece

	def expr_piece_1       (self, expr_or, IF, expr_ass, ELSE, expr_mapsto):           return _expr_piece (expr_or, expr_ass, expr_mapsto)
	def expr_piece_2       (self, expr_or, IF, expr_ass):                              return AST ('piece', ((expr_or, expr_ass),))
	def expr_piece_3       (self, expr_or):                                            return expr_or

	def expr_or_1          (self, expr_or, OR, expr_and):                              return AST.flatcat ('or', expr_or, expr_and)
	def expr_or_2          (self, expr_and):                                           return expr_and

	def expr_and_1         (self, expr_and, AND, expr_not):                            return AST.flatcat ('and', expr_and, expr_not)
	def expr_and_2         (self, expr_not):                                           return expr_not

	def expr_not_1         (self, NOT, expr_not):                                      return AST ('not', expr_not)
	def expr_not_2         (self, expr_cmp):                                           return expr_cmp

	def expr_cmp_1         (self, expr_cmp, CMP, expr_union):                          return _expr_cmp (expr_cmp, CMP, expr_union)
	def expr_cmp_2         (self, expr_union):                                         return expr_union

	def expr_union_1       (self, expr_union, UNION, expr_sdiff):                      return AST.flatcat ('||', expr_union, expr_sdiff)
	def expr_union_2       (self, expr_sdiff):                                         return expr_sdiff

	def expr_sdiff_1       (self, expr_sdiff, SDIFF, expr_xsect):                      return AST.flatcat ('^^', expr_sdiff, expr_xsect)
	def expr_sdiff_2       (self, expr_xsect):                                         return expr_xsect

	def expr_xsect_1       (self, expr_xsect, XSECT, expr_add):                        return AST.flatcat ('&&', expr_xsect, expr_add)
	def expr_xsect_2       (self, expr_add):                                           return expr_add

	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                       return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                      return AST.flatcat ('+', expr_add, _expr_neg (expr_mul_exp))
	def expr_add_3         (self, expr_add, SETMINUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, _expr_neg (expr_mul_exp))
	def expr_add_4         (self, expr_mul_exp):                                       return expr_mul_exp

	def expr_mul_exp       (self, expr_mul_expr):                                      return _expr_mul (expr_mul_expr)
	def expr_mul_expr_1    (self, expr_mul_expr, CDOT, expr_neg):                      return AST.flatcat ('mulexp', expr_mul_expr, expr_neg)
	def expr_mul_expr_2    (self, expr_mul_expr, STAR, expr_neg):                      return AST.flatcat ('mulexp', expr_mul_expr, expr_neg)
	def expr_mul_expr_3    (self, expr_neg):                                           return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                    return _expr_neg (expr_neg)
	def expr_neg_2         (self, expr_diff):                                          return expr_diff

	def expr_diff          (self, expr_div):                                           return _expr_diff (expr_div)

	def expr_div_1         (self, expr_div, DIVIDE, expr_divm):                        return AST ('/', _expr_mul (expr_div), _expr_mul (expr_divm))
	def expr_div_2         (self, expr_mul_imp):                                       return expr_mul_imp
	def expr_divm_1        (self, MINUS, expr_divm):                                   return _expr_neg (expr_divm)
	def expr_divm_2        (self, expr_mul_imp):                                       return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                            return _expr_mul_imp (expr_mul_imp, expr_intg, self._USER_FUNCS)
	def expr_mul_imp_2     (self, expr_intg):                                          return expr_intg

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add):               return _expr_intg (_expr_mul (expr_add), (expr_sub, expr_super))
	def expr_intg_2        (self, INTG, expr_add):                                     return _expr_intg (_expr_mul (expr_add))
	def expr_intg_3        (self, expr_lim):                                           return expr_lim

	def expr_lim_1         (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                              return AST ('lim', _expr_mul (expr_neg), expr_var, expr)
	def expr_lim_2         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):      return AST ('lim', _expr_mul (expr_neg), expr_var, expr, '+')
	def expr_lim_3         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg):     return AST ('lim', _expr_mul (expr_neg), expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                            return expr_sum

	def expr_sum_1         (self, SUM, SUB, CURLYL, varass, CURLYR, expr_super, expr_neg):                              return AST ('sum', _expr_mul (expr_neg), varass [0], varass [1], expr_super)
	def expr_sum_2         (self, expr_func):                                                                           return expr_func

	def expr_func_1        (self, SQRT, BRACKL, expr_commas, BRACKR, expr_neg_func):   return _expr_func (1, 'sqrt', expr_neg_func, expr_commas)
	def expr_func_2        (self, SQRT, expr_super, expr_neg_func):                    return AST ('^', _expr_func (1, 'sqrt', expr_neg_func), expr_super)
	def expr_func_3        (self, SQRT, expr_neg_func):                                return _expr_func (1, 'sqrt', expr_neg_func)
	def expr_func_4        (self, LN, expr_super, expr_neg_func):                      return AST ('^', _expr_func (1, 'log', expr_neg_func), expr_super)
	def expr_func_5        (self, LN, expr_neg_func):                                  return _expr_func (1, 'log', expr_neg_func)
	def expr_func_6        (self, LOG, expr_sub, expr_neg_func):                       return _expr_func (1, 'log', expr_neg_func, expr_sub)
	def expr_func_7        (self, LOG, expr_super, expr_neg_func):                     return AST ('^', _expr_func (1, 'log', expr_neg_func), expr_super)
	def expr_func_8        (self, LOG, expr_neg_func):                                 return _expr_func (1, 'log', expr_neg_func)
	def expr_func_9        (self, FUNC, expr_neg_func):                                return _expr_func_func (FUNC, expr_neg_func)
	def expr_func_10       (self, FUNC, expr_super, expr_neg_func):                    return _expr_func_func (FUNC, expr_neg_func, expr_super)
	def expr_func_11       (self, expr_pow):                                           return expr_pow

	def expr_pow_1         (self, expr_pow, expr_super):                               return AST ('^', expr_pow, expr_super)
	def expr_pow_2         (self, expr_fact):                                          return expr_fact

	def expr_fact_1        (self, expr_fact, EXCL):                                    return AST ('!', expr_fact)
	def expr_fact_2        (self, expr_attr):                                          return expr_attr

	def expr_attr_1        (self, expr_attr, ATTR):                                    return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1].replace ('\\', ''))
	def expr_attr_2        (self, expr_abs):                                           return expr_abs

	def expr_abs_1         (self, LEFT, BAR1, expr_commas, RIGHT, BAR2):               return AST ('|', expr_commas)
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                            return AST ('|', expr_commas)
	def expr_abs_3         (self, expr_paren):                                         return expr_paren

	def expr_paren_1       (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):           return AST ('(', expr_commas)
	def expr_paren_2       (self, PARENL, expr_commas, PARENR):                        return AST ('(', expr_commas)
	def expr_paren_3       (self, expr_frac):                                          return expr_frac

	def expr_frac_1        (self, FRAC, expr_binom1, expr_binom2):                     return AST ('/', expr_binom1.no_curlys, expr_binom2.no_curlys)
	def expr_frac_2        (self, FRAC1, expr_binom):                                  return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_binom.no_curlys)
	def expr_frac_3        (self, FRAC2):                                              return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4        (self, expr_binom):                                         return expr_binom

	def expr_binom_1       (self, BINOM, expr_subs1, expr_subs2):                      return AST ('func', 'binomial', (expr_subs1.no_curlys, expr_subs2.no_curlys))
	def expr_binom_2       (self, BINOM1, expr_subs):                                  return AST ('func', 'binomial', (_ast_from_tok_digit_or_var (BINOM1), expr_subs.no_curlys))
	def expr_binom_3       (self, BINOM2):                                             return AST ('func', 'binomial', (_ast_from_tok_digit_or_var (BINOM2), _ast_from_tok_digit_or_var (BINOM2, 3)))
	def expr_binom_4       (self, expr_subs):                                          return expr_subs

	def expr_subs_1        (self, LEFTDOT, expr_commas, RIGHT, BAR, SUB, CURLYL, subsvars, CURLYR): return _expr_subs (expr_commas, subsvars)
	def expr_subs_2        (self, expr_cases):                                         return expr_cases
	def subsvars_1         (self, SUBSTACK, CURLYL, subsvarss, CURLYR):                return subsvarss
	def subsvars_2         (self, varass):                                             return (varass,)
	def subsvarss_1        (self, subsvarsv, DBLSLASH):                                return subsvarsv
	def subsvarss_2        (self, subsvarsv):                                          return subsvarsv
	def subsvarsv_1        (self, subsvarsv, DBLSLASH, varass):                        return subsvarsv + (varass,)
	def subsvarsv_2        (self, varass):                                             return (varass,)

	def expr_cases_1       (self, BEG_CASES, casess, END_CASES):                       return AST ('piece', casess)
	def expr_cases_2       (self, expr_mat):                                           return expr_mat
	def casess_1           (self, casessp, DBLSLASH):                                  return casessp
	def casess_2           (self, casessp):                                            return casessp
	def casessp_1          (self, casessp, DBLSLASH, casessc):                         return casessp + (casessc,)
	def casessp_2          (self, casessc):                                            return (casessc,)
	def casessc_1          (self, expr1, AMP, expr2):                                  return (expr1, expr2)
	def casessc_2          (self, expr, AMP):                                          return (expr, True)

	def expr_mat_1         (self, LEFT, BRACKL, BEG_MAT, mat_rows, END_MAT, RIGHT, BRACKR): return _expr_mat (mat_rows)
	def expr_mat_2         (self, BEG_MAT, mat_rows, END_MAT):                         return _expr_mat (mat_rows)
	def expr_mat_3         (self, BEG_BMAT, mat_rows, END_BMAT):                       return _expr_mat (mat_rows)
	def expr_mat_4         (self, BEG_VMAT, mat_rows, END_VMAT):                       return _expr_mat (mat_rows)
	def expr_mat_5         (self, BEG_PMAT, mat_rows, END_PMAT):                       return _expr_mat (mat_rows)
	def expr_mat_6         (self, expr_vec):                                           return expr_vec
	def mat_rows_1         (self, mat_row, DBLSLASH):                                  return mat_row
	def mat_rows_2         (self, mat_row):                                            return mat_row
	def mat_rows_3         (self):                                                     return ()
	def mat_row_1          (self, mat_row, DBLSLASH, mat_col):                         return mat_row + (mat_col,)
	def mat_row_2          (self, mat_col):                                            return (mat_col,)
	def mat_col_1          (self, mat_col, AMP, expr):                                 return mat_col + (expr,)
	def mat_col_2          (self, expr):                                               return (expr,)

	def expr_vec_1         (self, SLASHBRACKL, expr_commas, BRACKR):                   return _expr_vec (expr_commas)
	def expr_vec_2         (self, expr_bracket):                                       return expr_bracket

	def expr_bracket_1     (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):           return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_2     (self, BRACKL, expr_commas, BRACKR):                        return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_3     (self, expr_curly):                                         return expr_curly

	def expr_curly_1       (self, LEFT, SLASHCURLYL, expr_commas, RIGHT, SLASHCURLYR): return _expr_curly (expr_commas, forceset = True)
	def expr_curly_2       (self, SLASHCURLYL, expr_commas, CURLYR):                   return AST ('set', expr_commas.comma) if expr_commas.is_comma else AST ('set', (expr_commas,))
	def expr_curly_3       (self, CURLYL, expr_commas, CURLYR):                        return _expr_curly (expr_commas)
	def expr_curly_4       (self, expr_ufunc):                                         return expr_ufunc

	def expr_ufunc_1       (self, UFUNC, LEFT, PARENL, expr_commas, RIGHT, PARENR):    return _expr_ufunc (UFUNC, expr_commas)
	def expr_ufunc_2       (self, UFUNC, PARENL, expr_commas, PARENR):                 return _expr_ufunc (UFUNC, expr_commas)
	def expr_ufunc_3       (self, expr_term):                                          return expr_term

	def expr_term_1        (self, expr_num):                                           return expr_num
	def expr_term_2        (self, expr_var):                                           return expr_var
	def expr_term_3        (self, STR):                                                return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_4        (self, SUB):                                                return AST ('@', '_') # for last expression variable
	def expr_term_5        (self, EMPTYSET):                                           return AST.SetEmpty

	def expr_num           (self, NUM):                                                return _expr_num (NUM)
	def expr_var           (self, VAR):                                                return _expr_var (VAR)

	def expr_sub_1         (self, SUB, expr_frac):                                     return expr_frac
	def expr_sub_2         (self, SUB1):                                               return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1       (self, DBLSTAR, expr_neg_func):                             return expr_neg_func
	def expr_super_3       (self, CARET, expr_frac):                                   return expr_frac
	def expr_super_4       (self, CARET1):                                             return _ast_from_tok_digit_or_var (CARET1)

	def expr_neg_func_1    (self, MINUS, expr_neg_func):                               return _expr_neg (expr_neg_func)
	def expr_neg_func_2    (self, expr_func):                                          return expr_func

	def varass             (self, expr_var, EQ, expr_commas):                          return (expr_var, expr_commas)

	def caret_or_dblstar_1 (self, DBLSTAR):                                            return '**'
	def caret_or_dblstar_2 (self, CARET):                                              return '^'

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
			if rule [0] == 'expr_func':
				if rule [1] == ('FUNC', 'expr_neg_func'):
					return self._insert_symbol (('PARENL', 'PARENR'))
				elif rule [1] [0] == 'SQRT':
					return self._insert_symbol ('')

			elif rule == ('expr_paren', ('PARENL', 'expr_commas', 'PARENR')) and self.stack [-2].sym == 'expr_mul_imp' and \
					(self.stack [-2].red.is_attr or (self.stack [-2].red.is_var and self.stack [-2].red.var in self._USER_FUNCS)):
				return self._insert_symbol ('PARENR')

		if pos and rule [1] [pos - 1] == 'expr_commas' and rule [0] not in ('expr_abs', 'expr_func', 'expr_ufunc'):
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
		if not text.strip:
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

# 	a = p.parse ('?(zap1 = 2)')
# 	print (a)

# 	# a = sym.ast2spt (a)
# 	# print (a)
