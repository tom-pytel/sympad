# Builds expression tree from text, nodes are nested AST tuples.

import ast as py_ast
from collections import OrderedDict
import os
import re
import sys

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

class AST_MulExp (AST): # for isolating explicit multiplications from implicit mul grammar rewriting rules, only used during parsing and appears only in this module
	op, is_mulexp = 'mulexp', True

	def _init (self, mul):
		self.mul = mul

	@staticmethod
	def to_mul (ast): # convert explicit multiplication ASTs to normal multiplication ASTs
		if not isinstance (ast, AST):
			return ast
		elif ast.is_mulexp:
			return AST ('*', tuple (AST_MulExp.to_mul (a) for a in ast.mul), frozenset (range (1, ast.mul.len)))
		else:
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

	if ast.is_diffp:
		ast2, wrap2 = ast.diffp, lambda a, count = ast.count: AST ('-diffp', a, count)
	elif ast.is_fact:
		ast2, wrap2 = ast.fact, lambda a: AST ('!', a)
	elif ast.is_pow:
		ast2, wrap2 = ast.base, lambda a: AST ('^', a, ast.exp)
	elif ast.is_attr:
		ast2, wrap2 = ast.obj, lambda a: AST ('.', a, *ast [2:])

	if wrap2:
		ast3, wrap3 = _ast_func_reorder (ast2)

		if ast3.is_curly or ast3.is_paren or ast3.is_brack:
			return ast3, lambda a: wrap2 (wrap3 (a))

	return ast, lambda a: a

def _ast_pre_slice (pre, post):
	if not post.is_slice:
		return AST ('-slice', pre, post, None)
	elif post.step is None:
		return AST ('-slice', pre, post.start, post.stop)

	raise SyntaxError ('invalid slice')

#...............................................................................................
def _expr_comma (lhs, rhs):
	if not rhs.is_slice or rhs.step is not None or not rhs.stop or not rhs.start or not rhs.start.is_var:
		return AST.flatcat (',', lhs, rhs)

	if lhs.is_mul:
		if lhs.mul.len == 2 and lhs.mul [0].is_var_lambda and lhs.mul [1].is_var:
			return AST ('-lamb', rhs.stop, (lhs.mul [1].var, rhs.start.var))

	elif lhs.is_ass:
		if lhs.rhs.is_mul and lhs.rhs.mul.len == 2 and lhs.rhs.mul [0].is_var_lambda and lhs.rhs.mul [1].is_var:
			return AST ('=', lhs.lhs, ('-lamb', rhs.stop, (lhs.rhs.mul [1].var, rhs.start.var)))

	elif lhs.is_comma:
		for i in range (lhs.comma.len - 1, -1, -1):
			if lhs.comma [i].is_mul:
				if lhs.comma [i].mul.len == 2 and lhs.comma [i].mul [0].is_var_lambda and lhs.comma [i].mul [1].is_var:
					ast = AST ('-lamb', rhs.stop, (lhs.comma [i].mul [1].var, *(c.var for c in lhs.comma [i + 1:]), rhs.start.var))

					return AST (',', lhs.comma [:i] + (ast,)) if i else ast

			elif lhs.comma [i].is_ass:
				if lhs.comma [i].rhs.is_mul and lhs.comma [i].rhs.mul.len == 2 and lhs.comma [i].rhs.mul [0].is_var_lambda and lhs.comma [i].rhs.mul [1].is_var:
					ast = AST ('=', lhs.comma [i].lhs, ('-lamb', rhs.stop, (lhs.comma [i].rhs.mul [1].var, *(c.var for c in lhs.comma [i + 1:]), rhs.start.var)))

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
			return wrap_ass (AST ('-lamb', rhs, ()))

	elif l.is_mul:
		if l.mul.len == 2 and l.mul [0].is_var_lambda and l.mul [1].is_var:
			return wrap_ass (AST ('-lamb', rhs, (l.mul [1].var,)))

	return _ast_pre_slice (lhs, rhs)

def _expr_mapsto (args, lamb):
	if args.is_var:
		return AST ('-lamb', lamb, (args.var,))

	elif args.is_comma:
		for var in args.comma:
			if not var.is_var:
				break
		else:
			return AST ('-lamb', lamb, tuple (c.var for c in args.comma))

	raise SyntaxError ('invalid lambda function')

def _expr_piece (expr, expr_if, expr_else):
	if expr_else.is_piece:
		return AST ('-piece', ((expr, expr_if),) + expr_else.piece)
	else:
		return AST ('-piece', ((expr, expr_if), (expr_else, True)))

def _expr_cmp (lhs, CMP, rhs):
	cmp = AST.Cmp.ANY2PY.get (CMP.text.replace (' ', ''), CMP.text.replace (' ', ''))

	if lhs.is_cmp:
		return AST ('<>', lhs.lhs, lhs.cmp + ((cmp, rhs),))
	else:
		return AST ('<>', lhs, ((cmp, rhs),))

def _expr_neg (expr): # conditionally push negation into certain operations to make up for grammar higherarchy missing negative numbers
	if expr.op in {'!', '-diffp', '-idx'}:
		if expr [1].is_num_pos:
			return AST (expr.op, expr [1].neg (), *expr [2:])

	elif expr.is_mul:
		return AST ('*', (_expr_neg (expr.mul [0]),) + expr.mul [1:])

	return expr.neg (stack = True)

def _expr_mul_imp (lhs, rhs, user_funcs = {}): # rewrite certain cases of adjacent terms not handled by grammar
	ast         = None
	arg, wrapa  = _ast_func_reorder (rhs)
	tail, wrapt = lhs.tailnwrap # lhs, lambda ast: ast

	if tail.is_attr: # {x.y} *imp* () -> x.y(), x.{y.z} -> {x.y}.z
		if tail.is_attr_var:
			if arg.is_paren:
				ast = wrapa (AST ('.', tail.obj, tail.attr, _ast_func_tuple_args (arg)))
			elif rhs.is_attr:
				ast = AST ('.', _expr_mul_imp (tail, rhs.obj, user_funcs), rhs.attr)

	elif tail.is_pow: # {x^y.z} *imp* () -> x^{y.z()}
		if tail.exp.is_attr_var:
			if arg.is_paren:
				ast = AST ('^', tail.base, wrapa (AST ('.', tail.exp.obj, tail.exp.attr, _ast_func_tuple_args (arg))))
			elif rhs.is_attr:
				ast = AST ('^', tail.base, ('.', _expr_mul_imp (tail.exp, rhs.obj, user_funcs), rhs.attr))

	elif tail.is_var: # user_func *imp* (...) -> user_func (...)
		if tail.var in user_funcs: # or arg.strip_paren.is_comma:
			if arg.is_paren:
				ast = wrapa (AST ('-func', tail.var, _ast_func_tuple_args (arg)))
			elif tail.var not in {'beta', 'Lambda'}: # special case beta and Lambda reject if they don't have two parenthesized args
				ast = wrapa (AST ('-func', tail.var, (arg,)))

		elif not tail.is_diff_or_part and arg.as_pvarlist is not None and len (arg.as_pvarlist): # var (vars) -> ('-ufunc', 'var', (vars)) ... implicit undefined function
			ast = wrapa (AST ('-ufunc', tail.var, arg.as_pvarlist))

	if arg.is_brack: # x *imp* [y] -> x [y]
		if not arg.brack:
			raise SyntaxError ('missing index')

		ast = wrapa (AST ('-idx', tail, arg.brack))

	if ast:
		return wrapt (ast)

	return AST.flatcat ('*', lhs, rhs)

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('-diff', expr, 'dx')
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
					return AST ('-diff', None, tuple (ds))
				elif i == len (ns) - 2:
					return AST ('-diff', ns [-1], tuple (ds))
				else:
					return AST ('-diff', AST ('*', ns [i + 1:]), tuple (ds))

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
						tail.insert (0, AST ('-diff', ast.mul [i + 1] if i == end - 2 else AST ('*', ast.mul [i + 1 : end]), diff.dvs))

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
					return (AST ('-intg', neg (ast2), dv, *ast [3:]), ast.dv)
				elif neg.has_neg:
					return (AST ('-intg', neg (AST.One), dv, *ast [3:]), ast.dv)
				else:
					return (AST ('-intg', None, dv, *ast [3:]), ast.dv)

	elif ast.is_diff:
		ast2, neg = ast.diff._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			if ast2:
				return (AST ('-diff', neg (ast2), ast.dvs), dv)
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
		ast2, neg = ast.add [-1]._strip_minus (retneg = True, negnum = False)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('+', ast.add [:-1] + (neg (ast2),)), dv

	return ast, None

def _expr_intg (ast, from_to = ()): # find differential for integration if present in ast and return integral ast
	ast, neg = ast._strip_minus (retneg = True)
	ast, dv  = _ast_strip_tail_differential (ast)

	if dv:
		if ast:
			return AST ('-intg', neg (ast), dv, *from_to)
		elif neg.has_neg:
			return AST ('-intg', neg (AST.One), dv, *from_to)
		else:
			return neg (AST ('-intg', None, dv, *from_to))

	raise SyntaxError ('integration expecting a differential')

def _expr_func (iparm, *args, strip = 1): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	ast, wrapf = _ast_func_reorder (args [iparm])

	return wrapf (AST (*(args [:iparm] + ((_ast_func_tuple_args (ast) if args [0] == '-func' else ast._strip (strip)),) + args [iparm + 1:])))

def _expr_func_func (FUNC, args, expr_super = None):
	func = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC

	if expr_super is None:
		return _expr_func (2, '-func', func, args)
	elif expr_super.no_curlys != AST.NegOne or not AST ('-func', func, ()).is_trigh_func_noninv:
		return AST ('^', _expr_func_func (FUNC, args), expr_super)
	else:
		return _expr_func_func (f'a{func}', args)

def _expr_subs (expr_commas, subsvars):
	if len (subsvars) == 1:
		return AST ('-func', 'Subs', (expr_commas, subsvars [0] [0], subsvars [0] [1]))
	else:
		return AST ('-func', 'Subs', (expr_commas, ('(', (',', tuple (sv [0] for sv in subsvars))), ('(', (',', tuple (sv [1] for sv in subsvars)))))

def _expr_mat (mat_rows):
	if not mat_rows:
		return AST.MatEmpty
	elif len (mat_rows [0]) > 1:
		return AST ('-mat', mat_rows)
	else:
		return AST ('-mat', tuple ((c [0],) for c in mat_rows))

def _expr_vec (ast):
	e = ast.comma if ast.is_comma else (ast,)

	if all (c.is_brack for c in e):
		if len (e) == 0:
			return AST.MatEmpty

		elif len (e) == 1 or len (set (c.brack.len for c in e)) == 1:
			if e [0].brack.len == 1:
				return AST ('-mat', tuple ((c.brack [0],) for c in e))
			elif e [0].brack.len:
				return AST ('-mat', tuple (c.brack for c in e))
			else:
				return AST.MatEmpty

		elif e [-1].brack.len < e [0].brack.len:
			raise lalr1.Incomplete (AST ('-mat', tuple (c.brack for c in e [:-1]) + (e [-1].brack + (AST.VarNull,) * (e [0].brack.len - e [-1].brack.len),)))

	return AST ('-mat', tuple ((c,) for c in e))

def _expr_curly (ast, forceset = False):
	e   = ast.comma if ast.is_comma else (ast,)
	kvs = []

	for kv in e:
		if not kv.is_slice or kv.step is not None or kv.start is False or kv.stop is False:
			if ast.is_comma:
				return AST ('-set', ast.comma)
			elif forceset:
				return AST ('-set', e)
			else:
				return AST ('{', ast)

		kvs.append ((kv.start, kv.stop))

	return AST ('-dict', tuple (kvs))

def _expr_ufunc (args, argspy = None, name = ''):
	kw = None

	if argspy:
		name, kw = AST.args2kwargs (args.comma if args.is_comma else (args,))

		if len (name) != 1 or not name [0].is_str:
			raise SyntaxError ('Function() takes a single string name argument')

		name = name [0].str_
		args = argspy

	args, kw2 = AST.args2kwargs (args.comma if args.is_comma else (args,))

	if kw is None:
		kw = kw2
	elif kw2:
		raise SyntaxError ('keyword arguments not allowed here')

	return AST ('-ufunc', name, tuple (args), tuple (sorted (kw.items ())))

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

	return AST ('@', var)

#...............................................................................................
class Parser (lalr1.LALR1):
	def __init__ (self):
		self.TOKENS_LONG.update ([(v, self.TOKENS [v]) for v in self.TOKENS_QUICK])

		lalr1.LALR1.__init__ (self)

		self._USER_FUNCS = set () # set or dict of names of user function names to map to AST ('-func', ...)

	def set_user_funcs (self, user_funcs):
		self._USER_FUNCS = user_funcs

	def set_quick (self, yes = True):
		self.TOKENS.update (self.TOKENS_QUICK if yes else self.TOKENS_LONG)
		self.set_tokens (self.TOKENS)

	_PARSER_TABLES = \
			b'eJztXWuP3DaW/TMLTDegBkp8Sv3NcZxZY20nazvBDowgcDyeRbBJHNhOdhbB/Pe9Lz6kYpVUqu6uF9HqkkSR0uW95Dl88+rNX149/vrZ1y/+0vzl397/+nc4hdtnT756DadvHr188uIZXHz18tFjObVyVnD+4umLr5+HcxsulLzgy6/xHS/o94snf/3h8aNX' \
			b'T17J9fNHwfWLdPlduvyGL189e/Tq37+Ar/0HShEvyPnxty+f/Q3v4sW3X3374vE3fwtX6PH1S/z99gv4ffL8m9d/e/WEZPoWpf7uET58/vTFtyjV0xev/4qCP31OIej3P1+i72ekka/xqbz2Cwr5+Ovnzx8FLaHDy6d//ffXQaCXQWC8+PKLZyQzivGf8PPo' \
			b'+Td4+eJLUQRefZEuv0uXoognz149wU+9fPocz18+/e7pl3jxmJX86jVJ9M0zigpEMsTqv149eUwevnz61VeomBdPycCPSYBHL77EmOODr1/KB4OVUGR+62OI3+twRis/f/TNq9dfY/jXpN8n//UY1U9OoOt2YCExALzr8X/A5afff/z0x9uPn/7Irj/B9bu3' \
			b'H99//uHDxx/+/uPPnz6//Zg9hks4vSVv7//5G3j56Y9fwvWn3397/zHc/Pr+v394+/G/07Mf4fKXt59/ePfhZ7n6+OF/0xV/+NP7T5/exavf4lV4zdsf0+Xnz/Fj/3j77nO4/o3eys6///ouCfqPf/yWpIlC//xTvPzp189R3l9+//mHn375LYtm/qIskvEy' \
			b'vRLD4kW4//z+Y3z2x9uPI2/h9vdc2rd//3u4fPf7x5//L9z889P7FNMfP7599z/v4+2nXLI/3sd3/f7rTx9+jR99G/2/S9EjJceYfEiv/D3T969RpB9/+vVDjNGHZAWQJ1rh3YdffnkbA//20/t37+MNpK9MoN8+ff4QPxJNHUX78HOSnl46uIlf+MQev2/e' \
			b'XN3YrnH2uuELhxfG4Y9vjL6WW7ijqw69NcY2N/Z64MB3PoSDAF1wwkvydcMvt82VbjS4q8as4OI6upJbcrihcMrxjwUHxS8NTqpfc7Iud8JLuGoN/7i2uWndtTjhJVxhQBAZ7vnDDi9QAMM/rr+WW5CJgurmqoPQFv+vg0uf37UruUA3FEVjnNte4mzUdXAV' \
			b't+hwo/gboEkMDqp35lpcbtqerjr+cSvwvboWJ7xEMUnTCkJeZ7fhOnNXfLqhz2n61114jF8mgcSdpWtutDjyPRlSrSRSXkdXcWuTQzt0uFGkYg3f1yQAhKcfy17g6gZ8oxfLPxa+blm/cHejyXQWX93HBzY+MJp/PKuH0iNFqG2bK7QbWoblRReX33k5oxOG' \
			b'hecavFvJC+HWjJ2CJYfuZv125GTXbws+Rq9167eDQDdGZaKlxC1CjBzs2MFlDpArr/RKRABX5QbO6fZGU2aDVHSl2wasTFbvGw8n+AL8apZvgw/EHzvXI9wMPd5oyhyIQJA1YkoGsTjT9JIDMeMbCOyyjIgPo3tysezik4tjly65eHbpg8uNomSrUCBOwC3/' \
			b'WJ2kDU4md8JLvHL8cyM4KJd4pTm1hyD4QkrUVh6I+fFLhgEI3tWqhHmYztlGquEc2Cr+cZghBGgUXZIebxjI8IIi065QiyZAt8QaHMlJ7nt5JbwH8HgV0lHuLA5wT0lO8Q8kr2u5hyxLr6Z/TGX8JbxA7Sr+sQh7HAbu8BKjDw8RYlqGErj1FAjMedW2kXVC' \
			b'qrI+4BIBOmsaE4uKPhwltdxafdAwOF65lIPp1qVvA3vwCyEKWoUr1csVC4wXNlwQfClIxRgh0CxaIDppygRjp3QLb6CrFf9YTI7CLCu6xKu+YVKEqF0Rb0T2QeUwwhv+sT7mb8U5HyPV8k8qBNhWaMSu+AfxVpAc7W8p7Zg+PLyWW7gLD9gvRMgb1nkfrIIy' \
			b'WP4wvsDFF2DsHL3ArcID8ipOIZTjSCOgQTyhxPNm1bRg67Ylu0Jig3BgUUwVpgEshBwHyQMgpUe8AM11uukMcLqDfw/hMHwL/wruO/jvUVEIXj1ycrtCv5B0gBsNpSEIB8HAJ8SsVRgKzivIL/DFtoGEBlm5s03nms43Xdd0fdPDe0CIFqRoQbDW4Pfw24B8' \
			b'kHQJ/1oQvTWE7mALBDQMgACHsYOPIilBlFqIUwuR6vHrKAUE1fh+uIeP93Dopkeh0T982zd9ByAHZIy029umd42Hwze+a3zfdKCStung6xDHFiIJFgTDQunKEZI4SPYWipKQ+BGJHeD2CqHbQ1YETjaNR+1DUBAVAB8sBIohvTSoV4WlUri8xvwKPsFmV2gs' \
			b'cHhzhYqABxh1OIG09Nis+CnG9poIjU4dPX2DfEb3Hk/VyEdi5KuejdbSGQuNbC2wBNlesW07tilZhs5egrUhjbRyVuLByIvIcODScXJQnpNOeF/0Rd+vUHCcqeTNlSW7DXQo2mOtFfQleor6GeplqIuSIiT+kPqcIIvtDiiEDTllxSkZzU9pV1FWeUBJlMCw' \
			b'Mg/9YYl5J5pQbc20x5xp22qfI7bPFQlH5SlX7XTMdlIqQD8ZLKqMlBVVIyoJmshjD7GNMTt4jFLiKSSYw5ArqlYqEypUF4jzsZ0DvthAfGsOOFwOCEClpVagY9mnq8h1vHaDahwxS2sw/iCvRR2AE0YRq2AQ4WqdA1rHV+scsXW6ap0jtk5frXOs1rnqpcGG' \
			b'FEDNgqHA0HIrcS0xHKnlWtOGll0xnZEmYBXav0woBMpzPlkxsLHVvkdsX8Pt76Enp6fbgwt2nFVSru2ISOwiiZ37ttCm8elVyxnkqtVBt9wl0nPFttfSiaYkX2npOdHyPPSIhNzFb+ulrdVwKNtKNrMSigS5cFNd9aJxz71TnovV2KWF/Vm1HWa+Jr0kN8+p' \
			b'r+M02rXSCyide9zjgR0AnGiN9ABboX3HKd+xd8cp2tNdj1kGvGFXAkXNX4BaQSOsKMcdKF5fsio4kzomIse45s0GjYRcfBGa4UznOdN5e8GJxIfhBNK3GmPP3Vqcm2woc1pOUkpgKjbXtzjqtpZFj7QsSuOIFA8gUnVI0BHZRfPIdG2rXY7ILjiCTslYLThX' \
			b'Axyg0VHXHHFUBkEtKxl/COdqiIMZYkWcIYqrAyTuYYBEVwuzx5wDOiot4QDnaqYjNpMx1T7HbB8m9Gqf47QPTdSgSoglnDsUGxZmk2D7cycVJJKtlkLuXu+KKkAPOeWAmyLwi1zOp5NxfLdqxeDSl7Z5rtH3MpcJWzcUxaGmh/2to1esf+7h4VZZL31FMmWH' \
			b'W/nD6A/NObPqfI8cQSCHIzs56ZswTkO6n01UdujrjxmAx2bgsEN6g7xIAL0V1Kw22d0m+CqxhoBLVd4uAy1QZ1VPk3oyVU+z9GSrnmaAluEGi94LdGku26UBTasujOI0oyfcM/QGxzapOnysnAp7XXWzSTeWyu1W4+o7VSU0hE1ylHdcwRoMePBcYNsw4rZt' \
			b'w8BDGjRxBJGhYXcyjEzxMDLFw8gUV8Q01+L4qZNKnGMw4QEv52/yNzgwjlqMuzpi+nhbvN7gwMXa3X4Qzfd9NgTuEhCBhvqlAbU4wtZemgp4dZPDi3LVSvuhM8JP9sL4yesKfAfpZHHStuf8haU4111YhL2pWewwWUxavf3q0lKcrSnuMD3n3MyNsxYUT1ZQ' \
			b'srim5jHwdDJ0avkOrKTDKotaRjnq6zDcTqdF6Kitjrx2/Lq67scRpwSIpOZ+ac1rYPKJbW59MCyelOY71UoC4JCOjY3azZbjwe5YdqekRYWHunDSgdfN5CYuIplqhsONKtOSrQJgqi7gpA696Ep6z6kTvILkwU3GIzWrCQ7GUx3nmU6ySh8KI5KVwsIgqBsd' \
			b'Bj/oTf0U6MrB+MTlFGMlhDyU8k/PL+rZ1bb8fkvvrb1GeUeaqctAZHUbQvM6+Ga+zqjzUElXneauOs1ddaRJaZKlfNjiGuC8HrfiDOk4f9KItO9phQfKtb0M2bRy5sGajrO65zCOQcQxtnjO9p4/7m2q9phaVz3IKO8ONU/VSRMGG3LNxXDNxXDNxUjlxFB9' \
			b'g8A6cIETuI+DD9nGVseObrO5TxuiaTg1Gk6NJnQcUyBejZ4SoLkOhbmLacShjGFlvLMVM9lQmmUzWTYT++ITyGclp1vWrWXd2lrKOmhBF15t1xe5sHUi2RGbDaHH8lQDF/ZCcMiR8BjX5gpcSdnNcXZznN3QWxMt7+oYsTLGSUMYfMQLetGZVkDDs4pDjHxV' \
			b'4YZZUivSWYeqQ5XyrJi4hlfQa0cJmMfktVjJwloFLq6D6+rEQh8qkdNxx+/sxBzM91aI3AYmD9U+XpyHhOmroTYYqq262YgDLRdFWy45UspSeW0EF6lbcZKkM3rgXpJVg9vMNYq2EcCWcNxKoM+iq4n3iEIhNhK9jqKlhGuFgDP5Wek2qDDXUcESHdmADTA0' \
			b'IpM2KA8X4VwFWhZ9oA5QN0ivuBQkzsihRsle+EVz9kQ6xwX2cIE5XF0OV1fDpdVwXTVcTwwXE8PFtHD1PVzcDxf2Q4WhsnCPLyw24HQ57DDCJZXReEjDyLbYqoBLK6J8uA4lVuxAToWz7qBwoFa48SzoDIsSILeChKNwlQKcwotj8HFCERYHUMGkYUxsEA5T' \
			b'EuoalY2VQ0wluAYUTqLBRj8cmI7tsNgmi2NELe7NiOkOwmO/LfbZ4qC8Dv81GBr3lu1wq0baGxQ3rsStHnH3T9x5tKGNF3FHzQ73G17h1pAr3MgXnWiPQtrOETfExc2KcQNK3GtT4+6zijaAxE13aW9QeBu+Cl+Nyfumpb0bMTjtbosvxbeTC+4Z2tM76G0U' \
			b'Dl7Ukwy09S346nGP1I73de1x02O4ppgo3EkWt+2krxjaAJP216QPoTC0zy5tw0r7QmKRjSLZoxT4FMx3473EBHd6pJ2XV6QLcIYUc4PbZDoUFvfipb2d6XP4atzjFF8L5w6lpc14V/ShnjbspM2QFT2iLZJxP9MbjiY+wIiAI6DCTYfX9BUMhbbBgiHv/2t4' \
			b'D2dD+wGTVsClx2jQ9pW84yduV+rRjXYrRa9oKdzyE3LVjcPIwCc87paLKqOtQOHsWIyWd/BEPeFGsYa39MTNVjt6FX4V4+0xqvCka79HFEHsqMhxAchRYaPCxp3BhkLY2AAYtoQZLhWScvDQ2b64Awjp7h5FQNmQPlNT+S6g4mYAyzkAih+BipkAFoe6dRMw' \
			b'4jYDicOHmAVdAU5cAhRXghT3MKDiWErtmvS3I7C4WdBydoiCAmWo4iZwpfnT3iIxuVukps7Ayf4LR4ttB5vYqseQQ1W9vBY3AJ7QzDdqYeRmxwkoouoq98vOwiQ/hCWqlxbruQmihvXLhFVWas1hneRV3gyqpKLKleXUwBrqm1LXHNdHI8itMqCz2Qi6bFRd' \
			b'bO8rNJvgdrW4aywBIvjD9dAngdHMAEe0ajcCSQiLWwzsA5a4tA8BJvgD3e0MnJiYZoGnSgAK+mEQtUMg9diM3GeAihmU2ponMBU89IyreArQitcgZp8AFhuhDYMRnakZxDLO0rcYatlbPCLuUpg14EVXQV7aJphaNFZLUJhk6fk1a0hM787+15A5yYvpOcqP' \
			b'3rPI9AzXUT8Zao+/MPgapqsYMz1+yCjfE/esItBn32Ytr+J3A/aLF6SA+EZDbBAup0mhncEL0fKJHcRpX44YKAJ71ncnDDIic4a8ZQNniMiIJ+ivC1/N+SPKEnmEGcQBnUAmZCJBrLulfACZ/xZpDjLvLWjmX7Skz2aGMfNKtCdKLMQqiVLsDrSyuiNqqbTy' \
			b'ALRimVbsBK2gQuzm4jrmBCtsYoVNApnYRCZ2cCQysUUysYlMYpAFTCJEUuKRXJg1DolPtBtLnp5Z/kDgjp4VWPaLCccGTVKWSI/yusGAN3JflB1txhjs7HIFYcoX39NsYWewRbBsxhbstDdbpHgto4pUvWi3MoUohlNUF9JRzhMSoW0sUSAHu2dbx57McHBO' \
			b'mMEHtXpxKjzgmAemmmzaLW02CNTSatNKsw2dV3wOJOAGRyKBYlNOm9pyljXn0Cc48Br852KswX98ot1Y5vTM8gcGVYeix9AKlLkw5LfjikIeivJaiLlgPt+63BumcvE1jfluBuYHQ2aYz057Y36K2jLMdwnz3TbMF8VwAuqsqDDHfInQ0pqBq+Bfwf9cwL9j' \
			b'8O+mwL/bAv4cnsC/E/DvBPy7BP7d4EjgX+waxOsA/t0i8O8Y/LsC+OdirIF/fKLdWOb0zPJpAP5FjxH8k4uAfzcC/zwU5TW5DODPty4TisBffE2DfzcD/IMhM/Bnp73BP0VtGfh3Cfy3dScExXAC6qyoMAd/idBS8PcV/Cv4nwv49wz+/RT491vAnwbiM/j3' \
			b'Av69gH+fwL8fHAn8+yL49wn8+0Xg3zP49wXwz8VYA//4RLuxzOmZ5Q8MwL/oMYJ/chHw70fgn4eivCaXAfz51mVCEfiLr2nw72eAfzBkBv7stDf4Z5IuAv8+gX+/DfxFMZyAOisqzMFfIrQU/Ludep3PhgJsZYEzZgFCDRRkggVQwJaIAE8lLhAfnHmYC+i8' \
			b'4rNwAfuKR+QC8rrGBegqXMDv3JUL6BMceMwFAzHGXJCeaDeWeRDQ8jdyOih7DHSQuTAdqFHL/yAUZrpwKXQQLJHJhXQQfE3SAb92Ox1EWyY6EKd96SCL2iI6IJ0zHfBLNtBBUAynoc6KCjM6CBFaSgd9pYNKB2dHB5rpQE/RgSY/PD2qTAfsgzKPFjrQQgc6' \
			b'0cHwSHSgi3SQRo3zO3emA810oAt0kIuxRgfxiXZjmQcBLX9jQAdFj5EOkovQgR7RQR6K6EAuAx2IJTK5iA7E1zQd6Bl0EGyZ0QE77U0HKWrL6EAnOtDb6EAUI1JbUWFOB/JoKR20q8oHlQ/Ojg949KmaGn2KQhnmA7OBD9gH5R4Zd8ooyefAB2ZwJD4oDjtV' \
			b'adgpv3NnPjDMB6bAB7kYa3wQn2g3lnkQ0PI3BnxQ9Bj5ILkIH5gRH+ShiA/kMvCBWCKTi/hAfE3zwYyRpNGWGR+w0958kKK2jA/SMFJ+ySY+EMVwGuqsqDDnA4nQYj5oj2eSwulMT6jEcCrEwOOG1NS4IRSGhw6pbFqC4mkJOT3wHWUmGUOkZAyRSmOI2Fc8' \
			b'Ej0UxxCpNIZILRpDpHgMkSqMIRqIsUYP8Yl2Y5kHAW2M+IAhin4jQyQXYYjRSKJBKGKIEH9hCDFJ7g1tLb6mGWLGSKJozowh2GlvhkhRW8YQaSSR2jaSKCiGk1FnRYU5Q0iEFjMEzZmlQayC9z0hvV4DeI1wnnB3E+h2CRMJ93rGOMSwgFGCS4QNnO8hL+NH' \
			b'D3B8z8vgVZasLHmuLKm5OU1PNadhouXmNJ01p+E1iEknZknx1zJMEEtqaVTTqVFtdESW1MVGNZ0a1fSiRjXNjWq60Kg2EGPMkumJdmOZBwFtjHjOkmW/gSUzF2ZJPWpXG4TC3BcuhSWDSTLRkCWDr0mW1DPa1aI5E0uK074smUVtEUvq1K6mt7WrBcWI1FZU' \
			b'mLFkiNBiltw2Fa8yRGWIE2cIzwzhpxjCkx9kCJ8xhGeG8Ikh2B8xhBeG8MIQPjGEHxyJIXyRIXxiCL+IITwzhC8wRC7GGkPEJ5JVswOTVHpuY8wHFOELR6KI5CIU4UcUkYciigh+hCLEJplsRBHia5oi/AyKCPbMKIKd9qaIFLVlFOETRfhtFCGK4XTUWVFh' \
			b'ThESocUUMTEhr1JEpYhTpgiepaGnZmmIH6SILqOIjimiSxTB/ogiZMaGlhkbOs3Y0N3gSBRRnLGh04wNvWjGhuYZG7owY2MgxhpFxCfajWUeBLTxasAQRb+RIZKLMMRo3sYgFDGEXAaGEJNkohFDiK9phpgxbyOaM2MIdtqbIVLUljFEmreht83bCIrhZNRZ' \
			b'UWHOEBKhxQwxMWuvMkRliFNmCJ7KoaemcuBmmzybA0+RIXpmiD4xBPsjhpBpHVqmdeg0rYN9xSMxRHFah07TOvSiaR2ap3XowrSOgRhrDBGfaDeWeRDQxogPGKLoNzJEchGGGE3uGIQihpDLwBBikkw0YgjxNc0QMyZ3RHNmDMFOezNEJukihkiTO/S2yR1B' \
			b'MZyMOisqzBlCIrSYISam9lWGqAxxwgwhKzzjaStDYPpcEUOYbMofXoOYdGKGEH+YmeisFJ9XfBaGYF/xiAzBIDNmCHQVhjCL1g6kT3DgMUMMxBgzRHqi3VjmQUAbI54zRNlvYIjMhRmC45YYYhCKNvKSS2GIYJJMNGSI4GuSIfi12xkimjMxhDjtyxBZ1BYx' \
			b'BKmdGYJfsoEhgmI4GXVWVJgxRIjQYobYbf5fZYjKECfFENxVbaa6qjFZcle1ybqqDXdVm9RVLf6IIaSr2khXtUld1WZ4JIYodlVnuwaYRV3VhruqTaGreiDGGkPEJ9qNZR4EtDHiA4Yo+o0MkVyEIUZd1YNQxBByGRhCTJKJRgwhvqYZYkZXdTRnxhDstDdD' \
			b'pKgtY4jUVW22dVUHxYjUVlSYM4Q8WswQ26YEmssgCVfiCVu54qy4QvPgXz01+BeUgamWx//qbPyv5vG/Oo3/FX/U5CTjf7WM/9Vp/C/7ikdqciqO/9Vp/K9eNP5X8/hfXRj/S/v8RjnW2pzik5HEo6PnGeTiN1BGLy1PpRCp5Sm5SMvTaBjwIBS1PAU1SMuT' \
			b'WCb3hi1P4mu65WnGMOBo1azliZ32bnlKUVvW8pSGAettw4CDYjg1dVZUmLc8SYSWsobaNnGwskZljXNhDcP92GaqHxsUYdgbVjKyrmzDXdkmdWWLP6pkSFe2ka5sk7qyTTc4UiWj2JVtUle2WdSVbbgr2xS6sgdirFUy4hPtxjLnB6KgjX4jaSiuapRCpKpG' \
			b'cpGqxqhDexCKqhpyGaoaYphMQKpqiK/pqsaMDu1o1KyqwU57VzVS1JZVNVKHttnWoR0Uw4mps6LCvKohEVpMGnV24X00RkE42bq9UsZdU0a7gTb0nNmG3MGtpjq4wYPiDm6VdXAr7uBWqYNb/FHmkg5uJR3cKnVws694pNmGxQ5ulTq41aIObsUd3KrQwT0Q' \
			b'Y222YXyi3VjmQUAbIz6YbVj0G2cbJheZbSgd3KrFpZVMmnWYh6ZZh3IZZh2KaTIRadah+JqedTijozuaNTGHOO096zCTdAlzqNTRrbZ1dCvro3I4SeHMQx+SacYgIWKLGWRix87KILWycSTMsaSygZt5gmFoT89tjGHpQMbAU2AMvAYx6cSMIf4wM9FZyf2K' \
			b'z8IYVg2OyBjkdY0x0FUYg9+5K2PIjqV4GjPGQIwxY6Qn2o1lHgS0MeI5Y5T9BsbIXJgxOG6pjjEIhbkvXApTBJNkoiFTBF+TTMGv3c4U0ZyJKcRpX6bIoraIKUjtzBT8kg1MERTDyaizosKMIUKEFjNEnZtdGeKMGYI7vO1Uhzduw8gd3jbr8Lbc4W1Th7f4' \
			b'I4aQDm8rHd42dXjb4ZEYotjhbVOHt13U4W25w9sWOrwHYqwxRHyi3VjmQUAbIz5giKLfyBDJRRhi1OE9CEUMIZeBIcQkmWjEEOJrmiFmdHhHc2YMwU57M0SK2jKGSB3edluHd1CMSG1FhTlDyKPFDFHnZleGOGOG4A4LO9VhYdkPMkTWW2G5t8Km3grxRwwh' \
			b'vRVWeits6q2w3eBIDFHsrbCpt8Iu6q2w3FthC70VAzHWGCI+0W4s8yBguhowRNFvZIjkIgwx6qcYhCKGkMvAEGKSTDRiCPE1zRAz+imiOTOGYKe9GSJFbRlDpH4Ku62fIiiGk1FnRYU5Q0iEFjPEiU7NhrSCJNFWnjgjnjD3uR4ic4Wa4grFfrCHIuMKxVyh' \
			b'EleIP8pWwhVKuEIlrlDd4Eg9FEWuUIkr1CKuUMwVrczBoy90qmFgC10V5A29qAJrJFG1G0s/iImNV4O+iqLf2FeRXKSvYsQag1DURyGXoY9CjJOJRn0U4mu6j2IGa0TDZn0U7LR3H0WK2rI+io566WI/xTbmCMrhRNVZUWPePyGRWswcdcp25YzDc8a91S24' \
			b'R9tO9WiDB8s92jbr0bbco21Tj7b4o7qF9Ghb6dG2qUebfcUj1S2KPdo29WjbRT3alnu0baFHeyDGWt0iPtFuLPMgoI0RH9Qtin5j3SK5SN2iH9Ut8lBUt5DLULcQk2SiUd1CfE3XLWb0ZEdzZnULdtq7bpFJuqhukXqy7bae7KAYTkadFRXmdQuJ0GKGqFO2' \
			b'K0OcL0O4lhgCT1sZApNZSwyBp8AQeA1i0okZQvxhZqKzUnxe8VkYgn3FIzIEeV1jCHQVhuB37soQ9AkOPGaIgRhjhkhPtBvLPAhoY8Rzhij7DQyRuTBDcNwSQwxCYe4Ll8IQwSSZaMgQwdckQ/BrtzNENGdiCHHalyGyqC1iCJfqEPySDQwRFMPJqLOiwowh' \
			b'QoQWM8QRTdnWlSTOhCR43OPDkIXfQBjtiDTanDh46JObGvrk6CDiyIY+OR765NLQJ/FHxCFDn5wMfXJp6JNTgyMRR3Hok0tDn8Lrd+cOHv3kCqOfBpKscUd8ot1Y7EFAG+M+4I6i38gdyUW4YzT6aRCKuCPEX7hDrJKJRtwhvqa5Y8bop2jRjDvYaW/uSFFr' \
			b'o9C7M0gaA+W2jYEK79dRfCu6FBKhL/eZVMupZGK7Vx9IRJ1LBeMAu/qdK2M8dLUCN6bBfYG6qUYormLYqSqG5fpFcV8/TJxSrbBSrbBSrbCpWsG+4pEansbVCkxQNtUq7KJaxU0YGFuoVnCKS//rjU9RSO3GcqdnlmUfNDsVPcZmJ7rFtIHMwDCoR/UKlIf9' \
			b'tWH+XZvPvpPnSA5BfMtVi3A5o/VpRt0i2jRrfWKnIj9IZGbQA0XfihDLmp+4ckG4s3UOngjsNMtNIRW+CK02qmeEyA3JwfhbKqtEduhukdABBm6JESF/3vJGg5El9MQmsMfJEgdmhsAKgRH6jAkCCwT0PyXkP6rGJM91Aj9VJ/CbkR6TjZd6gJd6gJd6gE/1' \
			b'AD84Uj3AF+sBPtUD/KJKgOdKgF9H+vWCfxRKu7Gc6Znllw6K/EWPscifXLjIz8AeyvuitVW2pB9pmYXGor2fVa73M8r1wUJZuZ6d9i7XxzjuXpj3sTB/s7VPOXyAU0VnJUXk7UESmW2FeCm7ExpPTJKuaFzR+DBozJ2/bqrz1/Vb0Linx4TG0uHrpMPXpQ5f' \
			b'9hWPhMbFDl+XOnzdog5fxx2+rtDhu47GUSjtxnKmZ5ZfOkDjoseIxsmlhMaitQEac2eu425cN6sP183ow40WytCYnfZG4xjH3dG4n4vG8gFOFZ2VFJGjsURmLhpPTDiuaFzR+CBo7LkVxE+1gvgtrSA4UlhaQby0gnhpBfGpFYR9xSOisS92rvrUDOIXNYN4' \
			b'7lz1hVaQNTROQmk3ljM9s/zSHI3LHgMaZy4FNA5ay9HYc/uG53YNP6tNw89o04gWSmgsTvuicYrjzmjs25loHD7AqaKzkiIyNA6RmYvGE5N7jxONa3v2wZH72IbJYG5CCDVT6G22oLehx4TeRtDbCHqbhN5mcCT0NkX0Ngm9zSL0NozeZh29B2KsIXl8ot1Y' \
			b'5vTM8gcGSF70GJE8ueRInjdfD8JhTuOIC66zs8tkIoAX39MYb2ZgfLBjhvHstDfGp3gtarYmlTPQ80s24bwohtNPZ0WFOc5LhGbg/KBlemKqbsX7ivengfeW8d5O4b3dgveWHhPeW8F7K3hvE97bwZHw3hbx3ia8t4vw3jLe2wLe52Ks4X18ot1Y5vTM8gcG' \
			b'eF/0GPE+uWzE+9wX4b3N8J6dXSYT4b34nsZ7OwPvgx0zvGenvfE+xWsZ3tuE93Yb3otiOP108skB3kuEdsX7iYm3Fe8r3p8G3jvGezeF924L3jt6THjvBO+d4L1LeO8GR8J7V8R7l/DeLcJ7x3jvCnifi7GG9/GJdmOZ0zPLHxjgfdFjxPvkshHv83CE9y7D' \
			b'e3Z2uR/Ee/E9jfduBt4HO2Z4z057432K1zK8dwnv3Ta8F8Vw+umsqDDHe4nQrng/MV224n3F+9PAex6p4qdGqvgtI1UwOQmAeRmp4mWkik8jVdhXPBLeF0eq+DRSxS8aqeJ5pIovjFQZiLGG9/GJdmOZ0zPLHxjgfdFjxPvkshHv83CE9z7De3Z2mUyE9+J7' \
			b'Gu9njGeJdszwnp32xvsUr2V4nwa18Es24b0ohtNPZ0WFOd5LhHbFe5r8CoC8feeYs4Z99cAbxSyFf78DBagTowF9n2vqYD7CiUIrogTMFxM7x+hGbaEFep9moFPCC0p4QSVewLhlR1pUp8gLKvGCWsQLYbC6KhDDQI61tXTwyygyN/2MxE7hLIuO2YEQGDeL' \
			b'IQDa4D8up5NcNjHEIBwtqJMxhDi7TDRaTUd8Dxii37SiToElFPkcMkV4ab6qDjvtvaqOpxHrajFVoBzY4z6rnzeoidMVrf0/4osQrcQX5IK/QBrw22n6NeQOxIEng3dEG13zZgtprNNFRyyhhB+EEHI2YCqYyQObRtYQ5CN+5cX5iNmlATH5QBgn2DsHc6eK' \
			b'3DnG7oGthKs74uksHLWCnRluRrzEnDMbKzeiZMjlMsUzoGKEwQIGBgDcA/2mR6gEnLsZLyUZAas4xmQ4ugTR6GZ9iN8m+JksoQ4QZ2+sQaDZHWDmIQtiCgLKEE0CjiA09FuhoViYfBh0CGVCSECXjhG460sRJ+ZixG4FKiounRxQZIUiNGYFjHGJxLhNoLEL' \
			b'YICou5Ul3IMDxrDiyMjR3jN6YNQRLDHx+eNGk71LHDuiyUYkCbWyI0cTkjP/F2Rp6Q33jy4M/2AMrajqfRJoU0YaZXcpnjR/KpyN2zmsw4BBdq3DSGPXFtzp7hp6AtzoDG785RVYIsSoLQWW0DCE6xWsBG7AP7YhDBqINM3gVlSpxgo+NmSu8tVv4N/cISxx' \
			b'xtU7w9IhoClCUVbQQUteemEnLmdMe9RsLOxQQZe3Ir3BVl1ue0Gfa/tqpYZKekxio6VpUYO0nwreWConqb3aXHAz6GI7/P3glWAVSqbUBF65E8IstyNutfMqWtY9QPFoQ9HI5DhEMHUERaRxZYut2E3hEIl/eliEaWPXylc3s/KlZFnEzRUwfZSNuZsgBQzU' \
			b'koCQlXHpxfZQxaFxX9pDF4ngGvtrNF5vGkpRKB7FolFeJArFoHsr/hx5jWwNbihnUwfpTUvSGHvYMtBowNqhikHYjYVvp8GMZg4ESZEoFodGpSAu4bj14o5p3hwBIm0aY3D3XU3HULpZUiPT+zT8JGjp3KkiC43woJEcPY3aeNAupyMqxCytUJm9upyaP7tb' \
			b'oCVq0bFHARmTMIFi3UnJ5dQgY25JZSZknFVpZHNJpKMxWndVAjlZwBAlzCpzTPY5ucVIgSs6PihYmDus6iwdQT4eMvjQwLE6bvDAcZ1HjCD0LUOy3F1NpowjdrUrmNDyq4fqwKYvza/KTMKKXw4r3QPDSgYpuHXFQcshh4CUCidLx8kNoQQtdxzFkgMiyd2i' \
			b'SLccRfoDokhfUaSiyGIUOZbKzdmgSL+8MWR1OBQBsSqKVBRZiiKuosidoghY4ySaVC+qGfUIYeJ4EeIu4UCRzKfSYLpv9m/+hOxwixCInSsgRkWCU0CChf2vp4cG9Lo7BIOWh+ieZ+/JXczua/706pYwGHLSLWInAYOqwFCB4VDAQLn5yIoJFwkNztwCSBMg' \
			b'6AoIFRDuARA4zZ9gveEiAcG6W0BwAoTjGMpZAeH8AMFUQDhFQDiRgZoVEDYAwoadwQ8DDpSXj6eRkYIfDTaINPcKDfSNWdCAc69LO2cnkAi7ZW/aJpvgY/nozQofxwAfRwAZ7rggwx0VZLgHgIx9SxOzgGL5eMwKFJcMFJTmzrAD8y6AgvPj6VQ7jL0l3IfU' \
			b'jRe0fqldPsSyAsPlAQMlqrMe2bADMJAyzqE9wmBnpqZVHPCCgWGPUZMVGC4GGMj/ZYx5moEMpI2zaqrUUGbAPR46PCsEBlcHQlZg2AgM5PeyxkJeZBeGxiLDigGhjoe8dEDAnHk0oyGPAg9QtstBA7W6JU5oaVjkyhAs1NGQFwgLmIIPPxbyaGHh0ooJrcaW' \
			b'Ri4m1MGQl4gHfcWDigdFPDiRsZAQy7jS7oNjQ2mnykOtrlsnW+6yVh0Oq4DQh8MMzMbHgRzgtBE/dpmC7Y5jsOTyhXB9hhqrEypVqHsqWehsm5LzRo628L9keBSBkI+xWp1m4WPZvq/zSiCkIlrs328tiXgcLEVjsN1xDKKssFJhZXdYadf+F8FKW2FlClZa' \
			b'gZVuLqwcx5DLCit3DCtnDylq7X8RpKgKKVOQoibbSzI46Zo3fcAQBhBGD4YOQ6BhCC76ABQRJQgiQmbXeYZsJSO6DRmwG2a2ccbAzOBXuFW6zxN6SOMxecekjReUojExY6qlJByT7yjppmQbExumr5gQUGmUAFYb7I4mH1p4zRKsfa5g9vvqmME1wqoTOO0Z' \
			b'Ggda1ztq3pRhKVqAsuA9mgBjQPk/mkIFc+AbaWBobpeYOefbhheVKrQqZjaCLLanjSIHFs1kzsJUGVyXzRWQ9kFM1jZvaGu3luKOZGsVPVDwAMolDty5jLEiZ928UVqBI6iOHAxcWo8OTn9/DeerG3gnqpI+cAPvQTylHbE9bU7raHfHrgFqyzetxhUBlcU9' \
			b'veDWyObVineVjTs04jZoYNbRxtO046EjAW/07t/TzZY/eqnBl7qNr5Vt4PyG91N5zoz+4pZukGsyd/qcLXxO4xeBRKG4gQsor2Z8nbZNCO3UtGYolpOUSAWZL/4hkVtZITn92+IfP22p5RmvaVVQzMQkulsmOki4m/SQNCf/sIy74RnJ6pfI6jaJO9pgqSi+' \
			b'6rIowFsn/rCwPnShojMVlS0Vj7MnkPnhTBHrChFrN8YNClRYOfGDCsl6hAFlBnvMdzSgEMvNWDbCQhItuqV4piDCEKIQwhqtehpUBB/kVjYj6kK1daK2drPqAAy5DtGyGhHJWZXw39NmtrJZ7ffIQukPwbwf/XHvUfl/U9htYTa9Z3g/vNokT18MDf9k2v6w' \
			b'aRbLxg93UIzhasfUDNJCKf8e0jROysWB9QdN27Qx1y4HSa12DLT1CMWpO3zl2sG2b48MyajFpWTx9r6trpqDH6rgREuh73+wtdWBwU03D3hwlHWMMi4u391nMrcnktJ9w0fPjaD3ePT3+vbtB5u/VLGYneJHBl6W6LH9demBDci7B+OY23HCxxrFvSf/vj+B' \
			b'HEDl+3SQzKtm5HrnB7an3Pc3NhycIkpVx82pYBatL8sRthkd2MS97jrzwJ6VeV5ZDb5mjE0ZA1sRL+jg9LBbZf7+sgV2gR7gYCX0NVNszBSmuaSDG5V3axOYXQVcljFsc7cH9r3P88rKaGvm2JQ5sMfpgg5OD6Vq9B1kDjT0ogyCA2bu+sBxKfO8sk7W6tk1' \
			b'j8Q8YppLOjg9lCred5RH0NDL8olt7uPAoVrzvLJqas18c1ZxzSUdnB52q5e7hS3uc3NMsFPKNb6Zf+Bovd0CQLrc7gNHJ4YbVlitwW/OQH1zSQenh91q8EszUG7rxZkJRzLf55EPFZ4dirW4VxPAwv7go8lYLRrLFDKYzzJZGzJao3CE6hscYrf0wH7ufcLf' \
			b'96GgvqPAvEM3XbriYWGrCsqbQBnHYV7Qwelht5EFhwVl1xzZwSpUNUttzFK+uaSD04PeebDOHY7OWZa7CqbDeVuzDxzmvVOA0RGmSO0QgiY4pclNpPndWjOOVvO6OYWDVV4ao32CKjfNKRys8t0aIu5Y5drOVztRxaTqbfPAB9LXYh9sgtKQ+Rk0fzgrrOZY' \
			b'wjU7HTjBZ9cwy44tX2J7LBzpf+T26JpTO9gapcH5J28NnK9+YgfP2dp53sC5zYLBZQZ2P2gVgex/2VvGb1x/d3Y78DP9luxgSx/bLIGHt7RuzvFg6+42nOEcrds153iwdXdvNDg36/bNOR5s3d0bJs7MuricwRkebN3d20DOzbptc44HW9c1b7SmOb8C1T46' \
			b'SO7u0AFVSNNSV7ggLT+AilBuf1A0+QB14x6HLZgAZwLJCHewUtE3zi8d/LPvds03Go9CgOlH/0pz27TNl7PQlBTYHegnT46chPKkI8kGFwgxJBcutJUtsMULWoXFrNpsEStc/kFkNsOv4AomGntuSZv4yfApSpnScGdZy5B432DqhpRJ07U6XBOLn4CFqFcY' \
			b'e4Gx95d6fRVuL+vAFRfG6GRBCZ9W6eAyM24uqUAJ6MJtCbirHLwFXbys5bBKLuDn++v/B1TXtbo='

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

	_STRS     = r"'(?:\\.|[^'])*'"
	_STRD     = r'"(?:\\.|[^"])*"'

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY)))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('UFUNC',        fr'\?'),
		('UFUNCPY',       r'Function'),
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LTRU})|(\${_LTRU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\$?(?:{_LTR}|\\_)(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

		('LIM',          fr'\\lim(?!{_LTR})'),
		('SUM',          fr'\\sum(?:\s*\\limits)?(?!{_LTR})|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?(?!{_LTR})|{_UINTG}'),
		('LEFTDOT',      fr'\\left\s*\.'),
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

		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\ne(?!g)q?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)(?!{_LTRU})|{"|".join (AST.Cmp.UNI2PY)}'),
		('IF',            r'if(?!{_LTRU})'),
		('ELSE',          r'else(?!{_LTRU})'),
		('OR',           fr'or\b|\\vee(?!{_LTRU})|{_UOR}'),
		('AND',          fr'and\b|\\wedge(?!{_LTRU})|{_UAND}'),
		('NOT',          fr'not\b|\\neg(?!{_LTRU})|{_UNOT}'),
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LTRU})'),
		('LOG',           r'log\b|\\log(?!{_LTR})'),
		('LN',            r'ln\b|\\ln(?!{_LTRU})'),

		('NUM',           r'(?:(\d*\.\d+)|(\d+\.?))((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))"),
		('ATTR',         fr'\.\s*(?:({_LTRU}\w*)|\\operatorname\s*{{\s*({_LTR}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"((?<![.'|!)}}\]\w]){_STRS}|{_STRD})|\\text\s*{{\s*({_STRS}|{_STRD})\s*}}"),

		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
		('COLON',         r'{:}|:'),
		('SCOLON',        r';'),
		('CARET1',       fr'\^{_VARTEX1}'),
		('CARET',         r'\^'),
		('DBLSLASH',      r'\\\\'),
		('DBLSTAR',       r'\*\*'),
		('SLASHCURLYL',   r'\\{'),
		('SLASHCURLYR',   r'\\}'),
		('SLASHBRACKL',   r'\\\['),
		('CURLYL',        r'{'),
		('CURLYR',        r'}'),
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('BRACKL',        r'\['),
		('BRACKR',        r'\]'),
		('BAR',           r'\|'),
		('PLUS',          r'\+'),
		('MINUS',         r'-'),
		('STAR',          r'\*'),
		('DIVIDE',        r'/'),
		('EXCL',          r'!'),
		('AMP',           r'&'),
		('COMMA',         r','),
		('PRIME',         r"'"),
		('EQ',            r'='),
		('ignore',        r'\\[,:;]|\\?\s+|\\text\s*{\s*[^}]*\s*}'),
	])

	_PYGREEK_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.GREEK))) + ')'
	_PYMULTI_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.PY2TEXMULTI))) + ')'
	_VARPY_QUICK   = fr'(?:{_PYGREEK_QUICK}|{_LTR})'
	_VAR_QUICK     = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK   = OrderedDict ([ # quick input mode different tokens
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})|(\${_LTRU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LTR}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

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

		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\ne(?!g)q?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)|{"|".join (AST.Cmp.UNI2PY)}'),
		('OR',           fr'or\b|\\vee|{_UOR}'),
		('AND',          fr'and\b|\\wedge|{_UAND}'),
		('NOT',          fr'not\b|\\neg|{_UNOT}'),
		('SQRT',          r'sqrt\b|\\sqrt'),
		('LOG',           r'log\b|\\log'),
		('LN',            r'ln\b|\\ln'),

		('VAR',          fr"(?:(?:(\\partial\s?|partial|{_UPARTIAL})|(d(?!elta)))({_VAR_QUICK})|(None|True|False|{_PYMULTI_QUICK}|{_VAR_QUICK}))"),
	])

	TOKENS_LONG    = OrderedDict () # initialized in __init__()

	_PARSER_TOP             = 'expr_scolon'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	# grammar definition and implementation

	def expr_scolon_1      (self, expr_scolon, SCOLON, expr_commas):                   return expr_scolon if expr_commas == AST.CommaEmpty else AST.flatcat (';', expr_scolon, expr_commas)
	def expr_scolon_2      (self, expr_commas):                                        return expr_commas

	def expr_commas_1      (self, expr_comma, COMMA):                                  return expr_comma if expr_comma.is_comma else AST (',', (expr_comma,))
	def expr_commas_2      (self, expr_comma):                                         return expr_comma
	def expr_commas_3      (self):                                                     return AST.CommaEmpty
	def expr_comma_1       (self, expr_comma, COMMA, expr_colon):                      return _expr_comma (expr_comma, expr_colon)
	def expr_comma_2       (self, expr_colon):                                         return expr_colon

	def expr_colon_1       (self, expr, COLON, expr_colon):                            return _expr_colon (expr, expr_colon)
	def expr_colon_2       (self, expr, COLON):                                        return AST ('-slice', expr, False, None)
	def expr_colon_3       (self, COLON, expr_colon):                                  return _ast_pre_slice (False, expr_colon)
	def expr_colon_4       (self, COLON):                                              return AST ('-slice', False, False, None)
	def expr_colon_5       (self, expr):                                               return expr

	def expr               (self, expr_ass):                                           return expr_ass

	def expr_ass_1         (self, expr_mapsto1, EQ, expr_mapsto2):                     return AST ('=', expr_mapsto1, expr_mapsto2)
	def expr_ass_2         (self, expr_mapsto):                                        return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr_colon):                     return _expr_mapsto (expr_paren.strip, expr_colon)
	def expr_mapsto_2      (self, expr_piece):                                         return expr_piece

	def expr_piece_1       (self, expr_or, IF, expr_ass, ELSE, expr_mapsto):           return _expr_piece (expr_or, expr_ass, expr_mapsto)
	def expr_piece_2       (self, expr_or, IF, expr_ass):                              return AST ('-piece', ((expr_or, expr_ass),))
	def expr_piece_3       (self, expr_or):                                            return expr_or

	def expr_or_1          (self, expr_or, OR, expr_and):                              return AST.flatcat ('-or', expr_or, expr_and)
	def expr_or_2          (self, expr_and):                                           return expr_and

	def expr_and_1         (self, expr_and, AND, expr_not):                            return AST.flatcat ('-and', expr_and, expr_not)
	def expr_and_2         (self, expr_not):                                           return expr_not

	def expr_not_1         (self, NOT, expr_not):                                      return AST ('-not', expr_not)
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
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                      return AST.flatcat ('+', expr_add, AST ('-', expr_mul_exp))
	def expr_add_3         (self, expr_add, SETMINUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, AST ('-', expr_mul_exp))
	def expr_add_4         (self, expr_mul_exp):                                       return expr_mul_exp

	def expr_mul_exp       (self, expr_mul_expr):                                      return expr_mul_expr
	def expr_mul_expr_1    (self, expr_mul_expr, CDOT, expr_neg):                      return AST.flatcat ('mulexp', expr_mul_expr, expr_neg)
	def expr_mul_expr_2    (self, expr_mul_expr, STAR, expr_neg):                      return AST.flatcat ('mulexp', expr_mul_expr, expr_neg)
	def expr_mul_expr_3    (self, expr_neg):                                           return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                    return _expr_neg (expr_neg)
	def expr_neg_2         (self, expr_diff):                                          return expr_diff

	def expr_diff          (self, expr_div):                                           return _expr_diff (expr_div)

	def expr_div_1         (self, expr_div, DIVIDE, expr_divm):                        return AST ('/', expr_div, expr_divm)
	def expr_div_2         (self, expr_mul_imp):                                       return expr_mul_imp
	def expr_divm_1        (self, MINUS, expr_divm):                                   return _expr_neg (expr_divm)
	def expr_divm_2        (self, expr_mul_imp):                                       return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                            return _expr_mul_imp (expr_mul_imp, expr_intg, self._USER_FUNCS)
	def expr_mul_imp_2     (self, expr_intg):                                          return expr_intg

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add):               return _expr_intg (expr_add, (expr_sub, expr_super))
	def expr_intg_2        (self, INTG, expr_add):                                     return _expr_intg (expr_add)
	def expr_intg_3        (self, expr_lim):                                           return expr_lim

	def expr_lim_1         (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                          return AST ('-lim', expr_neg, expr_var, expr)
	def expr_lim_2         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):  return AST ('-lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg): return AST ('-lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                        return expr_sum

	def expr_sum_1         (self, SUM, SUB, CURLYL, varass, CURLYR, expr_super, expr_neg):                          return AST ('-sum', expr_neg, varass [0], varass [1], expr_super)
	def expr_sum_2         (self, expr_diffp):                                                                      return expr_diffp

	def expr_diffp_1       (self, expr_diffp, PRIME):                                  return AST ('-diffp', expr_diffp.diffp, expr_diffp.count + 1) if expr_diffp.is_diffp else AST ('-diffp', expr_diffp, 1)
	def expr_diffp_2       (self, expr_func):                                          return expr_func

	def expr_func_1        (self, SQRT, expr_neg_arg):                                 return _expr_func (1, '-sqrt', expr_neg_arg)
	def expr_func_2        (self, SQRT, expr_super, expr_neg_arg):                     return AST ('^', _expr_func (1, '-sqrt', expr_neg_arg), expr_super)
	def expr_func_3        (self, SQRT, BRACKL, expr_commas, BRACKR, expr_neg_arg):    return _expr_func (1, '-sqrt', expr_neg_arg, expr_commas)
	def expr_func_4        (self, LN, expr_neg_arg):                                   return _expr_func (1, '-log', expr_neg_arg)
	def expr_func_5        (self, LN, expr_super, expr_neg_arg):                       return AST ('^', _expr_func (1, '-log', expr_neg_arg), expr_super)
	def expr_func_6        (self, LOG, expr_neg_arg):                                  return _expr_func (1, '-log', expr_neg_arg)
	def expr_func_7        (self, LOG, expr_super, expr_neg_arg):                      return AST ('^', _expr_func (1, '-log', expr_neg_arg), expr_super)
	def expr_func_8        (self, LOG, expr_sub, expr_neg_arg):                        return _expr_func (1, '-log', expr_neg_arg, expr_sub)
	def expr_func_9        (self, FUNC, expr_neg_arg):                                 return _expr_func_func (FUNC, expr_neg_arg)
	def expr_func_10       (self, FUNC, expr_super, expr_neg_arg):                     return _expr_func_func (FUNC, expr_neg_arg, expr_super)
	def expr_func_11       (self, expr_pow):                                           return expr_pow

	def expr_func_12       (self, SQRT, EQ, expr_mapsto):                              return AST ('=', ('@', 'sqrt'), expr_mapsto) # allow usage of function names in keyword arguments
	def expr_func_13       (self, LN, EQ, expr_mapsto):                                return AST ('=', ('@', 'ln'), expr_mapsto)
	def expr_func_14       (self, LOG, EQ, expr_mapsto):                               return AST ('=', ('@', 'log'), expr_mapsto)
	def expr_func_15       (self, FUNC, EQ, expr_mapsto):                              return AST ('=', ('@', _FUNC_name (FUNC)), expr_mapsto)

	def expr_pow_1         (self, expr_pow, expr_super):                               return AST ('^', expr_pow, expr_super)
	def expr_pow_2         (self, expr_fact):                                          return expr_fact

	def expr_fact_1        (self, expr_fact, EXCL):                                    return AST ('!', expr_fact)
	def expr_fact_2        (self, expr_attr):                                          return expr_attr

	def expr_attr_1        (self, expr_attr, ATTR):                                    return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1].replace ('\\', ''))
	def expr_attr_2        (self, expr_abs):                                           return expr_abs

	def expr_abs_1         (self, LEFT, BAR1, expr_commas, RIGHT, BAR2):               return AST ('|', expr_commas)
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                            return AST ('|', expr_commas)
	def expr_abs_3         (self, expr_paren):                                         return expr_paren

	def expr_paren_1       (self, expr_pcommas):                                       return AST ('(', expr_pcommas)
	def expr_paren_2       (self, expr_frac):                                          return expr_frac

	def expr_frac_1        (self, FRAC, expr_binom1, expr_binom2):                     return AST ('/', expr_binom1.no_curlys, expr_binom2.no_curlys)
	def expr_frac_2        (self, FRAC1, expr_binom):                                  return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_binom.no_curlys)
	def expr_frac_3        (self, FRAC2):                                              return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4        (self, expr_binom):                                         return expr_binom

	def expr_binom_1       (self, BINOM, expr_subs1, expr_subs2):                      return AST ('-func', 'binomial', (expr_subs1.no_curlys, expr_subs2.no_curlys))
	def expr_binom_2       (self, BINOM1, expr_subs):                                  return AST ('-func', 'binomial', (_ast_from_tok_digit_or_var (BINOM1), expr_subs.no_curlys))
	def expr_binom_3       (self, BINOM2):                                             return AST ('-func', 'binomial', (_ast_from_tok_digit_or_var (BINOM2), _ast_from_tok_digit_or_var (BINOM2, 3)))
	def expr_binom_4       (self, expr_subs):                                          return expr_subs

	def expr_subs_1        (self, LEFTDOT, expr_commas, RIGHT, BAR, SUB, CURLYL, subsvars, CURLYR): return _expr_subs (expr_commas, subsvars)
	def expr_subs_2        (self, expr_cases):                                         return expr_cases
	def subsvars_1         (self, SUBSTACK, CURLYL, subsvarss, CURLYR):                return subsvarss
	def subsvars_2         (self, varass):                                             return (varass,)
	def subsvarss_1        (self, subsvarsv, DBLSLASH):                                return subsvarsv
	def subsvarss_2        (self, subsvarsv):                                          return subsvarsv
	def subsvarsv_1        (self, subsvarsv, DBLSLASH, varass):                        return subsvarsv + (varass,)
	def subsvarsv_2        (self, varass):                                             return (varass,)

	def expr_cases_1       (self, BEG_CASES, casess, END_CASES):                       return AST ('-piece', casess)
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
	def expr_curly_2       (self, SLASHCURLYL, expr_commas, CURLYR):                   return AST ('-set', expr_commas.comma) if expr_commas.is_comma else AST ('-set', (expr_commas,))
	def expr_curly_3       (self, CURLYL, expr_commas, CURLYR):                        return _expr_curly (expr_commas)
	def expr_curly_4       (self, expr_ufunc):                                         return expr_ufunc

	def expr_ufunc_1       (self, UFUNCPY, expr_pcommas1, expr_pcommas2):              return _expr_ufunc (expr_pcommas1, expr_pcommas2)
	def expr_ufunc_2       (self, UFUNC, expr_var, expr_pcommas):                      return _expr_ufunc (expr_pcommas, name = expr_var.var)
	def expr_ufunc_3       (self, UFUNC, expr_pcommas):                                return _expr_ufunc (expr_pcommas)
	def expr_ufunc_4       (self, expr_term):                                          return expr_term

	def expr_term_1        (self, expr_num):                                           return expr_num
	def expr_term_2        (self, expr_var):                                           return expr_var
	def expr_term_3        (self, STR):                                                return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1].replace ('\\}', '}')))
	def expr_term_4        (self, SUB):                                                return AST ('@', '_') # for last expression variable
	def expr_term_5        (self, EMPTYSET):                                           return AST.SetEmpty

	def expr_num           (self, NUM):                                                return _expr_num (NUM)
	def expr_var           (self, VAR):                                                return _expr_var (VAR)

	def expr_sub_1         (self, SUB, expr_frac):                                     return expr_frac
	def expr_sub_2         (self, SUB1):                                               return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1       (self, DBLSTAR, expr_neg_arg):                              return expr_neg_arg
	def expr_super_3       (self, CARET, expr_frac):                                   return expr_frac
	def expr_super_4       (self, CARET1):                                             return _ast_from_tok_digit_or_var (CARET1)

	def expr_neg_arg_1     (self, MINUS, expr_neg_arg):                                return _expr_neg (expr_neg_arg)
	def expr_neg_arg_2     (self, expr_diffp):                                         return expr_diffp

	def expr_pcommas_1     (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):           return expr_commas
	def expr_pcommas_2     (self, PARENL, expr_commas, PARENR):                        return expr_commas

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
			if rule == ('expr_func', ('FUNC', 'expr_neg_arg')):
				return self._insert_symbol (('PARENL', 'PARENR'))

			if rule == ('expr_paren', ('PARENL', 'expr_commas', 'PARENR')) and self.stack [-2].sym == 'expr_mul_imp' and \
					(self.stack [-2].red.is_attr or (self.stack [-2].red.is_var and self.stack [-2].red.var in self._USER_FUNCS)):
				return self._insert_symbol ('PARENR')

		if pos and rule [1] [pos - 1] == 'expr_commas' and rule [0] not in {'expr_abs', 'varass', 'expr_func'}: # {'expr_abs', 'expr_ufunc', 'varass'}:
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
		def postprocess (res):
			return (AST_MulExp.to_mul (res [0].no_curlys).flat,) + res [1:] if isinstance (res [0], AST) else res

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
				res = postprocess (res [-1])
				print ('parse:', res, file = sys.stderr)

			if len (rated) > 32:
				print (f'... total {len (rated)}', file = sys.stderr)

			print (file = sys.stderr)

		res = next (iter (rated)) [-1]

		return postprocess (res)

class sparser: # for single script
	Parser = Parser

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: # DEBUG!
# 	p = Parser ()

# 	# p.set_quick (True)
# 	# print (p.tokenize (r"""{\partial x : Sum (\left|\left|dz\right|\right|, (x, lambda x, y, z: 1e100 : \partial !, {\emptyset&&0&&None} / {-1.0 : a,"str" : False,1e100 : True})),.1 : \sqrt[\partial ' if \frac1xyzd]Sum (\fracpartialx1, (x, xyzd / "str", Sum (-1, (x, partialx, \partial ))))}'''"""))

# 	p.set_user_funcs ({'N'})

# 	a = p.parse (r"N (x)'")
# 	print (a)

# 	# a = sym.ast2spt (a)
# 	# print (a)
