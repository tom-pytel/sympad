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

def _expr_ufunc (UFUNC, args, argspy = None):
	name, kw = None, None

	if argspy:
		name, kw = AST.args2kwargs (args.comma if args.is_comma else (args,))

		if len (name) != 1 or not name [0].is_str:
			raise SyntaxError ('Function() takes a single string name argument')

		args = argspy

	args, kw2 = AST.args2kwargs (args.comma if args.is_comma else (args,))

	if any (not a.is_var for a in args):
		raise SyntaxError ('undefined functions only take variables')

	if kw is None:
		kw = kw2
	elif kw2:
		raise SyntaxError ('keyword arguments not allowed here')

	return AST ('ufunc', name [0].str_ if name else UFUNC.grp [0] or UFUNC.grp [1] or '', tuple (a.var for a in args), tuple (sorted (kw.items ())))

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
			b'eJztfW2P3DaW7p+5wLgBNVDimyR/cxxn1ljbycbOYAdGEDgezyLYJA7sJHcvBve/L88LyUNKqpbU1VXV1USrSxJFSYfnkM9D8pDio7d/+T8ffv3HX5q/PP36xdev/P7Fs6/e+N03T7599uqFP/jq2ydPedfyXvn9F89fff0y7NtwoPgBX34Nz3iFv188++sP' \
			b'T5+8fvaaj18+CaFfpMO/pcNv6PD1iyev/+0L/7Z/ByniAQY//e7bF3+Hs3jw3VffvXr6zd/DEUR88y38fveF/3328ps3f3/9DGX6DqT+2xO4+PL5q+9Aquev3vwVBH/+Eu/A3//4FmK/QI18DVf5sV/gnU+/fvnySdASBHz7/K//9iYI9G0QGA6+/OIFygxi' \
			b'/If/efLyGzh89SUrAo6+SId/S4esiGcvXj+D5zz/2/Mv4eApKff1G5TkmxeYBJ+4kJr/fP3sKUb48vlXX4FCXj1Hwz7FFz959SWkGC58/S2/KFgHRKWnPvXpehP2YN2XT755/eZruP8N6vXZfz4FtWOQ13GbWYYV75/19N/94ec/fvz857tPn/8Ux5/98ft3' \
			b'nz78/sPHTz/848efP//+7pO47A/97h1G+/A/v/koP/35Szj+/MdvHz6Fk18//NcP//zj1/fp4o/+8Jd3v//w/uPPfPTp4/9NR/Tmzx8+f34fj36LR+Ex735Mh7//Ht/2z3fvfw/Hv+FTKTgTIAr680/x8Kdff/+vcPzLHz//8NMvv4mkpcN//lMkLBz++S4l' \
			b'Nz0dHgMH4fz3D5/Ka+H0Dyngu3/8Ixy+/+PTz/8vnPzP5w8pcT9+evf+vz/E089Ssj8/xGf98etPH3+NL30X479PyUO9RvE/pkf+IVT8axTpx59+/RiT8TEp3ssTFf/Th/cf4onPREKC3z7//jE+NZozyvLx5yTu+4+//PIuO/n8l++bt4+urW2cvmrowMCB' \
			b'0fBjGqOu+NSf4ZGFn8ZfujZXWQCdmXCfv25DEBxirGvaq+aRarRrrttGD/7gKoRyWAy47uBAGfqxXgpF10KQ6kdB1sggOPRHraIfO/gXkKj+DA4h1f7fNZBGus3CAQjQ0o/rrvjUy4S3+gudv1vD/1UI6eXZwHsIAklaSHLbc5JNexVCKSwFXCu8ofVCgYRe' \
			b'Kkc28CHXLeqjdfRj4db+ioPg0B+h4Rr/HBKFT8OxCG9pd40qUPivu3BZwQE8l8PpJV44DqRIGhM1cKK6NoZSmNmlaLs84FphTtDwHnyR1vRjfURLCfZn15oMBBmmjxesChfMjn4cacEfeSvB0dA88rZH/ZNUPsCKE0c7CIA39T7r+Ydaki+etmVQMFYersen' \
			b'RQwzPh3HMEMeZMen2U3XehCipezLQhQBpgywMsDnNjWwCGBmkwWn02uNmvPl9JHeNVAAvcr9kYObG9C/5rw2HQMQxhfjZRG9yfOI1xrzP2T/rnEuZFZ/gFm/7biQQcE0vkRbUdbgYgxPIYZCXAqxFNKlEEchfQi5blHxyocrfLEXFH9AdSxtDFIyCA4hKYZ+' \
			b'vEavrtIhHLWU00Oa4YFY5ny5oCJA5odioinR/lmYzxnVINujjbzhGPt29OMgFmPJDg9RjwDFAYkpiT6MQsLpNaa358dACW0gp5DSZDAH+HOUfqAfn6Wu+NwXUZRtRz8WVEgigfUViuQf/QiQe7jisw7vaQFXdpEzQo6xJsAKwjFpEVLQxhiU34RxEOdQez7w' \
			b'kUvlF0/jq/2Zw+cpH18N4Ujv+IiQGg5MOKDoUGxa1mrfSF3iJdWMVM7hRVT/SExYTz8WxOC09ngIafFlh2J5tWHmjDkeSi7mN6Xox9pYlv3ZNYltevoRlN4zK5iOfpDNGWI7PIQjFy5e8ak/CxdIfz5rdops4IKVgJ4tVTbgATY+APKCxQfYLlzAqBwU7tKU' \
			b'aAAvn05ff3m7A0Q2CIFQ3neNL08eq3we8Yb2BhiAo7wUfdv0Hh92ng931v87/9/5fw8YuwGU40XwL7JwDvG0tzBmIg9FPm6H0OLRoPWHg3/ozr/Jb95i3nK66f1mmt42vWv6rukBh/xj/JXWS9NquNGf+2wKOaVvfAFtvYCtRt17sELYAfDyhdjDELzJR2sx' \
			b'3s7/e/H9oZep9UK1XqoWxPIPG3bN4KscIHPr45lmsM0AiAXF1EPFoJvBNJ3fbNO5puuarm+6oen9UzFNA1SMHEKEU74u6GuBPusDxDoPtD1gcrfzBN94c3b+/S3c2AKSe3P6rK7g1T7IS/N982gHdYu3j7xRIPd5w8DOW6b11npk+Ko2FGxp1+PVt1ADxPMO' \
			b'dtWOJ7XjQJZqcQ9VODJRT3YFHYBBe8XRdmTRnqqWqiPrU2AbbkaLXdUCe1aGRs2SDTs2V8/7gfeK7WfRfJmaWcGk2Smdki6jDjPdFfqaUhbryMtpexLTulMK0QVdUUaHbIaqUXh+REkUW02ZY7+YQLtlc+Cba5k+qzINVqlGOTOjPGpDkTW1xJyfcVpG9gFJ' \
			b'L6gKlRRVwqoIGpCp9qmMKTphSrKcInPHafgSiHJHdfpQh9B47lvljX9X41NZs/qRs7puuRHGVZhoGtVXXDozY/kGF9XvDKTEH/qktdC2hoY1tKq9hapJjm0SW01ybiZx1STnZpKumuSsTPKoD032wPxtYP5W1465szNXq0PHXBtqatTbBG5ZNiT31PF17m61' \
			b'bFVTjXp2RjXcx8qmHdBEtcEYexdbFUBKce+zJu/Boza0W3q6MFDDcmj5suJCoLgUhH5K9kUMijuz2YHBLqgh9MlQSTJD6Ormp+NDH6YpBkOq6UhTHdV6ofxBAax9Hzfpr+Os1VEG7CiHdewK7XfMwQzhLWO6pdzt6LKj3Nrh2eDRDATwJwperi5Wd28fOSqu' \
			b'jgp11z649FOhcwRijhzjnZpWQyiUF6wOKkOOy5B+cNmByRBd6TLN5OwhlLA6kBdlHsXUqFQck6FoMIaqwytO3Tz2EigaAlONcepKORRSHuzi91Xrx+ohamveP70VQMWqdhOcmVW8JhQNpKu2OTfbmFpgzs8o/rga5byMguN9VRhaqnhoqd9XKxy5aCjUOmqs' \
			b'jmw6UJPcYt4+1dsnBtrD8OTQkMHiVk19IGUrrIwdc4w1dQ7AG2mPO0NnwxBAlT0as1MvvueJGtDdQBBQM8FWk+gdaZ20zC4R7srnnnvqoowuddJ41fTqzI91BBj4RtncBO82O/ZMG1TMs8vaML2spfllMEALn0Dlpe/4QS2XgWqJhZZodai/6Y5UV1V2E1e0' \
			b'yBVVOzPaMVU7e7Rjq3ZmwcgQqA8BkogmaoP/jJqaOGiHCaN2x5ybdd7CkClVR5tJxB3aqpFcIwZLsG3h4zUPWBEw8k/x6Dc1GnHRERfNjLttQwBN+DyDxOCIPR6LpmgsmqKxaArbTS2dW0ZvRziB42su1cBvYWwdutj6Okr67Jiq29WRGMesGHRpQN2lFvhH' \
			b'Qx9Glu8uP7WQzPZc2EfxYF7F9KIfAr10bYWw47U8HfcWO/sQ8pZzDyGVnaol6IgliN0krn8QeUvXvHXMr+vsqIHJoxrjRAT4qie0ta7ws9Gw8ybR7NXWVzTQQZM3sM4mPyubeok0DTQge/HOktlA55pHfOmrMApJp0/mwfgZPoWdIjOD4mlPD3f0NM238qdq' \
			b'wBlP4dSNgT1W9UtCx283UjcYVUaq7o88qi8UivAtVtUHpNRh3ITi8RLou68weSI7DbV8nOBjJ0QvPfFJ33GhaAOTdOGrAoGwNBPWVJ8+hGoK1RSK7MQMRgWPPlmga1fyeeWDluoK4PvU9LkITd95QJNZ6iN76N4urwj10L93ga4+XQe5LenQbbm3rSPM7Kjm' \
			b'0Q2kP+p+bjGwhYyFNzmuszsqgTh853v8tAWWS54gona8pyaiI9zt6B5HgOsI0zuCcscv17HdaLjdaMIoUmqtGGqtGGqtmNBKMbUb4HjdAA7VT7kmEK/hFn8cxcv9ApBGNBbkVf4SEOxtGz3zZt4J35HBO3pGB49gTzfeRHiHudFchbrzZXd6YdmwXDZsaClQ' \
			b'2bBUNiyVDdpRKMhnw4A7W2s3Z1aivMSWkdhSdreU3W1tcpzgq/uo/vLzLFbVsZBnZivAfUuTplxYxcJB/7IXFtIXay2QOsck5LigOSpojgoa3NZE87s6mlAyjqU6mn9Jx1yCe1oB4VEbvoboH9qxcruqwKxNgpqBfNZh/YXm+MVPxwWt9lSTwp7YFr5lCB8y' \
			b'hG8YQgM3Zmavup7ybk/P7NkYXBHr2SoDV6V2XCGjVjIKM1TzZOYZqkbyEm8cN60MjSmFXKRkOxC+g7ij7Id7iEAeol3zdoerIxr05sD6EAMmUSPVILdB+1Bh4hzIqsP0ZiJVIliWvgOL+NeS2qRuJrTvQO+g9JHJPCODQR1yKZIuJB4UgaxpkBzJMRnIA8od' \
			b'0CMc+2vwSUf4niN8zBG+awgfNYQPusFXHeHLhvBZPzAzfGgTPhoJH4wELYGGoDIAM3vB/wlf1AZrAcPC10/h06dAqNBpAx/rhI/JejmVl1N5gyiY9g8f9/EVBwVTiGH+IzA7tN5hqhHMLoaZ4qBWqH2gbn08mPUHuQEm/YHzwGtVwTdPYAYOQIyBtS4hb/n7' \
			b'YEwXjEaB0U4wXgOGS0Obu7feorR0NKwfiSuWNrj2JixMiSuQNtc9rMK8g9WLd7BQKKxwCmtY7nCp5wYXwcRFd+EE8u81mIDWRfVRelxzGZdhxutwF6zqCy+ClSpbCIXIPYQqiKhggVR8rAJJ8PW4TDMs+wlrWOIiq/7Yn3ewsiwICktpOlwuuMUVR3H5TFgG' \
			b'mJbExfUtcbXpYaBkeTtce5tcd5Zlh4WnB0yIv+rg38d2IGJLS5Ti2s+wQioIAu/rQaod3L/DFVUVromL689iQlpclZaWUAYZ4cAXh2uv+mtfsq97EB5fAGkEQaEaR6ukwitgnVuQEtLa8tK/IJc/7yAM4pKV/FVYI7WDPayN7R/cQUz/sg51z6urdoYkADzC' \
			b'lVJhSVFIHtRfr2n5WUgYmgHioWXBRj67X3fwuOF7gAMAgQwA2nkMCABHwJXAwAQ8aHNIcIdEhQJHJ0ACEbKbAIvdAsA4Dli0Q39HgKHHoAFzS2AIyCLwsKBmW+KFXYIYtuGSZydwwybksFPYYe8ePVA+7XBPf1MYguEljthFSHJUFLlDHOknsARfuBBPmn+Z' \
			b'x0A89jFQT7/zO/v/sQI9CzKxWUtNaWyUU5VrDDjg7xON66JJvx+CoKrYLgYiK7AoVAsnK5jUf1BW8aIbA2umVF2NSAVLWUL/AqQYvkItPywsUaysB0ZEs4RqPMAgjsvKxmox0k01TeCztYh+Ph4s7jmLgnYFEvo4sFRthoj+flgnZjMyakZHnwN2bj1KQp5Z' \
			b'hZRtgZa7hJgwWDNDTX8NPqcZ0bOlGhfscgClYsQIChjmH407xlE49hkcd4Sm0NTYEQLhvqX6/jVloIirFC1uEWTxnhHKQijDLDYe1Ca4xQCwGewl5OIzxf8IgllI7Uq5w9aSVlw8FOhcPj17E2Sf+IwUSjiOqQDctEHGEBNgPbwqoDvHAJBPD0O8D4dzsE9W' \
			b'Xor8wcIC/4MRF7MA5rREA1niwV+4nhNIpEQLnOlmaCFlvMANGD/wA8shOCJKF7mCWMLpx8DiRBaAcI8x6/ui/xi4zRfbx15JwCJ6xCK7FbXV25LH7uj8QeQRmKNdwR7ulgxS2YPYQx+TQVpikLZkENBGu6QaDmWhZeJomTgCb7SJN9psS7zRTvJGm3ijjXWT' \
			b'LdTBzFEShxRlRBoUrF0pdLrFUlqZLHpDfDEZFXJKixklD5Y1/sgVWYye9coswcIaKXkXtT/HEKvaBuFhkiHYXMsZos0Zok0ibqKHFjN5ThF7GSJpJzCEJIgRP1DcvewwQQpme//FbRnhdFxQWxEX2oowxAFm1IowiwjAUEQgAMMEYJgATCIAk22JAMwkAZhE' \
			b'AGYT8BsC/qKTJhNhBPwUrF0pbLrFkjyylTAZD/JFGUSITypivM+uC00y5LOYmcxdjDUH+WYV5PPDJOSzgZZDvskh3yQRN0G+KeDe7IP7pJkA90bAvSnhnrPE1saArbhfcf9icN8R7rsR7rtFuO8oouI95A3HuO8S7rtsS7jvJnHfJdzf1lfkCPddgftShBHu' \
			b'U7B2pbDpFks7ifuT8QY7DmLcl/X87LrQJOM+i2mkzF2MNYf7bhXuBwUL3GcDLcd9l+O+SyJuwn1X4L7bh/tJMwH3ncB9V+I+xd2M+67ifsX9i8H9jnB/NEyDnKg34n5HEWkkKuE+e1/xyYz7XbYl3O8mcb9LuL+to6cj3O8K3JcijHCfgrUrhU23WJJH4v5k' \
			b'vMGOgxj3O4H72XWhScZ9FtNImePRLO53q3CfHyZxnw20HPe7HPeFiJtwvytwv9uH+0kzAfc7gftdifsUdzPud0tdyJeA/m0lgAdCAAMRwDAigEEQQEscgLspGqAYSAMD08DANDAkGhiyLdHAMEkDQ6KBYRMNDEQDQ0EDUoQRDVCwdqWw2V2WRJJMMBkPM0gR' \
			b'xEwwCCbIrgtlMhOwpEaK3cVYc0wwrGICfphkArbRciYYciYYkoibmKDs6B/2MUHSTGACMVKIhJBMQNc3M0FfmaAywcUxgSL3rxq5f5X0/cKJpVhTTABSswdYsQdYsQdYJQ8wxYpbZAI16QFWyQNMEdYygSLPryo8v5kIJRNwsHalsNldlkQSTDAdD9awKIOI' \
			b'CUhLxAT5daFMYoIgqZFidzHWDBOoVW7f8DDBBMFGi5lA5W7fJOw2JiB5EhOofS5foRlmAiVcvqp0+XLczUwwVCaoTHB5TKCICdSICeT0HUVDSZWaYQKODlldMRMoZgKVmEBlW2ICNckEKjGB2sQEiphAFUwgRRgxAQVrVwqb3WVJJMkEk/GACcogZgIxUjS/' \
			b'LpTJTMCSGil2F2PNMYFaxQT8MMkEbKPlTKByJlBJxE1MoAomUPuYIGkmMIESTKBKJqC4m5mg3Z3HDIM6vaBywp1wAg0MUqOBQUoODIITS7ECJ8Ax5G6TmMHQTRyKzMCDhFQaJESx4paYYXKQkEqDhNSmQUKKBgmpYpBQJsKIGShYu1LY7C4bLmfkMBkVyKEM' \
			b'YnIQQ4Xy60KfTA4sbCZ5F2PNkcOqoULhYZIc2EzLySEfKpSE3UgOxVAhtW+okNBMIAcxVEiVQ4U47nZywDmulkawItx3CPRtie+A7C4g7xzsCgiN8Dgw7DmCtQhXDFFYhchgAIr00Jx0w8m/ZzIxr9Jmpc27oE1NnWp61KmmZaeapk41LTrV4NjnbtwRbULm' \
			b'5q41zV1rmrvWdOpao1hxi7SpJ7vWdOpa05u61jR1remiay0ToaRNDtauFDa7y4bLkjano/qcMgoi2tSidy2/LvRJtBmENVLyLsaaoU29qnctPEzQZjDTYtrUee9aEnYbbeqid03v610TmmHa1KJ3TZe9axx3O22O59tVcqjkcDnkYIkcRt+80PKjF3BiKVYk' \
			b'B0vkYBM5WLqJQ5EcLJODTeRgsy2Rw+R3MXT6MAZFWE0OlsjBFuQgRRiRAwVrl+JApiolt+F6xg6jeCjBRBCzgxXskF0XCmV2YGmNFL2LsebYwa5iB36YZAe203J2sDk72CTiJnawBTvYfeyQNBPYwQp2sCU7UNzt7LBn4l1lh8oO954daEqGHk3J0HJKBn6O' \
			b'jGJFdnDEDskXo+ms5VBkB56eodP0DIoVt8QOk9MzdJqeoTdNz9A0PUMX0zMyEUbsQMGFpKXgNh5JcpiMOthxEJODmKSRXxf6ZHJgYY2UvIux5shh1SSN8DBJDmym5eSQT9JIwm4kh2KSht43SUNoJpCDmKShy0kaHHc7OeyZnVfJoZLDvScHmrcx/rymlvM2' \
			b'4MRSrEgOHZFDl8iho5s4FMmB53DoNIeDYsUtkcPkHA6d5nDoTXM4NM3h0MUcjkyEETlQMJfOmQ3JgY4kOUxGBXIog5gcxEyO/LrQJ5MDC2uk5PFolhxWzeQID5PkwGZaTg75TA4tRNxEDsVMDr1vJofQTCAHMZNDlzM5OO52ctgzha+SQyWHe08OPZFDPyKH' \
			b'XpJDT+QgpvbBMdBAn8iBIrQciuTQMzn0iRz6bEvk0E+SQ/pcM0VYTQ49kUNfkIMUYUQOFKxdKWx2lw2XM3KYjArkUAYxOfSCHLLrQp9MDiyskZJ3MdYcOfSryIEfJsmBzbScHPqcHFJCtpFDX5DDvs+/Cs0EcugFOZRfguW428lh8Ty/Sg6VHO4fORjySJuR' \
			b'R9pIj7Qhj7QRHmlDHmmTPNKQfdkjbdgjbdgjbZJHmmLFLZKDmfRIm+SRNps80oY80qbwSGcilOTAwdqVwmZ32XBZksN0VJ9TRkFEDkZ4pPPrQp9EDkFYIyXvYqwZcjCrPNLhYYIcgpkWk4PJPdJJ2G3kYAqPtNnnkRaaYXIwwiNtSo80x91ODuOpf7uHwQ9q' \
			b'giLaShMXSxOaxvvq0XhfWGZbDvnVNORXiyG/mob86jTkF3I3D/nVPORX85BfnYb8Uqy4pWbE5JBfnYb86k1DfjUN+dXFkN+W1+qjK6N2BAVrV0ort5491BSX2aK31JqYugFbE2UQtybEyN/8ulArtyZYZBnLdTHWXGti1cjf8DDZmmBrLW9N5CN/k7AbWxPF' \
			b'yF+9b+Sv0ExoTYiRv7oc+ctxtxPGeIZgJYxKGBdIGIbc1WbkrvYaMNJjbchjbYTH2pDH2iSPteGbOBSbFuyxNsljTbHilpoWkx5rkzzWZpPH2pDH2hQe60yEUdOCgrUrhZVbT05rjhv4wlEDY+oGbGCUQdzAEH7r/LrQKjcwWGQj5e9irLkGxiq/dXiYbGCw' \
			b'sZY3MHK/dRJ2YwOj8FubfX5roZnQwBB+a1P6rTnuZr5QdRrhQXuf/PN8kitbHJot+hsYwyydVkh+bDXyYyvpx1bkx1bCj63Ij62SHxvkZz+2Yj+2Yj+2Sn5sihW3NK1w0o+tkh9726ITivzYqvBjZyKMphVSsHalsNldNlzOphVORh3sOIinFbIfW8GcOIBz' \
			b'W8g2CL3y9EIW2sgUxKPZ6YWr/NnhYXJ6IZtr+fTC3J+thIhbSEMV/my1z5+trJPaYeJQ5NNWXZhmWPq1Of528tizlGYlj9rEODVp3LaJAUtteqPgipsZWdidIAs4sRQrkAUcw+Kgu0gWsJjWjsgC9z5t9BAKZ7KgWHFLy4jupsgCQpksKMJasuClRGEnySIT' \
			b'YbSyKAvsSmGzu2y4LMliOiqsQ1oGEVmQoqhlkV8X+iSSCMIaKXkXY82QBFlgKUmEhwmSCGZaTBIofSKJJOw2kiB5EklQgmZIQmiGCQJlZ3IgIQQ5cNzt5FBnWldyuGRyIL+2Hfm1rfRrW/JrW+HXtuTXtsmvDcsssl/bsl/bsl/bJr82xYpbIodJv7ZNfm27' \
			b'ya9tya9tC792JsKIHChYu1LY7C4bLmfkMBkVyKEMYnIQfu38utAnkwMLa6TkXYw1Rw6r/NrhYZIc2EzLySH3aydhN5JD4de2+/zaQjOBHIRf25Z+bY67nRzqTOtKDpdMDuScsCPnhJWeCUueCSs8E5Y8EzZ5JiydtRyK5MCeCZs8ExQrbokcJj0TNnkm7CbP' \
			b'hCXPhC08E5kII3KgYO1KYbO70pEkh8mogx0HMTkIn0R+XeiTyYGFNVLyLsaaI4dVPonwMEkObKbl5JD7JJKwG8mh8EnYfT4JoZlADsInYUufBMfdTg73caJ1B/zgs3yliPtNEZBvjkYTimhCjWhCSZpQRBNK0IQimpCfv6WzNuwhfUwTKtEEXY1b8kZM0oRK' \
			b'NKE20YQimmh5yBO+AQxPM6wGlgIuqwnCYBm1K8XOkmDjkfRLTEYd7DiI/RKCMPLrQrPsj6BT9DjFky7GmvNHrCKM8DDpj2CDLfdH5ISRhN3oj3Dohct9EvtIQ2gn+CMEaaiSNDjudtKoE7ArXVxyi4Ic13bkuLbScW3JcW2F49qS49omxzVkSnZcW3ZcW3Zc' \
			b'2+S4plhxSy2KSce1TY5ru8lxbclxbQvHdSbCqEVBwdqVwmZ32XA5a1FMRoUWRRnELYpOtCiy60Kf3KJgYY2UPB7NtihWOazDw2SLgs20vEWRO6ytEHFTi6JwWNt9DmuhmdCi6ESLonRUc9zt5FAnYFdyuGRyGIgchhE5DJIcBiKHQZDDQOQwJHKgeC2HIjkM' \
			b'TA5DIoch2xI5DJPkMCRyGDaRw0DkMBTkIEUYkQMFa1cKm91lw+WMHCajAjmUQUwOgyCH7LrQJ5MDC2uk5F2MNUcOwypy4IdJcmAzLSeHISeHIYm4iRyGghyGfeSQNBPIYRDkMJTkQNe3k0OdgF3J4ZbkQKMZj0sS7gai0AVZaEEYjkY2udHIJidHNjka2eTE' \
			b'yCZHI5tcGtkE+ZNHNjke2eR4ZJNLI5soVtwiYbjJkU0ujWxym0Y2ORrZ5IqRTZkIJWFwsHalsNldNlyWhDEd1eeeURARhhMjm/LrQp9EGEFYIyXvYqwZwnCrRjaFhwnCCGZaTBguH9mUhAXCCHKvpQ1XjG9y+8Y3Cf2wAhRl4cAcTg5xQlnkTdv5Y8/yrLa5' \
			b'nOX4jr8W3yUyxYmbEQ7CYGj47qbpddSkMKMmhZFNCqCHydX4YNoUNyMMNyMMNyNMakZQrLil+XRlMwLylUmtCLOpFXHN411N0YygTJf+x3PqSDrtSoGT5JaEkh/qmIwH8+jEOeQPIIVW8fivSAsgCMVBkWCdbtjHVbrpMi7TbcRpFw9np9OtaksEO8rpdGyr' \
			b'KWqgdBSz6fKmBCbZBhk3zacTjQkEHFTM7IS6qPs4oU60JnCmBqjd31i0K/iugheM3wFqRWLwPIELrKvHyIu+lD6m5aASQexZtfUMCeLEpNALMtCCBAIBBOC/L6B/zv1GULigum1HzQC7BOQh21iu+luu+luu+ttU9bfZlqr+drLqb1PV326q+luq+tsc5MfV' \
			b'fZJGu1LAJKklGWRFfzLeMBFEFX3CdChwHCy+xYfIRoI6Vtxcbd6uqs2zVWRtnjW/vDZv89p8TNf6KrzNq/Ao0nwdPr2IwRrlDhV4W0A0x91bdecaOwCx3jPZuQJxBeITAjF5d93Iu+ukd3ceiDuKqBztWz4HIE4eXYoVtwTEkx5dlzy6bpNH15FH13U3ATFJ' \
			b'o10pYJLUkgwSiCfjARCXQSUQc7AEYvLWOvLTuj1OWrfKSRseJoGYNb8ciHMnbUrXeiAu/LM3AHF6UQBi4aB1pYOW4y4G4j0ThysQVyA+IRBTt4cbdXu4Rd0ePpbjbg/H3R6Ouz1c6vagWHFLQDzpPXWp38Nt6vdw5D11w01ATNJoVwqYJLUkgwTiyXgAxGVQ' \
			b'CcQcLIGYOjQcdWS4PZ0YblUnRrCKBGLW/HIgznsxUrrWA3HhC70BiNOLAhCL7gtXOkM57mIg3jNJ9wyBuPZdP+S+673ADYXNGwR2OXB37RLghqzFXbC49+mhGzHXBeCmWHGLwI1RR8ANoQzcFGEtcGNiDO4kcGcilCDOwdqVwqZbLMkjQHw6ns8XoyAJ4qGr' \
			b'Oo/RsyIJ0oOURorcRXXPwDupfim8h4cJeA/2WQzvKHqC9yTsti5qkidhPCVoBuKFZhjiUXaGeBJCQDzHXQLxshda75lyW6G+Qv09gnpFUK9GUK8WQT1HBKhXDPWKoV4lqFfZlqBeTUK9SlCvNkG9IqhXBdRLEUZQT8HalcKmWyzJI6F+Mh5AfRk0CfVZjJ4V' \
			b'yVDPUhopchfVPQf1ahXU88Mk1LN9lkO9yqFeJRE3Qb0qoH6fM1JoJkC9ElBfuiA57mqo3zOBtkJ9hfp7BPWaoF6PoF4vgnpNEQHqNUO9ZqjXCerzLUG9noR6naBeb4J6TVCvC6iXIoygnoK1K4VNt1iSR0L9ZDyA+jJoEuqzGD0rkqGepTRS5C6qew7q9Sqo' \
			b'DwYQUM/2WQ71Ood6nUTcBPW6gHq9D+qTZgLUawH1uoR6irsa6vdMe61QX6H+HkG9Iag3I6g3i6DeUESAesNQbxjqTYJ6k20J6s0k1JsE9WYT1BuCelNAvRRhBPUUrF0pbLrFkjwS6ifjAdSXQZNQn8XoWZEM9SxlJnIX1T0H9WYV1PPDJNSzfZZDvcmh3iQR' \
			b'N0G9KaDe7IP6pJkA9UZAvSmhnnPEWqjHSawequeXd7lExIeRr0ddzGUr8O9WgL+9JwTgjkwCAKcwmtfQ/KRrPRoQ08PXzpcQAj6KK/+KRycqHp2o0uhEKB5iS1/EmRydqNLoRLVpdGIYg66K4YmZDCUlXONikTRYsZA33WRJJEV1C1zQBcFuJvowETTFDXkM' \
			b'0kD8FA6La6TsXTjKuWHIP4ezd0SjQo9ozhHhofKTOGyxxRyh8lGNqDXFsm4hCcz3q8Y3Cj0xUygxvlGV4xs5rmAKDIFfTxf+txvg13OGIsqAnWcMZZEwOl+gSrqYIwoH/ADkQMxAVCB5AElgKQNMDZ0hvAdcF9V4yK6jwS5ikAuir7kBaZdWsSWyLkPUHE3N' \
			b'egRdipwRLRkpM5SMVeRhHzIuwMRQtHlsYMDACHoTiBfg7hZYt3/USQC26+Kbj4BQo0Ej2XARAJ7r8XC9HGlWVEMzcFkBKxJTAFDWA8kKBInAEVEjh4wAFlD++4nyv6euePcQkGp9/RQQhKrbGQNC623aDsPtgQF1PgUOU1WqHQNEtwAkbqg/UZ3ofiKFqAa1' \
			b'PBpthBiQPFP2aZ4rciioaOpDIIgyhRsqocgIQYB/wO6uxWy0FE2GFbUJc1w0Ea1HghUopQetYvjrDnKdj+MFuVuEKRtxW6od5sBVj5tQZQGihMbYGaNKRI/wzwgDDfYD10uQAKCcQJV93ddBN9dTjD4E0pSLzkSkUSDz1vpK8y+fOR/7FEHLxWe0VS2X7ias' \
			b'cYeEG4aYQUCMflgtGa/h2QqL7PuB/gNkGYAWMJUdQwyuCghh0DcEi9T5e+ALyOl7Nf7fHQaCsLgavRqC9JFhKMJOF2EHbPhgm0TKqhsqNOIjw/AGS6NqFI6oQdONgCd1PmIc0DIuc4JL7ILZCJggeAf1H2+fzb0pZqZv/dCYlLyj0NLrZ0Bpdw+AabeyNTVX' \
			b'35mq69jj1Hdm6jpGgo05gzpP0YpC+w3tDNgYfX8AB3LB2lZU4fbbAzrMawtbTz47nVNf7CxueGF8zoa8AvqGXHncik3pADtS5QaIA5wMGio6C3tmMidXO40nsUJzFxWZM25HjTDF39WjP/OavtYDyT9+bcadskLjI2LyUbuzcwD3Vm5ixWayPqO5ClNWXHTz' \
			b'9pSwMzMC4HDuoHvYgDK7Q/TJJPxA2LhP8EHDLgYeUuGO4BY6eXXkVu0ffSC3UPOv7rEnG+xkMafFhZuwYNfdsg5yX3BhTZ1jJS5cQr1itk7R4uCo29Ul7hkqUIJX1B6We4u9fJvgwB4PEXCs421bJlvHZ5fD8o7VMtH3AiHg0+5nChPwBiwTt254SLAwe0ew' \
			b'7UeMFvuAjggbCvuZ1rY8VmCH24Yd7ojYIXADlnU4SY3iiLhRMeMWQ89yvACbnbKCcXS4uFOo6LZBRXciqLAVKipUrICKvkLFwaCi3wYV/YmgwlWoqFCxAiqGChUHg4rhvPsyL7r/8nyx4Cxh4EBlHiZmnnFP5YHLePMvn/8fA86B68IboBb3cyruB3Bhnm2R' \
			b'p4x8DkX+3L0TM2X+dv5Kpx570MVS39ZSX0v9rUo9ZbT7RfQPstRbmAsyYKlXtdTXUn/LUn//qvcPvdSfeNBiLfXrS/3s2rLHRgDMwKdu33MpOj0AkCB3Vv4x9sryrxAcm9GSqwkJwjKrc+urIkac+QDGihFnVjPAAnh6XFDnggvqbnFBHaxesAgNNo5frGjw' \
			b'sNAAC+3FeAFuiQYo831rJcB3ItDjPoBHoMWFzOzGEYi19D+E0k+Bl+cDXFb6MfUX00dgoNBDMeqxDkClf+Ogwlr6L7n0Y+G45CEA+4s/Xry8PkJoAkA56nq/p9K/cZxgLf0XWPrxykMY//MgHQQaxwDh9GVbh/w9sFIPRe6BD/rDQg9SPJwi3/aPEe59QYAD' \
			b'ZHxXx/9dftnvz2L035mV/YdG+C309e1wSICrw/8uv9BDLqyFvhb6WOjPfPSfT2z8aOLRAGBqpbBjfyixTvpZ9RUSXLrH33hsYPBB7pTw4CPaOZC4xXw/dx+/aagENNgzrx+4O6wjqOID8RcLD7SeZP6/bqwQ3DBaku/8qxHbltNbUZdAxaRPvi+oU3T2sUdr' \
			b'rFKceNhgxY6KHUuww47+V2KHrdgxjR1WYAe8ZQV2nHiQYcWOw2DHJeOGG/2vxA1XcWMaN9yKPgyBGa552yNSIEwwRhBAKIQGhaDQIRxILEAg4FKNpVBxyeu4xE2VtpZKFpSKsiRkOV/5nI6JgFwdMnTMyzEfY67sOedCwjG/6nY6n6Y8GnIX5gRcGEyz3Xcz' \
			b'5tZsWLTI2AqF0h02A7tbqZbAM8CmIohE+JPKdisUPgM/I8VjgbsbzUMCsJxHCyh+qmoLc8SiuMgk84Vj0jT97UzjZqzTX4KF+oTGIysFOD2epYbmLayWo3tMNiwdaVu44IH0rYfMTvtwqjlYDIaFsBQQpdceBsDaNhZWNlHOfH/l94+ufRwYeNrAwkywwBus' \
			b'gQWrX7lssc644i98DwvWvcTVbvF9uERw1/hAXGhv4PWs9HgtzrAiL6wZhcJ3sB4LCHatbimFzxA3/eF7NLzHTr+Jl9rRC1+poSans7+0mo5uJv5QAjMhQYsLj1n8zG4Hn8VbKhB8Fzt2MsOxE0K2LKhPX/wDejT8Fbz0b2b+8Pquw45kOIYvykE4tOgMpsbe' \
			b'MjVQ6lcnyFeyF/5BdXjmGorvVouvbkpBsVzGbIpUV6TKg+jeP6jmj0OpAu64ot3m1wwfYVq7cVo9yMwl14sGTRqbt2TmdeAredBcgOEfOxrGj3VczyZQsYP6aNSS6nGePwAgfGMuaU1x31vPGvRhVrEm7X5t+vdSs8SyZlupXQ8zO1xvkJcShApVk/6As/ri' \
			b'j3xG0/9l3P2x5V03hfXF0fxb5PXiqWjt/oxyts8dh/zD9A1nmZvNTI62R8rVUIs7g02hkzUPwk+5H2rDLOCrEeeTx4EpT7CRItqoCNCyu7Mi0d7TUmEb2gbseounB946dWePXrdRplAHKR3QJ3iYAgJtvFtv0LW5+jbShy4KCVSY7o49sKhA5+m9Ky3QASA2' \
			b'nwbs/73DDfoG7vQFyzbKJhPtsz1Z4+Y6xEEKD64tlG3Qaz0OXbKBW2D9baQcW8vQsjLUNw9yo1wy0ao+fRECF98pN1JNVwvQogIEPc8PcaNcMtF4v1UBAvMfphDp5oAbOKTX30YqGmpBWlaQhuZBbuRVmOghuHVBAvMfpDDBQJODbjCwY/1tpKmyC6GWp+ny' \
			b'BM7Qh7hRLpnoUzhIeWq7Q5Up3Rx8g3FR628jhdVOh4XFyjQPcqNcsq7PAfLEetfFhtIVrZeVMNss32Ao3YrYg1oaFcYQinNSY+2dWFjYuuZBbpRL1vVObCtsEzng9gWvb+5uk+N9Nz2BdFu7N5aVQBhJ9xA3yiXrujfOpwTCDIAz3UixtVNkYfEzzYPcaAjk' \
			b'ruYSGNO466dzi3Upx4CrjHKN/0cIsM0Fb0rDUMvdKDgGZUeUm9rVA7EOhechs9wO16fgoW+WbzB2fNUN4y1Mrlp9H06KShOi0B7rumjuhT1ght192sgQE0PN770hVHOvNjLEut6VuzAE0NkqY+ilBtHN8Tdg0VtGIsNMTB5YVPk4vW3MUvuYZtUGU5LW3nOb' \
			b'bf/7yErr+kvupZVcc283stHWuR33yEZ9c283stG6Xo9Ln38D30hYv9HnENL/tqdMPHT8eHGaxVn0oHwj+5/njJWT2d82F73RXM91408u3uauueiNbL6+Q+Sibd41F72Rzdd3uly0zfvmojeyuW7eapxdtqOGkldvCGD0txAAOsVAB99kpQu+SSVzhdc8xGi9' \
			b'7qFHHuZwwSQ+nnRhuunY/sn5P8XuR7HBmniHt3fxrzTfNcgPSEC+oL4T6wlMZlLKUyIvxXyEX+zAuyGHpY9V0UeiwgeibPowFEy5YY+Ef8jb4oNZIISyCh84iFdBVu0oKzqqV/m3v4Xs7rMpTl6CRBES+7z5Fnv5oUcfe/JpKg18jQ6KqN/3HNOk72KQ0v2L' \
			b'fMiAIWRvWLdQoYIUl3pYyyyE+DjfX/0vfJVXAA=='

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
		('UFUNC',        fr'\?({_LTR}\w*)?|\\operatorname\s*{{\s*\?((?:{_LTR}|\\_)(?:\w|\\_)*)?\s*}}'),
		('UFUNCPY',       r'Function'),
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LTRU})|(\${_LTRU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\$?(?:{_LTR}|\\_)(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)(?!{_LTRU})|{"|".join (AST.Cmp.UNI2PY)}'),
		('IF',            r'if(?!{_LTRU})'),
		('ELSE',          r'else(?!{_LTRU})'),
		('OR',           fr'or\b|\\vee(?!{_LTRU})|{_UOR}'),
		('AND',          fr'and\b|\\wedge(?!{_LTRU})|{_UAND}'),
		('NOT',          fr'not\b|\\neg(?!{_LTRU})|{_UNOT}'),
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LTRU})'),
		('LOG',           r'log\b|\\log(?!{_LTR})'),
		('LN',            r'ln\b|\\ln(?!{_LTRU})'),

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

		('NUM',           r'(?:(\d*\.\d+)|(\d+\.?))((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))('*)"),
		('ATTR',         fr'\.\s*(?:({_LTRU}\w*)|\\operatorname\s*{{\s*({_LTR}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"({_STR})|\\text\s*{{\s*({_STR})\s*}}"),

		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
		('COLON',         r'{:}|:'),
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
		('EQ',            r'='),
		('ignore',        r'\\[,:;]|\\?\s+|\\text\s*{\s*[^}]*\s*}'),
	])

	_PYGREEK_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.GREEK))) + ')'
	_PYMULTI_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.PY2TEXMULTI))) + ')'
	_VARPY_QUICK   = fr'(?:{_PYGREEK_QUICK}|{_LTR})'
	_VAR_QUICK     = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK   = OrderedDict ([ # quick input mode different tokens
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})|(\${_LTRU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LTR}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)|{"|".join (AST.Cmp.UNI2PY)}'),
		('OR',           fr'or\b|\\vee|{_UOR}'),
		('AND',          fr'and\b|\\wedge|{_UAND}'),
		('NOT',          fr'not\b|\\neg|{_UNOT}'),
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
	def expr_ass_2         (self, expr_mapsto):                                        return expr_mapsto

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

	def expr_lim_1         (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                          return AST ('lim', _expr_mul (expr_neg), expr_var, expr)
	def expr_lim_2         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):  return AST ('lim', _expr_mul (expr_neg), expr_var, expr, '+')
	def expr_lim_3         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg): return AST ('lim', _expr_mul (expr_neg), expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                        return expr_sum

	def expr_sum_1         (self, SUM, SUB, CURLYL, varass, CURLYR, expr_super, expr_neg):                          return AST ('sum', _expr_mul (expr_neg), varass [0], varass [1], expr_super)
	def expr_sum_2         (self, expr_func):                                                                       return expr_func

	def expr_func_1        (self, SQRT, expr_neg_func):                                return _expr_func (1, 'sqrt', expr_neg_func)
	def expr_func_2        (self, SQRT, expr_super, expr_neg_func):                    return AST ('^', _expr_func (1, 'sqrt', expr_neg_func), expr_super)
	def expr_func_3        (self, SQRT, BRACKL, expr_commas, BRACKR, expr_neg_func):   return _expr_func (1, 'sqrt', expr_neg_func, expr_commas)
	def expr_func_4        (self, LN, expr_neg_func):                                  return _expr_func (1, 'log', expr_neg_func)
	def expr_func_5        (self, LN, expr_super, expr_neg_func):                      return AST ('^', _expr_func (1, 'log', expr_neg_func), expr_super)
	def expr_func_6        (self, LOG, expr_neg_func):                                 return _expr_func (1, 'log', expr_neg_func)
	def expr_func_7        (self, LOG, expr_super, expr_neg_func):                     return AST ('^', _expr_func (1, 'log', expr_neg_func), expr_super)
	def expr_func_8        (self, LOG, expr_sub, expr_neg_func):                       return _expr_func (1, 'log', expr_neg_func, expr_sub)
	def expr_func_9        (self, FUNC, expr_neg_func):                                return _expr_func_func (FUNC, expr_neg_func)
	def expr_func_10       (self, FUNC, expr_super, expr_neg_func):                    return _expr_func_func (FUNC, expr_neg_func, expr_super)
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

	def expr_ufunc_1       (self, UFUNCPY, PARENL1, expr_commas1, PARENR2, PARENL3, expr_commas2, PARENR4): return _expr_ufunc (None, expr_commas1, expr_commas2)
	def expr_ufunc_2       (self, UFUNC, LEFT, PARENL, expr_commas, RIGHT, PARENR):    return _expr_ufunc (UFUNC, expr_commas)
	def expr_ufunc_3       (self, UFUNC, PARENL, expr_commas, PARENR):                 return _expr_ufunc (UFUNC, expr_commas)
	def expr_ufunc_4       (self, expr_term):                                          return expr_term

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
			if rule == ('expr_func', ('FUNC', 'expr_neg_func')):
				return self._insert_symbol (('PARENL', 'PARENR'))

			if rule == ('expr_paren', ('PARENL', 'expr_commas', 'PARENR')) and self.stack [-2].sym == 'expr_mul_imp' and \
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

# 	a = p.parse ("Function('f', real = True)(x, y)")
# 	print (a)

# 	# a = sym.ast2spt (a)
# 	# print (a)
