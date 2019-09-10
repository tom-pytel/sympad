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
			last, neg = last.strip_minus (retneg = True)
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
		if last.var in user_funcs or arg.strip_paren ().is_comma:
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
			b'eJztfW2P3LaS7p+5wPEAaqD5Lvqb4zhnjbWdbJwc7MIIAsfHZxHcJA5sJ/csDva/X1Y9RZFSS93STHdPz4wwnJZEUWSxWPXwrUg+evOX//P+t7//pfnL069ffP0qXV88++q7dPnmybfPXr1IN199++SpXJRcdbp+8fzV1y/zVeUbLRF8+TXF8Yp/v3j21x+f' \
			b'Pnn97LXcv3ySfb8ot38rt9/g9vWLJ6//7YuU2r8TFd0Nez/9/tsX/0VP3c3r776l3++/SL/PXn7z3X+9fsYUfE80/u0JvXz5/NX3RMPzV9/9lch8/pK/4N//+JZCv+D8f01vv/r+FeX6C/7y6dcvXz7JPCGPb5//9d++y8l/m8mjmy+/eMEUEhn/kX6evPyG' \
			b'bl99Kdmmuy/K7d/KrWT72YvXz8QnM43i/A6EJAIo0Msn37z+7muK/jvO97P/fPoiv6ay+PL5355/SdE8RUHI59+8YAYk1mRe/OfrZ085wJfPv/qKwjO53796zqLw5NWXxC968TV9z0kmHqteOQjjUxpP/z3dfvrjp09/vv346c/q/lO6f/f24/vPP374+OPf' \
			b'f/rl0+e3H6vX6TZd3nKw9//8PQX5+c9f8/2nP35//zE//Pb+v3/8xx+/vSsvf0q3v779/OO7D7/I3ccP/6/cIeVP7z99etfd/d7d5Wje/lRuP3/uUvvH23ef8/3vHCu8ewR0hP7yc3f782+f/zvf//rHLz/+/OvvVdbK7T/+UWWs/oBu8vOfb0v2S2oSKj9+' \
			b'fv+xe/X273/Pt+/++PjL/+SHf356X/Lz08e37/7v++7xU03Mn++7/P3x288ffuvSfNuFf1dyxKzsKPxQovyj4upvHUk//fzbh47UD4XXiZ6O1z+/f/e+e0hyU1Hw+6fPH7pYuxLsaPnwSyH33Ydff33be/j0lx+aN482zjY2XjV847Z0YzX9mMZur+QxPfGd' \
			b'pZ+GPa56Hngy+bv03mYvuuVQG8dX1TzSjUmPqjEh3VxlX/HrPDaBbrTFj2ubjfZXtZf2O14u1l50m+6Uxo+nBBB9eqJbynX69w0lh88c3RABW/w4yRvlSfGnidSQvjb0f5V92vopypW8iBLOsmpzluNV9hW/zmOj+QOViCIKE6NteyU+G8X8UJ5+2sZTDuSl' \
			b'59t0xwXQpHhAijzm+8pf4bJhFmj+Ny6/1nRD8Yo/EknEiScCGc5UlEz52PmKX1uCbfseG82SYIgejtNo/LhEghNyiQimwhH3fPfCqfzCRPw4yVRK1rL8Jn8qaeI/vkkernrwuJAHfReS6G1z8VAkyIr4b9x2x6t+VLshVP+RCrLd8Rp+pPuPZuex/8HGoMCT' \
			b'3OuABCiAhnhn7/K4MeB5kizdNlo3VCjpztPHqWxSAGj7RAhGh3ZmwFRc/YAbwzwn0Q2N6+QwlSrnQgVREFIq65qEGkVP6GXnX3wsfGzxcfBxxcfDx2efjWLNZNzAXcSP8x21nVeoveiWsmLwsxGUklu620JKc54TSwyLl414IUVnKS4ociojllHJAokscykV' \
			b'nOY41RY/nvQbMKS2fMt8JBjNkIIskqSwT37ccC5biYa0q7EhI13tLR7pmalv8ZNE6kqek3oxbVv8eIIDkMSlzyQlIXyUxGEjOU0SgdIlTNh2eJ8lxpkMCQylEM8kIYnbOYRujMh1ZqvP3Euej2xRVnqkcN2TA7KlvOnQ3bVyp1W+0fkGgNcKthJGIUWCBc1M' \
			b'IVlnIhO+PWJh6iSUKh1EqfHjiyoSQ1CcifP8U1WfQRDYevxwLROuxItu6c7ll1fymJ7yC+Q3cThswTOXueoIMzh/jiJwXQSMshyB8/kFBxWv/JVGpqlqTMiZ2gpvtvRAlZIhoExfpdJM2p1KhUq2bSLVB4mKEJqQlHmbUHWr0n/S7W2qc7apLto6QvmUStKv' \
			b'hCcxufSJaag6dwQcibMEBKn6U0kuomtiij2llLidxME0ITbttmlV0+qmNU2b4tT079J/+lRTuvSfYk16lMosEUX/KY7UWmE4IB1IcSeNS5iRQEIpCpOITTWwSuWlEj1tSpii802bXGjaRGiq2KlCTs2l1FBq2tjElNXkVBN0ExJptgmuCRRhijrFnVojnnUl' \
			b'VdZJplL7Iylb0uaElD5JWUp1mwJvEydMQ7CpSPKTqiii44fm0Zbq6TePEtNJuhLj6ZI4r1JpPLLy1lh4O1xafpu8PZ4DXdZyOmk5RZSE4is1d1AEgXlPLTkuMGI1B9tyyT0KEhyhLIpR5Y+5RK5WhTtrQTLnUEZGiiMXC9QrZvVy/Nzjo3AQvBvjGrjVcanH' \
			b'nRGOgB2JKieC4/wZ0wxIM0JISUg435r5crp0tUe62p44HZSnyjrJSrpq2zm1jbi+Mv3sEKcF4qxfmX925isjsMrwI8xgNnSZlszmPNb5Snm4LeJ7hV8X+HmqoyjVguGmk2lS3pq2SeSvInpkETVKOC29DWkHcX3MDYB2hY2zV5Qti72iPh7166hTRwVDXT8q' \
			b'r8SRleXHZrlaWX5uluuV5edmuVlZft76tbXS48w90G0eUlAYCVqr1vN2h7pRORnp0DK+qvOoHtqcj5S0hGRAyEmpWbcW2rkLzcrAqnQKIlfVD6tDpFQWV5FOreQqPcwW8NJiGqDF+N2jmIekxbvFqGYeEsCjjXmQE3G3nNS9ZWWUiZQgw/Jo+DFxau1+M4uC' \
			b'CEgABgZgYHAysQFhUhkaGRtJfCCiHnz1wleik5JLPEwp2LvMlzePPHrJ3tzHvKE4PYDE+55a3LOsAhY94x/yU+fwbudNKoqtH8goZhmRc2cy5KPQuTb5gc058hS0xtyzXmeTT90pIxsZzOivzD75cKcnJvPcfbquXD2SCCdGrrJ7+vnTxEK9dj7PLdsMFWS3' \
			b's/L+3Ly3dmX6LcDMyvTzW6IpaZgk9mmxREvXlctHFe3EHmIqs2S1xpjdp3TcNTlTYiN2smSgmBvuXA2vZTebnZrx5ISWlei9UgK48sVycZHdk6CaDEpMmkL/IIbTvOKKv8HYoww9IkQ2jMXoTbZ854RXKdgrBQrFtHJnVIS5ViCrGwirrK1QsqaCp8gxZSuL' \
			b'L3iynEVWzKZaSH0LHWhNlnpUNyuz65ksdKTe8MwrcWflCkSLmPGQGWAfOgPcg2YAWVZwk0E6Qi23IB4UC97QvP3Dy7TlesCpxul7nlcyrdBie6B3JucCGhEThkcqt6ExR3cbJiiqswrQsArQsArQ3BQCgLMZAI+XrobjZx9F8oKdnsXrHkzUK9h83YuchNtS' \
			b'W+k1R3MvWPkoikWt1/dCyMmYCEpr70l+ZKTOu3uSH+mv+vZ+5IdI07AB0jD9EVMf2hOFKugr3tOJLqleNjJsZ64wNGswULKuIjhrxa5REFZKZysXhWIhnhqZMzJXMs9hyjJ+Gr+XR7poCZ04iyvi9hAAKWpp43HLfF12efyZKHR20cddeXtkgzoR7G4RK92Z' \
			b'avENdU4EyEwe8dUy0stDkiuKncaywKhV4E+wxgwI3kLsW5NrBakE8gonhVoEI+9maqSBfA18DXy5dsClRSXRSnUUEZ/jgYGHMICT8qofwBoZHqAy69xM7kHLxGCAZgRoRmCV6Lr37KloLlsEBTrGc4s/8KoYNLa8TJMHjHajneWhuh4xeyibb7vWt5XWt83T' \
			b'lGgTWrQJLdqENrcF7WrZfLwdXDSzF4DncnNBILJMAwOBneqGd+30SG4wiBIFl+i1efyUP7K2W05lr3JT5T50O7eNEzF2ue0FMXYQYwcxxsXgmshxonoOPHPgmVubESfYn4vZO1wztBrhnh93HJQk8O7V2K/OU32c8kcbgpZqJiXuoRgeikHBmq44/QObTWRp' \
			b'NeBcEADhq2nFcid2k1jhgfHmDUlJgJQErnJghdet5s0Ma1HJwXiJ9p2lHWlpO1priugRB1tIXos4W+Ez6kgr05Wymy1/z4laWbGePowPrwTcg8s0y4TNMqFFFvRVLUpUPUCI+EoBMJC5bd6kb3gHOBqGpF3gIufIMIJzjZHSTUlSXjyRRhng+gIVFSotITYQ' \
			b'02m7cO6rglc1QwqbDTM4DMsD9VsqrcgZpO1SOctVHcRD4UFwWonSpPfEJtpxgbZboJ0WqNdMvUlai0tL52ndPC2apzXmtMCc1mPTKmxarEwrlWmjAlqYT4vyiWG03TDVtWRMSyPytIMVbalEe/xQedGOELQdBO0FQRs/UJeVts6gcqF9ban2pQVltPJgSzuw' \
			b'JwbSogPqoVDvhGUo+ZOE8N7pyZ8Kn+xtCRvIxNfS3vUpHprz99tUYDgBhHY8p13caR952pW+4V3j6YiLwJvO01kWW9qWnLZ7pwB8jEfDu7bzwQyaQtA+8ZF2gOcjIJpNS1vmcxDNsdBHdKwDH9FAG7TTvvl8GgVSo43MNX2XPon0npJInNhEXU5QSEW5CUQY' \
			b'f0yngVAESZHoYAPezZ02RMeZBg1vl04HjUSH7CR+bhJfN0EJ0Z5PoaA0UijaV54286eTEkg/eY92IouOneDjT+hTfkmfbSnilvd059MLiHY6McDyOQMNn5Gh+JiTFCiV+Kal1JNnSwG3zDfOZpTjSigFnJKwaSnrtP185H32N7RjvQLDiP9EKPkS0cQDooJO' \
			b'ZMFJDxvCDzqngA6AwZkEW9ptnqjnczX4+A1iYvJNorkJ7gfSYtLdnt6qadXNMAR4KTpssxqrvib7oynzAOf267aeqd93RbfNiH6rAzruiHFuqNZuhmI7DpUSdrvq7YqCj6q4O6WSc5pJwV33d1DV3Wxlv2uK3o4ouzug7s2/7GPCe/eYED+EdHH/y43LN1R0' \
			b'bdb9ruMVpMOIlspA/Wl8Gr2+fi+ToAA4YAsCoA11GAR0wQE0mUYbXIQJO22f0hHcStuNICJ2/Vq00rpeszSHSlNop5/K3dKMJXYwlZ77eCMNb8YZP8AaJxijd3GFGoa0z1GHKwS8foAv6gCubAVbUvxkQ3QQY7YzcCZWOOMFa/QAb1JYWvXV4Q41Z4E3kEqe' \
			b'bCCo4UvgC/XaI+NNF1qC05BCy7c0arftOUIeBG4ZcFRpUZCeLsEbCk9S0vYRJ7bF7aDPgJraRcmdz3eaMbIXX4mYZLN7ELBqWWU5ywRYeAlP+ciCKIMLspwEiHNeARmYrgBbA8gSNgpeZabWqKXDXqwqZCsm9BBqUSABrjiBW0KFiyiMKLFX4CUpdhDmt4+p' \
			b'ukhS8BhyE9VjAtEkxo9T3gjPTIdnXd+K2zLSkLkLMCYYZmQE7rgYtuLXHvxSDR8ApqlQ+I7aS7mpJM2kLpDGlVrL8DJK7jrHsKUq2FIdbOHb+bBF4SOLdA+2eqntwNYOQb3gDlQktrXI9Xiw2MtQ3ZdSOd3uNeSSIYtfGFyQEMmMGkCW2gNZeJ0hS9JfAFmq' \
			b'ImsWZKkOskDXCGQJ51CUIUrsFWRJiB3I2kUqO2h53V2YWttZZ8YpYgA01k6AVA4hQWRKxQKkbM8xSNkKpGwBKbsQpCxAyg5Aqk5tB6TsPscgZbtW1XiYqOrcAKFAOq6+fs9iaQFR6BXyBcmQuNgBRNk9EIU4MkQJAUsgqiJrFkTZAlF2AqKEbyjIECX2GqIQ' \
			b'Ykmryq1YtWLV9bCKMgbd9RNYlUNIEMIqeBFW+Z5jrPIVVvmCVQvHnSg8cckPsKpObQer/D7HWOULVo2GiarOjWCVF6zywKruPYulB1Z5YJUHVmEcCyytsMrvwSohTrBKCFiCVRVZs7DKF6zyE1glfENBhiix11iFEEuwyq9YtWLV9bCKiIbuhgmsyiEkCGEV' \
			b'vAirQs8xVoUKq0LBqrAQqwKwKgywqk5tB6vCPsdYFQpWjYaJqs6NYFUQrArAqu49i2UAVgVgVQBWBWDVYNhdhT1YheAZq4SAJVhVkTULq0LBqjCBVcI3FGSIEnuNVQixBKvC9Oj7HUKsMu6+gtb5QYst+1iJI0BLYdBdxT505XASkKALXgRdsecYumIFXbFA' \
			b'V1wIXRHQFQfQVae2A13xgGP0KmPt42GiqjMk6JXH2iPQq3vP8hmBXhHoFYFeEegVB+gV96AXoszoJQQsQa+KrFnoFQt6xQn0Er7hEnLsNXrJqwXo1a7otaLXzdCLIsPgs5bxdrqS5ZvqoVcXTgLSblzwMkruOkfopatRd11G3fXCUXeNUXc9GHXvpTZEL71D' \
			b'0JA+B0IEvcbDxF6GgF6gXlKt35N8agy7awy7awy7awy768Gwu94z7C6vBb0yAQvQqyZrDnrpMuyuJ4bdM99QliFK7BV6SYgl6BVX9FrR64boRRFBibWgF/qMfKnQK4eTK6EXbo2Su84xeukKvXRBL70QvTTQSw/Qq05tB70OOUYvXdBrNExUdYYEvWTGUKww' \
			b'y3tGLw300kAvDfTSQC89QC+9B70QZUYvIWAJelVkzUIvXdBLT6CX8A1lGaLEXqMXQixBL7VdDbdWHDsWjtkmq7NMKNKVcMwyjrGpo8fFNV1oCa5M9qKEbc8xmlWTi7pMLuqFk4sak4t6MLnYS20HzewBx2iGu8KBkWBR1XkSQJMpRo0pxvKeAQ1TjBpTjBpT' \
			b'jBpTjHowxaj3TDFm4gTQhIAlgFaRNQvQyhSjnphizKxDcYYosdeAhhCLAE0B0MBQErOQ0aoPVYRT/tAYugIKkAZ3mgoNZS2ClpDkx+Ysjs3tV1vbFbKPBdkkEug4G+k4G3ScDTrOdEmR88U1XWgJTsvI4IVL7QiyTdV9NqX7bBZ2nw26z2bQfe6lNoTsXYKG' \
			b'9Dmf7wSyx4PFXp4A2UZ60AY96PKeBNWgB23QgzboQRv0oM2gB2329KAzcYDsTMACyK7JmgPZpvSgzUQPOrMOxRmixF5BtoRYBNlmBbQV0I4FaI6EgdVZVioZrFPiS+ALAZoDoOXQEpwADV4kWq7nGNBcBWhlpRK+XQBoDoDmBoBWp7YDaP33VKJDAp3PdxnR' \
			b'dsJwyqrOlCCaE0TDcqfynhHNAdEcEM0B0RwQzQ0Qze1BNCFOEE0IWIJoFVmzEM0VRHMTiCasQ3mGKLHXiIYQixBtaJS7ItqKaNdGNE+SwOospm+8QrnFJfBFI4yG0IgZnBEzOPEi0fI9x4hWmcGZYgZnFprBGZjBmYEZXC+1HUTzBxwDmuTMZg6MBIuqzpMA' \
			b'mhjDGRjDlfcMaDCGMzCGMzCGMzCGMwNjOLPHGC4TJ4AmBCwBtIqsWYBWjOHMhDFcZh2KM0SJvQY0hFgEaEPL3RXQVkC7NqAFEgNWZ7GPoysBWgCgYcaDL67pQktwAjR4kWiFnmNAq2zlTLGVMwtt5Qxs5czAVq6X2g6ghQOOAU0yaDMHRoJFVedJAE0s5gws' \
			b'5sp7BjRYzBlYzBlYzBlYzJmBxZzZYzGXiRNAEwKWAFpF1ixAKxZzZsJiLrMOxRmixF4DGkIsArShee8KaCugXRvQWpIBVmfZ9oauDr6OBYQBrQWg5dASnAANXiRabc8xoLUVoLUF0BYuWDdYsG4GC9Z7qe0AWnvAMaDhLgPaaLCo6jwJoLUCaC0ArXvPgIYF' \
			b'6wYL1g0WrBssWDeDBet4ngA0IU4ATQhYAmgVWbMArey0YSYWrGfWoThDlNhrQEOIRYC2xwZ4BbQV0BYBGhU9ZgWszApYzApYzApYzApYzAp0oSV40ibxMkruOkeAZqtZAVtmBezCWQGLWQE7mBXopTYENLtD0JA+5/OdANp4sNjLEwDNyqyAxaxAeU+CajEr' \
			b'YDErYDErYDErYAezAnbPrEAmDoCWCVgAaDVZcwDNllkBOzErkFmH4gxRYq8ATUIsArR2dwuOO45p2P+xwNoJ9uVYke1AU802BnrdatxtcaXWGqxUDKxUDKxUug8kuDLZS0wKKsettcpKxRQrFbPQSsXASsUMrFSUSDXS2Wmu2QOuhd2dfK7hoSY+5EZbyZo0' \
			b'2sRYxcBYpbznRhuMVQyMVQyMVQyMVczAWMXsMVbJ9EmjTQhY0miryJrVaCvGKmbCWEXicyjVECX2utGGEIswLq4Yt2Lc0VtvnoqeMc7gjhpwmDOwmDOwmDOwmDPoPkAwbsDByyi56xw34Ko5A1vmDOzCOQOLOQM7mDPopbbTgPMHHMGD6z4niDNoxo0F5mZc' \
			b'yZk042TmwGLmoLznZhxmDixmDixmDixmDuxg5sDumTnI9EkzTghY0oyryJrVjCszB3Zi5kDicyjUECX2uhmHEEsgTq8GxtPIllhn1ANHuHYC5bZzDI5Dgw1Scdni6lpc8BIitRFLUJlJ0DKTIF6UeOg5NjiuZhJ0mUnQC2cSNGYS9GAmoZfajsFxOODY4Fgy' \
			b'aDMHRoJFVedJDI5lJkHxKlUHAupwbHiMGQWNGQWNGQWNGQU9mFHQe2YUMpFieCyELDE8rsiaZXhcZhT0xIyCNrZjI4qWjY9bSaU2QEaoRYCnVsBbm3JHaspR+aKL5mRlmMPKMIeVYXRJkfPFNV1ouSatEi+j5K5zBHCuWh/myvowt3B9mMP6MDdYH9ZLbWcj' \
			b'7kOOAE7uBODGg0VV5wkA52SJmMMSsfKeBNVhiZjDEjGHJWIOS8TcYImY27NELBMHYMsELAC2mqw5wObKEjE3sUQssw7FGaLEXgGahFgEaBe33mDnUJQV1k4Ha+pUi8U8yQq3XKSLqtFF1eiianRR89LXHFqCK5O9KGHfc9x2q7qounRR9cIuqkYXlWOicxto' \
			b'137iOszeM1l8XM5IZ3VA167jVpzk0WZejASLqs6dtOKkm6rRTS3vufWGbqpGN1Wjm6rRTdWDbqre003NxEnrTQhY0nqryJrVekOXoGvBTXRVM/tQuCFKCnXLDSEWAd26DuFhQtxJWm6GypfbLUZabgYtN4OWm0HLzaDllkNLcGWyF7XcTM9xy81ULTdTWm5m' \
			b'YcvNoOVmBi23OrWdlps54LjlhrvcchsNFlWdJ2m5GWm5GbTcuvfccjNouRm03AxabgYtNzNouZk9LTchTlpuQsCSlltF1qyWmyktNzPRchPWoThDlNjrlhtCLAK0dRnCCmhHAzQ+1pXVWRZWOSysclhY5bCwymFhVRdaghOgwYsAzfUcA1q1sMqVhVVu4cIq' \
			b'h4VVbrCwqpfaDqC5A44BDXcZ0EaDRVXnSQBN1lU5rKsq7xnQsK7KYV2Vw7oqh3VVbrCuyu1ZV5WJE0ATApYAWkXWLEAr66rcxLqqzDoUZ4gSew1oCLEI0NZlCPcP0DAIfXxgsxPg1g4Arq1BzlNRs4pLp9ShU+rQKXXolDp0SrvQEpxADl4Ecr7nGOSqTqkr' \
			b'nVK3sFPq0Cl1g3nTXmo7IOcPuE25yyA3GiyqOk8CctIVdeiKlvcMcuiKOnRFHbqiDl1RN+iKuj1d0UycgJwQsATkKrK6CA5DXZk3dROd0czAnASjXd0fZT9TEbAI8468Ebm7Bag73dZytwVw+oJabbRPDm2U4w7ZhUQqcTaGkC1+h/uSdyEkCBmCwIsMQWLP' \
			b'sSFIvbmvYoHqjEEWbvCbz++0wx1+uXjL/65FSNzn2BakbPE7HibmzFG5Eaip6nBifse7/GYKWFplgYKSFQpKligoWaOghosU7J6dfoWMbAwi7B1AG2iahjem3eWCm2USgv1+u+yM2oQIF3EJfNGEh2SDPGjQSdgO3BLVj7HfKF23PVAbrla4IajdANHOjGKz' \
			b'TxY+ZzPstvqUVA6Y3vR6HJG6EHJNCiBeRsld5wiRfDWl6cuUpl84pekxpekHU5o74OP3OgIfXyYwx8NEVeegOhfPY/Zyc/DkYb9nllLiFWjJqSxoNRXaDuKJLxOUk4cMZ8agdEKUkqlQREJMnHzH4DHcMHwFjwcJHpZmglmx7AR45BASRJnsReBhe47Bo7Ld' \
			b'98V23y+03few3ff2EHjYfY7BwxbwGA0TVZ2DGjzsXPDYY4cv8WbwkFSWgEdH22HwsDPAQxiD0glRSqYGD4TYBx7D/bpX8HiQ4OHJgIQVy0+ARw4hQQg84EXg4XuOwaMa3PFlcMcvHNzxGNzx/hB4+H2OwaMM5YyHiarOQQ0efi547BmvkXgzeEgqS8Cjo+0w' \
			b'ePgZ4CGMQemEKCVTgwdC7AEPMzRmvz3wWAdi7s7UGZUV9ofw7QTY5BAShMAGXgQ2bc8x2FR7QviyJ4RfuCeEx54QfrAnRC+1HeBp9zkGnrIbxHiYqOrcVMDDwy0e+0Fklij5Bpn2BhekAj3oQ9KezSAkygxJkv4SSGoLWXNGWHyxZPJTsCShUI4hSuw1LCHE' \
			b'jKPAzdD0fIWnFZ5mwFNsPMaF/cS4cBdCghA8wYvgKfYcw1M1LuzLmLBfOCbsceibHwwJ91Lbgae4zzE8leHg8TBR1bnZgSeMBmeWKCETmfYGF6RCejA48M3vGQaWKDM8SfpL4CkWsmbBUznwzU8c+JbZhkvIsdfwJK9mwNPQkHyFpxWeDsMTlRLDBS4j8NSF' \
			b'kCBJRcQrJYa7zhE8ITDgie4FnvDtfHgKmLGiSw1PvdSG8DSgZkicAxUCT+NhoqpzM4QnTjSHYHjib5Bpb3BBKjQEse3DE57H4UmiFHjK6S+Ap0L1PHhihgCeQNcuPGW2oRxDlNgreJIQc+BpaP69wtMKTzPgSTVQQFzG4CmHkCAET/AySu46x/BU7Y8Vyv5Y' \
			b'YeH+WAH7Y4XB/li91HbgaYegXnAHKjI8jYaJvdzswBP2xsosUUImMu0NLkiF4GmwMVbYszGWRJnhSdJfAk8VWbPgqWyMFSY2xspsQzmGKLHX8IQQc+CJjbkT5DQJQJrEogRUsdo3xghg0eofYJYZg61tRi4zBl7bjF/m9LZC7Qwgc02S7FPsIXMdREvhyFzC' \
			b'UdVgKoRL/mQewkhnBO3cBOKlcLSObC/ybU9jY7SNM1EwXHdFH+kUYQ81vGjoivQm6QMab5uUv5blESBJZdkhZYwdWm5IgCkmWQ+jxXycrtHzhVbfGfapHUHnRsm9wjBwZBDd0Lo9XazK9UKr8mybpAdm5b3Uh1C64Q0QiVo/pLR85ECMRgW5SfLeyjrA0eC0' \
			b'DrBkd4itGjbmmQPCxwiee3DQI0FaBjgwMN8Y6s5T6hRvfs/ARhONLUCXsJAERqke+Eqahq0vypRhprRG4W2boRglM4nHzJ9c/rPWDmpk7tBMQPo3XQEgnRAlnXoFIUJ00Owesw/9JpSmet3zb6BfAmxWILowXLukEEOwnoJpT+hM0AxcBhDXKMwQPAt/RycX' \
			b'GW0JVQ3jaQbMenJwzsTgEACnwK8Cvh3Auw7QqRnNuxmgxmDWDkCsa8b5fcB1GLKyGhpGqQxRHSaNAFJGo2tB0f7JwYw7m2zOHR2yEodtslnTfENomMaFGhN20OCaOLBxc4yP5mk96Tspe1/Ts46T2voRtd3TwDq15uamUpKHe62/SbN2dXiJ/h5oeaA5cbeU' \
			b'uGpAUFk9IGWm4t9V6OXKHBbUwfaMylz1eESr7VEVm5bFkdCkMImqi1L0G1fUhxT9sJLnnsUlKjoTV/+L0lOP8siKz5i7pWvLncNLBIIdENBUTMuAoPlXErLHiVRulrfLmuXhECT4o6GCIIHvkGB7/6r5rP20WHeyms/jDsnPBCCBof351AARtrwSRXMfkbpr' \
			b'1NEN9YLO9K+OghisZAwbixDDnA01OpQIHUpQ+dzjJkK3Q5DZ20SwQAcavNrQyB52euSB4CFelAEtes1HGHCR89Io280h0YPm1kW8fg/fToy2HhdKgCNbGit1I1gy1x74NvHEz+g6hJldB3PSVsV4i8LWGIGGx221LAbdBy6bVo1gBJF5R3CCCnxOd2JsccFY' \
			b'K0LLiUyTXYokIpczrDeu7kltkrASH0nMaOj0fM2IsSmOUzUl0j1NCyi6nzN6kJsVYQQGcvPhBM2GS+xkDKGADc14NmqjWJ/NuYcX/LmbD8QZiodreDUHHqQp0TUjhq2HVhoMg2ZC4vubi0CLI00CXHjPgvl57bGFoupcwHdT0489+H9XOgLqRoP/zb/C44Tv' \
			b'NEiQtO5SVTZl42a1+qWq79xafKb63uWaerLBvmVjkZvVzpetzJK/WfXxodH/JP7X0mJ3HkUOR2iiz7VG2qfQ7oSTev5CFVvJWfEXpd3c7mbxv2kLvNZxc31FJ0u5E0/zcVnMb4IfVHl7PZX351H5St3ZpuA26u8Tqvuq6vNUfaDmVB63WJ2fXMuPq+Huehoe' \
			b'zq/hetXwVcNFw9tVw2druL+ehrfn13Czaviq4aLhcdXw2RoeLnZ47V4NqV2SCl+Y9h5JVWk91eUMnt1UNZt/KVp+mOCHB8Hbi9XSlLVumvscGju5eu/UU9urBk9PWacYLM1an7HavbVp6iPUufH2tHlyHfCe+tcP1u9ecj08Z/eBOVbv28ru9V5pNZZc9/8X' \
			b'1dP8QW+t652Y7pq3bHXeyjVmAVuyjlmfVJPY+nECUarAU0msKr+q/G2pvN/5X6jyflV5Lyrv5qq8at60O3sXQb81aza2Jgp9bWZVhlL29+zJajOmLopVY0e0WYxDElselxjZDaeSSpJISGMLGWTxGxG9Tuy646nqTWByOY4WHzPVjXAZDGUTvcSGa7MNuCaI' \
			b'FgFfDE01H/1MXk5ARcdTjDwdmamKz57RFXO1xMdBJ7bb2c/tSbmuuW5uwHUzzvg7yPy2QOJOAWRMO2Eh2OsXwlQlX5WJX1ifLy+3WXXxZNluq0706cqYs93/79eFVcHj5cI673ryMbOumhIjprT0O3W/JnJz5eomY0OVpF1nGGiptJ146fP+4ZxrS+aC5hy3' \
			b'guaNy9RYdc0RmOVSe4ZdQg6MkLr4OLV5WcL9KuEXLeH81Q1GHh+qhNvHCRtYwsMq4Rcu4WaV8BtJeDtPwm88iXVmIT/DPi2doE+dPnsToeeiP+Gk0ojgc5KnFHwkcAzh53eHhJ+2xxg7pHXyeFbWh7jqw6UAP4v9uXUgnloHjmXnwDFdtwIYkfyU6GHJP5JF' \
			b'wxmF/4wbdx1VAbj8z2FecOYmEOT6nLteHjIM8AenDI5qzXMi2b+AjeuOJf8oqLPa2JxQCTg3l7H/60FN2D8LdALTtlUZ9ikDz9vektXZKauFC9oS+aBK7J+iuzsqcVsm1ydRC3cf1YKzdZdUoz9xek6L6JuvWIgXukLhRupCAnkh1k/TmnPDBQikPVGdx5Tp' \
			b'HErUzRLfxsqCVY96ekTlf4GWhCfVpUtevLNYmfyqTJejTGFVpjutTKF5Q3tBqxalSgaCkV+0zRtPR7Mmf7ZrE2/aDHpLgZOgkEegjWKNJQ+7/eEqXR9t+Hh2OqgLx/IF2geadoD2vRMhFEsY7UCq+NgXy8fg+Woj5+3uEQ90MpoJlPBGL0wlXaf+OD45FnU0' \
			b'RmxBOzjEr0RtyNrf9P7KvrI9f07JjqSkhscUHkiYN8LqFuwRDHLRCUGJ7u6PTKytrOQv/3bkj98RPhCy8hF6jm32LVPtbkg1gdRBwn0z948WQQz8mEy/lMzR0xknKSW2dNSmj/f+0aKNqXe0MCL9Mc1hl2Y5eneMbIsKSvcNU/cfmasOnCupm+5MSd4vPZ8f' \
			b'SZUWnRuZ/Pi8SD/KlfqMRnBINeVsRY8zFbHtPFnMN+Uv1Rnt4C957bphoIlgO18diKwfchAtF017RnFKid7kj+mNlyRK3CaqxcmfSKR4E6JbdWSeXR7iDePjoky5Pp/sEeSf0CFDqssQSY4/lYim1uFlSqlr4FpeG9g9Htl5fbKoxx0KVx9FWqkbM09gqa9z' \
			b'Y0c9scnXyJcZCC2d6XMydIXokon6xUkvdbErl76Jphl4HtdR3/ikCfQdinukcb6niA/XlbOEmTrffRfD0Gemo0GF6dfIo1tFGiLdNvfaobRHekSnl2gagTuHQxbDKtAs0DToeZ8dSnukT3Yjgd7uGVLpC7VpjuhoqHf6NbIaV8GGYMfmXjuMaI50+G4s2FSM' \
			b's4Sb5kmO6mgaY/o1cjzsET5U+aYZqvvsUNojXcSjyLeaC+A0C3hsR7Ny06+R8bUPKWJum3vtUNrLupA0y7Z4xHVC2kspdBLvmvmOpiYXhE507vrSpHJ+ADvW3qYIf2jutUNpL+ttXkv465KcrwhtczpXW2PsDQkerd1VaARZ4dxnh9JuH0Rpq5jCRTdS6raU' \
			b'vG2r48fJioSMsO6F02SEprd9v+65dwepWDZRez6cJGu4W3Ywx1nWGSZVuSmPslbM49UYnoVmviPTtkUf9D4Wc7/9oWC8Vwz3mK/qDvK1bS7SgaHLerWXwdDYXKQDQ0cs8c7E0Gz/NFnXHWIsVddndFT5zvVlBwYv66B2rZAz8VjN4bNqFjmyOF76zc2jBrdH' \
			b'DCfvGrdNc/EOvF7W+7xIXrvm4h14/bCsVmm39+WOl4JU/9eLZV+MM2MffY1yXDadetfLkRbz3AeHsrsoc9/Tl51p7oXDKpDlHdw7XXa2uRcOZbe8E32ny84198Kh7FJ/HRbEW3SHrOk80GJPfHtDO1D4yJ7EIcAtncpcl27iLIegcqG92hLP6TyzLVYi0Qmv' \
			b'Y6HbZvCP0GEnNJUWfxGb4b9WIoi9ZXq0z75QmiqGWtj2yUcqe14AYPqLVmUB6ejiUbHEoqN3BrvjK+w3zxFaSUrEkFbBkrgZsIcO8WDxjRy6pUzJm1RCPJRMQ8c8ZMwLDmncPBGoXfKVvhWdrSCrD8WGhjb618bxekTgLG3RnmIhHydk++KTwvxw9f8BZsca' \
			b'hw=='

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

	def expr_div_1         (self, expr_div, DIVIDE, expr_divm):                    return AST ('/', expr_div, expr_divm)
	def expr_div_2         (self, expr_mul_imp):                                   return expr_mul_imp
	def expr_divm_1        (self, MINUS, expr_divm):                               return _expr_neg (expr_divm)
	def expr_divm_2        (self, expr_mul_imp):                                   return expr_mul_imp

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
