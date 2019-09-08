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

def _expr_mul (expr): # pull negative out of first term of nested curly/multiplication for consistency
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

		elif ast.is_minus or ast.is_neg_num:
			if mul:
				return AST ('-', mcs (ast.neg ()))

		break

	return expr

# def _expr_neg (expr): # propagate negation into first number in nested multiply if possible
# 	mcs = lambda ast: ast
# 	ast = expr
# 	mul = False

# 	while 1:
# 		if ast.is_curly:
# 			mcs = lambda ast, mcs = mcs: AST ('{', ast)
# 			ast = ast.curly

# 			continue

# 		elif ast.is_mul or ast.is_mulexp:
# 			mcs = lambda ast, mcs = mcs, op = ast.op, mul = ast.mul: mcs (AST (op, (ast,) + mul [1:]))
# 			ast = ast.mul [0]
# 			mul = True

# 			continue

# 		elif ast.is_num:
# 			return mcs (ast.neg ())

# 		break

# 	return expr.neg (stack = True)

def _expr_neg (expr): # TODO: this is counterintuitive, something not right
	return expr.neg (stack = True)
	# if (expr.is_mul or expr.is_mulexp) and expr.mul [0].is_pos_num:
	# 	return AST (expr.op, (expr.mul [0].neg (stack = True),) + expr.mul [1:])
	# else:
	# 	return expr.neg (stack = True)

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
			b'eJztXW2v3LZy/jMFrg1ogeWbSPmb4zi3Rm0njZOLFkYQOI5vETSJUztJW1z0v5czz/BFWmlX2nP25RwLh2clURQ5HM48GpJD6sHrv/zTu19//EvzlydfPv/yZTw+f/rFN/Hw1eOvn758Hk+++PrxEzkoOep4/OzZyy9fpKNKJ1oy+PxLyuMl/3729K/fP3n8' \
			b'6ukrOX/xOMV+Vk7/Vk6/wumr549f/fNnsbR/ISryCUc/+fbr5/9OV/nk1Tdf0++3n8Xfpy+++ubfXz1lCr4lGv/2mG6+ePbyW6Lh2ctv/kpkPnvBT/Dvv35NqZ9z/b+ku198+5Jq/Rk/+eTLFy8eJ55QxNfP/vrP36Tiv07k0cnnnz1nComMf40/j198Racv' \
			b'P5dq09ln5fRv5VSq/fT5q6cSk5hGeX4DQiIBlOjF469effMlZf8N1/vpvz15nm5TW3z+7G/PPqdsnqAh5PGvnjMDImsSL/7t1dMnnODzZ198QemZ3G9fPmNRePzyc+IX3fiSnuciI49Vrx2E8bGMJ/8STz/+8cPHP998+Phndf4xnr998+Hd79+///D9jz/8' \
			b'/PH3Nx+q2/E0Ht5wsnf/89uH7z/+8du7D+ni13f/8f3f//j1bbn5Qzz95c3v3799/7OcfXj/3+UMpX189/Hj23z2Wz5L2bz5oZz+/nsu7e9v3v6ezn/jXBHdI+CXdPrzT/n0p19//490/ssfP3//0y+/fRhcp8sff/qznP7971VF6wfoJF3/+aawo5QuqdLl' \
			b'7+8+5Ftvfvwxnb7948PP/5su/ufju1K/Hz68efuf7/Llx5qYP9/l+v7x60/vf81lvsnp35YaMWszhe9Lln9UXP41k/TDT7++z6S+L7yP9GTe//Tu7bt8EWWnouC3j7+/T1fv/kvOMinvfy7Uvn3/yy9vehcf//Jd8/rBxtnGdg8bPnFbOrGGfmL09qFcxis+' \
			b'c/TTWB0jHvYicGXTc/G+S1F0yqk2OOrmgW5MvFSN8fHkYYqVuByx8XSiLX5caDa6fVhH6XYnynV1FJ3GM6Xx01IByD5e0SkVpPDjpA4qEqw5SbzhYypD/w9TTKivOjlSFJWoqGoqpKp1D1OsxOWIjeYHVGQfURI5bMNDidkorrdq6Sc0LVEqN1s+jWfcQE3M' \
			b'B6TIZTqv4hUOG66q5n/j0m1NJ5SvxKOQSJxEIpHhSnVSqbbLsRIXSrJtP2KjucUN0cN5Go0fRyQIiSWKmrPE0ikJZfxvG2oVtKqjE6ruFj8OD7DIcWW75gE1MzUKGBIjXHXR4kARVFCIcrdNbRajHWRe4jdO7UZVl2o3xeCSWrfbiRo+pPuXZvey98DGsOTF' \
			b'lnygvRRA7QbZTtHlcmO41iaKlA6N1g21VDxr6eGGM5S8x1MwNISZCWMz9hNuDAs0ybNvXBbOeINlWXnRGtI0G9vaVMpDN3N8ibGIsSXGIcaVmBYxbYrZKGYagwbOOvy4NlObo3wdRadUlUiHYUUyFj8b0Rk5pbMolrrkR/JiWNCc3JBGdHQD1Y95sbRKZUh4' \
			b'ubViE2ouTW3x05L6A6XUlk+Zo4SmCXFQ2RiHmHS54foGySayyjXWJ42qoyUiXjP1HX6icD2U66hoTNsWPy1JHUhiOWCSojg+iIKxQQvGqxYVJcjYZthPsuNMQgxGWnCRatXlFJoFiiVH2OoT92Lkg0q/6JJY26UrB+CLddM+nwU50yqd6HQCPAwCvQRhyJgA' \
			b'QqPqUeqZyAh/D1issqzSuwdZavy026yFxBA0pw34qd6iQQA6Ngr/MJqBKdROlgm2bbr5UC7jVbqB+kYO+y145hJXHaEH188RlkZhlwwIhB1LmmvTDU4qUekpjUoTBEcxiCbD6y0hZUxs0ZQRGGILGWrTiDVR4aP+bEnRfdt436htxNetiv9Ry7fxlbSNr6qt' \
			b'awhTHClfVLYuNF1sb8VNbqLcN5GzBAnx7aiiXHSu6dqGWN81UaciyPrQ+K4J2yaoJugmxHzpqdiGKiqOiknVlv5jrvxm4cguYsyWGE8v3GinOMKcqHERPSJcqNiAKjJPRTpUJERFSoJtOnqybYJrQvyNtMb3fsyhJRWiZoxUhCZ0TRfVoWsi/32kTjfeNN42' \
			b'PuZMBcQSIoBG66RlpYkv9Shc0R6JWhfVOoJnS8RGGrYRIuPb0NAbl2iJgaj5rnmwpZf56weR9SRjli8fRP6r2CYPYiPgrkY03vyxLejuazKt+NrRYW2tM7RWh/ZwaKbIXjSEb/maGEXNRgynZMz1GO+5GR9ohzZGY1Ku/DC3y8NV+S7QnMw/tJSRRrFyRFt1' \
			b'QRrJcXyPm8JHcHCMd+BZ5lWPRyN8AVMiVU7Ex7kzltmizA44pLzUW7Nsnq5cbVGu1icuR9pXAJULWnXuAjpHvF9ZfyG40wJ31q5NcKEmUEaAlsEdLAEzctWlyqmmde1iTS5bhZ4g1I1/ntdUJ68pzTgeH2l8E6vTrOJ6GnHVYvAa6ZcosXNtMg/aFUgu9Br1' \
			b'3DSKOn/UIaQuI/UPqU9IzRQbYWX8SRgftivjL8N4tTL+MozXK+Mv8fYNYisqGTni+mHMSPv1xXupTlQaQ9jKWAkbSd/x7BxuiLWkZMxBhpSctJ01a9NdpumsqFEa6+L3yafYjeKbLLoiqToZ9oI4ATIbwLCACYcHnZdUGO4OuOzSoAJiLWItoIqm8ZAjxsAD' \
			b'X95bxnYyndOCvx6mIhOn1o58xSivwCiPyRAPqPRWJlBEURN0MnbSiDiEyIG7rXCXcCfmG8GuiyXYu8yXKDnQxFbfx7qhlVu0aut6ynHPqgowbBkMUZ+6hne7bkGs0XYgo5jNBP47nWbOxApKRlKZ8NaY6dbr3PV5unGRyxpeBCvLz2Nwkj+U+AvE48rb2x0A' \
			b'bVc5Ptuc7ZYleO20XkLOA8M21WdtgYu0gNUr6y8GPCvrL+Ubp2C8EBO1+MbF48rrE4h5xxgPxqw+IQv7o47l8kyFjfjykvukE13h7uzagguZqhlqTuj9iZ4vFYAjHyzLDXliCc7JsMZ2ymn7O3HxxiIpHsXATTyAFDI7hMeypz6/xlZZmCELxCTi1cqjaXHm' \
			b'ni95AEFwjQyXG1mGwOtEmJeyQoSn6Vl8ZSVJYHkkjwo+6KQBeA2tLN+dMdNeeKSZ6ytvapVlA3Flg13ZQGxwKxsa8vJg40I6UYGZ8gky4jV5D3yqVbcehia/Vu99fcm5Q4v3g96ZGPQwOSacolSyvrFE5RIuMcUjQcMjQcMjQbPhpNJUjozGro7vFxqXarfS' \
			b'ECxk98BVQMEf7V7UxF9KeaXX3Zl7wcoHnRU/MnUvhJzcmfBmMPekPjJm1Np7Up9W6uPvR32INA0vJA3nI3E2op1g6DX9kHeUoUN8OxsZ9jMPMcBrMLiyrnm4xIpDx+y3WlpFDgqNQ5w1MhdlHsrMiSkbFtBcgFzSQStcKckNlxZpdECeYujx3Na6kPRUM1wM' \
			b'mA/QFVw5fBL3PtGVvDiXzky1bIg6LQJtJo0baxkv5iHNFddO6clg1Cr8J1spB9kPAPig09tCXg5phRZV36RRfDM1GkGxBrEGsfzWQGTAVYAqWcnPckH3foSHh3bMOvvR73vKgISHkeEhJ56FJ3eMcUX7rojPAiSTZ/K+4xUtMFBamaDGwGEH26SFWLfIuYVY' \
			b'tj7brVbsVpsmBWFHWdhRFnaUTfaTXT2Rb3tPFzAZDeLSy1VApEy9ivUZ0BSRJDs9HuolS4NDZEkaheSHrM0LouzD9GK/D922+G4UYXbJUoEwOwizgzDjYHBUWh7CbY/oyDO3vm5PtocXc3e49gceNeuo+PkxyInCBNoJG/vbtfSejg/S1qLlxeP5BilJCyWh' \
			b'ZE1u1PaTnKljyTXgnxdI4aORpW6my5ND/pPk0GuSGA+J8fwqgh9cXqeb2Bbw8oMjEW1nG3FAkfccbXuQxJD4GCCFAXkG4TbenbINLj/Lx+R9h70TmJjuU20H+4lWneXDJvnQIhf6YS1W9AKBQPFR8TAicW3bvI7P8I5xNMhHu8Z1XCPD+M7vk1iu1ILfJvQq' \
			b'wasL77OKTDAd7zEwqubGkMeWuRtKY+DVB9ZQQ1p6xTFvucot3lD8QrLAcFYkjZrSPgu0uwLtrEAbEdMuxLTalpqLtqmlZfG0ipyWkNOKa1puTWutaS0yNTDtTUDL7olZxCiSDnJ2pRFv2tuKtlmiHX+orWgfCNoEgnaAoO0eaBcH2sKB9jmgdiG66d1My8No' \
			b'vcCW9naPDKSlAtSXoX4MC0eMJ79O3pU9xpM3HS1HJZyI9dHkKGHpbRz/221sMHyxg7fTb/C1Adds5IMI9G0NT1u0b+kjGlva8Nw3vLd5R3u10wdCaM952vBeUwragb7j7wM0/NWKQHdpy3hi84asANqVf0Nvf/r0CT7IoehjEpo35Oci4zORGZuOEtKO/4H2' \
			b'39cNNmyPaSNnNpErm6h3G89fpqBvWnD+nrfD5630aa99fHCAN3Pn/eM7hyp1RFq877dCOO0zTzObmyggG/pgCG3mz58L2PI+7g3vTc+75vOXJuKjfJPo3RKtgb/cwF9J4EoQSy1/14E/YaDwLZX4GNEfIwJRwDxl3nFVO/lWCuXj+JsmmygQm8D71Mf8+Zsb' \
			b'zDBiSLxLHw+gLfbpsyz8+YiYV9uhIJJx3qzfcin0T/vYxxSeSuRCuHXpP97x9jvSYtLdnt6qadW1BVh6OmyLWdrT5PY2lTmDHAZFDui2manfd0G3zYh+qwM67ohrO2rtZii241SxYLer3q4o+KiKu1MrOZdrLB/xd1DV3Wxlv0uKTqUNld0dUPfmH/YR4b17' \
			b'RIjvQzyY/2ND8zVxNiTdz90yLzaKmCB99acOoWIESL1P6ZJ2CQdsz4aaCwKm4MCotZUxoTZ8ZKDUJ0uNLTjZGoTtKgfjiyom24QUcwimUOnF1jiyrbCknq5Ofb8RI5xMLcYZP8CaVjDGjOBKjKdtezKuEPf9AF/0AVyJz9N+UeSncxBjtjNwpqtwphWs0QO8' \
			b'iWljvQruKLZoN2zPAmxIp2mgYcto0/H3XXAwTU4tyWnAoeNT3cnNHAh5kDgw4KhiUXTdcryhZyIVdKgRp+tK2EEfNR26DjV06YytI93Lr2RM8pkvBKw6ZoDierXbdF+Qix+yIErj4HCQ2ldABsYrwNYAsoSVgleJsTVqab8Xq4RmGpg/DFvcREAuELkLXEKC' \
			b'QxV9kNwr9JISM4a16hG9K6J6PmLBifL7KFaIgMxkIMudKjZixIK5I/gl4GWhCrcNXitwTQCXahQMJSJXiaGUbCSxj3IiSaJylO7kLAfGK1Xhlcp4hWeX4RU907FY9/CqV+IOXql9gcCKSecqM2SPJut6lao7USqVm4raQDYZq/gG+NSioFZqXmOV2oNVwlnB' \
			b'Kil/AVZlmmZhlcpYBaJGsErYhir6ILlXWCUphlhVQZQd2Fp3GZ9Wy+qsAEUMgJraCXRKKSSJylHEcNsLjE62Qidb0MkegU4W6GQH6FSXuINOdl9gdLLZjhpPQw1TagRoAvkKRValAJsssAn9QD6gmFbqXWOT3YNNwlfBJiFgCTYlmmZhky3YZCewSZiGKvog' \
			b'udfYhBRz7Ci3gtQKUseBFFUSCttOgFRKIUlUjiKGt73AINVWINUWkDpiiImeIU61A5CqS9wBqXZfYJBqC0iNpqGGKTUSkGoFpFqAVL7PotkCpFqAVAuQagFSg1Er1e4BKeGrgJQQsASkEk2zQKotIDUxSpWYhir6ILnXIIUUc0CqXUFqBanjQIqIhsL6CZBK' \
			b'KSSJylHEcN8LDFK+AilfQMofAVIeIOUHIFWXuANSfl9gkPIFpEbTUMOUGglIeQEpD5DK91k0PUDKA6Q8QMoDpPwApPwekBK+CkgJAUtAKtE0C6TKWDqIGgEpYRqq6IPkXoMUUswBKT89tH63oKoMqq9odWa0ImKguR3Qio7O41BhVkonCVWO0p2c5cCY1VWY' \
			b'1RXMOmIsXWEsXQ3G0nsl7mDWDlFDGp0D9TpVfiQNt1CulMBWJ7DVAbbyfZZRDKQrDKQrDKQrDKSr4UB6twe2hLUCW0LAEthKNM2Cra7A1tRAujANVfRBcq9hCynmwFZYYWuFrZvBFmWG8XQtg+l0hD9bDVs5nSRUOUp3cpYDwZauhtR1GVLXRwypawyp68GQ' \
			b'eq/EIWwNKNoNBFtaZdgaT9P1KgXYQg2k1Koghi2NMXWNMXWNMXWNMXU9GFPXe8bUE2sBW4mABbCVaZoDW7qMqeuJMfXENFTRB8m9gi1JMQe2uhW2Vti6IWxRRtBcLbCF7iEfKthK6eSochQVq3uBYUtXsKULbOkjYEsDtvQAtuoSd2BLHwgMW7rA1miaTtWV' \
			b'EtiSeUBxqiz3GbY0YEsDtuB5xQepeg1beg9sCWsFtoSAJbCVaJoFW7rAlp6ALWEaquiD5F7DFlLMgS21XR2wVgC7LQCzJCeswzJNSEcCMMsAxviFNOLSK1OGWqYM081OznJgGKumDHWZMtRHTBlqTBnqwZRhr8QdGLMHAsOYVEAnLowkIyQr9RIkk4lDjYnD' \
			b'cp+RDBOHGhOHGhOHGhOHejBxqPdMHCbiBMmEgCVIlmiahWRl4lBPTBwmvqGKPkjuNZIhxSwkU0AycJHk2CeY6mMUAdTB0XEN1Se1zeoJtWT1gXqQyHfNWQL7y6/OsitW3xZWk0igj2ykj2zQRzboI9MhFsIH0+TUklzlKJGuKhBWm6qnbEpP2RzRUzboKZtB' \
			b'T7lX4hCrBxTtBsLqVAGduDCSrOvVC1htpLNs0Fku90lYDTrLBp1lg86yQWfZDDrLZk9nOREHrE4ELMDqTNMcrDals2wmOsuJb6iiD5J7hdWSYhZWmxXJViS7LSRzJAysw7LGyGCFER9aPmiLg2lyakmuchRJl+sFRjJXIVlZY4RnFyKZA5K5AZLVJe4gWf++' \
			b'Qn16j7h8lqDMjQSGslIxgTInUIaFSuU+Q5kDlDlAmQOUYfUSOF1BmdsDZUKcQJkQsATKEk2zoMwVKHMTUCZ8QxV9kNxrKEOKWVA29KpdoWyFsqOhrCVJYB0WFzY6EpS1gDIMAvLBNDm1JFc5iqSr7QWGssqdzRR3NnOEO5uBO5sZuLP1StyBsvZAYCSTCujE' \
			b'hZFkhGSlXoJk4tRm4NRW7jOSwanNwKnNwKnNwKnNDJzazB6ntkScIJkQsATJEk2zkKw4tZkJp7bEN1TRB8m9RjKkmIVkQ9fbFclWJDsayTyJAeuw+LnR0SHWsYwwknkgWUotyVWOIunyvcBIVvm8meLzZo7weTPweTMDn7deiTtI5g8ERjKpgE5cGEnWqbpe' \
			b'gmTi+Wbg+VbuM5LB883A883A883A880MPN/MHs+3RJwgmRCwBMkSTbOQrHi+mQnPt8Q3VNEHyb1GMqSYhWRD/9wVyVYkOxrJAskA63AQJAtAsgAkC0CyACRLqSW5ylEkXaEXGMlChWShIFk4AsmwiQUdekhWl7iDZOFAYCSTCujEhZFkhGSlXoJkQZAsAMny' \
			b'fUYybInB98Cr1uEgta+RLOxBMiFOkEwIWIJkiaZZSBYKkoUJJBO+4eBT7jWSya05SLbHiXdFshXJFiEZNT2G/K0M+VsM+VsM+VsM+VsM+efUklzlKN3JWQ6EZLYa8rdlyN8eMeRvMeRvB0P+vRKHSDagaDcQkqUK6MSFkWRdr15AMitD/hZD/uU+CavFkL/F' \
			b'kL/FkL/FkL8dDPnbPUP+iTggWSJgAZJlmuYgmS1D/nZiyD/xDVX0QXKvkExSzEKysLtBxj0As20Pz06ya8YKaXuMM0tSQcocDM62LCdsn8HpxMDpxMDpJD+AZGyfyc1OznLYpDyTfVacTswRTicGTidm4HSijKmK3DHQ7IFAe6KRjSaVYEawmTaWmM20Uj0x' \
			b'08T3xMD3pNxnMw2+Jwa+Jwa+Jwa+J2bge2L2+J4k+sRMEwKWmGmJpllmWvE9MRO+J5KfQxV9kNxrMw0pZoFbt4LbCm63bq+11PQMbhZnW94amE02TAhYTAhYTAjkB5CMTTZJ08lZDmyyVRMCtkwI2CMmBCwmBOxgQqBX4o7J1h4IAU51qQ7MBzbcxhKz4VZq' \
			b'J4abTAtYTAuU+2y4YVrAYlrAYlrAYlrADqYF7J5pgUSfGG5CwBLDLdE0y3Ar0wJ2YlpA8nOoog+Se224IcUcbNOrh/B+SItcMfoThrYwAW/bOR7DvsEupThscXSIdSxL7DGMaYKcWpKrHEUE+F5gj+FqmkCXaQJ9xDSBxjSBHkwT9Erc8Rj2BwJ7DEsFdOLC' \
			b'SDLyGC71Eo9hmSZQvKLUgYCqTHgOY7pAY7pAY7pAY7pAD6YL9J7pgkQkEC4RssRzONE0y3O4TBfoiekCbWzmIarJ3sNBSqk9iJFqFtKpFelW4+2WjDdqX+i0k8VcDou5HBZz0SEWwgfT5NRyVDkqFo6zHAjZXLWky5UlXe6IJV0OS7rcYElXr8SdrbD1gUDI' \
			b'liqQuTCSrFN1vYBsTlZ1OazqKvdJWB1WdTms6nJY1eWwqssNVnW5Pau6EnFAtETAAkTLNM1BNFdWdbmJVV2Jb6iiD5J7hWSSYhaSXeNKgepjJCuenRTP1KnWd7WNRodUS29Uozeq0RvV6I1q9EZzakmuchQV3vYCW2tVb1SX3qg+ojeq0Rvlze+J+wbARnY6' \
			b'zDbOVoGOXbutPRDYbpOq6MSPkWRkt5Uait0mPVKNHmm5z/YaeqQaPVKNHqlGj1QPeqR6T480ESf2mhCwxF5LNM2y19ALyDbbRK808Q7V9EFKqG01pJiFcOsKgk8T205iqxlqX7ZSjNhqBraaga1mYKsZ2GoptSRXOYpsNdMLbKuZylYzxVYzR9hqBraaGdhq' \
			b'dYk7tpo5ENhWkwroxIWRZGSrlXqJrWbEVjOw1Qp3yFYzsNUMbDUDW83AVjMDW83ssdWEOLHVhIAltlqiaZatZoqtZiZsNeEbquiD5F7bakgxC8nWBQQrkt0akjlqWdZhWQvlsBbKYS2Uw1ooh7VQObUkVzmKkMz1AiNZtRbKlbVQ7oi1UA5rodxgLVSvxB0k' \
			b'cwfCppwlJBtNRkhW6iVIJkuhHJZClfuMZFgK5bAUymEplMNSKDdYCuX2LIVKxAmSCQFLkCzRNAvJylIoN7EUKvENVfRBcq+RDClmIdm6gOD+IRlGl28f0ewEqoUBsoUa3VpqatZr6X869D8d+p+yR5JD/zOnluQqRxG6tb3A6Fb1P13pf7oj+p8O/U83mA3t' \
			b'lbiDbu2BsHEuV0AnLowkI3Qr9RJ0k16nQ6+z3Gd0Q6/Todfp0Ot06HW6Qa/T7el1JuIE3YSAJeiWaNrmKh/EuDIb6ib6nSmrTKAPUozAHMdV3JwHdre8B7i7DMadcKu3SyGbOYBu57DRaLci2rrGHXLx6Ki12adBNtgdbgeeU0gSlaN0J2c5sE9HvbWuQnTy' \
			b'6zhie930aUw73F+Xmrb633Xu2KGuRym5dZQNdsfTkEMHnyn5rqYQL/MDVvbYTRSwtBrZY9fIJrtGdtk1ss2uGeyza/fss5v4LH4dwuIBnoGmPb4dszfatdholxXOTOy0m7gX0CB80PyR1ZhsYLlJ2gxmUSoeYbNP/wj7yxUwGy4zuCGY3QzJzo5eCblCs/+D' \
			b'veeyuy7Ve6RGwDhYa8bRKKeQJCpHxQJb0wuERm019tWWsa/2iLGvFmNf7WDsawd4BlQMiYqVbstI13ia2BBVLWBB5TrP+qBvu2c4KzEMsJJKWWAmpZocApS2jGRNfrw35RXA2CBNU8GIpBjYRIwaw626V9T4JFHD0dwua5ObQI2UQpKoHEWo4XqBUaMaZ2rL' \
			b'OFN7xDhTi3Gm1h1CDbcvMGqUUaXxNIQapRY1ari5qLFn6CgxTFBDSlmCGlKTg6jhZqCG5BXA2CBNU6MGUoyhxnCn7BU1PknU8OQLwtrkJ1AjpZAkKkcRavheYNSovD3b4u3ZHuHt2cLbs/WHUMPvC4waxbdzPA2hRqlFjRp+LmrscdxMDBPUkFKWoIbU5CBq' \
			b'+BmoIXkFMDZI09SogRQjqGGGXugXRY11rOWOzIfFyrQYX2knxldyCkmicpTu5CwHRplqfKUtYyvtEWMr9AyhzGBopVfiDuLsENVL7hxI16nOI2kIcUqNKsThUZUWoyqJLSrgGYsbYFKLUlqpdo1Fe4ZTElsFi6T8JViUaJozmtJ2GZDaicGUxDNU0QfJvcYj' \
			b'pNjzTW0z9BlfcWnFpcO4RK3EWofDCC7lFJJE5SjdyVkOhEtIDFyic8ElPLsMl+iZDhnXuNQrcYhLfm8gXGLSdarzSJrYMFWNhrjEhebbJJX8jMUNMKlFKa1Uu8IlXI/jUmIrcCmVvwCXMk1zcInbBrgEonZxKfEMVfRBcq9wSVLsw6WhB/iKSysuzcAlRa3E' \
			b'OqomcCmlkCQqRxEuqV5gXFIVLqmCS+oIXFLAJTXApbrEHVxS+wLjkiq4NJqm69VoB5cUcEnYQrikgEsKuKSASwq4pAa4pPbgkrBVcEnKX4JLiaZZuKQKLqkJXBKeoYo+SO41LiHFPlwa+m2vuLTi0gxc0tRErKN6ApdSCjmqHEW4pHuBcalaQefLCjp/xAo6' \
			b'jxV0frCCrlfiDi7pfYFxqaydG0/TqbpGO7iE1XOJLYRLWDrnsXTOYzTJY+mcHyyd83uWziW2Ci5J+UtwKdE0C5fK0jk/sXQu8QxV9EFyr3EJKfbhEnthR6xpInI0kSERobpqNxcjSEWLdABWZgyvtgmyzBhqbRNwmXO4/EQuHUSwrm2iPp9kZ5djoCymc/RO' \
			b'IG7bCtpiPDlzMMRZgbl2AupiusiL/ZCnZroKLYC+bTcT/vyxi+9I4KPw09aRtKU3f54hSj3MtU2sY6BHBB2pLTNEdl2GyQ0JMOUkNpyW+Tg6di0faNEcUed6YYN9paQIzXDWMXpuqP11mabTR0zTJTcjPZin61EwxNANeclEudsYO6S2PORwIPHl4XZHbOIl' \
			b'e6PJO1VXeQiqGjN5iQvCy87iBrjZCrHCiApUN7R/MS1BdIRh6T4bW8SaALQlHOTvzg6W9CFbw+SUnbQSpTX8bkPCYL3fNynXY9YqPw2KD43yx3+TmQ8G+SDl1Gv9kCJDsnvEMfQb0Tn+es+/geM1RTFOu6gJQ5SewueWYJkwGYAMBK7hl7F3LvCOThkyzBKc' \
			b'WgJSRlFGyhod50z3DZBvEvVqxBsi3TEId8igm4FmjGJhgF7ZcPP7EOswViXdMwxPCZsyGI0gUYKhozFo/5RfApxNWmXSAU423bB3OGvybogJ04BQg8EODBwJAIe1fp66k6KTlvdVPCk3qW07orZ7LKszaG62kdp7rL9bN6LDS/T3gMmxSTsJ3zUlLpYDtdUn' \
			b'oszU/LsKvVyZ/YJ3sD2vMlddHdFqd6uKHclSkSgVqVKRrKtR9Bu/qA8p+mElT12Ka1V0JrD+d6lf0N624jPubmlcM3DP8NqAYAcENPFoGRA0/4hC9iiSyWZ5WGaW+0OQ0N4mKggS+IIE6n695pP2q27Paz4NOMQ444EEkfHaqgEibHlFiXbUR6OeHPVufb0S' \
			b'M/6rW0EMVrD0cYH5iKHOihoZJUJGCRX8fTUR8iY+ZrvPRJDvAmiOJCJ5+0VuoaEPTRnJotvc2kSV4s+i2DyLTRearYvu+B6+nRhmvXUoERzZ0iBpO4Ilc718L4Un7Yyug5/ZdTAntSrGLQpbY0T+8sjFLItB94HbJoxZE/IBkWvHCWrwOd0JO7M7oc2BLkUU' \
			b'k6sa1ptQ90hRrBGJmeKpoXOaEWNzG6cwJeI5zQcoOp8zepDMCj8CA8l8OIHZcK2djB0oIAXkaaiN4k9MmHMPL7TnNB8oEeXBb3g1Bx7ElMhmxNB6CGIwDMyE+Njra0GL25oEuOKeBfPz6LGFouphe7c1/ZYH/+9CR0DdaPC/+Yd/FPGdBgniQ9esspH1N3ur' \
			b'X6P6zn2Lz1TfO/+mnnpLK/YSudnb+XqVWeo26318aPQ/Fn6UFrvzKXK4BRN9rhvSPoVuTzSp116pYiv5PPvVaTebpLdigdc6nj+wvlzRyU3uhNN8bH3PN8EPqrw9TuXb86l8pe5E3UXe3ydS91XVFxjifTWn9rjg6/ykWn67Gu6O03B/GQ03q4avGi4a3q0a' \
			b'PkvD2+M0PFxGw+2q4auGQ8NJvVYNn6Hh/qqH1+7NkNo1qfAVau8tqSotprqOwbObqmbzD0XrDSP08CB4uGotjZzP09xn0dipZXunnNpeNXjvcBlvnUSz1md87V5kmvoW3rndRbV5cgHwvvevHyzcvdb38Jz9BuZ4vW8rv9d7p9VYa93/X/Se5gd6i1yvfrpr' \
			b'3nrVeSvXuPrsyTrmfVJNYptHEUDpBR7rvKr8qvKXVHm/879Q5f2nrfJeVN7NVXnVvA47uxVBvzVrNjYj8n1tZlWGRvZ36EkqM6YqWF2wI9osxj6KbVAiooP9byqpJGZCGgNkkMVvRPSy2OUv5tVbvqQ2HG06ztaMcBkMZRe9yIaj2QZQE+YxlgkuTW51tI+Z' \
			b'E1iRmYphp1vmKpHL6lh9j1Dy6wasVnPZPSnYNdvNDdhuxzlv7x73+Ts5ZqIF3OlbwR7fClPv+LpR/LLX+RENN+t1PNm426offbpG5l2G+v/9V2HV8ri58JV3nIDMfF1NyRFTWrqeuv8ycnMF64bDQ7W0HTEStFjiTrj6ef+IztGSucCiw0Kl2UMzNWAdOQiz' \
			b'XHJPvFHIgUFS1z2KZi9LeLtK+FVLeN94PG7w8VOUcPsoYgNLuF8l/Mol/ObD65+2hId5En4b81jnFvITb9WSBX3qI7I3EXqWuRPPK40IvsrjZicSfBRwU+HnXA4JP+2QMfa91ckvrbI+dKs+XAvws8RfQAf0icEfBdxYByiXY18AI5IfK3tY8m/PqeGcwn+m' \
			b'vbtuVQG46c/lYXBmE4jrdraNLw/5BrQHZw1u26HnVLJ/4b3rbkv+WUbP72ZzQiXgAs/v/7ZYE/ZPBJ3Gu21Vhkll4NntCzqenfK1cCW7Ih9Uif2TdHdLJS7hdX0StWjvq1pworuiGv2Z0zM7Rd980QKrybUtUriRupAoX5ED1LTm3HANAmkPFX6FSw4WK1Ge' \
			b'Jb7Q4oJVj4oekVBfqTPhSXXpWtfvLFamdlWm61GmsCrTnVYm37ym7aBVQKuSz3bHN0LzuqUPxsZ4+LVtOZr2g95S4igoFOFpr1hjKcLGFPH4YMNfYacPdOFLYJ62gqZNoNveFyEU71XM+fNnXxx//85X+zir3S880FfRjKeCN3phKVGep/44P/kW6miO8glS' \
			b'NZG1IW9/0/sr28raOp5LsiMlqeEnCg8UzPtg5fV6+KyefMruO1oSUf7ILdzKQv7yb0f++B5jg+FzXiQfaWJJ2bgbUk0AdZDwCLYz/2gNxCCOyWwXkzn2WcZJSumrgpna+PzeP1qzMXWP1kbEP6bZ79Is39sdIzsCHtXd9D1T938kVx/4niScLPhbkrxdelrL' \
			b'RN7G9L3IGMffifSjXEnfZgR3VFO+qdjiW4rYdZ4c5pvyR4AVBn9Y9jr+P0y7P/V4DvPy76cfKYlbLZxR0rrmRn9Mb3dNUpY35k+S5k8gbbz52EUDeW2Xi+4mmXEbxiqfT+joNXDCgAqpXCHaZqY9lWxGO+/6xNM1CIHXCubLWw6tOVnWIwGtqm9FTKk/M09S' \
			b'qeNz40BdssnbqJcZSCt94+dkeAqZJQi5KrGlvnYVIn30zd3tCQN1kE9aQBXQziMm+p62PfxanCXF1AXvhy4MY2YGGlaYvo06ulWWX9O3nO9tQDOPdIhOL8o0AHeOgCr6VZJf03jnvQ1o5pEO140kebtnKKUvzaa5xUDDu9O3UdVulejXMcP7GzCEOdKbu7FE' \
			b'U/vNkmqaGLnVQHMW07dR42F371MUbJqOurcBzTzS/7sVwVZzIZvm+2470Nzb9G1UfO0gRt7b5v4GNPOy/iFNpC0eOZ0Q89IEWdRdMz/QrOuC1JHO3ViaN04XYMfalYzN4Jv7G9DMy7qSR0l93YTzNSA0pwu1l8XelODR2hdtXpN3zb0NaOZw75tZkXd650aa' \
			b'25Ymt6H6pDi5hZBX1d0PmlzK9LYfl697ZxCHZXOr50NG8m27cIBzzbKeLunITXmU1GEer8ZQzDfzA/mPLXqg97A47u1PBVe84obHfFV3kK+hucoAhi7ruV4HQ7vmKgMYOuJXdyaGJm+mg7bMFGPJD/iMgfx2d2PJU3fiCTB4WV/0uhismisOYO+I3+Mc6+5a' \
			b'OKybRYFcgJc+c7MALi/rWl4dl21z3QFMPtLP9FqY3DbXHcDkZbOUd9mZlzbAXx6wMqb8H5fLvhzn5D56Dw14VX6yJ21AWtV05wOWVCzvX97ZRrPN3Q9otOWd1zvbaK65+wGNtryDfGcbrW3ufkCjxU44HKW36NVYmyNggNM3pw0xacuR9GE2uREt87pZFVzX' \
			b't9QgtMkXLRUj918pyI+n7prBP1KHndTUTPQEf3u2/6+VwEZXLU2knfZk7p2+BVRL2T7BiA3PCxxsf5GuLJodXTArXmj0+ZHBJwEUPnPDGTopSuSP5o9I1gzYQx/h4DF1GkPnsXNeSkmTB/Ep7WKsdDvpuxGyrlKchegbBto4XmkpFXZ0zjk4Ia4tMTHNdw//' \
			b'H7BEJmA='

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

	# def expr_mul_exp_1     (self, expr_mul_exp, CDOT, expr_neg):                   return _expr_mul_exp (expr_mul_exp, expr_neg)
	# def expr_mul_exp_2     (self, expr_mul_exp, STAR, expr_neg):                   return _expr_mul_exp (expr_mul_exp, expr_neg)
	# def expr_mul_exp_3     (self, expr_neg):                                       return expr_neg

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

	def expr_mul_imp       (self, expr_mul_impr):                                  return _expr_mul (expr_mul_impr)
	def expr_mul_impr_1    (self, expr_mul_impr, expr_intg):                       return _expr_mul_imp (expr_mul_impr, expr_intg, self._USER_FUNCS)
	def expr_mul_impr_2    (self, expr_intg):                                      return expr_intg

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

	a = p.parse ('-x * a!')
	print (a)
	# a = p.parse ('-1 * a')
	# print (a)

	# a = sym.ast2spt (a)
	# print (a)
