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
def _expr_ass_tuple (ast): # check for tuple assignment and reorder if present (assignment will be inside tuple)
	if ast.is_comma: # tuple assignment? ('x, y = y, x' comes from parsing as ('x', 'y = y', 'x')) so restructure
		vars = []
		itr  = iter (ast.comma)

		for c in itr:
			if c.is_var:
				vars.append (c)

			else:
				if c.is_ass and c.lhs.is_var:
					t   = (c.rhs,) + tuple (itr)
					ast = AST ('=', (',', tuple (vars) + (c.lhs,)), t [0] if len (t) == 1 else AST (',', t))

					vars.append (c.lhs.var)

				break

	return ast

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
			b'eJztXfuv3DZ2/mcK7L2ABpD4ln9zHGdrNHbSOFl0YRiB4/UWQZPYsJ20RdD/vTwPvjTSSKO5986LsHzFoUjpkIf8PpKHj5tXf3n55Juvv3nxl+Yv//Lut3/4W/j59dOvvve3bx9/9/TF197x1XePn/Ct47vw9y+evfjmebh3wSH4BV9+A+94gX+/ePrXH588' \
			b'fvn0JbufPw6+XyTn35LzW3K+/Prxy3/9wn/t30CK6EDvJz989/Xf4Vd0/PDVDy+efPv34IKA338Hf3/4wv99+vzb7//+8inK9ANI/bfH8PD5sxc/gFTPXnz/VxD82XOMgX///TsI/TXmyDfwlF/7BcZ88s3z549DLoHHd8/++q/fB4G+CwKD48svvkaZQYx/' \
			b'938eP/8WnC++5IwA1xfJ+bfk5Ix4+vXLp/Cp7549h/uXz/727EtwPKFMfvk9SvTt15gUn8iQqv94+fQJBvjy2VdfQca8eIYKfoICPH7xJaQcHnzzHX8waAlEprc+8en7PtxBy88ff/vy+28g/veYv0//4wlkP3r5vO4KDbEC/Lue/Jt3fvr9p09/vPn46Y/M' \
			b'/cm73775+O7zj+8//viPn3759PnNx+yxd/rbGwz27n8++CA///FrcH/6/cO7j+HHb+/+88c3H/8zPfvJO3998/nHt+9/YdfH9/+dXPThT+8+fXobXR+iK7zmzU/J+flz/Ng/37z9HNwf8K3k/ftvb5Og//znhyRNFPqXn6Pz598+R3l//f2XH3/+9UOWzPxF' \
			b'WSKjM70S4oIj/P787mN89sebj4Ng4efvubRv/vGP4Hz7+8df/jf8+J9P71JKf/r45u1/vYs/P+WS/fEuvuv3335+/1v86JsY/m1KHmZyTMn79Mrfs/z+LYr008+/vY8pep+04OWJWnj7/tdf38TIH35+9/Zd/OHLVybQh0+f38ePRFVH0d7/kqTHlxY/PmUx' \
			b'f/z8+4df4lc+UczXzaubje4bo28bchhwKAt/XKPkLf/0v9DV+z+mUbrZmNvCg365EM9H6IMXODHUxqKPaW5kI/07ZaNa77iNvuiXPDYYT1j6o/1HBb00eIl+y0ub3Auc3tVp+mO6ZtPR6/0vcHoXRPQiq2bjbun3BtMqvDAoiKY/hhPkIyrMpU41Nz51nYH/' \
			b't8Gnz391LTvAD96pIO1dz2lX4jb4sl/02Aj6hs/RDnLTNkbdss9G0Gt7+mNa79Pdshc4QZeY4z4NpBn+GdyZv6DbhhSP/6ULjxU4/F2y/y392Cj2JGlRoaLlRFkZfdmvSx5d6bERmNXSf1+SAB390RTEuzYKJZSG/mgQnfLX/9pIVKGGV/fxgY4PlKI/tr3l' \
			b'n15/mFGiuYESAJrhfPU+Jv9l+Q5eENc/lz7pmgLEn3roFTRZ+qvtn4OYIz9HvAYSmO2fRaSNkploqZCzEAMPPfQwmYcvFTeyZRGgLtrCO/3cSKx00hdP2TXCFzHQui8Y/uZfCD9IvokQgEP+A8sCerWXATcKKwcgka8asSRDRcUHvkxSFQTda18HTV4T/cPo' \
			b'n3w0+djkY8jHJR9LPn3w2Qgst1AsJZVgQX8g/4K4wUvlXuAEl6U/m1DtyAkuRcU9RIHYBOD8gPUPr1WIBl66GyzKDH7+VR0pyVdcKuiS/hgvXUdZ1pETM3LTdcGBiek6yEUVMJxSDZ7oFX63/E7/ZY/MbShJhX/w8R5Y7CT98UXsln/7aoth8D9kLEUBB2Sw' \
			b'pD8acJHi+F/ghBzwD4VGofmnJfE9YHRdZKBQsvw7GJsQ1InyoLyIGMJicYPyz7nvn3Mme88bk2of/jTp255BMKclfFdGV8suoYJDBwdRhi/JAlTXoRKil8SKMPRKP/0b0NXRHw3MwMjcoRM+0jYEwP4DN0AsiYH8F0kioemPtrGOC6r9kChBf1KDAPAZ5dYd' \
			b'/UFdchZ06ARXGx7e8k//KzwgL58gqzDPPb+xVkDHGj9s4AUmvgAo0OALTBceYFD24ljaUqIB1HxE3/p51Tad13Xna4T/lMc8hSgJiNA1Hg89Avri4UHNI0sPqOFrtlON057arf/vfNTO/xf+v0eV1ofxZdnLqZGX/ae7FsJ67lVYhrzDx/OXj+kzuRMQy99b' \
			b'X2v8F0Xja6Sv0M40zjbONc5/t216/x4vRCcBtrxbwffg214gBxjoE9V50TuQXSOm+YIKEQDmPH5BGv1rO5+kToLbNj183b8Pokp4v//tP977SzU9CO3D+4zoXdN7kO2Ben0F6k3T28b6yzW2b5zPj65xonH+Uz6NHRQVnwMd1G4PJkb5xqVvVvrCD2hses/F' \
			b'AN/WE6yvjZ6adWNBAT6ql9NTt1eSzxjMlwbyVkAj1Ttvocr6kF5tN6Av8PA687dXN5Af/ifkANxaCqX4KST6FtkMbz0+fQXNTfzt4FZ1fSK6vulJaV1PGm5ZW14TWAQE6daRTlEzeHccreu4qAi+Sw6g+UWoOO/jqDgIR2UmvC+EQldFhBMtJa9uNOqtyEPO' \
			b'Pcq1kfzifIr5U+ZLmRdjGcHp96XPMLLo/phCtFzkWyrJiImQNQKrygNKIixJIvRDf5hTHiq/ELXSnnKlJXCu+jlN/dygcNieslVPp6wnIQP0o8JilmFmxazhLAk5kafepzam7OgpSoVnpMAch1wha6nhCL7UXUDsgkEP/9HGJ7nWgOPVgABUknsF2InDtk9f' \
			b'ket09ea7ccgsnZei82/vNOSB94IkQhdM1Vp1VO24qp0T1k5ftXO62unbqp1T1c5NzwM2mAE4LBgaDJ2qfdJT1lynRBjZZdUpapGD1ZkeqNAI5Od0C+O9ylT9nrB+FY2/o2UHUBR/Hl2w0+ySUm+HRSIfNluQbQt0Gp/edJKtZpKHZ3syifRUT3rFtjTB9Uqy' \
			b'5UTy82AR4fqk6G0922cUxdKCq5nmWCjIlavqpucct2SdstSsBlsWWCzrOMzynLRc3ByVPkdl1AUrIEM+WTzAAECFVrMFWDPtGyr5hoIbKtFWUm2COgPJ9+Jg2twV5OsrmKmCeUEWFKuuOi+omhqiIkPIZvVUloSKfA1ZY6neWap31lxzMbFhSgHbV2PqybTF' \
			b'0GMCIfIUFYaqOGTfwTzcOtvodJukOJ1I0DwiUWcGnZBeJE1Xl6bq5YT0AhPpBE/Z8veqgCOMDKtaI05KIZDLgqch+ntVxNEU0SJncMbVeRL3ME8CUb82Zk+1BjhsLcE856qmE1aT0lU/p6yfrq36OV394HoN7IRoxLljseHIohIYhu65g4QdpdoKuft8F9gB' \
			b'esiVBzQUAV+kdj6NGFn61QpWOFvgppccveYlTTC6ITENtTwcrh3ZUf6TvYfNPWwy4pU7NNQfJoFIRI2a54fUCAQ5mOBJRZ8NxDgZCu3HYXlSF0z+sQLQFA2YfYhvoBf1DOigFNBN1cn+OoFXsTYYXGrm7TPfAvKs5tNsPqmaT4vySdd8WgBaigYsesfQJalt' \
			b'l+Y1tX2YzKkHT8gy9AqmOIk6i2y8FPaq5s1U3mhst2sF+w/VLMGZbFyjLHVdyzkPlhpsExNvcZrMbVxVegKJ6cJ+Ia6llib12hxo/TVNIxM0ewxuhjtxhppOPOnl8nX+CibI4ZBxX2dOn+6Q1yuYwFjt7UcaDG7ziXDXgAk44S9NrQV4N1eXB7TRyfFFuel4' \
			b'DNFo5ihzbRxlVQW/o1haDA/wGXdtRc7015Ziq2slO0olszz4bburK3KmFrkjWdC598vzhYJh03f2aC483KD3d4u7lcPNa0mGTRclz3aUt2HanUx70uGYHQZ19Lq6DcgJlwSfSEn2aUlbYpJu6a5dUCzchKJfQnAgimlJ2ZC72e48YJYlfyxa2I6o+ygdeRtN' \
			b'GurCIeGqhuMNKEiuVrwvBYy9MU7KYE0XbEVHY3gFyaOrjGZsVhUcjacc1RlHVaVvQ2OEq1LYJwTyRoZJEHLKXgG+FI1uRH7KcAz25fZPT2F78tWC3q/xhdV6lBvUdN0VIuvbIJrXSTjL8wyNiIJNdpJMdpJMdvI2DctiPexgS3DaGVtShTRUP3Fm2mvc8IEa' \
			b'tC3P3TR8p1mbhuq6pUiGUMQQuFiq95a+bk3q96jaWT1GZ9VnrOL+pAqzDqnroqjroqjrorh3orDDgWgdyMAy3sdZiKRjraLFW00btx292nV0gw+wBRkjaZ5maug3teauZxgHa4bmmc+a9aRDe5b0pElPFIpuXj7NdV1T5mrKXF3bWUdt6vpX6+0dL3RdUnbC' \
			b'agPs0bTowITDEQywpBcZNusKbInVzVB1M1TdIFgTNW/qbLFxjOOhMP8Ry+iFd9wSDe4yTjayNQsn1kt1mGcOsg6ylNbHxE29Qr46LMA0O6+Dbhb0K2CnHdhkJzb7IBOpHDt6p2N1EOHrQOGa74aJn3bqQWH6qqgJRYmaN5M4IKgt2lHTEUuWyPsjsGtdS0US' \
			b'7xCA7CRtAyfQNQLPFYCxcDhboM+SS1zkgEJFBznBKewxZZLpljk4SwLluw65mGfTiDJ6VAPpoNQj8bbPP9iYsw3MHLJEUvYgw7ZIpNicRpOO5JrqnwOjw6Z7sOccbDgH+63BZmuw0xpsMAa7i8HmWrAjH2z4B5v9QZ5BfsG5X9BygLVzYDWCbZZBf8DEQLgw' \
			b'tADbLYJ8PTQ1fEZ5OQUswWvhWFqvE9gDAloTXm7RQl76cLBiD7bigryFFgFkMOQwlDfIZihMkNeQ2dBBhIICG0LBihoY+YNZ6jAYCwOzMGFUw8mN3g9mjYL1Fiy3MEHPwX/ldQ2nzzo8ohFOUoSDbeFoSzgCEo7ydA0crgnnhsI5nQ7OrGzhlM4WDi6FkzgN' \
			b'nYS4gWYRHW2MR1TCuZlwOqSAN7dwKCQeIOrfBudFwquhlG86PJUWouMZuOHYYvSBg0V7fAeElhjPv6hHGfCAXB+qh5NVezr91Wf3xqtpg6kRcOKlj2PxKxqPyMQTOPFDIAyexouHteLJkdByw0T2KDwc8wxHQ4eUwFmQcDAoFLYNTHPawJmaBj6Jx13C6ayQ' \
			b'A/g50+D5m3AyLiTQgbR4zmkLPl2LR3ricadC0RGacJY1pI6SCWeGQjw489m7PTpsevwKxALdQPuQDkKF+Hj0M/yGH/DRHnIDJBJ0JiicnmpRE6hIPP3TvxuOAfVVawPH0foyv/E4t4EjbC0e3+vvluTo8JDPFjIKjs3GzPIx4AhefBV8FhLu4ChVH9SJ14Am' \
			b'gCEVQa4DQSp8VPi4W/gQAB9TsGHGkMOmVlMOIV5LaSwgAxJoLt41lvjs9iU0jZ7vAS0wz2QWXi4BVtwAWvQMvFjIWzsDJHYaSiw8hEpoRwDFJkixY6BiHwZWLEkpbZP+7QktdhG4XB6mgEQZrtgZZGn+NI+Am+wjYCen/c38H8wgm4EbGuXrA+hg7y/v2BXQ' \
			b'E0b+BoOONBI5A0bYgyVj7SJUciUwYVd1tOubQKrscia0MtyRjhspt/nQqOTOK3Wg06Br6INy/3PYR40412VYZ7J5ddlcuzgGODKUAmfawtGyiIk+HGyaPouNeh4f4WwpOMGowEkfF84hOAgvW8ZMHw5W7O+LnWAdXISfMsPQlnAUll3kWGphaLnNMBXqJyhG' \
			b'z8CqD9ATtOKN0RXcXsw+YSyMSmvCI7zj0IghqMVvEdpSsHhF6MU4W9iLIELgi2cJ4yhHtwaIURZQItyHYIzvzv5vgXOSF8pzlB+CZ4npCbFj/mTAPfxC8TUoVyllw4cE9D1SVxexPvs25XIXvxvgn4MAC8Q3aiSE4JznhW4BNUTNJ4Jgr0NposgIsLev4AzU' \
			b'ItEGvWaKNlhmABQI5+JnMwqJwkQqIRIxnlF8LSQuAbB7hBXB1/5HQHW+9j7yWfN/uOPPDpLRy5q1Z8otTCzJhracWLo7IpdKLA9ALIaIxcwQC2SImW6zQ00wzCeG+STQiUl0Yoor0YkZpROT6MSkL+zNJUwlY0ySv3mLReITaYeSp2eaPhDYA1MkJsL2mE+c' \
			b'k1gl0qO8g1AwR5H4luMGziBvk8mHhMGh5/nCLOCLkO8ZX5DXwXyR0rWSLFIfo9vJFZxNVKRc+GbOFJyiXTwxQg/60CGPA7nh6KywhBFqF+NMmMASE8yN3HQ7hm46nF5DNMCjN3hv6R5owBZXooHREZ0uDenQu/cmAEsEMDKuU4ixRQDxibRDmdMzTR8oug+j' \
			b'AcNgUOZDoN8NOwt5LKxr7AyoTz9NIXsbQ82jvl2A+kGRGeqT18Gon5K2EvVtQn27C/U5m6gEOS49Bepzitb2DkyF/wr/FwP/PcF/Pwf//Q74p/gI/z3Df8/w3yf474srwf+olRDcAf77VfDfE/z3I/Cfi7EF//GJtEOZ0zNNtwL+RwNG+E8+DP/9AP7zWFjX' \
			b'2Bngn36aTCiEfw41D//9AvgPiszgn7wOhv+UtJXw3yf432VXCNlEJchx6Sngn1O0Fv5thf8K/5cC/1AZJVrLdsM/VtoJ+IdEtAT/9AIK3rV0Z/inUPGK8I9Bt+AffBn+6d37wj9+wuJtCP+FGEP4T0+kHcqcnmn6QA7/4wED/Gc+BP+UUwn+i1hd20Unwz//' \
			b'NJlQAP8h1Cz8U6jd8B8VmeCfvQ6F/yxp6+AfM53gn1IyAf8hm6gEOS49OfyHFK2Ff7efAfpiSMBUHrhkHhDEA2KOBwSGMR3dxtiAQmDt4amBeG/pHthAFFdiAzHKBiKxgVjFBoLYQIywQS7GFhvEJ9IOZS4iavpGQQijASMhJB8mhIEFoIiFhBAylAmBNZHJ' \
			b'hYTAoeYJQSwghKDLjBDI62BCSElbSQgiEYLYRQicTVSIHBegghA4RWsJoa+EUAnh8ghBESGoOUJQGIaWT40TAoXA2qOYEBQTgkqEUF6JENQoIaRp5PTuvQlBESGoEULIxdgihPhE2qHMRURN3ygIYTRgJITkw4SgBoSQx0JCYGcgBNZEJhcSAoeaJwS1gBCC' \
			b'LjNCIK+DCSElbSUhqEQIahchcDax2FyACkLgR2sJoWsrI1RGuDxGoLmoYm4uKgiliRH0BCNQCKw+PAuVcJLugRF0cSVGGJ2EKtIkVHr33oygiRH0CCPkYmwxQnwi7VDmIqKmbxSMMBowMkLyYUbQA0bIYyEjsDMwAmsikwsZgUPNM8KCeaVRlxkjkNfBjJCS' \
			b'tpIR0qRSSskUI3A2USFyXIAKRuAUrWaE7oRWLZzTeoXKDWfCDTSJSMxNIgJhaB6RyNYpCFqnkDME/cLqxBOKBE8oEmlCEYWKV2KI0QlFIk0oEqsmFAmaUCRGJhQVYmwxRHwi7VDmIqLug6sgidGwkSSSD5PEYFpREQtJgp2BJFglRQraGGqeJBZMK4rqzEiC' \
			b'vA4miZS0lSSRphWJXdOKQjZROXJchgqS4BStJglcSYtzWgnxAe4FAv0A4hUAekLeKdjtEygC8CHYMYhFkCJgQnCgiu8rM3z0CNdr2i2vEmUlysslSknDanJuWA1KLQ2ryWxYDdxeTLwRUXK4joACiVLy4JpMg2uDKxKlHB1ck2lwTa4aXJM0uCZHBtcKMYZE' \
			b'mZ5IO5S5iKj74MqJcjxsIMrMh4hSDsbXilhQ+4KTiTKoJBMNiDKEmiVKuWB8LaozESV7HUqUWdLWEaVM42ty1/hayCYWm8tQTpQhRauJcufyvEoSlSTOnSQckcTcrjxQUh2RhMtIwhFJuEQSFA5JwjFJOCYJl0jCFVciCTdKEi6RhFtFEo5Iwo2QRC7GFknE' \
			b'J1xXswuKVHqu++AqWMKNXIklkg+zhBuwRB4LWSKEYZZgnWSyIUtwqHmWcAtYIugzYwnyOpglUtJWsoRLLOF2sQRnExUkx4WoYAlO0WqWmFulV1missRZswSt3JBzKzc4DLBEn7FETyzRJ5agcMgSvIpD8ioOmVZxUKh4JZYYXcUh0yoOuWoVh6RVHHJkFUch' \
			b'xhZLxCfSDmUuIuroKkhiNGwkieTDJDFYy1HEQpJgZyAJVkkmGpIEh5oniQVrOaI6M5Igr4NJIiVtJUmktRxy11qOkE1UjhyXoYIkOEWrSWJuLV8liUoS50wSitZ3qLn1HVBGaYkH3pgkwO3FxBuRBIeD6qR4rYfitR4qrfWgUPGKJKFG13qotNZDrVrroWit' \
			b'hxpZ61GIMSSJ9ETaocxFRN0HV04S42EDSWQ+RBJqsOKjiAW1LziZJIJKMtGAJEKoWZJQC1Z8RHUmkmCvQ0kiS9o6klBpxYfateIjZBOVI8dlKCeJkKLVJDG34q+SRCWJsyaJjkiimyOJDsMYvgWS6IgkukQSFABJomOS6JgkukQSXXElkuhGSaJLJLFqb0H8' \
			b'BIm5RRK5GFskEZ9IO5S5iKj74CpIYjRsJInkwyTRDUgij4Ukwc5AEqyLTDQkCQ41TxLdApII6sxIgrwOJoksPetIoksk0e0iCc4mKkeOy1BBEpyi1SSx57rAShKVJM6LJMhyreYs11AuyXKtMsu1Isu1SpZrDockwZZrxZZrlSzXqrwSSYxarrPTBdQqy7Ui' \
			b'y7UasVwXYmyRRHwi7VDmIqLug6sgidGwkSSSD5PEwHJdxEKSYGcgCVZJJhqSBIeaJ4kFluuozowkyOtgkkhJW0kSyXKtdlmuQzax2FyGCpLgR6tJYudaQX0dPGFHqcJUurgoupA0I1jOzQj2mQHFliYFy2xSsKRJwTJNCuZwaKDgScGSJwXLNCmYQsUrGShG' \
			b'JwXLNClYrpoULGlSsByZFIxHBEc5tiwU8clA4sHV0+pyDhtYo2c7xViMZKdIPmynGMwNLmKhnYKdwU7BminS0cZQ83aKBXODo1YzOwV5HWynSElbaadIc4PlrrnBIZuoODkuSoWdglO0ljjEziWFlTgqcVwMcSgya6s5s7bPCEXBoKuRWbYVWbZVsmxzOOxq' \
			b'sGVbsWVbJcs2hYpX6mqMWrZVsmyrVZZtRZZtNWLZLsTY6mrEJ9IOZc4vAEIdw0bekNThGIuROhzJhzscA/t2EQs7HOwMHQ5WTCYgdjg41HyHY4F9Oyo163CQ18EdjpS0lR2OZN9Wu+zbIZuoNDkuSUWHg1O0mjfqwsP7GZXy8fjo98oad80aYoI51JJuB9m7' \
			b'5Zy9G0o02btlZu+WZO+Wyd7N4bDPwfZuyfZumezdFCpeqc8xau+Wyd4tV9m7Jdm75Yi9uxBjq8sRn0g7lLmIqPvgKiZFjYaNnY3kw50NtncLDzUCpeBORx4bOx3sDJ0OVk0mInY6ONR8p2OB3TuqNet0kNfBnY4k6cpOR7J7y112b6Fj6TRUpnBRYiineeeD' \
			b'U7aaROaO+KwkUrscp0Iea7occPynVwyeArqLNDReQBp4Y9IAtxcTb0QaHA6qE94F/27pzqShZXFF0sCgW6QBvkwa9O59SYPPOIXbkDQKMYakkZ5IO5S5iKj74MpJYzxsII3Mh0iD8iv1NIpYUPuCk8kiqCQTDcgihJolCwq1myyiOhNZsNehZJElbR1ZYL4T' \
			b'WVBKJsgiZBOVI8dlKCeJkKLVJFFXbleSuGiSIPu3nrN/w7GNZP/Wmf1bk/1bJ/s3h0OSYPu3Zvu3TvZvXV6JJEbt3zrZv/Uq+7cm+7cesX8XYmyRRHwi7VDmIqLug6sgidGwkSSSD5PEwP5dxEKSYGcgCVZJJhqSBIeaJ4kF9u+ozowkyOtgkkhJW0kSyf6t' \
			b'd9m/Qzax2FyGCpLgR6tJoq7criRx0SRBxgs9Z7zQFAZIIrNcaLJc6GS54HBIEmy50Gy50MlyQaHilUhi1HKhk+VCr7JcaLJc6BHLRSHGFknEJ9IOZS4iJldBEqNhI0kkHyaJgc2iiIUkwc5AEqySTDQkCQ41TxILbBZRnRlJkNfBJJGStpIkks1C77JZhGyi' \
			b'cuS4DBUkwSlaTRJnu3C7RZ4QlSouiCqkvs9tE4kuxBxdCAoD2yZmdCGILkSiCw6HFYvpQjBdiEQXFCpeadvEUboQiS7EKroQRBcdL8/DLzjZELaF/RMxGAQRI8SRRJV2KH2REh1dxQaKo2HjBorJhzdQHBBHEQs3UGRn2ECRlZOJhhsocqj5DRQXEEdUbCIO' \
			b'9jp4A8WUtJUbKPZosoubKO4ij5BVVKocl6hiE0VO1WryqAu6K22cAG3cG2UYMnCbOQM3lDYycJvMwG3IwG2SgZvDQXUybOA2bOA2ycBNoeIVKcOMGrhNMnCbVQZuQwZuM2LgLsQYEkV6Iu1Q5iIiV8eBgXs8bCCKzIeIwrQlURSxoPYFJxNFUEkmGhBFCDVL' \
			b'FGaBYTuqMxEFex1KFFnS1hGFSYZts8uwHbKJypHjMpSTREjRapKoC7orSVw0SQgiCTFHEgLDUIlLJCGIJEQiCQqHJCGYJASThEgkIYorkYQYJQmRSEKsIglBJCFGSCIXY4sk4hNphzIXEXUfXAVJjIaNJJF8mCTEgCTyWEgSIU+ZJFglmWhIEhxqniTEApII' \
			b'6sxIgrwOJomUtJUkkXoSlJIpkuBsonLkuAwVJMEpWk0Sp7SgW1WeuBSeoMmQD8IXPr/GOUMMeEPk3EGToczcZCiDF3JHNhnK0GQokyZDcTjkDp4MZXgylEmToYwsrsQdo5OhTJoMFV+/N33QfCgzMh+qkGSLPuITaYdiFxF1H1wFfYyGjfSRfJg+BvOhilhI' \
			b'H+wM9MFayURD+uBQ8/SxYD5UzPKMPsjrYPpISRNR6BUkkmZFmV2zosIHVJTf8MeZR9CvzcRazyZzp8S6wCPyUroZRzgK8FI544H7FjCUbYA7+jlzN/Uz9Fw/Q1MnY/QwQCic3LfQ3LfQ3LfQqW9BoeKVTNzDvgUUKJ26FnpV12ITJsuO9C2wxGX/t83cUUhp' \
			b'h3KnZ5pkLwzcowGjgRt/QtkAbiAclIPOBchD4bqwMq/L1+Xxc6CHIL6m/kVwLrBzL+hgRJ1mdm7yGmUITswCgsDkaxZipaGbehgIPDtX57HERpHgGFPAi2CHr0FnI6SupAflHmFzJfCD7B+hgakFnlDQW/A8gefVRp6Qc2fHniZPHJkbAi8wJyAfBC5gHoj4' \
			b'f07Yf1JjSo76BW6uX+Cmsd7gRX0Bx30Bx30Bl/oCrrhSX8CN9gVc6gu4VR0BRx0Bt431243/KJS0QznTM00vLZr9owFjsz/5ULOfoD20+TnX2mzfP8xlFrqlx/Nte7egbR80lLXtyevgtn1M44oGvYsN+s1OA3P4AhULx0WiGBbi1OxqyHP7HfF4bgF1xeOK' \
			b'x0fBY0uGYDtnCLbtNB7DjDU2/lo2/lo2/tpk/KVQ8Yp4bEeNvzYZf+0q468l468dMf5u4XESStqhnOmZppfmeDweMOBx5jOCxyHXcjy2ZNi1ZNK1i+y5doE9N2oo4TF7HYrHKY3747FtF+Jx+AIVC8dFIsfjkJqleDy3FrniccXj4+AxjYXYubEQu2MsBOYO' \
			b'81iI5bEQy2MhNo2FUKh4JTwetbPaNBhiVw2GWLKz2pGxkG08jkJJO5QzPdP00gKPRwNGPE4+Y3jMuVXgMY1yWBrdsItGNuyCkY2ooQyPyetgPI4JWYHHYike8xeoWDguEgUec2qW4vHcst/TxOM6rn107D61OTNQnQBE9Rx+6x34rfEx4rdm/NaM3zrhty6u' \
			b'hN96FL91wm+9Cr814bfexu9CjC0sj0+kHcqcnmn6QIHlowEjliefHMvzYewiHtQ0ykxGdvI2Nhe9jaHnUV4vQPmgxwzlyetglE/pWjd8jXlOUE8pmUJ6ziYqQI4LT4H0nKIFSF+MUM+t4a2IXxH/PBDfEOKbOcQ3OxDf4GNEfMOIbxjxTUJ8U1wJ8c0o4puE' \
			b'+GYV4htCfDOC+LkYW4gfn0g7lDk90/SBAvFHA0bETz6TiJ+HQsQ3GeKTt7G56G0MPY/4ZgHih7zOEJ+8Dkb8lK6ViG8S4ptdiM/ZRAXIhW/miM8p2hfx5xbkVsSviH8eiG8J8e0c4tsdiG/xMSK+ZcS3jPg2Ib4troT4dhTxbUJ8uwrxLSG+HUH8XIwtxI9P' \
			b'pB3KnJ5p+kCB+KMBI+Inn0nEz+Mh4tsM8cnbFKK3MfQ84tsFiB/0mCE+eR2M+CldKxHfJsS3uxCfs4kKkOPCUyA+p2hfxJ9bRVsRvyL+eSA+zVqxc7NW7I5ZKxYvQnyetWJ51opNs1asK66E+KOzVmyatWJXzVqxNGvFjsxaKcTYQvz4RNqhzOmZpg8UiD8a' \
			b'MCJ+8plE/DweIr7LEJ+8jc1Fb2PoecRfMLcl6jFDfPI6GPFTulYifprgQimZQnzOJipAjgtPgficon0RH5fEqkbPHDJz0cAvH/hImbUE4PYgAXleRADb09zfdjtQkWDpUIekABVj5owZ1YgdxIDvUwR1gplBMDOIxAzCFVfab2eUGURiBrGKGcLkdTFCDYUc' \
			b'W9vswJdBZBoAGoid4mkSHaoDYjAcK4MINBE+7rSTfKY4ooiHe+1kHMHexuZpaGPonCMgO8Y32xnhCYEhBxvu8EvzDXfI6+ANdxzOYBfryQIEAeP7IotvyDQqWI4LVbHlDqcrMQb6wF9PG/6vU/hXo7+nDrgp+IXE4ZpXu2hjmzB65AnJDMGUkPEBk8FCJpia' \
			b'ZYOgDwiWN+kjao9MjikmxVhG3yWoO9PsLlD2EHTt9kfURUhqCD1z5IyICXVnMVpO4mSo57zsM+BiBMIRFAwQeAD+zc9WCUi3GW41GSFrdL5JOdME8GizNeFvEoBmW6kF5hyMNgA1KyBmGbYAqgCklHgSkATAod8NDqMNyofBh9Au9EXo2lFCthNIsRQl9mtU' \
			b'YZPp7KAiaxiBMitkbLVKlJ2CjX0gw+fCnu0J++CQUXYfCTvEPeOHD2Nh0xEofu608eTgVseeeDKJJaFvduJ4gnLm/xlbOnzD/eMLEgB0YX26BCLCOeDNONYIvU8TpflTwBpdZ6En46XevyfTziBPGty6K/AJgKMywHHX12iJICN3NFrCPjjeD/ZOxkEiHx7G' \
			b'EoqBIoULuwWwGCzHhjXarsv3xfH/9R0CE1ZdRKf9gOkY4BTBKGvsgCavvsETdzzG02wmGzzY2qWjSzcwvEvHNELIrTO40oglPoYXgEY63O0gHbwCPwy2lcRhYy9wgPTYiPw9IRajFUgm5G7EguHys0Etu2d3Syzrbmn7AE2kieaRypEIgeoEmknDLhdpsZ9D' \
			b'IhT//NAIysbeXbB+YRdM8K6J090weZrDupOgAvL53zCkBDszdkdqEm3Z1R56LMe7wXYjwT01sWKkiRSaR0WzKDSF7q0JdOL9si3AwbqNxtJNh9Ioc9x20GDK8tGaQpBZ8Hqc3aiXgBA3i2KTaGiTEtz4GTZ5VPPqFDBpasbB3ZudTqGFs6Zfpg4ZAErg4uy5' \
			b'YgsttTc8l0M+qPnplBoyq7tV+iDzU/Nn/8gzE47s6NMAjVmgALHupPVyZqCxuLWyEDQuqkUy3Rrpcc7WHbVCzhgyOBcWtTtm7U9mPVbAlo8PChf6Djs8K2eVb00ifGjo6E4bPmCm5wljCH5Loyx31p+ZQBIQbD84wf1Zj2bOxk8t79DMAos9AFj6BwaWDFS8' \
			b'Jo/bFjkGqFRAWTtzrgQT0NxpNE2OiSV3iyPugM5MezwcEW3FkYojq3HkVLo4l4Mj/QE40h0RR7qKIxVHVuOIrThytzji8+08BlevaUD1FIHidDHiLgFBoMxnM3R6KAA0f/r68AhQEAwtPtsrFpwFFqy0xp4fHuDr7hAOOpq2e6GWlLtY99f8aeUjhGFflR4B' \
			b'fCI0iAoNFRqOBg1Yn0+sqXCd4GD0I4/TCAmyQkKFhPuABCr1Z9h7uE5I0PaRB3GEhBOZ3lkh4fIgQVdIOEtIOJfJmxUSxiFh6jTx48AD1ubTGW7E6CeDDizN/YIDfmQROMDC7LHTthNMhBO2p47WRgA5YEZnBZATAJBTAA17WqBhTwo07EOAxqEtikVQccAc' \
			b'zQoV1wwVWOgu0Jx5F1BBFfKMOh/KPELo98UbHLjPqT5k2mWFhquDBixVFz3TYQ9owMy4iHEJBaZNiZs8gIOg4ZCZlBUargYaMPx1zIJagA2YG5c1aCl9uwEOhHBwlwANpk6OrNAwDQ0Y9rrmR16nOUNCs6ElSKhzJK8eEqBunswMyZNAhL6/KjwQ3SOkhQ6n' \
			b'SrYagaHOkLxGYIAyfPz5kScLDFfXVOgUjDlSU6FOkLxGRIBiWxGhIsIYIpzL/EifzLgn70Ojw+j5lkfah7cuxNwDK0B7G6gLx0MNyM4TwQ7IoCkE2WeBtjmRCZTrt8x14+fqnnzLQt5T60Jlx5pcNnZ0I//XTJhCGEqp6s6zAbLyvNhlrRDMIzwawO1sjViY' \
			b'PoUzs82JTKyswFKBZX9gEVv/VwGLqMAyCyyCgaVfCiwnMg2zAssdA8vFg4rc+r8KVGQFlVlQkbPjJhmguOYVRCIUIQgh/CDw0AgbGgAD0IKgIuIEgkSo7jKvkoKrop2ogn1Z3YZVA6tDB8esu7yoh1IeC3gs3ODAMo2n1LRciGMBHhTeVHBjcYMSFosC5BoW' \
			b'gW5C86D0UsdbqqDsp35mf3AmE75GZLWU3YCigI5Ftqs9s16PI1NUwYaqyr3pAFKAEBB1IYI+4I04WzRXTKyfy5VDO0+NjC9mSvJwcbCS2l160hehqwyyx/UV0PZBdAYzRmCdisC0A+FqiQ/AYuzbJtb7UzujQ2/ZvBJSek+fdeihwOnAw6jXt/5+s/HvbCEa' \
			b'PN/493ilYgyfeIt+EvygMeA14fCgW4vnRPqGkCyOwIbNBIWGs8H8T81HYUs6oTae9ejf0AwPscaTEw1JoPb/mn86/Q9fquGldvK1fJicm3g/tvL04F86GK7L/fFzZuRzCr7oqRV2cG9x39TZr+OxC3EMG3YbhdaTZKl8KzX+A3o3vEt7+m9G/9FTgaPS4Mb9' \
			b'RKFao+h2nehewv2k91Fm/0HLd+IZyurWyGqnxB0c0jQqvuizJPh3zPyDJnzpgw1qbEAbbDRnTzwc+DsmrB9JmJhMm29mQZfFFd2UkQS35Xn1PU46hNY0NJig5YQ7dQlaVQjABLgEQIf7pYYs8h+k8TdN2aUh23rONjGddV3LPQtB2QjYTlnpq36Lp+Lyqbev' \
			b'iZiGl932Kp5N/Z9/067Y028c+Aycu2WcfBEhrvc+asnG8zMf7KIkd/uWeS+t7yDcR8n32QST9I9bA0Sz34VSyz0j7bxCM+wOX7l1ke7FqeFdO6Fxcd9al83RLzHiBVut38G7SdvyyOCmmge8KMkqJhk2r+/vs5ibMynpEBmungZQ7/Fq7/Xtuy9S/1j3Y3mJ' \
			b'b++g0MPY7doLBp/3j0YpN8OCD0feP0Dxb8+gCkA3ILtI6K4ZeN/5BSMx9/2NiYvKxFgXc7ocLCL2dXXCNIMLBsi3fRdeYJdZFpSywdWqMVk1YADyii4qEPv1+u+vXoAF9QgXjT+2tVZM1wrdXNNFBWK/cYHF3cB1NcM0d3uB7X5ZUMoMUWvHZO0Ac9UVXVQg' \
			b'xvrSd1A7cIrNmhoCM27u+oKJLcuCUp5sdbZrJUmVRDfXdFGBGOt+31ElAUWvqyimuY8LJnstC0pZU/vnO+qKba7pogKxX+fcrBx4X1plgp5StXHN8gsm/O0VAaZIzoSApPMPyrDajZ+uQTBx6IouKhD7dePX1qBc16trE8yGvs8rn268OBbNOTpoHGClXfh0' \
			b'alYHv/V2DdMuq2Ui1DT/HyaEwRy9tRcYvA+Jf9+XUKB/NfBTYy4qP12F5WlYNs01XVQg9ptjcFxYts2JXZSFstap6Trlmmu6qECoveft3OFEnXXVa0R1sPxr8QUzxfeKMLjCSqs9YuA6qbRGCnN+vyGNk8151ZzDRVk+Nqn7DLNcN+dwUZbvNxhxx1kuzR7Z' \
			b'3i7JetM88AX0tToEqWBsjv0Cnj+eFrolmrDNXhesEdo3zrprx5dIHyuXBpy4Pvrm3C5aqzQ2T//stQHL3s/sIm3svYTg0pbNwG4F+1+0GUH6v+4twzduvzv7WYSZf0t2kaZPbsHAg2taNZd4kXb3m9Rwidrtm0u8SLv7DxpcmHZh2fwFXqTd/QcmLk27XXOJ' \
			b'F2l3/zGQS9OuaC7xIu3a5pVUuPqaodoFj45rdw8ekIXoCWtVaJjAt9Re5fr3GY0hfHbD6YkC9hmB0FSMvJZGQ3ullf8ptNgKDcrDGF71g/9C0ti0ltmOGBKLAvl7+smLIxWhvOiEYgPGDVovCL5pny7aFyvsiSWyvbBgvwiWWZdfgU1QvBBCY27CJ8OnsGTy' \
			b'wJ2hXPaF9xWUbl8yYZUKbMml+ImFlVxsBwb7L9p9BRxda7wv7KThaOjMB4gbfVCbGc6mEz4TwIfGEuBIKv8W8LEkNpxIE3x8mNe3/w/sDPIs'

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

	TOKENS_QUICK   = OrderedDict ([ # quick input mode different tokens (differences from normal)
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

	def expr_scolon_1      (self, expr_scolon, SCOLON, expr_ass_tuple):                return expr_scolon if expr_ass_tuple == AST.CommaEmpty else AST.flatcat (';', expr_scolon, expr_ass_tuple)
	def expr_scolon_2      (self, expr_ass_tuple):                                     return expr_ass_tuple

	def expr_ass_tuple     (self, expr_commas):                                        return _expr_ass_tuple (expr_commas)

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
