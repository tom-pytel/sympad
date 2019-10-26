# Builds expression tree from text, nodes are nested AST tuples.

import ast as py_ast
from collections import OrderedDict
import os
import re
import sys

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

_SP_USER_FUNCS = set () # set user funcs {name, ...}

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
def _expr_ass_lvals (ast): # process assignment lvalues
	def is_valid_ufunc (ast):
		return ast.is_func and ast.func in _SP_USER_FUNCS and all (a.is_var_nonconst for a in ast.args)

	if ast.is_ass: # if assigning to function call then is assignment to function instead, rewrite
		if is_valid_ufunc (ast.lhs):
			ast = AST ('=', ('-ufunc', ast.lhs.func, ast.lhs.args), ast.rhs)

	elif ast.is_comma: # tuple assignment? ('x, y = y, x' comes from parsing as ('x', 'y = y', 'x')) so rewrite
		vars = []
		itr  = iter (ast.comma)

		for c in itr:
			if c.op in {'@', '-ufunc'}:
				vars.append (c)
			elif is_valid_ufunc (c):
				vars.append (AST ('-ufunc', c.func, c.args))

			else:
				if c.is_ass:
					t = (c.rhs,) + tuple (itr)
					v = c.lhs if c.lhs.op in {'@', '-ufunc'} else AST ('-ufunc', c.lhs.func, c.lhs.args) if is_valid_ufunc (c.lhs) else None

					if v:
						ast = AST ('=', (',', tuple (vars) + (v,)), t [0] if len (t) == 1 else AST (',', t))
						vars.append (c.lhs)

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

def _expr_mul_imp (lhs, rhs): # rewrite certain cases of adjacent terms not handled by grammar
	ast         = None
	arg, wrapa  = _ast_func_reorder (rhs)
	tail, wrapt = lhs.tailnwrap # lhs, lambda ast: ast

	if tail.is_attr: # {x.y} *imp* () -> x.y(), x.{y.z} -> {x.y}.z
		if tail.is_attr_var:
			if arg.is_paren:
				ast = wrapa (AST ('.', tail.obj, tail.attr, _ast_func_tuple_args (arg)))
			elif rhs.is_attr:
				ast = AST ('.', _expr_mul_imp (tail, rhs.obj), rhs.attr)

	elif tail.is_pow: # {x^y.z} *imp* () -> x^{y.z()}
		if tail.exp.is_attr_var:
			if arg.is_paren:
				ast = AST ('^', tail.base, wrapa (AST ('.', tail.exp.obj, tail.exp.attr, _ast_func_tuple_args (arg))))
			elif rhs.is_attr:
				ast = AST ('^', tail.base, ('.', _expr_mul_imp (tail.exp, rhs.obj), rhs.attr))

	elif tail.is_var: # user_func *imp* (...) -> user_func (...)
		if tail.var in _SP_USER_FUNCS: # or arg.strip_paren.is_comma:
			if arg.is_paren:
				ast = wrapa (AST ('-func', tail.var, _ast_func_tuple_args (arg)))
			elif tail.var not in {'beta', 'Lambda'}: # special case beta and Lambda reject if they don't have two parenthesized args
				ast = wrapa (AST ('-func', tail.var, (arg,)))

		elif arg.is_paren and not tail.is_diff_or_part and arg.as_pvarlist: # var (vars) -> ('-ufunc', 'var', (vars)) ... implicit undefined function
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
	if ast.is_differential or ast.is_var_null: # null_var is for autocomplete
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

	def set_quick (self, yes = True):
		self.TOKENS.update (self.TOKENS_QUICK if yes else self.TOKENS_LONG)
		self.set_tokens (self.TOKENS)

	_PARSER_TABLES = \
			b'eJztXfuv3DZ2/mcK7L2ABpD4ln9zHGdr1HZSO1l0YQSB4/UWQZM4sJ20RdD/vTwPvjTSSKO5986LsHzFoUjpkIf8PpKHj5s3f3n95OvnX7/8S/OXf3n/6z/8Lfx8/vSrb/3tm8evnr587h1fvXr8hG8d34W/f/Hs5dcvwr0LDsEv+PJreMdL/PvF07/+8OTx' \
			b'66ev2f3icfD9Ijn/lpzfkPP188ev//UL/7V/AymiA72ffPfq+d/hV3R899V3L5988/fggoDfvoK/333h/z598c23f3/9FGX6DqT+22N4+OLZy+9Aqmcvv/0rCP7sBcbAv//+CkI/xxz5Gp7ya7/AmE++fvHiccgl8Hj17K//+m0Q6FUQGBxffvEcZQYx/t3/' \
			b'efziG3C+/JIzAlxfJOffkpMz4unz10/hU6+evYD7l8/+9uxLcDyhTH79LUr0zXNMik9kSNV/vH76BAN8+eyrryBjXj5DBT9BAR6//BJSDg++fsUfDFoCkemtT3z6vg130PKLx9+8/vZriP8t5u/T/3gC2Y9ePq+7QkOsAP+uJ//mnZ9+//HTH28/fvojc3/y' \
			b'7ndvP77//MOHjz/848efP31++zF77J3+9haDvf+f33yQn/74Jbg//f7b+4/hx6/v//OHtx//Mz370Tt/efv5h3cffmbXxw//nVz04U/vP316F12/RVd4zdsfk/Pz5/ixf7599zm4f8O3kvfvv75Lgv7zn78laaLQP/8UnT/9+jnK+8vvP//w0y+/ZcnMX5Ql' \
			b'MjrTKyEuOMLvz+8/xmd/vP04CBZ+/p5L+/Yf/wjOd79//Pl/w4//+fQ+pfTHj2/f/df7+PNTLtkf7+O7fv/1pw+/xo++jeHfpeRhJseUfEiv/D3L71+jSD/+9OuHmKIPSQtenqiFdx9++eVtjPzbT+/fvY8/fPnKBPrt0+cP8SNR1VG0Dz8n6fGlxY9PWcwf' \
			b'fv7j7c/R4xPF/L55c7PRfWP0bUMOAw5l4Y9rlLzln/4Xunr/xzRKNxtzW3jQLxfi+Qh98AInhtpY9DHNjWykf6dsVOsdt9EX/ZLHBuMJS3+0/6iglwYv0W95aZN7gdO7Ok1/TNdsOnq9/wVO74KIXmTVbNwt/d5gWoUXBgXR9MdwgnxEhbnUqebGp64z8P82' \
			b'+PT5r65lB/jBOxWkves57UrcBl/2ix4bQd/wOdpBbtrGqFv22Qh6bU9/TOt9ulv2AifoEnPcp4E0wz+DO/MXdNuQ4vG/dOGxAoe/S/a/pR8bxZ4kLSpUtJwoK6Mv+3XJoys9NgKzWvrvSxKgoz+agnjXRqGE0tAfDaJT/vpfG4kq1PDqPj7Q8YFS9Me2t/zT' \
			b'6w8zSjQ3UAJAM5yv3sfkvyzfwQvi+ufSJ11TgPhTD72CJkt/tf1zEHPk54jXQAKz/bOItFEyEy0VchZi4KGHHibz8KXiRrYsAtRFW3innxuJlU764im7RvgiBlr3BcPf/AvhB8k3EQJwyH9gWUCv9jLgRmHlACTyVSOWZKio+MCXSaqCoHvt66DJa6J/GP2T' \
			b'jyYfm3wM+bjkY8mnDz4bgeUWiqWkEizoD+RfEDd4qdwLnOCy9GcTqh05waWouIcoEJsAnB+w/uG1CtHAS3eDRZnBz7+qIyX5iksFXdIf46XrKMs6cmJGbrouODAxXQe5qAKGU6rBE73C75bf6b/skbkNJanwDz7eA4udpD++iN3yb19tMQz+h4ylKOCADJb0' \
			b'RwMuUhz/C5yQA/6h0Cg0/7QkvgeMrosMFEqWfwdjE4I6UR6UFxFDWCxuUP459/1zzmTveWNS7cOfJn3bMwjmtITvyuhq2SVUcOjgIMrwJVmA6jpUQvSSWBGGXumnfwO6OvqjgRkYmTt0wkfahgDYf+AGiCUxkP8iSSQ0/dE21nFBtR8SJehPahAAPqPcuqM/' \
			b'qEvOgg6d4GrDw1v+6X+FB+TlE2QV5rnnN9YK6Fjjhw28wMQXAAUafIHpwgMMyl4cS1tKNICaj+hbP2/apvO67nyN8J/ymKcQJQERusbjoUdAXzw8qHlk6QE1fM12qnHaU7v1/52P2vn/wv/3qNL6ML4sezk18rL/dNdCWM+9CsuQd/h4/vIxfSZ3AmL5e+tr' \
			b'jf+iaHyN9BXamcbZxrnG+e+2Te/f44XoJMCWdyv4HnzbC+QAA32iOi96B7JrxDRfUCECwJzHL0ijf23nk9RJcNumh6/790FUCe/3v/3He3+ppgehfXifEb1reg+yPVCvr0C9aXrbWH+5xvaN8/nRNU40zn/Kp7GDouJzoIPa7cHEKN+49M1KX/gBjU3vuRjg' \
			b'23qC9bXRU7NuLCjAR/Vyeur2SvIZg/nSQN4KaKR65y1UWR/Sq+0G9AUeXmf+9uYG8sP/hByAW0uhFD+FRN8im+Gtx6dvoLmJvx3cqq5PRNc3PSmt60nDLWvLawKLgCDdOtIpagbvjqN1HRcVwXfJATS/CBXnfRwVB+GozIT3hVDoqohwoqXkzY1GvRV5yLlH' \
			b'uTaSX5xPMX/KfCnzYiwjOP2+9BlGFt0fU4iWi3xLJRkxEbJGYFV5QEmEJUmEfugPc8pD5ReiVtpTrrQEzlU/p6mfGxQO21O26umU9SRkgH5UWMwyzKyYNZwlISfy1PvUxpQdPUWp8IwUmOOQK2QtNRzBl7oLiF0w6OE/2vgk1xpwvBoQgEpyrwA7cdj26Sty' \
			b'na7efDcOmaXzUnT+7Z2GPPBekETogqlaq46qHVe1c8La6at2Tlc7fVu1c6rauel5wAYzAIcFQ4OhU7VPesqa65QII7usOkUtcrA60wMVGoH8nG5hvFeZqt8T1q+i8Xe07ACK4s+jC3aaXVLq7bBI5MNmC7JtgU7j05tOstVM8vBsTyaRnupJr9iWJrheSbac' \
			b'SH4eLCJcnxS9rWf7jKJYWnA10xwLBblyVd30nOOWrFOWmtVgywKLZR2HWZ6Tloubo9LnqIy6YAVkyCeLBxgAqNBqtgBrpn1DJd9QcEMl2kqqTVBnIPleHEybu4J8fQMzVTAvyIJi1VXnBVVTQ1RkCNmsnsqSUJGvIWss1TtL9c6aay4mNkwpYPtqTD2Zthh6' \
			b'TCBEnqLCUBWH7DuYh1tnG51ukxSnEwmaRyTqzKAT0ouk6erSVL2ckF5gIp3gKVv+XhVwhJFhVWvESSkEclnwNER/r4o4miJa5AzOuDpP4h7mSSDq18bsqdYAh60lmOdc1XTCalK66ueU9dO1VT+nqx9cr4GdEI04dyw2HFlUAsPQPXeQsKNUWyF3n+8CO0AP' \
			b'ufKAhiLgi9TOpxEjS79awQpnC9z0kqPveUkTjG5ITEMtD4drR3aU/2TvYXMPm4x45Q4N9YdJIBJRo+b5ITUCQQ4meFLRZwMxToZC+3FYntQFk3+sADRFA2Yf4hvoRT0DOigFdFN1sr9O4FWsDQaXmnn7zLeAPKv5NJtPqubTonzSNZ8WgJaiAYveMXRJatul' \
			b'eU1tHyZz6sETsgy9gSlOos4iGy+Fvap5M5U3GtvtWsH+QzVLcCYb1yhLXddyzoOlBtvExFucJnMbV5WeQGK6sF+Ia6mlSb02B1r/nqaRCZo9BjfDnThDTSee9HL5On8DE+RwyLivM6dPd8jrDUxgrPb2Iw0Gt/lEuGvABJzwl6bWArybq8sD2ujk+KLcdDyG' \
			b'aDRzlLk2jrKqgt9RLC2GB/iMu7YiZ/prS7HVtZIdpZJZHvy23dUVOVOL3JEs6Nz75flCwbDpO3s0Fx5u0Pu7xd3K4ea1JMOmi5JnO8rbMO1Opj3pcMwOgzp6Xd0G5IRLgk+kJPu0pC0xSbd01y4oFm5C0S8hOBDFtKRsyN1sdx4wy5I/Fi1sR9R9lI68jSYN' \
			b'deGQcFXD8QYUJFcr3pcCxt4YJ2Wwpgu2oqMxvILk0VVGMzarCo7GU47qjKOq0rehMcJVKewTAnkjwyQIOWWvAF+KRjciP2U4Bvty+6ensD35akHv1/jCaj3KDWq67gqR9W0QzesknOV5hkZEwSY7SSY7SSY7eZuGZbEedrAlOO2MLalCGqqfODPte9zwgRq0' \
			b'Lc/dNHynWZuG6rqlSIZQxBC4WKr3lr5uTer3qNpZPUZn1Wes4v6kCrMOqeuiqOuiqOuiuHeisMOBaB3IwDLex1mIpGOtosVbTRu3Hb3adXSDD7AFGSNpnmZq6De15q5nGAdrhuaZz5r1pEN7lvSkSU8Uim5ePs11XVPmaspcXdtZR23q+lfr7R0vdF1SdsJq' \
			b'A+zRtOjAhMMRDLCkFxk26wpsidXNUHUzVN0gWBM1b+pssXGM46Ew/xHL6IV33BIN7jJONrI1CyfWS3WYZw6yDrKU1sfETb1CvjoswDQ7r4NuFvQrYKcd2GQnNvsgE6kcO3qnY3UQ4etA4ZrvhomfdupBYfqqqAlFiZo3kzggqC3aUdMRS5bI+yOwa11LRRLv' \
			b'EIDsJG0DJ9A1As8VgLFwOFugz5JLXOSAQkUHOcEp7DFlkumWOThLAuW7DrmYZ9OIMnpUA+mg1CPxts8/2JizDcwcskRS9iDDtkik2JxGk47kmuqfA6PDpnuw5xxsOAf7rcFma7DTGmwwBruLweZasCMfbPgHm/1BnkF+wblf0HKAtXNgNYJtlkF/wMRAuDC0' \
			b'ANstgnw9NDV8Rnk5BSzBa+FYWq8T2AMCWhNebtFCXvpwsGIPtuKCvIUWAWQw5DCUN8hmKEyQ15DZ0EGEggIbQsGKGhj5g1nqMBgLA7MwYVTDyY3eD2aNgvUWLLcwQc/Bf+V1DafPOjyiEU5ShINt4WhLOAISjvJ0DRyuCeeGwjmdDs6sbOGUzhYOLoWTOA2d' \
			b'hLiBZhEdbYxHVMK5mXA6pIA3t3AoJB4g6t8G50XCq6GUbzo8lRai4xm44dhi9IGDRXt8B4SWGM+/qEcZ8IBcH6qHk1V7Ov3VZ/fGq2mDqRFw4qWPY/ErGo/IxBM48UMgDJ7Gi4e14smR0HLDRPYoPBzzDEdDh5TAWZBwMCgUtg1Mc9rAmZoGPonHXcLprJAD' \
			b'+DnT4PmbcDIuJNCBtHjOaQs+XYtHeuJxp0LREZpwljWkjpIJZ4ZCPDjz2bs9Omx6/ArEAt1A+5AOQoX4ePQz/IYf8NEecgMkEnQmKJyealETqEg8/dO/G44B9VVrA8fR+jK/8Ti3gSNsLR7f6++W5OjwkM8WMgqOzcbM8jHgCF58FXwWEu7gKFUf1InvAU0A' \
			b'QyqCXAeCVPio8HG38CEAPqZgw4whh02tphxCvJbSWEAGJNBcvGss8dntS2gaPd8DWmCeySy8XAKsuAG06Bl4sZC3dgZI7DSUWHgIldCOAIpNkGLHQMU+DKxYklLaJv3bE1rsInC5PEwBiTJcsTPI0vxpHgE32UfATk77m/k/mEE2Azc0ytcH0MHeX96xK6An' \
			b'jPwNBh1pJHIGjLAHS8baRajkSmDCrupo1zeBVNnlTGhluCMdN1Ju86FRyZ1X6kCnQdfQB+X+57CPGnGuy7DOZPPqsrl2cQxwZCgFzrSFo2URE3042DR9Fhv1PD7C2VJwglGBkz4unENwEF62jJk+HKzY3xc7wTq4CD9lhqEt4Sgsu8ix1MLQcpthKtRPUIye' \
			b'gVUfoCdoxRujK7i9mH3CWBiV1oRHeMehEUNQi98itKVg8YrQi3G2sBdBhMAXzxLGUY5uDRCjLKBEuA/BGN+d/d8C5yQvlOcoPwTPEtMTYsf8yYB7+IXia1CuUsqGDwnoe6SuLmJ99m3K5S5+N8A/BwEWiG/USAjBOc8L3QJqiJpPBMFeh9JEkRFgb1/BGahF' \
			b'og16zRRtsMwAKBDOxc9mFBKFiVRCJGI8o/haSFwCYPcIK4Kv/Y+A6nztfeSz5v9wx58dJKOXNWvPlFuYWJINbTmxdHdELpVYHoBYDBGLmSEWyBAz3WaHmmCYTwzzSaATk+jEFFeiEzNKJybRiUlf2JtLmErGmCR/8xaLxCfSDiVPzzR9ILAHpkhMhO0xnzgn' \
			b'sUqkR3kHoWCOIvEtxw2cQd4mkw8Jg0PP84VZwBch3zO+IK+D+SKlayVZpD5Gt5MrOJuoSLnwzZwpOEW7eGKEHvShQx4HcsPRWWEJI9QuxpkwgSUmmBu56XYM3XQ4vYZogEdv8N7SPdCALa5EA6MjOl0a0qF3700AlghgZFynEGOLAOITaYcyp2eaPlB0H0YD' \
			b'hsGgzIdAvxt2FvJYWNfYGVCffppC9jaGmkd9uwD1gyIz1Cevg1E/JW0l6tuE+nYX6nM2UQlyXHoK1OcUre0dmAr/Ff4vBv57gv9+Dv77HfBP8RH+e4b/nuG/T/DfF1eC/1ErIbgD/Per4L8n+O9H4D8XYwv+4xNphzKnZ5puBfyPBozwn3wY/vsB/OexsK6x' \
			b'M8A//TSZUAj/HGoe/vsF8B8UmcE/eR0M/ylpK+G/T/C/y64QsolKkOPSU8A/p2gt/NsK/xX+LwX+oTJKtJbthn+stBPwD4loCf7pBRS8a+nO8E+h4hXhH4NuwT/4MvzTu/eFf/yExdsQ/gsxhvCfnkg7lDk90/SBHP7HAwb4z3wI/imnEvwXsbq2i06Gf/5p' \
			b'MqEA/kOoWfinULvhPyoywT97HQr/WdLWwT9mOsE/pWQC/kM2UQlyXHpy+A8pWgv/bj8D9MWQgKk8cMk8IIgHxBwPCAxjOrqNsQGFwNrDUwPx3tI9sIEorsQGYpQNRGIDsYoNBLGBGGGDXIwtNohPpB3KXETU9I2CEEYDRkJIPkwIAwtAEQsJIWQoEwJrIpML' \
			b'CYFDzROCWEAIQZcZIZDXwYSQkraSEEQiBLGLEDibqBA5LkAFIXCK1hJCXwmhEsLlEYIiQlBzhKAwDC2fGicECoG1RzEhKCYElQihvBIhqFFCSNPI6d17E4IiQlAjhJCLsUUI8Ym0Q5mLiJq+URDCaMBICMmHCUENCCGPhYTAzkAIrIlMLiQEDjVPCGoBIQRd' \
			b'ZoRAXgcTQkraSkJQiRDULkLgbGKxuQAVhMCP1hJC11ZGqIxweYxAc1HF3FxUEEoTI+gJRqAQWH14FirhJN0DI+jiSowwOglVpEmo9O69GUETI+gRRsjF2GKE+ETaocxFRE3fKBhhNGBkhOTDjKAHjJDHQkZgZ2AE1kQmFzICh5pnhAXzSqMuM0Ygr4MZISVt' \
			b'JSOkSaWUkilG4GyiQuS4ABWMwClazQjdCa1aOKf1CpUbzoQbaBKRmJtEBMLQPCKRrVMQtE4hZwj6hdWJJxQJnlAk0oQiChWvxBCjE4pEmlAkVk0oEjShSIxMKCrE2GKI+ETaocxFRN0HV0ESo2EjSSQfJonBtKIiFpIEOwNJsEqKFLQx1DxJLJhWFNWZkQR5' \
			b'HUwSKWkrSSJNKxK7phWFbKJy5LgMFSTBKVpNEriSFue0EuID3AsE+gHEKwD0hLxTsNsnUATgQ7BjEIsgRcCE4EAV31dm+OgRru9pt7xKlJUoL5coJQ2ryblhNSi1NKwms2E1cHsx8UZEyeE6AgokSsmDazINrg2uSJRydHBNpsE1uWpwTdLgmhwZXCvEGBJl' \
			b'eiLtUOYiou6DKyfK8bCBKDMfIko5GF8rYkHtC04myqCSTDQgyhBqlijlgvG1qM5ElOx1KFFmSVtHlDKNr8ld42shm1hsLkM5UYYUrSbKncvzKklUkjh3knBEEnO78kBJdUQSLiMJRyThEklQOCQJxyThmCRcIglXXIkk3ChJuEQSbhVJOCIJN0ISuRhbJBGf' \
			b'cF3NLihS6bnug6tgCTdyJZZIPswSbsASeSxkiRCGWYJ1ksmGLMGh5lnCLWCJoM+MJcjrYJZISVvJEi6xhNvFEpxNVJAcF6KCJThFq1libpVeZYnKEmfNErRyQ86t3OAwwBJ9xhI9sUSfWILCIUvwKg7JqzhkWsVBoeKVWGJ0FYdMqzjkqlUcklZxyJFVHIUY' \
			b'WywRn0g7lLmIqKOrIInRsJEkkg+TxGAtRxELSYKdgSRYJZloSBIcap4kFqzliOrMSIK8DiaJlLSVJJHWcshdazlCNlE5clyGCpLgFK0mibm1fJUkKkmcM0koWt+h5tZ3QBmlJR54Y5IAtxcTb0QSHA6qk+K1HorXeqi01oNCxSuShBpd66HSWg+1aq2HorUe' \
			b'amStRyHGkCTSE2mHMhcRdR9cOUmMhw0kkfkQSajBio8iFtS+4GSSCCrJRAOSCKFmSUItWPER1ZlIgr0OJYksaetIQqUVH2rXio+QTVSOHJehnCRCilaTxNyKv0oSlSTOmiQ6IolujiQ6DGP4FkiiI5LoEklQACSJjkmiY5LoEkl0xZVIohsliS6RxKq9BfET' \
			b'JOYWSeRibJFEfCLtUOYiou6DqyCJ0bCRJJIPk0Q3IIk8FpIEOwNJsC4y0ZAkONQ8SXQLSCKoMyMJ8jqYJLL0rCOJLpFEt4skOJuoHDkuQwVJcIpWk8Se6wIrSVSSOC+SIMu1mrNcQ7kky7XKLNeKLNcqWa45HJIEW64VW65Vslyr8kokMWq5zk4XUKss14os' \
			b'12rEcl2IsUUS8Ym0Q5mLiLoProIkRsNGkkg+TBIDy3URC0mCnYEkWCWZaEgSHGqeJBZYrqM6M5Igr4NJIiVtJUkky7XaZbkO2cRicxkqSIIfrSaJnWsF9XXwhB2lClPp4qLoQtKMYDk3I9hnBhRbmhQss0nBkiYFyzQpmMOhgYInBUueFCzTpGAKFa9koBid' \
			b'FCzTpGC5alKwpEnBcmRSMB4RHOXYslDEJwOJB1dPq8s5bGCNnu0UYzGSnSL5sJ1iMDe4iIV2CnYGOwVrpkhHG0PN2ykWzA2OWs3sFOR1sJ0iJW2lnSLNDZa75gaHbKLi5LgoFXYKTtFa4hA7lxRW4qjEcTHEocisrebM2j4jFAWDrkZm2VZk2VbJss3hsKvB' \
			b'lm3Flm2VLNsUKl6pqzFq2VbJsq1WWbYVWbbViGW7EGOrqxGfSDuUOb8ACHUMG3lDUodjLEbqcCQf7nAM7NtFLOxwsDN0OFgxmYDY4eBQ8x2OBfbtqNSsw0FeB3c4UtJWdjiSfVvtsm+HbKLS5LgkFR0OTtFq3qgLD+9nVMrH46PfK2vcNWuICeZQS7odZO+W' \
			b'c/ZuKNFk75aZvVuSvVsmezeHwz4H27sl27tlsndTqHilPseovVsme7dcZe+WZO+WI/buQoytLkd8Iu1Q5iKi7oOrmBQ1GjZ2NpIPdzbY3i081AiUgjsdeWzsdLAzdDpYNZmI2OngUPOdjgV276jWrNNBXgd3OpKkKzsdye4td9m9hY6l01CZwkWJoZzmnQ9O' \
			b'2WoSmTvis5JI7XKcCnms6XLA8Z9eMXgK6C7S0HgBaeCNSQPcXky8EWlwOKhOeBf8u6U7k4aWxRVJA4NukQb4MmnQu/clDT7jFG5D0ijEGJJGeiLtUOYiou6DKyeN8bCBNDIfIg3Kr9TTKGJB7QtOJougkkw0IIsQapYsKNRusojqTGTBXoeSRZa0dWSB+U5k' \
			b'QSmZIIuQTVSOHJehnCRCilaTRF25XUniokmC7N96zv4NxzaS/Vtn9m9N9m+d7N8cDkmC7d+a7d862b91eSWSGLV/62T/1qvs35rs33rE/l2IsUUS8Ym0Q5mLiLoProIkRsNGkkg+TBID+3cRC0mCnYEkWCWZaEgSHGqeJBbYv6M6M5Igr4NJIiVtJUkk+7fe' \
			b'Zf8O2cRicxkqSIIfrSaJunK7ksRFkwQZL/Sc8UJTGCCJzHKhyXKhk+WCwyFJsOVCs+VCJ8sFhYpXIolRy4VOlgu9ynKhyXKhRywXhRhbJBGfSDuUuYiYXAVJjIaNJJF8mCQGNosiFpIEOwNJsEoy0ZAkONQ8SSywWUR1ZiRBXgeTREraSpJINgu9y2YRsonK' \
			b'keMyVJAEp2g1SZztwu0WeUJUqrggqpD6PrdNJLoQc3QhKAxsm5jRhSC6EIkuOBxWLKYLwXQhEl1QqHilbRNH6UIkuhCr6EIQXXS8PA+/4GRD2Bb2T8RgEESMEEcSVdqh9EVKdHQVGyiOho0bKCYf3kBxQBxFLNxAkZ1hA0VWTiYabqDIoeY3UFxAHFGxiTjY' \
			b'6+ANFFPSVm6g2KPJLm6iuIs8QlZRqXJcoopNFDlVq8mjLuiutHECtHFvlGHIwG3mDNxQ2sjAbTIDtyEDt0kGbg4H1cmwgduwgdskAzeFilekDDNq4DbJwG1WGbgNGbjNiIG7EGNIFOmJtEOZi4hcHQcG7vGwgSgyHyIK05ZEUcSC2hecTBRBJZloQBQh1CxR' \
			b'mAWG7ajORBTsdShRZElbRxQmGbbNLsN2yCYqR47LUE4SIUWrSaIu6K4kcdEkIYgkxBxJCAxDJS6RhCCSEIkkKByShGCSEEwSIpGEKK5EEmKUJEQiCbGKJASRhBghiVyMLZKIT6QdylxE1H1wFSQxGjaSRPJhkhADkshjIUmEPGWSYJVkoiFJcKh5khALSCKo' \
			b'MyMJ8jqYJFLSVpJE6klQSqZIgrOJypHjMlSQBKdoNUmc0oJuVXniUniCJkM+CF/4/BrnDDHgDZFzB02GMnOToQxeyB3ZZChDk6FMmgzF4ZA7eDKU4clQJk2GMrK4EneMToYyaTJUfP3e9EHzoczIfKhCki36iE+kHYpdRNR9cBX0MRo20kfyYfoYzIcqYiF9' \
			b'sDPQB2slEw3pg0PN08eC+VAxyzP6IK+D6SMlTUShV5BImhVlds2KCh9QUX7DH2ceQb82E2s9m8ydEusCj8hL6WYc4SjAS+WMB+5bwFC2Ae7o58zd1M/Qc/0MTZ2M0cMAoXBy30Jz30Jz30KnvgWFilcycQ/7FlCgdOpa6FVdi02YLDvSt8ASl/3fNnNHIaUd' \
			b'yp2eaZK9MHCPBowGbvwJZQO4gXBQDjoXIA+F68LKvC5fl8fPgR6C+Jr6F8G5wM69oIMRdZrZuclrlCE4MQsIApOvWYiVhm7qYSDw7FydxxIbRYJjTAEvgh2+Bp2NkLqSHpR7hM2VwA+yf4QGphZ4QkFvwfMEnlcbeULOnR17mjxxZG4IvMCcgHwQuIB5IOL/' \
			b'OWH/SY0pOeoXuLl+gZvGeoMX9QUc9wUc9wVc6gu44kp9ATfaF3CpL+BWdQQcdQTcNtZvN/6jUNIO5UzPNL20aPaPBozN/uRDzX6C9tDm51xrs33/MJdZ6JYez7ft3YK2fdBQ1rYnr4Pb9jGNKxr0LjboNzsNzOELVCwcF4liWIhTs6shz+13xOO5BdQVjyse' \
			b'HwWPLRmC7Zwh2LbTeAwz1tj4a9n4a9n4a5Pxl0LFK+KxHTX+2mT8tauMv5aMv3bE+LuFx0koaYdypmeaXprj8XjAgMeZzwgeh1zL8diSYdeSSdcusufaBfbcqKGEx+x1KB6nNO6Px7ZdiMfhC1QsHBeJHI9Dapbi8dxa5IrHFY+Pg8c0FmLnxkLsjrEQmDvM' \
			b'YyGWx0Isj4XYNBZCoeKV8HjUzmrTYIhdNRhiyc5qR8ZCtvE4CiXtUM70TNNLCzweDRjxOPmM4THnVoHHNMphaXTDLhrZsAtGNqKGMjwmr4PxOCZkBR6LpXjMX6Bi4bhIFHjMqVmKx3PLfk8Tj+u49tGx+9TmzEB1AhDVc/itd+C3xseI35rxWzN+64TfurgS' \
			b'futR/NYJv/Uq/NaE33obvwsxtrA8PpF2KHN6pukDBZaPBoxYnnxyLM+HsYt4UNMoMxnZydvYXPQ2hp5Heb0A5YMeM5Qnr4NRPqVr3fA15jlBPaVkCuk5m6gAOS48BdJzihYgfTFCPbeGtyJ+RfzzQHxDiG/mEN/sQHyDjxHxDSO+YcQ3CfFNcSXEN6OIbxLi' \
			b'm1WIbwjxzQji52JsIX58Iu1Q5vRM0wcKxB8NGBE/+Uwifh4KEd9kiE/exuaitzH0POKbBYgf8jpDfPI6GPFTulYivkmIb3YhPmcTFSAXvpkjPqdoX8SfW5BbEb8i/nkgviXEt3OIb3cgvsXHiPiWEd8y4tuE+La4EuLbUcS3CfHtKsS3hPh2BPFzMbYQPz6R' \
			b'dihzeqbpAwXijwaMiJ98JhE/j4eIbzPEJ29TiN7G0POIbxcgftBjhvjkdTDip3StRHybEN/uQnzOJipAjgtPgficon0Rf24VbUX8ivjngfg0a8XOzVqxO2atWLwI8XnWiuVZKzbNWrGuuBLij85asWnWil01a8XSrBU7MmulEGML8eMTaYcyp2eaPlAg/mjA' \
			b'iPjJZxLx83iI+C5DfPI2Nhe9jaHnEX/B3JaoxwzxyetgxE/pWon4aYILpWQK8TmbqAA5LjwF4nOK9kV8XBKrGj1zyMxFA7984CNl1hKA24ME5HkRAWxPc3/b7UBFgqVDHZICVIyZM2ZUI3YQA75PEdQJZgbBzCASMwhXXGm/nVFmEIkZxCpmCJPXxQg1FHJs' \
			b'bbMDXwaRaQBoIHaKp0l0qA6IwXCsDCLQRPi4007ymeKIIh7utZNxBHsbm6ehjaFzjoDsGN9sZ4QnBIYcbLjDL8033CGvgzfccTiDXawnCxAEjO+LLL4h06hgOS5UxZY7nK7EGOgDfz1t+L9O4V+N/p464KbgFxKHa97soo1twuiRJyQzBFNCxgdMBguZYGqW' \
			b'DYI+IFjepI+oPTI5ppgUYxl9l6DuTLO7QNlD0LXbH1EXIakh9MyRMyIm1J3FaDmJk6Ge87LPgIsRCEdQMEDgAfg3P1slIN1muNVkhKzR+SblTBPAo83WhL9JAJptpRaYczDaANSsgJhl2AKoApBS4klAEgCHfjc4jDYoHwYfQrvQF6FrRwnZTiDFUpTYr1GF' \
			b'Taazg4qsYQTKrJCx1SpRdgo29oEMnwt7tifsg0NG2X0k7BD3jB8+jIVNR6D4udPGk4NbHXviySSWhL7ZieMJypn/Z2zp8A33jy9IANCF9ekSiAjngDfjWCP0Pk2U5k8Ba3SdhZ6Ml3r/nkw7gzxpcOuuwCcAjsoAx11foyWCjNzRaAn74Hg/2DsZB4l8eBhL' \
			b'KAaKFC7sFsBisBwb1mi7Lt8Xx//XdwhMWHURnfYDpmOAUwSjrLEDmrz6Bk/c8RhPs5ls8GBrl44u3cDwLh3TCCG3zuBKI5b4GF4AGulwt4N08Ar8MNhWEoeNvcAB0mMj8veEWIxWIJmQuxELhsvPBrXsnt0tsay7pe0DNJEmmkcqRyIEqhNoJg27XKTFfg6J' \
			b'UPzzQyMoG3t3wfqFXTDBuyZOd8PkaQ7rToIKyOd/w5AS7MzYHalJtGVXe+ixHO8G240E99TEipEmUmgeFc2i0BS6tybQiffLtgAH6zYaSzcdSqPMcdtBgynLR2sKQWbB63F2o14CQtwsik2ioU1KcONn2ORRzZtTwKSpGQd3b3Y6hRbOmn6ZOmQAKIGLs+eK' \
			b'LbTU3vBcDvmg5qdTasis7lbpg8xPzZ/9I89MOLKjTwM0ZoECxLqT1suZgcbi1spC0LioFsl0a6THOVt31Ao5Y8jgXFjU7pi1P5n1WAFbPj4oXOg77PCsnFW+NYnwoaGjO234gJmeJ4wh+C2NstxZf2YCSUCw/eAE92c9mjkbP7W8QzMLLPYAYOkfGFgyUPGa' \
			b'PG5b5BigUgFl7cy5EkxAc6fRNDkmltwtjrgDOjPt8XBEtBVHKo6sxpFT6eJcDo70B+BId0Qc6SqOVBxZjSO24sjd4ojPt/MYXL2mAdVTBIrTxYi7BASBMp/N0OmhAND86evDI0BBMLT4bK9YcBZYsNIae354gK+7QzjoaNruhVpS7mLdX/OnlY8Qhn1VegTw' \
			b'idAgKjRUaDgaNGB9PrGmwnWCg9GPPE4jJMgKCRUS7gMSqNSfYe/hOiFB20cexBESTmR6Z4WEy4MEXSHhLCHhXCZvVkgYh4Sp08SPAw9Ym09nuBGjnww6sDT3Cw74kUXgAAuzx07bTjARTtieOlobAeSAGZ0VQE4AQE4BNOxpgYY9KdCwDwEah7YoFkHFAXM0' \
			b'K1RcM1RgobtAc+ZdQAVVyDPqfCjzCKHfF29w4D6n+pBplxUarg4asFRd9EyHPaABM+MixiUUmDYlbvIADoKGQ2ZSVmi4GmjA8NcxC2oBNmBuXNagpfTtBjgQwsFdAjSYOjmyQsM0NGDY65ofeZ3mDAnNhpYgoc6RvHpIgLp5MjMkTwIR+v6q8EB0j5AWOpwq' \
			b'2WoEhjpD8hqBAcrw8edHniwwXF1ToVMw5khNhTpB8hoRAYptRYSKCGOIcC7zI30y4568D40Oo+dbHmkf3roQcw+sAO1toC4cDzUgO08EOyCDphBknwXa5kQmUK7fMteNn6t78i0LeU+tC5Uda3LZ2NGN/F8zYQphKKWqO88GyMrzYpe1QjCP8GgAt7M1YmH6' \
			b'FM7MNicysbICSwWW/YFFbP1fBSyiAssssAgGln4psJzINMwKLHcMLBcPKnLr/ypQkRVUZkFFzo6bZIDimjcQiVCEIITwg8BDI2xoAAxAC4KKiBMIEqG6y7xKCq6KdqIK9mV1G1YNrA4dHLPu8qIeSnks4LFwgwPLNJ5S03IhjgV4UHhTwY3FDUpYLAqQa1gE' \
			b'ugnNg9JLHW+pgrKf+pn9wZlM+BqR1VJ2A4oCOhbZrvbMej2OTFEFG6oq96YDSAFCQNSFCPqAN+Js0VwxsX4uVw7tPDUyvpgpycPFwUpqd+lJX4SuMsge11dA2wfRGcwYgXUqAtMOhKslPgCLsW+bWO9P7YwOvWXzRkjpPX3WoYcCpwMPo76/9febjX9nC9Hg' \
			b'+ca/xysVY/jEW/ST4AeNAa8JhwfdWjwn0jeEZHEENmwmKDScDeZ/aj4KW9IJtfGsR/+GZniINZ6caEgCtf/X/NPpf/hSDS+1k6/lw+TcxPuxlacH/9LBcF3uj58zI59T8EVPrbCDe4v7ps5+HY9diGPYsNsotJ4kS+VbqfEf0LvhXdrTfzP6j54KHJUGN+4n' \
			b'CtUaRbfrRPcS7ie9jzL7D1q+E89QVrdGVjsl7uCQplHxRZ8lwb9j5h804UsfbFBjA9pgozl74uHA3zFh/UjCxGTafDMLuiyu6KaMJLgtz6vvcdIhtKahwQQtJ9ypS9CqQgAmwCUAOtwvNWSR/yCNv2nKLg3Z1nO2iems61ruWQjKRsB2ykpf9Vs8FZdPvf2e' \
			b'iGl42W2v4tnU//k37Yo9/caBz8C5W8bJFxHieu+jlmw8P/PBLkpyt2+Z99L6DsJ9lHyfTTBJ/7g1QDT7XSi13DPSzis0w+7wlVsX6V6cGt61ExoX96112Rz9EiNesNX6HbybtC2PDG6qecCLkqxikmHz+v4+i7k5k5IOkeHqaQD1Hq/2Xt+++yL1j3U/lpf4' \
			b'9g4KPYzdrr1g8Hn/aJRyMyz4cOT9AxT/9gyqAHQDsouE7pqB951fMBJz39+YuKhMjHUxp8vBImJfVydMM7hggHzbd+EFdpllQSkbXK0ak1UDBiCv6KICsV+v//7qBVhQj3DR+GNba8V0rdDNNV1UIPYbF1jcDVxXM0xztxfY7pcFpcwQtXZM1g4wV13RRQVi' \
			b'rC99B7UDp9isqSEw4+auL5jYsiwo5clWZ7tWklRJdHNNFxWIse73HVUSUPS6imKa+7hgsteyoJQ1tX++o67Y5pouKhD7dc7NyoH3pVUm6ClVG9csv2DC314RYIrkTAhIOv+gDKvd+OkaBBOHruiiArFfN35tDcp1vbo2wWzo+7zy6caLY9Gco4PGAVbahU+n' \
			b'ZnXwW2/XMO2yWiZCTfP/YUIYzNFbe4HB+5D4930JBfpXAz815qLy01VYnoZl01zTRQVivzkGx4Vl25zYRVkoa52arlOuuaaLCoTae97OHU7UWVe9RlQHy78WXzBTfK8IgyustNojBq6TSmukMOf3G9I42ZxXzTlclOVjk7rPMMt1cw4XZfl+gxF3nOXS7JHt' \
			b'7ZKsN80DX0Bfq0OQCsbm2C/g+eNpoVuiCdvsdcEaoX3jrLt2fIn0sXJpwInro2/O7aK1SmPz9M9eG7Ds/cwu0sbeSwgubdkM7Faw/0WbEaT/694yfOP2u7OfRZj5t2QXafrkFgw8uKZVc4kXaXe/SQ2XqN2+ucSLtLv/oMGFaReWzV/gRdrdf2Di0rTbNZd4' \
			b'kXb3HwO5NO2K5hIv0q5t3kiFq68Zql3w6Lh29+ABWYiesFaFhgl8S+1Nrn+f0RjCZzecnihgnxEITcXIa2k0tFda+Z9Ci63QoDyM4VU/+C8kjU1rme2IIbEokL+nn7w4UhHKi04oNmDcoPWC4Jv26aJ9scKeWCLbCwv2i2CZdfkV2ATFCyE05iZ8MnwKSyYP' \
			b'3BnKZV9430Dp9iUTVqnAllyKn1hYycV2YLD/ot1XwNG1xvvCThqOhs58gLjRB7WZ4Ww64TMBfGgsAY6k8m8BH0tiw4k0wceH+f72/wELqfIk'

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

	def expr_scolon_1      (self, expr_scolon, SCOLON, expr_ass_lvals):                return expr_scolon if expr_ass_lvals == AST.CommaEmpty else AST.flatcat (';', expr_scolon, expr_ass_lvals)
	def expr_scolon_2      (self, expr_ass_lvals):                                     return expr_ass_lvals

	def expr_ass_lvals     (self, expr_commas):                                        return _expr_ass_lvals (expr_commas)

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

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                            return _expr_mul_imp (expr_mul_imp, expr_intg)
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
					(self.stack [-2].red.is_attr or (self.stack [-2].red.is_var and self.stack [-2].red.var in _SP_USER_FUNCS)):
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

def set_user_funcs (user_funcs):
	global _SP_USER_FUNCS
	_SP_USER_FUNCS = user_funcs

class sparser: # for single script
	set_user_funcs = set_user_funcs
	Parser         = Parser

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
