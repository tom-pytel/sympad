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
_SP_USER_VARS  = {} # user vars {name: ast, ...}

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

def _ast_mulexps_to_muls (ast): # convert explicit multiplication ASTs to normal multiplication ASTs with index information for explicit muls
	if not isinstance (ast, AST):
		return ast
	elif ast.is_mulexp:
		return AST ('*', tuple (_ast_mulexps_to_muls (a) for a in ast.mul), frozenset (range (1, ast.mul.len)))
	else:
		return AST (*tuple (_ast_mulexps_to_muls (a) for a in ast))

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
	if rhs.is_slice and rhs.step is None and rhs.stop and rhs.start and rhs.start.is_var_nonconst:
		if lhs.is_comma:
			for i in range (lhs.comma.len - 1, -1, -1):
				first_var, wrap = lhs.comma [i].tail_lambda # ._tail_lambda (has_var = True)

				if first_var and wrap:
					ast = wrap (AST ('-lamb', rhs.stop, (first_var.var, *(v.var for v in lhs.comma [i + 1:]), rhs.start.var)))

					return ast if not i else AST (',', lhs.comma [:i] + (ast,))

				if not lhs.comma [i].is_var_nonconst:
					break

		else:
			first_var, wrap = lhs.tail_lambda # ._tail_lambda (has_var = True)

			if first_var and wrap:
				return wrap (AST ('-lamb', rhs.stop, (first_var.var, rhs.start.var)))

	return AST.flatcat (',', lhs, rhs)

def _expr_colon (lhs, rhs):
	first_var, wrap = lhs.tail_lambda

	if wrap is None:
		return _ast_pre_slice (lhs, rhs)

	return wrap (AST ('-lamb', rhs, () if first_var is None else (first_var.var,)))

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
	tail, wrapt = lhs.tail_mul_wrap # lhs, lambda ast: ast

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
				ast = wrapa (AST ('-func', tail.var, (arg,), src = AST ('*', (tail, arg))))

		elif arg.is_paren and not tail.is_diff_or_part and arg.as_pvarlist: # var (vars) -> ('-ufunc', 'var', (vars)) ... implicit undefined function
			ast = wrapa (AST ('-ufunc', tail.var, arg.as_pvarlist))

	if arg.is_brack: # x *imp* [y] -> x [y]
		if not arg.brack:
			raise SyntaxError ('missing index')

		ast = wrapa (AST ('-idx', tail, arg.brack))

	if ast:
		return wrapt (ast)

	return AST.flatcat ('*', lhs, rhs)

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('-diff', expr, 'd', ('x', 1))
	def _interpret_divide (ast):
		numer = ast.numer.strip_curlys
		d     = e = None
		p     = 1

		if numer.is_var:
			if numer.is_diff_or_part_solo:
				d = numer.var

			elif numer.is_diff_or_part:
				d = numer.diff_or_part_type
				e = numer.as_var

		elif numer.is_pow:
			if numer.base.is_diff_or_part_solo and numer.exp.strip_curlys.is_num_pos_int:
				d = numer.base.var
				p = numer.exp.strip_curlys.as_int

		elif numer.is_mul and numer.mul.len == 2 and numer.mul [1].is_var and numer.mul [0].is_pow and numer.mul [0].base.is_diff_or_part_solo and numer.mul [0].exp.strip_curlys.is_num_pos_int:
			d = numer.mul [0].base.var
			p = numer.mul [0].exp.strip_curlys.as_int
			e = numer.mul [1]

		if d is None:
			return None, None

		ast_dv_check = (lambda n: n.is_differential) if d == 'd' else (lambda n: n.is_partial)

		denom = ast.denom.strip_curlys
		ns    = denom.mul if denom.is_mul else (denom,)
		ds    = []
		cp    = p

		for i in range (len (ns)):
			n = ns [i]

			if ast_dv_check (n):
				dec = 1
				ds.append ((n.as_var.var, 1))

			elif n.is_pow and ast_dv_check (n.base) and n.exp.strip_curlys.is_num_pos_int:
				dec = n.exp.strip_curlys.as_int
				ds.append ((n.base.as_var.var, dec))

			else:
				return None, None

			cp -= dec

			if cp < 0:
				return None, None # raise SyntaxError?

			if not cp:
				if i == len (ns) - 1:
					return AST ('-diff', e, d, tuple (ds), src = ast), None

				elif not ast.denom.is_curly:
					if e:
						return AST ('-diff', e, d, tuple (ds), src = ast), ns [i + 1:]
					elif i == len (ns) - 2:
						return AST ('-diff', ns [-1], d, tuple (ds), src = ast), None
					else:
						return AST ('-diff', AST ('*', ns [i + 1:]), d, tuple (ds), src = ast), None

		return None, None # raise SyntaxError?

	# start here
	if ast.is_div: # this part handles d/dx
		diff, tail = _interpret_divide (ast)

		if diff and diff.diff:
			if tail:
				return AST ('*', (diff, *tail))
			else:
				return diff

	elif ast.is_mul: # this part needed to handle \frac{d}{dx}
		mul = []
		end = ast.mul.len

		for i in range (end - 1, -1, -1):
			if ast.mul [i].is_div:
				diff, tail = _interpret_divide (ast.mul [i])

				if diff:
					if diff.diff:
						if i < end - 1:
							mul [0 : 0] = ast.mul [i + 1 : end]

						if tail:
							mul [0 : 0] = tail

						mul.insert (0, diff)

					elif i < end - 1:
						mul.insert (0, AST ('-diff', ast.mul [i + 1] if i == end - 2 else AST ('*', ast.mul [i + 1 : end]), diff.d, diff.dvs, src = AST ('*', ast.mul [i : end])))

					else:
						continue

					end = i

		if mul:
			mul = mul [0] if len (mul) == 1 else AST ('*', tuple (mul))

			return mul if end == 0 else AST.flatcat ('*', ast.mul [0], mul) if end == 1 else AST.flatcat ('*', AST ('*', ast.mul [:end]), mul)

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
		ast2, neg = ast.src._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return neg (_expr_diff (ast2)), dv

	elif ast.is_func:
		if ast.src and _SP_USER_VARS.get (ast.func, AST.Null).is_lamb:
			ast2, neg = ast.src._strip_minus (retneg = True)
			ast2, dv  = _ast_strip_tail_differential (ast2)

			if dv and ast2:
				return neg (ast2), dv

	elif ast.is_div:
		ast2, neg = ast.denom._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('/', ast.numer, neg (ast2)), dv

		ast2, neg = ast.numer._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

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
	elif expr_super.strip_curlys != AST.NegOne or not AST ('-func', func, ()).is_trigh_func_noninv:
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

	return AST ('@', f'{var}{VAR.grp [4]}' if VAR.grp [4] else var, text = VAR.text) # include original text for check to prevent \lambda from creating lambda functions

#...............................................................................................
class Parser (lalr1.LALR1):
	def __init__ (self):
		self.TOKENS_LONG.update ([(v, self.TOKENS [v]) for v in self.TOKENS_QUICK])

		lalr1.LALR1.__init__ (self)

	def set_quick (self, yes = True):
		self.TOKENS.update (self.TOKENS_QUICK if yes else self.TOKENS_LONG)
		self.set_tokens (self.TOKENS)

	_PARSER_TABLES = \
			b'eJztXWuv3LaZ/jML9BjQACIpktL55jhOa6ztpLYTtDCMwHHdItgkDmwn20XQ/77vjRdpNCONZs6ZG2H6iEPxfnkeku9L8eb1n14++vrp18//VP3pv97/8g94hJ9PH3/1Ch7fPHzx+PlTsHz14uEjeSh5anh+8eT518/CUwWLlgi+/BrjeE5/v3j85+8fPXz5' \
			b'+KXYnz0Mrl8k63fJ+g1bXz59+PIvX0Bq/425iBZyfvTti6d/x1/R8u1X3z5/9M3fgw09vnqBf7/9IgRi6+Nn37z6+8vHlL1vsQDfPUR/z548/xYz+OT5qz9jGZ48o8D0968v0PdTqpyv8a2k8AWFfPT1s2cPQ4Whw4snf/7Lq5C3FyHvL3p5x19ffvGUHDBT' \
			b'f4U/D599g9bnX0oNoe2LZP0uWaWGHj99+RgTfvHkGT6/fPLdky/R8ohr/+Uryt83T6lgUORQxr+9fPyIPHz55KuvsMaeP6GWf0QZePj8S6wHfPH1C0kwNB9mmWN9BKV9FZ7Y/M8efvPy1dcY/hVV/OO/PcJ2ISeoecUPCP3ov8H66bcfPv3+9uOn3zP7J7C/' \
			b'e/vx/efvP3z8/h8//PTp89uP2WuwwuMteXv/71/By4+//xzsn3779f3H8OOX9//6/u3Hf6V3P4D157efv3/34Sexffzwv8nGCX96/+nTu2j7NdpCNG9/SNbPn2Ni/3z77nOw/0qxsvNvv7xLGf3nP39NuYmZ/unHaP3xl88xvz//9tP3P/78a1bMPKKskNGa' \
			b'osSwaAm/P7//GN/9/vbjwFv4+Vue27f/+Eewvvvt40//F378+9P7VNIfPr599z/v489Pec5+fx/j+u2XHz/8EhN9G/2/S8WjSo4l+ZCi/C2r719iln748ZcPsUQfUitAfmIrvPvw889vY+Bff3z/7n38Af0ry9Cvnz5/iInEpo5Z+/BTyj1F2vvxKQv5/U+/' \
			b'v/0pOnzikG+q1zcr21XOP6jY0qKl8finrRr7QH7CL7J18MdV6OAe9Bz4VxvCQYAuOKGVfK0olcZVN6Yy4G6qRoHlQXQlt+SwonDa8x8LiWqONDiZes3JtrkTWsGmLP9xplopzir8QivYMCBkGZLjhD1aMDhkhjJi+Y9XD+Qn5I2iaKobSE05/P8guHT5L1WL' \
			b'Bd0wzgbLrjope2MeBFdxiw4rzWlAjSrINdS4k1ixgBxtx38c5FRz5jAWsGJbUo3DG25C+Rnsmbvmx4qSa+i/6cLrBi3wNOL+gH+sGnHk3FKD6joUqomu4rbmoJOD6jusNNW9gQwZzpHiP5ZrBmyrhrJsHP+xmEeuGvi1MtyTMUt1fGHji6bhP55TBBs0KNWc' \
			b'rm6wS2BTcX7RxeW/vDzRCcPCe4OJs4f40w6dQtP23e36z4GTW/854mMQrV//2Qu0akyWtdTrJRMDBzd08JkDDNcboyQLkIj2Pef0c2VoFEK3ujG60tDnsNXrykNASAEHGudvgw8EJhj98zzCj77HVUOjBaGpq3wdujaOXHoBfZLHJLa9hdBtPjThZXRPLpZd' \
			b'uuTiyMXWycWziwouK039VmNv4B6s+Q/WXchucHK5E1rR5vnPShBSrGhruLuHIJBhQ73aygtpfxwrDcED5O6GurKgIUSluJFgJFOcyvAfh6OCqwyBSFG8CHIqWKgwSmEtNgEDuB7QkZ3kdy1xgiNAtQ49qeceXMCBup3hP9DFHshvGLbkh/5jxXIQtGAFG/7j' \
			b'8A2HgV9oxRqAl9pSpuWn57gAMJSKlBR6FrCJYBOhPHMg9hcTfXC/zNoQ3kslg+ONSwOSfrYpbeAjrnJM10RbLTbdBIsNFhcsBEUaurTGNlTUGtHJ0IgYOqWfEAPZFP9xWHHS29mKidQVUyckcKPanJuQbShr2vIf28XBrhkGsHSa/6SpAjY3FcAq/oNMaqUu' \
			b'FFnRVoeXD+Qn/Aov2AkK5LnyXR2aB2nfUsIOI3AxAuwFjiJwKrwgr+IkoaznQiO6QTlhXvS6rhQMCwWFh6SgjRtkMujJ1ENsBdgIAxC6CkBMh/ABQ7y1VeuA9Fv4D24wwBT0aoUTAYXRKawryBGkC6StavTroaGpMwE9Q3JgIDQ0mNI4fYBnDcQLKeoKOh2M' \
			b'7NZXbVu1kGhddarqIB7Ik4JMKcihajAtSBtyA02tCQ8VFFlByRrCd2gRhDjwg94rwDLo28rgf0gcCqSwRPAOQ0LKCpJWBn+DZyh411Qd/MW8Y7S66iCqGrEPSBrpuPNV11YeTFe1UCmqanXVmqqF8FBQBSWFBobu4GjEA8A4BzNQmHvCgECE9gr4GSHdA1HD' \
			b'xMtVHhsCgkJOLc3xoBdiHWGlQoQ4jQXrAxzD4BOa7wbbDR2g7eDx+gbyiT+xivBRs69G3kKx0BkrAR8dvX2NdEe/KarS5ifW5jcdN57quKVrabWWGxNbAtu45UalFqJnCKa0dBkjz0Y8OImIGhBcWu4GmiNoJPo6+qJOVBDitHvL6xtLDd+rS6lFrr2xeuP6' \
			b'ivW0Vj/9OtlUIVIP0Bmd5s7n6hPIi4Af9jDq0V56tKaBcP8Z0p4zpO2R0hekaKVetCkD+xwGdgHgc2inG8ohzcXa0l7n0F7MA0gQ1HCx6qjSYhVJ1YQayasAihyLdvwiZb1ovecclYqxinnySUOElh6EabijAslXUPgyIo4/IozM3oysFJqwBtBdQbTTbz9Y' \
			b'GhLzKIhZQdTKYuEgYxaLD6GhyKWVTqCVutJKp99KXV1a6QxaSZVWOvVWuulkXqF4P/qGKoE3F5uyB3EOLUgF500jEUTQNvEbEr9K28rukuw2yxTSSkPL28aX5j6D5m5Y5KAct21HP4+fs5Ne4bJwTXLGLrLvzPI1bNz49kYZgUIj4pqOx03H46aT0aWMDDcj' \
			b'wpywNBOJXheEPyK0ETEgthPFajm4DctuK9FTzkrT0bZ4J/vhnuVfnmfnKFjVumz3LKnRVnpfy3285U7ZGhFYShdmMQhSCndinMPhextkSDwiHHt33MM9y25q8FuDPyoeQnx3PdULNcMV5hhfvC1VgopHVCVMXJ5hz7tNNROG9xXVkOfB6Hkwel86zY2XuaoS' \
			b'gWysBJa6CSwFsbEVjRvRu9Am6Fl4VDIuSlQnP60lLSnN6lG6KDydYPsY1tc3rrTPCbYP6gtq0UiDZ2mII4oQbBkhJ9kwWNtatC7hWRrk6A1SE5lIBRYVj7vbAFM0qyqT4FMfES2xOKp7l+Y6g+ZqbGmnc2inAn/n0E50nIUWMZYWMUcmzZGjN3hyoZZ1FiF1' \
			b'mbTcXf1j8kc5isEbHZgwrxZ4X6rlX7WR9hfh3+ZzWm/kHBjunfCCo3SPw7WSEajgbWKWQ3kRYol8laUOUZuFBm6p+0OMEIJn1GjloWBFXm5Fwt1EFSIbNFKkaRSfv0A1S4yhq/khbal486q0zR5tgzFyZfLktFTiogUzVWKpr9n11ZT62qm+bKmvXeqrcTwJ' \
			b'w0k3qgV1gnEsjcpUt1RQeWR5SK7UJWzVcVct1b2lujtb6miqjixRhLX4waRSM9kMpBNJpG95/dbT3PA88dugiax00Lyk96dTJlI3FLU5zWpzmtXmNK/zeM1o+a2TKZjjFawo8lxND3iNCoG0jd0VjfLq5LfdXqPiZtEZOPIGtcp1/q4IKkjFMWkYIwf4a60K' \
			b'3j08mRzdKAZw1GlmPvNXymfeFoA8qmTIyeLNddfaA+trLbgrQ++oQ8/L5rzX19oDfemBR1YLkNW1KEcFLU5YQvKBAXzgsvIBfcseHy39YpVPIyqf5kHQOTTpi4O0Y0heW46ufKblDHoEFNawmN3w51C5jRU9bRcaGB+IFSLNZ08csuVGN+IaPsprlLhTF6P+' \
			b'Vr5/dQpNjuJ82lqjjenSHEdvDtWEUdfJmbsu4KcJSgFalAFIpl/A83SazpdRdApNgWowhtVgDKvBmKAGY/LvuGAdmaDTYTaJT25UIDN+sNeGpzuNl4Ay+zH8u2O/Hfu1kowl1aki2hoR+rnyjY71BRJBflE02r3uSOCpRa5oWK5oWK5oHqRtYRqdCr/bzh9P' \
			b'b3iYOh61pI33hj6/wbNhIV7t5cmaq45HvOdAjiHGM/J4RgXPqXufFk9NWfkedeVbYwvQ4rQJGpe8/ml4/dPw+qeRJU5DqxbC8sAYgUuiBqa8t1FK32wWyEMxG+6WDXfLJoi7KZATbRvHv3kKeHVbRDRQrCiDW2kuG+bC3FyWm8tyc1lpLitD33IdW65jW+Zm' \
			b'xx97jLt2/dMjrpwlOoPmQ0iyfC7DhQs1HO7rYQFtIlMafo6Hn+Phh96q2ANc0YPbjn2OpxCQlhdUo6cNTGKj4pQvVTlx4owv+myxCrFq+UhR/CJbqN+W91dYuQxXJPgZJPwCEt4yFGeJWJfcr1uOs5Vmke0ZJ+3j5dnK/ICvKqLMdKXBJhrMlDqawgeokCb0' \
			b'OC09TefLGfwEYc1dlJ7ogWU1dYU3IVaa7qLAfXi8j6LLSs2E1SLV4kLKhIJ2VEAjtCxcnZWELkeVDQ6uz7zC1psF20RLawxalCkeapJ6QSDxVmqm4ZqKhMy8y9IlYSIceEj++BFF/HggfjkQv5iHn8vDb+Xht+Hww3D4QTT8wiJ+wBE/3ojVhlWGV87hJANP' \
			b'IKLwCr+6jS2JjI2kjHsV+BlN1JmHXqpxeQj51HiQEaYSGlpK43c4cOJRY1WCPzwvjece8RgMVi/WL1Yw9jqsZexSWNVY17jMxO6Cy1Aos8bveOEZJNxkxEOTuP+Le8EW78zFFgI3VIxFeTKUSaNuDX4yp3XQ5Hgrcov3INNV03jhMl65ileT4tW14Ib3feIF' \
			b'o3h/K16LWtNdunQnLATD66jxYk2cRfEd3HR1Kt7niteQaoy5xlth6WJbiI1uVMYAeBuzoiuiMXZoI7xenG9eNfge0+8wDnqP4bFxV9jXVx1lhG5wRve6rvjuUEwA0oYGW1GZMDN4E6mnK1EdXfFK98PSVdCYJbormu4WpetMcbpHRe0wL1R8eOs7KQ/eXErX' \
			b'iteYLF7uC/1nhde8erqWlS4brVZ8Tyveo47Fw2jBZ4tPulS3xtwrRRcY02W8VEtY9Xj1Kl7oSvVD151DOCwQ1gX87igVDIWthJ2br+nF8HRTOd0dvkLMWCForDqsESu3NmNW8c5dahOMCdsLJ9orvLfW47XgEDVemuzx+nasN7lR2recF0W3CCvMGd70ThUG' \
			b'oeDZUlR01y4kBaNl1WKHMW8QXhBUCqRcFaQUPCl4cld4ohFPNuGIG4MSn6ZXOaYYn+0q9KdddwEuOO3T2U79DliDh7in8OZicKYeYI2fwBuP9esnkMVvxhZfeR6PfgRhfMIYP4Yy/j5xxnNeja/Svx2xxs9Cm8sEGcxVBjR+AmqqP9wt0pa/ReJq8Yf7Dyq+' \
			b'TeAPbyB2AYVo3ZgvCXtYFDYVB/uZvMk5gU5alr/zYUpWu7q3zh1dNyfU6q9XE3z5sAyP382u853XRpa+vPyOe7px+ZotXfMlbkQ+naEfa7JEtcBcVTAi4siuDN55TCgJ/vDD+VNoiV9In0JMvK4ML8PqISeExTsq9kZQLSgK/lADc1c0xS+0zEJUm6GqZmRF' \
			b'ff8euoJ/PHMZURbHKu4/2AmgBQ+IZRAvPQRv0a7lwaiLmyuWsYmetNnuGXwpLcZf9hZNBGMKs4bGBCgMx3TRNW2S6OXQTDnC5sTnEJ4phez/GlynXGPvjqWofa9IVE2cFFVPBuXDFHqp4ehL5WsHLxn6MUI8SRvQP0u7FiYI6QZCEC/ICzFGSxQRrNNMwb62' \
			b'k0Vo/4wyxOkQxNGrDJT5L2ARKiYTCUeziUgk305qtY3JZqQSMxPJhWnFwQMwjNkFoe+WhgTgwC2SH4zjW6ie/9AXl7bQjp038z1ftglUk4R286lGH4huCtXcE9U4pho3QTVYKW7zvB5HhBOGccIwTgjGJYJxPZMIxo0STNpXSEEWs4tjcnEj3JLHv8Yr8Q12' \
			b'YzduiFNc4hMql97gt6PalvqkgZFe5YuIHpf0qqCWsIFFJA95TF5F39MMMmO5ESLLGYSdDsIgqWwL6cMl+nDb2EOqynLWvaSZc4eUahtzjBCG3XefZE+2OAmemMMRZRlyRtzgmRum9nvUlg0fRVo+TAyy56PCysMnYvA9k4hhdB9IpY0gjnshJch6Y2y5kWdm' \
			b'jRLiG+OHOU/vHCfQW2KMegxbSJkL0wDXV0YCeSgadWINPCAJ51FRf2df0zzgZ/CARJbzADsdhAdS8RbyQNqPUltXEVJVlrMe0sx5QEq1dAXhCiEUQrg4QuiYELopQui2EAKHJ0LohBA6IYQuEULXM4kQulFC6BIhdHsQQseE0I0QQp6ZNUKIb7AHd+OGCKEb' \
			b'EMKox0gIyUUIoRsQQh6KRl3wI4QgCedReRV9TRNCN4MQJLKcENjpIISQireQELpECNvkE6GqLGfdS5o5IUiplhKCL4RQCOHSCIFAmKRv2wkB32wiBCxMzYTAEbB3VfNTCIF9RRMJgbyuEQLahRA47mWEQAlRDtcIoZeZISGkN/ih3nrcICHogTx53GMghMyF' \
			b'CYHrKxFCL5SqdbQKIYSE86i8ir4mCYF9bSeEEFlGCOJ0CELIireMEDCoEAKXZgMhhKqynHUvaWaEEEq1lBDa3UTbl0QLvjDDxTODZmbQU8ygyY+Txxg/8CsaRVr4QQs/6MQPumcSP+hRftCJH/YQWVNClMN1fsgzs8YP8Q3yg95oiCL0gCJGPUaKSC5CEXpA' \
			b'EXkoogixBoqQhPOovIq+pilCz6AIiSynCHY6CEVkZVpGETpRhN5GEVJVlrPuJc2cIqRUSymiKxRRKOJyKaJhimimKILMig97jVME+6BR1AhFiG6pTuqlum8SRTSjFNEkimj2oAjWN8XHGkXkmVmjiPjG+GHOewEdp9GjiFGPkSKSi1BEM6CIPBRRhFgDRUjC' \
			b'eVReRV/TFNHMoAiJLKcIdjoIRaTiLaSIJlFEs40ipKosZ91LmjlFSKmWUoSqC0cUjrhcjmBNWD2lCYuZs8wRdgNHsA8aRqIDy5jJz8ARtmcSR4yqwOqkAstxL+QIyxxhRzgiz8waR8Q3yBF2oyGOsAOOGPUYOSK5CEfYAUfkoYgjxBo4QhLOo/Iq+prmiBla' \
			b'rSGynCPY6SAckYq3kCOSSiuXZhNHSFVJ1r2kmXOEvFrMEeqETlEcmyl2PT9R2OKM2IIVlvSUwhJminWW6CFsoZkwcs7gXzSsRHlJi/KSTspL7CuaxBmjyks6KS/pPZSXNCsv6RHlpV5m1jgjvjF+mPNeQFcHW482Rv1G2kguQhsDFaZeKKINsQbakLTzqLyK' \
			b'vqZpY4YKU4gspw12OghtpOItpI2kwqS3qTCFqrKc9ZBmThtSqsW0QYd/SUeWOQAJQBP0D0C/QYhPQLwBhQl/I0Z6wb6AaQGzGKcIJxgDYFxjqkcwb/jTgYU7C3dePnca3o0zU7txhgxyp8l249Cu5cHcKf4Ud3jiTiN7cibtyQ1M5E4zuidn0p6c2WNPzvCe' \
			b'nBnZk+tlZsid6Y3xw5z3Aro62HLuHPcbuDNzYe40g225Xigch8Eq3BnSzqPyKvqa5E4zY1suRJZxpzgdgjuz4i3jTpO25cy2bblQVZaz7iXNjDtDqRZz59YThIU2Cm1cCm20TBtTXxvCHstH1U12VN3wUXWTjqqLP6KNVmijFdpoE220PZNoox2ljTbRRrsH' \
			b'bbRMGyNfD+llZo024hsZuZnBzpXeuzrYerzRjpjEG8lFeGNwDr3nh3hDrIE3JO1eEVT0Nc0b7QzekMhy3pCaPARvpOIt5I028Ua7jTekqixn3UuaOW9IqRbzxtRBwsIbhTcugjc65o1uijfYD/JGl/FGx7zRJd5gf8QbnfBGJ7zRJd7oeibxRjfKG13ijW4P' \
			b'3uiYN7oR3sgzs8Yb8Y3xw5z3Aro62Hq0Meo30kZyEdroBrSRhyLaCH6ENiTtPCqvoq9p2uhm0IZEltMGOx2ENlLxFtJGl2ij20YbUlWWs+4lzZw2pFSLaWPquGGhjUIbl0AbDR84aaYOnGBf5TMn9BDaIByRB9OG+MNh1cjhk0YOnzTp8An7iibSRjN6+KRJ' \
			b'h0+aPQ6fNHz4pBk5fNLLzJA20hvjhznvBXTRltPGuN9AG5kL00YzOILSC4XjMFiFNkLaeVReRV+TtNHMOIISIstoQ5wOQRtZ8ZbRRpOOoDTbjqCEqrKcdS9pZrQRSrWYNqYOJRbaKLRxEbTBH8XGx3baUOQHaUNltKGYNlSiDfZHtKGENpTQhkq0oXom0YYa' \
			b'pQ2VaEPtQRuKaUON0EaemTXaiG+MH+a8F9DVwdajjVG/kTaSi9CGGtBGHopoQ6yBNiTtPCqfAkzThppBG6FlMtpgp4PQRkpgIW2oRBtqG21IVVnOupc0c9qQUi2mjR2PLhbaKLRxnrTBMvFmSibekCHayGTiDcvEmyQTF39EGyITb0Qm3iSZeNM3iTZGZeJN' \
			b'kok3e8jEG5aJNyMy8V5m1mgjvjF+mPNeQFcHW482Rv1G2kguQhsDmXgvFNGGWANtSNp5VF5FX9O0MUMmHiLLaYOdDkIbqXgLaSPJxJttMvFQVZaz7iXNnDakVItpY+txRns1zNGOk4cvBHJxBGJYIdlMKSRDhWD3ZZ1kk+kkG9ZJNkknWfyRoEN0ko3oJJuk' \
			b'k8y+okmCjlGdZJN0ks0eOsmGdZLNiE4ydsWUmzVJR3wzyPfAYHZcHfwGHulE3jEWIsk7kovIOwaqyb1QJO8Qa5B3SPv0yqGir2l5xwzV5BBZLu9gp4PIO1LxFso7kmqy2aaaHKrKctZDmrm8Q0q1lEr01lOPhUoKlVwclTQsMG+mBOYdKeM3LDNvMpl5wzLz' \
			b'JsnMxR8tR0Rm3ojMvEkyc/YVTVqOjMrMmyQzb/aQmTcsM29GZOa9zKwtR+Ib44c5z00nKxL2G5mk4UXJWIi0KEkusigZSM57oWhREvzIokSaJ4/Kq+hrelEyQ3IeIssXJex0kEVJKt7CRUmSnDfbJOehqixn3Uua+aJESrWYScrZyLvby8JKbAqP3BmPNBu4' \
			b'xM1ZmrAk3UxJ0rFnsyTdZJJ0w5J0kyTp4o/WJSJJNyJJN0mSzr6iSeuSUUm6SZJ0s4ck3bAk3YxI0nuZWVuWxDfGD3PeC+iiraeANeo3LkiSiyxIRJKu8bwdfchcFiZ5aFqYiDUsTCQPeZReRV/TC5MZEvUQWb4wYaeDLExS8RYuTJJE3WyTqOvUULg4qeXc' \
			b'pPTU3gJFSreYVqYuTi20UpYlp0YnS5YleHEodEV8bKURvM/MEI3QQ2gE7VoeTCPiD4cVPXXDz5qfQiPsK5pII+R1jUbQVWiE415GI5QQ5XCNRnqZGdJIemP8MOe9gK4OtpxGxv0GGslcmEa41tJqpBcKx2GwCn2EtPOovIq+JumDfW2njxBZRh/idAj6yIq3' \
			b'jD4wqNAHl2YDfYSqspx1L2lmtBFKtZg2ymnzQhtXQRssWbdTknVLhmgjk6xblqzbJFkXf0QbIlm3Ilm3SbJu+ybRxqhk3SbJut1Dsi43jtsRyXovM2u0Ed8YP8x5L6Crg61HG6N+I20kF6GNgWS9F4poQ6yBNiTtPCqvoq9p2pghWQ+R5bTBTgehjVS8hbSR' \
			b'JOt2m2Q9VJXlrHtJM6cNKdVi2iinzQttXAVtsBDETglBLPtB2sgkIJYlIDZJQMQf0YZIQKxIQGySgLCvaBJtjEpAbJKA2D0kIJYlIHZEAtLLzBptxDfGD3PeC+jqYOvRxqjfSBvJRWhjIPvohSLaCH6ENiTtPCqvoq9p2pgh+wiR5bTBTgehjVS8hbSRZB92' \
			b'm+wjVJXlrHtJM6cNKdVi2jjnw+aKmMMU8rg08jD+Lr8QyQSipwhEsx+MNyMQzQSiE4GIPxpgQiBaCEQnAmFf0aQvRI4SiE4EovcgEM0EouQkCEFd21SSnnwqkvITsrL2rciYYeOHZeiVx9XB1vtW5Kjf+K3I5MJUogdU0gtF34oMfphKQtp5VF5FX9PfipxB' \
			b'JSGy/FuR7HSQb0Wm4i38VmRHQsD4vchtdBKqy3L2vaSb0Uko2WI6KYfQC5GcEJHcGYk4Fp27KdE59joWnbtMdO5YdO6S6Fz84bByIjp3Ijp3SXTOvqKJJOJGRecuic7dHqJzx6JzNyI672VmSB3pjfHDnPcCJltOHeN+A3VkLkwdru5TRy8UjsNgFeoIaedR' \
			b'eRV9TVKHmyEyD5Fl1CFOh6COrHjLqMMlkbnbJjIPVWU5617SzGgjlGoxbZRD6IU2roI2+BC6mzqEjl2OD6G77BC640PoLh1CF39EG3II3ckhdJcOobOvaBJtjB5Cd+kQutvjELrjQ+hu5BB6LzNrtBHfGD/MeS+gjMzBIfRxv5E2kovQxuAQei8U0YZYA21I' \
			b'2nlUPgWYpo0Zh9BDZDltsNNBaCMlsJA20iF0t+0Qeqgqy1n3kmZOG1KqxbRRDqEX2rgK2mANKzelYYWdjTWsXKZh5VjDyiUNK/FHtCEaVk40rFzSsGJf0STaGNWwcknDyu2hYeVYw8qNaFj1MrNGG/GN8cOc9wK6Oth6tDHqN9JGchHaGGhY9UIRbYSaFdqQ' \
			b'tPOovIq+pmljhoZViCynDXY6CG2k4i2kjaRh5bZpWIWqspx1L2nmtCGlWkwbO96pe6e00RTmuDTmYN39+2GQegOLNAMmaXI2YcUrN6V45cgQm2SKV44Vr1xSvBJ/xCaieOVE8colxSvXN4lNRhWvXFK8itEvJBTWvXIjule9/KwRSnxj/DDzvYCuDrYeoYz6' \
			b'jYSSXIRQBrpXvVBEKGINhCJp51F5FX1NE8oM3asQWU4o7HQQQknF0zGtBbSSZB9umwZWSMDGMnhJXJiF3FSWrcX8Yqbu420Ds5gLWooc4xreS2aRe15/QFfQHq+UU1P6V5r1r/SU/pUm6hi9iBc7qWbGoKdm76RzpZPOle6ZpHOlB4yBnQodg8qVXs4Wq6Cq' \
			b'q0c+YEJ9L/1f17uKWTV+mPv0DpWu9EDjatRj1Liin9hDkC0YFc1gAYL5YX+UMxqGNhN3yHskjJB9/ImjQKwzFK/0NGeEls0Vr9hplDOkMDMpg6rASkYWal5poguCIbtN6BEay3LmKaT2mAJ4GyxIQgn7hNG0tzSViYxR35KOQ43MAanAUL3l2+MTc0ydRD9V' \
			b'5jg6WwSmCCyhMnYQZoiMcG5scFI7Uaw85aaUp1y3Gf0dh6f1gihMOVGYcklhin1Fk9YLowpTLilMuT0UphwrTOFjiP7rC4SYNVwgdOOGVgcDpahxj3FpkFx4acBgH9YFUne1ztYCrALlWPnJzdJ8cjM0n0Ja+fyfnQ4y/09VtPukv4uT/tVWjaeQguVse+lw' \
			b'+WaSlGjbZF/m+ITQU4e6C0IXhD4qQnsWMfspEbNXmxEaNatFrOxFrOxFrOyTWJl9RRMR2o+KlX0SK/s9xMqexcp+RKy8htApa9AbB7lN7xxHmiP0uMeA0JnLCEKHussR2rPI2LOw2M+SFPsZkuIQWYbQ4nQIhM6qaGeE9momQocULGfbS4fLEDqUaC5CT52f' \
			b'LghdEPq4CM3SXD8lzfVmC0Ibek0ILRJcLxJcnyS47CuahNCjElyfJLh+DwmuZwmuH5HgriN0zBoitBk3hNADee24x4jQyWUMoaXOegjN0lnPclk/SyjrZwhlQ1o5QrPTQRA6VdHuCG3mIrSkYDnbXjpcjtBSorkIPXVU+VQRuuyPnwian5p+Dg4rRHQ3hehu' \
			b'C6I7ek2I7gTRnSC6S4jueiYhuhtFdJcQ3e2B6I4R3a0jei8za+ge3yC6u3FD6O4G6D7qMaJ7csnRPd8O74XDMcdVKlgv6eYxeRV9T+O+m4H74i3HfXY6CO6nsi3bBkergD+XZhP2S1VZzrqXNHPsl1LNwP7eTvfUuePCAYUDzosDPHOAn+IAv4UDPL0mDvDC' \
			b'AV44wCcO8D2TOMCPcoBPHOD34ADPHOBHOCDPzBoHxDfGD3Oe3jlOoMcBox4jBySXjRyQhyMO8BkHSLp5TF5F39Mc4GdwgESWcwA7HYQDUtkWcoBPHOC3cYBUleWshzRzDpBS7coBU4eFCwcUDjgvDmiZA9opDmi3cAAZ5oBWOKAVDmgTB7Q9kzigHeWANnFA' \
			b'uwcHtMwB7QgH5JlZ44D4xvhhztM7xwn0OGDUY+SA5LKRA3JfxAFtxgGSbi/rKvqe5oB2BgdIZDkHSA0eggNS2RZyQJs4oN3GAVJVlrPuJc2cA6RUu3LA1MnfwgGFA86LA1hDxk9pyPgtGjKewxMHiIaMFw0ZnzRk2Fc0iQNGNWR80pDxe2jIeNaQ8SMaMr3M' \
			b'rHFAfIMc0I0b4oCBtsy4x8gByWUjB+ThiAO6jAMk3Twmr6LvaQ6YoUcTIss5gJ0OwgGpbAs5ICnT+K1yAKkqy1n3kmbOAVKqXTmAjvE2lZ24ze3iqaC557vbFlICFH8+LTTnRw3YS+/u63M4oFDQymo6OEAmLnPDkJupguKT01da1gta1gs6rRd02zPp83Oj' \
			b'6wWd1gt6j/VCUKbXIwuGXm7WvjqH6WPGWXQwyHwKh8ffeMmgWqGMjvBog//44bnksok1euHo03PZyiEk3yuDir5z1kDQH//23MjqQfOdmv3vz0mk+ffnpEoPwB4Yj5XMLPwAXUujYZ4sOVQc9+nWS8IZh4SyJQ4hF/zryN5a+uvIHchEswa9bolKuur1NiJZ' \
			b'p5COmMMIZwhJZAwh9DCbGzZq9BANENxns/4I4yN6OD39m1bgeAYMT83Me7C7L9ya3SF2FrS2DKc9KA0QisNoNnxuBM4w5OWkagDKiIwjsBgwcW9AnFaMCdC3Gn4WLWLYqGpLX6kFAWq1pm24EZEmJ7I9EDoI/CD2LMCceWCDMIMY0weYAC2AFlCarWgxOue8' \
			b'N8AIU0foSgU24L/eAB1zYWO3aRdNqs4UO7KpEzZrwZDReUt2Ae0AR3bCELXrjMMfA0OGS04EE3O3gAJ5UR53ECEM9LGTB5i95yU7AsxGcAnLubMAGMpt/l/ARlEMdw84xAu4wIW32pwTAI2Dj6bbOOYCUPUHdNFbKAkufqBVdl/81BNQlHbIDohGAYFsQiDI' \
			b'y1VOayLq2C3TmrDJBG64NUEbTdiCvo9E3tERdY2HyvGkeYsLbpN//Qf++wMiFY1iRqKdkKo5GlpFdHIJnbA9y5QoQySNwTdPiQjlLe11rpR8ElpTrVs7wKm0/0mvMQ9UEXT9mY16o/ijpdmU2W//BuphdJ//7iBM4AtFFLrZDmG4B39OMIZfwNtphdbMW6FB' \
			b'1d/9JGrDBKrJoYmQ6WQmUsNVGrYntt0ENFH+zxOesJfsumqzGw+WDiZNWj7ytXnl1hx6r/hO50pXPk/C6f19bv8cdOvn6POdbK5jy1yHgUQfZPvHnqzAaeNUBfKHGcTP3OJ3btWxEGWoAnAMVAE73gXX4Epsk1bY2ErMrCNNXHHd2UrrLPaD1qYxOMhb0vBY' \
			b'8SfXmva4EOROB4VWuOjCJCjVjYKtkdVXXHkNF1yU2259ZeWq16cBUhvVpQ4uIT/HeU5EILfPTnRCm7Y9b7BhrTUvGmnNvUrKz3yKk7Zz/F6S8uqP7hZIi7aY/amgyDRyYLYOMb85SxSZO5+ZiSIXOGfZvO1SkyrqgeYpZ44hUhOzZiaTa6V2OXjg93TvGz/c' \
			b'4dZIS0/RrKlIH2ONZE4bT/BCkdMHFZqJY6SHWwJtgBZrdsUX7L7H3YuhOpm/BppEmm4PpOnuH2kylNH1kWcrR0KZgjB76gX30QXb8DQmL8cGl4MCC1Tv8vVPfVxgUQVYCrAcAFh8AZY7ABa1B7Co4wKLLsBSgOUAwHIq2y2XBSz6fHZsr26X9gSR49RB45AI' \
			b'oakcZ7Ufuy8iVH/A6LhFaERxDuSjgMM5gcNCIfC5AgQNqQPiAw/RS5bXHOJkdPWHb24Jm2Fg3SKmElY0BSsKVpwGVtBgObHJxPWihXO3AN6EEbZgRMGIO8QIwoPzXXBcL0ZYfwv4ThhxMoqoBSMuFCNcwYgzx4gzUjMtGLEZI6CraCijxm8jHh8vaGCf2h4m' \
			b'BT8ZuJDc3D1aUEKz0ELTlVPwaiNuNO3tig/Y17eIvjAEbgn3oJ+CA30bxe6he1oQ5XQQ5RRQpD1FFAnFOA0Uae8LRfadc8zCjj20SQt2FOygr7dfrhT1ENjBo/PM1iuNuyVWgM6OElW6y8DtoyBasOJasYI61xVoXOyAFVQlF7O3gbMJGmAdzS9IWuL20fks' \
			b'WHFtWEH+r0k9awZYUJ1c3k6owbuScJTgDUq0I+qKGmfBikmsIL/XqMl5vUITgxOLuiGMKNqcBSMYI2icnpgy50lgBGXuyiBCkxInDhxU66wdYUXR5rxirMDufCq6nCcLFVc5nVAIEYqnE0WZ85ohQhWIKBAxBRFnpMtJ+VP86eP7hovRG4+P+bnjcvB0V/DA' \
			b'dlxByPZ4MAIPd0JggniyCVJ2OaHuTkbZc/mXiVHteOzq9bOYe9g7mn+4Kt1adQ1gokb+L9HlIlzqYtn0+U5RFl4pPm+eQvWEF71g6C3zlRY1u1iIcjJKoAVpCtLshTRm7f8ipDEFaWYhjRGkUXOR5mRURgvS3AnSXAfKNGv/F6FMU1BmFso0k3svCWEgidcY' \
			b'iGGFMYUBhdHEEo5YRBCED8aOHDgINcL4N/kYNTI229ExyeNxMP6GY4XGB2T4NVZ96vuh28ceH3s7dlTu5A13berVsUeP9ebUk2P3wx4XuwZGS11CbegJdDXTWpuvNQ03By1VoXceoNIZgCP0tlz9CLMIn71msAuawo9DV2wSGqB33SZYFIKI2DY6tA/Gr/Wg' \
			b'oeL43a2xeECN7GHmjaYP0mhqW7u5y2q7DOLH2y+g8721Iaq24IWhDVUCUrW19ALl2B3Mb8CdZymanG31Wrv6Df51bx7A82YFYxcdFL5fQZ+AyRDGhuWlG7JWBt0U3qENZE43o3u6RxgmToCUuoIWBELocBoEbWXxejdwwZkT6hU0fJ95uAgYOxfMfeAX3qIB' \
			b'4K/wdBFeqeuoRKtm99Tg7eZ/FKnFSP3GaOVOwG5D/BanhHbwL93vp3N3Ss6NJNdgitBR8Dv6NX2bdjJ1vgoj7JHj51wttq/kCma18R/OABx/djb770b/8VtDO95op4+14nimrPuFWa93zH1bTf/DafKGd5TXdkle203ZHVyoNZp9o7IiQDQT/3C+33fhmbfl' \
			b'GTbkN3vT4KKoo4J1IwXTG8sGaIjrm66/plkvsOqXGb8XVXekKowTKpxZ0bfNNB+bROxDMEIswm+upjqqZRfPcX0BzOGde1xvZnPd4S2rtAZpuB4R1LkuoftpujZdrkV/w8Q0NO26U+/dpv/TMW0LvTnGgcvAuj2PGyPing3OR+3aJBC8N8NFVrt2epgBwNLg' \
			b'Tro+5Aro/MhDQFe7Gcp1s2OgrSZMwA4Y5Zrhxtcnh3hqQ5Obu252Ux3d4D7R0EkfJm5ubnNkeGuqezRc5CYWGS8J6O6wn+NK6jy6OqqAoOl4x7W9O6PuNPbthtt/bAkyv8urA/R63PBdanC3evdgXHI37Pm4oXwf/V+dwRjALZfMcKZ1NXA+uMGtmLtOY4Ph' \
			b'TjG2ztzcEeZx+7JR4aqBwZ30ddeZBkU587xyPbRlcGweHLgNeUWGe8Rui/87HBkoeT2C4X3IuoyLLePCVtdkuEfstj8wfzW4bGy46rAGRf7zvHJt6DI+No8PFFxdkeEeMbamPsT4oDXskjGC2jqHNqgRM88rV8raqrsMk2yY2OqaDPeIsXX4oYYJtvSyoeKq' \
			b'uzCoJzbPK9dNWalvGy2+uibDPWK3Zbpbugs/d9CEhkoDp63mG1R+2ykA6ldO+ECukR9cY2VBv2UMoSLRFRnuEbst6BePobyxF48n1Ke+S5NrK88OxVpIe+0ILBMUn9LYwu4DBV8fY3UaZ7hJz2MN/qMSF2rtLTUoAd8n/F0b3aDimxu4uTEbdyBVkHkLMrvq' \
			b'mgz3iN20Do6MzL46McN1aMqo2jKq2uqaDPeIZmddnkMq7ywbYCNth0fIZhtUHN8pwMCEk1o7hKBzVumMFVX9bpsbp1v1tjoHw3U+pux9jnXuqnMwXOe7bUscus6N36He9Zy699U9G6SwxT64Dca072eQ/RGbwcxpirbayeDZn13DLDNbUuIGWXhq4MQbBA9t' \
			b'n5nhc0xjKvwX0By6OjfDzbHz8YKLO1ODHz7Y3fB3DdL/ZbEMY1yPO/vZ8zMdS2a4qU/vMMG9N7WtLtFw8+6m6HCJzYsfLLlAw827+/bBxTWvqi7RcPPuvkVxcc2rq0s03Ly774ZcXPOa6hINN6+vXpuGDggLWrfRQcZ3hw5YheSIJ1l4eQp1/zrvAFDR5AOb' \
			b'Daoazxih6ED0v2FyN+obGq3/n33rNd/YeBQCmn7wXzecd2uyb2QY6grsDgyU90fqQr2uE7oNfRWLzhOia/ruF39jK3xfq8m+q4UfMZH6sP1U8Bsp+A1iSwWlJENS2DNlC8/xMINXr7F3Q8+kg13YJ+WNx98iFyZ5MH3Mo8EvquGABNdWKq1N3wLhmRVe6Kud' \
			b'Ihf+EAFe2wmxoIvnbOPlfMEF/Lx58P8iqmZk'

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

	_VARTEX   = '(?:' + '|'.join (sorted ((x.replace ('\\', '\\\\').replace ('+', '\\+').replace ('*', '\\*').replace ('^', '\\^') for x in AST.Var.TEX2PY), reverse = True)) + ')'
	_VARTEX1  = fr'(?:(\d)|({_LTR})|(\\partial|\\infty))'
	_VARPY    = fr'(?:{_LTR}(?:\w|\\_)*(?<!_))'
	_VARUNI   = fr'(?:{"|".join (AST.Var.UNI2PY)})'
	_VAR      = fr'(?:{_VARPY}|{_VARTEX}(?!{_LTR})|{_VARUNI})'

	_STRS     = r"'(?:\\.|[^'])*'"
	_STRD     = r'"(?:\\.|[^"])*"'

	_FUNCPY   = f"(?:{'|'.join (sorted (AST.Func.PY, reverse = True))})"
	_FUNCTEX  = f"(?:{'|'.join (sorted (AST.Func.TEX, reverse = True))})"

	TOKENS    = OrderedDict ([ # order matters due to Python regex non-greedy or
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
		('IF',            r'if(?!\w|\\_)'),
		('ELSE',          r'else(?!\w|\\_)'),
		('OR',           fr'or(?!\w|\\_)|\\vee(?!{_LTRU})|{_UOR}'),
		('AND',          fr'and(?!\w|\\_)|\\wedge(?!{_LTRU})|{_UAND}'),
		('NOT',          fr'not(?!\w|\\_)|\\neg(?!{_LTRU})|{_UNOT}'),
		('SQRT',          r'sqrt(?!\w|\\_)|\\sqrt(?!{_LTRU})'),
		('LOG',           r'log(?!\w|\\_)|\\log(?!{_LTR})'),
		('LN',            r'ln(?!\w|\\_)|\\ln(?!{_LTRU})'),

		('NUM',           r'(?:(\d*\.\d+)|(\d+\.?))((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))(?:_{{(\d+)}})?"),
		('ATTR',         fr'\.\s*(?:({_LTRU}\w*)|\\operatorname\s*{{\s*({_LTR}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"((?<![.'|!)}}\]\w]){_STRS}|{_STRD})|\\text\s*{{\s*({_STRS}|{_STRD})\s*}}"),

		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
		('SLASHSUB',      r'\\_'),
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

	_PYGREEK_QUICK = '(?:' + '|'.join (sorted ((g for g in AST.Var.GREEK), reverse = True)) + ')'
	_PYMULTI_QUICK = '(?:' + '|'.join (sorted ((g for g in AST.Var.PY2TEXMULTI), reverse = True)) + ')'
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
		('OR',           fr'or(?!\w|\\_)|\\vee|{_UOR}'),
		('AND',          fr'and(?!\w|\\_)|\\wedge|{_UAND}'),
		('NOT',          fr'not(?!\w|\\_)|\\neg|{_UNOT}'),
		('SQRT',          r'sqrt(?!\w|\\_)|\\sqrt'),
		('LOG',           r'log(?!\w|\\_)|\\log'),
		('LN',            r'ln(?!\w|\\_)|\\ln'),

		('VAR',          fr"(?:(?:(\\partial\s?|partial|{_UPARTIAL})|(d(?!elta)))({_VAR_QUICK})|(None|True|False|{_PYMULTI_QUICK}|{_VAR_QUICK}))(?:_{{(\d+)}})?"),
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
	def expr_mul_expr_1    (self, expr_mul_expr, CDOT, expr_neg):                      return AST.flatcat ('*exp', expr_mul_expr, expr_neg)
	def expr_mul_expr_2    (self, expr_mul_expr, STAR, expr_neg):                      return AST.flatcat ('*exp', expr_mul_expr, expr_neg)
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

	def expr_frac_1        (self, FRAC, expr_binom1, expr_binom2):                     return AST ('/', expr_binom1, expr_binom2)
	def expr_frac_2        (self, FRAC1, expr_binom):                                  return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_binom)
	def expr_frac_3        (self, FRAC2):                                              return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4        (self, expr_binom):                                         return expr_binom

	def expr_binom_1       (self, BINOM, expr_subs1, expr_subs2):                      return AST ('-func', 'binomial', (expr_subs1, expr_subs2))
	def expr_binom_2       (self, BINOM1, expr_subs):                                  return AST ('-func', 'binomial', (_ast_from_tok_digit_or_var (BINOM1), expr_subs))
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

	def expr_cases_1       (self, BEG_CASES, casess, END_CASES):                       return AST ('{', ('-piece', casess))
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
	def expr_curly_2       (self, SLASHCURLYL, expr_commas, SLASHCURLYR):              return AST ('-set', expr_commas.comma) if expr_commas.is_comma else AST ('-set', (expr_commas,))
	def expr_curly_3       (self, SLASHCURLYL, expr_commas, CURLYR):                   return AST ('-set', expr_commas.comma) if expr_commas.is_comma else AST ('-set', (expr_commas,))
	def expr_curly_4       (self, CURLYL, expr_commas, CURLYR):                        return _expr_curly (expr_commas)
	def expr_curly_5       (self, expr_ufunc):                                         return expr_ufunc

	def expr_ufunc_1       (self, UFUNCPY, expr_pcommas1, expr_pcommas2):              return _expr_ufunc (expr_pcommas1, expr_pcommas2)
	def expr_ufunc_2       (self, UFUNC, expr_var, expr_pcommas):                      return _expr_ufunc (expr_pcommas, name = expr_var.var)
	def expr_ufunc_3       (self, UFUNC, expr_pcommas):                                return _expr_ufunc (expr_pcommas)
	def expr_ufunc_4       (self, expr_term):                                          return expr_term

	def expr_term_1        (self, expr_num):                                           return expr_num
	def expr_term_2        (self, expr_var):                                           return expr_var
	def expr_term_3        (self, STR):                                                return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1].replace ('\\}', '}')))
	def expr_term_4        (self, SUB):                                                return AST ('@', '_') # special cased for last expression variable
	def expr_term_5        (self, SLASHSUB):                                           return AST ('@', '_') # special cased for last expression variable
	def expr_term_6        (self, EMPTYSET):                                           return AST.SetEmpty

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
			return (_ast_mulexps_to_muls (res [0].no_curlys).flat,) + res [1:] if isinstance (res [0], AST) else res

		if not text.strip:
			return (AST.VarNull, 0, [])

		self.parse_results  = [] # [(reduction, erridx, autocomplete), ...]
		self.autocomplete   = []
		self.autocompleting = True
		self.erridx         = None

		lalr1.LALR1.parse (self, text)

		if not self.parse_results:
			return (None, 0, [])

		rated = sorted ((r is None, -e if e is not None else float ('-inf'), len (a), i, (r, e, a))
			for i, (r, e, a) in enumerate (self.parse_results))

		if os.environ.get ('SYMPAD_DEBUG'):
			rated = list (rated)

			print (file = sys.stderr)

			for res in rated [:32]:
				print ('parse:', res [-1], file = sys.stderr)

			if len (rated) > 32:
				print (f'... total {len (rated)}', file = sys.stderr)

			print (file = sys.stderr)

		res = next (iter (rated)) [-1]

		return postprocess (res)

def set_sp_user_funcs (user_funcs):
	global _SP_USER_FUNCS
	_SP_USER_FUNCS = user_funcs

def set_sp_user_vars (user_vars):
	global _SP_USER_VARS
	_SP_USER_VARS = user_vars

class sparser: # for single script
	set_sp_user_funcs = set_sp_user_funcs
	set_sp_user_vars  = set_sp_user_vars
	Parser            = Parser

_RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: # DEBUG!
	p = Parser ()

	# p.set_quick (True)
	# print (p.tokenize (r"""{\partial x : Sum (\left|\left|dz\right|\right|, (x, lambda x, y, z: 1e100 : \partial !, {\emptyset&&0&&None} / {-1.0 : a,"str" : False,1e100 : True})),.1 : \sqrt[\partial ' if \frac1xyzd]Sum (\fracpartialx1, (x, xyzd / "str", Sum (-1, (x, partialx, \partial ))))}'''"""))

	# p.set_sp_user_funcs ({'N'})

	a = p.parse (r"x_{1}")
	print (a)

	# a = sym.ast2spt (a)
	# print (a)
