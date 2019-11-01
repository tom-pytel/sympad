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
						ast = AST ('=', (',', tuple (vars) + (v,)) if len (vars) else v, t [0] if len (t) == 1 else AST (',', t))
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
			return _expr_diff (AST ('/', ast.numer, neg (ast2))), dv

		ast2, neg = ast.numer._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			return _expr_diff (AST ('/', neg (ast2) if ast2 else neg (AST.One), ast.denom)), dv

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
			b'eJztfWuv3DaW7Z+5QB8DdQCRlEjJ3xzH6TEmTjJ20ncaRhA4bvcguEkc2EnuXDTmv1+uvTcfUlElqaqO6yVYPmJRfD/WIrk3ybvXf3n19Osvv/7qL5u//K93v/7Dv8LPL5998a1/ffPk5bOvvvSGL14+eSovJW/t3589/+rrF+GtgkFLAJ9/jTC+or+fPfvr' \
			b'D0+fvHr2SswvngTbz5Lxb8n4DRtfffnk1b995mP7d6QiGsj66Xcvv/w7fkXDd19899XTb/4eTHD47Uv8/e6z4ImNz1588+3fXz2j5H2HDPztCdy9eP7Vd0jg86++/Svy8PwFeaa///ESrr+kwvkaXyWGz8jn069fvHgSCgwWL5//9d++DWl7GdL+spd2/Pr8' \
			b'sy/JAon6D//nyYtvYPzqcykhmD5Lxr8lo5TQsy9fPUPEL5+/wPvz5397/jkMT7n0X31L6fvmS8qYz3LI43++evaUHHz+/IsvUGJfPaeaf0oJePLV5ygHfPj6pUQYqg9J5lCf+tx+G96o/hdPvnn17dfw/y0V/LP/fIp6Iav/zUWPl+I68aE8/Xdv/PjHjx//' \
			b'fPPh45+Z+WNm9sa3bz68+/2H9x9++MePP3/8/c0Hb+W/vCFn7/77N2//05+/BPPHP3579yH8+PXdf/3w5sN/pW8/euMvb37/4e37n8X04f3/TSaO7eO7jx/fRtNv0RSCefNjMv7+e4zsn2/e/h7Mv1GobP3Hr29TQv/5z99SamKif/4pGn/69feY3l/++PmH' \
			b'n375LctmHlCWyWhMQcIvDOH37+8+xG9/vvkwcBZ+/pGn9s0//hGMb//48PP/Cz/+++O7lNMfP7x5+3/exZ8f85T9+S6G9cevP73/NUb6Jrp/m7JHhRxz8j4F+UdW3r/GJP3406/vY47ep1rw6Ym18Pb9L7+8iZ5/++nd23fxh29UWYJ++/j7+xhJrOqYtPc/' \
			b'p9RToL0fHzOfP/z855ufo8VH9vn95vXdfdNurHu0YUMLQ+3wp93UzSP56X+RqfN/7AYW9lHPgn+1wZ/30AUrGMnVPcVS282d2Rhvbza18oZH0ZbsksU9+dOO/zQ+Us2BBitTbVn5PGRWMHqTaviPNZt7xUn1v2D0Jnj0SfbRccQOBnj3iaGENPzHqUfy06eN' \
			b'gqg3dz42ZfH/UbDp8l+qEgPsEGaNvKtO8l6bR8FW7KLFveY4fIkqn2pf4lZCRQY52I7/WJ9SzYlDKN6IuqQS91+4CuVnMGf2ml/3FF1N/00XPtcw+LcR+0f8474WS04tVaiuQqbqaCt2WxY6Wai+xb2msjc+QYZTpPhPwyXjTfc1JdlY/tMgjVw0/te94ZaM' \
			b'JFXxQxM/1DX/cRyjN/kKpZLTmzs0CVQVpxc2Nv/l5A0r+PXfDSJnB/FnM7QKVdu3b7Z/Dqzs9s+Ci0Gwbvtnz9N9bbKkpVYviRhY2KGFyyx8d70zSpLgI9GuZ51+3hvqhb5Z3Rm9oSqvNs778sGjl3HiSp8BSb7fz3Dlf/Rd3dfUSYBI3cZVoUWjw9IH3xS5' \
			b'K6LKG++7zXuk/xjtk03DNl2ysWTTVMnGsY0KNveamqtGI+CGq/kPiiwkN1jZ3ApGmBz/uRdgFCNMNbfy4MUn2FBjbuSDVDu6SE2o4FN3Ry1YQNAHpbhufAemMJXhPxadgYsM+KMoXGCbCgbKjFIoxTp0fS4HWLKV/K4kTG/pEVqHBtSzDzbeglqb4T++ZT2S' \
			b'3763khv6j4JlLzCggA3/sfjCfvwvGFEC/qOrKdHy03Gv9zihVGSijW6oZTVdgCQCd6Y+tBfDn7lFZhXoP0oJe8s7mzoh/WxTxJ6DuLwRqYmmSky6DoYmGGwwEPxo3541KlBRVUQrQ91haJV++hDIpPiPRalJU2cjIqk2TJc+gjvV5nwEhqGk6Yb/NF3s4Jq7' \
			b'PnKn+U8aHqCuKQON4j9gz0bKQpERpip8fCQ//a/wga18r3eWCt9WoW6QhoYitgjAxgDQBCwFYFX4QE7FSnw1jjMNRPP59GOh19VG+T6hfOZ9VL6Oa7CXb8bUPJqNx0Pf+3w78fjSATt8/26bTWs90bf+v7fzvUv5Jq1A/grBKZSVT5GP1xO1quDW+Yqmtuaz' \
			b'5KPzj/ftK0xpDBn8u/Jk62PUG9/ifLdu3aZtN62PtNp0atP5cHyalE+U8ilUNeLycfvU+Kr2SGPwsfH/LXJe04AN+ObdwPnGA5lv2Mrgv4/cZ0ghR/4bfPqYlY9aGfz2jn3Gu3rT+b9IO4LVm84HVQH4PDGDgju36dqN80+3aX2hqE2rN63ZtN6/z6jyOfUV' \
			b'7JuDpe7u0cVaP+r0403fIQDPTnlOBp77bur8YMtuHCrCe/UpbWhc51shygiF6gPE0NUbH6EDe5e++u5Qb7Dwdedfr+98OvETRYRXxa5q+eqzBWsUAl4dfX0NiqPfFNRa52dW53cdV57quKYrqbWWKxM1gTpuuVKphugdvCktTcbIuxYHVgKiCvQ2LTcDzQHU' \
			b'EnwVXVEjWhHivFvL67uGKr5XllKKXHqlcuPyiuW0VT79MhkrECkH3xit5sZnqzNIi4AfWhi1aCctWlNH+PQJ0o4TpJsTxS9I0Uq5aLN27Evo2CsAX0I93VEKaSzWrvV1CfXFPACCoIqLRUeFFotIiiaUSF4EPssxa6fPUtaKtlvOSakYRcyDT+oiNPUgTMNy' \
			b'io9+4zO/9ojT9wgjozcjM4U6zAF0tyLa+defnxoS8ygfsvJBqwaZ8wlrkH3v22d5raUzqKVuraXzr6WuWmvpAmpJrbV07rV018m4QvF69B0VAi8u1usaxCXUIGWcF41EEEHLxN+T7FXqVlaXZLVZhpCNVLR8rd1a3RdQ3TWLHJTluu3o5+lTdtYzXBauScrY' \
			b'RtadWb6Gyo1f75QRKDQirum433TcbzrpXcpIdzMizAlTM5HodUH4I0IbEQOinijUhr03YdrdSPCUsrXqaFm8k/Vwx/Ivx6NzCFa1Xpd79inRVlpfy2285UbZGhFYShNmMQgohRsxxnD43gQZEvcIy84tt3DHspvKu628O8oeIL67neL1JcMFZhlfXLMWCRSP' \
			b'qEiYuBzDnrNjJRO69w2VkOPO6LgzOrc2mjsnY1UlAtlYCCx1E1gKYuNGNG5E70KboGfhoFi8KlGd/bCWtKQ0q0fpVeHpDOvHsI6+sWv9nGH9QF9Qi0aaf68VcUIRQrP2kLOsGJS2Fq1L/14r5OQVUhGZSAGuKh4PtwCmaFS1DoLPvUe0xOJQ916r6wKqq27W' \
			b'erqEelrh7xLqibaz0CSmoUnMiUmzsPUGOxcqmWcRUq+Dlocrf0R/kq0YvNCBiHm2wOtSLf+qjNS/CP/G92l9L/vAsHbCE461eRyvloxABS8TsxzKiRBL5KssdYjaLNRx17I/Rg8heIZGK3eFRuTljUi466hC1ASNFKkaxfsvoGaJELqKX1KXihev1ro5oG4Q' \
			b'IhcmD07XQtxrwkyFuJbX7PKq1/JaVF7NWl5Lyqu2PAjDoBtqQZ1gHEujMtUtFVQeWR6SK3UJW3XcVNfi3lHcXbOW0VQZNUQRTYPTktaSyUYgnUgiXcvzt57mhuOB34gmsuIjU84nL6RmKOpymtXlNKvL0TiVsZwnjArnKpCnht1aGYhZnseKOs/NtIPXUAuk' \
			b'xexu1SvfnP3i22uob66aAydepla55t8NQQUpOiY9Y4Cqu9Wi4DXEs0nRnWIAh2Yz85m7UT5zzQqQJ5UPWZnC2e5WW2B1qxm3a9c7addzskTv9K22QLe2wBMrB/B0shEVqaDL6aeQvG0AL0wrH9Ep9ni19IsVP40ofppHQfPQpHMHad2QnLYc3HpYywW0CJ9Z' \
			b'w8J2w4eich0rejddqGC8gBUi02dH7LPlSjdiG47mNUrsqYlRe1tPwTqHKodQn5bWaHl6rY6TV4eqQ6/rZOddF/DTBNUALSoBtGK6guf5VJ1be9E5VAWUYQwrwxhWhjFBGcbkp7mgjEzQ7DBjQpQ7FciMX+y05uFO7cSjjH4M/+7YbcduG4mmIQWqVcBVEP3Z' \
			b'9aSO7QkSQf6qbrS87EjsqUXKaFjKaFjKaFiLVPo7n9wOgSJ1UMvWpI33PR2/weNgoVzt5M2aq5b7umNPlsHFMeY4xgPH8TqXpk31Ouc96Zy3Qg3QtLQOGpc886l55lPzzKeWyU1N8xVC8cAVgUWiBqZ8b6KUvh4XyPts1twga26Q9TpiOH27YJ2DevtYDLvu' \
			b'c7mI6rPccXmydHOLqUQsjWyeaATemjBrZHhrGN4ahrdG4K0RkmwYkxrGJP/ylBe6RbMqru0ufMucb7l0fZQ23DhiseSJXtYkbSYqb7uW6cReMY0yQmO0RLK8GSiepWa5oJ00Y3o3gWob3hGhyLrl+z1bEx23vI7CSmSYeeDQI5x3hDuFslrScLnW0s5aMmsZ' \
			b'TaFDU4eVOyvt08m7lQEk32WFBtdxS+2kOdfBnxb3Pa1IWLDwpdrggsONpismsLCOaya6rHSY61uMUjAzMqFAOioIIyMaGeZkOaYLT2XFgss9L9jt6kPdaam1Qc3z6MiXOLWWMP5ppQRrLtE6DVdYVCTYiaLCmAnnIuI8QBwGiEPwcAIejr/DcW846w1nnOHQ' \
			b'RJzJiPMYcRgjTmLELXIYm2FTISRROEgbtY2BDsYyWHjAyZhQg/ctWWPG59OosTfRj8C0r02NozUwXqtQjN4dtkBjKyN2tmAAiIJFq0TposmhiFHGmDWiOWFW6fOqsc8OW4rQyrAHEgu5vpy17w8aKtAAJmzXhXYQNIMgKIYmIRRmW/Q6XG7c4s5TujEa9ybj' \
			b'ClXcNoqraL0drvDEnaG4jxXXnFZ0Ny7d8eq94VZp3JWJwSdfpU1XoeJ+VtwsqhFyhVte6aJaHxpdjAwPNV20WsmNpL6OcEs436Rq8B3xdwiDvsM/KvYe/eG+o4TQRcywr6oNXweKCHzcvsLuKU9IDC4XdXTLKV8BTPe90o3OSBJd+UzXhdINpRglU1Y7pIWy' \
			b'7786XCGKS0XxsUKMuKfXF+k9Lm11dMkqXR26uedbV3ETOnKGEL3LFm+6H7dCwhXfHUv36lIBodRxkSquZ6WioQvLvT/kBcXgf3cUC3yhgtCu+cZd+Ke7xun273tAyj0w5b5DYTRy7zKSiutzqToQEqoKU5N73ELrcLG3Dxr3HztcwI4ikzuhXctpUXQhsELK' \
			b'cFc7lZX3hTcKrsV96BSwj65FWzHfA2aAJSuS3AySrDCywsgDwIgGjIzBhy0hiEuDrhxKjMuWX/qDsYfAFAwGdbbQPhNisAt7CmYuGl7cAGLUAphxKFs3AShuHFLcxjGsuAKwuAQtrgQu7lPCi+O0GrdJ/+ZDjJsFMleCLW6ILkjXbITZ/Ms+BlG5x6CqFj/s' \
			b'/0BdbQJ2eIG1C+BDk8h8ftiDoLDoOljv5UXgCVDSMheej04y9dW9SW9xEp3Aqj95Tajlwpw8nnld5SvTtcyDeS4e17zjXDabx+bz3bjSrDPgY/2TqMyXK/hFMCysseC+YgJI7w6H3k8BJU43nwJLXDWGi6x6oOn94n6Jg8FTC4B6d9CbXAqkRmdg2swAVCeg' \
			b'qreBFbrb0J6NAIu+isWIZgJjvQPAmA+TXgK1MGt5MeBipaVhyKU3CSMc4y7FxdDLzuITcZj8bAExAQojMV1STSsmen9UphShOvEeIjPFkP3fQuqUarTumIvK9bJExcRRUfFkKD6MoRcbel/KXzv4yKiPALEbNqB/FnclTBDiDYQgTsALMcSGKCIYp5mCXe0m' \
			b'i1D/GWWI1TGIo1cYkNTvwSKUTSaSvMzGyIS+2uBqSCoxMZFcmFasf/m+yOyC7v8YnOe77WNfKv9DhyTtYJtm3jj3ckkmMEySZc5nGD3BMnMYZmWXT8QultnFTrALCsWOj+LRG6yQihVSscIpNnGK7T2JU2yRU9LiQfKyN6FY5hNboJM8/C0qiV/QhG35IRqx' \
			b'iUIoX3rEbUelLeVJnSJ9kilDjzl6ua/EW+AMiT4PxKnoepovZkwuQmA5X7DVUfgi5W1PsrCJLFJYo1xhmSpsiSkkVwt5ojl0MeRAkjgLephDDeuk44JowTEtTC3sqB0rO4p0npgTZHFHhXmGS5zgek/ihOKCj0orPhz2nmwgs4vS5CJPzBYbxC/GDVOevlmO' \
			b'oDehKDoMa0WZDTMAl1dGArkv6nViDDwgEedBUXtnV9M84GbwgASW8wBbHYUHUvb25IG0+pSFNcoDMmUozhgkVwt5wK48sPLA1fFAxzzQTfFAt4MH2D/xQCc80AkPdIkHut6TeKAr8kCXeKA7gAc65oGuwAN5YrZ4IH5BC+7KD/FAN+CBosPIA8lGeGA4Gch9' \
			b'Ua8LboQHJOI8KKeiq2ke6GbwgASW8wBbHYUHUvb25IEu8UAKa5QHOuaBrsQDkquFPOBWHlh54Np4gLCXJGu7eQBfxngAzb5iHuAA2Lmq+C08wK7iE3mAnG7xAMzCAxz2fjxAEVEKt3igl5ghD6QvOEC3Kj/gAT0QE5cdBh7IbJgHuLwSD/R8qUpHo/BAiDgP' \
			b'yqnoapIH2NVuHgiBZTwgVsfggSx7+/EAvAoPZGGN8YBmmTTHN+CBkKuFPNAuk1ZfExu4lRCunhA0E4KeIgRNbqy8SrTAn4gWtNCCFlrQiRZ070m0oIu0oBMtHCCFpogohdu0kCdmixbiF9CCHn2IGfSAGYoOIzMkG2EGPWCG3BcxgxgDM0jEeVBORVfTzKBn' \
			b'MIMEljMDWx2FGbI87ccMOjFDCmuUGTQzgy4xg+RqITN0KzOszHC9zFAzM9RTzEDPPe/hKjMDuyBmqIUZREFUJx1R3X8SM9RFZqgTM9QHMAMrjeK1xQx5YraYIX4xbpjynkfLcfSYoegwMkOyEWaoB8yQ+yJmEGNgBok4D8qp6GqaGeoZzCCB5czAVkdhhpS9' \
			b'PZmhTsyQwhplhpqZoS4xg+RqITOoaqWGlRqulxpYlVVPqbIigQ1TQzNCDeyCqEGUWBkq+R2ooek9iRqKOqw66bBy2HtSQ8PU0BSoIU/MFjXEL6CGZvQhamgG1FB0GKkh2Qg1NANqyH0RNYgxUINEnAflVHQ1TQ0z1FJDYDk1sNVRqCFlb09qSDqpWVij1NAw' \
			b'NTQlapBcLaUGdUa7H05NEEv3PawkcUEkwapHekr1CAlj7SN6CUlo5omcKvgXUYWoIWlRQ9JJDYldxSdRRVENSSc1JH2AGpJmNSRdUEPqJWaLKuIX44Yp73m0VTD12KLoNrJFshG2GCgj9XwRW4gxsIXEnQdFtc2uptlihjJSCCxnC7Y6Cluk7O3JFkkZKQtr' \
			b'lC1YGUmXlJFCrpayBW3RJe1Yhn7gvibEH2B9DWRP+DsCvgS7ERqdQF6AsgBVDE8MDwQLvjsj1hM83/MpfStlrpR5/ZRpeMnNTC25GXpAmSZbcoNZy4spU9wpbvBEmUYW3kxaeBs8kTJNceHNpIU3c8DCm+GFN1NYeOslZkiZ6Ytxw5T3PNoqmHLKLLsNlJnZ' \
			b'MGWawdpbzxf6YTAKZYa486Cciq4mKdPMWHsLgWWUKVbHoMwse/tRpklrb1lYY5RpeO3NlNbeQq6WUubODX8rW6xscS1s0TJbTJ0ChBbLG8pNtqHc8IZykzaUiztii1bYohW2aBNbtL0nsUVbZIs2sUV7AFu0zBaF4z16idlii/hFem72oHGl77YKph5dtIUn' \
			b'0UWyEboY7BbvuSG6EGOgC4m7lwUVXU3TRTuDLiSwnC6kJI9BFyl7e9JFm+gihTVKFy3TRVuiC8nVUrqY2ve30sVKF1dBFx3TRTdFF+wGdNFldNExXXSJLtgd0UUndNEJXXSJLrrek+iiK9JFl+iiO4AuOqaLrkAXeWK26CJ+MW6Y8p5HWwVTjy2KbiNbJBth' \
			b'i27AFrkvYovgRthC4s6Dciq6mmaLbgZbSGA5W7DVUdgiZW9PtugSW6SwRtmiY7boSmwhuVrKFlO7A1e2WNniGtii5o0i9dRGEbRV3itCL2ELgg95MVuIO7BFLZtGatk0UqdNI+wqPpEt6uKmkTptGqkP2DRS86aRurBppJeYIVukL8YNU97zaKMpZ4uy28AW' \
			b'mQ2zRT3YOtLzhX4YjMIWIe48KKeiq0m2qGdsHQmBZWwhVsdgiyx7+7FFnbaOZGGNsUXNW0fq0taRkKulbDG1h3Bli5UtroItFLOFmmILRW7AFipjC8VsoRJbsDtiCyVsoYQtVGIL1XsSW6giW6jEFuoAtlDMFqrAFnlittgifjFumPKeR1sFU48tim4jWyQb' \
			b'YQs1YIvcF7GFGANbSNx5UC55mGYLNYMtQs1kbMFWR2GLFMGebKESW2Q5H2MLxWyhSmwhuVrKFgt3Gq5ssbLFZbIFi7nrKTF3TQ+xRSbmrlnMXScxt7gjthAxdy1i7jqJuev+k9iiKOauk5i7PkDMXbOYuy6IuXuJ2WKL+MW4Ycp7Hm0VTD22KLqNbJFshC0G' \
			b'Yu6eL2ILMQa2kLjzoJyKrqbZYoaYOwSWswVbHYUtUvb2ZIsk5s7CGmULFnPXJTF3yNVStti5+7C5GcJoy5zhVt64Ot4wrFFspjSKfYGg+bJSscmUig0rFZukVCzuSIghSsVGlIpNUipmV/FJQoyiUrFJSsXmAKViw0rFpqBUjKaYUrMlxYhfBukePEiOrYLb' \
			b'QB+dyDJKPpIsI9mILGOgW9zzRbIMMQZZhtRPLx8qupqWZczQLQ6B5bIMtjqKLCNlb09ZRtItzsIalWWwbrEp6RaHXC1kEL1zk+LKICuDXB2D1CwDr6dk4B1p09csBq8zMXjNYvA6icHFHU0+RAxeixi8TmJwdhWfNPkoisHrJAavDxCD1ywGrwti8F5itiYf' \
			b'8Ytxw5TnTyfzD3YbCaTmKUjJR5qCJBuZggyE4T1fNAUJbmQKItWTB+VUdDU9BZkhDA+B5VMQtjrKFCRlb88pSBKGZ2GNTkFYGF6XhOEhV0sJ5JK3MpZuL16XrW6NPJoygdhu1zSEReNmSjSOds2icZOJxg2Lxk0SjYs7moOIaNyIaNwk0Ti7ik+agxRF4yaJ' \
			b'xs0BonHDonHDonECOdwPXucKVXmitqYi8Ytxwxz0PNpo6ilUFd3GSUiykUnIQETe80WTEDGGSYjEnQflVHQ1PQmZISIPgeWTELY6yiQkZW/PSUgSkWdhjW5wtNzeMBHJxOQagcfJiORuKZdM3UV6zlyyCj9um0WWTEFwKadvinjtZA9cGmaIPegl7AGzlhez' \
			b'h7gDe9Bb1/yu+C3swa7iE9mDnG6xB2yFPTjs/diDIqIUbs0/eokZskb6Ytww5T2PtgqmnDXKbgNrZDbMGlxqiTV6vtAPg1FYI8SdB+VUdDXJGuxqN2uEwDLWEKtjsEaWvf1YA16FNbKwxliDSquR+AYzj5CrpWyx7ghf2eIm2IJF5c2UqLyhh9giE5U3LCpv' \
			b'kqhc3BFbiKi8EVF5k0TlTf9JbFEUlTdJVN4cICqX+7ubgqi8l5gttohfjBumvOfRVsHUY4ui28gWyUbYYiAq7/kithBjYAuJOw/Kqehqmi1miMpDYDlbsNVR2CJlb0+2SKLyLKxRtmBReVMSlYdcLWWLdUf4yhY3wRYs3mimxBsNuwFbZLKNhmUbTZJtiDti' \
			b'C5FtNCLbaJJsg13FJ7FFUbbRJNlGc4Bso2HZRlOQbfQSs8UW8Ytxw5T3PNoqmHpsUXQb2SLZCFsMpBo9X8QWwY2whcSdB+VUdDXNFjOkGiGwnC3Y6ihskbK3J1skqUYW1ihbsFSjKUk1Qq6WssW6IXxlizNiC9M+5CGNzBh6ijE0u0GYGWNoZgydGEPc0SGN' \
			b'whhaGEMnxmBX8UmHNBYZQyfG0AcwhmbG0AXG6CVm65DG+MW4Ycp7Hm0VTL1DGotu4yGNyYYZQw8Yo+eLDmkMbpgxQtx5UE5FV9OHNM5gjBBYfkgjWx3lkMaUvT0PaexIkBcPakzhjcoxmDV0iTVCzpayxroxfGWNM2KNB2MMy9JvOyX9Rqtj6bfNpN+Wpd82' \
			b'Sb/FHRjDivTbivTbJuk3u4pPZAxblH7bJP22B0i/LUu/bbXNGL3EDBkjfTFumPKex2TKGaPsNjBGZsOMYQdS754v9MNgFMYIcedBORVdTTKGnSH1DoFljCFWx2CMLHv7MYZNUu8srDG2sCzxtpnEO7JFyNVStlg3hq9scRNswRvD7dTGcDQ53hhus43hljeG' \
			b'27QxXNwRW8jGcCsbw23aGM6u4pPYorgx3KaN4faAjeGWN4bbwsbwXmK22CJ+MW6Y8p5H6ZmDjeFlt5Etko2wxWBjeM8XsYUYA1tI3HlQLnmYZosZG8NDYDlbsNVR2CJFsCdbpI3hWVijbMEbw21pY3jI1VK2WDeGr2xxE2zBulF2SjcKjY11o2ymG2VZN8om' \
			b'3ShxR2whulFWdKNs0o1iV/FJbFHUjbJJN8oeoBtlWTfKFnSjeonZYov4xbhhynsebRVMPbYouo1skWyELQa6UT1fxBahZIUtJO48KKeiq2m2mKEbFQLL2YKtjsIWKXt7skXSjcrCGmUL1o2yJd2okKulbLHwWtoHZYv6+gjDkP77ShyfijjUCHk0QwLx/2uQ' \
			b'CKtM2SmVKUsPkUimMmVZZcomlSlxRyQiKlNWVKZsUpmy/SeRSFFlyiaVqRj8njzCWlO2oDXVS88Wj8Qvxg0T3/Noq2Dq8UjRbeSRZCM8IlpTYhvYJPdLbCLGwCaSgjxAp6KraTaZoTsVAsvZhK2OwiYpe3uySdKdysIaZRPWnYpRDgklhsCc4o3zacVMXWnb' \
			b'BkIxVzTxOOZNtnNmGythHGem4e18GWkI+aa1pjRrTekprSlNbFG8xxYNVDNJ0Fuzc9KU0klTSveepCmlBySBBgXLoCil9yeI+6BXqwvniFDbS/+3taViUo0bpj59g6qUHuhJFR1GPSn6iRYCglDDiwmRFHZCiaLe12QSDPkOYggpx090ADHO0JTS09wQKjXX' \
			b'lGKrIjdwPmaLvZH7RhKyp6qUJnKQxhKLa1RXSrOulC95qmf/sUASIYf9WQd4AMgl/OCL5DFpK1TqMVGi76WP+br1RBhTu8PPlTBOShKBIAI5qIwUhBAiEVwaCZzVUhMrPtkpxSfbjYO+Zf80MxBlJyvKTjYpO7Gr+KSZQVHZySZlJ3uAspNlZSdbUHbangrE' \
			b'pGEq0JUfmgcMVJvKDuMkINnwJCAO+6XYKp0N9VmHybL2kp2lumRnqC6FuPLhPVsdZXifSmf5yL5LI3sOY6fKkmWVJVtSWQo5mrFQRMA8tdV6BeYVmE8GzI4lxm5KYuzUODDjcBeREjuREjuRErskJWZX8YnA7IpSYpekxO4AKbFjKbErSIm3gDklzbfEQWrT' \
			b'N8uB5sBcdhiAObPpA3MothyYHQt/HYt93SyZr5sh8w2BZcAsVscA5qx0FgOzS+JeCWMnMDuW97qSvDfkaC4wT+1qXoF5BebTATMLZ92UcNaZHcBs6DMBswhknQhkXRLIsqv4JGAuCmRdEsi6AwSyjgWyriCQ3QbmmDQAsyk/BMwD8WvZYQTmZDMAZimuHjCz' \
			b'nNWxhNXNEq+6GeLVEFcOzGx1FGBOpbMcmJNkVcLYDcwsWnUl0WrI0VxgntpAfK7AvK59nwGIn5uWDboUgNxOAbndAeSWPhOQWwFyK0BuE5Db3pOA3BaB3CYgtwcAuWUgt9tA3kvMFqjHLwB1W34I1O0A1IsOI6gnGwH1fKm75wVdjUtTIF6izANxKrqehns7' \
			b'A+7FWQ73bHUUuE9522+JG8aA+SmsUci3DPm2BPmSq4XaNGZqN/AK/Sv0Xw70O4Z+NwX9bgf0O/pM0O8E+p1Av0vQ73pPgn5XhH6XoN8dAP2Ood8VoD9PzBb0xy/GDVOevlmOoAf9RYcR+pNNCfpzLwT9LoN+iTIPxKnoehr63Qzol8By6Gero0B/ytue0O8S' \
			b'9KewRqHfMfS7EvRLrpZC/9SW3hX6V+i/HOhvGfrbKehvd0A/PQz9rUB/K9DfJuhve0+C/rYI/W2C/vYA6G8Z+tsC9OeJ2YL++MW4YcrTN8sR9KC/6DBCf7IpQX/ugKC/zaBfouylWkXX09DfzoB+CSyHfim8Y0B/ytue0N8m6E9hjUJ/y9DflqBfcrUU+qf2' \
			b'567Qv0L/5UA/67q4KV0Xt0PXxbF/gn7RdXGi6+KSrgu7ik+C/qKui0u6Lu4AXRfHui6uoOvSS8wW9McvgP6u/BD0D/Reyg4j9CebEvTnXgj6uwz6Jco8EKei62non6EREwLLoZ+tjgL9KW97Qn9Si8nCGoV+1opxJa2YkKul0E+bbetNM3Ez2tUzQH2ke9Ae' \
			b'kAl81uezQX15jIADxx7u6Dd0I8hOWeEGnWPiUrRmo3dMDig82SilZXagZXag0+xAt70nnf1WnB3oNDvQB8wOghK8LkwPeqnZOvwN8SPhLBYYJD75w9lvPEFQrTAFEFHpEffx/LdkUyCLnhc6/C2bJ4SYe8lX0XVOFsD68ulvhbkCDhzcOgFOAs1PgJPSPAJp' \
			b'IJxGErPnEXAtdYB4BBynbfcZcDxr0KVZQ8hbog6ywV9L5rahv5bsPYdo1nzXLTFIt3m9iz+2maMjwjBCFcINGTEIK8ymhFHdHEJ/QvlsjB/Re6BR09OkaQWFZ6Dv1Di8h7aHoqxZjqwRUXchabeNoBE50YVmo+YoXhJQEkoSRAZ8jIBYQMMAhQfj4LSKS0C8' \
			b'++HpZBG6hkoqffUU4NL9lrrgKBBNDlt72HMU1AHk7AE1AWN2owugZRtXAqJ4kPC52QkSxRHmJ8OJMFD0rejW0QKjmSJizEWLZYMsGkJdKGRkAyVU6wodw1EKFWcRPhZBh1o6vnCngI7hvBIYYh4OR3w6lMPqoPfjm9bZ48rBo5CFuDKKKWHOdhG4QqnN/wvG' \
			b'KArhQXGGmMB/0Vg3MjPk62eDO2XM0XYJ7mz+5VvnY58TzHB8hSyf4VQTCJRWv44IQgF4mgQ8Pi2XP4hxBwDOcBEpBxzvt2n7wIMFBp9nBiDeO84LSrD37toqO4AHc2eAVHNEgCJwYgBaBFD1yUAqgpJNoIT6vKoBkK4PAyPUz+ggCEuY98oOUElTVAgADU5W' \
			b'NGXFBklHUal05wt+kAfkoGlp7GQOW5vx5VBcun845BLUgtRB1+PIhWX1i0EvIFe1cBrWzJyGVZ9gyDQyXKpzRCJAOpth03AqhvpE3Y0jEiX98lAJiIQGsnhqpmdOzdCydk/P6mMv/z7oyOiaRkVLl3bsp13aOeqyzslHN9nIprmukc1eSztmJn7sxo7mbEVH' \
			b'owMTnz4kEMfK4lxZdQogGcrwTwEm3uzzqiHKrvXM6VZbBpitadXRp1MXsdazNWhBB29JReOejzqr25Mhjz0f8LnHrApRUKxzp1jb06tM/k2p7U2kePpkN6/PA5tG1ZyOKuI+i1FNe4rF5QQybXvZGMPaZk40yepPJeo+pwENSOhEou7Nv7rHnqZo1didC3hM' \
			b'AwaSdeho5izAYylwDEcve02LrnqEMr6kUpHm6OGjknOCjj1gQwphFD8WTYja/TEDx9Z+atiwx5kI7bvFZUuR+RQTofq8YQQ3c5w/ltCYG4EeZZ4zgiiNWQoraLmnXWehFA0nOgcATHcAwHSfHmAycNHVCccmJwKXFVgO1N7tgwrq8ORDlVNjylHxxJfs/pOc' \
			b'6rR4olY8WfHkQDxxK54cF0/UAXiiTosnesWTFU8OxJMzWEq5LjzRl7MIe1MLr2cIGOeOFUcCBk3pvagl1kOBYPMv3zEeAxEhmPHpWDHhUjBhTynupeICdafjwAL3zGuWvBxHYOvqx4TGCht+fOcjiKhXiFgh4vQQQR3lfIYOtwsS1j72cE3Q0KzQsELDA0ED' \
			b'wcBFzipuFxoa99gjOkHD2aiLrtBwhdBgV2i4XGi4IGXQFRoK0ODN2GpJOyLPAiaoP5/bsiR7PwOUoIR8CpCgiCZBAidJ3Ptg9U64wKm8vLu9egy89a3/McGdb6Legs4iaQ7QEF2B5AyA5EzAoz1H8GjPBTzaTwUeh44wZkHGATqfK2TcOGRQ27tGMegxIIMK' \
			b'59ImJbV9TDzg2zlEonQLgD1EjXOFiFuECGpU160psQAiqDSuZt2ihrJEjbZPowmSe9hDNDNXiLgliCD3N6JNNQMjqDiub3HT4E4hdBDcNESLnHZVtlwhYidEkNsb07e8XfGHwTCiqgkaVp3LFRoUXbd2biqXp4YGSteNIYMmVUv0GShfVpYgYtW5vFGIQFM+' \
			b'F43Lc0SImxw8KCCD4sHDqnJ5q8igVmRYkWEHMlyQxiWlT04P/pQoUbz195QnBq9bP5diBurx3vtsT4Ie/mXPCEMAI2NIsmRruD0blcz9D/eFXvDw1vGLGGnscUN4xA07MeKwN4QhqvB/H9UrgiNYZNdxX9yAZM/btAOWUCHsHJlABXhqdNJCEYvFIWejqrkC' \
			b'zAowewOM2fq/F8CYFWCoECYAplkCMGej2LkCzFEB5nbApd76vxe41Cu4UCEctK6SgMVH8RqAwmjCUMI4wiDSEHw0AA6gBkNGjhcEFqHbm7x7GumWbbE7clccdL1hF6FuUfuugKJPzT60+NjYY0NHG+X2XXOrpgYdG3OpIadGHFseGltsGgiWmoQaaQl0e9FW' \
			b'nW9VS0s1TPNR3zqPUOiMuxFxWy5+6wZV0CyvhrpQFUCrWB3ULx+6PpAVQoZYL1rqRutB/cRuu6yOuA8Vuk9eV/oodaXGqsteV5VlgL5VbQGLP1nVQRPFl4GylH86vbKhD5A/d34Q4+1J+bVWZN3k1hilaLK2m9faqu/xt/v+kX/f3fsOXMEVvt/7FuIHQihk' \
			b'lABdJ3VvYKdwj68nc7oi3NHNun7Q5OFSb3ydelboGrrfVtfOe/Y2GDVBTaDmi73D1bhoan7s43/hEgowAPb/oCXy5VX39fLY/NfxfxRog0DdaLByb143En6D4WAz+JfuwdO5PUVnC9HViNE3HZxHX9Gpr5Ox820SYSEch6Vih1QjqfIj2vgPwwDLB7pm/23x' \
			b'H381tKwNMx2F6nu6paS7PZNeLUx9u5n+h2HyyDdKa7tPWtux5A5uoCom3+gsCz6YiX8Y7/dteORtZYSdf8W42v+jjHWFjOnRvHmMxNym689ntjOs+nnGQU1VR3q+GFFhiEUHimne0wg0BEYBonCsaSqjStbsLJeXRz9cUsflZsbLDpeQ0hykzstR4N7RZeJy' \
			b'W/j3TFPDp9226n0b+z8d0i7f4yEObAbG3Wkcj5oagP900qZNEr9P9nCW1dJG78cFfljwIE3fp8oPIk7cBfRm2UOprhd62vmEIdkRg9x6uPL12SGeGqly89DVbjYnf7BONLTC4O0IYXN1mxPDW735hA9nuY5ZxvH73QO2c8ytLqOpQ88DT8erre3DPepBQ9/9' \
			b'cP2XpiDzm7w6QqvH0HPfB6vVy71xzu2w5SNRn6L9qwvoA1iAyR5OtN4MrI/+YHHmoeMYebhRlOaZ4w1hHrfv1yvsZvBgOX3bduYDUc48p1wO7do5xjsHFiVv6OEWsWzy/4A9A1LXEzy8Dlmt/WJHv2g2t/Rwi1i2PjB/Nrhf37Cb4z4Q+c9zyqWh1/4x3j8g' \
			b'xrqhh1tEaU59jP5Bc9h9+gg0dY79QCNmnlMulK1Z99pNsm7SbG7p4RZRmocfq5ugpvfrKnbzEA/0xOY55bJZZ+q7eovb3NLDLWLZNN3uuwo/t9P0KwqV0m7mP9CAW+QB+pUTLpBx+cEltk7od/QhqBXd0MMtYtmEfu8+lFf23v0JutQP+eTayrN9sRbSQSsC' \
			b'+wmK9+5bGAfUn7CPKelnTehrvlCgxAUdvn0fSMAP8T/5aPQI1R491DZ7sYkbkFqReQcy280tPdwilmkdnBiZ3ebMHi5Ds/aqHb2q3dzSwy2iXqzLc0zlnf06WKHusH1s9gNV8kUeBk/YqbXAB/ZaYZ+V7LGiol+2uHG+Rd9sLuHhMi8pe19imdvNJTxc5suW' \
			b'JY5d5sYtKHc9p+zd5hM/oLC9XXAdlLTvZ5D9CauhwNrbVdFuFj3YDbTUz37Pjpi4QvbcNXDmFYIN2xf28D6mkgr/FVSH3lzaw9WxeHvB1e2pwaEHyx8+1yD93y+UYYjbYWc/e27mhkUPV/X5bSb45FXdbK7x4epdpuhwjdWLw0qu8OHqXb58cHXVqzbX+HD1' \
			b'Ll+iuLrq1ZtrfLh6l6+GXF31ms01Ply9bvPa1LRBWNC6jRbSvztYoAjJEjtZeE+7L/vXeQPwBU0uUG2+qLHHCKIDIwc2qLJrX2n9/+xab7lG5ZEPX/WD/5qPyMARRumMDENNge09A+XtkZpQr+mEZoNDFPiEDdimc7/4jK1wvlaTztXCmVqNlEfTjwWnptBh' \
			b'w5RRijJEhZYpS3gidfGfXqN1+5ZJG7vomC7+4uC7Zpkw5MF8mIfC2Sk+8hb/eRyFO7l1Y2kLjPjt0ukgvKaAGzZ9KLBxYqOSDU4QefT/AfV45y4=' 

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

		('LIM',          fr'(?:\\lim)_'),
		('SUM',          fr'(?:\\sum(?:\s*\\limits)?|{_USUM})_'),
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

		('WSUB1',        fr'(?<=\w)_{_VARTEX1}'),
		('WSUB',          r'(?<=\w)_'),
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

		('LIM',          fr'\\lim_'),
		('SUM',          fr'(?:\\sum(?:\s*\\limits)?|{_USUM})_'),
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

	def expr_div_1         (self, expr_div, DIVIDE, expr_divm):                        return _expr_diff (AST ('/', expr_div, expr_divm))
	def expr_div_2         (self, expr_mul_imp):                                       return expr_mul_imp
	def expr_divm_1        (self, MINUS, expr_divm):                                   return _expr_neg (expr_divm)
	def expr_divm_2        (self, expr_mul_imp):                                       return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                            return _expr_mul_imp (expr_mul_imp, expr_intg)
	def expr_mul_imp_2     (self, expr_intg):                                          return expr_intg

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add):               return _expr_intg (expr_add, (expr_sub, expr_super))
	def expr_intg_2        (self, INTG, expr_add):                                     return _expr_intg (expr_add)
	def expr_intg_3        (self, expr_lim):                                           return expr_lim

	def expr_lim_1         (self, LIM, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                          return AST ('-lim', expr_neg, expr_var, expr)
	def expr_lim_2         (self, LIM, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):  return AST ('-lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3         (self, LIM, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg): return AST ('-lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                   return expr_sum

	def expr_sum_1         (self, SUM, CURLYL, varass, CURLYR, expr_super, expr_neg):                          return AST ('-sum', expr_neg, varass [0], varass [1], expr_super)
	def expr_sum_2         (self, expr_diffp):                                                                 return expr_diffp

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

	def expr_sub_1         (self, WSUB, expr_frac):                                    return expr_frac
	def expr_sub_2         (self, WSUB1):                                              return _ast_from_tok_digit_or_var (WSUB1)

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
		'WSUB1'           : 'SUB',
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

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: # DEBUG!
# 	p = Parser ()

# 	# p.set_quick (True)
# 	# print (p.tokenize (r"""{\partial x : Sum (\left|\left|dz\right|\right|, (x, lambda x, y, z: 1e100 : \partial !, {\emptyset&&0&&None} / {-1.0 : a,"str" : False,1e100 : True})),.1 : \sqrt[\partial ' if \frac1xyzd]Sum (\fracpartialx1, (x, xyzd / "str", Sum (-1, (x, partialx, \partial ))))}'''"""))

# 	# p.set_sp_user_funcs ({'N'})

# 	a = p.parse (r"b = dx [?h(x, y)]^lambda x, y, z: True!")
# 	print (a)

# 	# a = sym.ast2spt (a)
# 	# print (a)
