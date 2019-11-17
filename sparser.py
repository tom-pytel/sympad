# Builds expression tree from text, nodes are nested AST tuples.

import ast as py_ast
from collections import OrderedDict
import os
import re
import sys

from lalr1 import Incomplete, PopConfs, Reduce, Token, State, LALR1 # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

_SP_USER_FUNCS = set () # set of user funcs present {name, ...} - including hidden N and gamma and the like
_SP_USER_VARS  = {} # flattened user vars {name: ast, ...}

def _raise (exc):
	raise exc

def _FUNC_name (FUNC):
	return AST.Func.TEX2PY_TRIGHINV.get (FUNC.grp [1], FUNC.grp [1]) if FUNC.grp [1] else \
			(FUNC.grp [0] or FUNC.grp [2] or FUNC.grp [3] or FUNC.text).replace ('\\', '')

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
		ast2, wrap2 = ast.base, lambda a: AST ('^', a, ast.exp, is_pypow = ast.is_pypow)
	elif ast.is_attr:
		ast2, wrap2 = ast.obj, lambda a: AST ('.', a, *ast [2:])
	elif ast.is_idx:
		ast2, wrap2 = ast.obj, lambda a: AST ('-idx', a, ast.idx)

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
def _expr_ass_lvals (ast, allow_lexprs = False): # process assignment lvalues
	def can_be_ufunc (ast):
		return (
			(ast.is_func and ast.func in _SP_USER_FUNCS and all (a.is_var_nonconst for a in ast.args)) or
			(ast.is_mul and ast.mul.len == 2 and ast.mul [1].is_paren and ast.mul [0].is_var_nonconst and not ast.mul [0].is_diff_or_part and ast.mul [1].paren.as_ufunc_argskw))

	def as_ufunc (ast):
		if ast.is_func:
			return AST ('-ufunc', ast.func, ast.args)
		else: # is_mul
			return AST ('-ufunc', ast.mul [0].var, *ast.mul [1].paren.as_ufunc_argskw)

	if ast.is_ass: # if assigning to function call then is assignment to function instead, rewrite
		if can_be_ufunc (ast.lhs):
			ast = AST ('=', as_ufunc (ast.lhs), ast.rhs)

	elif ast.is_comma: # tuple assignment? ('x, y = y, x' comes from parsing as ('x', 'y = y', 'x')) so rewrite
		vars = []
		itr  = iter (ast.comma)

		for c in itr:
			if c.op in {'@', '-ufunc'}:
				vars.append (c)
			elif can_be_ufunc (c):
				vars.append (as_ufunc (c))

			elif c.is_ass:
				t = (c.rhs,) + tuple (itr)
				v = c.lhs if c.lhs.op in {'@', '-ufunc'} else as_ufunc (c.lhs) if can_be_ufunc (c.lhs) else c.lhs if allow_lexprs else None

				if v:
					ast = AST ('=', (',', tuple (vars) + (v,)) if len (vars) else v, t [0] if len (t) == 1 else AST (',', t))

					vars.append (c.lhs)

				break

			elif allow_lexprs:
				vars.append (c)
			else:
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
	if args.is_var_nonconst:
		return AST ('-lamb', lamb, (args.var,))
	elif args.is_comma and all (v.is_var_nonconst for v in args.comma):
		return AST ('-lamb', lamb, tuple (v.var for v in args.comma))

	raise SyntaxError ('mapsto parameters can only be variables')

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

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('-diff', expr, 'd', ('x', 1))
	def interpret_divide (ast):
		numer = ast.numer.strip_curly
		d     = e = None
		p     = 1

		if numer.is_var:
			if numer.is_diff_or_part_solo:
				d = numer.var

			elif numer.is_diff_or_part:
				d = numer.diff_or_part_type
				e = numer.as_var

		elif numer.is_pow:
			if numer.base.is_diff_or_part_solo and numer.exp.strip_curly.is_num_pos_int:
				d = numer.base.var
				p = numer.exp.strip_curly.as_int

		elif numer.is_mul and numer.mul.len == 2 and numer.mul [1].is_var and numer.mul [0].is_pow and numer.mul [0].base.is_diff_or_part_solo and numer.mul [0].exp.strip_curly.is_num_pos_int:
			d = numer.mul [0].base.var
			p = numer.mul [0].exp.strip_curly.as_int
			e = numer.mul [1]

		if d is None:
			return None, None

		ast_dv_check = (lambda n: n.is_differential) if d == 'd' else (lambda n: n.is_partial)

		denom = ast.denom.strip_curly
		ns    = denom.mul if denom.is_mul else (denom,)
		ds    = []
		cp    = p

		for i in range (len (ns)):
			n = ns [i]

			if ast_dv_check (n):
				dec = 1
				ds.append ((n.var_name, 1))

			elif n.is_pow and ast_dv_check (n.base) and n.exp.strip_curly.is_num_pos_int:
				dec = n.exp.strip_curly.as_int
				ds.append ((n.base.var_name, dec))

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
						return AST ('-diff', e, d, tuple (ds), src = AST ('/', ast.numer, ('*', ns [:i + 1]) if i else ns [0])), ns [i + 1:]
					elif i == len (ns) - 2:
						return AST ('-diff', ns [-1], d, tuple (ds), src = ast), None
					elif not ns [i + 1].is_paren:
						return AST ('-diff', AST ('*', ns [i + 1:]), d, tuple (ds), src = ast), None
					else:
						return AST ('-diff', ns [i + 1], d, tuple (ds), src = AST ('/', ast.numer, ('*', ns [:i + 2]) if i < len (ns) - 3 else ns [i + 2])), ns [i + 2:]

		return None, None # raise SyntaxError?

	def try_apply_ics (ast, arg): # {d/dx u (x, t)} * (0, t) -> \. d/dx u (x, t) |_{x = 0}, {d/dx u (x, t)} * (0, 0) -> \. d/dx u (x, 0) |_{x = 0}
		diff  = ast.diff._strip_paren (1)
		ufunc = _SP_USER_VARS.get (diff.var, diff)

		if arg.is_paren and ufunc.is_ufunc_applied and ufunc.can_apply_argskw (arg.paren.as_ufunc_argskw):
			diff = AST ('-diff', diff, ast.d, ast.dvs)

			return AST ('-subs', diff, tuple (filter (lambda va: va [1] != va [0], zip (ufunc.vars, arg.paren.comma if arg.paren.is_comma else (arg.paren,)))))

		return AST ('*', (ast, arg))

	# start here
	if ast.is_div: # this part handles d/dx y and dy/dx
		diff, tail = interpret_divide (ast)

		if diff and diff.diff:
			if not tail:
				return diff
			elif len (tail) == 1:
				return try_apply_ics (diff, tail [0])
			else:
				return AST.flatcat ('*', try_apply_ics (diff, tail [0]), AST ('*', tail [1:])) # only reanalyzes first element of tail for diff of ufunc ics

	elif ast.is_mul: # this part needed to handle \frac{d}{dx}
		mul = []
		end = ast.mul.len

		for i in range (end - 2, -1, -1):
			if ast.mul [i].is_div:
				diff, tail = interpret_divide (ast.mul [i])

				if diff:
					if diff.diff:
						if i < end - 1:
							mul [0:0] = ast.mul [i + 1 : end]

						if tail:
							mul [0:0] = tail

						mul.insert (0, diff)

					if i == end - 2:
						mul.insert (0, AST ('-diff', ast.mul [i + 1], diff.d, diff.dvs, src = AST ('*', ast.mul [i : end])))
					elif not ast.mul [i + 1].is_paren:
						mul.insert (0, AST ('-diff', AST ('*', ast.mul [i + 1 : end]), diff.d, diff.dvs, src = AST ('*', ast.mul [i : end])))

					else:
						diff = AST ('-diff', ast.mul [i + 1], diff.d, diff.dvs, src = AST ('*', ast.mul [i : i + 2]))
						expr = try_apply_ics (diff, ast.mul [i + 2]) # only reanalyzes first element of tail for diff of ufunc ics

						if expr.is_mul:
							mul [0:0] = ast.mul [i + 2 : end]
							mul.insert (0, diff)

						else:
							mul [0:0] = ast.mul [i + 3 : end]
							mul.insert (0, expr)

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
		if ast.src:
			ast2, neg = ast.src._strip_minus (retneg = True)
			ast2, dv  = _ast_strip_tail_differential (ast2)

			if dv and ast2:
				return neg (_expr_diff (ast2)), dv

	elif ast.is_func:
		if ast.src and ast.func in _SP_USER_FUNCS: # _SP_USER_VARS.get (ast.func, AST.Null).is_lamb:
			ast2, neg = ast.src._strip_minus (retneg = True)
			ast2, dv  = _ast_strip_tail_differential (ast2)

			if dv and ast2:
				return neg (ast2), dv

	elif ast.is_pow:
		ast2, neg = ast.exp._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('^', ast.base, neg (ast2), is_pypow = ast.is_pypow), dv

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

def _expr_diffp_ics (lhs, commas): # f (x)' * (0) -> \. f (x) |_{x = 0}
	if lhs.is_diffp:
		diffp = _SP_USER_VARS.get (lhs.diffp.var, lhs.diffp)

		if diffp.is_ufunc_applied and diffp.can_apply_argskw (commas.as_ufunc_argskw): # more general than necessary since diffp only valid for ufuncs of one variable
			return AST ('-subs', lhs, tuple (filter (lambda va: va [1] != va [0], zip (diffp.vars, (commas.comma if commas.is_comma else (commas,))))))

	return Reduce # raise SyntaxError ('cannot apply initial conditions to derivative of undefined function')

def _expr_func (iparm, *args, strip = 1): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	ast, wrapf = _ast_func_reorder (args [iparm])
	isfunc     = args [0] == '-func'
	ast2       = AST (*(args [:iparm] + ((_ast_func_tuple_args (ast) if isfunc else ast._strip (strip)),) + args [iparm + 1:]))

	if isfunc:
		ast2.src = AST ('*', (('@', args [1]), args [iparm]))

		if ast2.args.len != 1 and ast2.func in {AST.Func.NOREMAP, AST.Func.NOEVAL}:
			raise SyntaxError (f'no-{"remap" if ast2.func == AST.Func.NOREMAP else "eval"} pseudo-function takes a single argument')

	elif args [0] in {'-sqrt', '-log'}:
		ast2.src = AST ('*', (AST.VarNull, args [iparm])) # VarNull is placeholder

	return wrapf (ast2)

def _expr_func_func (FUNC, args, expr_super = None):
	func = _FUNC_name (FUNC) if isinstance (FUNC, Token) else FUNC

	if expr_super is None:
		return _expr_func (2, '-func', func, args)
	elif expr_super.strip_curly != AST.NegOne or not AST ('-func', func, ()).is_trigh_func_noninv:
		return AST ('^', _expr_func_func (FUNC, args), expr_super, is_pypow = expr_super.is_pypow)
	else:
		return _expr_func_func (f'a{func}', args)

def _expr_ufunc_ics (lhs, commas): # ufunc ('f', ()) * (x) -> ufunc ('f', (x,)), ufunc ('f', (x,)) * (0) -> ufunc ('f', (0,)), ...
	if lhs.is_ufunc:
		if lhs.is_from_Function:
			return AST ('-ufunc', lhs.ufunc, (commas.comma if commas.is_comma else (commas,)), lhs.kw)

		else:
			ast = lhs.apply_argskw (commas.as_ufunc_argskw)

			if ast:
				return ast

	return Reduce # raise SyntaxError ('cannot apply initial conditions to undefined function')

def _expr_ufunc (args, py = False, name = ''):
	args, kw = AST.args2kwargs (args.comma if args.is_comma else (args,))

	if py:
		if len (args) != 1 or not args [0].is_str:
			raise SyntaxError ('Function() takes a single string name argument')

		name = args [0].str_
		args = ()

	if AST ('@', name).is_var_const:
		raise SyntaxError ('cannot use constant as undefined function name')

	return AST ('-ufunc', name, tuple (args), tuple (sorted (kw.items ())), is_from_Function = py)

def _expr_varfunc (var, rhs): # user_func *imp* (...) -> user_func (...)
	arg, wrapa = _ast_func_reorder (rhs)

	if var.var in _SP_USER_FUNCS: # or arg.strip_paren.is_comma:
		if arg.is_paren:
			return wrapa (AST ('-func', var.var, _ast_func_tuple_args (arg), src = AST ('*', (var, arg))))
		elif var.var not in {'beta', 'Lambda'}: # special case beta and Lambda reject if they don't have two parenthesized args
			return wrapa (AST ('-func', var.var, (arg,), src = AST ('*', (var, arg))))

	elif arg.is_paren and var.is_var_nonconst and not var.is_diff_or_part and arg.paren.as_ufunc_argskw: # f (vars[, kws]) -> ('-ufunc', 'f', (vars)[, kws]) ... implicit undefined function
		ufunc = _SP_USER_VARS.get (var.var, AST.Null)

		if ufunc.op is None:
			return wrapa (AST ('-ufunc', var.var, *arg.paren.as_ufunc_argskw))

		elif ufunc.is_ufunc:
			if ufunc.is_ufunc_unapplied:
				ast = ufunc.apply_argskw (arg.paren.as_ufunc_argskw)

				if ast:
					return wrapa (ast)

			elif ufunc.can_apply_argskw (arg.paren.as_ufunc_argskw):
				return wrapa (AST ('-subs', var, tuple (filter (lambda va: va [1] != va [0], zip (ufunc.vars, arg.paren.comma if arg.paren.is_comma else (arg.paren,))))))

	return Reduce # raise SyntaxError ('invalid undefined function')

def _expr_sym (args, py = False, name = ''):
	args, kw = AST.args2kwargs (args.comma if args.is_comma else (args,))

	if py:
		if len (args) != 1 or not args [0].is_str:
			raise SyntaxError ('Symbol() takes a single string name argument')

		name = args [0].str_

	elif args:
		raise SyntaxError ('$ does not take direct arguments, only keyword assumptions')

	if AST ('@', name).is_var_const:
		raise SyntaxError ('cannot use constant as symbol name')

	return AST ('-sym', name, tuple (sorted (kw.items ())))

def _expr_subs (expr, subs):
	def asslist2srcdst (asslist):
		subs = []

		for ast in asslist:
			if ast.is_ass:
				subs.append (_expr_ass_lvals (ast, True) [1:])
			else:
				raise SyntaxError ('expecting assignment')

		return tuple (subs)

	# start here
	if not isinstance (subs, AST):
		subs = asslist2srcdst (subs)

	elif subs.is_ass:
		subs = (_expr_ass_lvals (subs, True) [1:],)

	elif subs.is_comma:
		if subs.comma [0].is_ass:
			subs = asslist2srcdst (subs.comma)

		else:
			subs = _expr_ass_lvals (subs, True)

			if subs.is_ass and subs.lhs.is_comma and subs.rhs.is_comma and subs.rhs.comma.len == subs.lhs.comma.len:
				subs = tuple (zip (subs.lhs.comma, subs.rhs.comma))
			else:
				raise SyntaxError ('invalid tuple assignment')

	else:
		raise SyntaxError ('expecting assignment')

	if expr.strip_curly.is_subs: # collapse multiple subs into one
		return AST ('-subs', expr.strip_curly.expr, expr.strip_curly.subs + subs)

	return AST ('-subs', expr, subs)

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
			raise Incomplete (AST ('-mat', tuple (c.brack for c in e [:-1]) + (e [-1].brack + (AST.VarNull,) * (e [0].brack.len - e [-1].brack.len),)))

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

def _expr_var (VAR):
	if VAR.grp [0]:
		var = 'partial' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_'))
	elif VAR.grp [1]:
		var = 'd' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_'))
	else:
		var = AST.Var.ANY2PY.get (VAR.grp [3].replace (' ', ''), VAR.grp [3].replace ('\\_', '_'))

	return AST ('@', f'{var}{VAR.grp [4]}' if VAR.grp [4] else var, text = VAR.text) # include original 'text' for check to prevent \lambda from creating lambda functions

def _expr_num (NUM):
	num = NUM.grp [1] or (NUM.grp [0] if NUM.text [0] != '.' else f'0{NUM.grp [0]}')

	if not NUM.grp [2]:
		return AST ('#', num)

	g2  = NUM.grp [2].replace ('{', '').replace ('}', '')

	if g2 [1] in {'-', '+'}:
		return AST ('#', f'{num}{g2.lower ()}')
	else:
		return AST ('#', f'{num}{g2 [0].lower ()}+{g2 [1:]}')

#...............................................................................................
class Parser (LALR1):
	def __init__ (self):
		self.TOKENS_LONG.update ([(v, self.TOKENS [v]) for v in self.TOKENS_QUICK])

		LALR1.__init__ (self)

	def set_quick (self, state = True):
		self.TOKENS.update (self.TOKENS_QUICK if state else self.TOKENS_LONG)
		self.set_tokens (self.TOKENS)

	_PARSER_TABLES = \
			b'eJztnXmv5DaS4L/MAl0PyAQk3nr/2eXqHmN8jY/eaRQMo2zXDIz1BZft7UFjv/vGxUNK3e/KzEeUXqUkUhQZQcZPJEPUi9d/+eLlpx99+slfDn/5X29//h5+4uFHr/76Jfx89t7nrz75CHbe//y9l/+OO1/99atPXn72j7gHv598ijH//t7n8P8X//iYwuBX' \
			b'EvmAQr/46L0v/o1333/1t29evvfFqy9k/+P34tn38+7f8+5nvEsppFz8FXbkp5VfBb8ff/jJV5Tuh598+nH8beOOism8/Orzj/6ByaSdL76k3H/1fozCu68+/uzLf3zxCu//4Sdf/g0L+xUV7MOPKTr9/x+fY/hHJLVPMY7I5X2SyMtPP/74vSjJz6Mkcefz' \
			b'D//2b1/GTHzeyxsevfoP+O+9jz+D/z94/yMKw7OffCASw7338+7f865I7NVHX7zCG3/+4cf4++o/X2JJ3/uSiopJfskZhIx9GX9RVh98+PcPP8ArXoruON5nH5FoQRpRyv/5xauXFOGDD//6V6wQn3xIdeclZfq9Tz5AsWHAp3j9x+999sWXn0oWYwWgE/+b' \
			b'hY0/LWsBbvny32H33R/fvvvzzW/v/iz238H+d29+e/v7N7/89s333/747vc3vxXBsPv2n79CyA9//hT3f37739+8+e2/4+G7P359+1s++BZ2f3rz+zff/fKj7P32y//Ne3y/d2/fvfsu7f2a9mIyb75Nuz98/8909vff043+6813v8f9X+kGfPqPn7/Lef6v' \
			b'//q1d/DND9+9yzlNBfrxh1y2fPb3t7+l/Z/++PGbH35KiX33x28//k8hmrj77Q8//1KKKeXqtzfflUnBTjz8820KefP99ynSm1S4f757m0tKUkolwDIVgk8Bf/z8wy8/p4D/STn64effU5a+y6UBPZdi+/NNEvLPv6Q7/1FGefPz973zpVy//e6Xn356kw5/' \
			b'SYl9C0L4P2+z0vrxfv3h7Xdv0wFUyJ+zLH599/sv6dapkqSS/PJjLi0l2jt4V1z5zY9/vvkxy4+v/Prw+sXRqYPtbg604xrcsS3+B6ebGzmEI9rTGO1gusPR3fRO8JGK18EFOp7CXYp19HSmObzQBwNpwv8Wdm7iWTmXThwpV7rh/5yFUHVTnlL65JRz5Snc' \
			b'hb3W8X8ebtCGGzmFu7Dn4S8cTDgcOcTjDvxCxinfEAL/6YOFGC3nLZ+Kh0dDeW0Nls3GopmbeJJP8bG2hxfKwAmPf/mULQ+Vkx08h4lAdlqT9izlELIOiaN+vL2RM0dFOVEt/+dBCIrvC0e4i7IldaBmborDuF+cZ6WjsrGY9GdSMN6ZMinnOesgCjnJxx4l' \
			b'gvlikfh0Vs6dnHD5ROifOGoqmjH8n+UA2DsayojRchjVhJnh3Dj+D2r40XGl1lhRSNEOqg7WJAlwTQwwXtTMeYRDUDVdCzdSGA3Vw8KgU215qJTs4Dm8HESLhbDcVtJhGJ6SutI/HU4PB6e608ORGP0MmOb0sHfR0bgiZ7mRSCYGJ7rBCUivONGJSloTj6GR' \
			b'U8UEs4FysiIOzYpIp09P5cMjmAtMDKo7thpso93Bg27BKKGG5V4jwWTu7JpYSg9iHQ3pFq0AxDOxQeB1XKCOzUALArRQUdvCGmBYOp/POD6j8hnPZ3Q+E/hMSueoqexa8X9OpzymU6Y8hbu4F/g/EN/NTd7FPcMtIV6CV5P+Ldw+1ws8wmj5EPRKpilQtGhi' \
			b'MV3WTnPgW7ea//NYDbj5trxLosSGKztst1tCRbQdLAo8yafkuJE0sW0frI31rXc+noETlCEndTFacBC/YTtLf2g0+RLcQWk7/s9hmfgaOMJdFADYCY/mSZDnD54JAk0ArbVw7oDEgutdG20aRdAMvdFQMOiUPaz2LlZMI2ZRWobUShWVACdf2GwM8JBMmo6H' \
			b'joQMCnxBApFKiIctpX9yKh1ClqheYJwu7plG9lQ8peMZqZ+ww+oEObmUHh753g3jmXR0VJRSa+UwhoBgWhKMMvyfg0SUSM3QLkbrDozChg9ifUfLrUhUGrSNARnNLQkKIwX+z/lsbdgOoRAd/1c8BzmBpLX8Hz0CSZilXdwzMfBGDuEoBjB8IEe+44qQ0Oda' \
			b'eRRx9LRl4vXY4B21K2diAD5kyRnYg+e7182hBdW1IBfgE2DFkM2D+gL1H2w6tH602w1Wwe4A0gDxdLCrDi08W7Qg6xYacgsBLYS0YKhaUAUISmMM/APU4fMKWLsW/uCMP+AVgMvW4C9cCflqG/iFCtdajAkp2IPGPUgfctFCNlrIR2swBmQXJNKCiWuhVbRw' \
			b'sxZu0cI9wPiDVWqhQrcglU4fOnPo7KFzh84fOkzjgLmGyJg2HENL6CCZBjPQIv9BaCAbMPxtAxEbi88mIG6F1RYeKQD28EyCbQzyDdnGMjVQpgYThn2QW2twHy4GSbYgyqAPwRyCPQSUTXsI/hDCIcCNMe8QHzKNdhv0Do/GGh9RoVaBJYFaC49n8FAKJgos' \
			b'IoDEW8SORwNygGoQUHdYeHwwh3YLzxQII1BlgNtgruCGEIyP8bB7g+YG8gZqf4H6xhN4+Q0EGz7ELOOP4lhYEgxFDdwQ0Sm0pdDXCHQ6prRrXbmSuvKiY6W3rF3UFGm7a6UKcd1AreJha+TXymVtkBOdxJeqJxdiDMcpc2XrNNcirmNtk2LRiWqRrrSWaa5O' \
			b'WsVqw9WAtI76V66q/3rVDwq3Yk8s1QBR1NfUj+EawRYhBeAZMS2GTAvpogi1TkIp4bKUj1/CojKWFXBQ8YZVTqraaCUrKhdXqpHKJBWorDVlbRnWk4n6AXUC1WAb0UPD0pb2ENtBrPNcz2MNL+tzUY9j3eX6GitoVdGdVIRGk9mqrTzVNWJErZcHN2kSNj72' \
			b'2UhpfdK45Omu1aeN60VrYmWwgntlI6dVVw31VRvqtur3evX7ouWu3+sXbO+rnq9Tz2jgq4KvWMEvWi1jOa0S6rvYl9b0WIBD5ZCxgz24qufL1bMWe02P2/TAJt0eedSLwzV03Dp8NgepQyZah/JEgUF6IJxaBy61DoB2bdXuFWvXVe1esXZ91e61avdFF0cv' \
			b'+Rmsk0mQJj6KUWlv6oDYAw2I2VD7OFfcurCg3J6kr+No8mBPhaHxTRzodjIk6vTdk4qP5g1PbdKMBE1m8Vzm1vS0jLqqsOtyJTO5Nk6tqjoxcg9GRmahTB33vmZTE6cnyRcGf2M328qv48YV+Hzg7nfgfhm2d2y0KFqcnEHF1Jmxx5u8DDIC1gomAlvAwC03' \
			b'dOLC0sgAioqTYqJj9op64ThccQ1QomgKKzVLckHDIHNjVoy/6s9rW3Gmcpw3x1lynCXPfYIGwhqsBv26U9W9YJIdPxZ4VpgPVZh3EKbn2u+52nuu9r6bk2k0eFW2S7JlE+HZRISmVtT9Rt6LkRf7LMPh4tgaok3Hst9U3+brfVIj52XFXsuq+iFfkV5BiIrd' \
			b'zqter0ev+NqAEgdz+K0KvDQF0qsAtUVek0JRS0pe2sA2WVV5waqkxyARfnXaPrNeC7/+pOrA8fW2QMULY3S6qvma1Wx81e816xf2q36vVr/0fjF3Q+m3Pimd25MSvgFMfRLbSt9ExntNVJyhTkv5llonVziJ0cg0oJt64fxreaH9QK850kWa8F1rwNPXgNf0' \
			b'4iIqoyrh6Zphq2N708P2lkby+JG3qucp1KPE6LGVtA0f6UZU42inquQRVaK1kIQ5wzO+DJsgHnk8Yxl9gil+VcuD08RUOT8OtaucH8HMdCaaeHkwFpcyepuEDYsTZ0Vyk0ZYsJMzvj5GQ1T8hN0J4LuOe0JVWQ/RKJqmSvfBHoIaIz2/wFXZ0STInZz544Jk' \
			b'vJwQvh5AKXPfEu6DryJU9d1P41A8lrr5BQeZtWwU64YHBF7QMMDX7Juter66dNLUB+LH1m+w0isZfVW95ddj7nqrVC1aFaJDtxk6WFZVLXGKFpO6R2XwGlTkg6/YB1+xDz6Nslm+p0pH5H2v2PueGrWisBfsx5kHHwLHkjE9y/bfclwn439Ohnar+td70rN6' \
			b'6uqL1zz58RrfN6m+dxepObJm1aht7HudvF5VZbYos3CHl+HwjSxCsG8qgre+IxSqbb5E24wvznGdV7XOb63zuopsq8jq6xMXaiZk3N7bWue3jiM1tc5fZJ3H13A1v6OJPziScEMfV8If0KeOnw7R8haKvokvM+j8VQjy5NI86kNXdJxqXevyiquOkbrSSN3w' \
			b'sUZoHqeiIxO4QmjLx7LgPXuQ6WLBevJi0tFpSRfL5JInDd+CfqzcUDcS38UTI4PY6PPBGaDhMxpdqevsXnK9QycdGkuuL8RdthpbYUQ3XInRTJy3Y+eRMTp6WyjxsiCfxwqYi68h7C1QVXipKkR/Js3+TJr9maQFa2nBWnxD8NfxI6V13J55xdDqz3Gv/bS0' \
			b'TKeqK07ew4swXJ/5GRe9W7QsPKirH8sjjz+YmS5Ay15M5HXCv5YHegLrL7D+AnduyelB84wK6ZPfoahT7leKKOdZzS7Ejiv6qOFEPENKniobrkOemeU5suea4vlJ1jPXPDMvxO4pqNTUsbELrBmoGMODWkYGtcyNuHfz+Ifh8Q/6gdIaGZYwNNJADzOxbyL2' \
			b'Kft7y8OOuMUGLReP+uEFvlMI/EM3qhbnUusVu9WZipTrVbDjlsqDoHUiacP7AlBZrbwZbtn0WjG99kbGetj0Wja9VkyvvZEv6Vkc+oFcg0Rr+7rW9hVY/4ErSyD1wwXy8I7nHAeB0NyNfAzX1Zpx7TXjRSsrjaPAHD1wdcnJ3dWXvB6q9x1I2AHbGCqBPRHj' \
			b'qx6KJF++64PN0ovh9qItz8/J/PYBrnSOy5zjGue4MndtjpfZHOGmnu205/rhY5XwtTE+3LITQSwf9z3lswGtfDeAGhU1U17znppvqOp4KNvYVeE+3Ao4KtV1E+u6kjqOHKncuFBuhEPHwOhEm+x21hxeN/igT5/MRjce/Gx2V9RoFhirrMOPS6hYoZNUWNms' \
			b'MHzkpx4A9wZAPFgobqZBcokitlTMQRm5gF6KhmXot2Kud6xVHgMIXGcwr5hTqpGeayNpwnE9o2bWcm2iuqELtzknbnTckWnxWxv4jSIULn7qCj+ohF9Twk8pocYgEy3WflxbDZeRwMUOoOoofDMbaoHC9/Ox2uAwN+RP4WJruGIRLlaMy4Xgmri4EB+uQ03i' \
			b'hPOoNNCaQsGiZLHOoXhxaSOQrkIjgkvt4DQLrlGFy1NBbVMGlQ3noJwK14rDt8LxlXBcGgnXksOXRHFdMXxnFN8QxVcesUGj2z42aPTPhfIqfEcO6ovChVxxwQycVoYy6QZbMioYDe8R7gKFP7aQ0yPk/Ah3PkIOjgb3m8Oxg9MNhsMu/KE2jmggjmgZjlCO' \
			b'o6bTcAnagSNI4IiN5oj6OaIij9iOjtj8j1CXjqivIzb5I7b3IzaqI7b2Izb1o8YjqE7HDtOh6B2mAGdAr0eHwaCIIwjxCBX1iKlavNjgvTHj2EKPWEmOAS9vMS28GYj6iLcG0R09hoCOjngnLDnICSVxxMyAHo4ab8rpevyPDh2LAY3aEe3XsaVojZESQwU8' \
			b'Ksw21JpjwFxQeVGqDrMLwVD9j1hqlJTDQKhMR6ikR1Dg0WNCGAvLQulDACkHd1q6d4un4Q9lhZb2qPE+WCa0pkc0mUcsMgkf76opCCNjPEgPfjv8hQSgRhw7KgJpA7MC98ByotChvh7xDlj4QEqi/+BakhyEesxMQ8XAI0gETNgR6uHRo5CxWBAb2twR0w5a' \
			b'sk1VBHWLmSX5QgyoxceO8goHAU8qEjOKEi/uvkYTh4atmrVq1taYtWrTqk27AJum0KZN2TJXmLNmhUXrj9COWDczbeBOH0+32Lhu4L+jHtDqqRHLd44WT+20es2I5bPZ+uGbc2gBcSWgWSvoUTd+wd75vsXz+2yepwtN3Jm0fX6N9bs3++c5O9AgfPr3GDbQ' \
			b'j1jBMzd+fqf582MGEPMkRtCTGfRLhvDwL3eLfPa3SOhO3wKy/h++abXZOlJXWWykPzGTNJQwZyzTlFd/PIB78dl8enG5FSNaDDEs9PRLa6omh7Z6lrUY6jgxscXDZRxr6ZnaPGzVG9HBkZU4yoKjFTgCk0Y6TDbLvSGtlkdo0ESn4S0ebVk22YOZCvyAaDTh' \
			b'+Llb/DwrmXKIh2Mc+FVqMusQD0dYRs2722HiIRyXUR2aeqxBWIWWTD4uVnxi9o2Yfnc3829tRgBO8GzBAK5KlVDgBAeNIAFqO8iC0ACyyHhA64FKtwuEwN8SEVip0DrQB5o8/5Etw1rCRm2UFjFypgamZJkbcTeSg24q8OAwiSEgoWFIW9CEGIF1zxRUoQOs' \
			b'6PiLQ4ty1QReKPclYuh9TMwyDk+2qvc3SpycTxzYTPluVa8QIi7hkMhkyKJ0HxorbYRLw1z0ckT2gAvD3KIQKrvwi0sogqGF5mKMHtTodgOoFYWI90RiuCxVbOUxyBL14u4o/Eh9e/iX6kqPgrF+LLEwSavgIYuF+ip+AEZMcxMZqX4xHEttTwGS0g8pXsQk' \
			b'ng6xYalebeA8JXAyMlV7Sw9uyt6S9h3wFB+lult6TArNLT4pMVjRRt/icwvY4Ft6UgGjdovPCGBwIMAhec0cee2TwndN3+WhgetHoKvuCN4CuifAFdhW0F4iaB2D1i2AFiubG7DW0SmsQi4dYOVw05iVWAmy8TjvJsgWPbSUPmVTIBtvONdjk0hTSB3rtFF8' \
			b'3b/lKE1TqO56sQcbsZSMPbYfV9CUTkagxtJLnKk0+10/MtmRnk46gCpIEiUz3SkyTxLmTmEsciF1oqWUdRSWbi8sY6n7sBQ9L8KS45WodJOkdFtJ6TIps4wmQekYlJLzyEnHnHSCyVhaUdYqSI7DcYSJdg8Tp2h4HRwMK/j3kOyL66VU/p0v/5B4mNGlqRf6' \
			b'xsBgBoZiy4Ak73OcxRFJJfFM3o3Yo3sI9jhMYgj2YvxZ7EmkCexhUIk9isojlVg/8y3HsJdDddfL4GAbG8pkCy7ESwWXzuNEKiXu8ETEHRVCcMfpjIx7YvUrmTdyA5dy4guBI/FiMceIx1reQbxU6h7xooqXiCfxCuKRGEaJR4XbQjyVB04L+U8RT/EcUsy5' \
			b'EE/xGCo3o0LHoq8B8ca7gxF1M/0/t3Ne6jmA7rEhVwF35oBj5wL8mQUcRujBrfAw4H2Osww3udbk3QQ3XcBN5y3BLd52Fm4caQpuemYirnfPUbqlUN31Yg+22Ym6VOpItvEUemQrpvGoBJFseoJsPaqdpMw9uVjOQtbENSngKNf0Xq7FMve5Jtpd5JpIoOCa' \
			b'nuSa3so1nbmWMzrJNc1ck5xHrmnmmhauxdKKtma5JjwbwZivGKsYqxhbhzHDGDNLGDMDjJkCY0YwZtZgzHA8k3cTxkyBMZO3hDGJP48xjjSFMTOHsfKeoxhLobrrxR5s8xiLpY4YG0+hhzFTYMwUGDNrMHaSsmBMylnImjAmBRzFmNmLsVjmPsZEu4sY43gl' \
			b'xswkxsxWjJmMsSyjSYwZxpjkPGLMMMaMYCyWVrS1E2PhiTF2R7/BBwbYgkPhc4PSqGPiY8BozkHR9Z0U++DxDJ4lX0U1cFZUo96KdHYRPZ7jmbyb0OML9Pi8JfSscmJUe7wYudrlv3HypAwhMfzkdh+ejjjR5deQpfVRkCnvabaLg2i6S8LoMO+OA8bvBUzU' \
			b'Zx8wosN9rpKnbNnqMEn1QdiS5DTuOK7YaVIVXpO433OcpBN9mER6ZGp0m6kx471xrX6Td+4O7fWXxNlf9TyIdFXdJKSPoTYxTyuMUNKKfoVW2KDEZVJPe0xSUCRWvMTk3UgsupMQi8MkhhAr3U2ghQeOk4/ooiQ4M9jq+YIJfmk1g7De/cfwlUN114s92Gbx' \
			b'lSQgEJtIoTEiM4abnI6I00w5iqGyTnQW2AzwTu/FtIslLzSBqItFHiOd3vsiQMpxj3RR90uki9LIrNOTXpBUVbbgjqoP466Q0VRXipJPGojQo+x40UShc9Hczq5U29QhwTokWFm3jnU8s6WXZrb0YGZLFzNbWma29JqZLS3XmrybKFfMbHGYxIiUi7ed65pJ' \
			b'pCmyzc1s9e45SrYUqrte7ME2T7ZY6ki28RTKPpsuum26mNnSa2a2TlMWjkk5C1kTx6SAoxzbO7OVytznmGh3kWMigYJjkzNbeuvMls4zW0VGJznGM1sx55FjPLOlZWYrlVa0tZdjbeVY5Vjl2DqO8dSWXpra0oOpLV1MbWmZ2tJrpra04Xgm7yaOFVNb2uQt' \
			b'cUziz3OMI01xbG5qq3fPUY6lUN31Yg+2eY7FUkeOjafQ41gxtaWLqS29ZgDyNGXhmJSzkDVxTAo4yrG9U1upzH2OiXYXOcbxSo5NTm3prVNbOk9tFTKa5BhPbcWcR47x1JaWqa1UWtHWXo7tXQGjcqxy7NlxjGfK9NJMmR7MlOlipoz3Oc4yxzzHM3k3cayY' \
			b'J+MwiRE5JvHnOcaRpjjm5zhW3nOUYylUd73Yg22eY7HUkWPjKfQ45guO+YJjfg3HTlIWjkk5C1kTx6SAoxzbO4OWytznmGh3kWMcr+SYn+TY1mk0nafRChlNcoxn0mLOI8d4Mk3LfFoqrWhrL8e2r1VSOVY59jw5RkvxtViv5zmGEUqOsY8Hcyz6e9DvEsfk' \
			b'ZsixuBs5RvcQjpliixyL8Wc5JpEmOIZBkxzr3XOMYzlUd73Yg22WY6nUwrGJFEqO4U/kGJVAOMbpLHDsNGXmWCxnr9BJKaMcYwXv4Fgqc49jUbtLHJN4BcdICKMcI4lt4RhVFuZYIaMpjlHyIeVcOEbZ8XylKjQs2trLsdmVPyrHKscqxzLHeFzRLI0rmsG4' \
			b'oinGFY2MK5o144rGcDyTdxPHinHFFGzyuGKMP88xjjTFsblxxd49RzmWQnXXiz3Y5jkWSx05Np5Cj2PFuKIpxhXNmnHF05SFY1LOQtbEMSngKMf2jiumMvc5Jtpd5BjHKzk2Oa5oto4rmjyuWMhokmM8rhhzHjnG44pGxhVTaUVbezk2u1pH5VjlWOVY5hiP' \
			b'K5qlcUUzGFc0xbiikXFFs2Zc0XiOZ/Ju4lgxrshhEiNyTOLPc4wjTXFsblyxd89RjqVQ3fViY9PoXBE+C7JY7AgyP7INQFYMLJpiYNGsGVg8TVlAJgUthE0gkxKOgmzvwGIqcx9kot5FkHG8EmSTA4tm68CiyQOLhYwmQcYDizHnEWQ8sGhkYDGVVrS1F2R1' \
			b'KY4KsgqylSALDLKwBLIwAFkoQBYEZGENyCS+ybsJZKEAWchbAlm81SzIONIUyMIcyMp7joIshequF3uwzXMsljpybDyFHsdCwbFQcCys4dhJysIxKWcha+KYFHCUY2Evx2Je+xwT7S5yjOOVHAuTHAtbORYyx7KMJjkWmGOS88ixwBwLwrFYWtHWXo7VtTgq' \
			b'xyrHVnKsY451SxzrBhzrCo51wrFuDcc6jmfybuJYV3Csy1vimMSf5xhHmuJYN8ex8p6jHEuhuuvFHmzzHIuljhwbT6HHsa7gWFdwrFvDsZOUhWNSzkLWxDEp4CjHur0ci2Xuc0y0u8gxjldybPJ9aQzZxrEucyzLaJJjHXNMch451jHHOuFYLK1oay/Hnnox' \
			b'jsqxyrFL4RhaG8go/sxyDCOUHCMrJRzjfY6zyLEYz+TdyDG6h3CMwySGcCzGn+WYRJrgGAZNcqx3zzGO5VDd9WIPtlmOpVILxyZSKDmGJyLHqATCMU5ngWOnKTPHYjkLWSPHYgHHOMYK3sGxVOYex6J2lzgm8QqOkRBGOYYhmzhGlYU5VshoimOUfEg5F45R' \
			b'djxfqQoNi7b2cmz78iCVY5Vjz5Rj7Ohhlxw97MDRwxaOHlYcPewaRw/emGOymzhWOHqkmDY7esT48xzjSFMcm3P06N1zlGMpVHe92INtnmOx1JFj4yn0OFY4etjC0cOucfQ4TVk4JuUsZE0ckwKOcmyvo0cqc59jot1FjnG8kmOTjh52q6OHzY4ehYwmOcaO' \
			b'HjHnkWPs6GHF0SOVVrS1k2OqLujxuBwbW8yq8uzCeMYOH3bJ4cMOHD5s4fBhxeHDrnH4wKXfxOEj7iaeFQ4fHCYxIs8k/jzPONIUz+YcPnr3HOVZCtVdL/Zgm+dZLHXk2XgKPZ4V/h6W/T0ojgo5tSWqnaQvVJPSFhInqkkxR6m21+sj5bVPNdHxItU4Xkm1' \
			b'Sa8Pu9Xrw2avj0JGk1Rjr4+Y80g19vqw4vWRSis620u1urxHpVql2kaq8ayZXZo1s4NZM1vMmlmZNbNrZs0gkpVZs7ibqFbMmnGYxIhUk/jzVONIU1SbmzXr3XOUailUd73Yg22earHUkWrjKfSoVsyaWZ41ozgq5NSWqHaSvlBNSltInKgmxRyl2t65s5TX' \
			b'PtVEx4tU43gl1SbnzuzWuTOb584KGU1SjefOYs4j1XjuzMrcWSqt6Gwv1epiH5VqlWrbqOZ4Ds0tzaG5wRyaK+bQnMyhuTVzaE7imbwbqeaKOTQOkxhCtRh/lmoSaYJqbm4OrXfPMarlUN31Yg+2WaqlUgvVJlIoqeaKOTTHc2gUR4Wc2gLVTtNnqsXSFhJH' \
			b'qsVijlHN7Z1JS3ntUS3qeIlqEq+gmpucSXNbZ9JcnkkrZDRFNcczaTHnQjXHM2lOZtJSaUVne6lWl/6oM2nPlGYgI4UfOAYZ7eivae6v6aX+mh7013Qm2zF9+IXOLvbY5GqTd1OPTRPb8JiDJELssMX7zqENDQXGmuqx6Rm2cf3Mf+O9tpQt7G3pyW2+1xZL' \
			b'Hntt4yn0vjumym6bPojUAud0xfdhrCSbSpe/D0NB/H0Ymw9N2h3vuOltiKMM61y4Qb9NVL1EOBLDsOeWpHHSc9Nbe26aGJerIEtqsuumuetGURVlGOIUnTjNnTjNuEtF55wNcGfwY9BQ0+LHoS3gL6DFam/p8QDMzS2yHEzFLX/GJgPwnNYMGXxj5sIxaGoH' \
			b'79KQuL2Dp7iDp5Y6eGrQwVMZg7zPcZY7eIrjmbybOniq6OCpvKUOnsSPFMQDbGBqpJvHUae6eWqum1feebSbl0J114s92Oa7ebHssZs3nkJjRFrS01NFT09xT08xC1OCSz29k1tIT08KXIieenpS0tGentqGwdzTi3ntcTAqe7Gnx/HKnp6a7OmprT09lXt6' \
			b'WUaTPT3FPT3JeezpKe7pKUZfKq3obG9P75wWFamgq6C7MNCxF6Vb8qJ0Ay9KV3hROvGidGu8KJ3heCbvJtAVXpTO5C2BTuIn0BkGnRkBHUedAt2cL2XvzqOgS6G668UebPOgi2WPoBtPoYnSEtAV7pSO3SkpWIWc4BLoTm4hoJMCF6In0ElJR0G316ky5bUP' \
			b'OlH2Iug4Xgm6SadKt9Wp0mWnykJGk6Bjp8qY8wg6dqp04lSZSis62wu6c1p0pIKugu7CQGcZdHYJdHYAOluAzgro7BrQWY5n8m4CnS1AZ/OWQCfxE+gsg25s4o5PT4HOzoGuvPMo6FKo7nqxB9s86GLZI+jGU2iMSEtAZwvQWQadvDqQElwC3cktBHRS4EL0' \
			b'BDop6Sjo7F7Qxbz2QSfKXgQdxytBZydBZ7eCzmbQZRlNgs4y6CTnEXSWQWcFdLG0orO9oJtdlcQ+NevO6gvZ6o7Us33ymbVfyq70uzD6eaafX6Af0cYPCOgLAnohoF9DQM/xTN5NBPQFAX3eEgElfiKgZwL6TEBKgnOCtocvmOKgn+Ngef9RDqZQ3fViD7Yx' \
			b'DtK0ZGJhlEJk4XgqDcmLr4w85KCERM9I9ILEmO4SEk/uJEiUshe6ICRKoUeR6PciMea1j0TR/iISRQ4FEv0kEv1WJPqMxCyjSSR6RqLkPCLRMxK9IDGWVnS2F4nntMDJbh46QmK4mH5gpeEj0lBtJGIYUNHvXdaLXTnNkiunGbhymsKV04grp1njymkknsm7' \
			b'aVmvwpWTwyRGXNZL4kcq4gFUOvoRKlISHE118YKpJb4Kt068JZKx5TmZYqmvMh+jS32lUN31Yg+2+aW+oiSEjBMpNEZkx1SU02nBL3byNOLkmdJcWvbr5C6y7JeUudAFLfslhR2jotnr5Jny2qNi1P4SFaMcMhXNpJOn2erkiZzy+fWFQk5TZMQGadjZEy/u' \
			b'uKalJcDY4dOIw2cquehvLyHPaemUc+4xVjZeHhsfs6fomYd+iYd+wENf8NALD/0aHnqJZ/Ju5KEveMhhEkN4GONHHnrmoS946JmHnnkoF0zw0DczvcTe/cc4mEN114s92GY5mCQgHJxIoTEiM+agnI4c9MxBLxxMaS5w8PQuzMFY5kIHyMFY2DEO+r0cTHnt' \
			b'cTBqfYmDUQ6Zg36Sg34rB6niMAMLGU0x0DP/Ys6FfZ7Z54V9qbSis53s0+e03Epl32Wwr7kg/rWP/U1vfmldL720rgcvrevipXUtL63rNS+t41es5aX1uJu+6V28tM5hEiN+01viRwbiAVQ4+hEGUhKcE5Uun/q+99wL7L37j37fO4WWUU+3WQYmCQgDJ1Jo' \
			b'jMiMGSin01e++TV2La+xpzQXGHh6F2ZgLHOhA/rWtxR2jIF642vsinrewsGU3x4Ho+aXOBhlkTmoJ19l11tfZdcdjb6kb35nWU1+85tfZ4+5FxZqfp1dy+vsqcSiu70sPKdFWioLL4OFl8LBR+0HttwPbJf6ge2gH9hmBnp5DZB+F/uBfDPqB8pu6ge2RT+w' \
			b'2FI/UOKnfiC/Ckg/sR/Ycj+w5X4gx5nqB7Zz/cDy/qP9wBSqu17swTbfD4wSiP3A8RQaIzKTfiCfTv3AlvuB8lpgSnOpH3hyF+kHSpl7AkjKGu8HttsYmPuBMa89/kWtL/YDRQ5FP7Cd7Ae2W/uBbe4HZhlN9gNb7gdKzmM/sOV+YMvsS6UVne1l3zkt5VLZ' \
			b'V9l3sezjt//80tt/fvD2ny/e/vPy9p9f8/YfNgB5+y/uJvYVb/9xmMSI7JP4iX389p8v3v6jJDgnaGz4gin2zb0D2Lv/KPtSqO56sQfbPPuiBCL7xlNojMhM2MenE/v4NUAvrwGmNJfYd3IXYZ+UudABsU8KO8q+va8Bprz22SdaX2SfyKFg3+RrgH7ra4A+' \
			b'vwZYyGiSffwaYMx5ZB+/BujlNcBUWtHZXvZdxYIvZ8C4mfcgFlkWORb5FdkVmXUpvLooVvGCLX5pwRY/WLDFFwu28D7HWWaVXGvybmKVLlil85ZYFW87t16LRJri09xyLeNMSrnQXS9Xg22eSbGkkUnjKZTLs+CJRCN94E8fLPInJiTY4UVYPC++4qcWXvEb' \
			b'F17JqInF6qNGlLaIGilkgRotqOlRZuuSK15nysgt3BxmeMmVmOuIGV5oxctCK6mkoowNmCG8nPFyKrVrVbtWl4Mry7iyS7iyA1zZAldWcGXX4MpyPJN3E65sgSubt4QriZ+6Vpa7VgW0PHMLf9DI8IkpdNm5rlV5/1GMpVDd9WIPtnmMRQlEjI2n0BiRmZCM' \
			b'TyeYWe5akaZCTnMJbSd3EcZJmQsdHH1S1jjv7F7exbz2eSdaX+SdyKHgnZ3sWtmt0LMZellGk8yzzDzJeWSeZeZZYV4srehsb9fqnFZYqV2r2rV6NFY5ZpVbYpUbsMoVrHLCKreGVY7jmbybWOUKVrm8JVZJ/PmuFUea4pPb3LVK99VdL1eDbZ5JsaSRSeMp' \
			b'9LpWrqCRW9u1igkJdhwzxzFt3BRq3F7UxGL1USNKW0QNxytR48a6Vm4rZVymjNxitmvlGDOS64gZx5hxgplYUlHG1q7VOa1rUvFS8fJoeAmMl7CElzDASyjwEgQvYQ1eJL7JuwkvocBLyFvCS7zVLF440hRewma8pFzorperwTaPl1jSiJfxFHp4CQVewlq8' \
			b'xIQEL4HxEhgvYQovYS9eYrH6eBGlLeKF45V4CWN4CVvxkv0C4y1m8RIYL5LriJfAeAmCl1hSUcZWvMyuJnIpeDmz0br6JYDrHJ0L7PgQlhwfwsDxIRSOD0EcH8Iaxwes2OL4EHcjkkLh+MBhEkOQFOPPIkkiTSApzDk79O45hqccqrte7ME2i6dUasHTRAol' \
			b'nkLh5hDUIX1TO6xxcDhNmXkVy1nIGsEVCzjGrrDXwSGVuceuqN0ldkm8gl1h0sEhbHVwCNnBoZDRFL8COzjEnAu/Ajs4BHFwSKUVbe0dhTunJUAqxyrHzppj7BQRlpwiwsApIhROEUGcIsIap4gg15q8mzhWOEVwmMSIHIu3neUYR5ri2JxTRO+eoxxLobrr' \
			b'xR5s8xyLpY4cG0+hx7HCQSLogmN6DcdOUhaOSTkLWRPHpICjHNvrPZHK3OeYaHeRYyKBgmN6kmNbXShCdqEoZDTJMfagiDmPHGMPiiAeFKm0oq29HDunhToqxyrHzppjhjlmljhmBhwzBceMcMys4ZjheCbvJo6ZgmMmb4ljEn+eYxxpimNmjmPlPUc5lkJ1' \
			b'14s92OY5FksdOTaeQo9jpuCYKThm1nDsJGXhmJSzkDVxTAo4yjGzl2OxzH2OiXYXOcbxSo6ZSY6ZrRwzmWNZRpMcM8wxyXnkmGGOGeFYLK1oayfHzDktulE5Vjl21hxjr7+w5PUXBl5/ofD6C+L1F9Z4/WF9Fq+/uJs4Vnj9cZjEiByT+PMc40hTHJvz9Ovd' \
			b'c5RjKVR3vdiDbZ5jsdSRY+Mp9DhW+PgFW3BszfTXacrCMSlnIWvimBRwlGN7vftSmfscE+0ucozjlRyb9O4LW737QvbuK2Q0yTH27os5jxxj774g3n2ptKKtvRyjBTOAJGe04v654WxplX0Ih7Z7/mgLd8Cbv0DENY+9bhTaDUQdDz8eadnTOd7RSkUD9w5d' \
			b'uHcc05e09RoHD7q/OBCm/bSQVOHigU0zbmkhqSC3nuMe2hI97eOh53w8ejcdXT0Ks4y9G/b4KOMPtjH0oSzzGlISLa0hFbj6ts1oaiUGdeH9oUPGIKe3gMHTlBmDsdRtKQIT98zUFJte6R6CS6Sd4DDJoIfDqPQlHJKWB4tIhSke6q2OIqgPjBwXkeJMzTqL' \
			b'aHYWifkXKGp2FtHiLJLKLLrLUMQ72lsKx/9Ni/8DHeH/TtH/+lYISZnDcOKjOryeo2PiYgnFUSJ2kYKEQMHeFPAGtFt0OCSwTXfEhFYliRKF1vgHCmWILmaGJFs7SQNyLBHjhBZDn78NhIhkmCMC0iBRwIv194XFR5O+2tr3zPyIjV828GTZs0lP9jza8BXW' \
			b'e8p0b/TNi0Z6thOS7W/fxCb7us61LlnRoyw5NG0w93UchjZy2ToOTeOp79w2exgN4bwJRPuXLB+aPbJ5ZO2iqUOLpectljsbo6WS3dLVdm16unUz9mut7dr2qEoPk9dkwIonzbarhuyeDJkqXt4fMWbbDJlZ+ejV7DVkMyMO+22ZXWnL9E57pi7MppkNds2v' \
			b's2tB369t69k16jU/hG0zT2XfFH1Kbr19U2xz9tk4c8F2TlF+19s6s9LWYWVdYe/sfXU1/SM9uJ2Mni7YPdU+wnMchEF1aKEqtF04Axu4ceTyXvqld7F/u2xfHHY8u2c7yln5t84O4oD3Yz3r0eM8og9nZlxzTjYRBXZPHVlFTrmrn/8O/4IafwsFoUE4d4+D' \
			b'cM0Wy3g68bThSXDJGuoJa6ieb882Wb+xuZpyngY/M9cW8zVYwZxYRZMso+qwFnRiIaEWQNk1fjmC5m5COX8Df+opLCdZzd5MzS7LiSk8gPVcay0ne8ZYI2rveGgdUSvTT4zYUGgCkt8v4tqBLaJjdwBNz/NiOuN0JM9/oAhbWlDVi5PbEe3Fsc0Li+OBpudN' \
			b'/yRTGw9pUqs5HXSou8cfKDyLQcInNYeTprAOFBadZ3d/A4Xh8Prc5mdnXJEeea723ExY80RztYX56ux5W6/Nlot9wjrx+XLnOGd7xtZL0VdDn2zO9vCv7haASh3d7vws2S7rBblCyWI9uV5LttWKocruZ+b2ch7EnsTdhNxSSTJouZ6NHdvxFMZCUvf2KAbF' \
			b'uxIDBr+QOZTteRqyEcfrRzVm8OvuatSKwbjBIFw1cAsGDk0Vudofscqdu6FzZ2DrjqgszJO5m8nTpIk0vDYYVAP13bsBhOw8iQ0EzT2e/dvzjuXYiyePOboWrumhrqXafvaGjzLoH93subDX9g0NHzaPpxhvuw/bd/K4px7A2oUnsnaFpdP+zJ72ntjSVSv3' \
			b'yK9L9CwcqvqMH+7Ow8A9gHHTD2DcujMwbqEat2rczse4qWrcnsC4mQcYqGvOwLid+dRpNW7Py7id9bDc1Ro3eyWzEOdsyc7iZf2LsV7nb7geykopEtAFT5Lei1U6/Asa3i1abPTzgFxWA/UsDNROD7XrMVLkfn72RuryXTnu0R0t4CqBluyUr3aq2qlrt1PU' \
			b'/ziXZynKTLVSy1bKd7cMGO9u0baTvTrDNwGqvar26r7tlT0ne2Wrvdptr57c33/rOsp3MF86L3d8sWZsuCzxfZuyRszZMzBp1Gx7Zg1PxBeacEHs4u8BzRzngyQW1tg7e/69yJMFeh/C6KmODR9lZ4/xc0/+rkA1ftX4PZXx64bGryuMX9f7e1Dj120zfl01' \
			b'fmz8WjF+3U7j9wDvCVTjd8HG77kYPmzt/c5skw2fa3p/D2n4KB/rDR+er4ZPnvgw47uM3gO8LlCH5+rw3ENZNW7B1+uacS6W6yzG51yLdoqmPd0DeP5XO1Xt1N3tlER6bj5kdzVU/C0+/rt4Q2XRjwwbEn7jUWOjwm89YsOCX7ZfD+HcX+1XtV/3YL/aar/2' \
			b'2K82/T0H+1X995+n/YJy4rQSjq6erS2jqn2h7vyU9ycxZXTne+kyShnuZMkojUVLpkjLELRs0wzaMEet+xZ5Aa3ulqw3NJtbtL1Q/eFXk3Wrzv/P07qdr0VTF2zR1JNZNHVvFk3dg0VT9/FstsmO1ZcDqh07AztGjbK+aLnBjl3/YL7Rt4Q3aGO4w73K+nJA' \
			b'tVdPYa8ogfpi+FZ7xWJ7HpOPGs0U1unG4A4/Xz35ywHVXj0Te9W2j+kDdo0GSyT4fNwlNHQM0SmygSctTc9X/sn9+au9ulZ7xRHP4N3LKzFXz867SwVcfIc+suSf3PW+2qlLt1PcaM/Ltf6i7RSn/uzNVIte89jOOxzAahXZq+o1X+3VdnuF1f+c3wS6aHNV' \
			b'H6vEXuFwFX+70len+WqmdpipUM1UNVOPaKaqb3w1U0tmiur54zhfVTtV7VS2Uw3aKTJT1+ICD3lLH9M9K5OFbx6cy0d06/L2D2y/UOVHvPKcLRls7hzsGSppzqpt+hYHKO81tZUO6ylWJ+U4wB9ee1xsBs6j1uCPTofyNBoKT6e7w2sF/ykKUAFbBQTA/otj' \
			b'e3jdYGyMd1RwcOiwUYBhCHQtCPY1WhgwAAfQFygA6jNUAFAsCAY016GNhRhQb8mnGNugwXaI382M9wQb0+AfOqagNYZ4UENahcsE4AI3YHTBCsERKKwFZbUdtnw+VlCPFLrTBksZMveRIXNY8Y9uZ/F2fvaGiuy5W3dni5bfnvxrQetsm9vTUMqIm8oIyAlq' \
			b'FVRg/EBeM5YvP5Y1/GxwtuT4aaWGswtNtJ9l4FvvH1ZV/mBU/uuFw52LI81XoLXGffykkqMVyyicyuafpmxABIffpIYyApnv4R99kr1VVKaws0x2plge14SB82Bb2uCmi8mWYqKo8ASy+A8fEfpnGMydQNj0wyBvxTEVvyuLjw8CflYImuTgUBRowYq1tEYk' \
			b'E06E0xia5kYzi7RGRqBlJRdnnHKi99dbWpQEWUxLYwKGslDx0RCu8UEEDGFBiaDttLCxXtNTjRkRfJuFH4IoAKoCWEHdRGXgo1/a6PlPH3rnBpsEFz/Dv8lrTm6z9e/06uZkd/zuY3nrpziMSHUIzp5pG6Kn9SfcWDxtr43hg/UBH7u5sekDVMoNTa7Z1+rg' \
			b'UTG1POxarW192Fc5jxaoDnkre2R8JvXFVm/Y+1ofmzbsdcU9uxTXtJvT375xBVPViK+qQvrwzDauHvpszbM5POnG4jF3aT04dPRkDcg9RSPyh/0bjnrd5fonvQ3XFltt7apqEg7PbOPqsbf7P1MH7s/cYofxLpu+4/WwsZR8bURrGhH2FZ7XxtWjNyazUDfW' \
			b'tyOsBvfWlmj+RDacgiiPd244tbPnSpZZfyAndS9X9C2tP9ju4NTBPUojM9zQcFEIamxOvoACx7gqg1Pn0vjsIW3YfZY9nECzCxvPAOa/xQt2bJLuyA/OBZnmQW7a33gyoqm2fFV1codntnH1aC/AlofDeWwssTuN5jxII1or6dlGsthAcGE82XCSvDye2nBm' \
			b'fE28+9rW349VqattXGMb0afneW1cPcyD2UasBvdmH9Hf6r43dF7adSVLro7CrGtY9vDMNq4e7kEbFlaD+2tc7vAQGzoG7rqSBVgHaFa1L3Q9fV4bV4+HG6Apq8G9tTF0D36YDf1ud13JcqzeN+uamT08s419OputzewuHcAtHb25Dl5ude6waUPH2U0XkKO7' \
			b'XroI3c4nwljKbW2EaxohvlrxvDauHuoxG2FZE+69QeKbMQ+8le+a3CEdlvyZj54UExfn0UDt4Xw2/Jos/YRHuBtXly2jKfqe22qsHPfVZqeV7A4rN3wBaX3sqS2+ILbzapCmxaynN7kOVqi7ZwRHZiofbY7yPJt5OGzduEB+83VrNnxr8CHSnd24Cm0Z5bnY' \
			b'Bo/vr17qxmraM5Z0Pj4JZ9Hm8Q3mXRsXqdl59ZoN3xR+uNTHNq5VW4agHqrx75of3WUE3OHxN6yy9xOJNlbbnhGvagz6lSEc6kYbv2i8xwGpVql+leoOdaONq9SdhgSfHjF7nzVxQZQr2ViPz9SVCpe0uZKN9XjmI4HnMkQPEXZv/DZZ/rtLWieJnt6iH7jh' \
			b'hjNRua7c6XW+51NX8EXy57Vx9aieY+uqR3t4ZhtXD1erx6rq4Q7PbOPqUf3i1lUPf3hmG1ePUKvHquoRDs9s4+pR3f3WVY/u8Mw2XsKwvkm5qnrgmnfPa+Pq0R5eG1oyVF6ttCqdYPxAjYATKHE6CfKTyTJQ3+uy6oBeaDkkXCII6ht+LhtfGpZ5dVDIaGzQ' \
			b'd/+PY7uT2KhrugJrVP9POXbWsb2VUbHGsM+X5aVRfX9VHYqBKwV3iuIbXkuZamOQmmepRuF5qDGcFpjbfiqxBhc1N9VabG4trW+DnucgFVmJmVY+phWPXV7tOK10DOcl567B9YzQH4KXB0Dps1pc21/XFcvBsnMKjxs6yzYAsv9akbx1I+mafAa0+fXN/wdi' \
			b'zudF'

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
	_LTRU     = fr'(?:[a-zA-Z_]|\\_)'

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
		('UFUNCPY',       r'Function(?!\w|\\_)'),
		('SYM',          fr'\$|\\\$'),
		('SYMPY',         r'Symbol(?!\w|\\_)'),
		('FUNC',         fr'(@|\%|\\\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LTRU})|\\operatorname\s*{{\s*(\$?(?:{_LTR}|\\_)(?:\w|\\_)*)\s*}}'), # AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

		('LIM',          fr'(?:\\lim)_'),
		('SUM',          fr'(?:\\sum(?:\s*\\limits)?|{_USUM})_'),
		('INTG',         fr'\\int(?:\s*\\limits)?(?!{_LTR})|{_UINTG}'),
		('LEFTDOT',      fr'\\left\s*\.'),
		('LEFT',         fr'\\left(?!{_LTRU})'),
		('RIGHT',        fr'\\right(?!{_LTRU})'),
		('CDOT',         fr'\\cdot(?!{_LTRU})'),
		('TO',           fr'\\to(?!{_LTRU})'),
		('UNION',        fr'\\cup(?!{_LTRU})|\|\||{_UUNION}'),
		('SDIFF',        fr'\\ominus(?!{_LTRU})|\^\^|{_USYMDIFF}'),
		('XSECT',        fr'\\cap(?!{_LTRU})|&&|{_UXSECT}'),
		('MAPSTO',       fr'\\mapsto(?!{_LTRU})'),
		('EMPTYSET',     fr'\\emptyset(?!{_LTRU})'),
		('SETMINUS',     fr'\\setminus(?!{_LTRU})'),
		('SUBSTACK',     fr'\\substack(?!{_LTRU})'),

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
		('FRAC',         fr'\\frac(?!{_LTRU})'),
		('BINOM2',       fr'\\binom\s*{_VARTEX1}\s*{_VARTEX1}'),
		('BINOM1',       fr'\\binom\s*{_VARTEX1}'),
		('BINOM',        fr'\\binom(?!{_LTRU})'),

		('CMP',          fr'==|!=|<=|<|>=|>|(?:in|not\s+in)(?!{_LTRU})|(?:\\ne(?!g)q?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)(?!{_LTRU})|{"|".join (AST.Cmp.UNI2PY)}'),
		('IF',            r'if(?!\w|\\_)'),
		('ELSE',          r'else(?!\w|\\_)'),
		('OR',           fr'or(?!\w|\\_)|\\vee(?!{_LTRU})|{_UOR}'),
		('AND',          fr'and(?!\w|\\_)|\\wedge(?!{_LTRU})|{_UAND}'),
		('NOT',          fr'not(?!\w|\\_)|\\neg(?!{_LTRU})|{_UNOT}'),
		('SQRT',         fr'sqrt(?!\w|\\_)|\\sqrt(?!{_LTRU})'),
		('LOG',          fr'log(?!\w|\\_)|\\log(?!{_LTR})'),
		('LN',           fr'ln(?!\w|\\_)|\\ln(?!{_LTRU})'),

		('NUM',           r'(?:(\d*\.\d+)|(\d+\.?))((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
		('VAR',          fr"(?:(?:(\\partial\s?|partial|{_UPARTIAL})|(d))({_VAR})|({_VAR}))(?:_{{(\d+)}})?"),
		('ATTR',         fr'(?<!\s)\.(?:({_LTRU}(?:\w|\\_)*)|\\operatorname\s*{{\s*({_LTR}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"((?<![.'|!)}}\]\w]){_STRS}|{_STRD})|\\text\s*{{\s*({_STRS}|{_STRD})\s*}}"),

		('WSUB1',        fr'(?<=\w)_{_VARTEX1}'),
		('WSUB',          r'(?<=\w)_'),
		('SUB',           r'_'),
		('SLASHSUB',      r'\\_'),
		('SLASHDOT',      r'\\\.'),
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
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})|\\operatorname\s*{{\s*(@|\\\%|\\_|{_LTR}(?:\w|\\_)*)\s*}}'), # AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

		('LIM',          fr'\\lim_'),
		('SUM',          fr'(?:\\sum(?:\s*\\limits)?|{_USUM})_'),
		('INTG',         fr'\\int(?:\s*\\limits)?|{_UINTG}'),
		('LEFT',         fr'\\left'),
		('RIGHT',        fr'\\right'),
		('CDOT',         fr'\\cdot'),
		('TO',           fr'\\to'),
		('UNION',        fr'\\cup|\|\||{_UUNION}'),
		('SDIFF',        fr'\\ominus|\^\^|{_USYMDIFF}'),
		('XSECT',        fr'\\cap|&&|{_UXSECT}'),
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

		('VAR',          fr"(?:(?:(\\partial\s?|partial|{_UPARTIAL})|(d(?!elta)))(partial|{_VAR_QUICK})|(None|True|False|{_PYMULTI_QUICK}|{_VAR_QUICK}))()"),
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

	def expr_piece_1       (self, expr_or, IF, expr, ELSE, expr_mapsto):               return _expr_piece (expr_or, expr, expr_mapsto)
	def expr_piece_2       (self, expr_or, IF, expr):                                  return AST ('-piece', ((expr_or, expr),))
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

	def expr_mul_exp_1     (self, expr_mul_exp, CDOT, expr_neg):                       return AST.flatcat ('*exp', expr_mul_exp, expr_neg)
	def expr_mul_exp_2     (self, expr_mul_exp, STAR, expr_neg):                       return AST.flatcat ('*exp', expr_mul_exp, expr_neg)
	def expr_mul_exp_3     (self, expr_neg):                                           return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                    return _expr_neg (expr_neg)
	def expr_neg_2         (self, expr_div):                                           return expr_div

	def expr_div_1         (self, expr_div, DIVIDE, expr_divm):                        return _expr_diff (AST ('/', expr_div, expr_divm)) # d / dx *imp* y
	def expr_div_2         (self, expr_mul_imp):                                       return _expr_diff (expr_mul_imp) # \frac{d}{dx} *imp* y
	def expr_divm_1        (self, MINUS, expr_divm):                                   return _expr_neg (expr_divm)
	def expr_divm_2        (self, expr_mul_imp):                                       return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                            return AST.flatcat ('*', expr_mul_imp, expr_intg)
	def expr_mul_imp_2     (self, expr_intg):                                          return expr_intg

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add):               return _expr_intg (expr_add, (expr_sub, expr_super))
	def expr_intg_2        (self, INTG, expr_super, expr_add):                         return _expr_intg (expr_add, (AST.Zero, expr_super))
	def expr_intg_3        (self, INTG, expr_add):                                     return _expr_intg (expr_add)
	def expr_intg_4        (self, expr_lim):                                           return expr_lim

	def expr_lim_1         (self, LIM, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                          return AST ('-lim', expr_neg, expr_var, expr)
	def expr_lim_2         (self, LIM, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):  return AST ('-lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3         (self, LIM, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg): return AST ('-lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                   return expr_sum

	def expr_sum_1         (self, SUM, CURLYL, expr_var, EQ, expr_commas, CURLYR, expr_super, expr_neg):       return AST ('-sum', expr_neg, expr_var, expr_commas, expr_super)
	def expr_sum_2         (self, expr_diffp_ics):                                                             return expr_diffp_ics

	def expr_diffp_ics_1   (self, expr_diffp, expr_pcommas):                           return PopConfs (_expr_diffp_ics (expr_diffp, expr_pcommas))
	def expr_diffp_ics_2   (self, expr_diffp):                                         return expr_diffp

	def expr_diffp_1       (self, expr_diffp, PRIME):                                  return AST ('-diffp', expr_diffp.diffp, expr_diffp.count + 1) if expr_diffp.is_diffp else AST ('-diffp', expr_diffp, 1)
	def expr_diffp_2       (self, expr_func):                                          return expr_func

	def expr_func_1        (self, SQRT, expr_neg_arg):                                 return _expr_func (1, '-sqrt', expr_neg_arg)
	def expr_func_2        (self, SQRT, expr_super, expr_neg_arg):                     return AST ('^', _expr_func (1, '-sqrt', expr_neg_arg), expr_super, is_pypow = expr_super.is_dblstar)
	def expr_func_3        (self, SQRT, BRACKL, expr_commas, BRACKR, expr_neg_arg):    return _expr_func (1, '-sqrt', expr_neg_arg, expr_commas)
	def expr_func_4        (self, LN, expr_neg_arg):                                   return _expr_func (1, '-log', expr_neg_arg)
	def expr_func_5        (self, LN, expr_super, expr_neg_arg):                       return AST ('^', _expr_func (1, '-log', expr_neg_arg), expr_super, is_pypow = expr_super.is_dblstar)
	def expr_func_6        (self, LOG, expr_neg_arg):                                  return _expr_func (1, '-log', expr_neg_arg)
	def expr_func_7        (self, LOG, expr_super, expr_neg_arg):                      return AST ('^', _expr_func (1, '-log', expr_neg_arg), expr_super, is_pypow = expr_super.is_dblstar)
	def expr_func_8        (self, LOG, expr_sub, expr_neg_arg):                        return _expr_func (1, '-log', expr_neg_arg, expr_sub)
	def expr_func_9        (self, FUNC, expr_neg_arg):                                 return _expr_func_func (FUNC, expr_neg_arg)
	def expr_func_10       (self, FUNC, expr_super, expr_neg_arg):                     return _expr_func_func (FUNC, expr_neg_arg, expr_super)
	def expr_func_11       (self, expr_pow):                                           return expr_pow

	def expr_func_12       (self, SQRT, EQ, expr_mapsto):                              return AST ('=', ('@', 'sqrt'), expr_mapsto) # allow usage of function names in keyword arguments, dunno about this
	def expr_func_13       (self, LN, EQ, expr_mapsto):                                return AST ('=', ('@', 'ln'), expr_mapsto)
	def expr_func_14       (self, LOG, EQ, expr_mapsto):                               return AST ('=', ('@', 'log'), expr_mapsto)
	def expr_func_15       (self, FUNC, EQ, expr_mapsto):                              return AST ('=', ('@', _FUNC_name (FUNC)), expr_mapsto)

	def expr_pow_1         (self, expr_diffp_ics, expr_super):                         return AST ('^', expr_diffp_ics, expr_super, is_pypow = expr_super.is_dblstar)
	def expr_pow_2         (self, expr_fact):                                          return expr_fact

	def expr_fact_1        (self, expr_diffp_ics, EXCL):                               return AST ('!', expr_diffp_ics)
	def expr_fact_2        (self, expr_attr):                                          return expr_attr

	def expr_attr_1        (self, expr_diffp_ics, ATTR, expr_pcommas):                 return AST ('.', expr_diffp_ics, (ATTR.grp [0] or ATTR.grp [1]).replace ('\\', ''), expr_pcommas.comma if expr_pcommas.is_comma else (expr_pcommas,))
	def expr_attr_2        (self, expr_diffp_ics, ATTR):                               return AST ('.', expr_diffp_ics, (ATTR.grp [0] or ATTR.grp [1]).replace ('\\', ''))
	def expr_attr_3        (self, expr_idx):                                           return expr_idx

	def expr_idx_1         (self, expr_diffp_ics, expr_bcommas):                       return AST ('-idx', expr_diffp_ics, expr_bcommas.comma if expr_bcommas.is_comma else (expr_bcommas,))
	def expr_idx_2         (self, expr_abs):                                           return expr_abs

	def expr_abs_1         (self, LEFT, BAR1, expr_commas, RIGHT, BAR2):               return AST ('|', expr_commas) if not expr_commas.is_comma_empty else _raise (SyntaxError ('absolute value expecting an expression'))
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                            return AST ('|', expr_commas) if not expr_commas.is_comma_empty else _raise (SyntaxError ('absolute value expecting an expression'))
	def expr_abs_3         (self, expr_paren):                                         return expr_paren

	def expr_paren_1       (self, expr_pcommas):                                       return AST ('(', expr_pcommas)
	def expr_paren_2       (self, expr_bracket):                                       return expr_bracket
	def expr_pcommas_1     (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):           return expr_commas
	def expr_pcommas_2     (self, PARENL, expr_commas, PARENR):                        return expr_commas

	def expr_bracket_1     (self, expr_bcommas):                                       return AST ('[', expr_bcommas.comma if expr_bcommas.is_comma else (expr_bcommas,))
	def expr_bracket_2     (self, expr_ufunc_ics):                                     return expr_ufunc_ics
	def expr_bcommas_1     (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):           return expr_commas
	def expr_bcommas_2     (self, BRACKL, expr_commas, BRACKR):                        return expr_commas

	def expr_ufunc_ics_1   (self, expr_ufunc, expr_pcommas):                           return PopConfs (_expr_ufunc_ics (expr_ufunc, expr_pcommas))
	def expr_ufunc_ics_2   (self, expr_ufunc):                                         return expr_ufunc

	def expr_ufunc_1       (self, UFUNCPY, expr_pcommas):                              return _expr_ufunc (expr_pcommas, py = True)
	def expr_ufunc_2       (self, UFUNC, expr_var, expr_pcommas):                      return _expr_ufunc (expr_pcommas, name = expr_var.var)
	def expr_ufunc_3       (self, UFUNC, expr_pcommas):                                return _expr_ufunc (expr_pcommas)
	def expr_ufunc_4       (self, expr_varfunc):                                       return expr_varfunc

	def expr_varfunc_2     (self, expr_var, expr_intg):                                return PopConfs (_expr_varfunc (expr_var, expr_intg))
	def expr_varfunc_3     (self, expr_sym):                                           return expr_sym

	def expr_sym_1         (self, SYMPY, expr_pcommas):                                return _expr_sym (expr_pcommas, py = True)
	def expr_sym_2         (self, SYM, expr_var, expr_pcommas):                        return _expr_sym (expr_pcommas, name = expr_var.var)
	def expr_sym_3         (self, SYM, expr_pcommas):                                  return _expr_sym (expr_pcommas)
	def expr_sym_4         (self, expr_subs):                                          return expr_subs

	def expr_subs_1        (self, LEFTDOT, expr_commas, RIGHT, BAR, SUB, CURLYL, subsvars, CURLYR): return _expr_subs (expr_commas, subsvars)
	def expr_subs_2        (self, SLASHDOT, expr_commas, BAR, SUB, CURLYL, subsvars, CURLYR):       return _expr_subs (expr_commas, subsvars)
	def expr_subs_3        (self, expr_cases):                                         return expr_cases
	def subsvars_1         (self, SUBSTACK, CURLYL, subsvarss, CURLYR):                return subsvarss
	def subsvars_2         (self, expr_commas):                                        return expr_commas
	def subsvarss_1        (self, subsvarsv, DBLSLASH):                                return subsvarsv
	def subsvarss_2        (self, subsvarsv):                                          return subsvarsv
	def subsvarsv_1        (self, subsvarsv, DBLSLASH, expr_ass):                      return subsvarsv + (expr_ass,) if expr_ass.is_ass else _raise (SyntaxError ('expecting assignment'))
	def subsvarsv_2        (self, expr_ass):                                           return (expr_ass,) if expr_ass.is_ass else _raise (SyntaxError ('expecting assignment'))

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
	def expr_vec_2         (self, expr_frac):                                          return expr_frac

	def expr_frac_1        (self, FRAC, expr_binom1, expr_binom2):                     return _expr_diff (AST ('/', expr_binom1, expr_binom2))
	def expr_frac_2        (self, FRAC1, expr_binom):                                  return _expr_diff (AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_binom))
	def expr_frac_3        (self, FRAC2):                                              return _expr_diff (AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3)))
	def expr_frac_4        (self, expr_binom):                                         return expr_binom

	def expr_binom_1       (self, BINOM, expr_curly1, expr_curly2):                    return AST ('-func', 'binomial', (expr_curly1, expr_curly2))
	def expr_binom_2       (self, BINOM1, expr_curly):                                 return AST ('-func', 'binomial', (_ast_from_tok_digit_or_var (BINOM1), expr_curly))
	def expr_binom_3       (self, BINOM2):                                             return AST ('-func', 'binomial', (_ast_from_tok_digit_or_var (BINOM2), _ast_from_tok_digit_or_var (BINOM2, 3)))
	def expr_binom_4       (self, expr_curly):                                         return expr_curly

	def expr_curly_1       (self, LEFT, SLASHCURLYL, expr_commas, RIGHT, SLASHCURLYR): return _expr_curly (expr_commas, forceset = True)
	def expr_curly_2       (self, SLASHCURLYL, expr_commas, SLASHCURLYR):              return AST ('-set', expr_commas.comma) if expr_commas.is_comma else AST ('-set', (expr_commas,))
	def expr_curly_3       (self, SLASHCURLYL, expr_commas, CURLYR):                   return AST ('-set', expr_commas.comma) if expr_commas.is_comma else AST ('-set', (expr_commas,))
	def expr_curly_4       (self, CURLYL, expr_commas, CURLYR):                        return _expr_curly (expr_commas)
	def expr_curly_5       (self, expr_term):                                          return expr_term

	def expr_term_1        (self, expr_var):                                           return expr_var
	def expr_term_2        (self, expr_num):                                           return expr_num
	def expr_term_3        (self, STR):                                                return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1].replace ('\\}', '}')))
	def expr_term_4        (self, SUB):                                                return AST ('@', '_') # special cased for last expression variable
	def expr_term_5        (self, SLASHSUB):                                           return AST ('@', '_') # special cased for last expression variable
	def expr_term_6        (self, EMPTYSET):                                           return AST.SetEmpty

	def expr_var           (self, VAR):                                                return _expr_var (VAR)
	def expr_num           (self, NUM):                                                return _expr_num (NUM)

	def expr_sub_1         (self, WSUB, expr_frac):                                    return expr_frac
	def expr_sub_2         (self, WSUB1):                                              return _ast_from_tok_digit_or_var (WSUB1)

	def expr_super_1       (self, DBLSTAR, expr_neg_arg):                              expr_neg_arg.is_dblstar = True; return expr_neg_arg
	def expr_super_3       (self, CARET, expr_frac):                                   return expr_frac
	def expr_super_4       (self, CARET1):                                             return _ast_from_tok_digit_or_var (CARET1)

	def expr_neg_arg_1     (self, NOT, expr_neg_arg):                                  return AST ('-not', expr_neg_arg)
	def expr_neg_arg_2     (self, MINUS, expr_neg_arg):                                return _expr_neg (expr_neg_arg)
	def expr_neg_arg_3     (self, expr_diffp_ics):                                     return expr_diffp_ics

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
				self.tokens.insert (tokidx, Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

				if self.autocompleting:
					if sym not in self._AUTOCOMPLETE_CONTINUE:
						self.autocompleting = False
					elif self.autocomplete and self.autocomplete [-1] == ' \\right':
						self.autocomplete [-1] = self.autocomplete [-1] + self._AUTOCOMPLETE_CONTINUE [sym]
					else:
						self.autocomplete.append (self._AUTOCOMPLETE_CONTINUE [sym])

			else:
				self.tokens.insert (tokidx, Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, ('', '', '', '', '')))
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
		self.stack [-1] = State (s.idx, s.sym, s.pos, AST ('*', (s.red, AST.VarNull)))
		expr_vars       = set ()

		if self.autocompleting:
			reds = [s.red]

			while reds:
				ast = reds.pop ()

				if ast.is_var:
					if not (ast.is_differential or ast.is_part_any):
						expr_vars.add (ast.var)
				else:
					reds.extend (filter (lambda a: isinstance (a, tuple), ast))

		expr_vars = expr_vars - {'_'} - {ast.var for ast in AST.CONSTS}

		if len (expr_vars) == 1:
			self.autocomplete.append (f' d{expr_vars.pop ()}')
		else:
			self._mark_error ()

		return True

	def parse_getextrastate (self):
		return (self.autocomplete [:], self.autocompleting, self.erridx, self.has_error)

	def parse_setextrastate (self, state):
		self.autocomplete, self.autocompleting, self.erridx, self.has_error = state

	def parse_result (self, red, erridx, autocomplete):
		res             = (red is None, not self.rederr, -erridx if erridx is not None else float ('-inf'), len (autocomplete), self.parse_idx, (red, erridx, autocomplete, self.rederr))
		self.parse_idx += 1

		if self.parse_best is None or res < self.parse_best:
			self.parse_best = res

		if os.environ.get ('SYMPAD_DEBUG'):
			if self.parse_idx <= 32:
				print ('parse:', res [-1], file = sys.stderr)

			elif self.parse_idx == 33:
				sys.stdout.write ('... |')
				sys.stdout.flush ()

			else:
				sys.stdout.write ('\x08' + '\\|/-' [self.parse_idx & 3])
				sys.stdout.flush ()

		return False # for convenience

	def parse_error (self): # add tokens to continue parsing for autocomplete if syntax allows
		self.has_error = True

		if isinstance (self.rederr, Incomplete):
			return self.parse_result (self.rederr.red, self.tok.pos, [])
		if self.tok != '$end':
			return self.parse_result (None, self.pos, [])

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

		if pos and rule [1] [pos - 1] == 'expr_commas' and rule [0] not in {'expr_sum', 'expr_abs', 'expr_func', 'expr_subs', 'subsvars'}: # {'expr_abs', 'expr_ufunc', 'varass'}:
			return self._parse_autocomplete_expr_commas (rule, pos)

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_intg':
				return self._parse_autocomplete_expr_intg ()

			return self.parse_result (None, self.pos, []) if self.rederr else False

		return self._insert_symbol (rule [1] [pos])

	def parse_success (self, red):
		self.parse_result (red, self.erridx, self.autocomplete)

		if not self.has_error: # if no error or autocompletion occurred and all remaining conflicts are trivial reductions then clear conflict stack because parse is good
			if all (len (self.rules [-c [0]] [1]) == 1 for c in self.cstack):
				del self.cstack [:]

		return True # continue parsing if conflict branches remain to find best resolution

	def parse (self, text):
		def postprocess (res):
			return (_ast_mulexps_to_muls (res [0].no_curlys).flat,) + res [1:] if isinstance (res [0], AST) else res

		if not text.strip:
			return (AST.VarNull, 0, [])

		self.parse_idx      = 0
		self.parse_best     = None # (reduction, erridx, autocomplete)
		self.autocomplete   = []
		self.autocompleting = True
		self.erridx         = None
		self.has_error      = False

		if os.environ.get ('SYMPAD_DEBUG'):
			print (file = sys.stderr)

		LALR1.parse (self, text)

		res = self.parse_best [-1] if self.parse_best is not None else (None, 0, [], None)

		if os.environ.get ('SYMPAD_DEBUG'):
			if self.parse_idx >= 33:
				print (f'\x08total {self.parse_idx}', file = sys.stderr)
			elif self.parse_best is None:
				print (f'no parse', file = sys.stderr)

			print (file = sys.stderr)

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

	set_sp_user_funcs ({'N', 'O', 'S', 'beta', 'gamma', 'Gamma', 'Lambda', 'zeta'})
	# set_sp_user_vars ({'f': AST ('-ufunc', 'u', (('@', 'x'), ('@', 't')))})

	# a = p.parse (r"dsolve (y(x)'' + 11 y(x)' + 24 y(x), ics = {y(0): 0, y(x)'(0): -7})")

	a = p.parse (r"\sum_")
	print (a)


	# for v, k in sorted (((v, k) for k, v in p.reds.items ()), reverse = True):
	# 	print (f'{v} - {k}')


	# a = sym.ast2spt (a)
	# print (a)
