# Builds expression tree from text, nodes are nested AST tuples.

import ast as py_ast
from collections import OrderedDict
import os
import re
import sys

from lalr1 import Token, State, Incomplete, PopConfs, Reduce, LALR1 # , KeepConf # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

_SP_USER_FUNCS = set () # set of user funcs present {name, ...} - including hidden N and gamma and the like
_SP_USER_VARS  = {} # flattened user vars {name: ast, ...}

def _raise (exc):
	raise exc

def _FUNC_name (FUNC):
	if FUNC.grp [1]:
		return AST.Func.TEX2PY_TRIGHINV.get (FUNC.grp [1], FUNC.grp [1])

	else:
		func = (FUNC.grp [0] or FUNC.grp [2] or FUNC.text).replace ('\\', '')

		return f'{func}{FUNC.grp [3]}' if FUNC.grp [3] else func

def _ast_from_tok_digit_or_var (tok, i = 0, noerr = False):
	return AST ('#', tok.grp [i]) if tok.grp [i] else \
			AST ('@', AST.Var.ANY2PY.get (tok.grp [i + 2].replace (' ', ''), tok.grp [i + 1]) if tok.grp [i + 2] else tok.grp [i + 1])

def _ast_func_tuple_args (ast):
	ast = ast.strip_curly._strip_paren (1) # ast = ast._strip (1)

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

	def lhs_ufunc_py_explicitize (ast):
		return AST ('-ufunc', f'?{ast.ufunc}', *ast [2:]) if ast.is_ufunc_py else ast

	# start here
	if ast.is_ass: # if assigning to function call then is assignment to function instead, rewrite
		if can_be_ufunc (ast.lhs):
			ast = AST ('=', as_ufunc (ast.lhs), ast.rhs)
		elif ast.lhs.is_ufunc_py:
			ast = AST ('=', lhs_ufunc_py_explicitize (ast.lhs), ast.rhs)

	elif ast.is_comma: # tuple assignment? ('x, y = y, x' comes from parsing as ('x', 'y = y', 'x')) so rewrite
		vars = []
		itr  = iter (ast.comma)

		for c in itr:
			if c.op in {'@', '-ufunc'}:
				vars.append (lhs_ufunc_py_explicitize (c))
			elif can_be_ufunc (c):
				vars.append (as_ufunc (c))

			elif c.is_ass:
				t = (c.rhs,) + tuple (itr)
				v = lhs_ufunc_py_explicitize (c.lhs) if c.lhs.op in {'@', '-ufunc'} else as_ufunc (c.lhs) if can_be_ufunc (c.lhs) else c.lhs if allow_lexprs else None

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
		if arg.is_paren:
			diff = ast.diff._strip_paren (1)
			func = _SP_USER_VARS.get (diff.var, diff)
			args = arg.paren.comma if arg.paren.is_comma else (arg.paren,)

			if func.is_lamb:
				if len (args) == func.vars.len:
					return AST ('-subs', AST ('-diff', diff, ast.d, ast.dvs), tuple (filter (lambda va: va [1] != va [0], zip ((AST ('@', v) for v in func.vars), args))))

			if func.is_ufunc_applied and func.can_apply_argskw (arg.paren.as_ufunc_argskw):
				return AST ('-subs', AST ('-diff', diff, ast.d, ast.dvs), tuple (filter (lambda va: va [1] != va [0], zip (func.vars, args))))

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

def _expr_mul_imp (self, lhs, rhs):
	ast = AST.flatcat ('*', lhs, rhs)

	if rhs.is_differential and self.stack_has_sym ('INTG'):
		return Reduce (ast)
	elif rhs.is_abs and rhs.abs.is_mul and rhs.abs.mul [0].var == '_' and rhs.abs.mul [1].is_curly and self.stack_has_sym ('SLASHDOT'): # |_{...} - might be right hand side of subs
		return Reduce (ast) # ast
	else:
		return PopConfs (ast)

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
			return AST ('^', ast.base, neg (ast2)), dv

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

# def _expr_intg (expr, var, from_to = ()): # find differential for integration if present in ast and return integral ast
# 	if not var.is_differential:
# 		raise SyntaxError ('integral expecting differential')

# 	return AST ('-intg', expr, var, *from_to)

def _expr_diffp_ics (lhs, commas): # f (x)' * (0) -> \. f (x) |_{x = 0}
	if lhs.is_diffp:
		func = _SP_USER_VARS.get (lhs.diffp.var, lhs.diffp)
		args = commas.comma if commas.is_comma else (commas,)

		if func.is_lamb:
			if len (args) == func.vars.len:
				return AST ('-subs', lhs, tuple (filter (lambda va: va [1] != va [0], zip ((AST ('@', v) for v in func.vars), args))))

		elif func.is_ufunc_applied and func.can_apply_argskw (commas.as_ufunc_argskw): # more general than necessary since func only valid for ufuncs of one variable
			return AST ('-subs', lhs, tuple (filter (lambda va: va [1] != va [0], zip (func.vars, args))))

	return Reduce # raise SyntaxError ('cannot apply initial conditions to derivative of undefined function')

def _expr_func (iparm, *args): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	ast, wrapf = _ast_func_reorder (args [iparm])
	isfunc     = args [0] == '-func'
	fargs      = _ast_func_tuple_args (ast) if isfunc else ast._strip (1) if args [0] != '-sqrt' else ast.curly if ast.is_curly else ast._strip_paren (1)
	ast2       = AST (*(args [:iparm] + (fargs,) + args [iparm + 1:]))

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
		if lhs.is_ufunc_py:
			return PopConfs (AST ('-ufunc', lhs.ufunc_full, (commas.comma if commas.is_comma else (commas,)), lhs.kw, is_ufunc_py = lhs.is_ufunc_py))

		else:
			ast = lhs.apply_argskw (commas.as_ufunc_argskw)

			if ast:
				return PopConfs (ast)

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

	return AST ('-ufunc', name if py else f'?{name}', tuple (args), tuple (sorted (kw.items ())), is_ufunc_py = py)

def _expr_varfunc (self, var, rhs): # user_func *imp* (...) -> user_func (...)
	arg, wrapa = _ast_func_reorder (rhs)
	argsc      = arg.strip_curly

	if var.var in _SP_USER_FUNCS:
		if argsc.is_paren:
			return PopConfs (wrapa (AST ('-func', var.var, _ast_func_tuple_args (arg), src = AST ('*', (var, arg)))))

		elif var.var not in {'beta', 'Lambda'}: # special case beta and Lambda reject if they don't have two parenthesized args
			ast = wrapa (AST ('-func', var.var, (arg,), src = AST ('*', (var, arg))))

			return Reduce (ast) if rhs.is_differential and self.stack_has_sym ('INTG') else PopConfs (ast)

	elif argsc.strip_curly.is_paren and var.is_var_nonconst and not var.is_diff_or_part and argsc.paren.as_ufunc_argskw: # f (vars[, kws]) -> ('-ufunc', 'f', (vars)[, kws]) ... implicit undefined function
		ufunc = _SP_USER_VARS.get (var.var, AST.Null)

		if ufunc.op is None:
			return PopConfs (wrapa (AST ('-ufunc', var.var, *argsc.paren.as_ufunc_argskw)))

		elif ufunc.is_ufunc:
			if ufunc.is_ufunc_unapplied:
				ast = ufunc.apply_argskw (argsc.paren.as_ufunc_argskw)

				if ast:
					return PopConfs (wrapa (ast))

			elif ufunc.can_apply_argskw (argsc.paren.as_ufunc_argskw):
				return PopConfs (wrapa (AST ('-subs', var, tuple (filter (lambda va: va [1] != va [0], zip (ufunc.vars, argsc.paren.comma if argsc.paren.is_comma else (argsc.paren,)))))))

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
			b'eJztnXuv4zaS6L/MBaYPYAMWSVFS/5fX7A02r81j7g4aQdB5zCK4mSRIJ3NnMdjvfutJFfW0feQ+tg/R7mORoiiyWKyfSBXpF6/+9MV7n3706Sd/2v3pf/3w8/fwpcGPvvnsnc8/+OQjOEwHH33z7ufvvPfveJgOvvrzV5+899lf9Qi+P/n0S/j7l3c+h79f' \
			b'/PVjOgffdP37dO6Lj9754n/z4bsf/Ns3773zxQdfyPHH72jsu/3hX/rDz/iQckhl+DMcyFcl3w6+P/7wk68o3w8/+fRj/a70wFGBKKP3vvr8o79iRukgj/7iS6rLV+/qGT784OPPvvzrFx9geT785Mt/w6p/RdX88GNKTn//43M8/xGJ9FNMI1ICWZKE+O97' \
			b'n3788Tvw/TlL/XOV+ucURxX9XKUucXwdFpEj+iJ/nlUAQx/8B/x55+PP4O/7735E5zD2k/dF3nj0bn/4l/5Q5P3BR198gGX6/MOP8fuD/3wP5fLOlyQYzPJLLg6U+Uv9Rkm//+FfPnwfr3hPWp7TffYRNQzITtvoP7/44D1K8P6Hf/4zKtMnH5IavkeFfueT' \
			b'91HIeOJTvP7jdz774stPpYiqPhTxf7hp8KviNoNbvvfvcPjmj2/f/OP1b2/+YY7fwPF3r3/74fdvfvntm++//enN769/M6fh8Id//gpnfvzH3/X45x/+65vXv/2XBt/88esPv/WBb+Hw769//+a7X36So99++X/9Ed/vzQ9v3nyXjn5NR5rN62/T4Y/f/zPF' \
			b'/v57utHfXn/3ux7/Sjfg6D9+/q4v89/+9msW+ObH7970JU0V+unHvm597O8//JaO//7HT9/8+PeU2Xd//PbTfxvR6OG3P/78ixVTKtVvr7+zWcGBBv/xQzrz+vvvU6LXqXL/fPNDX1OSUqoB1skIPp344+cff/k5nfjvVKIff/49Fem7vjbQzlZs/3idhPzz' \
			b'L+nOf9gkr3/+Pou3cv32u1/+/vfXKfhLyuxbEML//aFvtDzdrz/+8N0PKQAK+XMvi1/f/P5LunVSklSTX37qa0uZZoE35spvfvrH6596+fGVX+9evdhHt4v1w44PIh7UFf5xuzo+SBBCdOQx2a6ud3s5pREccnodXOA1Cg8p1b6hmMPuRfC7vd/Vh4cUETAi' \
			b'BI3Yd3jgD/yngQJ492CjXBhFNc5G4SEcVZH/NM1uX7UPEoWHcNTA/3ZXQ1Z8psED+MaM8Du0+MfvIqSoqoc8SoP7QGWtwu5FTZWQu0A4UrjjItW7Fw4TNPi/j4o26Bo5wDjMBEpShXREreSg1BWkgFZpuUwQs3dUCFfxnwZydVxCCOEhipUaAdvjwQT12MRz' \
			b'U2MTYw3pf6j1dMADLKTEc9FBChLJYSija6mNXR/RUUSVIqiVdqIoJiKl2HuqVQj8J3JeqCuByhC8BLVxsBxckMh/IhQispp5lDQ1bwSFQf2RE/GgJ0IjjctFgiA0MF0LN0JBUstIlTHK2aDzcoBxeDlI1UOda1aAFGyHUaImWXQ4jIP5haEaBydSNHmUGwez' \
			b'i/YhmpL1XUMKMYiohhHORnTSJFXQMHRt0kmwEyhKKhyqCTdEih5H9cF9qCgz0HTQENSpqtu1EA9WCFtI7jVxGu0bWJIjUoFy5Kn2gfoE9n1Id9C+AOWsuEIddn40LFB9qJXYAIxOkX1MwzEmTcsxXR/TUYxoKPUcqrZ3/Cd2qXga1RxsFB7iUct/QHIPD/0h' \
			b'HgXuBHoJHrLxh9v3uoghTNYHoUnJILWUTG0q5ssNc9hxPpXnPw2mYlpUng5Jithn5YANNbYFdQRJC2GGAkuuOkh22KN3sVIty+I1BiKoLFE0UGQNYejUlIb+Q0IWC9pIEnTkPw3c2Un7RDrEuoN1aLGIQrZm15KMwaq/qARoOxA9tlas1IzRWaHb5Nk9G/2A' \
			b'mt6qLtaBLaF0BlFEp8KHyBex7lsFg7EvWbuLlKeDJgA5qnmkoKP8R1EpCEUifaBy6FE4yJFoIRw4PfB6wJwCITUpPwy12Q01JoX2jvKuagnqGahdxZUI/KdBUXELo0I6VrJuJz3wwCFVdIdty0WDtnYHS+KKJIWJWv7T+N7CsO1BKUb+Yx52ojCxrvkPPefI' \
			b'uZoO8SjoyQcJQkhPMHCgRG3NmpBwhxrNz0n0SBX0eghC6IHj5AQ+SUkMHMFD3KvDroK2q0AwgKlAvAZlB4UB7QcLB4oFLQRdE2wZSKzbgUA6OHS7CnSzAmFX0IMrlCacqcBmVdAWICiPKfA/4A1KDPGgkxU81MFpvAIQWQX8hitB+6sDfEP/q2pMCTnUYAzg' \
			b'CPKHUlRQjArKUQVMAcUFiVQghQq4X8HNKrhFBfcAhII5qoDLFUil87su7Lp618Vd1+w6zGOHpSaDW4GyV2CVOlQELEC1w8dYemaDHlIdIOEBH6x2jjoX3ArbFEw0WmmkLhQb63SAOh0wYzgGuVUBj+FikGQFooSO34YdtFqLsoFHL+j97a6FG2PZIT0UGk04' \
			b'tDswEG4PNqrBxw+w1A09wcLjKehZQ4rc0AMpmKyGcFI5rDwU+4CGDQ6gLaEp2wqZhOLE0/isDocP2GGhbNDsL7C9MQIvf4DTgYNY5AeCMaXCmuBZbIEHMjJ0tqKzrxDzFKa8i67cia686LjRK25dbClq7a4SFWLdwFbFYBXku5bLqlYiOkkvqicXYoqIMcXW' \
			b'3Kf+YAM3pYHvt4FfeLYE3mmP99zDG+ngjinS+aIF96sFr3ACqrTvHbcvSR/7dU0dXRrqa5p04I4fmuwExgj8A8Gf2sKcraOcpYxtLd9+DY0yWgUcKN5Q5UTVJpXMKBcr1YQyiQJZrbHaMtSTGf0AncBmqA/SDgeWtvQH7Qeq86znquFWn40eq+6yvqqCliZ6' \
			b'VBMhG/np19cy7joIK+tGhlbSJWodmNX6HO1HnUvGX5Ufd64XVVBlqOWB3NX6vO26Yqjv11C/qHjwDoP4trTz/bYzGoBDaeC7buCqtO/9tu+Lystsa+WE+lEn1zw9FvgdZL9rd/Uulna+3Xb2wmN63KYHNhn2yKOeTqhSuIr4bA5Sh0JUEeWJAoP8QDhFB25V' \
			b'B6B169K6d9y6sbTuHbduU1r3Xlv3Raezl/wM1slryoM+ilFtH8qE2IUmxOoySXHPvQsryv1JxjqRXh6cozA0v4kT3VGmRKN/fFb6aH7gd5T0RoJeZvEr61Pz8zLr6tqzLnfia8GzwS+ohcuLkUcbmVD8D+7YxkD7so2py3ToHTfzC339TN6I+K3TKLV8Rzae' \
			b'Lce3PL3S8rgb7TkaZRQtvnzDhilvPt+aDX7RygxnJY8BLROu5VeYbSdOhAeZIHP60lPamP1SX0Q+71gDnDQ0nbMtS3JBwyDvPmuBu8v9FmpxZ41ctshFilykhsd8Bzh3QDXIdac09wpyI5vkhhusaYswHyHMhrW/YbVvWO2bbkmmavCKbNdkyyaiYRPRHoqi' \
			b'nm/kGzHyYp/ldYcsLWjVppentDt+SntFa0rcQ1k9dM9tDAVyvC7IlZU+d9SuuISZF3aVdr2fdsWFeU6WcMF3acBba0BabFd65D01KLaSk2WR2CdLU95wU9JjkAi/LLq4tlEpFpy7WiMYpO/SUlfXUq7mBupoBFkcIu/YbOJqUeqUdcXfQTtnIDDalUydpJQr' \
			b'5PXPQR5qPSlN6b9P339f0bI1bIzSCE+IO689yQ97UhoHsqEtzfMUzePYnAV5/scdKOnhRJomUrg0yVtsEu+FJAQWeR/EL6Rb8cfi9xnqEUrpS7NcnCahyPntULvI+S2YmS6oiZfXpOJwQoMaNixRXJnISRZhwS6uuHiIBkT8BNwJ4LuOx7GlsS7RKQ6HIt2L' \
			b'PQQdgozpWlblSFNoj3Llll1k0CucsuThItwAPdBLu23TKxyZntP92uVh9+D42VcMmIzsa+xpX7Pnpss8+SgylAfit93MbS2Dk8mFyhUvjnjsrfqe61p19wxD96vSVGucoq2ENmwM3oGIPHQde+g69tClWbaa7+lSiHxzHfvmUqd23MfZC6iffGhlgMubARbX' \
			b'oDud1q0Z7DUrQYyCd3njUvr18Q7U3O/Kpor33F1e4TKD4pJzky1H1qwYtRMH1aNVNUVmqzJrH7EGChfiEIKbQ0HwqUtD2mKbb9E243op1nlXdP5UnfdFZKeKrHhV36iZkBcyTV10/tQJwkPR+ZvU+UrcTeC05xVc+IUTCg/0W4H4Bc3q9ad7vPio+wd1dfb9' \
			b'T3uQa60X11qJxy9oBC9+nP5BXnyyyx8lCi2f9jWHZa9zdh/zZq9ycmHy6rHkzQ6p5Ebj2Y3GixsNF0TSRwlPzWCjwwcXgGRBI/CyxeotqzV66NB8Y1lLcdvNWInF6Iab8IWZ+HoqHi2OV1cLJy4W5PDoitv4rWsIuwqUJrzVJkRnJs/OTJ6dmaQHe+nBXhxD' \
			b'8Dvy80YduT/zZpHFp2PTZ/m0Q6Mrmw1usIaJ9TnIF6t1fWD9bQlvxZflrQ5Vw8JIoGKHJvI84W9ZgtZy+7VshloeAJHjg+fJd887hlGzRk5FS5q+pq3D2JbJw8eB79GwaWs4ccNZNPzA07CeNGwaWzGCh34cFspo+/ZQRyPg8CDPozJqDTJcDTT0JOugD6ui' \
			b'qb33r9BPnCRbLxdPemVBBQNrbGCNDeUp6ZZVB+8UiuvH/TZw5J7Ks2Jl9vmUBf0gowf6QeH6QX7QsMbRPZQDZFR6zL32GJRUaehn0NBw15qfZWp+lsFW3zl5Ase4yKcq2WAWxRvp2UkGs1D/KM/xsaziudTQqiWhtyh7bBv2SFJffkeSt4s5qJkaftZlf3Lc' \
			b'2Ra3tcU9bXEn1tJjb7LHUn9rUBUa/mr5S1sbitGUXnihp6HYyfhRtomuZJ9o6lTUL3mPY+qvbWmGSxnDrgj3cnuaOBQu6XpQXXei48iRwo3b5AbcsWNQdNKa7Ghy2L064BMf/QQu+mbgz+B2RqNZYNxknd4gklRIJNzSKPdIA4MORwg4YIgoJ64Riw11lEUc' \
			b'pI7D2nHVOik9yk3lxBpnG5O8tUlnqqRnrJENayO1hOh26mq16IY3O5xF2fGMxzoV7q2Ov0mBwsWfNsFfzsCfzcDWgmJUqPmgWBVumoa/NYq/SInlAe1yuJQd1Mjh8lvQCIerr1GFcGIat9FCpyDcgAY33MDNIHDDPNwkD3qOw9V9KF6UL7Sgw06DgkZJ41Y2' \
			b'uH8NCNuhQcGNVHACHXcgws2HQPMc7hGN20VDnR3U2eHaX9z7Btf+4sJf3P8LV4vhzlG4eAyXb+Pbelwyhmug8EERHfVwGTBoqsNlibgPAr4wPBxAV/aQK1R6X0Hp9lDaPdxpD429D3h82O07iD7geTiE/9gaezQQe7QMeyj73lM0XIJ2YA8qtcdOs8e22WPn' \
			b'32M/2mP334M67bG99tjl99jf99ip9tjb99jV9x5DoFH7DvOh5B3mADHQrvuIp0H4exDcHgS4x1xrvDjgvbHgqB97VJB9i5dXmBfeDMS7x1uDqPYNnoF22eOdsOagmSiJPRYGZL/3eFPOt8E/FIwsBlTQPdqvfUXJDkFqDMLfOyw2aMq+xVJQfVGqEYsLp6ET' \
			b'7LHWKKmIJ0Hh99BIe+gy+4baAWUPZyl/ONFhIfCgonuTSCo8B/9Bm/YoNDS5e483xMqhWd2j7dxjNNYfu8fe0ylMjOkgY/ju8BsyAFXfd1QXahYsE9wMK4zSB2XdoxhQCtioLbUY/cECYFXgbIOFOlCdMATpwJ7twQ7sG5Q41hFSt6QPkA+ca70UH3UGet8+' \
			b'UsFJungbkjCKEtN2X6OJQ8NWzFoxa8eYtWLTik27AZvm0KbN2TJ+pk0WDbvkEXbNzOPy5O7QxtWzZm76CXXV2A2eybuNTV4zMHtubPruzeThBjzJ7MWB6YP0OIRbNIENNkazYuwaTGENHkWcY/QaNnuN5DBr/JpjzB/lsY0JbLRI0CWaixnAJjOBzYQRvHPb' \
			b'h3cX+9fkFpCEv2wFd/+KLxHOzUvEcwcB3/4PLqw40zQGmZywo/zeRgaZhpi1lLUYSzsfIIYznG476ynzOTWdNW1K27GTWzTW9TBhYfupqmwWB2dTdGYFZyhw1iXNbqglbow1DmyRaRqrPdIyD95I4A/DqaXGnzHEn90jiw3pcC4Df22UHlwhHc6kbGrF4TzO' \
			b'Uw2tOf52BA0P1qx6O2PZg1j3+EgLXw+sfL1s6XGlJFn72lh8OI8LhHCLQ7L+rSEAWgVs4HoFAqgwdY4BjqIErQ2QXszSQFMpEzgQbAbKBbqhoCGdppIyJtINl1DRXzXDCjw1wkXFtMjuOkWOLIHvsnAqntCEazoESqq0JJjMhM5Y3GCEEocqQM3UShYGPnSS' \
			b'29fAZ5w3k0hrauSNYNL6XQBPqfoZpLSd11Al6QawojrTmKJ5NLSUmsItIzJBlwSjyJ41LiHMarW0lOKMQebcS3qUcgA0bNwI0dBdWoiua8EcmtKXezI/3Uuks8NULv4P7aVc8FfwV/B3Lv4i4y+u4S9Smgx/UWNRg/pAfeDvGfxJqoS/KPjrM0j4MyOjdJpK' \
			b'KvjTGy7iL6Wbw9/UaInS+/yuk/izCXyXhVPxFH9xEn9aaUkwmQmdyfAXDf6iwV8c4i8y/mKOv1Hegj+pqZE34U/qdwn8afVz/Ek7r+KP0w3xFzfEX8zx14tM8cfBKLJnjevxZ7RaWmpb/NWPmhgbg+9OkLeEu4K654k6hBsWbO3dBn8y1EmUTvnxscStzflR' \
			b'ohB2fc4JcHQbAVw6TeVjwKXbLgGuv2oGcHjKAg61VGcDs7tOAS5L4LssnIo3P1uYaixzhuPL6bRFG0Yo2qjogjbOZ2Jakares22QOdU2ppI0RtKINq3ZBdCW6p6hTVt4DW2SboA2d9gObS6fkTTNIWiTYBTZs64ltFl9lpYaoG2AtOolPVop0xo8fWinoBYL' \
			b'1ArUCtSOglrFUKvWoMZpMqhxVIKavMWi71WoVQK1KmWToFYZqJlPgpredhFq6ao5qFU51CipzFninozp+kmo2WL5Lgun4i1ATWusUBtdTqczqFUGapWBWjUHtdxfYCL/mArS2OgmpIpdgmla9Zxp0sCrTON0Q6ZVGzKtypnWt4YyTYQnomdV65lm1Fkaaium' \
			b'NYVphWmFaUcxLTDTwhrTAqXJmMZRiWlBmBaOYZo4pbmQsklMC4ZpNoUyTW+7yLR01RzTwoLfRnbbSajZBL7Lwql8C1DTKivURpfT6QxqwUAtGKiFOaiFHGqjzHkWUitpZE1Yk6pdAmta+Rxr0sarWON0Q6yFDbEWcqz1IlOscTCK8FnbeqwZjZamWsSa4GyC' \
			b'Ym2hWKFYodhRFGPHErfmWIKVHjiWSFSimDiVuHmnEkMxcSfhPJx1J3HGnSSddr07SbrtIsXSVXMUm3InSRSzt52kmE3guyycyrdAMa2yUmx0uRt6kjjjSeKMJ4kbepIkiuWuJOPMhWJSSSNrophU7RIU08rnFJM2XqUYpxtSbENXEpe7khiRKcU4GEX4rG09' \
			b'xYxGS1OdSbHuKij2eP/yi/Frxf382TJpzoV9AxYdy6ERg0bcaZk77Rp3WkqTcYejxp7tFLtKnlbI06aMEnlaQ57WpFDytGvYwQ4t15zs8s561/+fBo8tFpKjHX62cItHF41mdnjU5k4ajcoyFTz5afApctSQcxTsDy/CF23VnC/Skmt8mfeq3wItbY+VJLKe' \
			b'K1xE9a/nShgXe4wYsETh0UOjOpxJjQU3w018DGmrYl4Fb1fx3+5oKAxGRO3EqCj2FMLNhWXbA919/fkQ6dZHSZ5XnOLXIq2wt/icVhKltErBA39P44pOKbE4EORSXiskxKKbCbHSaSolEyvdTaCFgcjZK7ooCy4M9vuUwwy/8NQswrIiTOErS+C7LJzKOo+v' \
			b'VH2B2PhyOn1QmTHcJFoRRzUQEbu+QXwvrQHwqII98Ma3Y9pptU1LIOq0shcgXSp6RjrVgDXSqVhy1pF0NsIdFaMfSZkSC/EkGFuReyf1YejZGkqznTmSqqqrGEqVCcGCuutHHb/W8muvtXDxyeC1lkQl1MlrLX/May0vr7V8SNkkyJnXWt6mUMjpbZdGZv1V' \
			b'c2Bbeq2V3XYSbDaB77JwKt8C2LTKCrbR5X74Wsub11revNbyc+M2n7/WGmcuGJNKGlkTxqRql8CYVj7HmLTxKsY43RBjG77W8vlrLSMyxRgHowifta3HmNFoaapzMfa4/SUKxgrGng/G+L2WX3uvhZMbg/daEpUwJu+1/DHvtby81+I8vH2v5c17rXTa9++1' \
			b'0m0XMZaumsPY0nut7LaTGLMJfJeFU/kWMKZVVoyNLvfD91revNfy5r2Wn3uv5fP3WuPMBWNSSSNrwphU7RIY08rnGJM2XsUYpxtibMP3Wj5/r2VEphjjYBThs7b1GDMaLU11LsbO3QukYKxg7LlhjF+T+bXXZKj9g9dkEpUw1grGjnlJ5uUlGefh7Usyb16S' \
			b'pdO+f0mWbruIsXTVHMbaJYzZ205izCbwXRZO5VvAmFZZMTa6nE5nGGsNxlqDsXYOY/lbtHHmgjGppJE1YUyqdgmMaaFzjEkbr2KM0w0x1m6IsTbHWC8yxRgHo8SytvUYMxotTXUuxs7d06NgrGDsmWEs8PqvsLb+S9JYjEmUYkx9PcIx67+CrP/iPIJd/xXM' \
			b'+q9gPoqxdNsljPVXzWAsVAsYy247hbEsge+ycCrfPMZSlQVj48vDcAFYMAvAglkAFuYWgIV8Adg4c8aYVjKrcUhVuwDGUuUzjGkbr2FM0g0wFjZcAhbyJWBGZIIxCUYRPmtbwpjVaGmqczFW9uYoGCsYOw5jPKkY1iYVUdEHk4oSlTAmk4rhmEnFIJOKnEew' \
			b'k4rBTCqm06GfVEy3XcRYumoOY0uTitltJzFmE/guC6fyLWBMq6wYG10ehpOKwUwqBjOpGOYmFUM+qTjOXDAmlTSyJoxJ1S6BMa18jjFp41WMcbohxjacVAz5pKIRmWKMg1GEz9rWY8xotDTVuRgru3EUjBWMHYcxnlQMa5OKqN+DSUVUrmBmFYPMKoZjZhWD' \
			b'zCpyvsHOKgYzq5hOh35WUdMvcyxdNcexpVnF7LaTHLMJfJeFU/kWOKZVVo6NLg/DWcVgZhWDmVUMc7OKIZ9VHGcuHJNKGlkTx6Rql+CYFjrnmLTxKsc43ZBjG84qhnxW0YhMOcbBKLGsbT3HjEZLU53LsbIDR+FY4dhxHOuYY90axzpKkw3HOCphrBOMdcdg' \
			b'rBOMdSmbhLHOYKwzKRRjettFjKWr5jDWLWHMZjCJMZvAd1k4lW8BY1plxdh0DhnGOoOxzmCsm8NYl2NslLlgTCppZE0Yk6pdAmNa+Rxj0sarGON0Q4x1G2KsyzHWi0wxxsEowndaH8GYaV5pqnMxVrbgKBgrGDsKY7jCFAqGX4sYq+mTYUyiFGN8LHFrGKNE' \
			b'IUgeFFKM0W0EY+k0lY8xlm67hLH+qhmM0craOYxlt53CWJbAd1k4lW8eY6nKgrHx5XTaYgwjFGNUdsEY5zOBMap7j7Fx5owxraSRNWJMq3YBjKXKZxjTNl7DmKQbYGzLddJUjB5jRmSCMQlGET5rW8KY1WhpqnMxdh17cBSMFYxdP8bYx6Ne8/GoOU2GMY5K' \
			b'GBMfj/oYH49afDw4j9r6eNTGx6M2n4Qxve0ixtJVcxhb8vHIbjuJMZvAd1k4lW8BY1plxdjo8nro41EbH4/a+HjUcz4ede7jMc5cMCaVzGocUtUugTGtfI4xaeNVjHG6IcY29PGocx8PIzLFGAejCJ+1rceY0WhpqjMx5s7dFKRgrGDsuWGMfTzqNR8PVOWB' \
			b'j4dEJYyJj0d9jI9HLT4enEdtfTxq4+ORTte9j0e67SLG0lVzGFvy8chuO4kxm8B3WTiVbwFjWmXF2OjyeujjURsfj9r4eNRzPh517uMxzlwwJpU0siaMSdUugTGtfI4xaeNVjHG6IcY29PGocx8PIzLFGAejCJ+1rceY0WhpqnMxVrbxeOsYm9rBquDshnDG' \
			b'vh71mq8H7s828PWQqIQzcfWoj3H1qMXVg/OoratHbVw90um6d/VIt13EWbpqDmdLrh7ZbSdxZhP4Lgun8i3gTKusOBtdXg9dPWrj6lGzqwelcUaAU1DLHT7GtxCoSVWNxAlqUsFLQE0LnUNNWnoVapxuCLUNHT7q3OHDiEyhxsEosaxzPdRMs0iDnQu1sqlH' \
			b'gVqB2klQi/zGLK69MYv0yaAmUQq1KG/M4jFvzKK8MYsp5wS1aN6YpdOxf2OWbrsEtf6qGajFpTdm2W2noJYl8F0WTuWbh1qqskBtfHkcvjGL5o1Z5DdmlMa1fW4TUIv5e7PxLRhqWlUjcYSaVvACUEuFzqCmLb0GNUk3gFrc8L1ZzN+bGZEJ1CQYRfFZ5xLU' \
			b'rF5Lg50LtbLFR4FagdppUOP3Z3Ht/VnkNBnUOCpBTd6fxWPen0V5f8Z5RPv+LJr3Z/aToKa3XYRaumoOakvvz7LbTkLNJvDdblDUuPL+LFVZoTa6PA7fn0Xz/izy+zNK49o+tymo5W/RxrcQqElVs3pr61wGalroHGrS0qtQ43RDqG34Fi3mb9GMyBRqHIyi' \
			b'+KxzPdSMXkuDnQu1suFHeYv2jGEGYfr5D3fqFGTgKciwNgUZKE02BclR4596odjVScjAaKtDyihNQgZCG4Zrm0DnIPW+S2RDayEJ5yYhwwLaWEH7/9MTkbZwOJMYhp/liUittk5Eji6n09kPjTk7E8ki2vMvwsy+WQuDX4SpJedUtf4XYegU/yJM3QdDOtyQ' \
			b'cFRy3yvRYCpSGnwNcCSPiR+F6UWzwWRkSIjrNZIFp7ORXFqcjcSuhwWFezHtuHIyL2lU3bH+5bQL8IXPc/pb0HX9Ep9gwHK9pCcCMC8vEd1gFl7S79QY/l3fTiGDH5W5ZQoOf06mDO+un4gnDe88D+/82vDOU5pseMdRaXjnmYH0vTq888zA2GeThnfeDO+8' \
			b'SaHDO72tQBAD+ItNfmKQl66dG+T5pUGevfnkIM8m8F0WTqVcGORpxXWQN7qcTh9UWjLO82ac53mc5xmFKcOpcZ7Px3mju8g4T2prRE/jPKnjJcZ5WugMg9rkq+M8EchgnOc3HOf5fJzXl1jHeRyM0gNY7fpxnqmhNNi547zr20qkcK5w7lY4x/6Tcc1/Ekky' \
			b'8J+UqMQ58Z+Mx/hPRvGf5Dyi9Z+Mxn8ynY69/2S6rXKuZs5NTWama+c4t+RFmd18knM2ge+ycCrlAue04sq50eVRvChZWsI540gZ2ZEyii9lynCKc7k75fguwjmprRE9cU7qeAnOaaFzzkmTr3KO0w05t6E7ZczdKY3IlHOie9IDWO16zhkFlwY7l3PXt9VI' \
			b'4Vzh3K1wLjLn4hrnIqXJOMdRiXNROBeP4VwUzsWUTeJcNJyLJoVyTm+rnIvMuTjBuZR6jnNxiXP25pOcswl8l4VTKRc4pxVXzo0up9MHlZZwLhrOReZcFM5phlOciznnRncRzkltjeiJc1LHS3BOC51zTpp8lXOcbsi5uCHnYs65XmTKOQ5G6QGsdj3njIJL' \
			b'g53Luevbi6T8GHYh3u0Rj5cSxLWlBKi/g6UEEpWIJ0sJ4jFLCaIsJeA8ol1KEM1SgnQ69ksJ0m2VeC0Tr+2JR1lwSdAApRzmuLe0rCArwiT3bALfZeFU1gXuafWVe6PLoywriPquNCbZJ/Tx4oIoiwtSnlPoyxcXjG8k6JMKmzYg9Ek1L4E+LXSOPmn7VfSJ' \
			b'QAbo23BxQcwXFxiRKfo4qLGseT36TLNIg52Lvuvbv+Qx6GuJfocCwALABQCCjF3dngDC5py9J3kJQlhbghDok+89yVFp70lZghCOWYIQZAlCSDn3e0+aJQjpdOiXIKTbCgwxAKKhL4EhZcHJXGdymIFhMMsRqshArNDIZvtR2qJM7kdpE/guC6cyz0MxiUGg' \
			b'OL48yLIElh1DUaLTrpS8OCHI4oSU5wQUQ744YXwjhqJW2LQF7U0p1bwAFFOhMyiqDqxBUQWSQzFsuDgh8OIE7Xppj8pedLpHJQexq6Y26aRuDEir/dJ4ZwLSX9/OKGVsWNB4e2PDjseG3drYsKM02diQo9LYsGMc0vfq2LBjHHIeFEpjw86MDTuTQseGelsd' \
			b'G3Y8NuzM2LDjsWHHY8OUw9zYsFsaG9oMJseGNoHvsnAq68LYUKuvY8PpHA4qMxkbcnQaG3Y8NuwYgynPqbFhl48NRzeSsaFU2LQBjQ2lmpcYG2qhMwxq26+ODUUgg7Fht+HYsMvHhr3IdGzIwShdwWl9ZGxomloa7Fz0Xd9uKgV9BX03hz7s54FUchl9qLMu' \
			b'R59EKfr4+MDfa+ijRCFIHhRS9NFtBH3pNJWP0ZduK+jDAIiFvgR9lAWXBBqnz2EGfXhqFn1ZEabQlyXwXRZOZZ1HX6q+oG98OZ0+qMwYfRKt6KMacL0RfSnPCfSRHHr0jW/E6NMKmzZA9Gk1L4C+VOgMfdr2a+hTgeToI7lshD4qRo8+IzJBnwSjdAXWvIQ+' \
			b'q+nSYOei7/r2XCnouwH0RcFfWxCYIdDz6M+vjf4ggR+M/iRKEehl9OePGf15Gf1xHt6O/rwZ/aXTvh/9pdsKAj2P/rwZ/Xke/Xke/fU5zCDQL43+siJMITBLYAOmbgsITNUXBM7kcFCZMQIlWhHoefTnZfSX8pxAoM9Hf+MbMQK1wqYNEIFazccjEOf6EYOu' \
			b'HqAwFT5DoerAGgpVMDkK/YajQJ+PAo3oBIUSjNIlnNaHUWg1XhruXBRe304tBYU3gMIyChyMAnl5X7O2vA8VdrC8T6LSKFCW9zXHLO9rZHlf02eTRoFmeV863fTL+9JtdRTIy/sas7yPsuCS4LN4ymFuFLi0yC8rwuQo0CbwXRZOZV0YBWr1dRQ4uryRRX6N' \
			b'WeQn0WkUyOv8Glnnl/KcGgXm6/zGN5JRoFTYtAGNAqWalxgFaqEz9Gnbr44CRSCDUeCG6/yafJ2fEZmOAjkYpSuw5vWjQFNDabBz0Xd9+7kU9BX03R76eH+XZm1/F9TWwf4uEpXQFwR9x+zu0sjuLk1I2ST0BYM+m0LRp7dV9AVGXzDoC4y+wOhLOcyhb2mn' \
			b'l6wIk+izCXyXhVNZF9Cn1Vf0jS5vZJeXxmz0ItEJfYHRFwR9mucU+vL9XsY3EvRJhU0b7E01L4E+LXSOPmn7VfSJQAboCxuiL+To60Wm6ONglK7Amtejz2i6NNi56Lu+rVwes5XZtW5fdhTKFGOKL0WXIuvWcHXVqKoZVfUaqmpKk6GKoxKqakFVfQyqakFV' \
			b'nbJJqKoNqmqTQlGltxVUTe5E1l81h6d6AU/TSLJl8V0WTmVaQJJWU5E0upy3BbM8qg2M6h3/oM8kfuocP5qXUKdm5NQMm/pCpNH65aSRplslDacbkqYW0jwSMnUOGbmXWXgnUVG0mBWop4xRUmmJEyhDdLn6DVTKwKoMrG5gYNUwrZo1WjWUJqMVRyVaNUKr' \
			b'5hhaNUKrJmWTaNUYWjUmhdJKb6sDq4YHVo0ZWDU8sGqYXCmHOXI1SwMrW4RJitkEvsvCqawLFNPqK8VGl7NlVpkJyDg6sazhgRWmcG2f5xTZmpxsoxsJ4qTCpg2IdVLNS+BOC53jTtp+FXcikAHumg0HVk3OvF5kijwORukKrHk98oymS4OdO7C6vj1VysCq' \
			b'DKwuj6qWUdWuoaqlNBmqOCqhqhVUtcegqhVUtSmbhKrWoKo1KRRVeqvFgVW6ag5P7ckDK1sW32XhVKYFJGk1FUmjy+l0NrBqDYzapYFVm+NH8xLqtIyclmHTXog0Wr+cNNJ0q6ThdEPStNsMrNocMnIvO7DiqCh1YAXqKWOUVFri1IHV9e1kUuhS6HJxumAH' \
			b'hILh1yJdWvpkdJEopQsfS9waXShRCJIHhZQudBuhSzpN5WO6pNsu0aW/aoYueOo0umRl8V0WTmWap0uqptBlfDnbQkMXjFC6UHnn6NLmC6dTXkyXlhdLt7xMur3QGulUv4wu2nRrdJF0A7q0h03o0h4yuui9DF0kKooWswIlulgllZY4lS7Xt1lI+X2bMjV3' \
			b'nURin4d2zecBtXDg8yBRiUji89Ae4/PQis9DG1I2iUjG56G1KZRIettFIqWr5oi05OeQ3XaSTjaB77JwKt8CnbTKSqfR5W0Y0sl4OLRB6ORE6pOUyn0bxpkLrqSSRtbELanaJdCllc/RJW28ii5ON0TXhr4Nbe7bYESm+OJgFOGztvX4MhotTXXmFFy4vi09' \
			b'CsYKxq4TY+wP0a75Q6AKDvwhJCphTPwh2mP8IVrxh+A8WusP0Rp/iHS67f0h0m0XMZaumsPYkj9EdttJjNkEvsvCqXwLGNMqK8ZGl7dD34jW+Ea0tcHY7GAr95EYZy4Yk0oaWRPGpGqXwJhWPseYtPEqxjjdEGP1hhjLvSeMyBRjHIwifNa2HmNGo6WpzsXY' \
			b'9W3PUTBWMHadGIuMsbiGsUhpMoxxVMJYFIzFYzAWBWMxZZMwFg3GokmhGNPbLmIspZvDWFzCmL3tJMZsAt9l4VS+BYxplRVjo8vpdIaxaDAWDcbiHMZijrFR5oIxqaSRNWFMqnYJjGnlc4xJG69ijNMNMRY3xFjMMdaLTDHGwSjCZ23rMWY0WprqXIxd31Yb' \
			b'BWMFY9eJMfb3a9f8/VD5Bv5+EpUwJv5+7TH+fq34+3EerfX3a42/Xzrd9v5+6baLGEtXzWFsyccvu+0kxmwC32XhVL4FjGmVFWOjy9tmiDHj3dc2BmNzfn1t7tc3zlwwJpU0siaMSdUugTGtfI4xaeNVjHG6IcY29Otrc78+IzLFGAejCJ+1rceY0WhpqnMx' \
			b'dn3bZBSMFYxdJcY63gqjW9sKA1VtsBWGRCnGOtkKoztmK4xOtsLo+mwUY53ZCiOd7vqtMNJtlzDWXzWDsW5p+4vstlMYyxL4Lgun8s1jLFVZMDa+vPMDjHVm44vO9xjr5ra86PItL8aZM8a0kkbWiDGt2gUwliqfYUzbeA1jkm6AsW7DLS+6fMsLIzLBmASj' \
			b'CJ+1LWHMarQ01bkYoy0vgCIFZWehDM5Bd70JpIEkCta2xBoafDT1gfG2D2veiNgNXM43iVK+sSmmH39xRxCOkcPfIfL//udfXM84vo3cTH/+RW+9xDi0HpJw7jdf3ALksvtO/tYLnwroI8Hu7/aSVMR5zGmS9GsvLm3HOZWTxR1GpN97cT3uOL8J3JEUetyN' \
			b'M2fcaXUrW/eQquoug7wkiAx52uRryKOqjXc4JLFsxDwqR888KZn1Z5SoKE3gOqkRQ88I2kuD9dDDZo/4N1T01+HfSPFdTX/pLBKQkuIZ4l8N/XiBfol7lniTuOsUccQ3YdoMzYYcW/WEJ17Nk0mIlNFGSTPnvm7JIhQheoQLkGJAiFUyTFHhsS7plgSWAEGs' \
			b'vlr8aAcup1j3zK5PWPR1c062vDfgyXqrxT7CVs9Z6RO9xtUYL5re3ujmdjUZ1XnXb2tGk91Ei4mG8mImcmgc183ilE3cwrfbGsLMBO715x+T2SNrp6YOLVZctlj11RitOtktV2zXY2zXyXbrtMdSemy8J+Nlniax3YsRu5ARO9OANcsGLF6hAfPFgBUD9kQG' \
			b'bMXrphiwt27A2iPHjIfrMWD1xgZsODf5DIzYWSPIEw1ZZsSCcUO8B0PWXs6QhfjsjZmjH+A83aDt/gWa/RLKTtNh3ZGmrTrXtM2/4nmEdTt2bsyf+YjmbtjC+et6VHs7Fi48lZVz3N2PtnLYpmc/soV7sXTubT26QQk2mu5vL/zo5q19W7Ftbvim+THDz+aG' \
			b'bNu12rWzbBr15ut5couZXTvSpjnuvxsOQ119ozbt7dizasPXl4cT7NmEM84Jz2tr9szN2DNXptRG9mzOowXSQsOwZwvk2WDbt7m9azEM14BcHMjFgVzYBjbW0wX+V09hD8kWZh4tZ9lDGhpu/px3tD1s5uwhakGZmlu1h9hMmU0UPyd211IbiVovmp0bzN57' \
			b'i0SCEtKfS9mjvdijW50YVAx4sqruKZxCcJPIi5nUSXNaFXN6O4+HGzwaPqkpnDWDVTGDmz8W+icxYJd8JizPg8WAXakBK69YtzdgYffq2lxyF9aVvF333Ks2XYe3+nI1mS4yIldsuU62WrzMp5NlPPEa3XRvxXLhHMnbddPd/at7CTDFN6rQnFdnyc6yXlAw' \
			b'FCbqyfOwZOc8hEE4usdZsqt/CHuSFQa80hBj0HI9Tzt2pl8IS82d/SgW78WAwTeoCorzug3ZxJraJ/F3w4XihxONmn2LkL89KAZuxcBhr6PV03tUuZsxdPGKbN0eWw/LFk4yeY6UI70XGL4NaLY3gCDFy9jApf0LxA5CmZ7KBlZdd/4DHe4rUB7qTrF52FxP' \
			b'afioox1p/fAgNk9u+3Ai4nEPethPntACnmr7Ro977QWsXfc0T3zWyvnmSp/2ipW7cSt35NRbZtwcSer6H+7uzbh1FxjLHq7AuLXFuBXjdj3GrSrG7e0bN6jW9satugLjdiOvTotxex7GzRXj9gTGrbqTtxC3YMluxH+tvFF4Im8PRwK6p5ek5zl5QMd7iRYb' \
			b'/TyggMVA3bOBeqyH2v0YKVo3c/VG6g5dOc53R2vdS0AL2Slf7FSxU/dup2i4cS3PUlSYYqWOsFLVSwZMgz9fcWjJXl3hSoBir4q92tpe1ddkr+pir862V0/u73/qj+I8wnz5/lds7sKMxQuZMifmzN+3SaPempk1jNAFTfg7R+b/Bc0cl4Mk1h5j7+obG0Vu' \
			b'8GMss0bPoXCiNNHJxu/J1woU41eM31MZv25o/Dpj/Lrs/0WNX3ea8euK8euNnxPj151h/C6wTqAYvxs3fs/B8GEnzwezh97wxUP2/5KGj8pxvOHD+GL4+qEulflko3eB5QJleq5Mz13KqpFxuWPXjKu0XE81Pxcd2il+7XkJz/9ip4qderSdkkTPzYdsM0PF' \
			b'v7XO/2/VUNXoR4adJ+ATFnaml3vqVPigRfaruYRzf7FfxX5tYL+qYr8eZb+q9P+O7Vfx33/G9utAr5VwdvUqbRlp9Y2681PZn9aUURE2GzJKhTaxZJTX0JLhz17ssRmWbVpoXhLjQHteIi+gt70kow1d5SWaW1B1+PZk3Yrz/zO2bldp0dwNWzT39BbNbWrR' \
			b'3IYWzZ34bHaSHSuLA4oduwI7Rn2xLLQ8x47d7WR+wLEl9o0DDi4djyrL4oBir57CXlEGZWH42faK5XfXLx89PnehDh9wcqzm56snXxxQ7NUzsVfc/8pOFhsYLBHl3btLePcSKQcdDb75+erJ/fmLvbpXe8UJr2Dt5b2Zq+fi3eU63HyHfmSpeXLX+2Knbt1O' \
			b'cae9Ltf6m7ZTnPuzN1MVmSnqg3jgyF4Vr/lir063V6Tt17wU6KbtVXmuEoNFE+38XFW85oudOsdOVcVOFTv19uxUW7zji51as1Oo1texCLHYqWdlp9DfioZ97b04wUPx0s/pXqXJgvNX9zO6V/Fa8J7sFzb1Hq+8CUuGluKa7Bm22lkWDQ2Z272ivtGhnqI6' \
			b'uVjTCb971eB2MxCPrQb/KTrY6Ab3jaHoevfKQTldgz8R7aD88P/rBzh+sQdTiZ2gwnR7uB1YqICJwFi0FOcxDgcb+MYSdGEHogeVBh0APYQSQSWgTaE6aEhAPBVuRBXRruoNwcigu/EBv3HQggYNTTLEgZpUDncLwH1u0HcW7wu2l1I6iHUN/q/xP5UmPLo0' \
			b'YNDX/9G9arxXc+zdQMPQqnczt63R4Nez/yqgA5tm18dSKeJyKcAEQBfAX/480K9IzRUK9J1+tVgLl0w3/hY2ms56UGDg2ugfKiv/VlT/f5QGoeL79GiUMUy/nQR3pjNUs+YpagYAqPGHqKGGgOQN/uHvsONvr2ON2g1q1E5VqmpwOxiIh45fIcWGlWTTMFNR' \
			b'uMPR//DZoA8xgVuhre/jY2uvosp348oj79tFEQSSQiOCQNtl9tGak0tF7zxIPni3KpKfG+IADSk5NuOLJlqsXtFWJMhf2hCT5FkZmeIjIVwHFpzlC+daJ3Kup2XtWnmCCbnc8YlDZQ95sfwhDHVwnbYFPo8OPvTU50fRwyQHm0qvsf9nrzRXn/J/9objbGdu' \
			b'mp3K8xqmIhWC2KvsQPR8/oQfFk410cHwIXmHj9bc08IOHlRO62/u5C536LsdjqWO7nr1NXQ/txt+7CCMY9Lw65QPjrmOTo2jKz0Ka2lDdULOZ31Yv1wx4MdokN89sw9rh79S0xx2T/ph4YRtuk71ZL0nvs0e1Ow2+OA81yYZvcV7sLJMjCuLnR1rSbt7Zh/W' \
			b'ji3G+wMV2MzW4vBwq0847zIW0sTUQelCoy5E0+/P6sPaMTENs6Iax/SisGFPwpci+QffNoxjj//gu5uzrmSRTU3epFHlEUNK0Pd42EW/i5fvYoG7Ga4Yoq4W5bdOcOoVzkd3DV0v7gYfHDfrUTs8OZGc3vX1/1cvOPUjmU584SufcNj+jvmHXzhMTPgUQz7W' \
			b'pmb3zD6sHVMzXldmyLvddXxYYNtM4WzchY4V9FwXWe0e6LyRf/BF8jh2Il19RKKtPkfejFtyYrqlGMZxy1e7Z/Zh7Ziab9rMMFb1RsYR3aku8EG3pNMvY8GVuZejulXcPbMPa8fE3Mu23ara6rkDHRQv80GHv9MvY/mVaZljehe6lT6vD2vHRadlrBZs0sPQ' \
			b'8/diH/SmPf0yFmPxszmqk8XdM/uwt+bUhMpxney8gd8pA7y5gV3f55rdeR90jT0yKTmv+7Xk6EI+dYKFPDUvUbrgsAvikonn9WHtmJqEuWQXtIqwaXfEBS+X/9jVI+dmwoK//jkT+6riybtn3F3VB38clr7aS9+KteX0OZSwZU9V3diix863cbM76YNri069' \
			b'ZvDRBV/nXNryV788a1cLcc+ft5E3k2/nneT1dfJud96HqxTPvHrhg4sAN8908cMadPrczu11d1ySeqsfbqXzZ5CuxQPhqXs8rkl+xIcqBaJ9ZDZzH1z2e6Gspz6sVKdPPF2k65/zPvR0E9DsnuSDCrtNoijIP3+eq5gC1gXclaB88MNrh893NioaJRpV7cqH' \
			b'PqxR20wE3pq/DW5vcicfbsbn6TYFJ+7lw814/fN/1zAtj6vMHv3hFWP9/w2y678G+ZtglmY9v6kPq8pGC/buXVXc7pl9WDuKl9hR2uF3z+zD2jE1k1i0Y6Qd7e6ZfVg7ig/cUdrR7Z7Zh7VjaiqyaMdQO3CfzOf1Ye0orn1HaUe1e2Yf3o6wrJU8Sjvc7pl9' \
			b'WDuq3atQ0w5XPKlVuxTBL1RqjxEobYrETf0YStB0r6zOQLvTPke49w+0Jv7YtcetFyR1PZ0a2jn/z6njKDW2M12B2pT/d1FUvbH7mKKmSCVbjs/3yaEUDfYET+kDb4hMWtiKxtWkTRjvxNjWYGzzXFq5xmhs0lYsW0N714DOm+2Uacti2qq4NtsUd7JFMcQ3' \
			b'LId4wK2K8A0Yb8yAHqY8nIhVvjkrztzxo2R0GMbWci2XGYoPxzWtO2VJxdDHgIy+fvj/LH1byA=='

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
		('FUNC',         fr'(@|\%|\\\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LTRU})|\\operatorname\s*{{\s*({_LTR}(?:\w|\\_)*)(?:_{{(\d+)}})?\s*}}'), # AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

		('LIM',          fr'(?:\\lim)_'),
		('SUM',          fr'(?:\\sum(?:\s*\\limits)?|{_USUM})_'),
		('INTG',         fr'\\int(?:\s*\\limits)?(?!{_LTR})|{_UINTG}'),
		('L_DOT',         r'\\left\s*\.'),
		('L_PARENL',      r'\\left\s*\('),
		('L_BRACKL',      r'\\left\s*\['),
		('L_BAR',         r'\\left\s*\|'),
		('L_SLASHCURLYL', r'\\left\s*\\{'),
		('R_PARENR',      r'\\right\s*\)'),
		('R_BRACKR',      r'\\right\s*\]'),
		('R_BAR',         r'\\right\s*\|'),
		('R_SLASHCURLYR', r'\\right\s*\\}'),
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
		# ('BARSUB',        r'\|_'),
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
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})|\\operatorname\s*{{\s*({_LTR}(?:\w|\\_)*)(?:_{{(\d+)}})?\s*}}'), # AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

		('LIM',          fr'\\lim_'),
		('SUM',          fr'(?:\\sum(?:\s*\\limits)?|{_USUM})_'),
		('INTG',         fr'\\int(?:\s*\\limits)?|{_UINTG}'),
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

	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                       return PopConfs (AST.flatcat ('+', expr_add, expr_mul_exp))
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                      return PopConfs (AST.flatcat ('+', expr_add, AST ('-', expr_mul_exp)))
	def expr_add_3         (self, expr_add, SETMINUS, expr_mul_exp):                   return PopConfs (AST.flatcat ('+', expr_add, AST ('-', expr_mul_exp)))
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

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                            return _expr_mul_imp (self, expr_mul_imp, expr_intg)
	def expr_mul_imp_2     (self, expr_intg):                                          return expr_intg

	# def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add, expr_var):     return _expr_intg (expr_add, expr_var, (expr_sub, expr_super))
	# def expr_intg_2        (self, INTG, expr_super, expr_add, expr_var):               return _expr_intg (expr_add, expr_var, (AST.Zero, expr_super))
	# def expr_intg_3        (self, INTG, expr_add, expr_var):                           return _expr_intg (expr_add, expr_var)
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

	def expr_idx_1         (self, expr_diffp_ics, expr_bcommas):                       return PopConfs (AST ('-idx', expr_diffp_ics, expr_bcommas.comma if expr_bcommas.is_comma else (expr_bcommas,)))
	def expr_idx_2         (self, expr_abs):                                           return expr_abs

	def expr_abs_1         (self, L_BAR, expr_commas, R_BAR):                          return AST ('|', expr_commas) if not expr_commas.is_comma_empty else _raise (SyntaxError ('absolute value expecting an expression'))
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                            return AST ('|', expr_commas) if not expr_commas.is_comma_empty else _raise (SyntaxError ('absolute value expecting an expression'))
	def expr_abs_3         (self, expr_paren):                                         return expr_paren

	def expr_paren_1       (self, expr_pcommas):                                       return AST ('(', expr_pcommas)
	def expr_paren_2       (self, expr_bracket):                                       return expr_bracket
	def expr_pcommas_1     (self, L_PARENL, expr_commas, R_PARENR):                    return expr_commas
	def expr_pcommas_2     (self, PARENL, expr_commas, PARENR):                        return expr_commas

	def expr_bracket_1     (self, expr_bcommas):                                       return AST ('[', expr_bcommas.comma if expr_bcommas.is_comma else (expr_bcommas,))
	def expr_bracket_2     (self, expr_ufunc_ics):                                     return expr_ufunc_ics
	def expr_bcommas_1     (self, L_BRACKL, expr_commas, R_BRACKR):                    return expr_commas
	def expr_bcommas_2     (self, BRACKL, expr_commas, BRACKR):                        return expr_commas

	def expr_ufunc_ics_1   (self, expr_ufunc, expr_pcommas):                           return _expr_ufunc_ics (expr_ufunc, expr_pcommas)
	def expr_ufunc_ics_2   (self, expr_ufunc):                                         return expr_ufunc

	def expr_ufunc_1       (self, UFUNCPY, expr_pcommas):                              return _expr_ufunc (expr_pcommas, py = True)
	def expr_ufunc_2       (self, UFUNC, expr_var, expr_pcommas):                      return _expr_ufunc (expr_pcommas, name = expr_var.var)
	def expr_ufunc_3       (self, UFUNC, expr_pcommas):                                return _expr_ufunc (expr_pcommas)
	def expr_ufunc_4       (self, expr_varfunc):                                       return expr_varfunc

	def expr_varfunc_2     (self, expr_var, expr_intg):                                return _expr_varfunc (self, expr_var, expr_intg)
	def expr_varfunc_3     (self, expr_sym):                                           return expr_sym

	def expr_sym_1         (self, SYMPY, expr_pcommas):                                return _expr_sym (expr_pcommas, py = True)
	def expr_sym_2         (self, SYM, expr_var, expr_pcommas):                        return _expr_sym (expr_pcommas, name = expr_var.var)
	def expr_sym_3         (self, SYM, expr_pcommas):                                  return _expr_sym (expr_pcommas)
	def expr_sym_4         (self, expr_subs):                                          return expr_subs

	def expr_subs_1        (self, L_DOT, expr_commas, R_BAR, SUB, CURLYL, subsvars, CURLYR):  return _expr_subs (expr_commas, subsvars)
	def expr_subs_2        (self, SLASHDOT, expr_commas, BAR, SUB, CURLYL, subsvars, CURLYR): return _expr_subs (expr_commas, subsvars)
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

	def expr_mat_1         (self, L_BRACKL, BEG_MAT, mat_rows, END_MAT, R_BRACKR):     return _expr_mat (mat_rows)
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

	def expr_curly_1       (self, L_SLASHCURLYL, expr_commas, R_SLASHCURLYR):          return _expr_curly (expr_commas, forceset = True)
	def expr_curly_2       (self, CURLYL, expr_commas, CURLYR):                        return _expr_curly (expr_commas)
	def expr_curly_3       (self, SLASHCURLYL, expr_commas, SLASHCURLYR):              return AST ('-set', expr_commas.comma) if expr_commas.is_comma else AST ('-set', (expr_commas,))
	def expr_curly_4       (self, SLASHCURLYL, expr_commas, CURLYR):                   return AST ('-set', expr_commas.comma) if expr_commas.is_comma else AST ('-set', (expr_commas,))
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
		'BINOM2'          : 'BINOM',
		'BINOM1'          : 'BINOM',
		'expr_super'      : 'CARET',
		'caret_or_dblstar': 'CARET',
	}

	_AUTOCOMPLETE_CONTINUE = {
		'COMMA'        : ',',
		'PARENL'       : '(',
		'PARENR'       : ')',
		'CURLYR'       : '}',
		'BRACKR'       : ']',
		'BAR'          : '|',
		'SLASHCURLYR'  : '\\}',
		'L_PARENL'     : '\\left(',
		'L_BAR'        : '\\left|',
		'R_PARENR'     : ' \\right)',
		'R_CURLYR'     : ' \\right}',
		'R_BRACKR'     : ' \\right]',
		'R_BAR'        : ' \\right|',
		'R_SLASHCURLYR': ' \\right\\}',
	}

	_AUTOCOMPLETE_COMMA_CLOSE = {
		'CURLYL'       : 'CURLYR',
		'PARENL'       : 'PARENR',
		'BRACKL'       : 'BRACKR',
		'SLASHCURLYL'  : 'CURLYR',
		'SLASHBRACKL'  : 'BRACKR',
		'L_PARENL'     : 'R_PARENR',
		'L_BRACKL'     : 'R_BRACKR',
		'L_SLASHCURLYL': 'R_SLASHCURLYR',
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
					# elif self.autocomplete and self.autocomplete [-1] == ' \\right':
					# 	self.autocomplete [-1] = self.autocomplete [-1] + self._AUTOCOMPLETE_CONTINUE [sym]
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
		idx = -pos

		if self.tokens [self.tokidx - 1] == 'COMMA' and (self.stack [idx].sym not in {'CURLYL', 'PARENL', 'L_SLASHCURLYL', 'L_PARENL'} or \
				not self.stack [-1].red.is_comma or self.stack [-1].red.comma.len > 1):
			self._mark_error ()

		return self._insert_symbol (self._AUTOCOMPLETE_COMMA_CLOSE [self.stack [idx].sym])

	def _parse_autocomplete_expr_intg (self):
		if self.autocompleting:
			vars = set ()
			reds = [self.stack [-2].red]

			while reds:
				ast = reds.pop ()

				if ast.is_var:
					if not (ast.is_differential or ast.is_part_any):
						vars.add (ast.var)
				else:
					reds.extend (filter (lambda a: isinstance (a, tuple), ast))

		vars = vars - {'_'} - {ast.var for ast in AST.CONSTS}

		if len (vars) == 1:
			self.autocomplete.append (f' d{vars.pop ()}')
		else:
			self._mark_error ()

		return True
		# s               = self.stack [-1]
		# self.stack [-1] = State (s.idx, s.sym, s.pos, AST ('*', (s.red, AST.VarNull)))
		# expr_vars       = set ()

		# if self.autocompleting:
		# 	reds = [s.red]

		# 	while reds:
		# 		ast = reds.pop ()

		# 		if ast.is_var:
		# 			if not (ast.is_differential or ast.is_part_any):
		# 				expr_vars.add (ast.var)
		# 		else:
		# 			reds.extend (filter (lambda a: isinstance (a, tuple), ast))

		# expr_vars = expr_vars - {'_'} - {ast.var for ast in AST.CONSTS}

		# if len (expr_vars) == 1:
		# 	self.autocomplete.append (f' d{expr_vars.pop ()}')
		# else:
		# 	self._mark_error ()

		# return True

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
			# if rule [0] == 'expr_intg':
			# 	return self._parse_autocomplete_expr_intg ()

			return self.parse_result (None, self.pos, []) if self.rederr else False

		return self._insert_symbol (rule [1] [pos])

	def parse_success (self, red):
		self.parse_result (red, self.erridx, self.autocomplete)

		# if not self.has_error: # if no error or autocompletion occurred and all remaining conflicts are trivial reductions then clear conflict stack because parse is good
		# 	if all (len (self.rules [-c [0]] [1]) == 1 for c in self.confs):
		# 		del self.confs [:]

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

# AUTO_REMOVE_IN_SINGLE_SCRIPT_BLOCK_START
if __name__ == '__main__': # DEBUG!
	p = Parser ()

	set_sp_user_funcs ({'N', 'O', 'S', 'beta', 'gamma', 'Gamma', 'Lambda', 'zeta'})
	# set_sp_user_vars ({'f': AST ('-ufunc', 'u', (('@', 'x'), ('@', 't')))})

	# a = p.parse (r"dsolve (y(x)'' + 11 y(x)' + 24 y(x), ics = {y(0): 0, y(x)'(0): -7})")

	# a = p.parse (r"""Limit({|xyzd|}, x, 'str' or 2 or partialx)[\int_{1e-100 || partial}^{partialx or dy} \{} dx, oo zoo**b * 1e+100 <= 1. * {-1} = \{}, \sqrt[-1]{0.1**{partial or None}}] ^^ sqrt(partialx)[oo zoo] + \sqrt[-1.0]{1e+100!} if \[d^6 / dx**1 dz**2 dz**3 (oo zoo 'str') + d^4 / dz**1 dy**3 (\[-1.0]), \int \['str' 'str' dy] dx] else {|(\lim_{x \to 'str'} zoo {|partial|}d**6/dy**2 dy**3 dy**1 partial)[(True, zoo, True)**{oo zoo None}]|} if \[[[partial[1.] {0: partialx, partialx: dx, 'str': b} {-{1.0 * 0.1}} if (False:dx, 1e+100 * 1e+100 b) else {|True**partialx|}, \[0] \[partialy] / Limit(\{}, x, 2) not in a ^^ zoo ^^ 1e-100]], [[Sum({} / {}, (x, lambda x: False ^^ partialx ^^ 0.1, Sum(dx, (x, b, 'str'))[-{1 'str' False}, partialx && 'str' && a, oo:dy])), ln(x) \sqrt['str' / 0]{d**3}/dx**3 Truelambda x, y, z:a if a else b if partialy]], [[lambda: {1e-100, oo zoo, 1e-100} / \[b || 0.1 || None, \{}, \[[dy, c]]], {}]]] else lambda x:ln({}) if {\int_b^p artial * 1e+100 dx or \['str'] or 2 if partialx else 1e+100} else [] if {|{dz,} / [partial]|} and B/a * sePolynomialError(True * {-1}, d^4 / dy**2 dz**2 (partialx), 1e-100 && 1.) Sum(\[1, 1e+100], (x, {'str', 1.}, \sqrt[1]{partial})) and {d^5 / dz**2 dy**1 dx**2 (oo zoo && xyzd), {dz 'str' * 1. && lambda x, y, (z:zoo && lambda x), (y:0)}} else {}""")
	# a = p.parse (r"""\begin{cases} \sum_{x = \lim_{x \to \left[ \right]} \left(\sqrt[1{e}{+100}]{False} + 1{e}{+100} + \infty \widetilde\infty \right)}^{\left\{\neg\ \partial x\left[1., \emptyset, \text{'str'} \right] \vee \lambda{:} \partial \vee 0.1 \vee dz \vee \frac{\left(d^2 \right)}{dx^1 dz^1} - \frac{1}{\sqrt[\infty]{\partial}} \right\}} \left(\frac{\frac{x}{y}\ zd}{dz\ c\ dz \cdot 1{e}{+100}}, -\left(\partial x + dz + 1.0 \right), {-2}{:}{-{1 \cdot 2 \cdot 1.0}}{:}\left\{\partial x, 1.0 \right\} \right) & \text{for}\: \left(\lim_{x \to -1.0} 0^o o \wedge \log_\partial\left(ypartialx \right) a! \wedge \sqrt[xyzd]{\infty}\ \widetilde\infty \cap \frac{\partial^3}{\partial x^1\partial z^2}\left(0.1 \right) \cap \frac{\partial^9}{\partial z^3\partial y^3\partial x^3}\left(a \right) \right) + \left(\lim_{x \to \begin{bmatrix} b & True & \text{'str'} \\ dx & 1.0 & 0.1 \end{bmatrix}} -1 \ne dx, \begin{cases} \infty \widetilde\infty \wedge \partial x \wedge None & \text{for}\: dz! \\ \lambda & \text{otherwise} \end{cases}{:}\partial y, \left\{\left\{dy{:} \partial y \right\}, \left(False{:}\partial x{:}\emptyset \right), \lim_{x \to \partial} \partial x \right\} \right) + \frac{\begin{bmatrix} \infty \end{bmatrix}}{\begin{bmatrix} \emptyset \\ \partial y \end{bmatrix}} \le \ln\left(\left\{None, \infty \widetilde\infty, dy \right\} \right) \\ \left(\operatorname{GeometryError}\left( \right) \wedge \ln\left(x \right) - 1.00 \right) \left\{dx{:} 0.1 \right\} \left\{1.0{:} \partial x \right\} \sum_{x = 1{e}{-100}}^p artial\ True \cdot \left\{\text{'str'}{:} \begin{bmatrix} xyzd \\ dy \end{bmatrix} \right\} \vee \left(\left\{\emptyset \right\} \cup \frac{True}{\partial y} \cup \left|\partial x \right| \right) \cap \left(\begin{bmatrix} True \\ \text{'str'} \end{bmatrix} \cup \widetilde\infty \cdot 1.\ True \cup -\partial x \right) \cap \operatorname{Sum}\left(\left(\left( \right) \mapsto 1{e}{+100} \right), \left(x, \infty \widetilde\infty\left[1{e}{-100} \right], c \vee \partial x \vee None \right) \right) \vee \left(\cot^{-1}\left(\emptyset \right), \int dx \ dx \right)! & \text{for}\: \left[\left|\left(-1 \right) \right|, \frac{\partial^4}{\partial x^2\partial z^2}\left(\log_{\emptyset}\left(-1.0 \right) \right) \right]\left[loglambda\ x, y, z{:}\begin{cases} \infty \widetilde\infty & \text{for}\: 1{e}{-100} \\ dy & \text{for}\: dy \end{cases}, \operatorname{Sum}\left(False, \left(x, False, 0 \right) \right) \cap \sqrt[False]{2} \cap \frac{1}{dx\ a!}, \gcd\left(\left(dy \vee \partial x \right)^{1.0^{\partial x}}, \operatorname{Sum}\left(b{:}None, \left(x, -1 + 1.0 + \text{'str'}, xyzd! \right) \right), \left|-1 \right| + 1.0 \cdot 1.0 \right) \right] \\ \left|\begin{cases} \left(dx\left[\partial, \emptyset \right] \wedge \left(False \vee \partial x \right) \right) \left(\neg\ -1^{dy} \right) \frac{d^2}{dx^2}\left(dx \right) & \text{for}\: 1{e}{+100} \\ dy & \text{for}\: 1{e}{-100} \end{cases} \right| & \text{otherwise} \end{cases}""")
	# a = p.parse (r"""Eq(Union(dy2 - 2.0651337529406422e-09*notinxyzd, Union(Complement(diff(z20notin)*diff(s)*partialxb, diff(diff(diff(-1.0)))), Complement(diff(diff(diff(-1.0))), diff(z20notin)*diff(s)*partialxb))), Or(Union(Complement(Union(Complement(Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))), partial.chCa.dcGNDli().XG()), Complement(partial.chCa.dcGNDli().XG(), Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))))), diff(diff(dx))**1*e - 100), Complement(diff(diff(dx))**1*e - 100, Union(Complement(Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))), partial.chCa.dcGNDli().XG()), Complement(partial.chCa.dcGNDli().XG(), Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))))))), 0.1 - bcorx0orc)); slice(None); abs(Matrix([Integers])); Matrix([[[Eq(c, 2)]], [[{Lambda: oo}]], [[lambdax, slice(y, 2)]]])""")
	a = p.parse (r"\int oo + 1 dx")
	print (a)


	# for v, k in sorted (((v, k) for k, v in p.reds.items ()), reverse = True):
	# 	print (f'{v} - {k}')

	# print (f'total: {sum (p.reds.values ())}')


	# a = sym.ast2spt (a)
	# print (a)
