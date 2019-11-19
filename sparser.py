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
	# ast = ast._strip_curly_of_paren_tex._strip_paren (1) # ast = ast._strip (1)

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

def _expr_intg (expr, var, from_to = ()): # find differential for integration if present in ast and return integral ast
	if var.is_var_null:
		raise Incomplete (AST ('-intg', expr, var, *from_to))
	elif not var.is_differential:
	# if not var.is_differential:
		raise SyntaxError ('integral expecting differential')

	return AST ('-intg', expr, var, *from_to)

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

	if args [0] == '-func':
		ast2     = AST (*(args [:iparm] + (_ast_func_tuple_args (ast),) + args [iparm + 1:]))
		ast2.src = AST ('*', (('@', args [1]), args [iparm]))

		if ast2.args.len != 1 and ast2.func in {AST.Func.NOREMAP, AST.Func.NOEVAL}:
			raise SyntaxError (f'no-{"remap" if ast2.func == AST.Func.NOREMAP else "eval"} pseudo-function takes a single argument')

	else: # args [0] in {'-sqrt', '-log'}:
		fargs    = ast.strip_curly._strip_paren (1) if args [0] == '-log' or (not ast.is_paren_tex or ast.paren.op in {',', '-slice'}) else ast.strip_curly
		ast2     = AST (*(args [:iparm] + (fargs,) + args [iparm + 1:]))
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
	argsc      = arg # .strip_curly_of_paren_tex

	if var.var in _SP_USER_FUNCS:
		if argsc.is_paren:
			return PopConfs (wrapa (AST ('-func', var.var, _ast_func_tuple_args (arg), src = AST ('*', (var, arg)))))

		elif var.var not in {'beta', 'Lambda'}: # special case beta and Lambda reject if they don't have two parenthesized args
			ast = wrapa (AST ('-func', var.var, (arg,), src = AST ('*', (var, arg))))

			return Reduce (ast) if rhs.is_differential and self.stack_has_sym ('INTG') else PopConfs (ast)

	elif argsc.is_paren and var.is_var_nonconst and not var.is_diff_or_part and argsc.paren.as_ufunc_argskw: # f (vars[, kws]) -> ('-ufunc', 'f', (vars)[, kws]) ... implicit undefined function
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
			b'eJztnXuP5DaS4L/MAdMNZAKSSFFS/+exPXvG+rW2Z24HDcNoe7wL4zy24bZnZ7G4737xpIKZ1CtL1ZWZRbS6UqIoPoPxE8kg9eL1H758/7OPP/v0D4c//K/vf/ob/Ojl+3/+4uO/fgwnH3/z+XtffPgpnsaTj7/54xfvvf+veBpP/vynP3/6/ud/1TP4/fSz' \
			b'r+DvX977Av5++ddP6B780vMf0L0vP37vy//Np3/88F++ef+9Lz/8Us4/eU9d/zie/mU8/ZxPKYSYhj/BifzU8tvA7ycfffpnCvejTz/7RH9rPWkoQRRQzPTJ1VeUhT//Ue/w6YeffP7VX7/8EJPx0adf/Qvm+M+Uu48+Ie/099++wPsfY5F+/Bn6kcKBIqSC' \
			b'4b/vf/bJJ+9pqaPDF1zqX2ipsxtl9AstdXF7j3/HJH+RZACvPvw3+PPeJ5/D3w/++DHdQ9dPP5BixrM/jqd/GU+lmD/8+MsPMSlffPQJ/n747+9jubz3FRUMBvkVZwOS+pX+YgF/8NFfPvoAn3hfKpz9ff4x1QeUnVbNv3/54fvk4YOP/vQnlKFPP2IxpES/' \
			b'9+kHWMh44zN8/pP3Pv/yq88kiSo15PB/uGrwp+Y6gyjf/1c4ffv7t2//8ebXt/8w52/h/Ls3v37/2zc///rN37798e1vb341t+H0+3/+And++Mff9fyn7//zmze//qdevv39l+9/HS++hdO/v/ntm+9+/lHOfv35v8Yzju/t92/ffhfPfolnGsybb+PpD3/7' \
			b'Z3T97bcY0X+8+e43Pf+FImDn33/6bkzzf/zHL8nFNz9893ZMaczQjz+MeRtdf/v+13j+999//OaHv8fAvvv91x//2xSNnn77w08/22KKqfr1zXc2KDjRy398H++8+dvfoqc3MXP/fPv9mFMqpZgDzJMp+Hjj959++PmneOO/Y4p++Om3mKTvxtxAPdti+8eb' \
			b'WMg//Rxj/t16efPT3xJ3W67ffvfz3//+Jl7+HAP7Fgrh/34/Vlrq75cfvv/u+3gBAvnTWBa/vP3t5xh1FJKYk59/HHNLgSYXb82T3/z4jzc/juXHT359eP3iGJpDaF8e+CTgSVvjn+bQhpdyCVd05tDboW0PR7mlDnzV6HPwgFMnPCVfx45cqsML7w5Hd2jr' \
			b'l9HBo4P36nAc8MRV/KeDBLjmpXVq2jOnrrFOeApndeA/XXc41v1LccJTOOvgf39oIW6+0+EJ/GJA+Ot7/OMOAXzUnNjRSS+PntJa+8OLQJkYXup1R7msOEnt4UWDHtCxG52Sy6aXE3TDQCAltY9nVEvwxAvMAtRKz2nCMBpKRFPznw7uN5xCuMJTLFaqBKyP' \
			b'l+ZSz407VzVWMeaQ/vtWb3s8wUSKOycdSkEc+RrS2AyU+yY6UJ37MF5X5MGdOIw+jo4y5T3/CRwUioqnJHgnl1o3mAxOR+A/AaonSPlj2VPxBpAXFB+5ESq94TupW04SXEL90rMQUYNCgRUjOUYnZy+5kB274eNQqA7KoGV5iJf9qZNISeLsM5fpg74+v8z4' \
			b'6FKn5vwyeejog0nZ2DIkEScO9alDYx0GqZLa6zW0bBJJUBNYlJQ4iB7rveYkxFt559Tp6GsKGIQepAVjGg49OAeQIfAr0Z7fRUUHKmXZE0hJ6unoqW2gDgB/lbYJSGzNORtQCdSYL3+A7IkuQOfoOLr07NKPLgO7jE81FbmIqFKTojy7hv+EISZPnbrKOuEp' \
			b'nvX8B4rt5cvxFM88twZ9BBUxQwATNIohXqK/8RIqlzRTz/5Uu2LIXC/VgUOqHf/p4JmaW3ft6JTKEZuvnLDKxso4MBA6VQfoKE7xuqVribaSOLDFH0KtUpi4qws4UAKDSKhUAda1Z71L/8EjlxaqUCr/wH86SEkj1RboFEsEtEePrV/A1x16KnootBe1Z94d' \
			b'oEbAS6g1W3ST8+FzN0G3U8pQ/nuRz5bLIUgrEeFstD7A8UUwFYWXYUxWfwgUJCivFwQVYQhecvhnTvESUkQyMlArlDNfyZlIJpw0euL0hBmGJRTDw6shiVBd4tWxobDrVi71DuSu5kx4/tNhSUmheTpFb8OBJaup+EqFHxtVw0mDikZAjpSuqaTQU89/OqxS' \
			b'aX6klKgUA/8xL0JBeNm2/IfegeReS6d45vXmS7mEK73BNIIU9S3JQUQhSjO/QtHbltfHA/qikg1eb+BLlrjAGbzfva4ONZRJDcIEOfWEcpAdkBeQfNR5IFbDAdoqqDcosOEApTPAaQOFB49BWddYkA0GU8M5qDeoihqauSNxrmv871BXQluo4X2vhpdC9NIf' \
			b'ao//4WmgWw3SX1dYJXgOt0ESQaU7fAb+QzJqSEcNCakhJTUUSA0FVYPGryGiGmPC8OFdBxALWqqGUqlBRw/uMPjD0B6GcBi6w4DhHDDl8DCGDWEC4Qf4qSCoqj7gWy690kEjqSvwWEHKO3j1OoB6heiwWjvSPD3obwQzpRzirzBg+PX4Cw9CSdZQlDX4hYbf' \
			b'+wNUXI/lA29m4NQf+uEwYPrBP6QYNTtUPTASogcd1eHrCSjwjl5w4e0VRK0jWe7ofRVUVkeUqRvMPDxUoWKDiwbfNuDtD1GFxQnpa/BVHk5fYquGtEHVv8A6Rwest5dwG9MMl55dMSfoC3ODd0EW0Bkr4iWxHe++xtcAuqawi7zckby8GLjia65hrDGq8aEW' \
			b'MWL5wJrFy9rLbyuPyXNU1fQrz8mD6COw7JBIFdVzv6KEdd2VSr7/Si4t+c4r+YVjLe4a1fKOtXonSl3eKQZXJOG+JeE1DleWOr7zOqbSx/bdUoM2lfU1jVCxEuA3uOQmusoLYEsvgFQnJz5a7lNQEbxMcvzuc2uE81QgTwTxVARF9LJCZ4SNhSwjXCJQVoqs' \
			b'9JzKzYS8gIxglbTSmaOG8TK2D20X0gZE7lXirXwbuVZZZvlVgS3V9OBqQm5yr8i10hevhKOttCkX5Fo7622QinXZxib98NrnG9sLyiY937bSHwvaD3NVUeT3rchf1F675fwCVyr7fisbtUup4/uu4xd17IE18hIV4pAsoQSnyCBhh/YQSl3fdl07L1Ud5GVc' \
			b'3hVkxLXVgVm6rgO+10FpBSwhLCxIORRMDSVT5OCW5QBquC01fOc1HEoN33kNd6WG77mGXww6KsY9+EE65phv7m5XzOkyuPJogyvtUPo/d97KMKPcrmRci9+NLxEaGivDwdMgYyTBPTwofWWveLSt1cE27q1tDo+H6ODx/qLHG7Hl0AH3qgy476VsfDFsuHNd' \
			b'A3XMDG/LOPmdV/ULnj57UXsdYpExFi/TMdzaX6MlN173fLvnfjkqZ9S0OKmDlYImk2Vm7d1OgPZSUbW8FvRMvJ7NVvtBjBbl5cE5nRWRem54hE1eLuSqkcqmIG3tUrmggmj5cZla4znzdP6tlZgCpy9wsgInq+M+YQX3KhSHPomlVPsKDAdW0R1XXNeXAn1g' \
			b'gXasCTtuAh03gW6YK1dVgKV815Qvq4yOVUZfFYF9mOLvRPGLsg4svo0AWifLyhvcnb/Bvab1Lc3Lsprp3uvZUzXjOqWmrDy6s7rFd2tebFbq9r7qFhcMNrKsDH5LJd5iJdIiwNIy761Sa26TtGQT22apzhuvTno1ksIvCwGusNfKi6CpzZUFsvfeInGhu1Y1' \
			b'//byKkTXpYVeYwvFBa1USRANVloxsr3zRtqIPm4baaQ686eN1dNL0snqqraSp6RpN2JnIZ0dR0JU2vR1tOnXtKwOK6RUxNMq19ppq3K5VuUrucuNslTTk1WTqDdXi1KUegl0UurjHdeHc4IV3j+JJxLZskGMj3lWMcQVvtSfL1XzLtDiS1m/O4yXsn5HKmfw' \
			b'qvLFhFhMl6j3w0pGTJuoH0RbFrARNK5ao54Tv1gPnfSnGPilwh6tcVRVKeFHfSuqvHT6pJcXqMv4kHUDr8tmiPc/wiDbHeEyExKblhQjlDMWQmmf+2nAhlCzfbGMDNNWPALkBVg87vOCRnq+ZhPwJjEHJkdfOkRPUdV9Kx3Us50RMIFsFkaa9aHRRSmpdU0V' \
			b'SUBqu1mqbM37CW9xtV+FOF2bwWOwPTfjnt8zRQi450xXZOzfsLE/NXC5bNz5SFQvAx68u2Wh8x3TmUeGX8jwfwjyaidTdKWNb1uVwW2w7BR6783mNa5hKvZ8N1t7pNmKgrtgkKUr5XZRufUPWHCJq/0Iy11VsHzJ2rO+6Opb1dW4MJNlvymyf4nsu1JslxRb' \
			b'Wa5xwypDJu+6tsj+JYOLVZH9m5X9WkyX4J7j5aL4g4MPL+mLqvgDVev0m2VOFsC4l7qGwtnv22Bdu2jEzUbdeu3EqFsewB8QACfWw+6lzKKzkalESONLZWTkngXQD1zZrmXJkE86sBWqM59iICtIpwaPzmzqTRZ4TizwWMzEY5Dr84kPthPjmKkJ0ABN2Q78' \
			b'1gUKjftoaLqs0bv9qqyFC8PpJrF+wr3NuSNXnFpnNWKVRQbTZUnKXUgJm4qUarzlakQ7SMd2kI7tIKUlO2nJTmzJ8Dfwa2cr74n8VahiIrR7165VRdqUDXF3Wi/Jcu3lh8W5rViOe8JdMY965yMYfqqXcGBbmF76Jmr75tSeSuwfeq7Onju3/UDdYzKncTxt' \
			b'43hTS6rlwL5o0dbXtLslqzhZWVnxO0rHGq9jzx0H0XGAHYtNx6nqRTdWYy/dl/GY26Qgj3n4OGLyNQ+O+JfyEvv1YRxiQTGXPq+n/iupEn3TFYkdVxuw6LSyorB38vCkyHv0QKLtWbQ9i7Yvb1o3L2OOar+Mq91zJQdusTxUViY1Ni5eATFvZX8D/IXo9NK/' \
			b'lI/Ctrh5EKSrK1tp3ndLwpIqlf0sKhvfi1p57Wn5tafl1x4UgEMjb/XoFvhWLTuBYykHuq7kusZrCimUdYaP2XvrqeCh5AK96bKNnK4+cVT6dhkSVVXHO0uxgRzu4o5buOOm47jjeGnAt9uAsaA6FIeOf3r+GaTGIRldaY2P+OLU6TCEfBqhlm8jUOOi9sl7' \
			b'+lO77UtVPKZiHEoBP+6+Pw4LmGTeq8w3IuvIlcKR2+UIxDgwOAapUR6Nqw6vK3wTpC/Io7kIfkV+MJLNBdZL7XPoXCRopELVzIXOHQfsNTjqUwQsJ84RFxsUd+Ai9pLH09xx1gZJPZablhNLna1MkpVc02ukUKgWVMZE8miGHPzZDR3xhTe+McE1Fip+8Au/' \
			b'JQXR1ijtIEg17gWJn+TGjzZj/LilCW66AWLT4OJxkIAGxQUHvCsQGNwNEM3RcPss3CYIt69BAzAsSCzJBqsLnsPGgYPnWKgoaCBpDe7AhbtvoQKBom1wgB4H53FRBG6iBq2g8VgVcA9XrON2hbhUHaSxwbWMLbY5uAcy1eCGA7hRIQ6V4t4VuAAWrcrRNBpK' \
			b'vMGlXLhEAG1+cZU7SGmDu7cMKPQo9diaoZ6p83iEaoWCONaQ6iPk4AhyfoSUHD2eV4fjAM4V3odT+I+1c8TqOaKGODr8T87wCNbIESTriA3niDrgiJV6xLZ0RBVwhCwfUQMcsdkfsc0fsWEdawoDCuzoMPiAkWE46DNQCOAdmvAx4G2olCMU6BEK9ggFcaSI' \
			b'MM0oIkdspUdspsceTyCnxwGDwJAxQkxkh3dA9I8gv0eQ/yNIJ5bEEQNwmNABk4eJ8piOFgPAqLAYULEdUYcdUYEdUa1wjkEYjw06V+jLkXd0xqTCLWgExxYTgW6YAKiIIwjsESrv2FEdwB8MiB6FGwNmjEof46WU1HiLyhhOqM4ot+DZYTli+DUlntzxecyi' \
			b'w8KhAkI/EDD8DvgLnkD0jwM+UVEm4QyLHysJz7FOsCwxBiyFnmqL/oAPyh7c7TBVFeUJr8AfCOARGuGxw9LGPMIjPZUWhAP3QIFy0jGf2NSPAxYRVglmzlGNQcp7DBmT3+NDw9eo61DDFf1W9Nta/VaUW1Fut6LcGlRuU0qN33I7o93MG+KMjouDvzwifKrs' \
			b'2kl9l39nXdR6J2/pYvS0Sv91K3VgdaIH24wu3KIDw23oQdyjDK0Joz5sMzoR7kG9LOvGDiuoW9CCHf1LdCE5XKIPO9aI/PykVuzW6EUKYx/d2MU8Dpq11bqxW60du0Q/dhkNuVExdjenGikbmATRkV1GS1IFLGvKw/+EV0jx7hVyfIAL1/8/XBh0ufqkIQ07' \
			b'NpDoURq8mNSmrShUO4ogytUb/UoGoNyxtwMTm8YHRqWbGx7LK+A+tdNrZLq9NzrZZYe8ktEgGZigHddxhEZGOtJRknCiw3VYTHQ5jQXxKE3cDnyVfpeZD/xMKH5uGb8QHPU9+MOxEdL7+OoP/nBkBhmAH47Gr0bvzgK4j9//OGMChIHCtMgGl+cD7qNOjGge' \
			b'yIl6ZAUOIeJGSJEZfh03cOst/FAY8aMzDIFGAWXkoIyYJ5VhCmoZGtJbwAoKGh0JWcSV9FdPv/S/ZcDQb54x6nVkTS2v3xJLxA1FKcSJiaDkMn3UvxKIgIKjh/QrJKILHK3EX9xJLoYygSS8pVTCJR1IJrSBIzpRwluXJidHqsSDG5Lr8UbEFxfIGcJiiagP' \
			b'HIbNh1TJK1k7Yq6W3Cvt9LqWYqBzC0CKo+faMwQ8j4txqNm3ItL5mOltjOSEL0MyFkmCShWMJWCKvxNkUpWTtPcPRidLPtNT26lS1BShBam4CUqxAXMOJTCBqnmYi2EELKO1ca/oVa+BSxSBAL8gTH3zCt+pGLyotl/hew6otFf49gCqBa4DAtlfNZBXdnja' \
			b'XJ9nN/zWOyP4FL8GvRG7BbmPitytqN2O2cCYDUuYRWkL5C/hbFBXlLDxouUgpyArviJigyBW3CNig0FsMOErYsX/bCdv9DeF1JDp6JF/l8aaJan14Ibk2pZHQ7LJNA1ZmGrexQOyNB9W5cWHcDQYhgbhZzhlZ2B0hhSdZ0ELOiW/tc28j7nciM6VQ2+xAFJ0' \
			b'SoUvopP9naIz7IjOcDjreJqiS5DJboJMzpUEoLgcH+Ss743LtuDyXfZWCyqfASo7RuXSQCcKER0pKaMrCth40XKIU6QUX5GUMvKp7pGUZvgzBk4pFVKK/3lSxqemSJkbEiX/Lo01S0rrwQ3JtS0P7XN2WUpqvsUDUjIfTuXFh1DS9jS1l3nWw+yYkukQ63nQ' \
			b'QknJq61xasCcw42UXDkKGwsgpaRU9iIl2d8pJbsdKdllKDkWXUJJESihZCeU7Awlxwc563tTMjxwkizDx3sh4xwVCxELEZGIZAmBBbRAxHgkRBQnnf/jc3FbmgAkT76NYSgHKQ7hYBKxcFD9z3JwfGqCg3jLchClVmcGk1hzHEzLY0iuxxtzU4cx0zKBOBEC' \
			b'fpaqHgmI50pAcuec5icZm9QK4yRsym+ICemSLPuYt20E5LQuEzDmPiGgVvMSAcXfCQGpQnciIMtvSkBTK5aA4qZDqzUTkH+ZgOZBzvoZAU/IV7+ilzJFXze8oveVDPu6wr7CvsK+i9nXMPuaJfY1cqTsY6fIPrF8od9F9jXCPgkjsq8x7DNHZJ/4n2dffGqK' \
			b'fU3KPvLaShewNc9n2WeT5Ybkerwxyz7NtLIvHwKyrzHsawz7GmHflIEN5ciw7zz4ENPR2QrufMzaRvQ1K9GnmU/RJ7W8iD72d4q+Zkf0NRn0jZWSoI/dFH2NoK8x6Bsf5Kzvh76+oK+gr6DvYvSxaU6zZJqDhUJHij52iugTm5xm2ibHoE9scTSMiD5jixNj' \
			b'bUZbHPU/j7741BT62szwZ+z32Wiz7LMe3JBcjzdm2ae5VvblQ6i8lJOwrzXsa4V97RT7Utua87B56FOzaeu48zFzG+m30rYmZj+ln1T0Iv3Y3yn9drStaYxtTaTfWHQJ/dhN6Sf2NI2xpzEPctYX6CfUy8BuKLArsCuwuxh2bCDTLBnIYIHQkcKOnSLsxDam' \
			b'mbaNMbATqxgNI8LOWMXEWJvRKkb9z8Mu+puCXc4qJsLORpuFnfXghuR6vDELO821wi4fAsLOGMM0xhimEWOY5tQYJsIutYY5D1tgJ9m0ddz5mLmNsFtpDROzn8JOKnoRduzvFHY7WsM0GWsYU3QJ7NhNYSfWMI2xhjEPctYvhl1dXQXtHr4Q7jE5t7hO7jmz' \
			b'a2qt3Q7M2syqU06dsWlgNg1LbBrkSNnETufr78h1kU6D0ElCiXQaDJ0GE7XSaVhCE7ZweWbzujyWwfF/Hk42WW5IrscbGxbvcVk0p6v3yMTk1MYkwmc4MTLRTMekj3YmXKrU7Lrx0sfTrQwaVjJIqzZlkFTnEoOmV//tgZ9hpE4stRPscDrtEkDOjVkFSB5S' \
			b'1ChbDFPqy5kyY0j5tKsAr7ZPtWbd37i9Vbr2Dw1y22fIrLn+VvVIfa7mkftdqNQh4fgzyzZsSnQkbBMnZVu85AAn4Ea3lG980cZHlW8Uk/Atxk2pZL6pf0UcXgQOTkFHQVT0g3ohhjBBO7w1CbwkCTnYJR7ckFyPN+ZgF0tAkDcRQjWeCgrlUoFo/DYm1G50' \
			b'TQlJuRwJeR4h41HzbkWhG3O8DY2c/GU0xtQnaFRJWEKjFkwKR3HdC5Es6GMPjcJOCtDSUiNnWnLeJAwBpnmQC+DyTtpD9yYpQ5JlSPIZD0k6nn9zS/NvuFaHjhSN7BTRKPNvbs38m5P5Nw0jQtHMv8VY3Tj/pv5n+33jU1MgnJt/S6LNgtB6cENyPd6YBaHm' \
			b'WkGYD6HyUk5CQTP/5mT+zU3Nv7l0/u08bGGeZNPWcedj5jYyb+X8W8x+yjyp6EXmsb9T5u04/+Yy82+m6BLasZvSTubfnJl/Mw9y1i+n3QO2kim0K7R79rTjCTi3NAGHAyp0pLRjp0g7mYBzaybgnEzAaRiRdmYCLsbqxgk49T9Pu+hvinZzE3BJtFnaWQ9u' \
			b'SK7HG7O001wr7fIhVF7KSWhnJuCcTMC5qQk4l07AnYcttJNs2jrufMzcRtqtnICL2U9pJxW9SDv2d0q7HSfgXGYCzhRdQjt2U9rJBJwzE3DmQc765bR7wD4thXaFds+edjyl55am9FCl05HSjp0i7Qah3ZoJPScTehpGpJ2Z0IuxunFCT/3P0y4+NUW7YY52' \
			b'NoAs7awHe5HcmKWd5lpplw8BaWcm+/A80m4Q2g1TtEtn/M7DFtpJNm0ddz5mbiPtVk71xeyntJOKXqQd+zul3bAj7YYM7caiS2jHbkq7QWhnpv7Mg5z1y2n3gG1WCu0K7Z477TwvIPdLC8i9HgntxElp52UBuV+zgNzLAnINQ2nnzQJybyMW2qn/WdqNT03Q' \
			b'ztcztEuizdEu8eCG5Hq8MUe7mGuh3UQIQDtvVpB7s4LcywpyP7WC3KcryM/DZtppNpM8+5i5bbTzK5eQx+wntNOKXqKd+Duhnd9xCbnPLCE3RWdpJ25COy9LyL1ZQm4e5KxfTruyXUqhXaHd5bTjeTu/NG+Hwk9HSjt2irSTeTu/Zt7Oy7ydhhFpZ+bt4m0/' \
			b'ztup/3naxaemaDc3b5dEm6Wd9eCG5NpkaY52mmulXT6Eyks5Ce3MvJ2XeTs/NW/n03m787CFdpJNW8edj5nbSLuV83Yx+yntpKIXacf+Tmm347ydz8zbmaJLaMduSjuZt/Nm3s4KOdfhxbQrG6QU2hXaXU67nmnXL9GulyPdLrNit4i7XnDXr8FdL7iT5yLu' \
			b'eoO73sSsuBP/87iLT03hrp/DnY02izvrwQ3J9XhjFneaa8VdPgTEna76CJSwEXe94K6fwl2f4u4sbMGdZNNWcudj5jbirl+JO81+ijup6EXcsb9T3PU74k4zaHE3Fl2CO3ZT3MkqBv4V3I0PctYvx13ZFKXgruDuctzxxJ1fmrgDD3yknTt2irSTiTu/ZuLO' \
			b'y8SdhhFpZybuYqx+nLhT//O0i09N0W5u4i6JNks768ENyfV4Y5Z2mmulXT4EpJ2ZuPNm4s7LxJ2fmrjz6cTdedhCO8mmrePOx8xtpN3KibuY/ZR2UtGLtGN/p7TbceLOZybuTNEltGM3pZ1M3HkzcWce5KxfTruyK0qhXaHdxbRDNQyJxp9Z2qG005HQTpyU' \
			b'dnzOoS3Sjjz5NoahtKM4hHYxVkof0079z9JufGqCdrSGeYp2SbQ52iUe3JBcjzfmaBdzLbSbCAFox+XEtMNzpR25c1bztKPcj7Q7D5tpp9m0ddz5mLlttOPELtMuZj+hnVb0Eu3E3wnt9lyWzhKc0s4UnaWdxsy041xp7ph25kHO+sW0a65jV5RCu0K726Qd' \
			b'm6m0S2YqrR4p7dgp0k7MVFZ96LwVMxX1H2lnzFRaG7HSTvzP0y4+NUW7OTOVJNos7ZICGZLr8cYs7TTXSrt8CEg7Y6bSGjOVVsxU2ikzlTY1UzkPW2gn2Uzy7GPmNtJupZlKzH5KO6noRdqxv1Pa7Wim0mbMVEzRJbRjN6WdmKm0xkzFPMhZv5x2D9ivpdCu' \
			b'0O7Z047NVNolMxUUbzpS2rFTpJ2YqbRrzFRaMVPR00g7Y6YSY21HMxX1P0+7+NQU7ebMVJJos7SzHtyQXI83ZmmnuVba5UOovJST0M6YqbRiptJOmam0qZnKedhCO8mmrePOx8xtpN1KM5WY/ZR2UtGLtGN/p7Tb0UylzZipmKJLaMduSjsxU2mNmYp5kLN+' \
			b'Oe3KZipPQbvs/mOFejdMPTZXaZfMVXDXPTpS6rFTpJ5Yq7RrrFVasVbRMCL1jLVKjLUdrVXU/zz14lNT1JuzVkmizVLPenBDcj3emKWe5lqplw8BqWesVVpjraJeGhNYjn2pzcp5DMI+yayt6c7HLG5k30qblZjulH1S3YvsY3+n7NvRZqXN2KyYokvYx27K' \
			b'PrFZaY3NinmQs345+8rWKoV9hX0PZl/g2bywNJuHe83SkbBPnJR9QWbzwprZvCCzeRqGsi+Y2bwYaxhn89T/LPvGpybYF+Zm85Joc+xLPLghuR5vzLEv5lrYNxECsC+Y2bxgZvPUS2MCy7AvpHN65zEw+zSztqY7H7O4jX1h5ZxeTHfCPq3uJfaJvxP2hR3n' \
			b'9EJmTs8UnWWfuAn7gszpBTOnZx7krF/OvrLRSmFfYd/D2cdze2Fpbi/okbKPnSL7ZG4vrJnbCzK3p2FE9pm5vWAjVvaJ/3n2xaem2Dc3t5dEm2VfUiBDcj3emGWf5lrZlw8B2Wfm9oKZ21MvjQksx750hu88BmGfZDbJuY9Z3Mi+lTN8Md0p+6S6F9nH/k7Z' \
			b't+MMX8jM8JmiS9jHbso+meELZobPPMhZv5x9ZduVJ2FfX2b5Jrl3Td9ZwE/cwDV9rGXTGKjnMVC/NAbq5UjHQNnp/HtC5Lo4CuqZhhpKHAX1REMaKvImZh0EFe+zMERtIh6nRkH9DA1ZcMf/+ZFQmzgcCfWZY34kVHOuI6H5ECr51S/eOfPNoZYL6sifHpoc' \
			b'CfUnnx7qJfCYwfHTQ3SLPz3Uj5c+nm4dEPWzYKTEu1GUTsZDpeaXuEhFkvn6kJbObqOiPqUjB+5NYZ4MjXL6dWgUoIMCiyLEsOQsyyDpWOFcHqew9AhLyLBSsm5f0WuFxeT17ddy8smiW4dl7mNFpbN4x51Fx51Ft9RZdHKknUV2ip1Fx3ik38XOomM8ahix' \
			b's+hMZ9GZiLWzKP6Vj3gROLizLmN8dqrL6Oa6jDbybJfRenBDch1M4cx0GTXv2mXMh4BdRjnVXqNBpN5qTHi5XqNLe41nkUivUfJrq7yL8W/tNbpZOI69Rk13Qket98Veo5THSa9xRy6yQJ/0GsdkJ71GdtNeo2MQ8q/0Gk1+xfOlvcbr29Cl4LDg8JZxyJai' \
			b'YclSFIFDR4pDdoo4FEvRsMZSNIilqIYRcWgsRWOsYbQUVf8Rhy3jMDeCGp+dwuGcvWgSeRaH1oMbkuvxxiwONe+Kw3wIlY+nikNjMqq3GhNeDoep4eh5JIJDya+t8i7GvxWHKw1HY7pTHEq9L+KQ/Z3icEfD0ZAxHDVFl+CQ3RSHYjgajOGoeZCzfjkOr2/D' \
			b'l4LDgsNbxmFgHIYlHAY5UhyyU8RhEByGNTgMgkMJI+IwGBwGE7HiUPxHHAbGYcjgMPqewmGYw6GNPItD68ENyfV4YxaHmnfFYT6EysdTxWEwOJRbjQkvh8OQ4vAsEsGh5NdWeRfj34rDsBKHmu4Uh1Lvizhkf6c4DDviMGRwOBZdgkN2UxwGwWEwOBwf5Kxf' \
			b'jsPr2xHm2X7fvYDxzsDIayvC0toKlGk6UjCyUwSjrK0Ia9ZWBFlboWFEMJq1FTHWMK6tUP8RjD2DsR/BSEFU9IO0iCFM4bGfw6NNQhaP1oMbkuvxxiwetQQUj/kQEI9yqnjky0hIuduYIHOE7FNCnsUjhJQs27rvYhK2ErJfSUhNd0pIEYBFQkp5nBCy35GQ' \
			b'mkFLyLHoEkKymxKyF0L2hpDjg5z1iwnprm8XmULIQsj7IOTAhByWCDnIkRKSnSIhByHksIaQgxBSwoiEHAwhBxOxElL8R0IOTMjBEHJgQg5MyBjCFCGHOULaALKEtB7ckFyPN2YJqSWghMyHgISUUyUkX0ZCyt3GBJkj5JAS8iweIaRk2dZ9F5OwlZDDSkJq' \
			b'ulNCigAsElLK44SQw46EHDKEHIsuISS7KSEHIeRgCGnqybHnSwl5fTvPFEIWQt4FIVETeBLTeUKiHNOREFKclJCdWKbS7xIhyZNvYxhKSIpDCNmZQwmp/pWQeBE4OCUkBVHRD1TeGMIEIfHWJCGTJOQImXhwQ3I93pgjZCwBIeRECEBIPRVCyqUSUu82JsgM' \
			b'IakkRkKex8OE1Czbuu9iEjYSklO9TMiY7oSQKgBLhNTySAlJ1bsTIVmyU0KaorOEFDchZCfGqPzLhDQPctYvJ+T17VZTCHljhAQ/IC+FlJNfoqj4SxTVAimxvdCRfomCneKXKComJf0ufomiYlJqGPFLFJX5EkVlItYvUYh/JSVeBA5OSUlBsLdmMCFMkBJv' \
			b'TX+VwiYh+1UK68ENyfV4Y/arFFoCQsqJEPCrFHKqH6aQPAop9W5jgsyQkkpiJOV5PExKzbKt+y4mYesXKqpJUjZQeU04IWZMf0JMFYQlYmq5pMSkat6JmCzhKTFNESZfqpCYmZicK80dE9M8yFm/nJjXt8dNIeaNEbOQcqJPycs5uqXlHCjEdKR9SnaKfUpZ' \
			b'ztGtWc7RyXIODSP2Kc1yjhhrNy7nUP+xT8nLOTqznIOCqOgH+1cxhKk+5dyijiQJ2T6l9eCG5LozRTTTp9QS0D5lPgTsU8qp9in5MvYp5W5jgsz1KdN1HefxSJ9SsmzrvotJ2NqnXLmuI6Y7IaQKwGKfUsrjpE+547qOLrOuwxRd0qdkN+1TyrqOzqzrMA86' \
			b'8XwpIa9vJ5xCyELI+yAk7wjQLe0IgBJMR0pIdoqE9ELINfsBdLIfgIYRCekNIb2JWAkp/iMhPRPSG0J6JqRnQsYQpgg5tzdAkoQsIa0HNyTX441ZQmoJKCHzIVTjqRKSLyMh5W5jgswRMt0d4DweIaRk2da9yehGQvqVhNR0p4QUAVgkpJTHCSH9joT0GUKO' \
			b'RZcQkt2UkF4I6Q0hxwc565cT8r72y3lyEs59BWMN8ZR2SjklnJLtFql2M0TjNYvd0ppFFD06UqKxUySarFns1qxZ7GTNooYRiWbWLMZYu3HNovqf3eJmfGqKYnOrFfPksmlxQ3I93pgll+ZUyZUPofJSNoItszyxm1qQ2KULEmNQAidehNjx8sNu+9rDbuXa' \
			b'w5jDFEhSf4tAYn+nQNK1hw9kUWbZoUZ4utBC3BVGsu6wM+sOTXVxtjfBiCB09bvRlG5a6abdaDetY6h1S1Dr5Eihxk4Rap1ArVsDtU6gJmFEqHUGap2JWKEm/mM3reNuWme6aR130zoGXAxhCnDdXDfNJiELO+vBDcn1eGMWdloCCrt8CAg7OVXe8WVEntxt' \
			b'TJA5AHYpAM/iERJKlm3ddzEJW6nYraSipjulogjAIhWlPE6o2O3YTesyaByLLiGjCJaQsRMydoaM44Oc9cu7ade3QU3pppVu2tMQrWei9UtE6+VIicZOkWi9EK1fQ7ReiCbPRaL1hmi9iViJJv7nu2nxqSmK9Zu7aTYtbkiuxxuz5NKcKrnyISC5eoOt3jCr' \
			b'n6JUn1JKgxI49UymnpnUbwdSvxJImsMUSFJ/i0Bif6dA6vfppmneLIskwrNuGrsrjHqBUW9gNFYXZ3t7N+36toUpECoQehII9WxJ2S9ZUoIHPhIIiZNCqBdLyn6NJWUvlpQahkKoN5aUMdZ+tKRU/7MQGp+agFA/Zz2ZhVCSFjck1+ONOQjFnAqEJkIACPXG' \
			b'XLI3tpL9lHVkn1pHxqAYQj1bRPZsC9lvN4Tspw0hEwjFHCYQ0vpbgpD4O4FQX+0CoT5j+6gRnkJI3AVCvRg/9sb40VQXZ3s7hK5vM5bn8IGH8nGHOxkP7Nlso18y20DJpCMFFztFcInZRr/GbKMXsw0NI4LLmG3EWPvRbEP9z4MrPjUFrjlTjSTaLMSsBzck' \
			b'1+ONWYhprhVi+RAq+VWIGSONXiw0+inzjD41zzgPW6gm2bR13I2Z20i4leYZMfsp4aSiFwnH/k4Jt6N5Rp8xzzBFl1CO3ZRyYp7RG/MM8yBn/eJxP399G6sU2hXa3Q7t2KSjXzLpQLGkI6UdO0XaiUlHv8akoxeTDg0j0s6YdMRY+9GkQ/3P0y4+NUW7OZOO' \
			b'JNos7awHNyTX441Z2mmulXb5ECov5SS0M+YdrNgHCSZHu9TM4zxsoZ1k09Zx52PmNtJupe1HzH5KO6noRdqxv1PatTvSLmMAYoouoR27Ke3E/qM39h/mQc765bS7vk1SCu0K7W6HdoFpF5ZoF+RIacdOkXZBaBfW0C4I7SSMSLtgaBdMxEo78T9Pu+hvinZh' \
			b'jnY22iztrAc3JNfjjVnaaa6VdvkQkHbB0C4Y2gWhXZiiXUhpdxa20E6yaeu48zFzG2kXVtJOs5/STip6kXbs75R2YUfahQztxqJLaMduSrsgtAuGduODnPXLaXd9G54U2hXa3Q7t2LKxX7JsRIGkI6UdO0XaiWVjv8aysRfLRg0j0s5YNsZY+9GyUf3P0y4+' \
			b'NUW7OWvGJNos7awHNyTX441Z2mmulXb5EJB2xpSxN3aMvRgx9lMWjH1qwXgettBOsmnruPMxcxtpt9KCMWY/pZ1U9CLt2N8p7Xa0YOwzFoym6BLaiTAJ7cSCsTcWjOZBzvrltLu+zUoK7QrtboZ2A29IMixtSILiR0dCO3FS2g2yIcmwZkOSQTYk0TCUdoPZ' \
			b'kCTGOowbkqj/WdqNT03QbpjbhCSJNke7xIMbkuvBFMs07WKuhXYTIQDtBrMDyWC2Hxlk75FhauORId145Dxspp1m09Zx52PmttFuWLnxSMx+Qjut6CXaib8T2g07bjwyZDYeMUVnaSduQrtBNh4ZzMYj5kEnni+lHW08ArApxLuYeHAfpPE2yNcU+j0q/VCt' \
			b'epzLYwoel3ewbORId7BkJ8Ugq2vaw7JZAULyRKkI/H/cxbIxu1iaI+5iKfHOohA1inic2rqymdu60sab3bqSb2GIjtcD+CZzzNJQvcTNK8cdV3MhVV4KjamIP3H7yoapyMFlqEjlMFLxPGymombYVnmnqTlSxWwjIyd4mYyxKBIyar0vkZFyN5zvWtnsuGtl' \
			b'c45GSd6Z5aa467aVDbORf2XbyrHkOfOWjSgG9NfX9Ld5xZCEv0NLfwP5AVCSV7wiTLbQtGcgGdloqJhFIooik5AwKOibgN4p7haXBhDWJuGl0CIgKYwERFn4WPAoZBwDZTNIliByCo8laGSA8WC7/FNInMJBoRAMDHrb9dmi+BN9n9H0y2qedXzU7VGxqzJf' \
			b'ocanFPhG03nV07MqeVTGpG+jso2aNq9erW6NyhTVKGrPS/TmKqV5qi6XFWVOS+5h136mGs+VoqpD0oVREZL+U+WHOizM67D2sdRY5sV9UZPpOzrK/zqF1p0rtbYtik0VW1Rqubfe6uTNF8ICySVl16MQoLKrThQfiAWUhYNycNCaHZQFKUMoB/NGDP8dKMZt' \
			b'r8T0ynoV2tFPT+Vv1ZDmbbYeNmpKbybjo7ZsyE/RmOcas6EVu6IssezOFCb50M4RSjz181pRol0dRT3VqGO3D8OifV91N6EjdtWP9fhdEbzw8M4Jje8Vliq9RXbzGjhczYvkqH5xUMQ/8Ttl/8ABimtQwf4B75W3qj73V52Yt4b1yLW8aCJdZ1Snvz31SWtN' \
			b'H/iu2c9ruu4KNV1bes6Xarei2R6s2bDer0ir3c3L4IM12bBy5K++Hk225xjg6QTUM9BmDxoD3KjREm1GauSONNqCxcKlGo165c9bq6EsPkizYcfUvYJMYL8UErVOxzWX6rjpif0HqLlhpZprL3hpa29X1UE+r/Ll7d2oOv906q7dpO4aapsXvMT5e1F5KHHv' \
			b'9mUOan2faVyxbHq8lzlnFN2Skmv8Tj3T6naU3NUruIuUG6uhq3mXC+nY2zrl1rDTTj1UrMCbVG7vWLE1T2Gfght4Xvz6dkkPtfVlvO22NNrVTsI+rGfaUFbLeNsjaDL3JJrsISYqF2myYppSNNl1aLKuaLLH0WT+8Pra7IVn1sa8Q9vha9Zh4Ylsh40eI41y' \
			b'xWpsswqj5Uq0NCnQMqQrsyG+FTXW0HfvLlJlu9gQH/5neAWMpRmD9vp020X6DFKFEoNidf+67RK9hqtFH/aedjvvZ0+yGILWTjaUWv8ctdqFE6BcYu7hb2nhTjQZCDFmFIv0ejVabpnwU2g1uIa8X6bdzGKHk0UORdMtaDqMgRaGH2vSWTeg8cIVKb0j1hym' \
			b'rb1M9zkSrbhkwS5UQE3Y7a8JofAfRRnO7dEQX+3aJ1SG/sJXPFde8y5Tflh1T6kBw3o12FBy+ydXgg3FdemrH7aZp1wVe6kSPHsB7B9B7Q1P1Js16g4XGl7d+19Rd3ei7laO0SVaDqv62l/37lbLDY/Qza2eXstBkoqWK1ruqrRcKFruibQclOr+Wq6+Ai1X' \
			b'Fy1XtNx1abmuaLmn0nL1nUxZXL1Kuy2DuDL98AQWI7i97H1NrT7QRqTGzaZrNhOBlBZNda+aak+Tt/vRWLQF2FVrrDu0BtnLvq1vXgFxSHO5ormK5noumot6RtfwqkUJKXprs96qXwl8hleo+0mDXeHyg6LBigZ7LA3WX4sGK29ee2mwJ19ksPX7Qg9YDxrk' \
			b'Q0D3oNge+sGeNcrNi4Jr71vJUYtPFV09rquiz0aN/x9R8VHwaGO+RgPWt6UBd/iEzUo12AysCrk0t6rDJ1+pUNRhUYdPrQ6bU3XYGHXYJP8fVR0269VhU9ThlDr0og6bC9ThIyxXKOrwTtThs1CF7lQVOqMK0/+PqgrdelXoiiqc7iBzSW5Vg4+wfKEM85Vh' \
			b'vsfWc6Rp7tQm5Cp12XWM89HXsCqeYn2MJQlFcxXNtZvm4mCelTnbbqoLE6b/70N1te7VkZsXvoVhE3uFuhmaGfySRuseY/lB0WhFo+2o0VzRaBdrtPH/s9Fo97zUoO3vQKtVO2u2ZkG7NTSJhSO3V6np6OJGVyJwRp5U2VESdut4Umh76zsOdE7nOUobeJjX' \
			b'fr57RVyE9ognNem7e16wUPTdBfruKnWcv2Ed559ex/lddZx/DB3nH/Jel9VsZUHDFWu159c3LWtHL9ZkVHT3PU3g/SvCHbQ2PAmkwcqChqLBnlKDkQ4pq98v1mBcfs9kotP1r4h40OrwhL6z3D35goaiwZ6ZBmPBLRt47KDCpCifkbGGc6+QgND04JfnA558' \
			b'DULRYPeuwbjxXcGa0ntTYM/P2szhhGZNWxF1T75coGiue9FcLMfXtRzgZjUXFWZRXKniIksM1E4DDuXXDWmwYulfNNjlGozawDUvaLpZDVbevXIqrKYhfJ57LJb+RXM9RHM9kiFF0VxFc81rrr5Y9BfNtVZzobBfx+LKormeqebCbiN1Fvt7MdyHtMVPG1+d' \
			b'EkMDlf5KlFnHnzS+runHe9JmWOVHfPLq9Rpm85q0G9bYw1QbarTm8Bobjm9RWFGmGv5uMTz9usM9d8AdswP/ydkbZ9o8pyLn9vC6gWppehT6psemAf7h/MURdGaFvtHfEaIDVeXRE2gIdnPohloKFAe2fWjaB6gCEG2QBRA1yARULmQJNQxaO+M+LVA6+M3l' \
			b'psIUw2+MHDRRhf/RL/ZywG+F1n1w3aC1DEQCTQUrGttNDTKNuquXp1BHYNvHnb8wVFTjHaXS75pK0P5r/1HsLcberY0fhBJBMKxISIu8aCf/1UMj2v3sHqUrzKcLShpaHX64taJPfk0ms+Kk4heoT5OrPKBPYSFZ/UkWAJRn/1De+YOt4/8zPwP77JOnUN+j' \
			b'G33+CsSd7lBeu6fOK/CFPjcOeQbq7/bPQTtxtaM89jvksZ/LZg3MqCErdY+/Qz7boZ7JOsS2+h++lKQujH8vqE/ugPo111QcQ7Y48A1kmC4UT+XSSdGgtjTbl02VVC2lFeQz7GxkhHBFnpNtN66WxYUqtP7fcaniWomWNzTlEvZjKXdY6hAOlCCXOL6ltlLy' \
			b'/XTpQzz8MjWkNYEvP7E2aq4RSLODMFyltYNvnucHvX+G3J3xfmW96AP2/4onc49lgslcnkdbTfjJ5Su5mwZ36ovkClyvvp1h7+YqDi6xOt8U8QX+gN0CbpOgycKWltlc1DidaaD1tkaKdLmOhtocMoftOIqjdhlXH129xXdDPUI5w+gXvftuW/gXHSx0TdH/' \
			b'W8XKHZ7rwSLjbkCz+8N1HFxifp9GVj91O6NBsXfa1vrDDgeO7e0S0FPExBKU7x0XNT0jOtg3ep4Hi8weAxcZudhbVeMA+E4HDso/LAguufwwSGls040NA3mmB4tMflRpTl7WtrfwGG3OH84PnDjI3lh74BTY5c9zOU4MR8Xe71LXt4UyrQ7BHcK7aYzBNMia' \
			b'GyWunsPpBOoLgz/ctDi0j9NQcXop6HY0mxpsdzg/sNsvZ1juOS+jX5pQHf/P+77sGMPVM1xNzaf0AyLQ+PDwmDjbvVv0yDM8+aGtwocZcesPz/VgkZkY27tSPqBVx3UdXIr7DFY9UmPbUvpTjWmxIaGxzdmBVhbZG4mn1i172v1YGStXb35gqejVGXFoDs/1' \
			b'YJGZGFnbT6/Wu+tWd3ikA23OLn2YS7OMMm1ugN3huR4sMvlRpp0bIIrGvo2wPzzegXaflz7MhVoGoLa2Q7Q3fqYHi8yjD0BZ0di1LaKd+GMeaH596cNctsVGanNzDIfnerDB78QQ0YrmeHkHlSRha0d0qgMaa7I7XHbgOOh637g2gpYvVCv8dk32Bpf8xEhL' \
			b'aayTjRXX5zzTg0VmYljpURtrIh2P0XBxydU7OewypocFxbVxM6NAdpLnOhpyOFzhgV9uph//DmJjEdo+KuR3b9NWYPZq25MV3x02Hbj8besz54euUbw8gIEeNusJ4ZJr8PKRKJkBfsdzv1epDobDZQdn7dKn5w9czPoY4S4dLFbbR6tuWzHgQuubP7jqLh8T' \
			b'uwabkGvTDbj8/gEHZ6x5UBiLB651f9QIzg6WtO1DaY+rJC6dX96sLLrDEx4oyzv646q8fOSuKI1zAcGtOsqRHLxw/nKDsCJmGTGrD+VIDxazfYY2rwVPl7zP4u5A93Zw3RbTtm443N3BdXszI5pXMyWBSx0ffNByRfN/t0DHn5NYzGXiZ1WQuYPlZ6flo89J' \
			b'fprDcz1YZIol32aRcYfnerDITIyNFpGZFpn+8FwPFplip7hZZIbDcz1YZCYGV4vITIoM7nz7TA8WmWJ+uVlk6sNzPXgv0bJCd7PINIfnerDI1IfXtEVwLUt22yY6MLpahw5Y7LQJGO2dzTegf24FCQSBfECVOTSmgOrFXbor2ee2zfuGyk3/s+9w5hsrnJ5A' \
			b'8Ur/N0GS2tmtjVFseC/btmf3dCMp8oF7fQ+UXRLLwCJJIuhJ7FCs0B1Eh8MCtZyEQqLsT8RXRRfX7FNqcG91s686713en+xXrnuV4/ppLodQYcpwL3RH241gY+a2DtEmGzPDMwKO0OA17cQslRwcnne0wpl7PcGPLlA/X7/8//jXZTs='

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
		# ('CURLYL_L_PARENL', r'{\s*\\left\s*\('),
		# ('R_PARENR_CURLYR', r'\\right\s*\)\s*}'),
		('L_DOT',         r'\\left\s*\.'),
		('L_PARENL',      r'\\left\s*\('),
		('R_PARENR',      r'\\right\s*\)'),
		('L_BRACKL',      r'\\left\s*\['),
		('R_BRACKR',      r'\\right\s*\]'),
		('L_BAR',         r'\\left\s*\|'),
		('R_BAR',         r'\\right\s*\|'),
		('L_SLASHCURLYL', r'\\left\s*\\{'),
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

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add, expr_var):     return PopConfs (_expr_intg (expr_add, expr_var, (expr_sub, expr_super)))
	def expr_intg_2        (self, INTG, expr_super, expr_add, expr_var):               return PopConfs (_expr_intg (expr_add, expr_var, (AST.Zero, expr_super)))
	def expr_intg_3        (self, INTG, expr_add, expr_var):                           return PopConfs (_expr_intg (expr_add, expr_var))
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

	def expr_attr_1        (self, expr_diffp_ics, ATTR, expr_pcommas):                 return PopConfs (AST ('.', expr_diffp_ics, (ATTR.grp [0] or ATTR.grp [1]).replace ('\\', ''), expr_pcommas.comma if expr_pcommas.is_comma else (expr_pcommas,)))
	def expr_attr_2        (self, expr_diffp_ics, ATTR):                               return PopConfs (AST ('.', expr_diffp_ics, (ATTR.grp [0] or ATTR.grp [1]).replace ('\\', '')))
	def expr_attr_3        (self, expr_idx):                                           return expr_idx

	def expr_idx_1         (self, expr_diffp_ics, expr_bcommas):                       return PopConfs (AST ('-idx', expr_diffp_ics, expr_bcommas.comma if expr_bcommas.is_comma else (expr_bcommas,)))
	def expr_idx_2         (self, expr_abs):                                           return expr_abs

	def expr_abs_1         (self, L_BAR, expr_commas, R_BAR):                          return AST ('|', expr_commas) if not expr_commas.is_comma_empty else _raise (SyntaxError ('absolute value expecting an expression'))
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                            return AST ('|', expr_commas) if not expr_commas.is_comma_empty else _raise (SyntaxError ('absolute value expecting an expression'))
	def expr_abs_3         (self, expr_paren):                                         return expr_paren

	def expr_paren_1       (self, expr_pcommas):                                       return AST ('(', expr_pcommas, is_paren_tex = expr_pcommas.is_commas_tex)
	def expr_paren_2       (self, expr_bracket):                                       return expr_bracket
	# def expr_pcommas_1     (self, CURLYL_L_PARENL, expr_commas, R_PARENR_CURLYR):      return expr_commas.setkw (is_commas_tex = True)
	def expr_pcommas_1     (self, CURLYL, L_PARENL, expr_commas, R_PARENR, CURLYR):    return expr_commas.setkw (is_commas_tex = True)
	def expr_pcommas_2     (self, L_PARENL, expr_commas, R_PARENR):                    return expr_commas
	def expr_pcommas_3     (self, PARENL, expr_commas, PARENR):                        return expr_commas

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
		'COMMA'          : ',',
		'PARENL'         : '(',
		'PARENR'         : ')',
		'CURLYR'         : '}',
		'BRACKR'         : ']',
		'BAR'            : '|',
		'SLASHCURLYR'    : '\\}',
		'L_PARENL'       : '\\left(',
		'L_BAR'          : '\\left|',
		'R_PARENR'       : ' \\right)',
		'R_CURLYR'       : ' \\right}',
		'R_BRACKR'       : ' \\right]',
		'R_BAR'          : ' \\right|',
		'R_SLASHCURLYR'  : ' \\right\\}',
		# 'R_PARENR_CURLYR': ' \\right)}',
	}

	_AUTOCOMPLETE_COMMA_CLOSE = {
		'CURLYL'         : 'CURLYR',
		'PARENL'         : 'PARENR',
		'BRACKL'         : 'BRACKR',
		'SLASHCURLYL'    : 'CURLYR',
		'SLASHBRACKL'    : 'BRACKR',
		'L_PARENL'       : 'R_PARENR',
		'L_BRACKL'       : 'R_BRACKR',
		'L_SLASHCURLYL'  : 'R_SLASHCURLYR',
		# 'CURLYL_L_PARENL': 'R_PARENR_CURLYR',
	}

	def _insert_symbol (self, sym, tokinc = 0):
		tokidx       = self.tokidx
		self.tokidx += tokinc

		for sym in ((sym,) if isinstance (sym, str) else sym):
			if sym in self.TOKENS:
				self.tokens.insert (tokidx, sym if isinstance (sym, Token) else Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

				if self.autocompleting:
					if sym not in self._AUTOCOMPLETE_CONTINUE:
						self.autocompleting = False
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
		s    = self.stack [-1]
		vars = set ()
		reds = [s.red]

		while reds:
			ast = reds.pop ()

			if not ast.is_var:
				reds.extend (filter (lambda a: isinstance (a, tuple), ast))
			else:
				if not (ast.is_differential or ast.is_part_any):
					vars.add (ast.var)

		vars = vars - {'_'} - {''} - {ast.var for ast in AST.CONSTS}

		if len (vars) != 1:
			return self._insert_symbol ('expr_var')

		var  = vars.pop ()
		dvar = f'd{var}'

		self.autocomplete.append (f' {dvar}')

		return self._insert_symbol (Token ('VAR', dvar, self.pos, (None, 'd', var, None, None)))

	def parse_getextrastate (self):
		return (self.autocomplete [:], self.autocompleting, self.erridx, self.has_error)

	def parse_setextrastate (self, state):
		self.autocomplete, self.autocompleting, self.erridx, self.has_error = state

	def parse_result (self, red, erridx, autocomplete):
		res             = (red is None, bool (self.rederr), -erridx if erridx is not None else float ('-inf'), len (autocomplete), self.parse_idx, (red, erridx, autocomplete, self.rederr))
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
		stack          = self.stack

		if isinstance (self.rederr, Incomplete):
			return self.parse_result (self.rederr.red, self.tok.pos, [])

		if self.tok != '$end':
			return self.parse_result (None, self.pos, [])

		irule, pos = self.strules [self.stidx] [0]
		rule       = self.rules [irule]

		if pos == 1:
			if rule == ('expr_func', ('FUNC', 'expr_neg_arg')):
				return self._insert_symbol (('PARENL', 'PARENR'))

			if rule == ('expr_paren', ('PARENL', 'expr_commas', 'PARENR')) and stack [-2].sym == 'expr_mul_imp' and \
					(stack [-2].red.is_attr or (stack [-2].red.is_var and stack [-2].red.var in _SP_USER_FUNCS)):
				return self._insert_symbol ('PARENR')

		if pos and rule [1] [pos - 1] == 'expr_commas' and rule [0] not in {'expr_sum', 'expr_abs', 'expr_func', 'expr_subs', 'subsvars'}: # {'expr_abs', 'expr_ufunc', 'varass'}:
			return self._parse_autocomplete_expr_commas (rule, pos)

		if rule [0] == 'expr_intg' and pos == len (rule [1]) - 1 and self.autocompleting:
			return self._parse_autocomplete_expr_intg ()

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_sub' and stack [-1 - len (rule [1])].sym == 'INTG':
				return self._insert_symbol ('CARET1')

			return self.parse_result (None, self.pos, []) if self.rederr else False

		return self._insert_symbol (rule [1] [pos])

	def parse_success (self, red):
		self.parse_result (red, self.erridx, self.autocomplete)

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

	# a = p.parse (r"""Limit({|xyzd|}, x, 'str' or 2 or partialx)[\int_{1e-100 || partial}^{partialx or dy} \{} dx, oo zoo**b * 1e+100 <= 1. * {-1} = \{}, \sqrt[-1]{0.1**{partial or None}}] ^^ sqrt(partialx)[oo zoo] + \sqrt[-1.0]{1e+100!} if \[d^6 / dx**1 dz**2 dz**3 (oo zoo 'str') + d^4 / dz**1 dy**3 (\[-1.0]), \int \['str' 'str' dy] dx] else {|(\lim_{x \to 'str'} zoo {|partial|}d**6/dy**2 dy**3 dy**1 partial)[(True, zoo, True)**{oo zoo None}]|} if \[[[partial[1.] {0: partialx, partialx: dx, 'str': b} {-{1.0 * 0.1}} if (False:dx, 1e+100 * 1e+100 b) else {|True**partialx|}, \[0] \[partialy] / Limit(\{}, x, 2) not in a ^^ zoo ^^ 1e-100]], [[Sum({} / {}, (x, lambda x: False ^^ partialx ^^ 0.1, Sum(dx, (x, b, 'str'))[-{1 'str' False}, partialx && 'str' && a, oo:dy])), ln(x) \sqrt['str' / 0]{d**3}/dx**3 Truelambda x, y, z:a if a else b if partialy]], [[lambda: {1e-100, oo zoo, 1e-100} / \[b || 0.1 || None, \{}, \[[dy, c]]], {}]]] else lambda x:ln({}) if {\int_b^p artial * 1e+100 dx or \['str'] or 2 if partialx else 1e+100} else [] if {|{dz,} / [partial]|} and B/a * sePolynomialError(True * {-1}, d^4 / dy**2 dz**2 (partialx), 1e-100 && 1.) Sum(\[1, 1e+100], (x, {'str', 1.}, \sqrt[1]{partial})) and {d^5 / dz**2 dy**1 dx**2 (oo zoo && xyzd), {dz 'str' * 1. && lambda x, y, (z:zoo && lambda x), (y:0)}} else {}""")
	# a = p.parse (r"""\begin{cases} \sum_{x = \lim_{x \to \left[ \right]} \left(\sqrt[1{e}{+100}]{False} + 1{e}{+100} + \infty \widetilde\infty \right)}^{\left\{\neg\ \partial x\left[1., \emptyset, \text{'str'} \right] \vee \lambda{:} \partial \vee 0.1 \vee dz \vee \frac{\left(d^2 \right)}{dx^1 dz^1} - \frac{1}{\sqrt[\infty]{\partial}} \right\}} \left(\frac{\frac{x}{y}\ zd}{dz\ c\ dz \cdot 1{e}{+100}}, -\left(\partial x + dz + 1.0 \right), {-2}{:}{-{1 \cdot 2 \cdot 1.0}}{:}\left\{\partial x, 1.0 \right\} \right) & \text{for}\: \left(\lim_{x \to -1.0} 0^o o \wedge \log_\partial\left(ypartialx \right) a! \wedge \sqrt[xyzd]{\infty}\ \widetilde\infty \cap \frac{\partial^3}{\partial x^1\partial z^2}\left(0.1 \right) \cap \frac{\partial^9}{\partial z^3\partial y^3\partial x^3}\left(a \right) \right) + \left(\lim_{x \to \begin{bmatrix} b & True & \text{'str'} \\ dx & 1.0 & 0.1 \end{bmatrix}} -1 \ne dx, \begin{cases} \infty \widetilde\infty \wedge \partial x \wedge None & \text{for}\: dz! \\ \lambda & \text{otherwise} \end{cases}{:}\partial y, \left\{\left\{dy{:} \partial y \right\}, \left(False{:}\partial x{:}\emptyset \right), \lim_{x \to \partial} \partial x \right\} \right) + \frac{\begin{bmatrix} \infty \end{bmatrix}}{\begin{bmatrix} \emptyset \\ \partial y \end{bmatrix}} \le \ln\left(\left\{None, \infty \widetilde\infty, dy \right\} \right) \\ \left(\operatorname{GeometryError}\left( \right) \wedge \ln\left(x \right) - 1.00 \right) \left\{dx{:} 0.1 \right\} \left\{1.0{:} \partial x \right\} \sum_{x = 1{e}{-100}}^p artial\ True \cdot \left\{\text{'str'}{:} \begin{bmatrix} xyzd \\ dy \end{bmatrix} \right\} \vee \left(\left\{\emptyset \right\} \cup \frac{True}{\partial y} \cup \left|\partial x \right| \right) \cap \left(\begin{bmatrix} True \\ \text{'str'} \end{bmatrix} \cup \widetilde\infty \cdot 1.\ True \cup -\partial x \right) \cap \operatorname{Sum}\left(\left(\left( \right) \mapsto 1{e}{+100} \right), \left(x, \infty \widetilde\infty\left[1{e}{-100} \right], c \vee \partial x \vee None \right) \right) \vee \left(\cot^{-1}\left(\emptyset \right), \int dx \ dx \right)! & \text{for}\: \left[\left|\left(-1 \right) \right|, \frac{\partial^4}{\partial x^2\partial z^2}\left(\log_{\emptyset}\left(-1.0 \right) \right) \right]\left[loglambda\ x, y, z{:}\begin{cases} \infty \widetilde\infty & \text{for}\: 1{e}{-100} \\ dy & \text{for}\: dy \end{cases}, \operatorname{Sum}\left(False, \left(x, False, 0 \right) \right) \cap \sqrt[False]{2} \cap \frac{1}{dx\ a!}, \gcd\left(\left(dy \vee \partial x \right)^{1.0^{\partial x}}, \operatorname{Sum}\left(b{:}None, \left(x, -1 + 1.0 + \text{'str'}, xyzd! \right) \right), \left|-1 \right| + 1.0 \cdot 1.0 \right) \right] \\ \left|\begin{cases} \left(dx\left[\partial, \emptyset \right] \wedge \left(False \vee \partial x \right) \right) \left(\neg\ -1^{dy} \right) \frac{d^2}{dx^2}\left(dx \right) & \text{for}\: 1{e}{+100} \\ dy & \text{for}\: 1{e}{-100} \end{cases} \right| & \text{otherwise} \end{cases}""")
	# a = p.parse (r"""Eq(Union(dy2 - 2.0651337529406422e-09*notinxyzd, Union(Complement(diff(z20notin)*diff(s)*partialxb, diff(diff(diff(-1.0)))), Complement(diff(diff(diff(-1.0))), diff(z20notin)*diff(s)*partialxb))), Or(Union(Complement(Union(Complement(Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))), partial.chCa.dcGNDli().XG()), Complement(partial.chCa.dcGNDli().XG(), Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))))), diff(diff(dx))**1*e - 100), Complement(diff(diff(dx))**1*e - 100, Union(Complement(Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))), partial.chCa.dcGNDli().XG()), Complement(partial.chCa.dcGNDli().XG(), Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))))))), 0.1 - bcorx0orc)); slice(None); abs(Matrix([Integers])); Matrix([[[Eq(c, 2)]], [[{Lambda: oo}]], [[lambdax, slice(y, 2)]]])""")

	# a = p.parse (r"""\sec(:'and\.dy+xyzd|_{\sum_{x=w_{1}}^2\tilde\infty=(\partialx),("s":z20)=w_{1}1.1e-100,318059230463951.06||1e100=\intadt}and{1.}.QnO.L1p().HTxLHYK(),$lV(real=True,commutative=True),\left.-.1/\Xi\right|_{\substack{-dy=\[1.6045630679378065e-16,oo,]}}&&f()or\theta_{84}if"s"elsebif0else\emptysetifaelsex0&&\partial,-0.00399730906428841,\partialyif-Falseelse\emptysetorcif\partialx+-1else[[[1.176573205446333e-05]]]if\frac\partialx1else(((-.1))))""")
	# a = p.parse (r"""Union(Complement(Union(Complement(Matrix([Le(Union(Complement(Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)), a), Complement(a, Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)))), ('s', 1.0, dx))])**(a[0.1, a])**partial**3 / (partialz**3*1e-100), diff(diff(FiniteSet(2, partialy)))), Complement(diff(diff(FiniteSet(2, partialy))), Matrix([Le(Union(Complement(Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)), a), Complement(a, Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)))), ('s', 1.0, dx))])**(a[0.1, a])**partial**3 / (partialz**3*1e-100))), -xyzd*FiniteSet()), Complement(-xyzd*FiniteSet(), Union(Complement(Matrix([Le(Union(Complement(Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)), a), Complement(a, Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)))), ('s', 1.0, dx))])**(a[0.1, a])**partial**3 / (partialz**3*1e-100), diff(diff(FiniteSet(2, partialy)))), Complement(diff(diff(FiniteSet(2, partialy))), Matrix([Le(Union(Complement(Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)), a), Complement(a, Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)))), ('s', 1.0, dx))])**(a[0.1, a])**partial**3 / (partialz**3*1e-100)))))""")
	# a = p.parse (r"""Union(Complement(Union(Complement(((FiniteSet(diff(partialx), -tau57, [[-28832738.092809968, 1., 's']]), Sum(xanddz*Matrix([-1, False]), (x, xyzdin1e + 100*notin*diff(partialyin)*diff(s), partial)))), (FiniteSet(-13.574245287492392, partialx, dx)**d**5 / (dy**3*dz**2*Noneord**1)) / (dz**1*partialx**{}*orz20)), Complement((FiniteSet(-13.574245287492392, partialx, dx)**d**5 / (dy**3*dz**2*Noneord**1)) / (dz**1*partialx**{}*orz20), ((FiniteSet(diff(partialx), -tau57, [[-28832738.092809968, 1., 's']]), Sum(xanddz*Matrix([-1, False]), (x, xyzdin1e + 100*notin*diff(partialyin)*diff(s), partial)))))), 0.006826903881753888), Complement(0.006826903881753888, Union(Complement(((FiniteSet(diff(partialx), -tau57, [[-28832738.092809968, 1., 's']]), Sum(xanddz*Matrix([-1, False]), (x, xyzdin1e + 100*notin*diff(partialyin)*diff(s), partial)))), (FiniteSet(-13.574245287492392, partialx, dx)**d**5 / (dy**3*dz**2*Noneord**1)) / (dz**1*partialx**{}*orz20)), Complement((FiniteSet(-13.574245287492392, partialx, dx)**d**5 / (dy**3*dz**2*Noneord**1)) / (dz**1*partialx**{}*orz20), ((FiniteSet(diff(partialx), -tau57, [[-28832738.092809968, 1., 's']]), Sum(xanddz*Matrix([-1, False]), (x, xyzdin1e + 100*notin*diff(partialyin)*diff(s), partial)))))))); Derivative(dy, y); Function('u', commutative = True, real = True); psi, y1""")

	# for v, k in sorted (((v, k) for k, v in p.reds.items ()), reverse = True):
	# 	print (f'{v} - {k}')
	# print (f'total: {sum (p.reds.values ())}')


	# a = p.parse (r"dsolve (y(x)'' + 11 y(x)' + 24 y(x), ics = {y(0): 0, y(x)'(0): -7})")

	# a = p.parse (r"a.b{\left(x\right)}")
	a = p.parse (r"a.b{(x)}")
	# a = p.parse (r"a.b(x)")
	print (a)


	# a = sym.ast2spt (a)
	# print (a)
