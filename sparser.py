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
			b'eJztnXmv5DaS4L/MAl0PyAQkkrrqv/LRs8b4mrLdO42CYZTt6oGxvuCyvT1ozHffOKlgJqVU5lPWy4MovZJEUbyCjJ9IBpnPXv3li/c/+/izT/+y+cv/evPz93DS24+/+fzFyw8//Rgu48X7X738+O8f08P3Xr54/9/xMl589devPn3/87/rFZw//exL+P9v' \
			b'L17C/1/8/RN6Bmd6/wN69sXHL77433z53of/9s37L7748Au5/uSFur43Xv5tvPycLymEmIa/woWcajk7OH/y0adfUbgfffrZJ3qu9cJRgiigmMGduy8pC1+9p0/48sNPPv/y7198iMn46NMv/w1z/BXl7qNPyDv9/x8v8fnHVKSfoR8pHChCKhj+//3PPvnk' \
			b'BZxfcqm/1FJ/qaX+kh5SRl9qqYvbCz6PSX6ZZADvPvwP+O/FJ5/D/x+89zE9Q9dPP5Bixqv3xsu/jZdSzB9+/MWHmKaXH32C5w//830slxdfUsFgkF9yNiDNX+oZC/iDj/720Qf4xvsicPb3+cckDyg7Fc1/fvHh++Thg4/++lesQ59+RNXwfUr0i08/wELG' \
			b'B5/h+5+8+PyLLz+TJGqtIYf/w6LBU80ygyjf/3e4fPvHt2//fP3b2z/N9Vu4/u71b29+/+aX3775/tsf3/7++jfzGC7f/PNXePLDnz/p9c9v/uub17/9l96+/ePXN7+NN9/C5U+vf//mu19+lKvffvl/4xXH9/bN27ffxatf45UG8/rbePnD9/+Mrr//HiP6' \
			b'x+vvftfrXykCdv7j5+/GNP/jH78mN9/88N3bMaUxQz/+MOZtdP39zW/x+qc/fvzmh59iYN/98duP/22KRi+//eHnX2wxxVT99vo7GxRc6O2fb+KT199/Hz29jpn759s3Y06plGIOME+m4OODP37+4Zef44P/jin64effY5K+G3MDcrbF9ufrWMg//xJj/sN6' \
			b'ef3z94m7Lddvv/vlp59ex9tfYmDfQiH83zej0Njf72/+ueMSb394892beANV9OexdH59+/svMTGx2sS8/fLjmH8KNLl5a9785sc/X/84lii/+fXm1bNt6zdt87DhixYvGof/+U3TPsgt3NFVQG+bptls5ZE68J3X9+CFoE54Sb62HbnUm2cBXMFb/RAdAjqE' \
			b'oA7bAS98zf914OD9g3VyzZ5T56wTXsJV3fF/XbfZ1sODOOElXOGzfgN52PYPfA8XcMaA8BwG/C9sWvBRc2JHJ73dNhWF2myetZQJiQXuO8plxUlqN88ceujxb3Tq7K3r5QLdMBAop7qJVyQc12+e1VjAbtNzmhwGSYlwjv/r4LljmcAdXmKxkhBQlg/mVq+N' \
			b'u+PTlqIL9BcafRzwAhMp7pz0zTaII99DGt1AuXfRoaHS6eO9r8iD33EYfWwDZSo0/F/LQWFSAictyK3KBtIWOHEd/9dCIC0/9FjQJPUW6gtWH3nQ1vog9CJbTlLAFHA9hIiwHEkwXPHJydtbF+QC3fB1kK6HMmhZ/nrb7DlJLUmcw/7tzouh3rvN+Gj61Mnt' \
			b'3aYvbUNnUja2DEnEjkO96+CMA+SIRVI3eg8tm6okVBPfcOIwemytjpMQH+WdU6dtoJoKsT4D6Tb4aNNjDjcoOi/1df8pKjpQKYc9QS1JPW0D6QWsJ8Omr7RNgJ+aqirUYFACqGBARTad6gJ0jo6jS88u/egysMv4lqvIRQREDYTy7D3/1w4xeerUVdYJL/Fq' \
			b'4P+g2B4exku8arg16Ct4SXWgxQSN1RBvqdXEWxAuaaaB/al2xZBZLvWGW0Id+L8OHtWc/zrQJZUjNl+5cHrBuhsaKoEicCPDe+aEBOJQqYgP1Rt1JZFhzd9g4864qws4UEo7qapS8nAPrZ/80B94ZN2D1Y8qX8f/dfCO43dQkTvSFlCtn/WYKqFZv+kpFtD+' \
			b'z+rA4Nt4h7WtdZpsesgaMuQebhkNARtCLxW14cLQViS11KtgwPFZO0qMbtsxWcOmJQE4kA6UpCpRuvUU/q7TeAsporgqao5yFWq58vHC6YXXC64yWEIxPLwbkgjFZbzbOgoSsMe3+gSyUzOxG/6vw5Lh2uH4Eq+qDVcxV/OdtgKH8mS1DVUJ70ZcOyop9DTw' \
			b'fx2KVEqAtBOVYsf/mS+iTsDZtPwffQxxkuQSrxp9+CC3cKcPuIFBivqG6kHQetDqh0lLn12Nvo7fJ/IJ1+gD/NoSF7iCD71XUApQJjVUJshpIKZjs4Fa5jeg/KBagVYAGUG7HTbQjKGgBrh0UHgB/uBVKO8aCxPerx26d/DXw98AMsdaW9f4R4oToqnh46+G' \
			b'SorewBd8K9UAgRpqfw0fL3UF9zXewzOojaB5PL4DniEdNSSkhpTUkL4aCqWGHNUQSY2xgF6rob3V8OEDl4DcGkqmBoU9wBE2Q7MZ2s3QbQYIGbzCcwgA3gelVYNGGCD4Ci6rGr4pNvjVC8wHHxV4rCDlHXyHbUDGoG5RRKDGO2xlkH5IPqa+wtRjwPgHL0FJ' \
			b'1lCUNfirwSM0/j5sQHg9uIHS6rtND67DZoBIMbWQVSgW1PTQ0PGjG5oifquANgft3dGnLFQ30C5Qn+FbDj5eQW11hJzaYeYhwRUqN5AC3MNtXyO3sDhRNvhdD5cP2LIhbSD+Zyh3dEDZPcBjTDfcYtIfiNzkC3OET6E+oDPUCXpa09NX+E1A9xR2qTM3Vmee' \
			b'DSz8mqWMUiOpD7VUJa4jKF28rYOcGzm38rrTqqfv6QtOAqRK8FB00I3XJxR0XwR9H4IWMhR534G8n3nW7N6Jxq89a/hOFLxjJAy+1Ibbrw2vnvGnZZHzrcuZSh/beUOffiKsr2koixVBGJIH+Ip8DDakMkgW9il3MGrud9hcvvscppVyryLuVMDdqidVLlvZ' \
			b'TCXjypWpVFKRbO2xtWa3vkzUE6gbKI5GFXPF8pB2oe1B6r7Ud63ptl6b+qx1mOutVtQiqlVEhezkBuK1n15pG5PemG/lXj00nQjX7zW2II0t7De2Z5Q9eq+REJ3iumaeFwV+2wr8GSWIq44rAr99gaN2KXK+fTk/o0LisTf5oGp1rI2f+A0Ev8GJo7bI+/rl' \
			b'7YOIu5WPBTnJiGyjA7f8md7iNwsUS4clhCUFOWmxXJtSF66+LoCUmyLlO5ByW6R8B1LuipRvXcrPBh0t4374wFMnlG/ujlfM7TLwctaBl7YqfaM7aG2YUW5fYvlCXaOTKg6Np+EAa9tIUP7xQemnfMVzZjQ4R5MqbCNxbHi+4vC4I3j0605GHXmQ8RlJuAzM' \
			b'r6Z0QjF8uQOdA3JmpjcFMXcg7meNEEZsKmsxqqyDKNEgH3w9D9P07K3nfjtqXFTaKBA0u/RpQZaZuHc0adrLrFgtnwk9C6/nAdV+EONHmWGLI3BeZO1YtvxR+UxMHsWx5+k4I2EqF1QUPJP+rBH4u3RevZFh3ZbT1nKSWk5Sx33FCp5VWB36JIYi9oVIbllV' \
			b'dyy4ri+FukKhdqwRO24GHTeDbpgrW1WEpYyXljGrjo5VR1+Vivt4CHRqGsFlK11HueuddtXKV93tf9W9orUz7qGslroHWUPCHK+DcmVl0w3KF0TqeEFbke/tyRcXJjpZugbnIshrFSQtNiwt9BYFi5JysiwU22gR6fWLtKbPJSn8ssjgUnu1mHhqenUvmGRO' \
			b'loXY99FScVkuy53qQWmpF9tSecThFa6cxfZZDHjvoHHihjxktc0yx9LnxtrQB5NZwdXU4rOXLymx0ZAXPFWe0p4vpz2/omV7KJQijCcXBi2Y5JYVdltWqOWJY0IWMT2lmETNeScfqSKblnsbRSbvXibeC2J4lxeeeGSLCLFt4VnINq4opj5+Ec+7wkwo5f1u' \
			b'sV7K+x2qnyEoAnpZ3iprJtqocMQ2ivpFtE0C22jj6jjqSfFH9tBJ/2rgjnAR2jkbSVWVUj7711LFM9cYqJPlDe5xaxJelW3c7mPkQbZdwmUsVHUaUpJQ1li5SztdVxtyz/L4BTky1lNxZygIwHiQ6BkNEX3NpuUuMTEmx1A6TE8l7r6RTuzezgyYQJ4QpY+Y' \
			b'x0YXa0qtS79q3jLK2oIWsS39ZuGdr1cUSh+XEzheTuB4OYEbK4IP8Y4WEjheSEAN3XG7Z9dxxKqXQRHeabOQ+sZJ3fBHXsOVoW3lU0+m80o7P37VB7fDsnPpPTSfV7hWqtgFXrUEScsVZXfiQExXyu7ksusfscATVxcSqruqoPrUdW590d3XrLtxMSi3AVfa' \
			b'wKltwJeiO7XoypKQK1cfMvnXNaUNnDoYWZU2cNVtoNa1M1CsvEwVTzhQ8UA/G4snEK/X31/zstDGP+g6DT/+Pg+Z/XtZD+B1PYB/0IUCbDAuL+CJYyWrZP8gs/FsuEqemoof+0buG52Ub8TFacSh0jRKCmSfajL68mL0xSkRj63c74+js1kSx0ylQ338ssP1' \
			b'LVR4tCejkc6yVOw2xFmL6hh29zoNE+5Nzh1Vj1dDICcGQGSvG8pqiFupKW0ojf4WRImmd55N7zyb3kmL9tKivZgt4Vkw37Tcvvl3wYolyll6A40qVVf2dl1x6R7X7yAnrub6adwT/oolzpN0fsNUD2LDJhe99lJkUbSXBXlebK16FmnPfaJ+oF4VWW14ngnw' \
			b'vDcjSbplX7So72vapJHVnYRZsRlIx1qvY88dB9HxN1LHVafjVPWiJ2PHCbJfuvLXS0XubIcH7YV/zf3q8CAft9IXDtIXDtSvJVWiX77S6x4N3bkeNrLGu/fy8mR1D+iBqnXgah24Wofy1XUT9cuTgItRy60LuuWWy8NwZVz8hLUTUNUb0sQDnSG65kF+D7XB' \
			b'fW0gACit0pJuvSVhSRWB343A8RupkU+ghj+BGv4EwkqwcfJ1j24tP6plJ2ss5Zbua7l3eE8htWWp27l7cj0VPpReS1++bIKlix4CScCugCFxdbzxUc07lUH4uG82bpqNez2XhnzdDRkLqsMq0fGp59MgUodkdKVVnvkjqtOpWtnmv5aN6amRUTvlXdWp/fZF' \
			b'HOdWkkMp5PNvUROwkKnuB637Tuo8cqZw5bq5AjEODJJBpMojddXmVYVfiPSD6mhqgj+qPpgaHguMagBudRtInlwkJGYudBQYdyrizwtQOUGOMHcdTn5hKrmIG8njbu4oa5AvSL2UG5UT1zyUpxUmJjHXCqlSOhGGVjXHFRA3wYpbDmIrGmIviT+m4B7LFX/a' \
			b'Cn8xCWKusdJD3DXuXog/To0/XYw/bItpwI03oOY4XM4MlcBhjcGxcRwXr6CQcC87NHbCZoCb2uBGK7hrKZYnFiiWKBYplimOsWN1w8LFsXuocQ73jsLNinBJJe6Hh2P5OI6PO37h5v4B5Q1uuI4a11DjAmrcVg9X1uEGfLjQDrdsw6XwIASHo6rQvBza8eM3' \
			b'JBojYhuHeuVwURFa1uHaa9ywEbcawclOyJOHvPhqgCqzhdjgwbaG1G4h9VuQ9BZSsQ14XW22AzhX+Bwu4Q+ls0XxbFE+WxTMFjK19fQM3kOdsIUi2WID2qKgtqgIttimtqgKth7fg8Rvsflvse1vsYFtseVvsdlvPQYBot0OGA4+gtawxSa9haq2bfEx5GIL' \
			b'JbqFkt1iYA36CPgEc4CtdYu1Zdvj61C1tgMmAsp82+AfBN5R+uENDBzPUEuxOLYYisdkDJg8TFSgK4yh6bksUMFta/IRKG1BcozJxjygHtniUostNupti0mFMzTlLZYQlkuLCQBJbEF6W5DetsNAHAoASxVzAA8GDB4lU1O8NTpj+WLm8Ab9OypSiALzhxp1' \
			b'iyp2i3p0i3lHFbql4qXcoB8IGM4oeqgTW6j/2wEzU+FrmFh8A0WDEsNgsECxGDCWHiMgMWIisQpA+9t2GFlFecI78AeNfwstcdthaWMe4b2e6gKEg7IJknSqYZRZLCIsLswc1itEwrbHkLFS9PjS8DXqPNR0Rc8VPXeEnitKrii5q1JyDpXcjHJr9es7ajn9' \
			b'Yjyg62igmEePM0qvndR7+W/Yg9pv56udPs+bhYqwW6gMqx2F2GSU4q0pQ/CD22lFpej3FSOuTsQlRgcVZIfS6Zaowo7+JQqRHE5Rih2rRX5/UjV2S5QjhbGOguxiHgfN2mIF2S1WkV2iJLuMmrxx7UgZwSSImuwyipKK/7Cy3PyrfY40754jzwc4+f5/cAnK' \
			b'ozRomwwX7KrSdnfmLVGo7e7AAg8HyNDAsSq2zWnZvXGyKY2bGPM5Vr40Fz8YJewnx7+SYSEnwzM6VINDHjiME4dLrMKuRqWNQz8yRLNMgZtpEPwpYfzl26jQwR8OiJBiB3/4U9U4HINKHn8QGX8NeVVlD89x6dGe0ocwsLYcVP4uDwBciE8QqB8JgioDA7cM' \
			b'CLjjE0EhRDA4NIKGsvGgzhgSnQEFYgDH7tolrKCBuQ2rasMLcW6JF+amcXzOY0N9KTxq+ahWd+UH3ihCYuCUXsaJ+p9Fyuhvgin4aA8r5H8n1hxhEg9+SO5teQh2+GaXPDHf4oGlkgsHBz/bEUx4rWziECo5G0xR/ljOBlP7QTOzNK8mCYgwzeEZQBZzn+BM' \
			b'JX0IauJvB2uUZxoNGx6NN67IKeFMuVnIiZtgjnNVy5lhZ170LMsIPkaeC8/pA8z1z0nMLZyhyfT+OX7pMBBR2T7Hrw9QRs+R6qAc4L79H9ozvYCygLKAck1QdgzKRZ0qrEV0pJyMrljDxpvG8XmCk+IrclJ6WeoeOdkZTnYmfOWk+J/nZHxripNdjpMdc9LG' \
			b'muWk9eCH5N6Wh3Kyy3JS8y0eWCi5cKogPoSTneFkJ5zsdjnZMSfT7tx+0MJJyatJAnFScngOTmruU06KpA9ykv3tcrJbkZNdhpNjuSWcZDflZCec7Awnxxc9y3JlTjYrDMntE/JxbIQU8oSxnfA+at6ZJ5jPQss5Ui6hZJshZZ3SEs0uIjFdoeZZqQn+cAX0' \
			b'0fRsTyFozwTtFxG0lyMlKDvp2CRfOz4fGpzkscw2hhG5aYYoY6yUSOGm+FduEgrRBoXOwk+6QZ7gGTkaQ5niqBnGxEVVyFLcVCAZzkySkwWq9eCH5H58MDfeGUtDRj0nQqjkE1fHg6WsgkWq3BNW43VmpJRKxbB1Ly5hq2TbpInYKpk9B1u1LFK2Sm04yFb2' \
			b't8vWfkW29iNbtUlGxo7llzBWahoz1nF2mLO94ez4smcfu5xN+SpgzQC1vUCgXlBn87H4LJ3M2+5koloI1CgWIDIeCSLFSRHJ1+J2CJHkKbQxDEUkxSGITCIWRKr/2a7l+NYEEvGR7VpitVUSJrHmSJiWx5Dcjw/mSBgzLSScCAF/AcmNFMRrJSC/Xsk5Qz7K' \
			b'/Ei+nbApv21MSGeSgODTvJ0BfDHrCfhUxofAJ/52wEfSXAl8TnNoOpVGJBZ44qbAcww7PjPszIueZTkPu949p48y7U12w3P6RsnQryv0K/Qr9DuZfmzDh6cF9PNypPRjp0g/MV2h80H6eaGfhBHp5w39zBHpJ/7n6RffmqKfT+lHXqUbiKUc38/SzybLD8m9' \
			b'M6UyQz/NtNIvHwLSzxv6GbMYfr2Sc45+PqXffvBtTEdnUkDwk6ydA36a8xR+IuKD8JNC2IGfXxF+PgO/MdkJ/NhN4ecFft7Az+SXRbka/PoCvwK/Ar+T4ceGOG6RIQ6WCB0p/Ngpwk9scNy0DY6Bn1jfaBgRfsb6JsbqRusb9T8Pv+hvCn4565vY97PRZuln' \
			b'PfghuR8fzNJPc630y4eA9DOGN84Y3jgxvHG7hjeRfqnlzX7YPOqp2TRpIP5J5s7BP817yj+R8kH+sb9d/q1oeeMyljem3BL+sZvyTyxvnLG8MS96FuapI51DwV3BXcHdybhjcxq3yJwGS4OOFHfsFHEnpjRu2pTG4E6MaDSMiDtjRBNjdaMRjfqfx118awp3' \
			b'OSOaiDsbbRZ31oMfkvvxwSzuNNeKu3wIiDtjP+PMZJ+TiT43NcnnUgOa/bAFd5JNkwbCnWTuHLjTvKe4EykfxB3728XdigY0LmNAY8otwR27Ke7EgMYZAxrzomdhnoq7uroU3j1+PdtZSXdwudu90itDrtWodSStdki1TydU5JAwv2gxMVZrOhI6idP+Mjpy' \
			b'PcQn8hTaGIryiWIRPsV4KZnMJ/J8cHGdvHP08jquhONfFk9JsvyQ3I8PjliDx2Wxvwiv4jRk8UPZs/abmumY9NGEkx6xDWc33oZ4eQ4KRbkmFFJZnr6GbwUA+XGl81hkKXgknXYhH+fGjWv5yEMKG6WLoUr9KKrMrFJ49BKFx5hhXnC/aokBZj9hhBnIQu2+' \
			b'qDXT58JP77P0u6oz971QNyHdmkV0a+RI6cZOSrd46/icxxs9ioRrhHDyaiRcYwjXmOiVcOJfIYc3Lbsp6jzTDk9uMCFM8A4fTSIvSUIWd9aDH5L78cEc7mIJCPQmQqhCvBQYyq0i0fjl3PPlKJ1dRjYJI/cjZEBq3k3CkI6a43PAUZOewlGqwSE4aqmkeBTX' \
			b'1SDZbJJeGoUdbOklvJTImZect1rOjEwru8CeT+2orbHNSBmYLAOTdzow6Xkezi+ah8PFsHSkcGSnCEeZh/NL5uG8zMNpGBGLZh4uxurHeTj1P9v3G9+aQuHcPFwSbRaF1oMfkvvxwSwKNdeKwnwIKDgzD+fNPJyXeTg/NQ/n03m4/bCFepJNkwainmTuHNTT' \
			b'vKfUEykfpB7726XeivNwPjMPZ8ot4R27Ke9kHs6beTjzomdhnsy7x20KU3hXeHffvOOJOL9oIg6HVehIecdOkXcyEeeXTMR5mYjTMCLvzERcjNWPE3Hqf5538a0p3s1NxCXRZnlnPfghuR8fzPJOc628y4eAgjMTcd5MxHmZiPOTI6HpRNx+2MI7yaZJA/FO' \
			b'MncO3mneU96JlA/yjv3t8m7FiTifmYgz5Zbwjt2UdzIR581EnHnRszBP5t3j9nYpvCu8u2veBZ7aW7ZPMDYIOhLeiZPyjq8dnw/xLsjEnoahvAtmYi/GGsaJPfU/y7vxrQne4aNJ3iXR5niXePBDcj8+mONdzLXwbiIEEFwwk354rbzj1zWYDO9COvO3Hzbz' \
			b'TrNp0oC808ydgXcx7wnvVMqHeCf+dngXVpz34+qb8s6Um+WduAnvOFe1nJl35kXPwjyZd5e4R0vhXeHdtfDOMe/cIt7pkfKOnSLvnPDOLeGdE96J/8g7Z3hnI1beif953sW3pnjn5nhno83yLimQIbkfH8zyTnOtvMuHgLxzhnfO8E5MXfic451LebcXtvBO' \
			b'smnSQLyTzJ2Dd5r4lHci5YO8Y3+7vHMr8k5zaHk3llvCO3ZT3jnhnTO8G1/0LMyTeVe2UCm8K7w7nXc8fxcWzd9h9acj5R07Rd7J/F1YMn8XZP5Ow4i8M/N38XEY5+/U/zzvor8p3s3N3yXRZnlnPfghuTdZmuOd5lp5lw8BeWfm74KZvwsyfxem5u9COn+3' \
			b'H7bwTrJp0kC8k8ydg3ea95R3IuWDvGN/u7xbcf4uZObvTLklvGM35Z3M3wUzf2drOAvzZN6VTVMK7wrvTufdwLwbFvFukCPdVbNitwi8QYA3LAHeIMCTMCLwBgO8wcSswBP/88CLb00Bb5gDng0gCzzrwQ/J/fhgFniaawVePgQE3mCANxjgDQK8YQp4Qwq8' \
			b'vbAFeJJNkwYCnmTuHMDTvKfAEykfBB772wXesCLwhgzwxnJLgMduCrxBgDcY4BlZszBPBl7ZKKUArwDvZOA1PIHXLJrAwypPRwI8cVLeNTKB1yyZwGtkAk/DUN41ZgIvxtqME3jqf5Z341sTvGvmJvCSaHO8Szz4IbkfH8zxLuZaeDcRAgiuMRN4jZnAa2QC' \
			b'r5mawGvSCbz9sJl3mk2TBuSdZu4MvIt5T3inUj7EO/G3w7s1F+41mQk8U26Wdxoz866RCbzGTOCZFz0L82TelZ1SCu8K707nXc28qxfxrpYj5R07Rd7Vwrt6Ce9q4Z2EEXlXG97VJmLlnfif5118a4p39RzvbLRZ3lkPfkjuxwezvNNcK+/yISDvasO72vCu' \
			b'Ft7VU7yrU97thS28k2wmeQ4xc+fgneY95Z1I+SDv2N8u7+oVeVdneDeWW8I7dlPe1cK72vBufNGzME/lnbuYnVIK7wrvrpB3bLDSLDJYafRIecdOkXdisLLoN8wbMVhR/5F3xmClsREr78T/PO/iW1O8mzNYSaLN8i4pkCG5Hx/M8k5zrbzLh4C8MwYrjTFY' \
			b'acRgpZkyWGlSg5X9sIV3kk2TBuKdZO4cvNPEp7wTKR/kHfvb5d2KBitNxmDFlFvCO3ZT3onBSmMMVsyLnoV5Mu8et4dL4V3h3X3zjg1WmkUGK1jB6Uh5x06Rd2Kw0iwxWGnEYEUvI++MwUqMtRkNVtT/PO+ivynezRmsJNFmeWc9+CG5Hx/M8k5zrbzLh1AF' \
			b'KSfhnTFYacRgpZkyWGlSg5X9sIV3kk2TBuKdZO4cvNO8p7wTKR/kHfvb5d2KBitNxmDFlFvCO3ZT3onBSmMMVsyLnoV5Mu/KBitPxbvy07C3xD02XGkWGa6ALz5S7rFT5J7YrTRL7FYasVvRMCL3jN1KjLUZ7VbU/zz34ltT3JuzW0mizXLPevBDcj8+mOWe' \
			b'5lq5lw8BuWfsVhpjtxJDqMbLHP1S65X9GIR+klmTEqKfZPEc9NNEp/QTWR+kH/vbpd+K1itNxnrFlFtCP3ZT+on1SmOsV8yLnkV6Mv3KdiuFfoV+j6Zfy7N67aJZvbaWI6GfOCn9WpnVa5fM6rUyq6dhKP1aM6sXY23HWT31P0u/8a0J+rVzs3pJtDn6JR78' \
			b'kNyPD+boF3Mt9JsIAQTXmlm91szqxRCq8TJDvzad29uPgemnmU1yHmIWz0C/mOiEfirrQ/QTfzv0a1ec22szc3um3Cz9xE3o18rcXmvm9syLnkV6Mv3K5iuFfoV+j6cfz/G1i+b4Wj1S+rFTpJ/M8bVL5vhamePTMCL9zBxfayNW+on/efrFt6boNzfHl0Sb' \
			b'pV9SIENyPz6YpZ/mWumXDwHpZ+b4WjPHF0Ooxssc/dKZvv0YhH6SWZMSop9k8Rz000Sn9BNZH6Qf+9ul34ozfW1mps+UW0I/dlP6yUxfa2b6zIueRXoy/cpWLE9Gv77M9l36bzBAuTn84W6oQ0eOhDY8EtosGglt5EhHQtlp/9eGyPXgWGjDPNRQ4lhoQzzE' \
			b'+xgtpVKGQsX7LA5RpYjHqbHQZoaHXHPHv/x4qE0cjoc2mWN+PFRzruOh+RCqIGXFTMSqOQ6INhsuOPrJnH6CiZStkYnokQOPGRx/mIiLhpp1P96GeLkiGinlfqxHO6OiIvZDZKTyyI2LStGsNjbapHzkwIMpyZ0BUk6/DpBim0QvEDvjkrMsQ6WjtD1LeweX' \
			b'AXEJwldO1uE5fVhYUF7iHi7Nzg8aXT0ucz9lVDqMN9phDNxhDIs6jEGOtMPITrHDGBiQdD7YYQwMSA0jdhiD6TAGE7F2GMW/EhJvsOGFTLcxvjvVbQxz3UYbebbbaD34IbkfH8x2GzXv2m3Mh1CNl9pzDKbnqIFU42Wu5xjSnuNeJNJzlPyaxFDPUXJ5jp6j' \
			b'Jjrhowr9YM+R/e32HMOKPcew2e85juWW9BzZTXuOgVHIZ+k5ji968Xxqz/ESN3kpQCxAvF4gstVou8hqFFUoHSkQ2SkCUaxG2yVWo61YjWoYEYjGajTG2o5Wo+o/ArFlILYZIEbfU0Ccsx1NIs8C0XrwQ3I/PpgFouZdgZgPAYGoBSZANOajMZBqvMwBMTUi' \
			b'3Y9EgCj5NYkhIEouzwFETXQKRBH6QSCyv10grmhE2maMSE25JUBkNwWiGJG2xojUvOgDez4ViJe4CUwBYgHi9QKxYyB2i4DYyZECkZ0iEDsBYrcEiJ0AUcKIQOwMEDsTsQJR/EcgdgzELgPE+O4UELs5INrIs0C0HvyQ3I8PZoGoeVcg5kNAIMqlArEzQNRA' \
			b'qvEyB8QuBeJeJAJEya9JDAFRcnkOIGqiUyCK0A8Ckf3tArFbEYhdBohjuSVAZDcFYidA7AwQxxd9YM+nAvESd4nZBeId/QZ8QeMNoZFXWrSLVlqg0qQjRSM7RTTKSot2yUqLVlZaaBgRjWalRYy1HVdaqP+IxoHROIxopCAqOjkbwhQg51ZdJEnIAtJ68ENy' \
			b'Pz6YBaSWgAIyHwICUi4VkHwbGanhVONljpHp2ov9eISRkmWTHmKkZPQcjNREp4wU6R9kpBTGDiNXXHvRZtZemHJLGMluykhZe9GatRfmRR/Y84mM9Je4s0xhZGHkDTASNQIkGE+HGYlVmo6EkeKkjORrx+dDjCRPoY1hKCMpDmFkjJUSyYxU/8pIvIH2Rydh' \
			b'JAXB3txgQphgJD6aZGSShBwjEw9+SO7HB3OMjCUgjJwIAYSol8JIuVVGxnDGd3KMpJIYGbkfDzNSs2zSg4zUjJ6BkTHRCSNV+ocYqYWRMpJkuxIjuVqnjDTlZhkpbsJIzlUtZ2akedEH9nwqIy9xN5rCyMLIW2CkZ0b6RYz0cqSMZKfISLFSpfNBRnphpIQR' \
			b'GekNI80RGSn+IyM9M9IbRnpmpGdGxhCmGOnnGGmTkGWk9eCH5L4zRTTDSC0BZWQ+BGSkXCoj+TYyUsOpxsscI33KyL14hJGSZZMeYqRk9ByM1ESnjBTpH2SkFMYOI1e0U+VqvcPIMdkJI9lNGemFkd4w0uQ3sOdTGXmJO9gURl4VI8EPlE9h5eTPMvH6/rBo' \
			b'fT97DDvr+8Up/iqTrO8PS9b3B1nfr2HEX2Uy6/tjrGFc36/+lZWBV3XQSVhJQVArp19oiiFMsDLMrfVPkpD9hSbrwQ/J/fhg9heatASElRMh4C80yaX+SBPfxt9p0nCq8TLDypCu+N+Ph1mpWU7yH5OwEisdLlFhi9CRmTHxCTO1FhxiphZKysyw4sr/kFn5' \
			b'b8ov+dUmdtNfbZKV/8Gs/Dcv+sCeT2XmJe57U5h5VcwsrJzoV/Lijm7R4g6sxnSk/Up2iv1KWdzRLVnc0cniDg0j9ivN4o4Yazcu7lD/sV/Jizs6s7iDgqjohP3KGMJUv3JuiUeShGy/0nrwQ3I/PpjtV2oJaL8yH0I1Xmq/km9jv1LDqcbLXL8yXeWxH4/0' \
			b'KyXLJj1bk9Fz9Cs10QkjVfoH+5VSGDv9yhVXeXSZVR6m3JJ+Jbtpv1JWeXRmlYd50YvnUxl5ibvjFEYWRt4CIxtmZLOIkY0cKSPZKTKyEUY2SxjZCCMljMjIxjCyMRErI8V/ZGTDjGwMI9nCFU/IyBjCFCObOUbaJGQZaT34IbkfH8wyUktAGZkPoQrxUhnJ' \
			b't5GRGk41XuYY2aSM3ItHGClZNunZdjEJZ2GkJjplpEj/ICOlMHYY2azIyCbDyLHcEkaymzKyEUY2hpHjiz6w51MZeXN76Dw9C2eWeCxinvJOOaeMU7ZdG9euhmm8hrFbtIYRKx8dKdPYKTJN1jB2S9YwdrKGUcOITDNrGGOs3biGUf3PbnszvjXFsbnVi3l2' \
			b'2bT4IbkfH8yyS3Oq7MqHgOwyyxU7s1yxm1qg2KULFGNQgidelNjxcsTuTGsRY/ZSJInwDiKJ/e0iSdciPpJGmWWIGuHuOkRxVxzJOsTOrEM0svJcnMfgiDB0DTvUlK5a6apdY1etZ6z1i7DWy5FijZ0i1nrBWr8Ea71gTd6LWOsN1noTsWJN/MeuWs9dtd50' \
			b'1XruqvWMuBjCFOL6ua6aTUIWd9aDH5L78cEs7rQEFHf5EBB3cqnE49sIPQ2nGi9zCOxTBO7FIyyULJv0EBQlo+fgoiY65aJI/yAXpTB2uNiv2FXrM3Acyy1ho9QqYWMvbOwNG8cXfWDPp3bVLnHTmtJVK121p2AaLyHsFi0hBF98pExjp8g0WULYLVlC2MkS' \
			b'Qg0jMs0sIYyxduMSQvU/31WLb01xbG7ZYJ5dNlQ/JPfjg1l2aU6VXfkQkF1mnWBnFgl2U8sCu3RZYAxK8MRLATteBNidaQVgzF6KJBHeQSSxv10kDet01TKL/zTCva4auyuOZPVfZ1b/GVl5Ls6ju2qXuFVMwVDB0BNgqGeryn6RVWVfy5FgSJwUQ71YVfZL' \
			b'rCp7sarUMBRDvbGqjLH2o1Wl+p/F0PjWBIb6OUvKLIaStPghuR8fzGEo5lQwNBECCKs3ppO9sZvspywl+9RSMgbFGOrZOrJnu8h+PaPIBEMxewmGVHiHMCT+djDU16tgqM/YQWqEuxgSd8FQL4aQvTGENLLyXJxHY+gSN2i5jx9/KD/8cAOjgj0bcPSLDDiw' \
			b'btKRooudIrrEgKNfYsDRiwGHhhHRZQw4Yqz9aMCh/ufRFd+aQtec0UYSbRZj1oMfkvvxwSzGNNeKsXwIVZByEowZc41ebDX6KUONPjXU2A9buCbZNGkgwEnmzsE4zXvKOJHyQcaxv13GrWio0WcMNUy5JZxjN+WcGGr0xlDDvOhZmKeO/oVL3Gyl8K7w7lp4' \
			b'x8Yd/SLjDqyYdKS8Y6fIOzHu6JcYd/Ri3KFhRN4Z444Yaz8ad6j/ed5Ff1O8mzPuSKLN8s568ENyPz6Y5Z3mWnmXDwF5Zww9emPowa9Xcs7xLjX42A9beCfZNGkg3knmzsE7zXvKO5HyQd6xv13etSvyLmMKYsot4R27Ke/EEqQ3liDmRc/CPJl3l7hxSuFd' \
			b'4d218K5j3nWLeNfJkfKOnSLvOuFdt4R3nfBOwoi86wzvOhOx8k78z/MuvjXFu26OdzbaLO+sBz8k9+ODWd5prpV3+RCQd53hXWd41wnvuinedSnv9sIW3kk2TRqId5K5c/BO857yTqR8kHfsb5d33Yq86zK8G8st4R27Ke864V1neDe+6FmYJ/PuEjdBKbwr' \
			b'vLsW3rGVY7/IyhGrJB0p79gp8k6sHPslVo69WDlqGJF3xsoxxtqPVo7qf5538a0p3s1ZNibRZnlnPfghuR8fzPJOc628y4eAvDNmjb2xaezFoLGfsmbsU2vG/bCFd5JNkwbinWTuHLzTvKe8Eykf5B372+XditaMfcaa0ZRbwjupScI7sWbsjTWjedGzME/m' \
			b'3SVuYFJ4V3h3JbzD1gwJxtNh3mEFpCPhnTgp7/ja8fkQ78hTaGMYyjuKQ3gXY6VEMu/U/yzvxrcmeIePJnmXRJvjXeLBD8n9+GCOdzHXwruJECo5C+/wWnnHr1dyzvCOcj/ybj9s5p1m06QBeaeZOwPvYt4T3qmUD/FO/O3wjuS5Eu+4+qa8M+VmeSduwjvO' \
			b'VS1n5p150YvnU3lHm5EAbgrzHsU8eA419TrY5wr/zrehJTRaZAKd0QyzWgJCbBx0pDtbspOCkBU27W3pF6CQPAWcXpS/cXdLb3a3NEfc3VLinYUhqhXxOLWlpZ/b0tLGm93Skh9hsJ77f8Fnjlkeqpe4qaWP27HmQsLNLf3IRTzFbS09c5HPGS5SOYxc3A+b' \
			b'uagZrm3uQ8ysOw8bYzkkbFShH2IjZW1/HQGJdyU4coVO4SjJ27PiFHfdztIzHfnMdDTF7lmkho5YB3r8Pzj63z9nTML/Q0v/sx9PD5CUwRMoG2jc85iMdLRczEKxVhYSCAV+E9jbBd7BhQIEtkl6KbWISEojIVGWPpY8ShnPRFmdJLsEOUSODDUebai/S4od' \
			b'QigZiApMBKZA7AG1x2r/ROln1P1hXc+KPir4qN1Voy/Q5VNa/EhbelXWs3p51MikdKPGjeo2r2Otgo0aFXUpqtCzKc9dtXlYYea05Rq27nsqcl85qloknRgVIulBVYKoy9qDuqy9GHWmn+pY/+n7/CI0W3Wl2u1UrXbCRy19dN6SajPfolgR+KP6AtUcMuza' \
			b'Vd1jNVx3UMN1F6jhwoVot6LZ7lizlY+3i9Ro/UGN1p9No+0Pux6h1NqFSq3bV2xNU5Rb7JSqgjs0bAl+QCo8fAn+eqwHXaIA3YD3qAAr+IPqAeXBSrG1w5lQc6prV5BhevXBI5QkVqKjlGQw6weionR+yory3pWlo30yRWFi2e0rTR3VjqP0TpQoDu1LXU81' \
			b'6jhoj4HRTv66N+QWNcq2Hn8tDm+arzf/gpb3HEuVRgCH5SOA7nK+KdccC9ydiboH1fuYscBTVGeiNrmLeSvflq46MGFz6rclafl7V5nd474xUdm555AJ1HWQqMW6zp+q66an+k9Xd5TQJequOaEb3VyxyusvuDv9blReeDq11xyl9hzNqJ7QrQ63ovoc/XjV' \
			b'u+xeg0zWm96tzvxxF6zCO6DsXFhpzLC6ImV3FYruJCUXLuvbrk0U3UIl5+o1xw5Rilep5N6xgnNPZL+CZpunf86d0HOFtJRBw+vTbBc72Pe4HqsjDVMG+c6g0fxTWeQ9ZjrkJI1WpkGKRrsgjdYWjXYejRY2ry7QvnhmNc07tDW+ZF3WPJGtsdFnVNEvXZ0d' \
			b'rcpokRMtaGpp8dKF2RxfizpDo4GntDne/Gt4DsClmYXmInXcSXoNEoalixXn9nXcKfoNrtt+Hf12Hd9rT7KIglZfor6qMV33p91OnDDlEnukZkON1t6ORoO04TJHLNrL1Wy5tcZPod3ADcrgNC1nje5SY7ui8ZZoPLT8oiXmW6yDV6H52gtSfluUHEbVnqYD' \
			b'0UrUmM9ZoznUiN1ZNCJuGHEOpTi32UP81GueUCmGEz/5XPnse4QSRHPHp9SEGP1CdUgqChXYEytDHM04/VMQG81Trq49VRnufRD25/kgrJ6ol2vUHi4QurjvwaL2bkntLRzDS7QdyvvSP/9uVtsN59F29dNrOxBk0XZF212etrv8zu6tajtI7Fm0nbsAbVcX' \
			b'bVe03QVqu7Zou6fSdvXtTG1cvGq7LoO6S1Bnl6/JzqG2cEPb25qKfaRtCTTF56jL0bwEUlo01i1rrBVN5m5Mc2EduGzNdYNWJGvZx/W4M39DGswXDVY02L1pMOruXcKnFyWk6K+j9Zd7LhAaniMDSJNd5nKGosmKJjurJusvRZOVL7G1NNklLFo49peOHrHe' \
			b'tJVfJLoFBVe/AyVXi6Jzd6Ds6M1U4dXjei36Eavx74wKkHPgq0WasL4uTbjCT+osVIcORw/aXkvzSLV4CSsfilosavEi1KLbVYvOqEWX/J1VLbrlatEVtTilFmtRi+4EtXie5Q9FLd6IWrwfleh3VaI3KjH9O6tK9MtVoi8qcbrjLCV5pDo803KIMgxYhgHf' \
			b'hb7jJn2btiQXqdMuYxyw9ajBeEr2TEscigYrGmxdDcae7socbjUVhmWnf7ehwprwHJEGbQy/yrCdPUcdDW0NzqTZujMtZyiarWi2tTWbL5rtZM02/t2NZrvxpQtNf/3aDX8bZVUNV81rOSh9nO/Cwd3L1XhU4690ZQOl/WmVHiVhtQ4pq5+V9R4HOqf78Ac6' \
			b'tyiceS0YUPu11CjxwpHeu/EFEEXvHa/3LljXhSvWdeHpdV1YVdeFc+i68JjvvKyGKwskLlq73WuflVrlna9NPVGj3cF0QmieE/agyeEF/aJ0VxZIFE12CZqM2ntZZX+yJpPyu4+JUY9jbVjVK/w440Wr3SUskCia7B41GdXdsmHIGqpMivKOjDw8dCs9tT84' \
			b'sya7hDUNRZPdhSajhngJa1ZvTZHdn7War58jF0mDXcLyg6LBbkqDUVW+sOUFV6vBuDCLAksUmCMFhk21wwse6S8rB4ome7wmI+1yyQulrlaTlW+xnCqraaifNVhZOVA02Boa7EwGGEWDFQ02r8H6skKgaLAjNBjV9QtavVlU2J2qMDKzIA12QysBIHnxN5ov' \
			b'TpvheozuQrRaI7/NfAGj/Des1VDuW3zz4vUbJuCStBxK7HEqDjWb27zCVhMC1lisU65z9MBvXnW40w+40xx5w/6DcaYteypybjavHCTWdVjzHdQY+Pv6Aa6fbUF34s+S1+hvC9GBymrQE6gIdvPohmoKNAc2bGi/GxABVG2oC1CCIFkoCyhsVDFQabFm4s8Q' \
			b'1dQcofnFiEEVVfgH6qjCLg+qQ1R7cO/QxAbcoGpj+0JB11CfUTFV0beDiuGgSBxkE/4odWG11IHmX/aP4m0w3m5pzFAFUfFSXubS0CAjmsl/9eBEo+88oSS180kCDYS/r13RDy+6uRTWnEr81WybUlX/9BNdmGq3k3oIce8fVm/+Ydnxb8/PwD578w4qd3Sh' \
			b'H+UCjUJPKJvdk2YTSBLwx9Ehu4D7lf55UKS+pqYKmvbR2RuG2Rzir7rX0IzqHs/Dfo7baibX8FWz+B9+eaQuzHgvPO9Hd0iX8UclMWRLwmFxTZdHQ0XSS6mgLjRbok0WkpOC6uS34nuylEGqIWhQO5P9Ny5oof0DPBcoWtQ0He+FSoUbxgLusMAhHKi7XNjw' \
			b'DNLChd7nC947+Vjqd4QQRkH0PQnDQfo9aFNfqWBQle4f9H3Z5p6MzyvrRV+wfwvezL2WCSZzux9tNeFnL1PJozSsXV9Uo8D1shsX9Q6e/OCyqvPND6oefmJLO4SPJPhEOqI1+tMapDeNsj6uYWIv6ekbp9tkDtsZFEftBi4+uvoY3456eXo1LPAe2uPCP/7g' \
			b'6uaKtj+qQvnNXR5cWXypLEdVlrC5y4MrS7h06DebCzi4rPLd2qMblnvytkXjoO+sfWFX59FHu0ooTxET1538+ENRyhOVBkfP7/HgyrLCKE62RqypmHFuY6UD510e8T6XWX5oqDSwqQYWNnd5cGXJj57N1ZTFbaxbu501m/0Dp4OyD5YeOLN54ss8F5IfLBqH' \
			b'Pg6NezTDBtpBGzbtO2qArWmENTdE3KAFp4doIAT84W7XbbN+48QNj0jGRzfSfrN/4HiPXKH6y3kZ/Yb0b973accYrl7hlhZhdAnY7prHRdNJTquDfrl6TozPFRpMVDTUOHd4cGXJj65dJA3QNOeCDi6/dQacztXAlpb7ZAM61HjQVmrvQCOZ7IPEU+MPe1r3' \
			b'WBglCzY/OFS06FRF8Ju7PLiy5EfH1tSiWCnW06Rhc6YDzQRPepPLsYwUHdfo+s1dHlxZ8iNFaze6etVPmGFzvgPNc096k4uzDCId1fbQIPweD64s5x9EspVitfaHJvznPNAy/qQ32aB2YmCpNMGJJtht7vLgypIf5lnSBB/R4aQ6cEzHcqJDObbIfnPagSOY' \
			b'y33jUpXAw5EHPELOcg+4zIst0lENFBdK3ePBlSU/NHTmBprUi7UbK656eyeHXUn2iHBYDtczkmMnZJ6+8XabCzzwd7rp5M8dFVee40d2mvXbsa0qK7TnaZH3m6MOXHV47Dv7hy4NPfFtKNumt2s44ZZld/pokszQvuu52UtTAbi4+aSDszWc+Pb8gauHzxHu' \
			b'7MEV6vgRpytWBrim/boPFtrp41oXYadxUfqg2Tzm4Ey5R4Vx8MANBc4aQXpwHTt+OOzMiuGU+d+jFUS/ecIDa/E6nlr+XAinj74VRbFTNXAPlHKMB1ew0w2zSgXbrWBuUw5zcAVbZ3jyImB0yhcrbrV0UwdL9c5NzHDrrJs6WKrXMyp5EVMJuHLw0Qct/jN/' \
			b'qwU6nnZiMbeJn8Ph5Q6uOSstxbybmuM3d3lwZSkWdcdVlrC5y4MrS358s1SWqcoybO7y4MpS7AWPqiy45es9HlxZypZtx1WWenOXB++gWcwgj6ssbnOXB1eWstr1uMriN3d5cGVxm1ehpV33eM6n8dGBv2qagA5Y5rSVWoX7ifMD6HXbKlTTXuG4qzZuiV3T' \
			b'sm/cNV02AW7zvkGq6R/77vZ8o7TpDaxX6Z9reVyw6e1Oz1hfJKUDu6dbLZEPMuajcKk+tlwXqe4Fqm9Yp9Ad6g3vHAyqOAmF6nDYqbdaZ7Hu4X7UtN+82Wue93PvdvZwD7J/O26bwOKBwF9ha4EajuuyabNfSYdL96nGFfVcCq3H+5pcxW/ANd2YDl/x10fb' \
			b'jC6AmK8f/j/LAbza' 

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

	def expr_paren_1       (self, expr_pcommas):                                       return AST ('(', expr_pcommas)
	def expr_paren_2       (self, expr_pcommastex):                                    return AST ('(', expr_pcommastex, is_paren_tex = expr_pcommastex.is_commas_tex)
	def expr_paren_3       (self, expr_bracket):                                       return expr_bracket
	def expr_pcommas_1     (self, L_PARENL, expr_commas, R_PARENR):                    return expr_commas
	def expr_pcommas_2     (self, PARENL, expr_commas, PARENR):                        return expr_commas
	def expr_pcommastex    (self, CURLYL, L_PARENL, expr_commas, R_PARENR, CURLYR):    return expr_commas.setkw (is_commas_tex = True)

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

	a = p.parse (r"a.b{\left(x\right)}")
	print (a)


	# a = sym.ast2spt (a)
	# print (a)
