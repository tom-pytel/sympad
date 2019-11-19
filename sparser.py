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
			b'eJztnXmv4zaW6L/MA7ouYAOWSFFU/Zet5wWTbbL0m0YhCCpLD4KXToJU0q8Hjfnu76zUoVbbV65r+xLluhYpiuvh+YnkIf3i1Z++eO/Tjz795E+7P/2vH37+Hr7U+dE3n73z+QeffASX6eKjb979/J33/h0v08VXf/7qk/c++6tewfcnn34Jf//yzufw94u/' \
			b'fkz34Juef5/uffHRO1/8b75894N/++a9d7744Au5/vgd9X23v/xLf/kZX1IMKQ9/hgv5quS7hu+PP/zkK4r3w08+/Vi/K72oKUMU0Xtfff7RXzGidJF7f/ElleWrd/UOX37w8Wdf/vWLDzA/H37y5b9h0b+iYn74MQWnv//xOd7/iKr0UwwjtQR1STXEf9/7' \
			b'9OOP34Hvz7nWP9da/5z8qKCfa62LHz+HWWSPPsufZwVA1wf/AX/e+fgz+Pv+ux/RPfT95H2pb7x6t7/8S38p9f3BR198gHn6/MOP8fuD/3wP6+WdL6liMMovOTuQ5y/1G2v6/Q//8uH7+MR70vIc7rOPqGGg7rSN/vOLD96jAO9/+Oc/ozB98iGJ4XuU6Xc+' \
			b'eR8rGW98is9//M5nX3z5qWRRxYc8/g83DX5V3GaQ5Hv/Dpdv/vj2zT9e//bmH+b6DVx/9/q3H37/5pffvvn+25/e/P76N3MbLn/4569w58d//F2vf/7hv755/dt/qfPNH7/+8Fvv+BYu//7692++++Unufrtl//XX3F6b3548+a7dPVrutJoXn+bLn/8/p/J' \
			b'9/ffU0J/e/3d73r9KyXA3n/8/F2f57/97dfM8c2P373pc5oK9NOPfdl6399/+C1d//2Pn7758e8psu/++O2n/zZVo5ff/vjzL7aaUq5+e/2djQou1PmPH9Kd199/nwK9ToX755sf+pJSLaUSYJlMxacbf/z84y8/pxv/nXL048+/pyx915cG2tlW2z9ep0r+' \
			b'+ZeU8h82yOufv8/8bb1++90vf//76+T8JUX2LVTC//2hb7Q83K8//vDdD8kBAvlzXxe/vvn9l5R0EpJUkl9+6ktLkWaON+bJb376x+uf+vrjJ7/evXqxD/UuNA87vgh40VT4p9414UGc4KIrh8F2TbPbyy31YFetz8EDTr3wkkLtW/I57F54t9u7XXN4SB4e' \
			b'PbxXj32HF+7Af1rIgKsfrFftR15tbb3wEq6qwH/adrev4oN44SVctfA/7hqIiu+0eAHfGBF++4h/3C5AiKp6yL3UufeU18rvXjRUCEkF3IHcHWep2b2oMUCL/3uvYJ11Kxfoh5FATiqfrqiVash1BSGgVSLnCXz2NWWirvhPC7HWnENw4SVWKzUCtseDceq1' \
			b'8eemxibGEtJ/3+htjxeYSfHnrEMtiCe7IY91pDaue4+OPKrkQa20E0ExHinE3lGpvOc/geNCWfGUB+/EqY2D+eCMBP4TIBOBxcxhTVPzBhAYlB+5EQ56w7fSuJwlcEID07OQEFYktYwUGb1q66ydXKAfPg616qDMDQtAcsahl4hJ5u0PY2f+oK/GzokQbe5V' \
			b'j53ZQ3sfTM76riGZGHhUQ4/aenTSJJVXN3RtkknQE1iVlDkUEyhdxVlIt6a9c6+9ryhikHqQFpSvqttF8AeNhK0l6U7cRl0HWuWIUCAoeai9p/6BegDCHbRfQH4rLlyHigCVDFQFlFD0AXonz96nZR8TJrJP1/t05CPSSr2Iiu1q/hO6lD31ag/WCy/xKvIf' \
			b'qLmHh/4Srzx3CH0ELxkEkHwvl+jCYL0TmpeUU6Rgql8xXm6Yw47jqRz/aTEUk6NydEm1iP1XLlhpY1tQp5Cw4GZAcM1VB4kOe/cuVCpxmb/6gAflJYg0Sl2DGzo4haH/EJCrBfUlVXTgPy2kXEv7BLrEsoOmiJhFoVy7i1THoOFfVAK3HVQ9tlaoVKXRXSHd' \
			b'5N09A8CjtEeVxcazVpROIYJYa+WD54vQ9K2CztDnLO4CxVlDE0A9qqokZ03xj7ySE7JE8kD50Ct/kCuRQrio9cLpBTMLKqlN8aErZgmqT3Lta4q7asSpd6B0FRfC858Wq4pbGAWyZiHrdtIDD+xSQa+xbTlr0Nb1wVK5oprCQJH/tNh60tVIB1EtBv5jXnyC' \
			b'8LFp+A+988i9hi7xyuvNB3GCS28wfCBHsWFJSOhDieZ3Jnq98vo8OMH1wH5yA9+qxAeu4IXu1WFXQdtVUDGALE/sBmEHgQHpBw0HggUtBF0TdBnUWLeDCungst5VIJsVVHYFPbjC2oQ7FeisCtoCKsphCPwPqIMcgz/IZAUveHAbnwBcVh6/4UmQ/uoA39D/' \
			b'qgZDQgwNKAO4gvghFxVko4J8VB5DQHahRiqohQo0fAWJVZBEBWkATkEdVcDoCmqlc7vO77pm14Vd1+46jGOHuSaFW4GwV6CVOhQEzEC1w1daen+DHlIdIOABX7J2NXUuSArbFFQ0amkkMGQby3SAMh0wYriGeqs8XsPDUJMVVCV0/Oh30GoR6wZew6D3x12E' \
			b'hDHvEB4yjSoc2h14CMmDjmrxVQQ0dUtvs/CqCnLWkiC39HIKKqslnFQ1Fh6yfUDFBhfQltCUsUImYXXibXxvh8sH7LCQN2j2F9je6IGPP8Btz07M8gOBmUJhSfAutsADKRm6W9HdV4h8clPcRVbuRFZedNzoFbcuthS1dleJCLFsYKuis/Ly3chjVRSPTsKL' \
			b'6MmDGCKgT9E19yk/2MBtaeD7beAXjjWBq7XHO+7hrXTwminSuSIF9ysFr3AyqrTvHbcv1T7264Y6ujTU1zTpwB3ft9kN9BH4e4I/tYW52wS5SxHbUr79EhphtAI4ELyhyImoTQqZES4WqglhEgGyUmOlZSgnM/IBMoHN0BykHQ5c29IftB+ozLOcq4RbeTZy' \
			b'rLLL8qoCWproUU2EbOS3X9fIuOsgrGxaGVpJl2h0YNboe7QbdS4Zf1Vu3LleVF6FoZEX8rrR9+26K4r6fhX1i4oH7zCIj6Wd77edUQEcSgPfdQNXpX3vt31fVE5mW6taqB90cs3Ra4HbQfS7uGt2obTz7bazEx7T6za9sMmwR171dEKV3FXAd3OodchEFbA+' \
			b'scIgPqicIgO3KgPQuk1p3Ttu3VBa945bty2te6+t+6LT2Ut+B+tkmfKgr2JU2ocyIXahCbGmTFLcc+/CgnJ/krFOoMWDcwSG5jdxojvIlGhwj49KX80PvEZJKxK0mMVL1qfG52TWtY5nPV6LrQXPBr+gFi4LI49WMr7YH9yxjoH2ZR3TlOnQO27mF7r8TNaI' \
			b'+K3TKI18B1aekf0jT69EHnejPkeljFWLi2/YMGXl863p4BdRZjgreQ2ITLjIS5ixEyPCg0yQ1broKW3MdqkvAt+vWQJqaWi6Z1uW6gUVg6x9NgL3OrdbaMScNXDeAmcpcJZaHvMd4N4BxSCXndLcK8gNrJJbbrA2lsp8RGW2LP0ti33LYt92S3WqCq/U7Vrd' \
			b'sopoWUXEQxHU85V8K0pe9LMsd8jWgqg6vbyl3fFb2ivaU1I/lN1D99zGkKGa9wXVZafPHbUrbmHmjV2lXe+nXXFjXi1buOC7NOCtNSBttis98p4aFFuplm2R2CdLU95wU9JrkFR+2XRxbaNSzDh3tVYwSN+lpa6upeqGG6ijEWQxiLxjtYm7RalTNhV/e+2c' \
			b'nsBodzJ1ElKekOWfg7zUOhKa0n+fvv++om1r2BilEZ4Qd057khv2pDQOZEVbmucpmqdmdebl/R9Po6SXE2maQO7SJG+xSZwTkhBYZD2IF6Sj2GPxeoZahFL40iwXp4kv9fx2qF3q+S2omc6ripdlUjE4oUENK5YgpkxkJIuwYBNX3DxEAyJ+A+4E8F3H49jS' \
			b'WJfoFIdDqd2LvQQdvIzpIotyoCm0R5lyyykyaBVOUfJwERJAC/TSbtv0ippUz+l27fKye6j53VcUmIzsG+xpX7PlZp1Z8pGnLy/Eb7uZYyODk9FGZcwgW3kQvB6bXN9766gmn35oglWaa41VdJzQho3BpxCRlW7NVro1W+nWvQC4OrnIPrdm+1zq2DX3c7YE' \
			b'6icgogxy+UDAYh50p1O7DcO9YSEIQRAvqy6lXx9vRM39rhyseM/d5RVuNShmOTfZcqTNilI7cWA92llT6my1zuIj9kHhZhxCcHsoCD51e0gsuvkWdTPumWKZr4vMnyrzrlTZqVVWLKtvVE3IokzbFJk/dZLwUGT+JmW+EpMTuO14Fxd+4YTCA/1eIH5Bszr9' \
			b'+R4nduruQc2dXf/zHmRe68S8VvzxCxrBiS2ne5DFTzb7o0A+8m3XsFvOO2cTMmfOKyczJqdWS86ckkqmNI5NaZyY0nBGJHwQ93gWm40+OANUFzQCL8es3rJYo5UOzTeW/RS33YyVaIxueBCfn/FvpvxR4zg1t6jFzIKMHutiOn7rEsLmAqUJb7UJ0aDJsUGT' \
			b'Y4Mm6cFOerAT4xD8Dvy+0QTuz3xgZLHr2PRdPp3SWJcDBzfYx8Ty7OWLxbo5sPxGwluxZ3mrQ1U/NxLYsQFDlKEF2zeREQp/y460yE0ZWSNFHguRDYTjeXjHB4hRCwcORTucvqaTxFityXvIgdNoWcu1HLjlKFp+92lZZFrOVRR9eOiHZL4MvG+PejQY9g/y' \
			b'aioDWC8jV0+jUFIU+t4qQtsbAwsIxWYyOnl4Vqg9BiDh9Sy8noXXl3enW5YiTMkXg5D7beDAPZXnysqc9Clb/aGOHuinhpsH+anDBsf8kA+oo9Jj7rXHYE2Vhr77hsZ3nkZeaRp+pWn4lQYbf1fLOzn6Bb5VyQm0WMuB3qZkpAvVECSmULb5XGrcFanSI9Y9' \
			b'tg2bK6mhf001b3d7UDO1/PbLxuZ49C2ee4uH3uJRraXj3mbHxYpqURRa/or8pa0N2WhLL7zQS1HoZEQp50hXcpA0dSrql3wIMvXXWJrhUsqwK5V7uUNPaqxcknWvsl6LjCNHCjdukxuQYseg6KQ12QrlsHt1wDc++o1cNNzA38ntjERzhXGTdZpAoFqhKuGW' \
			b'xnoPND7ocKCA44aA9cQl4mpDGeUq9lLGYem4aJ3kHutN64klzjYmmXKTzFRJzlgiW5ZGagmRbZUxkgtnjj8LchwaD3cqPHgdf7ACKxZ/9wR/VgN/UwNbCrJQodSDUFV4ohr+ECn+XCXmBSSrxn3uIEI17s0FaahxazaKD05T4xlbaC2Ep9PgaRx4UgSepocn' \
			b'6EGvqXHbH1Yt1i20Xo0dBisZaxnPucHDbaCia1QmeMoK2qTjqUR4EBEeHu2x0eEZKGuNm4LxUBzcFIw7gvFgMNxChkdK4Y6yBjsjfONyPr4cojE7dnK04MMdNLhXEXcoQplrXEmE8riDA1nZQ+xQ8H0FOdxDjveQ4h5S3nu8Puz2HXgf8D5cwn9sjT0qiD1q' \
			b'hj3kf+/IGx5BPbAHkdpjp9lj2+yx8++xH+2x+++hiHvs/Xvs8nvs73vsVHvs7Xvs6nuHLpCofYfxUPAOYwAfaNt9wNvQAHuovD1U4h5jbfBhj2ljxlE+9igg+4iPVxgXJgZVvMekocr2Ld6BttljSlhykEysiT1mBtpg7zBRjrfFP+QMXA0ooHvUX/uKgh28' \
			b'lBiEcF9jtg8YisqKNRowq3ALOsAeS4y1FPAmCPseGmsPDbVvqQ2w3uEuxQ03OswAXlSULlVHhffgP0jTHisM1e3eYZGxYKhS96g39+iNZcfusXd0CwNjOIgYvjv8hghA1PcdlYOaBPMEiWFhseZBWPdYBVgD2KARU6JGwjSpCuFui5k6UJnQBeFAl+1BB+xb' \
			b'rG0sI4SOJAsQD9yLXrKP8tJh7cD/QJmn2sWkqIYhjojhu69RxaFiK2qtqLVj1FrRaUWn3YBOq1GnzekyfqdNGg275RF6zUzn8hzvUMc1s2pu+g11VdkN3sm7DVVeO1B79Vj13ZvKg5bp1V4cqD4Ii8O2VRXYYmO0K8quxRBW4ZHHOUqvZbXXSgyzyq89Rv1R' \
			b'HNuowFazBI3RXkQBtpkKbCeU4J3rPkxd9F+ba0Cq+HUtuPtXeIlwbl8injtwuPg/uOviTNXoZXLCjvJ7HellGmJWUzaiLO18gChOf7rubKbU59R01rQqjWMLuGC062FCw/ZTVdksDs6m6MwKzlDgrEua3VBN3JopLC9TWPFIzTxYjcBfjVNNjb9xiL/JRxob' \
			b'wuE8Bv4UKb24QjicRdlUi8N9nKMaanP8YQkaGqxp9Tij2b1o9/aRGj4MtHx7hKavRdtHo/HhPp54iHVD2r8yBEDNgA3crEAABabJMcBeFCBaB8nFLA00lDKBHd5GoFygBAUN6TbllDGRElxCRf/UDCvw1ggXFdMiS3WKHFkA12XulD2hCZd0CJRUaAkwGQnd' \
			b'sbhBDyUON1GUxw18qGTctgY+43iZRFpKU9cIJi3bBfCUip5BStt4DVUSbgArKjNVSPtoaCk1hVumygRd4hR4cTt0UiZGmJVqbqmEMwZZXb+kV6kagIaNG8AbuksE76YRzKE6fbknFdS9REKDCgB3+B86bLngr+Cv4O9c/AXGX1jDX6AwGf6C+qIE9Q4apM7j' \
			b'T0Il/AXBXx9Bwp8ZGaXblFPBnya4iL8Ubg5/U6MlCu/yVCfxZwO4LnOn7Cn+wiT+tNASYDISupPhLxj8BcFfGOIvMP5Cjr9RvII/KaWpa8KflO0S+NOi5/iTNl7FH4cb4i9siL+Q46+vMsWfSI/gLwj+gsGfkWpuqY3x1zxqYmwMvjtB3hLuCuqeJ+oQbh4r' \
			b'awV1/MlQJ1465cfX4rc250eBvN/1MSfAUTICuHSb8seAS8kuAa5/agZweMsCDiVVZwOzVKcAlwVwXeZO2ZufLUwlljnD8eN026INPRRt3EhS4VPTilTsnm2DiKmkIeWiNbWMaNNSXQBtqdwZ2rR119Am4QZoqw/boa3OZyRNUwjaxClo43bopEyMNivP3FJD' \
			b'tA2QVr2kVytlWou3D3EKaqFArUCtQO0oqFUMtWoNahwmgxp7JajJKhZ9r0KtEqhVKZoEtcpAzXwS1DTZRailp+agVuVQo6AyZ4mVmp6fhJrNlusyd8reAtS0xAq10eN0O4NaZaBWCdSqOajl9gITcYeUidZ6tz4V6hJM02LnTJPGXWUahxsyrdqQaVXOtL4l' \
			b'lGnsVKZVwrTKMM2IMzfUZkxrC9MK0wrTjmKaZ6b5NaZ5CpMxjb0S07wwzR/DNDFKq32KJjHNG6bZEMo0TXaRaempOab5BbuNLNlJqNkArsvcKX8LUNMiK9RGj9PtDGreQM0L1Pwc1HwOtVHEPAupBTT1TFiTYl0Ca1rwHGvSvqtY43BDrPkNseZzrPVVplhj' \
			b'p2LNC9a8wZqRaG6qZawJziYoFgvFCsUKxY6iGBuW1GuGJVjwgWGJeCWKiVFJPW9UYigm5iQcR23NSWpjTpJu1705SUp2kWLpqTmKTZmTJIrZZCcpZgO4LnOn/C1QTIusFBs9Xg8tSWpjSVKLJUk9tCRJFMtNScYRC8WkgKaeiWJSrEtQTAueU0zad5ViHG5I' \
			b'sQ1NSerclMRUmVKMnUoxMSWpjSmJlWhuqnMp1l0FxR5vX34xfi2Ynz9bJs2ZsG/AopM4NGTQiDuRuRPXuBMpTMYd9hpbtpPvKnmikCemiBJ5oiFPNCGUPHENO9ih5ZmTTd5Z9vr/0+Cx2cLGjMPPY83i0USjnR0exdxIo9V6TJlOdhp8iww15B45+8uL8EVb' \
			b'NOeLtOIaX+at6rdAS+yxkqqs5wpn0drXc0GMiT0FyFmi8OihUR3OpMaCmeEmNoZ0jjHvgre7+G93NOQHI6I4GBWhPWnoSYQnD8uxB3o0+/Oh0tJIqbnAaKm54IjJ8e5T/FokF/Ycl5NLvJRcyXng72l00S2lFzu8PMp7h4RelJjQK92mXDK9UmoCMHQEjl4x' \
			b'RlFwZlAHpBhmWIa3ZnGWZWEKZVkA12XulNd5lKXiC9DGj9Ptg9YZg068FXcmYN23h+sra8A/Kl/Pv3FqDD8ttWkIJJ+W9QLgS1nPwKcCsAY+rZUcfeK7FQApJzy2omgzIRYMapKMQW6BTkrGJLRlrTnwmcOrqrqK8VWZJXzG7LuVWULHa11uba0Ld6QM1rrE' \
			b'KzFP1rrcMWtdTta6nE/RJNqZtS5nQyjtNNml4Vr/1Bzhlta6smQnCWcDuC5zp/wtEE6LrIQbPe6Ga13OrHU5Wetyc4M5l691jSMWmEkBTT0TzKRYl4CZFjyHmbTvKsw43BBmG651uXyty1SZYoydijFZ63JmrctKNDfV2Rh73KETBWMFY88HY7zY5dYWu3DG' \
			b'Y7DYJV4JY7LY5Y5Z7HKy2MVxOLvY5cxiV7rt+sWulOwixtJTcxhbWuzKkp3EmA3gusyd8reAMS2yYmz0uBsudjmz2OVkscvNLXa5fLFrHLFgTApo6pkwJsW6BMa04DnGpH1XMcbhhhjbcLHL5YtdpsoUY+xUjMlilzOLXVaiuanOxti5B4QUjBWMPTeM8dqZ' \
			b'W1s7Q+kfrJ2JV8JYFIwds3LmZOWM43B25cyZlbN02/UrZynZRYylp+YwFpcwZpOdxJgN4LrMnfK3gDEtsmJs9DjdzjAWDcaiYCzOYSxfWhtHLBiTApp6JoxJsS6BMc10jjFp31WMcbghxuKGGIs5xvoqU4yxUzEmy2vOLK9ZieamOhtj5x70UTBWMPbMMOZ5' \
			b'U5hf2xQmYSzGxEsxpgYg/phNYV42hXEc3m4K82ZTmDcfxVhKdglj/VMzGPPVAsayZKcwlgVwXeZO+ZvHWCqyYGz8uB/uCvNmV5iXXWF+bleYz3eFjSNmjGkBs9L6VKwLYCwVPMOYtu8axiTcAGN+w31hPt8XZqpMMCZOwZiXfWHe7AuzEs1NdTbGyoEdBWMF' \
			b'Y8dhjCcV/dqkIgr6YFJRvBLGZFLRHzOp6GVSkePwdlLRm0nFdNv3k4op2UWMpafmMLY0qZglO4kxG8B1mTvlbwFjWmTF2OhxP5xU9GZS0cukop+bVPT5pOI4YsGYFNDUM2FMinUJjGnBc4xJ+65ijMMNMbbhpKLPJxVNlSnG2KkYk0lFbyYVrURzU52NsXJE' \
			b'R8FYwdhxGONJRb82qYjyPZhUROHyZlbRy6yiP2ZW0cusIsfr7ayiN7OK6bbvZxU1/DLH0lNzHFuaVcySneSYDeC6zJ3yt8AxLbJybPS4H84qejOr6GVW0c/NKvp8VnEcsXBMCmjqmTgmxboExzTTOcekfVc5xuGGHNtwVtHns4qmypRj7FSOyayiN7OKVqK5' \
			b'qc7mWDmWo3CscOw4jnXMsW6NYx2FyYZj7JUw1gnGumMw1gnGuhRNwlhnMNaZEIoxTXYRY+mpOYx1SxizEUxizAZwXeZO+VvAmBZZMTYdQ4axzmCsE4x1cxjrcoyNIhaMSQFNPRPGpFiXwJgWPMeYtO8qxjjcEGPdhhjrcoz1VaYYY6dirBOMdQZjpnm5qc7G' \
			b'WDmXo2CsYOwojOHWU2hg/FrEWEOfDGPipRjja/FbwxgF8l7iIJdijJIRjKXblD/GWEp2CWP9UzMYoy23cxjLkp3CWBbAdZk75W8eY6nIgrHx43TbYgw9FGN0s5Yan8IYlbvH2DhixpgW0NQzYkyLdQGMpYJnGNP2XcOYhBtgbMvN05SNHmOmygRjmh5jjBui' \
			b'kzIxxqxEc1OdjbHrOJijYKxg7PoxxjYezZqNR8NhMoyxV8KY2Hg0x9h4NGLjwXE01sajMTYejfkkjGmyixhLT81hbMnGI0t2EmM2gOsyd8rfAsa0yIqx0ePN0MajMTYejdh4NHM2Hk1u4zGOWDAmBcxK61OxLoExLXiOMWnfVYxxuCHGNrTxaHIbD1NlijF2' \
			b'KsbExqMxNh5WormpzsVYfe5JIQVjBWPPDWNs49Gs2XigKA9sPMQrYUxsPJpjbDwasfHgOBpr49EYG490u+ltPFKyixhLT81hbMnGI0t2EmM2gOsyd8rfAsa0yIqx0ePN0MajMTYejdh4NHM2Hk1u4zGOWDAmBTT1TBiTYl0CY1rwHGPSvqsY43BDjG1o49Hk' \
			b'Nh6myhRj7FSMiY1HY2w8rERzU52NsXKMx1vF2NSRVgVnN4YztvVo1mw98NC2ga2HeCWcialHc4ypRyOmHhxHY009GmPqkW43valHSnYRZ+mpOZwtmXpkyU7izAZwXeZO+VvAmRZZcTZ6vBmaejTG1EPv16bypqCWG3yMoxeoSTFNbRPUpHCXgJpmOoeatPIq' \
			b'1DjcEGobGnw0ucGHqTKFGjsVamLw0RiDDyvXNQc+F2rlUI8CtQK1k6AWeMUsrK2YBfpkUBMvhVqQFbNwzIpZkBWzkGJOUAtmxSzdDv2KWUp2CWr9UzNQC0srZlmyU1DLArguc6f8zUMtFVmgNn48DFfMglkx0/t17GOagFrI183G0TPUtJimthFqWrgLQC1l' \
			b'OoOatvIa1CTcAGphw3WzkK+bmSoTqIlToBZk3SyYdTMr1zUHPhdq5YiPArUCtdOgxutnYW39LHCYDGrslaAm62fhmPWzIOtnHEew62fBrJ/ZT4KaJrsItfTUHNSW1s+yZCehZgO4bjfIalhZP0tFVqiNHg/D9bNg1s/0fh37mKaglq+ijaMXqEkxszJry1wG' \
			b'aprpHGrSyqtQ43BDqG24ihbyVTRTZQo1dirUZBUtmFU0K9c1Bz4XauXAj7cKtaaspF3tKfrgpl+3aE6djvQ8HenXpiM9hcmmI9lr/Fsw5Ls6IekZc41PEaUJSU+YQ3djA+h8pKa7RDnUHBJwbkLSL2COhbX/Pz0paTOHs4p++FmelNRi66Tk6HG6nf0SWW1n' \
			b'JbmK9vyzMbMrbX7wszGNxJyK1v9sDN3in41peqdPlxsSj3LueiEaTE1Kg68Bj+pj4pdjtGo2m6D0CXscrzeV2M9Scq51lhK6I/UjSJMpyAWV+Uoj9jU/llPQwxe+5yn+qsNLekuw/Lu+k0IGvzRzyxQc/sZMGd7d2fDO8fDOrQ3vHIXJhnfslYZ3jrlH36vD' \
			b'O8fcC300aXjnzPDOmRA6vNNkBXzowJ9xchODvPTs3CDPLQ3ybOKTgzwbwHWZO+VyYZCnBddB3uhxun3Q2pJxnjPjPAlSxz6yqXGey8d5oxRknCclNdVO4zwp3yXGeZrpDHva3KvjPKmMwTjPbTjOc/k4r8+xjvPYqeM8x4TjMsk4z5Sy5sDnjvOu7yiRwrnC' \
			b'uVvhHNtPhjX7SSTJwH5SvBLnxH4yHGM/GcR+kuMI1n4yGPvJdDv09pMpWeVcw5ybmsxMz85xbsmKMkt8knM2gOsyd8rlAue04Mq50eNBrCi5toRzxpBSg9Sxj2yKc7k55TgF4ZyU1FQ7cU7KdwnOaaZzzklzr3KOww05t6E5ZcjNKU2VKefYqZwTc8pgzCmt' \
			b'gNcc+FzOXd9RI4VzhXO3wrnAnAtrnAsUJuMceyXOBeFcOIZzQTgXUjSJc8FwLpgQyjlNVjkXmHNhgnMp9BznwhLnbOKTnLMBXJe5Uy4XOKcFV86NHqfbB60t4VwwnJMgdewjm+JcyDk3SkE4JyU11U6ck/JdgnOa6Zxz0tyrnONwQ86FDTkXcs71VaacExES' \
			b'zgXhXDCcMwJec+BzOXd9Z5E8u1/ILsS7A+LxVoKwtpUA5XewlUC8EvFkK0E4ZitBkK0EHEewWwmC2UqQbod+K0FKVokXmXixJx5FwTlBBZRimOPe0raCLAuT3LMBXJe5U14XuKfFV+6NHg+yrSDo+mhIdZ/QJ6FqU51T6Ms3F4wTEfRJYU39E/qkiJdAn2Y6' \
			b'R5+0+yr6pDIG6Ntwc0HINxeYKlP0sVPRJ5sLgtlcYCW95sDnou/6zi95DPoi0e9QAFgAOANAqN+ausApIDycc/Ykb0Hwa1sQPH3ysyfZK509KVsQ/DFbELxsQfAp5v7sSbMFId32/RaElKzAEB0gevQlMKQoOFjdmRhmYOjNdoQqMBArVLTZeZQ2K5PnUdoA' \
			b'rsvcKc/zUEzVIFAcP+5lWwLXHUNRvNOplBKqjn18E1D0+eaEcSIMRS2saQc6m1KKeAEopkxnUNT2X4OiVkYORb/h5gTPmxO066UzKvuq0zMqJV2GI3ZHLxsVvNmoYKW/5gfOBKS7vpNRytiwoPH2xoYdjw27tbFhR2GysSF7pbFhxzik79WxYcc45DjIlcaG' \
			b'nRkbdiaEjg01WR0bdjw27MzYsOOxYcdjwxTD3NiwWxob2ggmx4Y2gOsyd8rrwthQi69jw+kYDlpnMjZk7zQ2lFB17OObGht2+dhwlIiMDaWwpv5pbChFvMTYUDOdYVDbfXVsKJUxGBt2G44Nu3xs2FeZjg3ZqWPDjtHHZZKxoWnqmgOfi77rO02loK+g7+bQ' \
			b'h33dk0guow9lts7RJ16KPr4+8Pca+iiQ9xIHuRR9lIygL92m/DH6UrKCPnSAuNGXoI+i4JxAA/UxzKAPb82iL8vCFPqyAK7L3Cmv8+hLxRf0jR+n2wetM0afeCv6NFQd+/gm0Ed10KNvnAijTwtr6h/Rp0W8APpSpjP0abuvoU8rI0cftepG6KNs9OgzVSbo' \
			b'E6egr5U9DFwmRp+VdAl8Lvqu78yVgr4rR18Q/MWCwBECHY/+3NroDwK4wehPvBSBTkZ/7pjRn5PRH8fh7OjPmdFfuu360V9KVhDoePTnzOjP8ejP8eivj2EGgW5p9JdlYQqBWQDrMGVbQGAqviBwJoaD1hkjULwVgRqqjn18Ewh0+ehvnAgjUAtr6h8RqEV8' \
			b'PAJrOtqO5/szFKbMZyjU9l9DoVZKjkK34SjQ5aNAU3WCQnEKCp2MAp0ZBVqJrznwuSi8vpNaCgqvHIVlFDgxCuTtfe3a9j4U2MH2PvFKo0DZ3tces72vle19bR9NGgWa7X3pdttv70vJ6iiQt/e1ZnsfRcE5wXfxFMPcKHBpk1+WhclRoA3gusyd8rowCtTi' \
			b'6yhw9Hgrm/xas8lPvNMoUELVsY9vahSY7/MbJyKjQCmsqX8aBUoRLzEK1Exn6NN2Xx0FSmUMRoEb7vNr831+psp0FMhOHQXKPr/W7POzkl5z4HPRd33nuRT0FfTdHvr4TJd27UwXlNbBmS7ildDnBX3HnOjSyokurU/RJPR5gz4bQtGnySr6PKPPG/R5Rp9n' \
			b'9KUY5tC3dLpLloVJ9NkArsvcKa8L6NPiK/pGj7dysktrDncR74Q+uVvHPr4p9OXnu4wTEfRJYU39700RL4E+zXSOPmn3VfRJZQzQ5zdEn8/R11eZoo+dij4v6DOHuFhJrznwuei7vqNcHnOU2TUeX3YUyhRjii9FlyLr1nB19ahqGFXNGqoaCpOhir0SqhpB' \
			b'VXMMqhpBVZOiSahqDKoaE0JRpckKqiZPH+ufmsNTs4CnaSTZvLguc6c8LSBJi6lIGj3OR4FZHjUGRs0cfpocPxqPUKdh5DQMm+ZCpNGy5aSRZlslDYcbkqYR0jwSMk0OGUnLbLwTL6VMI5RpDGWMkHJLnEIZosvVH6BSBlZlYHUDtGqZVu0arVoKk9GKvRKt' \
			b'WqFVewytWqFVm6JJtGoNrVoTQmmlyerAquWBVWsGVi0PrFomV4phjlzt0sDKZmGSYjaA6zJ3yusCxbT4SrHR46ydtc4EZOydWCah6tjHN0W2NifbKBFBnBTW1D+xTop4CdxppnPcSbuv4k4qY4C7dsOBVZszr68yRR47FXmtIK81yDOSXnPgcwdW13emShlY' \
			b'lYHV5VEVGVVxDVWRwmSoYq+EqiioisegKgqqYoomoSoaVEUTQlGlSS0OrNJTc3iKJw+sbF5cl7lTnhaQpMVUJI0ep9vZwCoaGMU5/MQcPxqPUCcyciLDJl6INFq2nDTSbKuk4XBD0sRtBlYxh4ykZQdW7KWUiUKZaChjhJRb4uSB1fWdZFLoUuhycbpgJ4SG' \
			b'w69FukT6ZHQRL6ULX4vfGl0okPcSB7mULpSM0CXdpvwxXVKyS3Tpn5qhC946jS5ZXlyXuVOe5umSiil0GT/O+tDQBT2ULnFu43TMN06neJgukTdLR94mHS+0RzqVLaOLNtsaXSTcgC7xsAld4iGji6Zl6CJeQpcoe6Kj2RNthZRb4mS6XN9hIXf9+zblt21u' \
			b'd2ouss1DXLN5QCkc2DyIVyKS2DzEY2weotg8RJ+iSUQyNg/RhlAiabKLREpPzRFpyc4hS3aSTjaA6zJ3yt8CnbTISqfR49EP6WQsHKKYN8Q524aY2zaMIxZcSQFNPRO3pFiXQJcWPEeXtO8qujjcEF0b2jbE3LbBVJnii52KL7FtiMa2wUo0N9W5U3D++o70' \
			b'KBgrGLtOjLE9RFyzh0ARHNhDiFfCmNhDxGPsIaLYQ3Ac0dpDRGMPkW7H3h4iJbuIsfTUHMaW7CGyZCcxZgO4LnOn/C1gTIusGBs9Hoe2EdHYRrDSlhqfxFhuIzGOWDAmBTT1TBiTYl0CY1rwHGPSvqsY43BDjDUbYiy3njBVphhjp2JMjCeiMZ6wEs1NdTbG' \
			b'ru94joKxgrHrxFhgjIU1jAUKk2GMvRLGgmAsHIOxIBgLKZqEsWAwFkwIxZgmu4ixFG4OY2EJYzbZSYzZAK7L3Cl/CxjTIivGRo/T7QxjwWAsCMbCHMZCjrFRxIIxKaCpZ8KYFOsSGNOC5xiT9l3FGIcbYixsiLGQY6yvMsWYSI5gLAjGgsGYkWhuqrMxdn1H' \
			b'bRSMFYxdJ8bY3i+u2fuh8A3s/cQrYUzs/eIx9n5R7P04jmjt/aKx90u3Y2/vl5JdxFh6ag5jSzZ+WbKTGLMBXJe5U/4WMKZFVoyNHo/tEGPGui+KaV+cs+uLuV3fOGLBmBTQ1DNhTIp1CYxpwXOMSfuuYozDDTG2oV1fzO36TJUpxtipGBO7vmjs+qxEc1Od' \
			b'jbHrOyajYKxg7Cox1vFRGN3aURgoaoOjMMRLMdbJURjdMUdhdHIURtdHoxjrzFEY6XbXH4WRkl3CWP/UDMa6peMvsmSnMJYFcF3mTvmbx1gqsmBs/HjnBhjrzMEXnZx60c0dedHlR16MI2aMaQFNPSPGtFgXwFgqeIYxbd81jEm4Aca6DY+86PIjL0yVCcbE' \
			b'KRjr5MiLzhx5YSWam+psjNGRF0CRgrKzUAb3oLtePdKgFgrWtsYaKnxU9Z7xtvdr1ojYDeqcb+KlfGNVTD/+Uh9BOEYOf/vA//uff6l7xnEykpj+/IsmvcQ41B4ScO43X+oFyGXpTv7WC9/yaCfB5u/2kZTFecxpkPRrL3U6knMqJos79Ei/91Iz7jiuCdxR' \
			b'DfS4G0fMuNOiVrbcPhWzvgzyUiVkyNPmXkMeFW18wiE17EbMo3z0zJOcWXtG8RLocXN0UiqGnqlsJ4F76GGzB/zrK/pb499A/l1Df+kuEpCC4hfxr4F+vEC/xD1LvEncdYo44pswbYZmQ46tWsITr+bJJETKaCOkmaSLJYtQhOjhL0CKASFWyTBFhceapFsS' \
			b'WAKo5m+Nxu/swOUU7Z7p9QmNvq7OSZf3Cjxpb9XYR+jqOS19otW4KuNF1dsr3VyvJqU6rUmtGk16EzUmKsqLqcihclxXi1M6cQvbbqsIMxWoyo80X1J7pO1U1aHGCssaq7kapdUkvVUX3XWu7jpLb532WkqvjfekvMzbJLZ9UWIXUGKPUGDtsgILV6jAXFFg' \
			b'RYE9kQJbsbopCuytK7B45JjxcD0KrNlQgQ3nJp+BEjt7BHmiIsuUmDdmiPegyOJlFJkPz16ZoSyeq9B2/wLpfgn5p+mw7kjVVp2r2uaXeB6h3Y6dG3NnvKLVN6zh/PW9qr0dDeefSsvV3OWP1nLYrme9svl70XQ1FeAtvbpBLjaa7o8XfnVzVr+t6LZ6uNJ8' \
			b'7vCzvSHdds167SydRj36et7cQqbXjtRpNffhjYah2Hg3qdPenj6rNly+PJygzyaMcU54X1vTZ/W0PoMslSk1q8+WLFogXBtYx4Hs1dAwNbRMru/ADXVSQ33UUB811AfrwIO1dIH//in0IenCzKLlLH1Iw8PN3/OO1oftnD6s3Zxl5XMfzSZ9iE2U6US1cQLl' \
			b'wuZaQXQk9gCR7FxhqvWWo8zTT0Xrz6XsUWfs0bROFCo6HGnV+imMQvCQyIup1El1WhV1ejuvhxu8Gj6pKpxVg1VRg5u/FronUWCXfCcs74NFgV2pAitLrNsrML97dW0muQv7St6eee5Vq67qrS+uJtVFSuSKNdfJWou3+nSylSdcm5nurWgunCN5+2a6u3/h' \
			b'BrsDrqhCc16dJjtLe0HGsEJRVu5fk53zEobbStzjNdnVv4Q9yQ4D3m2IPqi5np8eO9MuhGusftSrWLgXBQbfICpYpderyCb21D6JMsMt5NUZSs2uIuSrB0XBrSg47HW0g3qPYncTii5cka7bY8th3vzJKg8Xu8y6wHA1oN1eAUJNXkYHLp1fIHoQ8vQUOrDq' \
			b'uvNf6PBcgfJSd6rOwyZ7SsVHHe1I7YcXoX1S3YcTEY970cN+8oQa8BzdN3rdixfQdt3TvPFZLefaK3zbK1ruDrTckVNvmXKrqaau++XuHpVbd4Gx7OEKlFssyq0ot+tRblVRbm9fuUHRtldu1RUotxtYOi3K7fkot7ootydQbtWdrEJcuya7Ifu1sqLwBNYe' \
			b'NSV2T4uk5xt5QOd7iVob7Twgk0VB3auC2sJC7X6UFO2buWoldYemHI8zR4v1S0AL6SlX9FTRU/eup2jIcQ3vUpSRoqWO1FLVSwZMiz9fcYikr65wJ0DRV0Vfba2vmmvRV03RV4/SV09u73/qj+I8Yv+l41+xuQs11l5QlTWizsJ9qzTqsZlaQw/d0IS/dWT+' \
			b'X1DNUfQVuVb1XXNjo8gNfoxlUenV6Bmi1uGJyu/J9woU5VeU31Mpv26o/Dqj/Lrs/0WVX3e88uuK8suVXyPKrztD+V1gn0BRfjeu/J6D4sOOng9mD73iC4fs/yUVXzgcrfjQvyi+fKgr9Xei0rvAdoEyPVem5y6l1Ui53KlpxlVqrqecnws16ile9ryE5X/R' \
			b'U0VPPVpPSaDnZEO2maLi31nn/7esqBq0I8MO5PENCzvUyz11LHzRIv3VXsK4v+ivor820F9V0V9n668q/b9z/XXP9vtNcwc6rNlQjzULuoyXmHCm9Sr1Gkn4jZr2U96fVrVRFjYbQrK62U67cXwzGq6m4sO9ZV3n25fEPuh9eEGHPLb3bPxftNsJ2u0qNVp9' \
			b'wxrtyV/WKAsbarR6Y41Wn/nONqnHyuaAK9Zhz2eUSf3vmW+0PENv3fVkvsexJfaPAw4uax5Vls0BRV89hb6iCMrG8LP0Fdfd3S8+Ony/Qlk+4ORY40hfPfnmgKKvnom+4j5YTrJ4pMKSanwW5hKufomUg84G3/x+9eT2/EVf3au+4oBXsPfyntTVc7Luqjs8' \
			b'fIfnrZ7c9L7oqVvXU9xpr8u0/mb1FMdc1BQdEvaSEAj9EC9q0lfFar7oq9P1FUn8NW8Full9Vd6rjMKiiXZ+rypW80VPnaOnqqKnip56e3oqFuv4oqfW9BSK9nVsQix66lnpKbSvomFfvBcjeMhe+jndq1NZcP/qfkb3apYF70l/YXPv8cmr12SoJa5Jn2GL' \
			b'na3RUJHVu1fYP/wB5bQiUW/phtu9avG4GfDHVoP/5O2td4tnx5B3s3tVQx7rFuW9htzB/68f4PrFHlQlRl5huD0kBxoKf0caFESM5OfQDwcbuGIJsrCD6geRBhkAOYQcQSGgXaFIqEygiipMCM38U4KgaNDE+IDfOGhBhYYqGfxAVKoaTwvAc27Ar8F0QfdS' \
			b'yNpj10UNjbFxbvyjcwMKff0fpdVgWu2xqYGUoVbvZpJtUOE3s/8qUE2snuvel3IRlnMBKgC6Af7y54F+RWouUyDz9KvFmrmkvvG3sDuUq0GGgWujfyis/FtR/f9RGASL68OjYkY3/X4SCCfdoZK1T1EyEP2IP0QNJQQkb/APf4cdf3sdSxQ3KFGcKlTV4nEw' \
			b'4A8dv8KDjoaFbMJCQSGFo//h+0HvYgp3Qlzf+4PmM09R4btx4ZH5cbEKPNVCKxWBusucozVXLxWte1D9YGpVIFs3RAIqUjJsxoUm2rBe0VEkyF86EJPqszJ1iq+E8ByoGK5fuBdrqedmuq7rKG8xPq93euvQuq+p/msoQt3hG6a2Bb6PDj701udG3sMgBxtK' \
			b'n7H/Z580T5/yfzbBcbQziWa38riGoUiEwPcqOxC9nz/hhyunmuhg+LK8w9dr7ml+By8rp/W3+uQud+i7HY6lju56zTV0v3o3/NhBGPuk4dcpHxx3HR0aR1h65dfC+pPycc6H5asuCvwYCXK7Z/Zh6XBXqpr97kk/XDl+m65TPVnvCW+zB7W7DT4417VJRG8x' \
			b'DRaWiXFl0bNjKYm7Z/Zh6dhivD8Qgc10LQ4Pt/r48x7jSpqYOihdaNSFaAr+WX1YOiamYVZE45he5DfsSbgwkn9wtWHse/wH12/OepKrbGryJo0qjxhSgryHwy64Xbh8F/PczXDXEHW1ZsdT4JGP/cf5xlBv3/3wbBNq1ObUbhh2gw+OofUqDm9OBKd1v/7/' \
			b'6gOnfiRSjdvlPlDxta8emQZ/4WLcSkBeiJiYCCoKfixZ7e6ZfVg6pmbCrkzB40rzNXy4wraZ2tm4Cx1b0XNdZLV7oFFH/sFF5rHvRLjmiEBbfY5MjFtyYhqmKMZxy1e7Z/Zh6Ziah9pMMVbNRsoRzawu8EGTpdMf44orczJHdauwe2Yflo6JOZltu1W11XsH' \
			b'Gi5e5oPGgKc/xvVXpmuO6V1obvq8PiwdF52usVKwSQ9Di+CLfdDS9vTHuBqL/c1RnSzsntmHrTinJlSO62TnDfxOGeDNDuxSo7W78z44OXhkUDJsd2vBcfZv6gZX8tS8ROmCwy6IWyme14elY2oS5pJd0ArCpt0RN8Jc/mN3lpwbCVf89c+Z2OWLJ++eYXdV' \
			b'H/zhWPrqLp0US8vpcyh+y56qsrFJj51t43Z30gf3HJ36zOCjm8HOebQ78FfatrVrhLjnz9vIiuXbWau8vk7e7c77cJHCmU8vfHCD4OaRLn5Ygk6f27m97o5bVW/1w610/gzSU1omXFOPx73Kj/hQoaBqHxnN3Ae3BF8o6qkPC9XpE08X6frnrIeergLa3ZN8' \
			b'UGC3CRQE+efPcxVVwLKApxWUD354T/H5xkZFokSiql350IclapuJwFuzt8FjT+7kw834PM2mINJ7+XAzXv/83zVMy+Pus0d/eCdZ/3+D6PqvQfzGmYVZj2/qw6Ky0Ua+exeVevfMPiwdxUrsKOlwu2f2YemYmkks0jGSjrh7Zh+WjmIDd5R0dLtn9mHpmJqK' \
			b'LNIxlA48P/N5fVg6imnfUdJR7Z7Zh48pLHslj5KOevfMPiwd1e6Vb+jkK57UaurkwQsqjUMPrG3yxPpktQNN98rKDLQ7nX+EZwJBa+IPYTs8koERBuI0GRraOf/PocMoNLYzPYHSlP+vZRm4ae35pigp4h/ZPz8/h0Lg+aES3vNhySSFUSSuIWlCf5AYjguU' \
			b'bR5LlGeMxCZpxbx1dKYNyLw5apmOM6ZjjEN/hHE6vhj8W678cMAjjHAFLNKBDSjRXEOhyg5thT5SyyRFqNHd0FGunGfIPlxTDJ087Xuf5uuHrx/+P749a4Y='

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

	# a = p.parse (r"""Limit({|xyzd|}, x, 'str' or 2 or partialx)[\int_{1e-100 || partial}^{partialx or dy} \{} dx, oo zoo**b * 1e+100 <= 1. * {-1} = \{}, \sqrt[-1]{0.1**{partial or None}}] ^^ sqrt(partialx)[oo zoo] + \sqrt[-1.0]{1e+100!} if \[d^6 / dx**1 dz**2 dz**3 (oo zoo 'str') + d^4 / dz**1 dy**3 (\[-1.0]), \int \['str' 'str' dy] dx] else {|(\lim_{x \to 'str'} zoo {|partial|}d**6/dy**2 dy**3 dy**1 partial)[(True, zoo, True)**{oo zoo None}]|} if \[[[partial[1.] {0: partialx, partialx: dx, 'str': b} {-{1.0 * 0.1}} if (False:dx, 1e+100 * 1e+100 b) else {|True**partialx|}, \[0] \[partialy] / Limit(\{}, x, 2) not in a ^^ zoo ^^ 1e-100]], [[Sum({} / {}, (x, lambda x: False ^^ partialx ^^ 0.1, Sum(dx, (x, b, 'str'))[-{1 'str' False}, partialx && 'str' && a, oo:dy])), ln(x) \sqrt['str' / 0]{d**3}/dx**3 Truelambda x, y, z:a if a else b if partialy]], [[lambda: {1e-100, oo zoo, 1e-100} / \[b || 0.1 || None, \{}, \[[dy, c]]], {}]]] else lambda x:ln({}) if {\int_b^p artial * 1e+100 dx or \['str'] or 2 if partialx else 1e+100} else [] if {|{dz,} / [partial]|} and B/a * sePolynomialError(True * {-1}, d^4 / dy**2 dz**2 (partialx), 1e-100 && 1.) Sum(\[1, 1e+100], (x, {'str', 1.}, \sqrt[1]{partial})) and {d^5 / dz**2 dy**1 dx**2 (oo zoo && xyzd), {dz 'str' * 1. && lambda x, y, (z:zoo && lambda x), (y:0)}} else {}""")
	# a = p.parse (r"""\begin{cases} \sum_{x = \lim_{x \to \left[ \right]} \left(\sqrt[1{e}{+100}]{False} + 1{e}{+100} + \infty \widetilde\infty \right)}^{\left\{\neg\ \partial x\left[1., \emptyset, \text{'str'} \right] \vee \lambda{:} \partial \vee 0.1 \vee dz \vee \frac{\left(d^2 \right)}{dx^1 dz^1} - \frac{1}{\sqrt[\infty]{\partial}} \right\}} \left(\frac{\frac{x}{y}\ zd}{dz\ c\ dz \cdot 1{e}{+100}}, -\left(\partial x + dz + 1.0 \right), {-2}{:}{-{1 \cdot 2 \cdot 1.0}}{:}\left\{\partial x, 1.0 \right\} \right) & \text{for}\: \left(\lim_{x \to -1.0} 0^o o \wedge \log_\partial\left(ypartialx \right) a! \wedge \sqrt[xyzd]{\infty}\ \widetilde\infty \cap \frac{\partial^3}{\partial x^1\partial z^2}\left(0.1 \right) \cap \frac{\partial^9}{\partial z^3\partial y^3\partial x^3}\left(a \right) \right) + \left(\lim_{x \to \begin{bmatrix} b & True & \text{'str'} \\ dx & 1.0 & 0.1 \end{bmatrix}} -1 \ne dx, \begin{cases} \infty \widetilde\infty \wedge \partial x \wedge None & \text{for}\: dz! \\ \lambda & \text{otherwise} \end{cases}{:}\partial y, \left\{\left\{dy{:} \partial y \right\}, \left(False{:}\partial x{:}\emptyset \right), \lim_{x \to \partial} \partial x \right\} \right) + \frac{\begin{bmatrix} \infty \end{bmatrix}}{\begin{bmatrix} \emptyset \\ \partial y \end{bmatrix}} \le \ln\left(\left\{None, \infty \widetilde\infty, dy \right\} \right) \\ \left(\operatorname{GeometryError}\left( \right) \wedge \ln\left(x \right) - 1.00 \right) \left\{dx{:} 0.1 \right\} \left\{1.0{:} \partial x \right\} \sum_{x = 1{e}{-100}}^p artial\ True \cdot \left\{\text{'str'}{:} \begin{bmatrix} xyzd \\ dy \end{bmatrix} \right\} \vee \left(\left\{\emptyset \right\} \cup \frac{True}{\partial y} \cup \left|\partial x \right| \right) \cap \left(\begin{bmatrix} True \\ \text{'str'} \end{bmatrix} \cup \widetilde\infty \cdot 1.\ True \cup -\partial x \right) \cap \operatorname{Sum}\left(\left(\left( \right) \mapsto 1{e}{+100} \right), \left(x, \infty \widetilde\infty\left[1{e}{-100} \right], c \vee \partial x \vee None \right) \right) \vee \left(\cot^{-1}\left(\emptyset \right), \int dx \ dx \right)! & \text{for}\: \left[\left|\left(-1 \right) \right|, \frac{\partial^4}{\partial x^2\partial z^2}\left(\log_{\emptyset}\left(-1.0 \right) \right) \right]\left[loglambda\ x, y, z{:}\begin{cases} \infty \widetilde\infty & \text{for}\: 1{e}{-100} \\ dy & \text{for}\: dy \end{cases}, \operatorname{Sum}\left(False, \left(x, False, 0 \right) \right) \cap \sqrt[False]{2} \cap \frac{1}{dx\ a!}, \gcd\left(\left(dy \vee \partial x \right)^{1.0^{\partial x}}, \operatorname{Sum}\left(b{:}None, \left(x, -1 + 1.0 + \text{'str'}, xyzd! \right) \right), \left|-1 \right| + 1.0 \cdot 1.0 \right) \right] \\ \left|\begin{cases} \left(dx\left[\partial, \emptyset \right] \wedge \left(False \vee \partial x \right) \right) \left(\neg\ -1^{dy} \right) \frac{d^2}{dx^2}\left(dx \right) & \text{for}\: 1{e}{+100} \\ dy & \text{for}\: 1{e}{-100} \end{cases} \right| & \text{otherwise} \end{cases}""")
	# a = p.parse (r"""Eq(Union(dy2 - 2.0651337529406422e-09*notinxyzd, Union(Complement(diff(z20notin)*diff(s)*partialxb, diff(diff(diff(-1.0)))), Complement(diff(diff(diff(-1.0))), diff(z20notin)*diff(s)*partialxb))), Or(Union(Complement(Union(Complement(Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))), partial.chCa.dcGNDli().XG()), Complement(partial.chCa.dcGNDli().XG(), Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))))), diff(diff(dx))**1*e - 100), Complement(diff(diff(dx))**1*e - 100, Union(Complement(Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))), partial.chCa.dcGNDli().XG()), Complement(partial.chCa.dcGNDli().XG(), Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))))))), 0.1 - bcorx0orc)); slice(None); abs(Matrix([Integers])); Matrix([[[Eq(c, 2)]], [[{Lambda: oo}]], [[lambdax, slice(y, 2)]]])""")
	# for v, k in sorted (((v, k) for k, v in p.reds.items ()), reverse = True):
	# 	print (f'{v} - {k}')
	# print (f'total: {sum (p.reds.values ())}')


	# a = p.parse (r"dsolve (y(x)'' + 11 y(x)' + 24 y(x), ics = {y(0): 0, y(x)'(0): -7})")

	# a = p.parse (r"\sum_0")
	# a = p.parse (r"\int_0^1 a")
	# a = p.parse (r"\int x")
	a = p.parse (r"\int x")
	print (a)


	# a = sym.ast2spt (a)
	# print (a)
