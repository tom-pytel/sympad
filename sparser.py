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
	if not var.is_differential:
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
			return AST ('-ufunc', lhs.ufunc_full, (commas.comma if commas.is_comma else (commas,)), lhs.kw, is_ufunc_py = lhs.is_ufunc_py)

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
			b'eJztnemu5DaWoF9mgMoEIoCQuCr/eatqo721l5ouJAwjvXTDGJdtOO2aahTm3eesJKXQfreIuETqZlAiRZGH5PlE8pB68fpPX7z36UeffvKnw5/+1w8/fw8/evrRB3/+En4+e+fzDz75CBzvfv7Oe/+Ojq/+/NUn7332N3XB7yefYsi/vvM5/P/F3z4mP/iV' \
			b'SN4n3y8+eueLf2Pnux/85Zv33vnigy/E/fE7evXd7Pxrdn7GToohpeLP4JCfRn5b+P34w0++ong//OTTj/W3UUer0bz31ecf/Q2jSY4vvqTUf/WuBmHnBx9/9uXfvvgAn//hJ1/+BTP7FWXsw48pOP3/H5+j/0cktU8xjMjlXZLIe59+/PE7KsnPVZLo+PzD' \
			b'v/zbl5qIz3tpw7MP/gP+e+fjz+D/99/9iPzw6ifvi8TQ9W52/jU7RWIffPTFB/jgzz/8GH8/+M/3MKfvfElZxSi/5ARCwr7UX5TV+x/+9cP38Y73pOw43GcfkWhBGirl//zig/cowPsf/vnPWCE++ZDqznuU6Hc+eR/Fhh6f4v0fv/PZF19+KknUCkAX/jcL' \
			b'G38aLgV45Hv/Ds63f3z79h9vfnv7j8L9Ftzfvfnth9+/+eW3b77/9qe3v7/5rfAG5w///BV8fvzH39X98w///c2b3/5bT9/+8esPv+WTb8H59ze/f/PdLz+J67df/m928fPe/vD27XfJ9WtyaTRvvk3OH7//Z7r6++/pQf/15rvf1f0rPYAv//HzdznN//Vf' \
			b'v/ZOvvnxu7c5pSlDP/2Y85av/v7Db8n99z9++ubHv6fIvvvjt5/+pxCNOr/98edfSjGlVP325rsyKnDo6T9+SD5vvv8+BXqTMvfPtz/knJKUUg4wT4Xgk8cfP//4y8/J439Sin78+feUpO9ybqCcS7H9400S8s+/pCf/UQZ58/P3veulXL/97pe///1NOv0l' \
			b'RfYtCOH//JALrR/u1x9/+O6HdAIV8ucsi1/f/v5LenSqJCknv/yUc0uR9k7eFnd+89M/3vyU5cd3fn14/eLo24PrXh7I4U/ocA3+B5dPL+UUzshlMNjBdoejf9m7wGet3gc3GL2ETgp1DHTldHhhDhbihP8dOF7qVbmWLhwpVebE/3kHvu3L8lJrzi55X15C' \
			b'J7gaz/8FeEATX8oldIIrwF882Hg4sk9AB/xCwind4AP/mYODEA2nLV/S06OltDYW8+Y0a/alXuRLfG7c4UVr4ULAv3zJlaetFwdew0ggOY1NLkcphKRD5Fg+wb2UK8eWUtI2/F8AIbT8XDhDJ8qWigNL5mVxqu7iOhc6FjZmk/5s8sYnUyLlOicdRCEX+Tyg' \
			b'RDBdLJKQrsq1sws+X4j9C0dDWbOW/3PsAa6jpYRYI6daTJgYTo3n/6CGHz1XaoMVhQraQ9XBmiQe/qQeNkgxcxrhFIqa7oUHtRgMi4eFQZea8rRtxYHX8HYQLWbCcVtJp3F4SepK/3I8Px1c6s5PR0L0E2BP56e9m47WFynLjUQSMbjQDS5AfMWFToqksXoO' \
			b'jZwqJqgNlJMTcWDDbTgJyWv8cv/SEVQHRgxVH1sQttfuEKCcQUFhactzR7xJ9bk1oVozCHW0VM6oESCc1caB93HmOlYJDQjTQaVtCs2Aful6vuL5SpuvBL5i8pXIV1I8R0N5Ny3/501KY7pky0voRFfk/0B8L19mJ7ostwq9Be+muuDg8bmO4BkGy6dQxqSm' \
			b'IgVTdYvxcumcDvzoxvB/AasEN+WGnSRKbMTiYB3eEDZUj7Ao8CJfkvOTxInt/OCc1r3edb0CFyhBXuqlanMQv2WdS3+oQPkWdKC0Pf/nMU98D5yhEwUAOiOgqhL8hUNgmkBzQM0tzDsgveB+36h+owCGATjqC8qdkodV32vFtKIipYVIrWy1EODiC5cVA56S' \
			b'ejN66knIUIAvSCBSCfG0ofjPLqVTSBLVi45aoLjsSVytXjJ6ReonOLg4QU4+xYdnofdAvZLOji3F1Dg5VR8QTEOCaS3/5yGSVqRmyYnBugNj8cQnWt9Ri7ckKgOljR4Z0w0JCgNF/s9juTIkCE38ruT5v+KdyAswneP/6HVI/Bw50WXV86Wcwpl6MIggRaHj' \
			b'ipAw6Bt5LfH05mX1fmzwntqVt+qBL1xyBVzwrvf6dGig6BqQC7AKEGNJ50F9gfoP+h1aP+rwE1bB7gDSAPF04GwPDbxnNCDrBhpyAx4N+DSgqBooChCUwRD4B9jDdxfQdg38wZVwwDsAnY3FX7gT0tWc4BcqXOMwJMTgDgZdED+kooFkNJCOxmIISC5IpAEV' \
			b'10CraOBhDTyigWcAAEArNVChG5BKZw6dPXTu0PlDFw4dxnHAVENgjBvOoSV0EM0JE9DguwAIDWQDir85QcCTw/cUEHeL1RZeLwD88H6CbQzSDcnGPJ0gTyeMGNwgt8aiG24GSTYgymgO0R6iO0SUTXOI4RDjIcKDMe0QHhKNehvKHV6TDb6uQq0CTQK1Fl7V' \
			b'4AUVVBRoRABJcIidgArkANUgYtlh5vElHdotvF8gjKAoIzwGUwUPBG98pQfnS1Q3kDYo9hdY3ngBb38J3pZPMcn403IozAn6Ygm8JLqTb0O+rxHudE5x17pyI3XlRceF3nDpYklRaXeNVCGuG1iqeNpY+XVyWxPlQifhperJjRjCc8xc2TrDtYjrWHNKoehC' \
			b'1Ug3WssMVyfTarXhakCljuXf+lr8t1v8UOBO9ImjGiAF9TX1Y7hGsEZIHnhFVIsl1UJlUfg6L74UcZnLx89hURnLCjioeMMqJ1VttJIVlYsr1UhlkgpU1pqytgzryUT9gDqBxeBOUg4nlra0B20HWue5nmsNL+tzUY+17nJ91Qpai+hORYRKk9lqnLzVnUSJ' \
			b'uiAvbtIknL72OaW0OWtc8nbXmPPG9aKxWhmc4L51yum2q4r6phV1U8v3dsv3RcNdv9cvWN/Xcr7NckYFXwv4hgv4RWNkLKdphfpe+9KGXgtwqBwSdnAHX8v5esvZiL6m1216YZNuj7zq6XANnTce381B6pCIxqM8UWAQHwin1oFrrQNQuq6W7g2Xrq+le8Ol' \
			b'G2rp3mrpvuh09JLfwTqZBDnpqxjl9mUdEHugATEXax/nhlsXZpTbk/R1PE0e7KkwNL6JA91ehkS9uXtU+mp+4qlNmpGgySyey9wan5FR1zbuur2VmVynU6ttnRi5ByUjs1C2jnvfsqrR6UmyhcFf7WY7+fXcuCJfj9z9jtwvw/aOjRZFi5MzWDB1ZuzxJi+j' \
			b'jIA1gonIGjByy42dmLCcZACl1UkxKWO2inrh2b/lGtBKQZNfWbIkF1QMMjfmRPm3/XltJ8ZUntPmOUmekxS4T3ACvxNWg37dqcW9oJI9vxYELrAQqzDvIMzAtT9wtQ9c7UM3J1NVeFW2S7JlFRFYRcRTraj7lXwQJS/6WYbDxbA1qk7HvL+sts23+6ZGxsst' \
			b'Wy231Q75hsoVhNiy2Xkt19spV1w20IqBOfzWAry2AqSlALVF3lKBYim1smgD22QtyisuSnoNEuFXo+0L67Xw8qe2DhzfbgtseZOMztRivuVitqGW7y2XL7hr+d5s+dL6Yu6G0m99U7q0NyVcAUx9EtdI30TGe60WnKVOS7lKrZM7vIQ4yTSgn1pw/rUsaD/Q' \
			b'Mke6yRC+aw14+hrwmhYuYmHUQni6ZtgYbW9m2N7SSB6/8tbieYriaUXpsZZ0Jz4zJykaT45aJI9YJMYISZgzPOPLsIlikcczlmoTTOFrsTw4TWyV8+NQu8r5EdRMZ1XFy4uxmJTRahJWLF6MFclMGmHBRs64fIyGqPgNuxPAdx33hGphPUSjOJ2qdB/sJehk' \
			b'pecXuSp7mgS5kzG/bkjG2wnh8gCKmfuW8BxcilCL734aR8tjqZsXOMis5anlsuEBgRc0DPA122a3PVtdumjrC/Fjl2900is5W6qOCeRthKi53fVxqWo0bVSjbjs0sqzFtcQq2lDqHguD96EiO/yW7fBbtsNvcwUwbTojC/yWLfCpYbfk94JtOfMARORQMq7n' \
			b'mAGOw3oZA/QyvFuLf701PRdP3YHxlidAXuOak2p/d5UlR9qsKrWN/a+zJVZVZosyi3dYEIersgjB4VQRvHWdUKy6+Rp1My6e4zrf1jq/tc6bKrKtIqtLKK5UTcjYfXC1zm8dSzrVOn+VdR6X4hpep4k/OJLwkj6whD9QnkY/H2JkJYp5qQsaTP4yBFlzGR71' \
			b'oTs6jrXud3nDVcdKXTlJ3QhaIwyPU9GZjVwhjONz2fSerchMsWk9WTIZNVwyxVa5ZE3Dj6AfJw80Jwnv9cLInqto98EJoOEzGl2pe+1ec71DQx0aS66L4q67GBthRDfcjdFOXHdj15ExRi0uWrG0ILvHCpirryFsMVCL8FqLEG2aDNs0GbZpkhZspAUbsQ/B' \
			b'X8+vlM5ze+ZdQ6tNx73209JWnW3ddfIeFsNwfeZ3XLRwMbL5oKm2LI88/mCnugAHNl6I0qdgoyYyQOFfx2M+kYsyclFG7ueS/YPhyRUqWl5SUWffb5RWPnAx+6h9WDRZwzl55pW8YJ64DgXGV+DAgWtK4JfawIgLXOui9lShSG0dJrvCmoEFY3l8y8r4ln0p' \
			b'1t48FGJ5KIR+ILdWRigsDTrQe412U0RVZfNvee8RK9lo5OZJVWY5DZEfGiP/0DOr8rnWKsbGdrbS5XYL2HNL5aHROr20YSUBVFYna8Yda2EnWti9lBEg1sKOtbATLexeyjf2HA4IQapBorV93Wb7QnA64aJjLjrmIhb+oZXXebzm2Qtk51/K13J9rSA3X0Ea' \
			b'2YocBebpFaxLFvC+rgJ7qK55JGFHbGNYCGymqOtAWpJ8uRgIm2UQ/R2ktAK/OfPSBNwKHfdBx03Qcevu2hyvsznCQwPr6cD1I2iVCLUxPty+FFE0H/dG5bsCjXxYgBoVNVPeFJ+ab6zF8VC6savCfbgtctpU163W9VbqOHKkcuNKuREPHQOjk9Jkm7TT4fUJ' \
			b'X/Tpm9po44Pf1e6KGs0C4yLr8OsTrVboJBUubC4wfOWnHgD3BkA8mCluplFSiSJ2lM1BHjmDQbKGeei3Yq53XKo8FBC5zmBaMaVUIwPXRioJz/WMmlkj9cIU9nRe7Ou4E9PghzjwA0YoWPwOFn5tCT+1hN9ZwtKCBDRY83HjNdxjAndCgGrT4rJtqAEtLt7H' \
			b'KoOD3pC2Fndiw+2McCdj3EsEN8zFXfpwk2oSJVzHAoMSa1GoKFWsbyha3PcIJNuiAsF9eHA5Cu5bhVtV4Qci8FsRkL8WN5HD5eK4Vhz3TMJN5nDlKG44hgtJHRYW+OPaFWzEaLCLxrqQ1xYXZ6DlNdSVFlc24zYa0EoMTjJDXgyaqaHFSWOhrhzhaSCAYwOp' \
			b'PULqj1DERyjpo0X36XDs4PIJ/cEJf1gaR1QQR9QMR8jL0dBluAX1wBGkcMRGc8TyOWJBHrEdHbH5HyG7R2z9R2zyR2zvR2xUR2ztR2zqR4NnUJ2OHcZDwTuMAa5A2R49ekNhHEGQR6ioR4zV4c0Wn40JxxZ6xEpyjHh7g3Hhw0DcR3w0iPAY0AfK6YhPwpyD' \
			b'rFASR0wMlMfR4EM53oD/0alnMaBSO6L+OjYU7GQlx1AJjy0m+4ShKK8oUY9JBS+o+kfMMUrJoydUpiNU0iM0lGPASDAU5oPiBg8qGHQ09NwGL8Mfygm17NFgTjE/qEmPqC6PmF0SPD7VkBcGxnAQH/x2+AsRgOo8dpR8KglMCjwD84gCh/p6xCdgxiNGS+WC' \
			b'zyOpgW/AxJwoG3gGkUC9O0KDPwYUMGYLQkObO2Lc0UqyqXpguWJiSbYQApTpEWrzsaP04gX0aEnMEGHECLqvUcWhYqtqraq1NWqt6rSq065Ap7Wo06Z0mS/U2WmFRuuP0I5oNzut4M5fT7fouG5g3NM+kNZrRzTfJWo8s1PrtSOaLxTar8kaELcrmdWCAcsm' \
			b'LOi70Nd4YZ/OC3SjVcek7gtrtN+96b/AyYFCCenfQ+vAMKIFL1z5hZ3qL4wpQEyTKMGQ1GBYUoSHf/lXyOfwCgndmVeArP+Hy7A2a0fqKouODGdqkoYS5pRlmvLqjwdwLz6rzyD2uKJEiyGGhZ5+qU3byaGtnmYthjrOVGzxcqljLT1Vm4eteiM6OLKioyw4' \
			b'WoEjMGmkw2a13BvSaniEJg1t8UjLssoezFLg10VVheO3cPHbraTKIRyOb+Anq0mtQzgcXRlV736Higd/3GN1qOqx9mD1WVL5uJPxmdq3ovrD3dQ/btuXENDswECTUNCiUTnhwDASToiHTtDQFnhADYKF7hYIgb8lIrBSoYagLzgF/iN9hrWEFdsoLTRwpgbG' \
			b'5Jgb6lRy0EMFHuwnIQQkNAzpCpoQI7D+2YIqdIIVHX9xaFHumsALpb5EDC3WxCTj8GTT9v5GiZPTiQObKd1N28uEiEs4JDIZsig9h8ZKT8KlYSp6KSJ9wJlhbpEP5V34lS7QDnTppIQaPWoAtSID+jwkhs8SxVauXo6op85R+FHR7eFfqic9CmrdWGJhklTB' \
			b'Qy50EkkYgBHj3ERGqlsMx7KkpwCJwYWQGlYxSV7asNpebeB0JXAyMtvmFb24te4Vlb4HnuKrVPeKXpPi6RW+KTFYUU+/wncX0MOv6G0FFNsrfE8ApQMeHslr58jrnhS+a/ouDw3cMALd9o7gLaDbA67AtoL2WkHrGbR+AbRY2fyAtZ4uYRXy6QQrh5/GrIRK' \
			b'kNXz7EyQLXpoKX5KpkBWHzjXY5NAU0gd67RReNN/5ChNk6/peqEHB7GUFD62H1/QlC4qUDX3EmYqzn7Xj9S20tMLOP2Qmf4cmWeRcqdQs1tInGgp+RyFpd8LS81xH5ZSxouw5HAlKv0kKf1WUvpMyiyjSVD6DEpJvXLSMye9YFJzzElaB8lxOI4w0e1h4hQN' \
			b'b4ODcQX/Hop9upFK5d9l8w+JZ1F4Sx1NknIfgBRaBiTZzWEWRyRbCWezU7FHzxDssZ+EEOxp+FnsSaAJ7KFXiT0KyiOVWEfzI8ewl31N10vg4BgbymQtLsRLGZfO40QsJe7wguKOS0rkPjbuidWvZN5I5D6lIhTCRuJpFseIxyW8g3gpxz3iafEuEU/CFcSj' \
			b'chwlHmVuC/HaPHBayH6KeG2eQ9LUC/FaHkPlwinKmJM0JN54d1BRN9P/8zvnpZ4D6B4TchVwVwA4Ni7An1nAYYAe3AoLA3ZzmGW4yb02OxPcTAE3k48EN33sLNw40BTczMxEXO+Zo3RLvqbrhR4csxN1KddKtvEYemQrpvHIsxWhL83oncfKPTnNYyFn4ppk' \
			b'bpRrZi/XNL99rknJLnJNcl9wzUxyzWzlmslcywmd5JrJXJPUK9cMc80I1zTHnKR5rgnPRjAWKsYqxirG1mHMMsbsEsbsAGO2wJgVjNk1GLMczmZnwpgtMGbzkTAm4ecxxoGmMGbnMFY+cxRjydd0vdCDYx5jmmvF2HgMPYzZAmNWMGbXYOwsVsGY5LGQM2FM' \
			b'MjeKMbsXY5rfPsakZBcxxuFKjNlJjNmtGLMZY1lGkxizGWOSesWYZYxZwZjmmJO0F2PxiTF2R7vBBwbYjEHhc4PSqGHiY8Bo3kAxQ8iOgScweJZsFduBsWI7aq1IVxfREziczc6EnlCgJ+QjoWeVEWO7x4qRq17+GydPShAWaJg87mrpiBNdYQ1ZmqBCTOlO' \
			b's13sRdNd4ken2TkOmLAXMFqWfcBI+e0zlTxny1aDSaoLwpYkp3HD8TYbTbaF1SRdLg0n6UIfJkqPTI1uMzVmrDdu1W7yzt2hJXtJN2EziTPA7fOg0mRXyd0vofB19lG7TEgiS+1jnlwYoCQX/Qq5sHGJ+aSZtp4kL6WX3mKzU+lFTxJ6sZ+EEHqlpwnA8MRz' \
			b'9IoxioITgxqAb5hgmWlncNZ7/hjKsq/peqEHxyzKkgQEaBMxnKzIjEEnlxV3RcA2F4nJ8prh3/mjGH6a8aIgkHya4zHwmb3rAlKKe+DTol8Cnwojo0+ujAOQKssWAFIFihyjLSU11b+ikIxBzYOQkHyClElR+JLenf2r5lTHCes4YR0nXAc9nu4yS9NdZjDd' \
			b'ZYrpLiPTXWbNdJeRe212JtwV013sJyEUd/rYuf6aBJpC3Nx0V++Zo4hLvqbrhR4c84jTXCvixmMoO3Km6MsZme4ya6a7zmMVmkkeCzkTzSRzozTbO92V8tunmZTsIs0k9wXNJqe7zNbpLpOnu4qETnIsT3dp6pVjPN1lZLor5ZiTtJtjTeVY5Vjl2DqO8XyX' \
			b'WZrvMoP5LlPMdxmZ7zJr5ruM5XA2OxPHivkuY/OROCbh5znGgaY4Njff1XvmKMeSr+l6oQfHPMc018qx8Rh6HCvmu4zMd5k1o5LnsQrHJI+FnIljkrlRju2d70r57XNMSnaRYxyu5NjkfJfZOt9l8nxXIaNJjuX5Lk29coznu4zMd6Ucc5J2c2zvthiVY5Vj' \
			b'z45jPH1mlqbPzGD6zBTTZ+zmMMscCxzOZmfiWDF5xn4SQjkm4ec5xoGmOBbmOFY+c5Rjydd0vdCDY55jmmvl2HgMPY6FgmNBOBbWcOwsVuGY5LGQM3FMMjfKsb3Taim/fY5JyS5yjMOVHAuTHNs6t2by3Foho0mO5ek1Tb1yjGfYjEyypRxzknZzbPsGJpVj' \
			b'lWPPk2O0P1+D9XqeYxig5BgbfjDH1AiEfpc4Jg9DjqlTOUbPEI7Z4lCOafhZjkmgCY6h1yTHes8c41j2NV0v9OCY5VjKtXBsIoaSY/ijHCPPVoS+xLHzWJljmsdehlOBjHKMC3cHx1J+exzTkl3imIQrOEZFOMoxktYWjlFFYY4VMpriGD2YOaapF46RT5Ci' \
			b'KUqYk7SbY7PbgVSOVY5VjmWO8biiXRpXtINxRVuMK1oZV7RrxhWt5XA2OxPHinHF5G3zuKKGn+cYB5ri2Ny4Yu+ZoxxLvqbrhR4c8xzTXCvHxmPocawYV7QyrmjXjCuexyockzwWciaOSeZGObZ3XDHlt88xKdlFjnG4kmOT44p267iizeOKhYwmOZbHFTX1' \
			b'yjEeV7QyrphyzEnazbHZLTwqxyrHKscyx3hc0S6NK9rBuKItxhWtjCvaNeOKNnA4m52JY8W4IvtJCOWYhJ/nGAea4tjcuGLvmaMcS76m64XGptH5wn8WZJptBVkYOQYgKwYWrQws2jUDi+exCsgkk4WgCWSSu1GQ7R1YTPntg0yKdhFkHK4E2eTAot06sGjz' \
			b'wGIho0mQ5YFFTb2CjAcWrQwsphxzknaDrO7PUUFWQbYSZJFBFpdAFgcgiwXIooAsrgGZhLfZmUAWC5DFfCSQ6aNmQcaBpkAW50BWPnMUZMnXdL3Qg2OeY5pr5dh4DD2OxYJjUTgW13DsLFbhmOSxkDNxTDI3yrG4l2Oa1j7HpGQXOcbhSo7FSY7FrRyLmWNZ' \
			b'RpMci5ljknrlWGSOReGY5piTtJtjdYOOyrHKsZUc65hj3RLHugHHuoJjnXCsW8OxjsPZ7Ewc6wqOdflIHJPw8xzjQFMc6+Y4Vj5zlGPJ13S90INjnmOaa+XYeAw9jnUFxzrhWLeGY2exCsckj4WciWOSuVGOdXs5pvntc0xKdpFjHK7k2OQiavTZxrEucyzL' \
			b'aJJjXeaYpF451jHHOuGY5piTtJtjT71DR+VY5di1cAw1DhQy/sxyDAOUHCNNJRxjN4dZ5JiGs9mpHKNnCMfYT0IIxzT8LMck0ATH0GuSY71njnEs+5quF3pwzHIs5Vo4NhFDyTG8oBwjz1aEvsSx81iZY5rHQs7IMc3cGMe4cHdwLOW3xzEt2SWOSbiCY1SE' \
			b'oxxDn00co4rCHCtkNMUxejBzTFMvHCOfIEVTlDAnaTfHtu8ZUjlWOfZMOcaGHm7J0MMNDD1cYejhxNDDrTH04IM5Js7EscLQI4V02dBDw89zjANNcWzO0KP3zFGOJV/T9UIPjnmOaa6VY+Mx9DhWGHo4MfRwaww9zmMVjkkeCzkTxyRzoxzba+iR8tvnmJTs' \
			b'Isc4XMmxSUMPt9XQw2VDj0JGkxzLhh6aeuUYG3o4MfRIOeYk7eVYWzf0eDyOje1uVXl2hTxjgw+3ZPDhBgYfrjD4cGLw4dYYfOB+cGLwoc7Es8Lgg/0khPJMws/zjANN8WzO4KP3zFGeJV/T9UIPjnmeaa6VZ+Mx9HhW2HuofxtzTEtUO4tbqCY5LaRNVJMs' \
			b'jlJtr9VHSmufalK+i1TjcCXVJq0+3FarD5etPgoZTVItW31o6pVqbPXhxOoj5ZiTtJtqdXuPSrVKtY1U41kztzRr5gazZq6YNXMya+bWzJpBICezZupMVCtmzdhPQijVJPw81TjQFNXmZs16zxylWvI1XS/04JinmuZaqTYeQ49qxayZ+rcxx7REtbO4hWqS' \
			b'00LaRDXJ4ijV9s6dpbT2qSblu0g1DldSbXLuzG2dO3N57qyQ0STV8tyZpl6pxnNnTubOUo45SbupVjf7qFSrVNtGNc9zaH5pDs0P5tB8MYfmZQ7Nr5lD8xLOZqdSzRdzaOwnIYRqGn6WahJogmp+bg6t98wxqmVf0/VCD45ZqqVcC9UmYiip5os5NPVvY45p' \
			b'gWrncTPVNKeFtJFqmsUxqvm9M2kprT2qafkuUU3CFVTzkzNpfutMms8zaYWMpqjm80yapl6o5nkmzctMWsoxJ2k31erWH49HNVdn0y52T304Bxm1+B2O7X03w303s9R3M4O+m8mUO6Yvw9DVxd6b3G2zM/XeDHEOz9lLAmjnTZ87hzlUGhhqqvdmZjjHdTX/' \
			b'jffgUrKw52Umj/kenOZce3DjMfQ+TNaWXThzEKlFTumKj8g4iTblLn9Ehrz4IzIun9rkHO/ImW3IowSbnLlBP06Keol4JIZhT06kMdGbM1t7c4a4x1HaQmozXTqTu3QU3NAnfiBc0bkz3LkzjMEkBk7hAIMWvxwNtU751zSv6JWhBOAl7Rky+PDMlWPQ1g7e' \
			b'7XfwWu7gtUsdvHbQwWsz+tjNYZY7eC2Hs9mZOnht0cFr85E6eBJeyYcn2MDakW4eB53q5rVz3bzyyaPdvORrul7owTHfzdO8azdvPIaTFWlJT68tenoSpI05sqWe3ln00tOTzBZip56e5HK0p9duw17u6Wlae9zTgl7s6XG4sqfXTvb02q09vTb39LKMJnt6' \
			b'be7pSeq1p9dyT69lxKUc8+/unt4lbSpSQVdBd2WgYytKv2RF6QdWlL6wovRiRenXWFF6y+FsdibQFVaU3uYjgU7CJ9BZBp0dAR0HnQLdnC1l78mjoEu+puuFHhzzoNO8K+jGYziptAR0hTmlBmljjmwJdGfRC+gks4XYCXSSy1HQ7TWqTGntg04KehF0HK4E' \
			b'3aRRpd9qVOmzUWUho0nQZaNKTb2Cjo0qvRhVphxzknaD7pI2Hamgq6C7MtA5Bp1bAp0bgM4VoHMCOrcGdI7D2exMoHMF6Fw+EugkfAKdY9CNTdzx5SnQuTnQlU8eBV3yNV0v9OCYB53mXUE3HsPJirQEdK4AnQRpY45sCXRn0QvoJLOF2Al0kstR0Lm9oNO0' \
			b'9kEnBb0IOg5Xgs5Ngs5tBZ3LoMsymgSdy6CT1CvoHIPOCeg0x5yk3aCb3ZXEPTXrLuqz2e0dqef65LPDz2dX+t0I/QLTLyzQj2gTBgQMBQGDEDCsIWDgcDY7EwFDQcCQj0RACZ8IGJiAIROQouCUoO7hG6Y4GOY4WD5/lIPJ13S90INjjIM0FZlYqFJQFo7H' \
			b'ciJ58Z3KQ/ZKSJSQbcxxLiHx7CmCRMl3UQ6ERMnwKBLDXiRqWvtIlJJfRKLIoEBimERi2IrEkJGYZTSJxJCRKKlXJAZGYhAkao45SbuReEkbnOzmoSckxqvpB1YaPhINzUYinkaoeNq7rRebctolU047MOW0hSmnFVNOu8aU00o4m51pW6/ClJP9JIRu6yXh' \
			b'lYp4AhWPfoSKFAUHazu9YWqLr8KsEx+JZGx4TqbY6qtMx+hWX8nXdL3Qg2N+qy+VhJBxIoaTFdkxFeVy2vBLQrUxx7e07dfZE2TbL8lvUQ607ZdkdIyKdq+RZ0prj4pa8ktUVBlkKtpJI0+71cjTcktLW39lOU2RERujzcaeGEHHSUpbgLHBpxWDz5R7Tt5u' \
			b'Ql7S1imX3GOsbLwuNj52TzEwD8MSD8OAh6HgYRAehjU8DBLOZqfyMBQ8ZD8JITzU8MrDwDwMBQ8D8zAwD+WGCR6G00wvsff8MQ5mX9P1Qg+OWQ4mCQgHJ2I4WZEZc1AuKwc1VBtzfAscPH8Cc1DzW8gfOagZHeNg2MvBlNYeB7XElzioMsgcDJMcDFs5SJWG' \
			b'GVjIaIqBIfNPUy/sC8y+IOxLOeYk7WWfuaTtVir7Lp99pyviX/sU3/TmRetmadG6GSxaN8WidSOL1s2aRev4FWtZtK7O9E3vYtE6+0kI/aa3hFcG4glUOvoRBlIUnJI23T71fe+5Bey9549+3zv5lkHPj1kGJgkIAydiOFmRGTNQLqevfEuoNub4Fhh4/gRm' \
			b'oOa3kD9961syOsZAs3EZOw6B5O99a3p7HNRSX+KgyiFz0EwuZTdbl7IbHn1J3/zOspr85ndezq45EBYaXs5uZDl7yjUnazcLL2mTlsrCy2fhtXDw0fuBDfcDm6V+YDPoBzaZgUGW/tHvYj+QH0b9QHGmfmBT9AOLI/UDJXzqB/LyP/rRfmDD/cCG+4EcZqof' \
			b'2Mz1A8vnj/YDk6/peqEHx3w/UCWg/cDxGE5WZCb9QL6c+oESqo05vqV+4NkTpB8o+e1lPhXUeD+w2cbA3A/UtPb4pyW+2A8UGRT9wMnFf1RBNvUD81hoIaPJfmCT+4GSeu0HNtwPbJh9KcecpN3su6StXCr7Kvuuln28+i8srf4Lg9V/oVj9F2T1X1iz+g8b' \
			b'gKz+U2diX7H6j/0khLJPwif28eq/UKz+oyg4Jahs+IYp9s2tAew9f5R9ydd0vdCDY559KgFl33gMJysyE/bx5cQ+CdXGHN8S+86eIOyT/BbyJ/ZJRkfZt3cZYEprn31S4ovsExkU7JtcBhi2LgMMeRlgIaNJ9uVlgJp6ZR8vAwyyDDDlmH93s+8mNny5AMZN' \
			b'rINYZJlyTPml7FJmXQuvro5VvElLWNqkJQw2aQnFJi3s5jDLrJJ7bXYmVpmCVSYfiVX62Lk9WiTQFJ/mtmgZZ1JKhel6qRoc80zSnCqTxmMot2TBC4lGZg1/NBLBDm+6EnizlTC10UrYuNFKRo1mqY8aKbBF1EgGC9QYQU2PMlu3VwkmU0Ye4ecwk7dW0ZQr' \
			b'ZgxjxghmNLecpi2YIbxc8HYqtWtVu1bXgyvHuHJLuHIDXLkCV05w5dbgynE4m50JV67AlctHwpWET10rx12rAlqBuYU/qGT4whS63FzXqnz+KMaSr+l6oQfHPMZUAoqx8RhOVmQmJOPLCWYSqo05viW0nT1BGCf5LeR/DKmgxnnn9vJO09rnnZT4Iu9EBgXv' \
			b'3GTXym2FnsvQyzKaZJ7LzJPUK/McM88J8zTHnKTdXatL2mGldq1q1+rRWOWZVX6JVX7AKl+wygur/BpWeQ5nszOxyhes8vlIrJLw810rDjTFJ7+5a5Wea7peqgbHPJM0p8qk8Rh6XStf0Miv4Y9GItjxzBzPtPFTqPF7UaNZ6qNGCmwRNRyuRI0f61r5rZTx' \
			b'mTLyiNmulc+YkZQrZjxjxgtmNLecps1dq0va16TipeLl0fASGS9xCS9xgJdY4CUKXuIavEh4m50JL7HAS8xHwos+ahYvHGgKL3EzXlIqTNdL1eCYx4vmVPEyHkMPL7HAS1yDF41E8BIZL5HxEqfwEvfiRbPUx4sU2CJeOFyJlziGl7gVLzHjRR4xi5eY8SIp' \
			b'V7xExksUvGhuOU2b8TK7m8i14OXCRuumNsuqXwG47tG5yIYPccnwIQ4MH2Jh+BDF8CGuMXzAii2GD+pUJMXC8IH9JIQgScPPIkkCTSApzhk79J45hqfsa7pe6MExi6eUa8HTRAwlnmJh5hDFxiGuMXA4j5V5pXks5Izg0syNsSvuNXBI+e2xS0t2iV0SrmBX' \
			b'nDRwiFsNHGI2cChkNMWvmA0cNPXCr8gGDlEMHFKO+Xf3KNwlbQFSOVY5dtEcY6OIuGQUEQdGEbEwiohiFBHXGEVEuddmZ+JYYRTBfhJCOaaPneUYB5ri2JxRRO+ZoxxLvqbrhR4c8xzTXCvHxmPocawwkCDPVoS+yLGzWIVjksdCzsQxydwox/ZaT6T89jkm' \
			b'JbvIMcl9wTEzybGtJhQxm1AUMprkWLag0NQrx9iCIooFRcoxJ2k3xy5po47Kscqxi+aYZY7ZJY7ZAcdswTErHLNrOGY5nM3OxDFbcMzmI3FMws9zjANNcczOcax85ijHkq/peqEHxzzHNNfKsfEYehyzBcescMyu4dhZrMIxyWMhZ+KYZG6UY3YvxzS/fY5J' \
			b'yS5yjMOVHLOTHLNbOWYzx7KMJjlmM8ck9coxyxyzwjHNMSdpL8fsJW26UTlWOXbRHGOrv7hk9RcHVn+xsPqLYvUX11j9YX0Wqz91Jo4VVn/sJyGUYxJ+nmMcaIpjc5Z+vWeOciz5mq4XenDMc0xzrRwbj6HHscLGL4qBX1xj3Xceq3BM8ljImTgmmRvl2F7r' \
			b'vpTfPsekZBc5xuFKjk1a98Wt1n0xW/cVMprkWLbu09Qrx9i6L4p1X8oxJ2k3x2jDDCDJBe24f2k4W9plH/yh7V422uId8BauEHHNU+wbhboDUcfDj0fa9nSOd7RT0cC8wxTmHcf09WyzxsCDni8GhMmdNpIqTDywaeqRNpKK8ug57qEuMdM2HmbOxqP30NHd' \
			b'ozDJ2MNhi48y/OAYQ19DH1UW/GmwtIdU5CrcnEZjKzFoCusPxo3GtYDB81gZg5rjpsy+VZedmmIzK81DWv4cZx+HKf89HGqBL+GQSniwiVSc4qHZaihiuMmlTaQ4UbPGIiYbi2geBIqGjUWMGIukfHO6CijiU90r8sf/bYP/Ax3h/66l/80rISQlEM+Ij+3h' \
			b'9RwdExdLKI4SsVMKEgIFe1PAG9Bu0eCQwDbdERNalSRSCi2SRyhDdLEzJNnaSRqQY4kYZ7QY2vxtIEQiwxwRhAZCASaAFa2vGh9V+mpt31PzIzp+WcGTZs8qPelz1eErtPeU6t5om6dKerYTkvVvX8Um/bqsVJMWPcqWQ9MKc1/HYagjl7XjUDWe285t04eq' \
			b'COdVoOq/pPlQ7ZHOI22nqg41lpnXWP5ilFab9Japumv1222Y0V9bdNe2V1V6mbwlBVa8aTZdVWT3oMjaYh3jiDLbrsjsylev015FNjPisF+XuZW6zOzQZ+2V6TS3Qa/F9Xot+vvVbT29Rr3mh9Bt9qn0W0ufkluv31rWO9t1nL1iPdeSNluv6/wGXdd2fo2+' \
			b'c/fV1QyP9OJ2Nnq6oPfa5oHf48APqkMDVaHp4gXowI0jl/fWL72L/tul+3TY8eLe7Shl5d86PYiD3o/xrkev84S+Ew1aX5BORGHdU0cWgb3x/e/wL6j1ryAzNAjn73EQ7rRFM55PPG14E1zShmZcG0J6nmXPNmm/sbma4TwN+EO+03wN5L+F/LNWDIVmhMLH' \
			b'gXyat4EqAHk2UI1ZWzbl/A38uafQnKQ1ezM1uzQnxvAA2nOttpzsGbdmjUn31b417tCOWCLTb4xUXkYmIB1rSqod2DI6VpuGJC2qU6cjef4D893QhqpBjNyOqDOOTd5YHE8MvW+GJ5naeEiVWtVpoU5PTzNQeBGDhE+qDidVYR0olM5zvN+Bwnh4fWnzszOm' \
			b'SI84V3tpKqx5wrnaQn117rK112bNxXZhndh9+Uubs71g7dXSjvlPOmd7+Ff3CoBKHd3u8jTZLu0FqULpYl25TU22VYuhTeL9zdxez4vYk5ibkGkqSYY+rPgc9NiOtzAWUHuvr2KQxRtRYPALiUP5Xp4iGzG8flRlBr/+HpRabzCuPwhXFdyCgkN1Reb2R6x2' \
			b'l6zo/AXouiMWFKbJ3l3lmaY3vDYYVIPiu3cFCEl6Eh0Ipfc4+m/PGsuxhSePaYbX3dpLXUO1/eIVHyUwPKra83Gv7hsqPmweTzHeFu5J95297rUPoO3iE2m7QtOZcEFve0+s6aqWe4LlEj0Nh8V9oS93l6HgHki5mQdQbt0FKLdYlVtVbpej3Nqq3J5AudkH' \
			b'GKg7XYByu+Cp06rcnp9yu9hhuZtWbu5GZiEuVZNdxGL9q9Jel6+4HkJLtfSwK54kvTetdPgXNL5XqLXRzgNSWhXUzSuoO1io3Y6SIvPzi1ZS12/Kcc/maBF3CXSkp0LVU1VP3bqeoj7IJbxLUUKqllqnpUL3igET/CvU76SvLnAlQNVXVV/dt75yl6KvXNVX' \
			b'd9JXT27vv3Uf5TuswzS83fHVqrHhtsQPocqMqLNnoNKo6fbUGl7QBU24KXbx94BqjqJv6GxR37nL70WebdD7UEqv7VjxUZL2KD//5GsFqvKryu+plF83VH5dofy63t+DKr9uvfLrqvLLys+K8ut2Kr8HWCdQld8VK7/noviwxfc7s6es+Pyp9/eQis+fVis+' \
			b'vF4VX+7qUuJ3Kb0HWC5Qh+fq8NxDaTVuxbdpmnEpmutixud8g3qKpj39A1j+Vz1V9dTd9ZQEek42ZHdVVPwdPv67CUXl0I4MGxN+4xG/w4cvWLglRIBf1l8PYdxf9VfVX/egv5qqv7bqryb9PRf9dcv2+85dqQ5zd9djkL/1uqylKSYcab1YvUbV/EpN+ynt' \
			b'T6La6Mn30oVkNXN37cbxrNVwhr6nA97Lus6ibsOPETfYu/S0yaO/ZeP/qt2u+02Nqu/VarSnelmjJ9+TRmvvSaO19/nONqrH6uKAC9Nhz7OXSQ3xmS+0XK+3nsdgvjWvCGnQztDBvcq6OKDqq6fQVxRBXRi+RV+xyJ7P5KNBNYV1+2TRYUhfPfnigKqvnom+' \
			b'aprHtAG7NYUl0nte5hIGOoLYIE7wpmXo/So8uT1/1Ve3qq844AWsvbwBdfUsrbvaiJvv0LhVeHLT+6qnrl1PcaO9LNP6q9VTHHNVU7RJ2CtCILRDdLSkr6rVfNVX2/UVNoFLXgl0teqqvlYV+gqHq/jblaEazVc1tUNNxaqmqpp6RDVVbeOrmlpSU1TXH8fg' \
			b'quqpqqeynjqhniI1dSsm8JC29DHdi1FZuOrAPrHqsvIR3SkV9uSTgrekv7DYj3jnpWoyVBCXoM+wgOa02uZvcUDhvcb2Yk9YT7E6taEhj3B4HXCzGbiOpQZ/dDmWl1FRBLrcHV63UCJtDODRQh2Bv69fgvvFsTm8xsgp1mMLJ4euwUCgLOheEO5r1DKgBA5Q' \
			b'ZlAIUJ+hAkDhgnCg9DrUsRAC6i3ZEQdML7ZHbHv6TNAzJ/xD4xTUxhAOaknT4jYBuMENKF3QRHAGhdZAgTUdagBH5y0IswWZwB8lyN5HguxhxT96nMPHhdkHtqTP/bonO9T87uxfAzlk/dyc+1JC/FRCQK1AzYJKjB/IO42lK4wlDT8dnLU5NHOIlpPbDJIM' \
			b'fOv9w6rKH4zKfz1/eHJxZvgO1Njoxs8qedqxjPwpb+Fp8gbtgL5JDXkEMt/DP/4kO5dX3JknN5OtgHvCwHUQXhP9dDadn8kqvIEs/sPXhP4VgjMB2RCEe36g0Ytzyn5XZh9fBsKsEAzJwaMoUIMVe2mNSCaeCedkaZobVS3SGjmBmpVMnHHKidawN7QpCbKY' \
			b'tsYEAWWh4qsh3BOiCBj8YiuCdtPCxnpNbzb2XPD4VpKE33ABgBY0J6wnWhj46pcOev8zh961wSHexc/wb/Kes8ds/Tu/+3TmHH/6WNr6MQ4DUh2Cqxfahuht/QkPFk/Ta2P4cn3AV29ubFDT7JYmd9rX6qAmp5aHXau1rQ9pcBktsD3ko+yR8ZXUF1t9YA9s' \
			b'fWg6sOelLrcU1m6MfNfBFaytSnxVFTKHZ3Zw9TAXq57t4UkPFo+9S+vBoaMna0D+KRpROOw/cOTrLvc/6WO4triqa1dVk3h4ZgdXj73d/5k6cH/qFjuMdznMHe+Hg6UUaiNa04iwr/C8Dq4evTGZhbqxvh1hNbi3tkRzKHLgFER5vvPA6Z09d7LM+gM5qXu5' \
			b'om/pwsF1B98e/KM0MssNDTeCoMbmDjw0HvljAB4nzNr7b4C4+4mWKu1isqkhukM6sCstLpxQcwsHzwbmv8UbdhwSr0ZvfO+KxfrQ3O0Z4aSu2C4G50mKU9Xxq6qWPzyzg6tHcwU6Ph4u42CJ3WmU50Ea0VpJzzWS5QbSHdKBk+fl+dSBM+Zrwt3Xsf55XJSm' \
			b'6sY1uhFtfZ7XwdXDPphuxGpwb/oR7bDu+0DDpl13suTq6My6huUOz+zg6uEftGFhNbi/xuUPD3Gg0eCuO1mAdeBmVftCk9TndXD1eLiBm7Ia3FsbQ7PhhznQJnfXnSzHapWzrpm5wzM72NbztLWZ3aUDuKWjN9vBS6XmD5sOHCLcdAMZwZulm3AUcMKPpdzU' \
			b'RrimEeKSi+d1cPVoH7MRljXh3hskrph54KNch3KHeFjyFz56UkxmXEYDdYfLOfBLs/TTPcLTuLpsGU0x99xWtXLcW5udLGR/WHngwqT1oacOXTy2725c4oU/eYXXwQl194zgyAzmo81dXmYzj4etB2cobL5vzYErCh8i3tmDq9CWUZ6rbfC4rvVaDy6mPWNJ' \
			b'T2yrcGltHlc27zo4S6edd685cBXxw8U+dnCt2jIE9VCNf9f86C4l4A+Pf2CVvZ9AdHCx7RnxqsqgXxnioR508ALkPQZItUr1q1R3qAcdXKXuNCT49IjZ+66JG6XcyMHl+ExNqXCrmxs5uBwvfCTwUobo4WG7D15llv/uEtdZpOeP6HtueOBMUK4rd1rm93zq' \
			b'Ci4wf14HV49qObauejSHZ3Zw9fC1eqyqHv7wzA6uHtUubl31CIdndnD1iLV6rKoe8fDMDq4e1dxvXfXoDs/s4K0N60rKVdUD98J7XgdXj+bw2tJWorK00rXpAuMHasRr3Le3MXQx4s687AF94rLqQLnQNkm4dRDUN/yUNm4s66QeuvHQUN79Pw7tz0JjWdMd' \
			b'WKP6f63MA7nejqlYY9jmy/GWqYPddigE7iTcOQpveZ9lqo1Rap6jGoXXocZwXKBu+7FoDS5qbqq12NxIbrRTM0hFdmmmXZFpN+RyJ2RcZo0LpHEvVNkP9IT7HKE9REfbBqD0We37prffa8TlgVxgvsVzQ4sfOf+QfHB3tCZO4rX5Csju65f/H8Ob+Z0='

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

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add, expr_var):     return _expr_intg (expr_add, expr_var, (expr_sub, expr_super))
	def expr_intg_2        (self, INTG, expr_super, expr_add, expr_var):               return _expr_intg (expr_add, expr_var, (AST.Zero, expr_super))
	def expr_intg_3        (self, INTG, expr_add, expr_var):                           return _expr_intg (expr_add, expr_var)
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

	def expr_varfunc_2     (self, expr_var, expr_intg):                                return _expr_varfunc (self, expr_var, expr_intg)
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

	a = p.parse (r"""Limit({|xyzd|}, x, 'str' or 2 or partialx)[\int_{1e-100 || partial}^{partialx or dy} \{} dx, oo zoo**b * 1e+100 <= 1. * {-1} = \{}, \sqrt[-1]{0.1**{partial or None}}] ^^ sqrt(partialx)[oo zoo] + \sqrt[-1.0]{1e+100!} if \[d^6 / dx**1 dz**2 dz**3 (oo zoo 'str') + d^4 / dz**1 dy**3 (\[-1.0]), \int \['str' 'str' dy] dx] else {|(\lim_{x \to 'str'} zoo {|partial|}d**6/dy**2 dy**3 dy**1 partial)[(True, zoo, True)**{oo zoo None}]|} if \[[[partial[1.] {0: partialx, partialx: dx, 'str': b} {-{1.0 * 0.1}} if (False:dx, 1e+100 * 1e+100 b) else {|True**partialx|}, \[0] \[partialy] / Limit(\{}, x, 2) not in a ^^ zoo ^^ 1e-100]], [[Sum({} / {}, (x, lambda x: False ^^ partialx ^^ 0.1, Sum(dx, (x, b, 'str'))[-{1 'str' False}, partialx && 'str' && a, oo:dy])), ln(x) \sqrt['str' / 0]{d**3}/dx**3 Truelambda x, y, z:a if a else b if partialy]], [[lambda: {1e-100, oo zoo, 1e-100} / \[b || 0.1 || None, \{}, \[[dy, c]]], {}]]] else lambda x:ln({}) if {\int_b^p artial * 1e+100 dx or \['str'] or 2 if partialx else 1e+100} else [] if {|{dz,} / [partial]|} and B/a * sePolynomialError(True * {-1}, d^4 / dy**2 dz**2 (partialx), 1e-100 && 1.) Sum(\[1, 1e+100], (x, {'str', 1.}, \sqrt[1]{partial})) and {d^5 / dz**2 dy**1 dx**2 (oo zoo && xyzd), {dz 'str' * 1. && lambda x, y, (z:zoo && lambda x), (y:0)}} else {}""")
	a = p.parse (r"""\begin{cases} \sum_{x = \lim_{x \to \left[ \right]} \left(\sqrt[1{e}{+100}]{False} + 1{e}{+100} + \infty \widetilde\infty \right)}^{\left\{\neg\ \partial x\left[1., \emptyset, \text{'str'} \right] \vee \lambda{:} \partial \vee 0.1 \vee dz \vee \frac{\left(d^2 \right)}{dx^1 dz^1} - \frac{1}{\sqrt[\infty]{\partial}} \right\}} \left(\frac{\frac{x}{y}\ zd}{dz\ c\ dz \cdot 1{e}{+100}}, -\left(\partial x + dz + 1.0 \right), {-2}{:}{-{1 \cdot 2 \cdot 1.0}}{:}\left\{\partial x, 1.0 \right\} \right) & \text{for}\: \left(\lim_{x \to -1.0} 0^o o \wedge \log_\partial\left(ypartialx \right) a! \wedge \sqrt[xyzd]{\infty}\ \widetilde\infty \cap \frac{\partial^3}{\partial x^1\partial z^2}\left(0.1 \right) \cap \frac{\partial^9}{\partial z^3\partial y^3\partial x^3}\left(a \right) \right) + \left(\lim_{x \to \begin{bmatrix} b & True & \text{'str'} \\ dx & 1.0 & 0.1 \end{bmatrix}} -1 \ne dx, \begin{cases} \infty \widetilde\infty \wedge \partial x \wedge None & \text{for}\: dz! \\ \lambda & \text{otherwise} \end{cases}{:}\partial y, \left\{\left\{dy{:} \partial y \right\}, \left(False{:}\partial x{:}\emptyset \right), \lim_{x \to \partial} \partial x \right\} \right) + \frac{\begin{bmatrix} \infty \end{bmatrix}}{\begin{bmatrix} \emptyset \\ \partial y \end{bmatrix}} \le \ln\left(\left\{None, \infty \widetilde\infty, dy \right\} \right) \\ \left(\operatorname{GeometryError}\left( \right) \wedge \ln\left(x \right) - 1.00 \right) \left\{dx{:} 0.1 \right\} \left\{1.0{:} \partial x \right\} \sum_{x = 1{e}{-100}}^p artial\ True \cdot \left\{\text{'str'}{:} \begin{bmatrix} xyzd \\ dy \end{bmatrix} \right\} \vee \left(\left\{\emptyset \right\} \cup \frac{True}{\partial y} \cup \left|\partial x \right| \right) \cap \left(\begin{bmatrix} True \\ \text{'str'} \end{bmatrix} \cup \widetilde\infty \cdot 1.\ True \cup -\partial x \right) \cap \operatorname{Sum}\left(\left(\left( \right) \mapsto 1{e}{+100} \right), \left(x, \infty \widetilde\infty\left[1{e}{-100} \right], c \vee \partial x \vee None \right) \right) \vee \left(\cot^{-1}\left(\emptyset \right), \int dx \ dx \right)! & \text{for}\: \left[\left|\left(-1 \right) \right|, \frac{\partial^4}{\partial x^2\partial z^2}\left(\log_{\emptyset}\left(-1.0 \right) \right) \right]\left[loglambda\ x, y, z{:}\begin{cases} \infty \widetilde\infty & \text{for}\: 1{e}{-100} \\ dy & \text{for}\: dy \end{cases}, \operatorname{Sum}\left(False, \left(x, False, 0 \right) \right) \cap \sqrt[False]{2} \cap \frac{1}{dx\ a!}, \gcd\left(\left(dy \vee \partial x \right)^{1.0^{\partial x}}, \operatorname{Sum}\left(b{:}None, \left(x, -1 + 1.0 + \text{'str'}, xyzd! \right) \right), \left|-1 \right| + 1.0 \cdot 1.0 \right) \right] \\ \left|\begin{cases} \left(dx\left[\partial, \emptyset \right] \wedge \left(False \vee \partial x \right) \right) \left(\neg\ -1^{dy} \right) \frac{d^2}{dx^2}\left(dx \right) & \text{for}\: 1{e}{+100} \\ dy & \text{for}\: 1{e}{-100} \end{cases} \right| & \text{otherwise} \end{cases}""")
	a = p.parse (r"""Eq(Union(dy2 - 2.0651337529406422e-09*notinxyzd, Union(Complement(diff(z20notin)*diff(s)*partialxb, diff(diff(diff(-1.0)))), Complement(diff(diff(diff(-1.0))), diff(z20notin)*diff(s)*partialxb))), Or(Union(Complement(Union(Complement(Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))), partial.chCa.dcGNDli().XG()), Complement(partial.chCa.dcGNDli().XG(), Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))))), diff(diff(dx))**1*e - 100), Complement(diff(diff(dx))**1*e - 100, Union(Complement(Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))), partial.chCa.dcGNDli().XG()), Complement(partial.chCa.dcGNDli().XG(), Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))))))), 0.1 - bcorx0orc)); slice(None); abs(Matrix([Integers])); Matrix([[[Eq(c, 2)]], [[{Lambda: oo}]], [[lambdax, slice(y, 2)]]])""")
	# a = p.parse (r"\int dx dx dx")
	print (a)


	for v, k in sorted (((v, k) for k, v in p.reds.items ()), reverse = True):
		print (f'{v} - {k}')

	print (f'total: {sum (p.reds.values ())}')


	# a = sym.ast2spt (a)
	# print (a)
