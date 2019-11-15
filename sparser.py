# Builds expression tree from text, nodes are nested AST tuples.

import ast as py_ast
from collections import OrderedDict
import os
import re
import sys

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
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

	raise SyntaxError ('cannot apply initial conditions to derivative of undefined function')

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
	func = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC

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

	raise SyntaxError ('cannot apply initial conditions to undefined function')

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

	raise SyntaxError ('invalid undefined function')

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
class Parser (lalr1.LALR1):
	def __init__ (self):
		self.TOKENS_LONG.update ([(v, self.TOKENS [v]) for v in self.TOKENS_QUICK])

		lalr1.LALR1.__init__ (self)

	def set_quick (self, state = True):
		self.TOKENS.update (self.TOKENS_QUICK if state else self.TOKENS_LONG)
		self.set_tokens (self.TOKENS)

	_PARSER_TABLES = \
			b'eJztffuP3DaW7j+zwLiBKkB8S/2b43hmg02cbJzM3YERBE7iWQSbF+IkOxfB/d/vefEhlagqVVd3V1UTVrso8c1z+H0ieUg9e/OX1y8+/fjTV3/Z/OXf3v30HfzE249f/vUL+Pns+ecvX30Mjg8+f/7iP9Dx5V+/fPXis39EF/y++hRD/v355xLtQ7p//fHz' \
			b'1//Ozg9e/u3rF89fv3wt7k+ex6cfZOffs/MzdlIKKd+/gkN+lPxqDP/Rq08/ib8qOtDnk49effk6JvPiy88//gcmkxyvv8Dyvv7ygxiEnS8/+eyLf7x+ifm/+hIT/ujVF3/Din30CQWn///zc/T/mNrpU/SVlviA2uDFp5988jy23eex7dDx+Ud/+/cvYiE+' \
			b'H5UN717+J/z3/JPP4P8PP/iY/PDpqw+lxdD1QXb+PTulxV5+/PolZvz5R5/g78v/eoE1ff4FVRWT/IILCAX7Iv5im3340d8/+hBjvBDZcbjPPuYGfPlFbMv/ev3yBQX48KO//hVV4NVHpC0vqNDPX32IDYYen2L8T55/9vqLT6WIUQHowf/hxsYfxVKALF/8' \
			b'Bzjf//7N+z/e/vr+j8L9Htzfvv313W9f//zr199988P7397+WniD892/fgGf7//4Mbp/evffX7/99b/j7fvff3n3a775Bpw/vv3t629//kFcv/78v9nF+b1/9/79t8n1S3LFZN5+k5zff/ev9PS331JG/3z77W/R/QtlwI9//+nbXOZ//vOX0c3X33/7Ppc0' \
			b'VeiH73Pd8tMff//h6+9/TAn89u7XH4vWiM5vf//1h/9btEx0fvP9Tz+PkgJHKuSvb1Mh3373XXT+8S49/df7d7l60HKp0FiNlDU2Wbz5/afvf/6pkEJuv59+S4X6NlcHhFu21R9vU8v+9HPK7vcyyNufvhs9Lxvzm29//vHHt+n255TYN1DV/3mXJTUO98v3' \
			b'7759l25AC3/Kdf7l/W8/p6yTZqSa/PxDri4lOrp5X8T8+oc/3v6Qxc4xv9q8ebb1auPCzYYdPTpch/+pje1v5BbuyKUx2MaGzdbfjB7wnYrxIIKOj9BJobaUix02z8zGDJut2Vh03KSn9Cw/2A7oMB3/5w34cqLxkbY7j/zoETrBpTz/5yFNxXWCO3SCK8Bf' \
			b'v7Fwzz4BHfCrITYVBANYvXEYQ92MH8XbraU4ymLdnFTNcjnwIT+ScpnNMw3NYvChy490eauNOPAZJgK+yiYXPdNu8wzvQD7B3MiTraZW1or/8yAKbW/kETpRKCQOjHlT3EZ38VzzDwgbq0l/toveFh1YSHnORYemkId877BFdGoSl57Ks50HNj/w4wdbwwpk' \
			b'+D/HHhazpDytltsoJqiJ5Xb0/J/HwrN+GUyctR1UDzVJPNwQPawXMUt9IYalEhhoXAUNS+LhlqdHQ3mrO3HgM4yOugGVcKxm6TZMH4mujB/73dtJxJnbmUeTdPrd21GkrXVFyXInkUJMHoTpg7JfASiwSJSN99DJSTFBbkZL4SB7w6qUHu8+yrdbS80MWvkM' \
			b'ew320WEToOBQOIQCyWvGG+HOm0NCgXKMQ20toSFWCMKl/gIVUlQaHRgGFOiHgyyGAg3QLz3PTyw9cV1+4viJyk88P0npbDUDpOb/vEplTI90+Qid6Or5P2i+m5vsRJflnhCjoJO6voMoWVXwjjpMugW5EjRxsAixmC41FAC7IYcy/F+AoioGT2wLRZkM1HHF' \
			b'wekpbEcbsYObAh/yI7nvJM0O5QUNJPo2eh6fwAOSoRNddExccA/dm8LQHwQU7EYHtrbn/zzIQHP6mp3YAOAZsNdygeA2UFoaaot5Cs9tdE+6BSAkmEYBFJPerC8AOhUP28FGxbQCi9IzRCtVFAI8fFZ0Yrrtc+HCxrHWBEwsukx0MXugo4+O6GVItxWkl5kQ' \
			b'7yihnSfpbstAqJzcRh9oMMVUZfk/j2FZUqhdmuUxbBgjOr6JSqtRRCRLDfCN6eYeNlBt0dXzf95lyOjJiS3h+L/iZSYynbP8H73HCBdacqLLRM8buYW76EGPQITPQmBp6ihNpB4qr6dXJhPjYxf17GGiB74pyRNwwUvam26jQB0UtAuwOIjeEhiDBqNmgWh6' \
			b'1CBAJlCDYQPNBM0zgFNvFCCLgrZW0BsVeCjwUYAkCpoMuMlgCPwjjoYSK2gOBSUAb4wBySvITkF+CjJUHaQAKq3gvU9BfYETgAUUvOQpaHUFb1wKElUAeApeSgBLQWsVJKwg5cFsBrsZ3GYAd9gMkLrDuJARtKZyBJdYWnB4RC6oPbzNgewGSK6DpDuA4kD9' \
			b'BPAE7yFwRwKEAkOekCWUBBLFNA3+QR7QLgoaRlksF5S6wz/ICPpdbza93fRu0/tNHzZ9v+lB27AOEMbgCwZQP+Atggp0fNBPeJuCd0hAFAAwwP1gkCWg6wfo8mET+k0YNj3KChtE4+sG0oeGtzkkkR6yxNwhc/DGd29w3uA7HJQHxPwM5YsPMPoNeFu+xcbH' \
			b'H82hUCboizW8IZIlX0W+b/Atmu4p7aYbF6obzwYWsmJpomRIuoMSlWFdQCnirbLy6ySa6uXBIOFF1SQihvCcMivXYFhrWKdUl0LRg4Y4V6JVhtXH6KgmLHaSMspb+ybu6xE3CDh2aEt4IIL5ioavrAHMJskDnwiWMO1Q2xe+ThCH2edxa1goX6lwE0Wbqpio' \
			b'1lSpWJnmlIiVp1SYUksm2lHVC6Ww2a2Xdu8ImKO+i56LXkeNTvpb6G2hq1E/RSFF8ZpIVokEQZC50Th5C+sEFF180fLSIQYJ4OT9jMra4PKK4FI1eV6PPJ8pHgS9eea6JtfrkSv0U9MEekUCfaZMZFQXp0RcnM4gEsZZYCjYBji/yfVy5GpsfFGSVyhsEJ7H' \
			b'IB8FraCgGRS0g4LEFKSmHDbc0MR8MWIGabomzSuSpm/SvCJphibNa5HmsyFO2zmZ15OpCpmyiy9N1D7t/fhqxE6VJrnze9QgqzpYWRZ4x+9TbUbwFDOCnua4j4lPk+U40etFYN7cPSnp3J2MkTQvya1NxshciO6Piq7jgmTHC4bpTd7K+nObCr0mxIlT3JFn' \
			b'Ot2We45Y7hHjDCVGGeRLv7KKpqSZe+bxnrt6z8Mp7OjYW1FTcXEC9bmtBN2ftHpZm+tZ53uWXS+rPoPMTKW1cyPvXmyt88yzv2bJahEo+ZUSpPojbvIr2jMncKrH67Nx7ckz4XsukuciBX6l7xD1UNxjHWlindI5d77AAgp9a7wVjRdYuwOrdWC1DsNSG0bg' \
			b'am05bUvu8oG7fN81RTwcnIPMIAu+elZLMZjsIyZjXW+ajez1vIiSEaxm61fd7FkvWI64lYDNlZscL1eOaF6uxTAZfpvAzl1gZDLeetwlCxClosWYH/tcE90FiY5eW6Sxm7Hvow/BsKS6zVNfTw/TfErBYJpYr0msNjR5XpM8wd3keTXypH2hPAyk3/Zm89hv' \
			b'Nrhzk8YIDJxpey+WkQXF82jFDkDLzIml5hCywFXfGPyVbDze0PY1imQokSbxR3mXtSSE1ugP2M0wQ+5f9OM6vjOd9CF+HW2ieABRGEE2ASheWmOUEitJRrBoqIRCQdk0mdyfTAYr/cALT3gxkiDrCJKCrNyR8THvpuXl+UEGcsxjQ3y/ICE3OZ2eO1q73ku7' \
			b'utau90G7ToBl4Fee1qgnUdaua615MhXtREU9jafuZPIdT22RI768vOlonhRbbbrdc3R+/wHeRcZtUj6uz1hei6Oh11dsGK3FglePLD0xcG/bG+d9C6SXaYzKTijeLXHXrFJfUrqP5r92ar7XRDPlFzpS54SNzyfxkIW2ZgttzRbaNOaWPHW6I9tszbbZDKDk' \
			b'94ytBPNUWM+hZMaLXzWe8bQYGmAzqstEZxN33c6axdHOkLumqf43dJRts/S6BEkROjWQ2jPmCa2N9rZRf4etTbjfhigzdI0y9+0I6Ru2XgK24jYo1mnddHqfTpvWRPuaqBnPX0i3lzm94JpO75uH6ZpOX4RO4yZJwzvq8AdH5jf08Sr8AfmZ+AEBI3sOzE00' \
			b'ZTf5rHiyEzI8a0IxBk61Hex3RapiRTc60YUQNcDwPA/dQfMbMQUzxTHZbJ9kisM8yXiGE6IfJ8maTnROSwpytgxaeHDKNK9E0xDtANBLUiA0waFJ1LZv6bLEhi1gaqsqiPEmWvlose6hOfcG8Jcn6L71zUsSGdrJGbaTM2wnZ8ROzsweDGgrz93cc7KzkedG' \
			b'nuOv51c/zcTP2PDmGVnwNXuCuw2bXJSAbgesrTe6sTxK4RdNMsIwzd7insf5duHNQGnZfmKs/Doxj2Ho6FlePQ8qabHe8MoCyY+t59vS8ZVQlRdy8n0cMJLNVIijStmy1LHOBOaawIEDa0ZgXgvMR4FZq48DRhChbXNOF6AJKAjLk0VWJovsjWwX4HkGy/MM' \
			b'9AO1tjIxYGngT28dccwhswZ5/wArjOuTIZ6t24P1nFPf8w9l1BDlUvSIzbtso4jrEajnnsiTiW2BZcG+HJTRyf5cx1DqBErdjczJMJQ6hlInUOpu5ItZDuflUbV86z9X0396lnfPytGTuCGCvFzjM89e0Hg+frTSN024Nk14puSoaGw4T5OyLhlL+7bJ51Sj' \
			b'354at8c+hI3OFnFxS4Cmli73gGC3CwLEQaQT+D2WTQrwZG881hsPqcYTqlt3u4zuBpkGxt3A+hCiCoTW2U531kIvSCZjvyC7ycU+1Q8yBuSz3al79q35T4V1Q2vM030JRCddtlGXtegw8kDD/QvB/X4zMOAPIj02j+o2bzp88aZP1aKVCn6udig0lhuKRTTg' \
			b'EfU6KmxqHRYuCohfwRW9lFNTSTtZaSo3YCmxwam1pzXVVMdYwVqbDYqbFb/oFL9AQOUVZU4iMKxIpCJWxM9L/WzbpbOtFwIxfjICP3WAX9rAXQLYgPiBG/y6DX7aBr+zgt9YwaOl0FwMvx6K35zELxWCimnclY56A2XTuKka54ehbBrP3MHzVFHx8fwKPGsB' \
			b'j/PEM8jwiFxsVugqmtoWwoH4NLYwNjG2MR7SA02scW0CtyvgUeR4nDXUU0M9NR4xj8dl4UlZeDgW1FnjcVpo3YA6AfXTiAG4JRB7L/Zc3OOAxqE9ihHlCPc4FMeFUyi/6SwoxxZSAs+tghJtoXRbSH0LOW0turvNdoDHHfqDE/4QALaIAFvs+lso89bQY4iC' \
			b'HX2r8A9EtEW5bFFoW5TkFvv31uAjUJYtCnCLnXuLPXtrMFFoi+2AsR3GdpgFPIFabT16d5gVhAV93KJebDEdCmooS3xsKWkqD7h6TJDygawxPSxCwCKACLbQbFusNKgANsIWmnaLKXFCVAGqE5bDaW4BBKwtAgVXETRrqzFzQIFtjwGpgtiMHksK3j0WEsJj' \
			b'Ch49QVu2IJ0taOI2ULWxscGX2gw8BqwDOhTlqPAx/GHrKCoj5mPJH5Il0cATQ02MFYYgoLXbAd3UOhgcPfEPPakKEA/6xhYAcIuxoL9sUXqYbk/Vo/8gDjUVhAqYVkc1wDuID31oC915G7BVsUYQGtBqC/1v2xspMakDyhELSa2KOcPDAcuF8uzxIQkVFQl1' \
			b'sR++QvxC1GqY1TBrFrMaYDXAOjPA0ghYNaDyBVZ1i3BFb7n8JpxnPAvoym+mu+hl7gpg+FYd36fpPfnEeIYTgTuYdm5Y5o7EMzODaX2Ba5qxDTetL+JbQGGEPUgWxlgW1qBZ4OCdOOqodhCuhVMiW+AyQRIh/bs/dAsz+Ha+sBaOBLYwB21YPoG3QAAX9kHc' \
			b'5k9/iywbbpFnh+4W2Of/4S6d1bhHw1dBv3AYAHYRA02xLDTBQxpZyyibgZHsP3nYvASPaoqQPO7mAfYSWuqZaQiCzfJV0O/Cp8yR0CwK7lnHWQ6ZJcifU5UZh3K2Ic2feJlG4pkRmjFJU0j7IJgX13Zm9wmSIRx+R5GgGcLhl+3wi54I0/hhRZyMmIXrbgVk' \
			b'g9zRvCpCNx7XjEewr4ZwM4HxwFCOp+DeBc7xFK0E6XolrKsM7Xj0D8G7IYjX2BZou0xQrwu4R0RAAbs9iI+/JeTjzBZhXy9zV3bDgCgzazX0x3iO8T86IwNQFkIC7CchIiEwejEj0OwdYj1qFP0KO9ANTd4NmSUUvwBzwSo0QZ5CFbQtD6uHOo05FX+zzJEL' \
			b'i3N0qfDdMKqJtJDwCbffDqcc8ke8w3UQ7uHq9tFXS3WkcZT4SJSCmKgQE2Iqih3zxKr6IfogXSUvR8wVnbMERoI7nMOiYgiTRS1Yy2epsYTTuEVIwcKE3DCdVexGCsUEV4q2RnKUfp/CRarDx4hgFFeX4jVcpkR+THta3dKLlna3JHgPv/ii5G/p3SZAKOge' \
			b'TI6Iv7f42gH4eksvGgBYt8jxACjg4ZE97RJ7ugcn0MPHFPdHmnaXOONCwRryHI1PpqQZCbOR5YWRpWey9HvIEhvVT/iSH6Ha+HRj5bdClTFUl5yJKn1BlcWVqdIXVLk0fkJPzqtOjH48hKIoZpzvLCcmX+REX72IEQcvpOgLTqSHkRaXEpiOwvih5qI74T8/' \
			b'pT6/y3w7CfP4LNZSFX7BpurNcp5fx3mSYeQ8EedqzuN4kfF8lfD8WsLzmfBy81T5zjPfSS0i3XmmOy9sF5Va5HQY181y3Ay1uWOo7VpJzT0SmalGaGdNaEhhWKB9Kxf41YnJ+gUFlkk/dnv+nSczbL6OySw6I5npYvJPd/lKZEahhczQXSUz9OS8qmSGfkJm' \
			b'FNoJlxVZz5JZ9jXDqJSTa266kNBbaGwx6pTG+KHmQguNceVmphZR20oum8nAD6mKqniMhzlJ3eaYjKV6MJPFygiTRVmuZTKJJ0xGLTDLZFSvNUym89xk0fQ1JtO8ABNrIUymeZqSO0xqVDpiudtlsvnRWqSwheGZP3JR56oJrI3EGnG90bzmjj+LxIUBRqxV' \
			b'LLyz2/NvhbVijC45E2uZgrVMvjJrmYK1zBJrGWYts8BaZn4Va5TxLG0lXxSjqV6Lq1yL8XY4ywhnmYKzTIWzRny1kzKPvWLtVOGHjCXVmmUss46xJMPIWCLH1YzF8SJjmSpjmbWMZTJj5dJWGcswY0ktImMZZiwjjBW1WQS1yFjCVDMEFRpBNYJqBDVHUJYJ' \
			b'yu4jKDshKFsQlBWCsnWCshKqS85EULYgKJuvTFC2ICi7RFCWCcouEJStEFSZ8SxBJV8SY/VaJqileDsEZYWgbEFQ9hCC2klZCEpqpwq/kKs1S1B2HUFJhpGgRI6rCYrjRYKyVYKyawnKZoLKzVMlKMsEJbWIBGWZoKwQVNRmEdSRBNU/PkEdayh3n9RUtaB7' \
			b'anQzscR7EJpZsMhL9GLnKCUwpewzztMT6zw9a55HTyukEiROl5yJVEJBKiFfmVQOstrTx5rtsbblv3lOSaVCmYXqdbxpn5bc93IGhuLMUonzmhJ58aJSn29tcs5TR1hHHVEkQh0irbvbBu6yxloLQUpaWCM10bwNtGYrQV2YCaJ7ZClID8Y0EXkh88Gwmg+e' \
			b'kK3gQ9sJumLX5LUTzbWMa5BULKn/MglhgJKE6FdICPuOZhZi71kWSqG65IwsRIkLC7GfhIgsRKGFhcQL98rrTEeUBKcUSQndnG+Vk8ggeYaWRoWYo6TsC4mWoSfXIiUtxgNt5ZIzYVHFevHiID1XUeksAZOaZ4nEdvNiBov1VYVfsKmic+xl1lmzxwyFvaKU' \
			b'17KXxBP+oraYpTCzdvcOqQxTWNE8tYEPJZ8aPxIZFUdUVqdGVfJ77MBHdY8/8mlTc43CzpHCeO3I7Fs7MpO1I1OsHRlZOzL1tSMTY3TJmfirWDtiPwmR+KtYOzJLa0eG147MwtqRqawdjTKe5azki5xlqtcyZy3Fm46wjKwdmWLtyByydrSbsjCU1E4VfshQ' \
			b'Uq1Zhlq3dhQzjAwlclzNUBwvMlR17cisXTsyee2oKG2VoXjtKNYiMhSvHRlZO0raLII6lqFUY6jGUI2h5hiKZ/rMvpk+M5npM8VMX5znM/V5PuwrMs8XnYmhink+9pMQiaGKeT5C8CpD8VSfWZjpQ79ZhioznmWo5IsMFarXMkMtxdthqCAMFQqGCocw1E7K' \
			b'wlBSO1X4IUNJtWYZat0MYMwwMpTIcTVDcbzIUKHKUGunAU2eBiyap8pQPBMYaxEZiicDjcwHJm0WQR3LUMceqtAYqjHUdTOUZcPxvUfe2InVuC2sxq1Yjdu61bjtJFSXnJGhbGE1nrxtYTVuC6txu2Q1btlq3C5YjdtunqFGGc8xVPaVDl+5FhlqMd6UoazY' \
			b'jNvCZtzWbMZLhtpNmRkq1k4VftDXYrXmGMqusxiPGQpDRTmuZSiJJwxlqxbjdq3FuM0W40Xz1BjKssV4rIUwlGWLcSsW40mbRVDHMtT64y8aQzWGehIMxbN8dt8sn53M8tlils/KLJ+tz/LZGKNLzsRQxSwf+0mIxFDFLJ9dmuWzPMtnF2b5bGWWb5TxLEMl' \
			b'X+zw4wiogdl/kaJM9ZqhKJnms8U0nz1kmm83ZaEoqZ4q/JCipF6zFLVumi9mGClKBLmaojhepKjqNJ9dO81n8zRf0TxViuJpvliLSFE8zWdlmi+pswjqWIpaPGOiUVSjqKdLUWwjbvfZiNuJjbgtbMSt2Ijbuo04dguxEY/ORFGFjTj7SYhEUYWNuF2yEbds' \
			b'I24XbMRtxUZ8lPEsRSVf7PC2ei0z1FK8HYYSG3Fb2IjbQ2zEd1MWhpLaqcIv5GrNMtQ6G/GYYWQokeNqhuJ4kaGqNuJ2rY24zTbiRfNUGYptxGMtIkOxjbgVG/GkzSKoYxlq8aiIxlCNoZ4uQzlmKLePodyEoVzBUE4YytUZykmoLjkTQ7mCoVy+MkO5gqHc' \
			b'EkM5Zii3wFCuwlBlxrMMlXyxw7vqtcxQS/F2GMoJQ7mCodwhDLWTsjCU1E4VfsGmas0ylFvHUJJhZCiR42qG4niRoVyVodxahnKZoXLzVBnKMUNJLSJDOWYoJwwVtVkEdSxDtYMgGkM1hpplKM8M5fcxlJ8wlC8YygtD+TpDia/tkjMxlC8YqrgyQ/mCoZZ2' \
			b'RaEn51VnKF9hqDLjWYZKvtjhffVaZqileDsM5YWhfMFQ/hCG2klZGEpqpwo/ZCip1ixD+XUMJRlGhhI5rmYojhcZylcZyq9lKJ8ZKjdPlaE8M5TUIjKUZ4bywlBRm0VQxzJUOwmiMVRjqFmGGpihhn0MNUwYaigYahCGGuoMNUioLjkTQw0FQw35ygw1FAw1' \
			b'LDHUwAw1LDDUUGGoMuNZhkq+ZhiFnlzLDLUUb4ehBmGooWCo4RCG2klZGEpqpwo/ZCip1ixDDesYSjKMDCVyXM1QHC8yVHVPLynDKoYaMkPl5qky1MAMJbWIDDUwQw3CUFGbRVDHMtQZHAVx5QzVvgVy2Uzl2GTC7TOZcBOTCVeYTDgxmXB1kwkXY3TJGZnK' \
			b'FSYT7CchIlO5wmTCLZlMODaZcAsmE65iMjHKeI6psi8kOokwirzEVIvxpkzlxGLCscUE3fJjd4jdxG76zFexjqrwgx4XKzfHV26d3UTMUPgqSnMtX0k84StXtZtwa+0mXLabKJqnxleO7SZiLYSvHNtNOLGbSEIRcR3LV+uPqmh81fjqSfEVr065fatTbrI6' \
			b'5YrVKSerU66+OoWntMjqVHQmvipWp9hPQiS+Klan3NLqlOPVKbewOuUqq1OjjGf5KvkiX7nqtcxXS/F2+EpWpxyvTjkZXKXm28dXO+kLX0kdVeEXbKrcLF+tW6OKGUa+Emmu5iuOF/mqukbl1q5RubxGVTRPla94jSrWIvIVr1E5WaNKQhFxHclXuh040fiq' \
			b'8dUiX/Faldu3VuUma1WuWKtyslbl6mtVTnxtl5yJr4q1Kldcma+KtSq3tFbleK3KLaxVucpa1SjjWb5KvshXvnot89VSvB2+krUqx2tVdMuP3SErVrvpC19JHVXhF2yq3CxfrVuxihlGvhJpruYrjhf5qrpi5dauWLm8YlU0T5WveMUq1iLyFa9YOVmxSkIR' \
			b'cR3LV+dx/MTkHMDLZK3RCYCNua6QuXpmrn4fc/UT5uoL5uqFufo6c8VQXXIm5uoL5urzlZmrL5iLvaA56GeWv3rmr36Bv/oKf5XZz/JX8kX+6qvXMn8txQMl5ZIXFNYLhfVMYb1QWGzHfRS2k4VQmFRTFX7BpvrNUli/jsIkw0hhItbVFMbxIoX1VQrr11JY' \
			b'nyksN0+VwnqmMKlFpLCeKawXCotCEXEdS2HncT5Fo7BGYedPYZ5PrPD7TqzwkxMrfHFihZcTK3z9xArfSaguOSOF+eLECt/lK1GYL06sEC/sPl2FwjyfW+EXzq3wlXMrRtnPUVj2NcMo9ORapLDFeKCkXPJMYV6OrvB8dAXd8mN/yAEWu1kwhcVqqsIv2FS/' \
			b'OQrz6w6wiBkKhUWxrqUwiScU5qsHWPi1B1j4fIBF0Tw1CvN8gEWshVCY5wMsvBxgkYQi4jqWws7jAItGYY3CLoDCFFOY2kdhakJhqqAwJRSm6hSmJFSXnInCVEFhKl+ZwlRBYeyF3UfVKEwxhakFClMVCiuzn6Ww5GuGUejJtUxhS/GQwtSEwpRQmGIKU0Jh' \
			b'sY77KGwnC6EwqeaozjbVb5bC1DoKkwwjhYlYV1MYx4sUpqoUptZSmMoUlpunSmGKKUxqESlMMYUpobAoFBHXsRTWDrhopu9Pg7DgHj/WA210xBSi5ilEvW8KUU+mEHUmr236ehU9rUwiaonTJWeaRNTFJKLOF9IXTcbozF6EyNXVL73Z+/0qDDP/Cath9Dc/' \
			b'hZiKhlOIunotTyEuxdv5LGL8cC/2tPidECrfAR+5inmlOuWPXJEXf+SquLXJOT+FqFeRl8ulxhlEkela7qIWKL5zlRtiZw5Rr51D1MReomPSUAuTiJonESmopj4CYYrpRM3TiZqJLKk5/06IzPa39GoWvzdvh1t8NQGUuiW6B2i5RZYGWLilb3EV1LZ4MoZ7' \
			b'vAHaOX0uCzraUUM1qP1xn81qDHhBQzY2qff7TOohAT+xqveFVb0Xq3pft6r3MUaXnGnUVljVs5+ESKO2wqpevLA3mcx+lASnlMZubGHvFyzsfcXCflSI2bFb8sWxm6lec/RHlYrDt6WoOHwzHFx4MA7ihAk9W9t7sbZPzbpvELeTkQzipL6q8As2VXR2ELfO' \
			b'2j5mGAdxIuXVgziOFwdxVWt7v9ba3mdr+6J5qoM4traPtYiDOLa292Jtn4Qi4jp2EHceJ2zcheYMMZ07r2Hd0d+GbCR3J5JzbiXRqQnZdcd+uoRtHM0+G0czsXE0hY2jERtHU7dxNOJru+RMny4pbBxNceVPlxQ2juLlHf8I21ESnFL6jAnbO5oFe0fD9o6U' \
			b'NOoTW6ll1hsVZvZzJskXP2fiq9fioG8xHn4k0me+owpKe3eaK8BVVfzYHGL9uJsL812sqSr8gk1VnOM7s876MWYofBflvJbvJF78tEnV+tGstX7EXht0/rxJbqIa52HnM2wFiZF7Lk76zAlbQhqxhEwCEtEdy33ncXbHGQ/xGutdBus97NAu8NAu7FuNC5Nx' \
			b'XchM52U6k34r47ogobrkTOO6UIzrQr7yuC5kphMv7EKhGNcFHteFYlwXeFy3MLWJfrPjurIQs+O65IvjulC9ltfkluLhoC5khqOKSTt3mgvOVVT8mAPvG9Ht5CIjOqmpKvyCTVWcHdGFVQwXM4wjOpHv6hEdx4sjulAd0YW1I7qQR3S5eaojusAjOqlFHNEF' \
			b'HtEFZrUkFBHXsax2Hud9NFY7T1bTl8Vszj4wuyEg4DjO7RvHuck4zmV2Y7fn38o4zkmoLjnTOM4V4ziXrzyOc5ndxMvLTxzHOR7HuWIc53gc5+rshn6zn6MsCzE7fku+OH5z1Wt5/LYUr7NSchm/OR6/OWY3KriE5McceN/4bScXGb9JTVXhF2yq4uz4zR3C' \
			b'bpq3HssYTjKNYziR8eoxHMeLYzhXHcO5tWM4R7MjaQyXm6n6iUrH4zepSRy7OR67OWa5JBwR27Esdx6nhDSWO0+WuyCGe9ixG+9n8/v2s/nJfjZf7Gfzsp/N1/ez+RiqS840div2s7GfhEhjt2I/m3hhFyr2s1ESnFIau/GuNr+wq81XdrWNCjE7dku+OHbr' \
			b'q9fy2G0pHo7dytW4nsdusrHN88Y2LxvbUoPuG7vt5CJjN6mpKvyCTVWcHbut29gWM4xjN5Hv6rEbx4tjt+rGNr92Y5vPG9uK5qmO3XhjW6xFHLvxxjYvG9uSUERcR7KaOY+zRBqrNVa7KFYbmNWGfaw2TFhtKFhtEFYb6qw2SKguOROrDQWrDfnKrDYUrMZe' \
			b'2IWGgtUGZrWhYLWBWW1YYLWhwmplIWZZLfmaYRR6ci2z2lI8ZLWhYLWBWW0QVhuY1QZhtdig+1htJxdhNampKvyCTVWcZbVhHatJhpHVRL6rWY3jRVYbqqw2rGW1IbNabp4qqw3MalKLyGoDs9ogrBaFIuI6ltXO8sSRxmqN1c6a1QJv3A77Nm6HycbtUGzc' \
			b'DrJxO9Q3bodOQnXJGVktFBu3Q5evxGqh2LgtXtAcodi4TUmwT2S1wNu3w8L27VDZvj0qxByrZV8zjEJPrkVWW4wHqhqK7dtUMWnnTnPBuYqKH4dDdnDv5sKsFmuqCr9gUxXnWC2s28EdMxRWi/Jdy2oST1gtVHdwh7U7uEPewV00T43VAu/gjrUQVgu8gzvI' \
			b'Du4kFBHXsax2HoeQ3GH721luedvHUsJQiZkiKwkbXQITXRYL8d7rsG/vdZjsvQ7F3usge69Dfe91UBKqS87EQsXe66DylVmo2Hsd1MLutcC7rsPCrutQ2XU9zzapKMg2qnots81SvOlmtSDbrANvsz6AWWJCQii8mTrwNupQ20Md1u2hjplEEhHxrCYRjhdJ' \
			b'JO6hHvHH2u3TxQqWJK+XzBAD75+ONYgEwvung+yfTgoqclhBIEQc53H0RyOORhz3Shy8Ayzs2wEWJtu/QrH9K8j2r1Df/hVijC45E3EU27/YT0Ik4ii2fwWzRBy85SssbPkKlS1f88SRioLEYarXMnEsxdshDtnaFcyhxBETEuLgDVyBt26F2r6tsG7fVswk' \
			b'EoeIZzVxcLxIHGaOONZu2Qp5y5Ykv0wcvGcr1iASB+/ZCrJnKymoyGEtcVz8gRuNOBpx7CcOtsAL+yzwwsQCLxQWeEEs8ELdAg93DIoFXnQm4igs8NhPQiTiKCzwglsiDra6CwtWd6FidTdPHKkoSByuei0Tx1K8HeIQG7vgDiWOmJAQB1vSBbahCzUDunCQ' \
			b'AV0mDskkEoeIZzVxcLxIHG6OONbazZHIhTg4+WXiYKO5WINIHGw0F8RoLimoyGEtcSweZ3EJxHEOiy7tpKZrXGRh04Gwz3QgTEwHQmE6EMR0INRNB8AriOlAdCayKUwH2E9CJLIpTAfCsEQ2bC4QFswFQsVcYJTxLPEkXzOMQk+uZeJZirdDPGIoEIZN+khx' \
			b'OMREYDdlYSKpnSr8EGOkWrOstM5EIGYYWUnkuJqVOF5kpaqJQFhrIhCyiUDRPFVmYhOBWIvITGwiEMREIGmzCOrYxZTzOIaiMVRjqHNjqJ7NAPp9ZgD9xAygL8wAejED6OtmAH0nobrkjAzVF2YAfZevxFB9YQbQdwsM1fPSf7+w9N9Xlv5HGc8xVPY1wyj0' \
			b'5FpkqMV4U4bqZdG/7zJD9Ycs9++mzAwVa6cKP+hrsVpzDNWvW+6PGQpDRTmuZSiJJwzVV5f7+7XL/X1e7i+ap8ZQPS/3x1oIQ/W83N/Lcn/SZhHUsQx1HodFNIZqDHV2DMUmAv0+E4F+YiLQFyYCvZgI9HUTgV5JqC45E0MVJgK9yldmqMJEoF8yEejZRKBf' \
			b'MBHoKyYCo4xnGSr5IkOp6rXMUEvxdhhKzAV6VTCUOoShdlIWhpLajapqU7VmGWqdLUHMMDKUyHE1Q3G8yFCqylBrDQr6bFBQNE+VodieINYiMhTbE/RiT5C0WQR1LEOdx8EPjaEaQ50dQ2lmKL2PofSEoXTBUFoYStcZSkuoLjkTQ+mCoXS+MkPpgqH0EkNp' \
			b'Zii9wFC6wlBlxrMMlXyRoXT1WmaopXg7DKWFoXTBUPoQhtpJWRhKaqcKP2QoqdYsQ+l1DCUxIkOJHFczFMeLDKWrDKXXMpTODJWbp8pQmhlKahEZSjNDaWGoqM0iqGMZig5tAII4i6PVz4yoZo9TB39sjYsgLb2auNQwXCZ5OfPABIaAgEBr2agOe92ec9UH' \
			b'7BnjE4psJrNt+qAIPa2cUYSZeuaz5E6nFNnilCKbr3xKkc2Ehu4qoaHnvm+KYJjZo4nKnGePJsJyY1H5+IYy/OSa4zTCbaE1DsXqqmtJTOmNH3IxIr0xuO87m2gnZaa3WFVV1ju5bI3iWMo1isNTtnZoLmYczycS6a6lOZJuXs2ihpjlOdKRNTyH0ii2B0kB' \
			b'F40tKI8+1UXIjsokCqtTE9MJRXZEdpijuyV/+p+eeHrSD/g/UB+G0eSNxGcs8h70nzdLrJf4riS7CdO5yG5MbURnwmW7RDbLYoumeExY1dHTDsn4w4znEoFYMZarkcShIxshhdVkUBLB1CBuBfgn0F8Ce5cBnsDdCqCn0ciwAshHED6D3zXwJtTOcJ2wOuFz' \
			b'Auc6Mu+F5cMN1yIAL44cdvGTwPMwu7MEkVvZ3VJHwzVv+wkA10NfiXu7hmXrwC6i3DK+bcsjahDTCNAIyiKOIRypZTjyZ4FI6S0am7UB07630mEBnA4FpnWvmPQ+eCXoVLwiqmHPvouGUlWUQpVbQKp1KKUPfGnqVqNUngY4MVDpBaCyx4MVDssvBrDC4aCF' \
			b'R6IeAlrBnxa4RqDFI9zTARdFfjzwcsvgpQlT7gJg9jJBDBVsDZCFA4FMk5z2gpm5+wjQPNwr13iysraidgdEOxTNevRDtYaw0JEfF91WThSeZKx4F2RbgWpxmu88X8moeOXfEsKp4eFe0ei1mw721jQpfB5ohy10osElUu+K17bNn6Ddt1ApmvWyJ5n18msw' \
			b'r7aCc+gLXA3q5tZZ3NMdbSZom1v3KNc8wD/YvPYBddegdwx5oYA9RV975jUQCAt111B3hkJVroXAn3s4WCRIHC17HAeLmMQ9QePiy143ZxSmqZe3EesY+lBE9Rc9VHxauHMMg6QTnol7K6t3CRfjMh6vJpAM6HDoeOrYFtdatyp/5Adv+DXRPfBCwT3hZcPK' \
			b'YpCrH35m7jFn5R4J6+ZwzjWcywPa4cAB7QGDWb95c05LmQvWOA+1rHlO+GQeaVmzwKZBnyU0HQVLfPiLYYOn2uazx1jePE9o0lS1R1ve3Pw53AIz0vgznBdMrYMmKBbqN9rJXCdMrX2NQrO70yxynv0r1AObXZC5JVXHPRGQOuL9idunP91LVH/R6AS/Gn/d' \
			b'maGUPwOkgl93N8QaT4CNJ74aek3RC3so2YlDwdSZopg/FyDbYpLYUnfEM5yTLaa0phNZw0nRzTw8wNkHBLc1W/vKXRGPBXDq8l/HUDjnjWqYDWLXA2Ma1f6Y1zNU+8ee4+pPAGzTFzWo7SmhzD48lBUwBoU7j/e0c4CxBmH3bM0/gi+U89m9lp0Ret0DcqmT' \
			b'Ipd7XOQaGnI15Hok5NINuR4WufRJkcs/KnJBsRpyNeR6HOQyDbkeFrnMJU/rnxNMPbpt64VB01mj0n1BkKZ2u8wlxZNAzuZP6GC3iMRo8gDFbuhznehzpCXWVSAQvdScKQJdtFXDCc2uQrgFoiAQcg2EGghdEwjxAOFR34KoCA2CliEIX4SQLkJ3i5hNYHRm' \
			b'tuoNjBoY3RWMhscHo6GB0TFg9OgW6WtOsj0Gm0Jx5uwFYtTO2bCnxikjWPUE8IrgJmGWzvtp6DDi/HdyDOOMqYn6g8BMnzOY7ZyTeh+IpjEEHvqMbXEUsj26NXtDtoZsD4ZspkA2UyDb+O8ekM2sQzbTkA2zImQzRyLbaS3ZG7JdHLI9GVSzBarZAtXs6O8e' \
			b'UM2uQzX75FGNEc0eh2j+tAbtbUqsTYmdHLKow16NlcIZwNJZzIl5jSBEi4T+tLbpDYQaCB0LQtQtnoCt1AlRiD8+Jk13aSjk1O2WOojFdyPsMLdb6jj4rsTgdFrz8wZODZyOB6fTmVE9GXDy6e8awalZmD8VcNK0MINTmOcKVPL0tOae94ZTXNpHwCnK+M4j' \
			b'OSn+nWCK0tgLU5pqCl77Acv2t8RWUO9b5AHoXbcEy9BFbhFYQdXh1xB0NfP0pwJd5wpX5qLgyjwWXJmTwJU5AVyd5K1qFUg18/UGUo8AUviB96e5iW8VSFEzXeXsuMXZcdT9zqCDB3vNfL2B0cOBESnw095RvA+MpI9f+1KdGW6JmaBP4QQU7S72j26+3sDo' \
			b'WsGIQ7XzDVagkTTsk7AcMDA8M9Sx4JffjB7d4ryB0dWAEXewMzjp4FKx6ClZMeGUEXRkAqFHNw5vIHRxIEQQcWbG35cFQtyCTxmDFA7PEGh6nMhWGsEoNLvuBkYHgBHq2jlvRLksLGovRH+SrRJ/cy80s+6GQYdgkGsY1DDonjCoWW83DNrBIFSgs9ne1kDo' \
			b'OkEIN9nyWOyijbRxiB2/8HkWeIQWW/7xcSl+2bMdEX5ycEI5bzH8+cEUXP5swAqTXIKsVR8rgPZ5A0+00aiTqDraa/JwmzfQgL2C52QF4Dp67MvHeGSEosdh80ZDYXUI4KHxS3w9hAf3sy2MBzsMjeG28GLWbfoeAwEA8DODz7DzQv+A7gE9xW9AZtBWIH0o' \
			b'KjQ1tDRo7oAgg50VOxyeNhQzRBCDJNBgFuFVoY0GLungTiC4B1VD6EEIghQQ9gascqB7DU2goa3hj0pj71wauzngH+XlMK+wlBsUcKA3l/3ZOgR0t/NP9Vqgd9fPUSl8tRQdfXfV0oe//Fyh7E658FOmGa2R4jopq56UF9hq9I+/dx9GfyP/fhw6UAxEY3Tj' \
			b'N2U8HUJF/lSx8AgVA8WnL+NCBSG9E/zjj0CzpPojK6RrdQLkUQHPBsG+0NXraPuFekIee/8h8Y+fEOUSzTqi1pEfkFJxT3UfyrojlYc9LQB8AMWFlPD4pPK8pN1mceOW6RQtB9PsOr6oad6+g9BJJ6kY3pRJFhiWj8xTkE9qUTyaBQhIQUtx64IfACe1chjq' \
			b'LQ358ItK2G11fNFILa+o9TWUXuPL0hAlgW9v6Yp/y9ck8PSvGmEnm7V/u7F3nfO510pRrRAxF3LiOfYeett+xIvbRo16F74Yb1AT13azcERP6/z63kbDjbPocXqTr3IwpVdefm0EzQOmA8Jp2lpw3xfrkW4ovV9nzOaJXawb5jzx124e9eK2sXfqN/6xuk73' \
			b'GN0nbI6/cI7qLvEfNRtWFdcgdr+O9JsndrFuHDuUrynA6VAWJ17ucNFc8R0vbqLQus/e7oMDgKd1sW6M5lf2KsZBPQh14GS9iFYy5MIZ+PL+uAsXX46KyQ02npQ5eMDozMa5jes3wJP33LcM+Fld9LFORpAQBg/Xcv5c+pzbpAvHxOX9wsUrc/nvwGirrnHa' \
			b'4qIfWjow95Lp+OLFg65h93498psndrFuqHPH7n5zHhc3150mak7ffQ5t5qXusb9r4EO5cJW4vF+4cKH9wKB3vw7PjOVoGiTulTsa1Tyti3XD3g8k0nT1qWARrZ1OfaEV0VExudnaBMsBXarfPLGLdcPfX5dCHThdtxo293Ghbd5RMbn12tzL/p6F9p5P62Ld' \
			b'uKe5l1IHTta70CD3fi40eD0qJjdiM5I5oIOFzRO72MqyW9vBjh7orRrQLQ3kksj6zaoLrXhXRSC7cr03lFc1P25idcbdr5j3PItuiHsZzubCTwg63hJw/7mxrugH646lWpy8a+J+lHu+yg0ed0iHm/2Y+RJerniIhYqz7ax2s/biCqnV8Q65cGvPfaS7eLH+' \
			b'rJtTYXw/7YzpqXpwVdZhc/iFm3RWRdi94n6tI2NDvV0oN1fBLYvqmHmcM1mZPI9OP2yOu7ha5sjYey/c1HdPSdcvVql10z+X2PtxN+mlXiyjYyaZWrcvNMBu2kUX69O6ian76PPHrJEe1ffd5uEvVNbTBKKLZXbMPFjDgEIT/KZddPGe4DsZHl2otQSeH3El' \
			b'FwvxTrNzlypEu7mWi4XYNpgdIHS/OfriPT357y5p7SS6m8XYc0WGC0FZUZph1AGKEjZP7GLduNtuuyeiG/3miV2sG836a79u4FliT+ti3fBNN/brht08sYt1o9m2HaAbbvPELtaNvunGft3wmyd2sW40k70DdCNsntjFxwN2mzeWzk6UzetOxQearYhAQm8s' \
			b'tTg9VHhAKXvA8LfUG5ALhcCTgFDyIC08AlWsYpydDw3yHf9xaLcTGmVNMfBEovGfdvxi7cqTIy1qjJQ00PPJGSYcAtLtqWakjYG1kbTPkcahRikyAuAXNAdAO0olaXCpuVFrB9Q+TJ0Oq80H1fLhsH5yIGw8DBaeB2mHAUuGem1obzZqNIvFd6PjMDEnEalX' \
			b'eE/he56WhI4A7oG2p8l5jCY/gTb66ub/Aypyl70='

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
		('FUNC',         fr'(@|\%|\\\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LTRU})|(\${_LTRU}\w*)|\\operatorname\s*{{\s*(\$?(?:{_LTR}|\\_)(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

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
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})|(\${_LTRU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\\_|{_LTR}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

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

	def expr_diffp_ics_1    (self, expr_diffp, expr_pcommas):                          return _expr_diffp_ics (expr_diffp, expr_pcommas)
	def expr_diffp_ics_2    (self, expr_diffp):                                        return expr_diffp

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

	def expr_ufunc_ics_1    (self, expr_ufunc, expr_pcommas):                          return _expr_ufunc_ics (expr_ufunc, expr_pcommas)
	def expr_ufunc_ics_2    (self, expr_ufunc):                                        return expr_ufunc

	def expr_ufunc_1       (self, UFUNCPY, expr_pcommas):                              return _expr_ufunc (expr_pcommas, py = True)
	def expr_ufunc_2       (self, UFUNC, expr_var, expr_pcommas):                      return _expr_ufunc (expr_pcommas, name = expr_var.var)
	def expr_ufunc_3       (self, UFUNC, expr_pcommas):                                return _expr_ufunc (expr_pcommas)
	def expr_ufunc_4       (self, expr_varfunc):                                       return expr_varfunc

	def expr_varfunc_1     (self, expr_var, expr_intg):                                return _expr_varfunc (expr_var, expr_intg)
	def expr_varfunc_2     (self, expr_subs):                                          return expr_subs

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
		self.stack [-1] = lalr1.State (s.idx, s.sym, s.pos, AST ('*', (s.red, AST.VarNull)))
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

		if isinstance (self.rederr, lalr1.Incomplete):
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

		if pos and rule [1] [pos - 1] == 'expr_commas' and rule [0] not in {'expr_abs', 'expr_func', 'expr_subs', 'subsvars'}: # {'expr_abs', 'expr_ufunc', 'varass'}:
			return self._parse_autocomplete_expr_commas (rule, pos)

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_intg':
				return self._parse_autocomplete_expr_intg ()

			return self.parse_result (None, self.pos, []) if self.rederr else False

		return self._insert_symbol (rule [1] [pos])

	def parse_success (self, red):
		self.parse_result (red, self.erridx, self.autocomplete)

		if not self.has_error: # if no error or autocompletion has occurred to this point then remove all trivial conflicts because parse is good
			for i in range (len (self.cstack) - 1, -1, -1): # this may be dangerous because name of reduction is not preserved
				if len (self.rules [-self.cstack [i] [0]] [1]) == 1:
					del self.cstack [i]
			# if all (len (self.rules [-c [0]] [1]) == 1 for c in self.cstack): # alternative
			# 	del self.cstack [:]

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

		lalr1.LALR1.parse (self, text)

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

	a = p.parse (r"d/dx (f(x)) (0)")

	print (a)

	# a = sym.ast2spt (a)
	# print (a)
