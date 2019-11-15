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

def _ast_tail_mul_wrap (ast): # find rightmost unparend/uncurlied expression of ast implicit multiplication concatenated expressions
	tail, wrap = ast, lambda ast: ast

	while 1:
		if tail.is_mul:
			tail, wrap = tail.mul [-1], lambda ast, tail = tail, wrap = wrap: wrap (AST ('*', tail.mul [:-1] + (ast,)))

		elif tail.is_pow:
			if tail.is_pypow and tail.base.src and tail.base.src.is_mul and tail.base.src.mul.len == 2 and tail.base.src.mul [1].op not in {'{', '('} and \
					not (tail.base.src.mul [1].is_pow and tail.base.src.mul [1].base.op in {'{', '('}):

				if tail.base.is_func:
					tail, wrap = tail.base.src.mul [1], lambda ast, tail = tail, wrap = wrap: wrap (AST ('^', AST ('-func', tail.base.func, () if ast.is_comma_empty else (ast,), src = AST ('*', (('@', tail.base.func), ast))), tail.exp, is_pypow = tail.is_pypow))

					continue

				elif tail.base.op in {'-sqrt', '-log'}:
					tail, wrap = tail.base.src.mul [1], lambda ast, tail = tail, wrap = wrap: wrap (AST ('^', AST (tail.base.op, ast, *tail.base [2:], src = AST ('*', (AST.VarNull, ast))), tail.exp, is_pypow = tail.is_pypow))

					continue

			tail, wrap = tail.exp, lambda ast, tail = tail, wrap = wrap: wrap (AST ('^', tail.base, ast, is_pypow = tail.is_pypow))

		elif tail.is_minus:
			tail, neg = tail._strip_minus (retneg = True)
			wrap      = lambda ast, tail = tail, wrap = wrap, neg = neg: wrap (neg (ast))

		elif tail.src:
			if tail.src.is_mul and tail.src.mul.len == 2 and tail.src.mul [1].op not in {'{', '('}:
				if tail.is_func:
					tail, wrap = tail.src.mul [1], lambda ast, tail = tail, wrap = wrap: wrap (AST ('-func', tail.func, () if ast.is_comma_empty else (ast,), src = AST ('*', (('@', tail.func), ast))))

					continue

				elif tail.op in {'-sqrt', '-log'}:
					tail, wrap = tail.src.mul [1], lambda ast, tail = tail, wrap = wrap: wrap (AST (tail.op, ast, *tail [2:], src = AST ('*', (AST.VarNull, ast))))

					continue

			break

		else:
			break

	return tail, wrap

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

def _expr_mul_imp (lhs, rhs): # rewrite certain cases of adjacent terms not handled by grammar
	# print (f'lhs:   {lhs} - {lhs.src}\nrhs:   {rhs} - {rhs.src}\ntail:  {tail} - {tail.src}\narg:   {arg} - {arg.src}\nwrapt: {wrapt (AST.VarNull)}\nwrapa: {wrapa (AST.VarNull)}\nast:  {ast}')

	ast         = None
	arg, wrapa  = _ast_func_reorder (rhs)
	tail, wrapt = _ast_tail_mul_wrap (lhs) # lhs, lambda ast: ast

	# if tail.is_attr: # {x.y} *imp* () -> x.y(), x.{y.z} -> {x.y}.z
	# 	if arg.is_paren and tail.is_attr_var:
	# 		ast = wrapa (AST ('.', tail.obj, tail.attr, _ast_func_tuple_args (arg)))

	# elif tail.is_pow: # {x^y.z} *imp* () -> x^{y.z()}
	# 	if tail.exp.is_attr_var:
	# 		if arg.is_paren:
	# 			ast = AST ('^', tail.base, wrapa (AST ('.', tail.exp.obj, tail.exp.attr, _ast_func_tuple_args (arg))))
	# 		elif rhs.is_attr:
	# 			ast = AST ('^', tail.base, ('.', _expr_mul_imp (tail.exp, rhs.obj), rhs.attr))

	# if tail.is_var: # user_func *imp* (...) -> user_func (...)
	# 	if tail.var in _SP_USER_FUNCS: # or arg.strip_paren.is_comma:
	# 		if arg.is_paren:
	# 			ast = wrapa (AST ('-func', tail.var, _ast_func_tuple_args (arg), src = AST ('*', (tail, arg))))
	# 		elif tail.var not in {'beta', 'Lambda'}: # special case beta and Lambda reject if they don't have two parenthesized args
	# 			ast = wrapa (AST ('-func', tail.var, (arg,), src = AST ('*', (tail, arg))))

	# 	elif arg.is_paren and tail.is_var_nonconst and not tail.is_diff_or_part and arg.paren.as_ufunc_argskw: # f (vars[, kws]) -> ('-ufunc', 'f', (vars)[, kws]) ... implicit undefined function
	# 		ufunc = _SP_USER_VARS.get (tail.var, AST.Null)

	# 		if ufunc.op is None:
	# 			ast = wrapa (AST ('-ufunc', tail.var, *arg.paren.as_ufunc_argskw))

	# 		elif ufunc.is_ufunc:
	# 			if ufunc.is_ufunc_unapplied:
	# 				ast2 = wrapa (ufunc.apply_argskw (arg.paren.as_ufunc_argskw))

	# 				if ast2:
	# 					ast = ast2

	# 			elif ufunc.can_apply_argskw (arg.paren.as_ufunc_argskw):
	# 				ast = wrapa (AST ('-subs', tail, tuple (filter (lambda va: va [1] != va [0], zip (ufunc.vars, arg.paren.comma if arg.paren.is_comma else (arg.paren,))))))

	# if tail.is_ufunc: # ufunc ('f', ()) * (x) -> ufunc ('f', (x,)), ufunc ('f', (x,)) * (0) -> ufunc ('f', (0,)), ...
	# 	if arg.is_paren:
	# 		if tail.is_from_Function:
	# 			ast = wrapa (AST ('-ufunc', tail.ufunc, (arg.paren.comma if arg.paren.is_comma else (arg.paren,)), tail.kw))

	# 		else:
	# 			ast2 = tail.apply_argskw (arg.paren.as_ufunc_argskw)

	# 			if ast2:
	# 				ast = wrapa (ast2)

	# if tail.is_diff: # {d/dx u (x, t)} * (0, t) -> \. d/dx u (x, t) |_{x = 0}, {d/dx u (x, t)} * (0, 0) -> \. d/dx u (x, 0) |_{x = 0}
	# 	diff  = tail.diff._strip_paren (1)
	# 	ufunc = _SP_USER_VARS.get (diff.var, diff)

	# 	if arg.is_paren and ufunc.is_ufunc_applied and ufunc.can_apply_argskw (arg.paren.as_ufunc_argskw):
	# 		diff = AST ('-diff', diff, tail.d, tail.dvs)
	# 		ast  = wrapa (AST ('-subs', diff, tuple (filter (lambda va: va [1] != va [0], zip (ufunc.vars, arg.paren.comma if arg.paren.is_comma else (arg.paren,))))))

	# elif tail.is_diffp: # f (x)' * (0) -> \. f (x) |_{x = 0}
	# 	diffp = _SP_USER_VARS.get (tail.diffp.var, tail.diffp)

	# 	if arg.is_paren and diffp.is_ufunc_applied and diffp.can_apply_argskw (arg.paren.as_ufunc_argskw): # more general than necessary since diffp only valid for ufuncs of one variable
	# 		ast = wrapa (AST ('-subs', tail, tuple (filter (lambda va: va [1] != va [0], zip (diffp.vars, arg.paren.comma if arg.paren.is_comma else (arg.paren,))))))

	# if arg.is_brack: # x *imp* [y] -> x [y] ... reapply if removed by _ast_func_reorder
	# 	if not arg.brack:
	# 		raise SyntaxError ('missing index')

	# 	ast = wrapa (AST ('-idx', tail, arg.brack))

	if ast:
		return wrapt (ast)

	return AST.flatcat ('*', lhs, rhs)

# def _expr_idx (obj, idx):
# 	tail, wrap = _ast_tail_mul_wrap (obj)

# 	return wrap (AST ('-idx', tail, idx.comma if idx.is_comma else (idx,)))

# def _expr_diff_ics (lhs, commas): # {d/dx u (x, t)} * (0, t) -> \. d/dx u (x, t) |_{x = 0}, {d/dx u (x, t)} * (0, 0) -> \. d/dx u (x, 0) |_{x = 0}
# 	if lhs.is_diff:
# 		diff  = lhs.diff._strip_paren (1)
# 		ufunc = _SP_USER_VARS.get (diff.var, diff)

# 		if ufunc.is_ufunc_applied and ufunc.can_apply_argskw (commas.as_ufunc_argskw):
# 			diff = AST ('-diff', diff, lhs.d, lhs.dvs)

# 			return AST ('-subs', diff, tuple (filter (lambda va: va [1] != va [0], zip (ufunc.vars, commas.comma if commas.is_comma else (commas,)))))

# 	raise SyntaxError ('cannot apply initial conditions to derivative of undefined function')

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
			b'eJztffmP5DaW5j+zQFcBCkC8qfytXK7uMcbXuOzeaRQMo2zXDIz1BZft7UVj/vd9Fw8pJEUoMjIzIpMoZgUlisd7JL9PJB+pZ2/+8vrlZx9/9ulfur/8r3c/fw8/6fLjV3/9En4+f/HFq08/Bs8HX7x4+e/o+eqvX3368vN/JB/8fvoZPvn3F19ItA/p+vXH' \
			b'L17/G3s/ePW3b16+eP3qtfg/eZHuflC8fy/ez9lLKeR8/woe+VHyq/H5jz797JP0q5IHQz756NOvXqdkXn71xcf/wGSy5/WXWN7XX32QHmHvq08+//Ifr19h/p9+hQl/9OmXf0PBPvqEHqf//+MLDP+Y9PQZhoomPiAdvPzsk09eJN19kXSHni8++tu/fZkK' \
			b'8cWobHj16j/gvxeffA7/f/jBxxSGdz/9UDSGvg+K9+/FKxp79fHrV5jxFx99gr+v/vMlSvriSxIVk/ySCwgF+zL9os4+/OjvH32IMV5K3fFzn3/MCnz1ZdLlf75+9ZIe+PCjv/4Vm8CnH1FreUmFfvHph6gwDPgM43/y4vPXX34mRUwNgG78b1Y2/iiuBcjy' \
			b'5b+D9/0f377/8+1v7/+s/O/B/93b3979/s0vv33z/bc/vv/97W9VMHjf/fNXCPnhz5+S/+d3//3N29/+O12+/+PXd7+Vi2/B+9Pb37/57pcfxffbL/+3+Di/9+/ev/8u+37NvpTM22+z94fv/5nv/v57zui/3n73e/L/Shnw7T9+/q6U+b/+69fRxTc/fPe+' \
			b'lDQL9OMPRbZy96c/fvzmh59yAr+/++2nShvJ+90fv/34/yrNJO+3P/z8yygp8ORC/vY2F/Lt998n75/v8t1/vn9XxAPN5UKjGDlrVFm6+OPnH375uaqFor+ff8+F+q6IA5Vb6+rPt1mzP/+Ss/ujfuTtz9+P7tfK/Pa7X3766W2+/CUn9i2I+n/elZoaP/fr' \
			b'D+++e5cvoBX+XGT+9f3vv+Ssc8vIkvzyYxGXEh1dvK9ifvPjn29/LNXOMb/u3jzbedW58LxjT0SP6/E/1dn4XC7hinwaH+ts6Hb++egGX6kUDyLodAu99NSOcrFD98x0Zuh2prPoeZ7v0r1yYzegx/T8nzcQyommW9ru3fKjW+gFn/L8n4c0FcsEV+gFX4C/' \
			b'2Fm45pCAHvjVEJsKgg9Y3TmMoZ6Pb6XLnaU4yqJsTkSzXA68ybekXKZ7pkEtBm+6ckvXl9qIB+9hIhCqbPbRPe26Z3gF9RPMc7mz06Rlrfg/D1Wh7XO5hV6sFKoOjPm8ukz+6r7mH6hsFJP+bJ+CLXqwkHKfiw6qkJt87VAjOqvE5btyb++GLTf8+MbOcAMy' \
			b'/J/jAItZUp5Wy2WqJpDEsh49/+ex8Ny+DCbOrR2aHrYkCXBDCrBeqlnkhRiWSmBAuQoUS9XDmqdbQ32pe/HgPYyObQOEcNzM8mWY3pK2Mr7t9y8nEWcuZ25N0on7l6NIO+uqkpVOIoWY3AjTG3W/AlDgKlE2XUMnp4YJ9Wa0FA6yN9yU8u39W+VyZ0nN0Cqf' \
			b'Ya/BPjp0AQoOhUMokLxmghHuvDnmKWgc46d2ltAQBYLncn8BgRSVRgeGAQXtw0EWQ4UGGJbvlzuW7ri+3HF8R5U7nu/kdHaaAVLzf17lMuZbur6FXvRF/g/U9/x58aLPck9IUdBLXd9F6SJCCFh1jKwQEAuoYkqkGoByQx5l+L8AhVMMlyi9omQH6qri4fQU' \
			b'as4mtGDh8Sbfkute0uyxhkAl0sJG99MduEG15qT1OaYquIYOTc/QHzwoaI0e1K/n/zxoXXP6mr2oAAgM2E+5QHAZKC0N0mKewmydjtSaAHYExegBxTQ3GwoQTsVDPdjUFK0AofQFaYcqVQLcfFZ1W7qMpXChc9xOAiaWfCb5mC/QE5MnBRlqzQrSK9yHV5TQ' \
			b'3p18tWPoU04uUwgoTDE5Wf7P47NcU9i6NNfH0DEq9HyRmqnGKqK61ADYmG7pUwNJi77I/3lXQCKSFzXh+L/q9SVxm7P8H725CPtZ8qLPpMDncglXKYBuQRU+C4FrU6faRLKh8np6STIpPnZKzwEmBeC7kdwBH7yWvek7BfCmoEkAb0PVW4JfaMHYsqBqIrYg' \
			b'wCJoBkMHagL1DOCFKNADFOCJAhUp6JEKAhXoXgF+ABsZfELBn0ZWhhIri3/wLDh4GnJQkIWCLBXkqXq410MK8CKn4G0PWABwXzksHoSA5hW8ZymLMaHPQ9kgnsY/1w2mG2w3gMd3Q+gGeAYUrhzGhxxAo1hU+B9uesQqkB7e36DuBki2h2R7AN9A/QTSxmt4' \
			b'uKcKhAwhPygGlAsShEausFwGfyEf0I2yWC4odQ8S9aiTvoumi7aLrou+i6GLsYvQ2uA5UIwCzUCRoIQgJpQPOj60T3h/grdGQBQAMED6YJAXoOsH6PKhC7ELQxdRGfin8AUDCQN0a5A2ouoi5t6hxjW+bYP3Ob61wV2o5mdYv3gDosLPm2eodbhExeOPPGUN' \
			b'h6J0z4lWKVRR6Bt8b6ZrSru1jSttG88GrmTFtYmRqHYHJU2G2wLWIl4qI79WoqkgN6L8DvKbmglV9HN6z8afgROwEq3PT3m80RDnkbQqw83H6NRMpP0EqW/dqvsRVTdUsPVcwdyxpWK+pgErtwBilRKAdwRLmH1I91WoEwAylPDDSlg1vrrBTRratIlJ05o2' \
			b'Km5Mc42IG0/dYOpWMmkdi+1C9ah25nLQY08VkNq7tHNp16lF5/Zbtduqrab2KQ1SGl6rkk1VglXB3GicvIX10gGcoKRJfSjKA66XStSxweWjgkvV6vPx1OczZeQtmjtsq9fHUa8IvEOr0MdToc9IWfw6KuNU1BVPZxAZ4ywwFKxznW/1ej31atJ0hMwykEJ4' \
			b'HoMHFxBbgSaURwWBEJCgQuFcbNV8NdUMtelabT6i2vStNh9RbYZWm4+lNp8NadrOyZxEmqsTek3T9s609+NHVO0kNNU7V/sgb8koLFd4z+9TbUbwHDOCnib+TolPk+U40etlnteb2yclnbuXVWFNgL45mTTEkjnLrdF1WpDs+VWeAAiVZWX9uY3IHxPiOGls' \
			b'Li0I67bcc8Jyj9hoKDHSUGyV8YyeoOV46ZSReTxyV488nEKpsLPjFAi2VuO6thJ0h7UVvVQGV1rkOouDmFpI1RnpGcrI2rnmAM8/mu+KJU+kh+saJPkRN5nSnzmB0/Ey7DMnRj6eCd9zkTwXKfArfQ9h/bh9tCqdUjm/KQWunBCb4o5UXGCECtycAzfnMCzp' \
			b'L4FV0+NUj9zNA3fz2LcGeBwYBxngsi3kM88/Wggy2S+huM+bTezjefEko1fN1q662a9ecT3i1gE2T271eL31iObkWgyR4bdV2KVXGJmItx53zRWItaLFeB/7XKu6K6o66nyi7Gbc++DDLyypbvPSj6eHaT6HAFTTqvURVasNrT4fU32Cv9Xno6lP2gfKw0Dq' \
			b'p+3N5qHfbHCnJo0RrPzKdl7F82a8jU+PdvzJxBqWmp/oZQ3SLW0E/lo2Gne0XY0iGaLfVuMP8i5rqRKa0u9zBV9H6V/043q+0mlWTFOnalVxD1VhjEAQAxQvqzFKRTFW4aWibATJWNXq5O7qZLDSD2R9TnnhCzekWhC7CDI25t2zbMQwyECO+WsIkhBVcqun' \
			b'83NH0+ud6NU1vd4F7ToB+2Hg8UZT6llOOuibNs/WRHvhPs82KLcx8U7HLslJE14av+ZJsc2m2jJWc0StQLdIxq2WT+szPOZC83bNh4PI+Dry8LpYcOHD0bY3zruukMjvjUs7n/gEq9tmlfuS4t0W+GJqatO9Vi1TbuG93udTvHHZGluzNbZma2wab0ueKl+R' \
			b'HbZmO2wGT+qoaIg9mgaLPJCX2S7Hc2KOn/UyyellkrNV9WxVe66KdlbcY5rif0NH1jYLr2uoKUKmBlAr45xwi605uGeEaCD0jQbWdjbEhhfXgBe4lYfbs27tea09m6aeNfU0A/Ar6e4yLxVca89r8wh9a89X0Z5xk5/hHWH4gyPM5/R5JfyB+jPpwHsjNvPm' \
			b'eTLFNuVsc7JzMTzypxigaUrAtuORHk1TsdIIemkLPrUAw/MVdGUNNwDj5DqmuUMb+Y4cPknGH5wQ/ThJVg/S5uA5U51qiBYKnDLNj9Bwuh1YeU0NCE1IaCKw7bu5rmpDDZilVQHEeJOsVLRYp9C8cQP466vo0PrmNVUZ2nkZtvMybOdlxM7LzB5kZxfuu7n7' \
			b'ZCci943cx1/Pr4qaid95zpMNz9p6+K2GTS7VgG4Hgm03GpE3TCtvkJFab7MXuNNxvl15M1BpGwUbF9MqtpZVZ8OrzoZXnQ09bngkwCPStBmxLYE+EqryQk4+pgEj2fyENKrkthKYYwI/FJhqAvNQYB4KzFaxL5MTts01XUELwIqwPElkZZLIPhczd55fsDy/' \
			b'QD8guJUJAUsDfnrbkDp38kpS7N4lPGYDMrtsxxQ5p8g5RMqgIcm1tCM2TbKNGh5PhXruiTyJ2BZVFmyioS062VPqGEadwKh7LvMwDKOOYdQJjLrn8lUnh3PxIAmUovWdx9J3Itd3jPzDtdxpeaHGe56DQHk+fVjRt5bw2FrCM8XH4lNP97Rd0GYjX982ppxr' \
			b'xEudB/uZpxdPtnpLZuyKNF3vW8BuFwSIg9RO4Ply3s+Ah1DjCdR4/LRv3e1quhtkGhh3A7eHkJpAaJ3tfOcDREEyWWPyshNabFB9lPEfH0VO3TM29Z8L64amzPN9rULltmxTW9bShpEHGu5fCe7HbmDAH6T22CSq7970+OJNn1NFyxT8pOpQtVhWFFfRgMeq' \
			b'61R/WTtcuVhB/Aqu6KWcVCV6sqIqN2ApUeGk7amkmmRMAi7pbFCsVvzqEFr1Y0Oh8iquhqR+akyemgdVuSztZ1uuZNtFIwq4hx+EwI8a4Kc0ULO4GwCViB9iwa+w4CdY8Hsg2NTxSCQ0E8OvXOK3EfGLergvHXdT43ZQKJ/GuWEon8Zzz/CsGGz4eJYFnruA' \
			b'ZwTg+Vl4dhYe6Yqqxc1qpF94Bs+QQS1jI8SDZUDLGtcjcEsCnqKNR2jjMcwgqwZZNR7xhKc74YFOFrctQDhaNOBGZNw6jG9tiAO4jQ17Lho2487UiNWI9QjPQTcx0O5NjwO0HWgOAnYKSrODUu0g1R3ksLPo77vdALd7DAcv/GHn32Hv32G330GT2Bm6jf9B' \
			b'W9gpTAx6yg479w579g5rcYd9e0f3HSZn8L5Bn8VkMD3Qw27A2I6ewlvgAWl2Hv09ZgURNKUId6HB7RzmaOg/jGkpQYXlAR8IvRsoM8jaYQwoR8DEUVBooDtQ/w6qHpWwA5XuMBEqmSUBSCbMG7MiCXvMpbcioked0R0Iiyiuwf9QXx5LCsERCwnPo/QeE4WW' \
			b'soNWuIPuvgskNuaPukEpIGCg4mOqinwYCYI0lQhSpCwshUOyVDVYclIxahAuBvxF4Ukx+DgG4h9cDKQ/LCJkCu1uh+qGNrTDNLEyIomH0bBasHjQmnYB04KmvoPus4Neu4NevAuoUBQGEoeutIPmuItGCoulRl7YYcVS08BM4YkB08ZqjHiTFIjtCJthHL5G' \
			b'2EKwalDVoGoPqhpONZy6HJzSiFNL+OQriOpXUYreafm9t8xvVohV3kP3QcvcFrfwHTq9PdNb8blhzM9A2aVBmD0BxtQMlPkKznqGNNyKswprASsiHACwMIawsAXEAj1uhuRZBLNwDJyFcwJa4DJJ2eTqzkAtzMDa5aJZ2I5nYQ7RsGiCaoFwLRxCtu5f/gZ5' \
			b'Ndwgsw79DfDN/+D2m81wR2NUAb1wHO71CfpMtfYzgUEaPstQmvGQDDt5bLyGimoKjDy45lH0GkjqmbkGQsv6xc/vo2aeC8KpDJOnAXgO3o2nFDK61hMkPk990JRIniMyRyCv25++JxSGNPDbfoTG+CINz+En1xCZ8SuJ+KW/OYTGr2EejdJQ7aCTjNZ4hnA/' \
			b'nIDaeoLcXtA7no7geGxyRvF+G5LjTtiM5kEQXQmqwz08y5LQva8QHnsiHXBzAOTxgRrlcdqK4C7KxJTtGOJp2mxYBHyM5xjys1dAn7IQ3FeVyxzAgMUkQNNy+JqJLYl+hRDoAqfL8DcRg+JXXS7TAjNQoLAD7btD8bAtY07V3yxZlMJmwZSTucPxdaEQ1t8e' \
			b'jUzzm/sjqpH3f6YbFjemUC3iiHLouKiksREXUSEmXFQVG30oph/SXWSnXBRHRJW8s3xFlXY8ZaVGIcSVWsBW+sqKEgpjbVDj8hMuw3SOJTNqR8xndY0ucRolHfNzidnwdgwSV8eqVg3rK3Mds5xWN/RKpd0N1beHXwDX4G/oLSbAU6Au5kKE2xt8wQBIvaFX' \
			b'CsComx0PbiHA/w8dUrxClu7e+fL4kcPdcaTd50msla1cORqFTDky8WPjxivhRs/c6A9wIyrTT+iRb2Fz8fnCOv5dYEZ5CgkkeRMz+ooZfZVkZsZqtmd1hISBTknqCzzox4MkimLG+c5SYA7NEsw6IsAhcaCvKJBuJhZcS2A6zuKbnBqNtpDu/JTp/D7RjVPl' \
			b'4VcSUdXy2izbLMf5bRyXKkw4TupyM8dxvMRwfpHg/AaC84XgimYW+c0zv4kAid4805sXdkuNmfV0JLfNctoMlblTqOyxkph7IPJSjcAuksAQ+bAgh5YgMHI/JjB6WKbx2O/4d568dM+hZiheIS9KWchL98Vl8qKnhbwIq5fICwOdktTnyUuXGT562gl3+Srf' \
			b'OfIqoVmCWTc3AUiALbS1GnVKW3yTdZ1oi4WbmSzEllZz1zR1nzUfVC2szYLNMRdldzxzJUmEuVJFbmUuiSfMReLPMhfJdSRz6TLVWKl8ibk0L6MkAYS5qCRSBzqH0nG+/T5zzY/GEmWtDL/8iUszj5qw2kjrKRMVL5bjzypR4QMjljIVSxlhKbPMUoZDzVC8' \
			b'iaVMxVKmuMJSpmIps8ZShlnKrLCUmV+HGmU8S1M5NIsw61bXqVbj7XGUEY4yFUeZBY4a8dM4WR5bJdFULafNMs0ylNnGUJJhYiipxM0MxfESQ5lFhjIbGMoUhioFXWQowwwlAiSGMsxQRhgqtWLW0zpDCTPNEFJohNQIqRFSTUiWCckeIiQ7ISRbEZIVQrLL' \
			b'hGQ5lGQXbyIkWxGSLa4Qkq0Iya4RkmVCsiuEZBcIqc54lpByaBZh1q0T0lq8PUKyQki2IiR7DCGNkxVCEtFULWeRaZaQ7DZCkgwTIUklbiYkjpcIyS4Skt1ASLYQUtHMIiFZJiQRIBGSZUKyQkipFbOeTiWkiIREU4iIKiHxCpEK0klNJAPyREH5NYhP0EpQ' \
			b'6gU2hwr6BPIQmhByEtQQnDiCD4AJhIfQXYZDS79hM3s/IbuX+7Z5SVt8GslfPskj0Vlq9uskjw/UJG8qO22TLh3/zvN8esoMxSs8T4kLz3OYPJF4np4Wnpcgz5kltqckKJPM+cThSnKa53wMm+P8USHmOL+EZnFm3Srnr8aDVsolZ9onwaIE8SNR1I3ckBTq' \
			b'snflLWCSEb8FJGFVLbnNUs69BXBbOPotIGUobwGpire+BUg8eQsgRcy+BZgNBudU9fwWUGlm6S2AUs7NPr0FUEmCKL90CuaUk98CVN/GpW1c2iirpiyeKDWHJkrNZKLUVBOlRiZKzfJEKfYXmSjN3sRX1UQph8kTma+qiVKzNlFqeKLUrEyUmoWJ0lHGsxyV' \
			b'Q7MIs26do9biTcelRiZKTTVRao6ZKJ0kK4wkoqlaTptlmmWkbROlKcPESFKJmxmJ4yVGWpwoNRsmSk2ZKK0KushIPFGaBEiMxBOlRiZKcytmPZ3MSKoxUmOkxkg1IwVmpEO7xMxkm5ip9omx3/HvAiMFDjVD8SZGChUjheIKI1Wbx9C/zEi8gcys7B/D27OM' \
			b'VGc8y0g5NIsw69YZaS3eHiMFYaRQMVI4hpHGyQojiWiqltNmmWYZKWxjJMkwMZJU4mZG4niJkcIiI23YxEYNQxipaGaRkXgvWxIgMVJgRpJdbbkVs55OZqRT9/k2RmqM9DgZybLV48GDF+zE5NFWJo9WTB7tssmj7TlUeklt8mgrk0fbF5cZyVYmj3bN5NGy' \
			b'yaNdMXm0/TwjjTKeY6QSmkWYdauMtBpvykhWDB5tZfBolwwea0aaJMuMlERTtZw2yzTHSHabuWPKUBgpVeJWRpJ4wkh20dzRbjB3tMXcsdLMEiNZNndMAggjWTZ3tGLumFsx6+lkRtq+FbsxUmOkR81IPGtnD83a2cmsna1m7azM2tnlWTvsETJrl72JkapZ' \
			b'Ow6TJzIjVbN2dm3WzvKsnV2ZtbMLs3ajjGcZKYdmEbLD1lfCVynJLLoZSpJpO1tN29ljpu0myQoliWyqFtRmoWYpadu0XcowUZLU4mZK4niJkhan7eyGaTtbpu0qzSxSEk/bJQESJfG0nZVpu9yMWU8nU9LqhudGSY2Snh4lsYGjPWTgaCcGjrYycLRi4GiX' \
			b'DRyxO4iBY/YmSqoMHDlMnsiUVBk42jUDR8sGjnbFwNEuGDiOMp6lpByaRZh164y0Fm+PkcTA0VYGjvYYA8dJssJIIpqq5SwyzTLSNgPHlGFiJKnEzYzE8RIjLRo42g0GjrYYOFaaWWQkNnBMAiRGYgNHKwaOuRWznk5mpNV9y42RGiM9PUZyzEjuECO5CSO5' \
			b'ipGcMJJbZiQJNUPxJkZyFSNVrjCSqxjJrTGSY0ZyK4zkFhipzniWkXJoFmHWrTPSWrw9RnLCSK5iJHcMI42TFUYS0VQtp80yzTKS28ZIkmFiJKnEzYzE8RIjuUVGchsYyRVGKppZZCTHjCQCJEZyzEhOGCm1YtbTyYzUdiU3RmqMNGIkz4zkDzGSnzCSrxjJ' \
			b'CyP5ZUbyHGqG4k2M5CtG8sUVRvIVI/k1RvLMSH6FkfwCI9UZzzJSDs0izLp1RlqLt8dIXhjJV4zkj2GkcbLCSCKaquW0WaZZRvLbGCnVlDCSVOJmRuJ4iZH8IiP5DYzkCyMVzSwykmdGEgESI3lmJC+MlFox6+lkRmrbkhsjNUYaMdLAjDQcYqTJZyXsUDGS' \
			b'nNJrlw/ptZwCMVLyJkaqDme3Q3GFkYaKkYY1RhqYkVaO5LXDAiPVGc8yUg41w+jpiVtnpLV4e4wkx+7aoWKk6WG7s4w0TlYYSURTtZw2yzTLSMM2RpIMEyNJJW5mJI6XGGnxkF1qCccy0lAYqWhmkZEGZiQRIDHSwIwkJ+zmVsx6OpmRYmOkO2akdo78dTKT' \
			b'YxMHd8jEwU1MHFxl4uDExMEtmzjgHnMxccheYSZXmThwmDyRmMlVJg5uzcTBsYmDWzFxcAsmDqOM55iphGYRZt0qM63GmzKTEwsHxxYOdAnNK6vvAD9NEmd+SgKqWlqbJZvjJ7fNziFlKPyUqnIrP0k84Se3aOfgNtg5uGLnUGlmiZ8c2zkkAYSfHNs5OLFz' \
			b'yJXBejqZn7YfBdH4qfHTk+AnXl1yh1aX3GR1yVWrS05Wl9zy6pKTUDMUb+KnanXJVa7wU7W65NZWlxyvLrmV1SW3sLo0yniWn3JoFmHWrfPTWrw9fpLVJcerS04GT1l9h/hpnLjwkwioamltlmyWn7atMaUMEz9JVW7mJ46X+GlxjcltWGNyZY2p0swiP/Ea' \
			b'UxIg8ROvMTlZY8qVwXo6lZ90O9Ch8VPjp1l+4rUmd2ityU3Wmly11uRkrcktrzVhw5e1puxN/FStNXGYPJH5qVprcmtrTY7XmtzKWpNbWGsaZTzLTzk0izDr1vlpLd4eP8lak+O1JrpEfkrqO8RP48SFn0RAVUtrs2Sz/LRtxSnXl/CTVOVmfuJ4iZ8WV5zc' \
			b'hhUnV1acKs0s8hOvOCUBEj/xipOTFadcGaynk/npMo53mJyjd50sNTpBrzHVI2KqyEwVDzFVnDBVrJgqClPFZaaSp8xQvImpYsVUsbjCVLFiKg7ynNk8X0Xmq7jCV3GBr+rsZ/kqh2ZBZt06X63Fg8bJJa8oKwplRaasKJSV9HiIssbpC2WJjKoW2GbhZikr' \
			b'bqMsyTBRltTpZsrieImy4iJlxQ2UFQtlFc0sUlZkyhIBEmVFpqwolJUqg/V0MmVdxvkPjbIaZV0uZSHOQUHwZ5Wy8IGasnxfKIv9jn/nKcv3HGqG4hXKopSFsnxfXKYselooS4I8ZzZLWRjglOQxT1kYNkdZo+znKKuEZkFm3SplrcaDxsklL5TF91nlUbQM' \
			b'7Szr8QBlTdJnykoyqlpgm4WboyyKfjxlpQyFslKdbqUsiSeURSqYpSxqDkdSFrUQpqxKM0uURSnHLIBQFpUkSGXEUhmsp5Mp6zIOiGiU1SjrgilLMWWpQ5SlJpSlKspSQllqmbI4C6Ks5E2UpSrKUsUVylIVZXGQ58zmKUsxZakVylILlFVnP0tZOTQLMuvW' \
			b'KWstHlKWmlCWEspSTFlKKCvJeIiyxukLZYmMI4FtFm6WstQ2ypIYibKkTjdTFsdLlKUWKUttoCxVKKtoZpGyFFOWCJAoSzFlKaGsVBn8ezJltQMkmin64yYouMavzOI3nbZPCWqeEtSHpgT1ZEpQF7JiaKVJQb1IV07imKF406SgriYFdXFIV9ga6eE0J6jX' \
			b'Vq808RQCwvJ0oJ4nKm6S5W9+SjAXLYsx69anBNfi7X0zS2umKuxh6bsZVL6DLIVPcbL8vPCU3EaiSrLSpc3e+RlBvYmrXCkxTghKfW6lKpLeFSv1ooS9KUG9YUpQE1lJ08r6WZwT1DwnSI9qajfwTDU7qHl2UDNv5dbNOpvwlo039AaWvjVshxt8AwFguiFi' \
			b'BzS5QT4GNLihr3tVTLZ68IR7uPHXJX0tCsDnpJEYSH/aV6Ma4V3BiIwt3P0hC3eI6CdG7r4ycvdi5O6Xjdyx8YuRe/amQVll5M5h8kQelFVG7hLkObNEdpQEZVKGZmzw7lcM3v2CwfuoELNDsxyaxZl1c2xHQqXR2VpUHJ0ZflxoL43RxPjds/G7F+P3rNZD' \
			b'Y7RxLjJGE2FVLbnNUs6O0bYZv6cM0xhNqnjzGI3jpTHaovG732D87ovxe6WZxTEaG78nAdIYjY3fvRi/58pgPZ08RruMAyxuQ2uGmM1d1qjt5E8hNlI7jdTMNmLDr9iOyC2e+iUPNkE0h0wQzcQE0VQmiGkMZ5ZNELFTiQli9gq7mcoEkcPkifwlj8oEUYI8' \
			b'Z5a/heiJ3fAnf9WDzRHNijmiYXNEBtyePuE5YrlRYWa/7pFDs1izbnVMtxqvtyIB8xsJKPruuQ6iqB0/85EUe4DfJlkwvyUxVS2zzfLN8ZvZZpyYMkxf+pBK3spvEi996WPRONFsME40nnpT/tpH0c7id5GDtECqDfpGcGWoaNhQ0YihYq4Y1tnJXHcZR2Nc' \
			b'8BCusdyFs9y9Dt0CD93CocW0MBm3hcJs7Hf8uzBuCxxqhuJN47ZQjdtCcWXcFgqzSZDnzPK4LfC4LVTjtsDjtpWZSgybHbfVhZgdt+XQLM6sW19SW4uHg7ZQGI0EEz33rPso6tYl0sER2zgLGbGJmKqW2Wb5ZkdsYROjpQzTiE0qd/OIjeOlEVtYHLGFDSO2' \
			b'UEZsRTOLI7bAIzYRII3YAo/YArNYrgzW08ksdhnHaTQWuzwWU1fEZPq+v7jIW5nNoa3MZrKV2VRbmY1sZTbLW5mNhJqheNM4rdrKbCpXxmnVVmYJ8vKTxmmOx2muGqfxtmazsq3ZLGxrHhVidnyWQ7M4s259fLYWr7dSchmfOR6fOWYzKrg8ieOzpNBD47Nx' \
			b'FjI+EzFVLbPN8s2Oz9wxbKb5OAoZo0mmaYwmFbx5jMbx0hjNLY7R3IYxmqNZjzxGKxpa/CIjb3JOQqSxGW9yNrLJOVcK6+tkVruMQzgaq10eq10Lo93r2Iy3k/lD28n8ZDuZr7aTedlO5pe3k3l5ygzFm8Zm1XYyDpMn8tis2k4mQZ4zy2OzyGOzWI3NeFOZ' \
			b'X9lU5hc2lY0KMTs2y6FZnFm3PjZbi4djs3o1LfLYTPaVed5X5mVfWVboobHZOAsZm4mYqpbZZvlmx2bb9pWlDNPYTCp389iM46Wx2eK+Mr9hX5kv+8oqzSyOzXhfWRIgjc14X5mXfWW5MlhPp7KYuYyjOhqLNRa7Chbjg3n9oYN5/eRgXl8dzOvlYF6/fDCv' \
			b'5xSIxZI3sVh1MK8fiissVh3MK0GeM8ssNjCLDRWL8SG9fuWQXr9wSO+oELMslkPNMHp64tZZbC0esthQsdjALCZH9Xo+qpcukcWSQg+x2DgLYTERU9Uy2yzfLIttO7A3ZZhYTCp3M4txvMRiiwf2+g0H9lZjsUoziyzGB/YmARKL8YG9Xg7szZXBejqZxS7y' \
			b'QI/GYo3FLpLFAu+TDof2SYfJPulQ7ZMOsk86LO+TDj2HmqF4hcVCtU869MVlFgvVPmkJ8pxZYjFKgkMSiwXeLR1WdkuHhd3So0LMsVgJzeLMulUWW40HTTRUu6VJMNFzz7qPom5ocFmhB1hskgWzWBJT1TLbLN8ci1H041ksZSgslip3K4tJPGExUsEsi1G7' \
			b'OJLFKquPSjNLLEYpxyyAsBiVJEhlxFIZrKeTWewyzvi4xe6zi9xxdoiVEiMlNkpMlBjoGtjnapiHtzuHQ9udw2S7c6i2OwfZ7hyWtzsHzoKYJ3kT81TbnTlMnsjMU213DmplA1ngjc5hZaNzWNjoPM8wuSi52LNunWHW4k33iwXZ2Rx4Z/MRbJISEh7hLcyB' \
			b'Ny+HpZ3LYdvO5ZRJ4g6pns3cwfESd6SdyyPa2LBpOZRNy5KyXrMWDLxrORU+8QbvWg6yazm3Tf7dwhvEF5dxwEbji8YXd8YXvBkrHNqMFSY7sUK1EyvITqywvBMLd2TITqzsTXxR7cTiMHki80W1EyuYNb7g3VdhZfdVWNh9Nc8XuSi52LNunS/W4u3xheyy' \
			b'CuZYvkgJCV/wdqrAG6nC0i6qsG0XVcok8YVUz2a+4HiJL8wcX2zYQBXKBipJeZ0veAdVKnziC95BFWQHVW6brKPNfHH1p1s0vmh8sc4XbDMXDtnMhYnNXKhs5oLYzIVlm7kgoWYo3sQXlc1cqFzhi8pmLrg1vmA7ubBiJxcW7OTm+SIXJRd71q3zxVq8Pb4Q' \
			b'q7jgjuWLlJDwBZu/BTZ8C0tWb+Eoq7fCF5JJ4gupns18wfESX7g5vthg7Ea1LXzBKa/zBVu6pcInvmBLtyCWbrltso4288XqGRLXwBeXsJLSTkN6TCsnvP4fDq3/h8n6f6jW/4Os/4fl9f/AKRC/JG/il2r9PwzFFX6p1v/DsMYvvOYfVtb8w8Ka/yjjWa7J' \
			b'oWYYPT1x61yzFm+Pa2S1Pwxd/jBvOGadf5KsMI+Ipmo5bZZploW2rfOnDBMLSSVuZiGOl1hocZ0/bFjnD2Wdv9LMIhPxOn8SIDERr/MHWefPrZj1dPIKyWWc/dAYqTHSpTBS5LX8eGgtP07W8mO1lh9lLT8ur+XHnkPNULzCSLFay499cZmRYrWWH/sVRoq8' \
			b'fh9X1u/jwvr9KOM5RiqhWYRZt8pIq/GmjBRl5T72hZHiMWv2k2SZkZJoqpbTZpnmGCluW7NPGQojpUrcykgSTxgpLq7Zxw1r9rGs2VeaWWKkyGv2SQBhpMhr9lHW7HMrZj2dzEiXcUJDY6TGSBfDSLzGHw+t8cfJGn+s1vijrPHH5TX+yFkQIyVvYqRqjZ/D' \
			b'5InMSNUaf1xb44+8xh9X1vjjwhr/KONZRsqhWYRZt85Ia/H2GEnW+6OqGEkdw0jjZIWRRLSRnDbLNMtI2ywBUoaJkaQSNzMSx0uMpBYZaYM5QCzmAJVmFhmJrQGSAImR2BogijVAbsX8ezIjXcZpC42RGiNdDCNpZiR9iJH0hJF0xUhaGEkvM5LEMEPxJkbS' \
			b'FSPp4goj6YqR9BojaWYkvcJIeoGR6oxnGSmHZhFm3TojrcXbYyQtjKQrRtLHMNI4WWEkEU3Vctos0ywj6W2MJBkmRpJK3MxIHC8xkl5kJL2BkXRhpKKZRUbSzEgiQGIkzYykhZFSK2Y9ncxIdFICEMJFnEd+YcQ0ewY5hKM2Lp6k1AlEFa+QrNR9H/2DHRUX' \
			b'l9n8DXvbgcPIB+wR42OAbCGvXf7oBt1dOAgIM/XMX8UvBEapC4Fh30uuHAVkC4Ghf5HAMPDQdzfwmdnzf+qcZ8//wXJjUfnMhPr5iZvjMIJqoTF+ipuqWkpiSmd8k4uR6IzuHTwAaJysHAAkcqpa6OyzS5RGSSxSmuZvc0wOapWM0yFAUrVbaY2qtqxGkRZm' \
			b'eY0ayLGnAFnqVPkUIC7bqnEEJR+zGEJuVBypD51D6RggOyI3zNHdUDj9T3c83YkD/g9Uh88A01HhNPwgz0ETfrPGcpnfanKbMJtLbMZURvQl3LVPXLOstWoxxwS1ODraIxV/pI1bIg3DBLFEDEePXoQINhNADf5Tu7UjAT8D/RrAmwrUo4B5rEccwwbwHsH2' \
			b'DGYvATYhdYHojM8ZkzMgL6PxQSg+3r4sge7q6GAfMwkwjzMPy8i4ky0nyyC45aU+4952xKvhbt/+62iMS+C2Dmu7+jgYhDLCMUKwBF+IQmodhfxFAFF+WUaNNjxaewENK5h0LB5te5ukV79HAkrV26AaDkxdNHCaAydsbSsAtQ2c9JGvSP1mcCqD/DPjk17B' \
			b'J3sLjPJXhFP+SKyKx2FVsOfFqxFWcQc/H17Zh8Ws+aFqxixNUHIb3LLXiV3YwI7EL3ckfmGbPALDzO2Heeb+XrDGM5BLy2K3AbIjQSxiGGoGnkVgfVBQ2zADeJYB4W0AbQOYpfm7y3wBo+LVf2vApob7eyGjl2wir55mey8D5FA5tx9B6rBpBNn9Cxr2DchD' \
			b'M1r2LDNafgvULa3GHPu6toRwc2sm7mkOKTOiza1j1GsYEA56L2sZuBgXBOlcQTvQPn7qmFEPngXZNciOCKhxZaKsbcCfuT80VAlzbomGmMQdIeLqq10/Z1aMNd+GpRXioQaXX+tw/Y7W4AyjH+nbc+PdUWPVBQ7TihzBoqbC0wdw0hmVO0UNBNXKcIkXkV4K' \
			b'3T3P/d8RTDaIFIjs73/W7SFn3B4I4ubgzTZ4o1FrON+sm+/eXNKi5IodzX0tUF4SLOkHWKCsIIkJ8OIQ6SQ0IjMmMlvyZKJ0MQuVl4lImrTyEAuV3b+GG+BCGmSGy0KnbYgExUL7FrT0eZzotAWZ0FbuPMuVF//CdM92E2wfiQ+5J4JN296WWDVnfGWKVw1K' \
			b'8Kvx110YOLkHBii07LstUJXJremkVgOtKWjhw2TPvcN2dZng5S8Av3aYGmZzSxgzNGWYp6umk1TDWUHN3D+u2fvDtE277aqNCw9iIzZc/8sXVs5lgxnNBOt7hzJvtuFZBjOFIj7c/JU/A55NX8tA0HMimL1/BKvQCwp3GW9lD4xeDbnu2uZ+hFpYxxf3EnYZ' \
			b'oHUHgKXOCljuYQFraIDVAOsBAEs1wLo3wNJnBSz/oIAFxWqA1QDr/gFLN8C6N8Ay1zxTf0nodFG7rS8ckS4ajO4KeTTlenWLg2dBmu5f0K9uEHvRZgE01kDn8YHOiRZUjwJ46B3rQoHnWs0SzmguFcINUANhj2vY07DnsWAPraM97DsPFaEhzyLy+BshiOEG' \
			b'UZow6MIsyhsGNQy6DQYND49BQ8OgjRj04HbjWw6IPQWSQnWU6zVCU7xDeFICUU8ApijHDFVliojP9y1/Z4cuzpiQKxyFYfqSMWzvFNIzA5mWrzyQGk4CtAe3OW+A1gDtXgDNVIBmKkAb/90BoJltgGaeNqBpATRzIqCd1968AdpVAdqTATNbgZmtwMyO/u4A' \
			b'zOw2MLNPGcwYyOxpQObPa3beprvadNdZkYow49GYGVwAGj30fBd+PAn6MmHPeS3IG/Y07DkFe6hLPwEbpzOCD3+ri/+uCXycutlRnzD4JoT95GbHfQV+GZPOayTeMKlh0mmYdD7zpyeDST7/PTJManbgTwGTeJ0FpyYvFZ/4oNhrMQvn0j4APFHGtx6uSfFP' \
			b'RSeKfhCdNJ2hAkGHccrGG+InaBU3iPzQqW4IiKFn3CCUQiuHX0OI1YzInwJiXSpKmatCKfNQKGXOglLmdih1lneoTdjUjMwbNt0zNuG3zp/mxrpN2ERqemwT3hYnvLHJ9+Shr8/4ZmTeMOh+MIj639Pe3HsIgyT4ES+6GVzwxy46BPTQRl//4EbmDYMeIwZx' \
			b'5HbCwAYQYpU9+qV/o26QoKA/wS/PbD+4XXjDoEeBQXz7As4auFYIeiLWRxonivqBsOfBTbgb9lwV9hAyXJiJ9nVhD2vwiUKPwjEYQkzEuWmlEINCs75uGHQAg7CdXfIukeuCoKf9+kO2RYpef0Izvm7Qcwh6XIOeBj3nh55mY92gZwQ92HguZstZw55Hhz09' \
			b'rrwT9Fy1KTUULn8A8yJgCLr4xXz4sh23fW5Mwjre4fOXh07g/CVgFKa2hlSbzvsH1byBitNGYXPEVqN9TwGuewO6i3gfb8Mf3fb1bTyoQ9Ht0L3RUGgd3Nfow8Yfv34O/mc7GPT1+DQ+t4PXsL6LER+Cfk9JgmLfIGBA3XegEdAH1DlUF6gJKh6KCloGJUOj' \
			b'HRBb4Dn51nrJELELkkDTVkRVhYszgB8Ir2gJB30E0QaRB9EWnsTj13FZEHsl6FiDWPBHpbG3Lo3tjvhHeTnMK6zlFgcCaHNEtg5x3O39U9A1GHHtfiiVwi+WoqfPklr6UpafK5TdKxd+6bOANHboQcraT8oLJDX6xx9/D6O/UTj0/PrpQDEQiNGPX2TxdPAT' \
			b'hZNg4QEEA6QP+OFYEBDSO8M//DwyfhIZBYonCqSXZALQUdD+FbR/BRizKKP1K3JCHgf/Id+P7xDTEsMaYtVRmB89TbIPtezI3uGABoAKIBlgNjy3qD6oaF8tbqyZXtHiLrIwLSFo3l9D55iQFbvjXX8WsYWPqFOQT9YoHo4CmbJm8S3PiYbjspaxKdO7id/X' \
			b'OL5fJK1DfNS8RgSDQush1QK+sGWX/tbd5OHp32KEvWy2/u0VcuKdz3mpBIvCML2A7xJ7Db1cP6Bj3ahRr0JW7PDteGv3Cif0sN5v72U0unjwnqa74upxk97o/NYImsdGRzyH45nNaW9z3IB0g+X1xmK6p+S4UZjLRFzbPahj3dhbdRj/AH2Gpm/uvd+E7nSH' \
			b'E1C3if9weXAbcQ1U1xtH7J6S40Zx6jB9qebPh6u4yeMWjqZ/b+lYRaH1m9V+gy/4T8hxoxhNmhxsEUd1Haz8s3UfqlVxOCldX5/mcCHlpJissPFMy9GjQWc65zoXO5D0jjuVgTCrq87Vy/AQnsH5QNyW//CdzXXZ4WC3vl5xvMJW/o6MtsmN0xYf/RicAtB3' \
			b'kmnleCmgb2i93oB895QcNwp16Wgdu8twrK5bTb+cv98cq+a1vnG4XwxddrRmPBzlcNn5yEdv747PjOvRNCxcrXM0h3lCjhuFvRsspKnnc+EhGimd26Hxz0kxWW1t9uRAX4rdU3LcKPzd9SWs/PP1p6G7C4e2dCfFZO21iZX1LoW2mU/IcaO4o4mVuvLP1q3Q' \
			b'cvZuHFqmnhSTldjMWg70rNA9JccGkf3WnnXyYG7ToG1lsFY6Wuw2ObRM3hSBLL91OPSUW0yWVawuuN9Vs5kP3v9wp8HFOPzEHv6YO8+KG4m+t35Yt4ez90ncKnLHrt57cYt0WO2nTIbw6sN9rDtcZC+13VbHwqjN8Y5xuOPmLtJddtxwtk2YMKKfdx70TF13' \
			b'uaJDd7zDPTubIuy7tIfqxNiRYlabnuCSq+qUSZoLWWF8+N4+dKc5FsmcGPugw012d5T0guO2tG1u5xq7PW7tvFbHdXTKDFLr71L7tmvOC8dvm3W6i85+ylrnSZ3edffvsKWe5yFyXGenTHK1zi+twHfNedmbeyuToSs1d8DjGx6J40q81dTbtVai7R6L40ps' \
			b'+74OVLjvTna046b6u01ae4nuXU28G5JbCOMG0iyaDjSQ0D0lx43idpvfnkCjiN1Tctwomr3WeqPAA7uekONG4VujWG8UtntKjhtFM0M70Chc95QcN4rYGsV6o/DdU3LcKJpZ3YFGEbqn5Pi0vb57Y/noJV44dCrd0GzwA1XzBndB9pZuKjzqkwNgNFs3GIVn' \
			b'vL7BoyHxUEU8YRGP2dRW0rXzT+PRPaM/ftrtPY0VTTHgavKnHbdwVx/EaHH6SlILdH9yUAg94bExGHo+8oGt2Ayp6VlqbticFK3XsyGOA2gdpZKbbqziOY7r8UBTOu61OuqVj1d11ZGqSo5ThUYb+FXPDVgiPJJV025o1DqPDKBFj06VRIMCObJQ4bWi/Xhc' \
			b'ddDqwR9oexinC90534Fa/Pr5/wd20ZWG'

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

	# def expr_diff_ics_1    (self, expr_div, expr_pcommas):                             return _expr_diff_ics (expr_div, expr_pcommas)
	# def expr_diff_ics_2    (self, expr_div):                                           return expr_div

	def expr_div_1         (self, expr_div, DIVIDE, expr_divm):                        return _expr_diff (AST ('/', expr_div, expr_divm)) # d / dx *imp* y
	def expr_div_2         (self, expr_mul_imp):                                       return _expr_diff (expr_mul_imp) # \frac{d}{dx} *imp* y
	def expr_divm_1        (self, MINUS, expr_divm):                                   return _expr_neg (expr_divm)
	def expr_divm_2        (self, expr_mul_imp):                                       return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                            return _expr_mul_imp (expr_mul_imp, expr_intg)
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

	def expr_neg_arg_1     (self, MINUS, expr_neg_arg):                                return _expr_neg (expr_neg_arg)
	def expr_neg_arg_2     (self, expr_diffp_ics):                                     return expr_diffp_ics

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
