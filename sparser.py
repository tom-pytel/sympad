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

	if tail.is_diff: # {d/dx u (x, t)} * (0, t) -> \. d/dx u (x, t) |_{x = 0}, {d/dx u (x, t)} * (0, 0) -> \. d/dx u (x, 0) |_{x = 0}
		diff  = tail.diff._strip_paren (1)
		ufunc = _SP_USER_VARS.get (diff.var, diff)

		if arg.is_paren and ufunc.is_ufunc_applied and ufunc.can_apply_argskw (arg.paren.as_ufunc_argskw):
			diff = AST ('-diff', diff, tail.d, tail.dvs)
			ast  = wrapa (AST ('-subs', diff, tuple (filter (lambda va: va [1] != va [0], zip (ufunc.vars, arg.paren.comma if arg.paren.is_comma else (arg.paren,))))))

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

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('-diff', expr, 'd', ('x', 1))
	def _interpret_divide (ast):
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

	# start here
	if ast.is_div: # this part handles d/dx y and dy/dx
		diff, tail = _interpret_divide (ast)

		if diff and diff.diff:
			if not tail:
				return diff
			elif len (tail) == 1:
				return _expr_mul_imp (diff, tail [0])
			else:
				return AST.flatcat ('*', _expr_mul_imp (diff, tail [0]), AST ('*', tail [1:])) # only reanalyzes first element of tail for diff of ufunc ics

	elif ast.is_mul: # this part needed to handle \frac{d}{dx}
		mul = []
		end = ast.mul.len

		for i in range (end - 2, -1, -1):
			if ast.mul [i].is_div:
				diff, tail = _interpret_divide (ast.mul [i])

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
						expr = _expr_mul_imp (diff, ast.mul [i + 2]) # only reanalyzes first element of tail for diff of ufunc ics

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

def _expr_diffpics (lhs, commas): # f (x)' * (0) -> \. f (x) |_{x = 0}
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

def _expr_ufuncics (lhs, commas): # ufunc ('f', ()) * (x) -> ufunc ('f', (x,)), ufunc ('f', (x,)) * (0) -> ufunc ('f', (0,)), ...
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
			b'eJztnXuP3DaW6L/MBcYNVAES3+r/HMczG2ziZONk7g6MIHAS7yK4iRPESXYuBve73/MiRalEVUld3a2qJqx2UaLE5+H5ieQh9ezNX16/+PzTz1/9ZfeX//Xu/Q/wE08/ffnXr+Dni+dfvnz1KTg++vL5i39Hx9d//frViy/+EV3w++pzvPPvz7+Uxz6m89ef' \
			b'Pn/9b+z86OXfvn3x/PXL1+L+7Hm8+lHv/Hvv/IKdFEKK96/gkJ9WfhXe/8mrzz+Lv210oM9nn7z6+nUM5sXXX376DwwmOV5/hel9/fVH8RZ2vvzsi6/+8folxv/qawz4k1df/Q0z9slndDv9/x9fov+nVE6fo6+UxEdUBi8+/+yz57Hsvoxlh44vP/nbv30V' \
			b'E/HlIG149vI/4L/nn30B/3/80afkh1dffSwlhq6Peuffe6eU2MtPX7/EiL/85DP8ffmfLzCnz7+irGKQX3ECIWFfxV8ss48/+fsnH+MTL6Tu+L4vPuUCfPlVLMv/fP3yBd3w8Sd//SuKwKtPSFpeUKKfv/oYCww9PsfnP3v+xeuvPpckRgGgC/+bCxt/Wq4F' \
			b'iPLFv4Pzwx/fffjz7W8f/szcH8D9/dvf3v3+7S+/ffvDdz99+P3tb5k3ON/981fw+fHPn6P7/bv//vbtb/8dTz/88eu73/qT78D589vfv/3+l5/E9dsv/9O7OL4P7z58+D65fk2uGMzb75Lzxx/+ma7+/nuK6L/efv97dP9KEfDlP95/36f5v/7r18HJj99/' \
			b'6BOa8vPTj8n58x8/ffvjz+mh9/1NUADR+fu7337Og43u7//47af/mxVSdH734/tfBjGAI6X3t7cpvW9/+CE6/3yXrv7zw7s+p1CIKQODqLH04skf73/85X1WIX1Rvv89Jer7PpdQz3mx/fk2FfL7X1J0f+S3vH3/w+B6Vq7fff/Lzz+/Tae/pLC+g5z+n3d9' \
			b'nQ3v+/XHd9+/Sycgj+/7LP/64fdfUsxJRlJGfvmpzy0FOjj5kD357U9/vv2plwB+8pvdm2d7p3bW3+zYEdBhW/xP7Uy4kVM4I5fG23bG7/buZnCBz1R8Dh7Q8RI66a49xWKb3TO9091ur3cGHTfpKl3rL+w7dOiG/3MafNVNfkmZg0tucAmd4God/+cggpbz' \
			b'BGfoBJeHv7AzcM4+Hh3wCwmndENm4D+9s/hEezO8FE/3htLaGsyblawZTgde5EuSLigzBUWq8aLtL6n8VGlx4DUMBHxbk1x0TdndMzyD+vFc2nBlr6iUVcv/OUibMjdyCZ1YtlQd+ORNdhrd2XWudKxszCb9mSZ6G3RgIuU6Jx2KQi7yucUSUalIbLoq1w4u' \
			b'mP6CG17Ya8qaxstURcbwf5ZvAdfeUJKMltNYYZgsTlfg/xxkw0mSsfoaElEQIpQp8cB72MN4qXDJOciIoRRoKOYWnqeK4jqgS11+qhpx4DV8HMsEsmNZ0tNpGF8SqRledoenowf94enEHaO7wuHp4NLeuCxlfXORRIwu+PGFvIWZTqqkNfEcmjuJKCgQrSRx' \
			b'WKxcEeny4aX+dG9aCgyKH9sPttZu57E2dygJWuKa8EbF5/Qpd4FwDO/aG2oiKFRwX2o5kM6WM+RZIbSQWwsPd5leQL90vb9i6Ipt+iuWr7T9FcdXUjh7xapS8X+uTWlMl1R+CZ2YgYb/g+K7uemdeI/hlhAfQSfVv+3YQwQDTqEmSS1BGYRevaLaofoApa7J' \
			b'0Wr+z0PiWlacmPuWgu2oqYqDdTZWwc5EvcGZx4t8Sc4bCRNb8w5gJBI2uB6vwAXKpBPpsyKNUJiGFEtLf1gG/Ag6sHwd/+fgRsXPKHZiAUB1eGynnCA49ZQhBbnFOIVxOxVImqBmRJ/RDS0Db9IXlDklDwXdRFE0ohKlLYgcqlgJcPFZ1rDpNPSJCzvLcuIx' \
			b'sOjS0cXkQEeIjuilSZpbyGxPQTyjgA6upLM9q77Wymn0gQJrGVOG/3N4L9cUSpeiMoSQKX7V8EkUU4VVRPlVII0Ybt+mOsotugL/52yvJFh9YEk4/i97kXFCOWv5P3qHET9LTnSZ6Hkjp3AWPZgZIETec20mdlF7JAe9Lpn4PL7SOGqJzkQPfEuSK+CCF7Q3' \
			b'za4FcWihXBTKByATxQAqHSULqiagBEHTBXXU7aCYoHg6tevgEdAlLZR1C62xBY8WfFrQHS0UGdAI9EDb4h/xGVLcQnG0kALwxicg+BaiayG+FiJsGwgBRLqFV7oWmhpQAPR+Cy8fLZR6C29bLQTagopr4d0NtCdIbQsBtxByZ3ad3XXg8Lsu7Dq8B5+FiKDk' \
			b'WksKElMLDoe6GHIPFecwVgi3gXAb0L6eGgooFLwGtzZUg5BiiBTihKRg2qBMWiiUFkqlhWJpDaYK33Hh7RZygGFBZI3ZBTjsLrhd8LsQdgHEDYoO/LFkNNIeX/ogq5YEFF6l4AUSVApoMFD1XiMYoO17t4Ma92Hnu11odgELBP9IDyM04NCIjqB2AWPeYRoU' \
			b'vnuD8wbf4eAqVPUzrGO8gI/fgLfhU6wA/FF8F9YL+mI+bwit5NuS7xt8i6ZzCrvKxwXLx7OOK7rlGsXaoRrulIgNy0On+bQ18mvlsTbIhU7uF3GTB/EOxyGzgHUibixXbZPuogtV81yRZOmWdYeKoiIy5KXOlatVfl1VDpUcG7YhvSCV8w11YFkKmCzJA6+I' \
			b'TmEEUflnvlYUEZPocXOYCWAudCNhG4uZiNdYsFigpgSJBSgXmlxQRgJSkg6QCyx246TcG1LQUeZF1kW2o1QnGc5kN5fXKKM2Cd8mBO/iqgWVIXNSW3kra6QR2Pji5aRRdHKDlfc1SmtVm1emNttap9dVp89a7hy9eWabWrfXVbfQXnWt1Cur1GetjoS1ccjE' \
			b'xuEOgjKOFEPadlAUtW4vq261iS9P8lqFhcLjHNzpgKdbKI0WiqN18BwE2GImbFer+qKqGmrU1Rq9shr1tUavrEZDrdFrqtFnXZxGsDL+J2O9cVQjDvNbU9+br6zqKeNU9/Ju1cjrM2aYa73hl6w6enim0UNHrWvN8zS4jgPDTsaFnbl7UFbqWyZ6FE/lLQ1G' \
			b'y3iJCqseVzIB2UjGjExZ19HSa1M4cSRcZoaslxFyMVJoxTiBckC/IpdW/BtdZ5JWzCS1UuyBmR641QfubWGbx4aL0otzGijjdRLpfmskeKkQluvAYt81YrEh0p+m37W8krHhzzPHP4obkWLPQGd5LVL+kTlM+WeWIW+Hs7jPrAywOH79c5wkx0ny/LbfgF8z' \
			b'lJFapSOye3538lw5vqsFd2rBsRx7lmMvOqoplV9UWLUcx+XIzdxzMw9tFcDTlLGXfq/oUydqVeRQx+FnjctdqontVb2Qkg2tYuNZVc1hL7wucUUCWzzXurzsukQrdSW2zfBbK+0SKo0sz2vLu/RKxJpRsi4A216tvgurPmqEUuDVZngDPQxeSaPqWPZ1tTTF' \
			b'GyB0plbttVWt8bVOr61OwV3r9KrqlJaecjeRfuvbzhbednBxKPUfWImmVcSYRq4sHnPLFhgaJimmmu8QM5Ty+uNvZH3zjlbH0UOaAqm1/mjvuIYqohb8Q8/uq07aGf3Yhs90I22JX1NrdTxQdWjRcjybySpLNFYQYxaeZkp2laQua73cc710VtqDzO+1Towq' \
			b'XBNrQuwqyI6ZF+6KXQYDrWOedUEC0vzOUevqPlhSy/beytbWsr0vFFsTX2AbLuRasGcS2qatBXpOSW0Eh47NWu5iRB73jZENx5y0AcVjaIuNwQWvhmehqFNBRowUHBAZeV1rfWWty8tpYL72RmFYwsHWF9GH0GVBxkf09DorXoNx16hSe2pViFbEJrcIrNUy' \
			b'Rgxt6HPGgud9gMjIW7GRt2Ijb+qOS5wqnZF5t2Lzblag5PeMDQ/70bIgl7kbaXnozGp+VMZDXWBa1qqerGrHVVF3sbu2GYE3uGChGoxdTG2RhqqKaqbbE+6w8geXpBAOfFtxMLdwohqZXozOwNVCLNO6yvScTJtaPHN9sKY2+ctp8jJW5V2V6TmZbqtMX4xM' \
			b'43pCzQvP8Ad7nTf0YSj86egim+JrMcXXN9G6W/c7sZOJjObRAHoCSpsCsHWTpqsSFyPy0Yg8+CgFmscx6MwYFgJt5byLY4qG5Spui0k2IxwQ/VgJVjcid0pCkL0W0aiBQ6ZxEx6Jr1tpXpgQoeUJDRLWZT2XV3VYCro0a4D6XkfjFiVGLTSuXJX9ZVZ2qG30' \
			b'0qoNzcQ0m4lpNhPTYiamp7fWMyUPO+lB1iXRQ4sH/jqOQXG8hl8ZhfjWcyrYkq3Ont9t2ihWiK67kK3pn5L4VvuCey9nO/Om0CpZlaGN/MrgSmC9EaQH2lCHkyaoNc84kB5hY/I6ZXpF2HICKtfFziQaXOFEKkOG5cUzazzf5Bk5noEUmEee+RfafvDC1PGo' \
			b'C5ECrAzDA0lGBpLMjVjN8/iD4fEH+oGMGxkwMDQgQO8asQ8irye9GT2Lku2S8Zkp2z8FkhrUQ4b1kKkvwpclS2zWZComrqtSHbdIHmyskzClrXahTGTpqmV1akWd2hsZp2F1almdWlGn9ka+TWVx3B5Fy9X2c1XtJ7BkhI4lgWt6p+QlG6858YIUxM9FuioN' \
			b'1ygNz1rexJ9avKMBW5uMhV1d53LGzjC1IWxujt5F2XAuWsQrKux8GQS2Pi862UsFeX6t5eURuE027pGNG2Tjls+11V1Oq4NIPatgzzLhoxj42ubOuiFBEJ0mPUJZISZ7y1PbodbIe6ZTKw21Bs6n9aB4anmeUaIheVGiTZRoJZKMUKgQuCAIQIys/TupQTat' \
			b'anZvGnwhp4/FonULfjC2y6SWC4urqcOd4FUU2lRAXMFYSfxq3tLLOpWWFJWh3HmaiqOEpkIfZ1ZTNlMeC8XWKSpV+nYSLhYgeWlZxrA+ohyTTHmSEqp5sQxIZmHJTMzyaw1+xgI/xYAfAMHCxUUGWI74CRn8fgx+PAa/YoISjxszocUZfr4TP/iIO2TgAnhc' \
			b's40rTiF9CoeRIX0Kd6nBHUpR/nGXB9yNADfHxB28cONZLFloMYqKF6sR7oNaVFjKWMy4rQ2UssLpC1zpgJt942bRIHMK8qpwI3fcaAr3mMJtpQyuhgB/NIjAtc64Ohnf5FAd4Co5bMBoK42LXwOKOpxDnlSH9QlV2WiQjT2EAh77FlKyh5TtIeQ9xLI36G52' \
			b'e/CDRIM/OOEy6oA9KoE9tv49pHcPYrHHRr/Htr5v8Q+azB7b+B4b+B5rcY9NfK/xEsjKHhvSHtv3Hqttr/EGKId9h0mx+LTFKOCKwz90Q5L3UER7hbeATOwxHItxa4oSLxsKGq5ZvAQVsoeM7zu8Cu1vb/EpiMpjBFAFexDSPWY8YIbBE4p2j6FxYJQJyhfG' \
			b'T1HhX0MJsJJNh+WGsYE47APmjzKJRQnCt1d4FRME92MJOAwUpGUPkriHVr/3VJQYP+YPfSH4jooU46EYW7wMf1hCLaURHzLkD8FS9cAVzCLqwT1I7L7DX8w8FQ7ejp74h46GqgXTCF6gB/dYdRgglj0I1D5Q/vBWjIvKChNNGYVboA3toenuoSnvPRYg5gZi' \
			b'DJgeuB6MpJbEAesRE0glCnc6zCKFjTHhHVSpKEgoi13zDaovVFpVZVWVNaWyqr6q+mpj+kqhvirpKZepqmZWW9F7Lr8L9+OgmebqX00PlZc+g/7CV+v0Uk0vy2fWZ9hjPtBpW9NldoU+UxM6zWd6rWXdhkt9ZvWbx5rwRzSZH+oyv0Sbeb69EUdZq52k1/y5' \
			b'NZvndEEwPv27P+02pd82rNb8csXmp1Rb16s3TwrOH1Nxu3+5W6Ssv0XOdu0tkOf/4fqexXqPOq+i/fxpCrCJOlBnk0UHXXXuWks3m7rnbBZ6XD2qAw1JHW/uYc9pSz01FkFqM38V9Ifqs43jKTiOYtIYAY/Yu9GoQ1SzcQQljq10onLbbBDJnKCC3eFgP6lj' \
			b'CAO/VUhqGV89sfo8q2j86iN+uXBSVTcL1DXUO5RJUtu4xzHuX75afVtR4Z7VOG4Zu1aV47bOSZ23C1V6k6n1IKpdiXqHa1gWpObbTNWjJsDKtUe0Pf7m6h7HtUjnBRm4sjvW9SgZ5JjW/PicZd0fnVH7UxQCAPaTOyIMWGsxDWjcDl+JUZLoV8hAJ1o8IyHw' \
			b'yRlESIJbdggmaIEfZhHlmbRK/zdJjT7B2GJSBtpmkBspJWEJl+EBT8bxTf0Rc6RXwNzhLIfoqyU7UkCt+MgjGZQoESMoZclGF2bTN/EqYiolxRKxonMSXFRxp7MrCoYQLErBao4NSo14pvwIahjQqVQjYWKw5VVaghsF3aX7IuLwcoh1pbqsWjUnJ0GPcacA' \
			b'd/iCpewtVbhvbvHNxvtbep/x4RZfaRiKqHNv8VWjxbtQ8YOCut1znxc8HFLTzFHTPjg4F/Ul7hGWdgKYzXJoDvolY1hGUFZIXggkHUPSHYEkFqYbcdLRJWxHLp0Y+S0gMt7VJGdCpMsQmR09Il2GyLk+Uzs/HMTJ4yzn3aaWe02DuCdZmHyRha54EAm7CEOX' \
			b'sZAuRhzOBTDuefFFDo36X/HaAHnukHjDULlDFrOo8vzalLdJ2LllsJMII+ykPtfDLqWzQDq3gHSuJ11fNEXQOQad5CByzjHnnGAuSjSn5ETITcJtgml2DdOumWbukSimKsk2STJkFybm2DQFFeSQZHSzjPAp6empckcPi65hikVnpJjKRvpU0x+JYnS3UEw1' \
			b'MxRDzxmKKenWqb5XR09EiPks7imK9b66G6R0dEyNDZLmFn7NPjrml5LOm2p6fqlxly2OI6K05RAbh+57l8ov25SxKYRxuZ2MsJgTQViszNUI69M5jTASiRMRRvXNCMvKvIQwxVMtMQeCMMUDkkp6akmcOSVjhE33zyK7ZjpkbuX0zfWTq/a9njCxeGYdf2aJ' \
			b'hTcMcJVNr7Pb8W8BV/GJJjkTrnSGK90fPa50his9hys9jystuNLTc1WDyCd5lXyxGnXxmJ3Lmn3uAFZaYKUzWOkCrAagGgbLva2YNZXn06Y8TaJKL0OVRBhRJRW5HlUpyAKq9AJU6R5VfUqLqNKMKslBRJVmVGlBVRRlTsk8qgRRE2TylUyVTJVMYzIZJpM5' \
			b'RiYzIpPJyGSETKZMJiN3NcmZyGQyMpn+6MlkMjKZOTKZeTIZIZMpkCmPfJJMyZeqsXjMk2nuuQMyGSGTychkTiHTMFghk2RN5fm0KU+TZDLLyCQRRjJJRa4nU0pngUxmAZlMT6a+aIpkMkwmyUEkk2EyGSFTFGVOyVoyBSQTDXpiQ/MRMEQX5EpOlA6B0ev6' \
			b'WUUfFSwpVM/KEz8ukxSgKD5UUKh4osIhpeJIiYCyQCXhd9s40ECwW8zxJ2Yl89AWMnHFUMX99nGP+DYk+vO4xxty3NOv4B7bjWLis/ck8dNdTXJG4lPgQnz2kzsi8eluIb54OY4scl8z+vEn0h/dM/TnpHLWp+g/SMgU/XtfCDe/e3TM0n/2OZBULid+AaDM' \
			b'BfHiKghS5KqvBZ2KaO59YBQRvw/EzA5yblMup94H9DIDzhihvA/Eal79PtCnc/p9QC8wWCd54feBrGhK7wMUcpdyIO8DlBKpIpV825jGle8DbVO7qrWrWtk1ZhcPoupjg6h6NIiqs0FULYOoujyIquMTTXImcGWDqOwndyRwZYOoem4QVc8PomoZRNWFQdRB' \
			b'5JOwSr4IK1085mE199y4q6plEFVng6j6lEHUUbCCJsmayvNpU54m0bRsEDVGGNEkFbkeTSnIApoWDKLqfhA1S2kRTTyIGnMQ0cSDqFoGUZMoc0pWo6mtaKpoqmgao8kzmo4tN9Oj9WY6W3AWl5vRbwFNXu5qkjOhyWdo8v3RoylbhUZqu4im+ZVonDzO6ySa' \
			b'8sgn0ZR8EU2+eMyjae65AzR5QZPP0ORPQdMwWEGTZE3l+bQpT5No8svQFGtL0CQVuR5NKZ0FNPkFaPI9mvqiKaLJM5okBxFNntHkBU1RlDklq9G0duVwRVNF0/WiybCx5NE9HczIUtJklpJGLCVN2VLSNHJXk5wRTSazlEzeJrOUNJmlpJmzlDTzlpJGLCVN' \
			b'M42mQeRTaOp9pcEXjlk0zT43RpMRO0mT2UkeLG2bQtMoWEZTzJrK82lTnqbQZJZZScYIBU2xIlejqU/nNJrMAitJ01tJZkVTQpNhK8mYA0GTYStJI1aSSZQ5JavRtHxxd0VTRdPVo4kH9MyxAT0zGtAz2YCekQE9Ux7QM/GJJjkTmrIBPfaTOxKasgE9Mzeg' \
			b'Z+YH9IwM6JnCgN4g8kk0JV9s8HpwoAT2/rNs0sVjgk0yomeyET1zyojeKFhhk+RN5Rm1KVOTbFo2ohcjjGySmlzPphRkgU0LRvRMP6KXFU2RTTyiF3MQ2cQjekZG9JIsc0pWs2l2CXVlU2XT02QT20WaY3aRZmQXaTK7SCN2kaZsF4lNQuwiozOxKbOLZD+5' \
			b'I7Eps4s0c3aRZt4u0ohdpCnYRQ4in2RT8sUGb4rHPJrmnjtAk9hFmswu0pxiFzkKVtAkWVN5Pm3K0ySaltlFxggjmqQi16MppbOApgV2kaa3i8yKpogmtouMOYhoYrtII3aRSZQ5JavRNLsSuqKpoulposkymuwxNNkRmmyGJitosmU0WbmrSc6EJpuhyfZH' \
			b'jyabocnOocnOo8kKmmwBTXnkk2hKvtjgbfGYR9PccwdosoImm6HJnoKmYbCCJsmayvPZ52kSTXYZmiTCiCapyPVoSmEU0GQXoMn2aOqLpogmy2iSHEQ0WUaTFTRFUeaUrEZTXedc0VTRdIAmx2hyx9DkRmhyGZqcoMmV0SS+pknOhCaXoSk7ejS5DE1uDk1u' \
			b'Hk1O0OQKaMojn0RT8sUG74rHPJrmnjtAkxM0uQxN7hQ0DYMVNEnWVJ5Pm/I0iSa3DE0SYUSTVOR6NKV0FtDkFqDJ9Wjqi6aIJsdokhxENDlGkxM0RVHmlKxGU13oXNFU0XSApo7R1B1DUzdCU5ehqRM0dWU0dXJXk5wJTV2Gpq4/ejR1GZq6OTR182jqBE1d' \
			b'AU155JNoSr66G9w9OubRNPfcAZo6QVOXoak7BU3DYAVNkjWV59OmPE2iqVuGJokwokkqcj2aUjoLaOoWoKnr0dQXTRFNHaNJchDR1DGaOkFTFGVOyWo0hYqmB0BT3cb+MhFl2R7CHrOHsCN7CJvZQ1ixh7Blewgbn2iSMyLKZvYQ7Cd3RETZzB7CztlD2Hl7' \
			b'CCv2ELZgDzGIfApRvS+Em989OmYRNfvcGFFWzCEsm0PQKV+2pxhFjAJnUMUMqjy3NuVsClR2mVFEjFBAFatzNaj6dE6Dyi4wirC9UURWNCVQWTaKiDkQUFk2irBiFJFqg1OyGlTLN5mooKqgejKg4hkoe2wGyo5moGw2A2VlBsqWZ6BwbxWZgYrOBKpsBor9' \
			b'5I4EqmwGys7NQNn5GSgrM1C2MAM1iHwSVMkXQWWLxzyo5p47AJXMQFmegaJTvmxPmYcaBS6gkgyqPLd9ziZBtWweKkYYQSXVuR5UKYwCqBbMQ9l+HiormiKoeB4q5iCCiuehrMxDpdrglKwFlapbRVRQVVAVQcXzUfbYfJQdzUfZbD7KynyULc9HWfE1TXIm' \
			b'UGXzUTY7elBl81F2bj7Kzs9HWZmPsoX5qEHkk6BKvggqVzzmQTX33AGoZD7K8nyUlXG/VITHQDUMXEAlGVR5bm3K2SSols1KxQgjqKQ614MqpbMAqgWzUraflcqKpggqnpWKOYig4lkpK7NSqTY4JatBtY2NI0Z79l0urga79VVkXRGyAiMrHENWGCErZMgK' \
			b'gqxQRla8q0nOhKyQISv0R4+skCGLvRxHNg2uMA+uIOAKBXDlSZgEV/JFcIXiMQ+uuedAQLmEMnYFYVdgdgVhVyzLY+wahi/skjyqPMM2ZW6SXWEZuyTCyC6p1/XsSukssCssYFfo2dUXTZFdgdklOYjsCsyuIOyKtcEpWc2ubewsUdlV2bVtdjnea8Id22vC' \
			b'jfaacNleE072mnDlvSZcI3c1yRnZ5bK9JlzTH4ldLttrQrwcRzbJLje/44STHSdcYceJQRKm2NX76m5w9+iYZdfscyCgXEI9u5xsOuF40wk65cvulK0nRuEzu2IeVZ5hmzI3xS63bOuJGKGwK9branb16Zxml1uw9YTrt57IiqbELsdbT8QcCLscbz3hZOuJ' \
			b'VBucktXs2sbWE5VdlV0bZ1fL7GqPsasdsavN2NUKu9oyu1q5q0nOxK42Y1fbHz272oxd7OU4sml2tfPsaoVdbYFdeRIm2ZV8dTe4e3TMs2vuOWRXO2JXK+xqmV2tsCuW5TF2DcMXdkkeVZ5hmzI3ya52Gbskwsguqdf17ErpLLCrXcCutmdXXzRFdrXMLslB' \
			b'ZFfL7GqFXbE2OCWr2VW3pqiW7NdPKjjHj+DiB6aWjxYqHi1Ux0YL1Wi0UPXUYv1K44WqyC1sCIq5FZ1pvFBl44WqP5BbKI10cxwuVHMzXGoWWPs0UqimiUVimf1Njxam5OFooSoe86OFc88dfMRLRYMMbp0ELErfUVzhXRws3y/AkstIrJhXOrXJOT1YqBZB' \
			b'SyKmTcVtqtPVzKJicE1WCgejhWrBaKEiarV9Ot2clTsFHctSkeDAPdnAoeKBQ8UASyLOvyOAmXBL72Pxc8gWQBZIO90S4kGl3CKYQSXc0ufGMqTNbmlhH69HtrmvVzUr+2bNyq9YVfJdQB+NDeTdMQP5jr6SN+ymZTbyTmzkXdlG3sUnmuRM3bTMRp795I7U' \
			b'Tcts5MXLcWSRehQEh5Q6a/P28k7s5V3BXn6QkMnOWvLV3eDu0TGFPcpY7K/NPYr9Nc23C/8oi1LiDd8VpOD5sjvFdn4Ui/TaJLMqz7lNuZzstS2znY8Rxl6bVPP6XlsKstBrW2A773rb+axoir02tp2POYi9Nradd2I7n2qDU7K617aNrTHuyDdDiHMb68et' \
			b'/kZjpds6upmFhGuGlINyWvlBETZc1McMF/XIcFFnhotaDBd12XBRi69pkjN9UCQzXNTZ0X9QJDNcFC8nP4I5CoJDSh8XmTdi1GLEqNmIkTVvS98XHeBukKDJj4wkX/zIiCses7282ecaK+XFoKNMSpk3XA9B7uTL+hSTxlEUDLqYTZXn2ab8TYFOLzNpjBHG' \
			b'D45IRa8GXZ/OwgdHFpg0YnP1/RBlVjzFTzd7EUOqQfqKcWbeqNm8UYt5Y6oZTtVq6G1j042td+oq7raNuwftzHnuzPljE25+1JPzPeKcDFzSb6En5+WuJjlTT85nPTnfH31PzveIEy9uO31PznNPzmc9OT/fk/OMOPyd7MnlCZnsySVf7Mn54jE/7Tb3HHbj' \
			b'fI82ypyUdcPlH6TI+TLffKwPN4xC+nCSTZXn2ab8Tfbh/CK0xQhjH04qeH0fLqWz0IfzC/pwvu/D9UVT7MN57sNJDmIfznMfzjPOUm1wSlbjbBsbdVScbRNn6oKQph/6U5CWe272WM/Njnputscaux3/FnpuVu5qkjP13GzWc7P90ffcbI818XIcWeq5We65' \
			b'2aznZud7bpaxhr+Tn4XMEzLZY0u+2GOzxWO+xzb3XBPLSXpslntsMjlHCZci58t887Ee2zAK6bFJNlWe5z5/kz02ewrWFPEp9tok0thrk0pe32tLYRR6bXZBr83SYEjqtfVFVPxUpOUem+Qi9tYs99Ys4y3VCqdmNd62sb1Hxds28XYpaHvQ3hovS3PHlqW5' \
			b'0bI0ly1Lc7IszZWXpbl4V5OcqbeWLUtjP7kj9dayZWni5Tiy1FsL3FsLWW9tfnGaE5MTV1icNkjIZG8t+WJvLRSP+d7a3HPYW8sWp1HmoheXf5AiV/1DR3trwyiktybZVHmebcrfZG9t2fq0GGHsrUkFr++tpXQWemsL1qe5fn1aVjTF3hqvT4s5iL01Xp/m' \
			b'ZH1aqg1OyVqc6W1sAlJxVnF2MTjrGGfdMZx1I5x1Gc46wVlXxlkndzXJmXDWZTjr+qPHWZfhjL0cR5Zw1jHOugxn3TzOOsFZV8BZnpBJnCVf3Q3uHh3zOJt7DnGWG5B0jLNOcNYxzjrBWSzUYzgbRiE4k2yqPM825W8SZ90ynEmEEWdSwetxltJZwFm3AGdd' \
			b'j7O+aIo46xhnkoOIs45x1gnOYm1wSlbjbJNbhVScVZxtFmeeF6/5Y4vX/Gjxms8Wr3lZvObLi9d8K3c1yRlx5rPFa77tj4Qzny1eEy/HkUWcURAcUsSZn1/C5mUJmy8sYRskZApnvS+Em989OmZxNvsciKnPlrBR5qSsGy7/IEXOl/0pq9hGUTDOYjZVnmeb' \
			b'8jeFM79sFVuMUHAWK3g1zvp0TuPML1jFlpmIZEVTwpnnVWwxB4Izz6vYvKxiS7XBKVmNs23sHnLHVWybXLl2DE+CpoSliCRB0SVg6HIQxCvR/LGVaH60Es1nK9HY7fi3gCAldzXJmRCUrUNjP7kjIShbiObnFqL5+YVonDzO6xR2plGTkoOoUcVjHjVzz43X' \
			b'nfFFLuFwivVhCkiAwivMPK8s86VVZX7ZqrIYSYSIVNF6iKQCIIgM+LFgPZlXPT/4STVnY+h5PVlMfQQIryLzsoosCaikbwFACBzb2LqjgqOC417BYRgc5hg4zAgcJgOHEXCYMjiM3NUkZwKHycBh+qMHh8nAYebAYebBYQQcZgk4UnIQHKZ4zINj7rkDcBgB' \
			b'hzkVHDEgAYdhcBgGhymBwywDh0QSwSFVtB4cqQAOwWEWgMP04ODg5sFhGByS+ggOw+AwAo4ooJyUxeC4in0zKjgqOObBwWuk/LE1Un60Rspna6S8rJHy5TVSXnxNk5wJHNkaKZ8dPTiyNVLezYFjfl2Ul3VR3i0BR0oOgsMVj3lwzD13AA5Z/eTdqeCIAQk4' \
			b'eJmT5wVOvrS6yS9b3RQjieCQKloPjlQAh+BYsLCJqlzAwcHNg4NXNMXUR3DwaiYvq5mSgHJSFoNjdneKSwHHFmZb6oZLVzS7Enhb23BsW9sw2tY2ZNvaBtnWNpS3tQ2N3NUkZwRNyLa1DU1/JNCEbFvb0MyAJsxvaBtkQ9tQ2NB2EPkUdHpf3Q3uHh2z0Jl9' \
			b'bgydILvZhmaXPh0cTtnHdhQsIyhmTeX5tClPUzgKy/axjREKjmJFrsZRn87pWZSwYB/b0JtsZ0VTQlLgfWxjDgRJgfexDbKPbRJlTsnqWZRt7CpR0VTRtCk08cR/ODbxH0YT/yGb+A8y8R/KE/+hlbua5Exoyib+Q9sfPZqyif/QzqFpfrI/yGR/KEz2DyKf' \
			b'RFPyRTS1xWMeTXPPHaBJpvlDm6HplAn+UbCCJsmayvNpU54m0bRsgj9GGNEkFbkeTSmdBTQtmOAP/QR/VjRFNPEEf8xBRBNP8AeZ4E+izClZjaZt7P1Q0VTRtCk0sUFAOGYQEEYGASEzCAhiEBDKBgEosmIQEJ0JTZlBAPvJHQlNmUFAmDMICPMGAUEMAkLB' \
			b'IGAQ+SSaki+iSRWPeTTNPXeAJjEOCCpDkzoFTcNgBU2StUE+bcrTJJqWmQ3ECCOapCLXoymls4CmBbYDobcdyIqmiCY2HYg5iGhi04EgpgNJlCWNa9G0jX0cKpoqmjaFJs1o0sfQpEdo0hmatKBJl9EUn2iSM6FJZ2jS/dGjSWdo0nNo0vNo0oImXUBTHvkk' \
			b'mpIvokkXj3k0zT13gCYtaNIZmvQpaBoGK2iSrKk8nzblaRJNehmaJMKIJqnI9WhKQRbQpBegSfdo6lNaRJNmNEkOIpo0o0kLmqIoc0pWo4n2YAAybGI39C0SamoHdPDH4tg8rdRiYrVdd4HUUg+9uxAay2GDZYJhi5tHGIqXHlnO6cxybp8+/qHLtnMUq9hA' \
			b'JHfabiiznsMGGI9+u6HMek7PWc/peeu59P0PXTCfG8Q+uccQph2Ty9sxaFM8pmjGSluIxrexwKpSGGOyaTGs06YnG2v2I2QbBctkixlVea5tdJlSx0vPmt3hhlkHhIsRx52GpH5XE46kgCWnsNXQAgM8rIZsMaskbtaWQrMRXsyHcE6zEZ4WI7yYac3JyTiH' \
			b'Mdpb8qf/6QoAD/7v+P+W7gHoaf76hzaIPGg9b+aAl1CXc24EORvBxlQjkgnGDhlWAtispR2zqthhOsCLP800LuHDiClcCRGndmgECatR4CbM3U5U/Unlz6l6k6n3TtR6l6nyrlmgxgf6e0J5lzQ3qexeVydFnZRz0sxltXySTj7dLC1q39kOw6HuJMV5mlVZ' \
			b'0pB7WbtSVoZL3vOT/ruD5tun783m6u5kXReV3Lx62+dr9FGlkT4jTRbVGGqjdl4buc0opCbppLbqpdlX0jCjm07VS8veL+ld8IqUU/Z62HZHRjWqkppUUihyM4pqmZJSJ74yNYuVVN//P7+e0jN6yq7XVdgdvxh95U/UWd1pOsvb8+qtgc7izu359JbJ7P4f' \
			b'SXfZed2lSKXcRX+ZzHD/knSYog+FnaTH3Il6DAXzBF2m79790w/6wjUapCxNod1Bo52qzQL6oVjDvahhH1W7LRgkPEtP8S6abYFWiyN8230joyTmf3Maru0e7g2N3ryJZC0NCm9E22ER3b1rqfyit7bdv0C6byFDNORlzjLk5ZbovJmZm1Pf30qabmp6xT7N' \
			b'vmbSbFNTHvl0B/hDufefxIM0+SAaz2Var6HvMrP2g3sh7wryzpqwyadB4M88nFYkjTiY8FinFc39asbZd71myjgZpaD2V3PNh1VUfs8zcc6OJw9YJhxL8J4kVvdqMc7g8UwCJZ52evayFGbfkpT03+jBk47eEu0DTxLcn7qsqlJUZfvww3KPOST3iKpuSs2p' \
			b'qua4OxvONyzndm+2NotZtsF5qBnNLakn/QgzmplqIo20Pc20Wivxri6aLZ1Ka58fY2Zzo5pJUbE8xszm7l/dLYCROp9+e1pqkWYCCUDbGDQTuk4ttURDobndeeY3N/8C9QgGF2RmSVmyT0VHLXt74rI54ytUuHTlhCnGX7cxJeUeWVHBr72rwsoHv4aDXlV5' \
			b'TSkvuMLm4XuUrW0qMbcFPbYHb6rCO6ozTWOKaThrPIjVnVW56UfRb/YBdduSlXz5WojH0G/N5b+MYeVsX6lhuKgBHlilObNMryWl1mIWH3F8y59Br41f0yCn59Rk5lE0WabFIHHbeEt7bC1WNdgDGPEPtBfW8+ZeyjaivO5BcbVnVVz2sRUXpKwqrqq4Hkdx' \
			b'qaq4Hk5xqbMqLvfoiqutiqsqrkdSXLoqrodTXPrCR/S3pKU2tax745pp80rpvjSQolgvbzLxLBpn9y9oXLeohNHWAZJclc9VKp+VFlhXo4DovWujCuhizRnOaG7lwy0wgnSQrTqo6qAr00E07/a470CUhKqByhrI3zIpcNNJaNSkizZooV51UdVFd9NF2OQe' \
			b'WRdhEqouWqaLtmCHvmTT2hWqyYRsd9kLVFEHO8GeU00pUVVPRF1RrOn1qR9C4m2H+7+zqzCOmDRYOEWXURq2q8sOtkU9s0JT8ikKKodVim0LNuxVsVXF9mCKzWSKzWSKbfh3D4rNLFNs5okrNi2KzaxUbOe1X6+K7dIU25NSajZTajZTanbwdw9KzS5TavZJ' \
			b'KzVWaHadQnPnNWOvw2F1OOzeNBbHcQ32CVtQS489IObsLSCIdNB5LdKrDqo6aKUOolb9RGykzqiD+BNj/HdROsi2t3tqHAbfjLCx3O6p0aD9FO1T6s5rdF51U9VNq3WTr7ppjW7y6e/adFO1K38iuqmlKRkcvdyqnuK9ay/JzJxT/AhqiiK+ey9O0r9WS9Hj' \
			b'R7WUor1bwOu4vjLhlmAFonGLCICWdUsaGZrHLapUEHX4pQ8eumqU/kQ011a1lbk4bWUeS1uZ82grczdtdZZ3qkU6qhqtVx318DoKP9/+dBfuLdJRVFRXNy5u1C1xCtoQOrinV43Wqy56MF1EbbAuIj6mi8T7mufodHdLYIL2hINPtKDYbcFoveqia9RF/HDd' \
			b'0WChMuJiu36LAd3eIq2gUcEvvxdtwc686qKr0EV8+fHX8l20Knoqxks4XATsIh20BZPwqoMuSgeRhtigyfdl6SAuxaeqglrsm6GeCTiG3ZIlpa/W3FUXHddFKGpbX31yWaroib8OkY0Sf1vPV2PuqoJOUEGuqqCqgu5JBVWb7aqCxioI5Wd7S9qqDroqHYTr' \
			b'arkjdumm2arpP+S5CXUExbSZD3jW7cDvQzdhPe/x/u1pKQx5E7oKvO2cxlr0XQII/A1cUVqhTKLoKNeSh929gcILeB0vwx9ddvll3B1E0WW/e6Mg0cq7b9CFLaD75gbcz/bQGWzwbrxvD69lzS50eBM0fr6m8Ro2XFB9egeFAtUL9QXFBaUHSYVihlJGk90G' \
			b'74MWJR+R72MEDQKlTUayLVpl4FQOaBFUsmilAXKGegf1D4SCe1ngBvG4IgjbJhSyggzAHyXH3D05ZnfCP4rMYmR+NrqG9LQ5JV6L+twe/GuDEs176GcpGa6YjIa+sGroI19uKlX2MGH4ydJeWyPlGklsO0owAGvwj79qHwZ/A/8wvDvQE6iR0Y2fkHG08xT5' \
			b'U878Y+QMdH7Ar+BCDsPuHP/wg8/4kWfMUViZI13MFKie1uOeINggmnImjZ/JKMRz9B+if3iFoEuwNQTYgZ8b3E2Z7/LM43uTP1IEoKOgFPBtSA33SDosFzcqGgAiDa7jCxtONQDIUHu2YhHPq509bUmByCDrFaBpKlLckwVi5aLFdyHHRey7cjFjluj9xB8W' \
			b'Ob5rpGJvqOgV6jFItepiNeCbZjroTa7dDa4dHnJHvHn8V3zgIJqlfweJHDmnY55K1zC08Y0kOXB1k+2GUvmIBxdOO2hX+FK8w1flhQ0M3l9WtLHGr2hnzRbamtr1R96LUgsP7DEtfQZ7Sifcp2g9wb0eLEGqauYj0qJ3T+lgqdAbVbpm96gHF465S5OB/D9G' \
			b'q2keo+X43foDR6Tu8vzjxcFCYqtePSIdYfeUDpaKtR32YtWfT7XiCMsdDhoRvuPBZeRry5lvOfie/4QOlorB8MlRkTit8WDtn60B0VSFHDhKre584OzKqie5xIZjLif3CkHErd3hkFxz781Kg5/RWfNq5UMScA8ODuJ6/8dvbnaXDuz05uczB8+79X8nPrbo' \
			b'GIYtLvqhyQF9L5FmB88NNFVhH5Egt3tKB0tFu3mFHXbbOLi87jYQc/6Wc2o5z7WO4y0D59jloInk0w6ciz7x1rsfp0fGFamrOpyvdLSVeUIHS4W5J3WItX82lYgmTOc+0C5o1ZNcbnUc5VhrCrundLBUuHtsTVj752tR3e4+DjS0W/UkF18dYjnSqNB48wkd' \
			b'LBX3NcSS1/7ZGhba1t7PgYarq57kUqymLsfalt89pYNtJZulbWt9p25R522u05YqLOwWHWi6vOgBMg1XR+9yxWC5jNstt7xsZPPRWyAuR9jMgR/9s2zSf89RsZSoh2uJuUCcvVXigpJ7PvLlGXcIh8t9zbAIz0U8yCzEJtup2S09ODNq8XOnHLgq5z7CLR8s' \
			b'OcuGTkSpn3dM9FyNt1jTfnf6gQt7Fj1weMSFViufDvRktjIKTrmu1gzXbGXG8fHbe7dbd3CWzMqnjx64FO+egi4cLEzLRnkusuHjItBLPbiS1owl1RYfq9/s6uGE88vGny6zudvdxR5cSWuGt2pzj9XvdvVwbCBilg2J3UtzX2PqsKbZo8Q/+IGiep6b6OBK' \
			b'u9sY24VaqeB2HFdycC0+SVsj3FHlSg6uxWpodKzG/W71wUum+r+7hHUQ6MHZyLkguIIfS8idVqo9CQkJu6d0sFRUk6pjUtHtntLBUuGqVMxLBe7C9oQOlopqKXZMKuzuKR0sFaFKxRGpcLundLBUVMu3Y1Lhd0/p4J3y6urAY1IRdk/pYKlod28MbS+peGAR' \
			b'Kj1eYHshqJo3hoqbLircw5U9oFObS0zb8WNQXbhYS0M14e6wYu5l7fTduAvT4I/vdgd3Y0XTEyAGoz8lRg/WZ5trov2jl9ACXR/t+MJ3oDAYur/jnXhRDEn0LIkbihNeB3HhsEC5DkJJottlzzl+1uFOtbyPb7+HL++b67K9cpXsk4ttkl/3XIMpQmG2tKId' \
			b'F41z9wAkerBTKK5b5FyCnMO5ogWVXHUg9eAOtLxPwjX9FajFb27+P6G6o28=' 

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
	def expr_neg_2         (self, expr_diff):                                          return expr_diff

	def expr_diff          (self, expr_div):                                           return _expr_diff (expr_div)

	def expr_div_1         (self, expr_div, DIVIDE, expr_divm):                        return _expr_diff (AST ('/', expr_div, expr_divm))
	def expr_div_2         (self, expr_mul_imp):                                       return expr_mul_imp
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
	def expr_sum_2         (self, expr_diffpics):                                                              return expr_diffpics

	def expr_diffpics_1    (self, expr_diffp, expr_pcommas):                           return _expr_diffpics (expr_diffp, expr_pcommas)
	def expr_diffpics_2    (self, expr_diffp):                                         return expr_diffp

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

	def expr_pow_1         (self, expr_diffpics, expr_super):                          return AST ('^', expr_diffpics, expr_super, is_pypow = expr_super.is_dblstar)
	def expr_pow_2         (self, expr_fact):                                          return expr_fact

	def expr_fact_1        (self, expr_diffpics, EXCL):                                return AST ('!', expr_diffpics)
	def expr_fact_2        (self, expr_attr):                                          return expr_attr

	def expr_attr_1        (self, expr_diffpics, ATTR, expr_pcommas):                  return AST ('.', expr_diffpics, (ATTR.grp [0] or ATTR.grp [1]).replace ('\\', ''), expr_pcommas.comma if expr_pcommas.is_comma else (expr_pcommas,))
	def expr_attr_2        (self, expr_diffpics, ATTR):                                return AST ('.', expr_diffpics, (ATTR.grp [0] or ATTR.grp [1]).replace ('\\', ''))
	def expr_attr_3        (self, expr_idx):                                           return expr_idx

	def expr_idx_1         (self, expr_diffpics, expr_bcommas):                        return AST ('-idx', expr_diffpics, expr_bcommas.comma if expr_bcommas.is_comma else (expr_bcommas,))
	def expr_idx_2         (self, expr_abs):                                           return expr_abs

	def expr_abs_1         (self, LEFT, BAR1, expr_commas, RIGHT, BAR2):               return AST ('|', expr_commas) if not expr_commas.is_comma_empty else _raise (SyntaxError ('absolute value expecting an expression'))
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                            return AST ('|', expr_commas) if not expr_commas.is_comma_empty else _raise (SyntaxError ('absolute value expecting an expression'))
	def expr_abs_3         (self, expr_paren):                                         return expr_paren

	def expr_paren_1       (self, expr_pcommas):                                       return AST ('(', expr_pcommas)
	def expr_paren_2       (self, expr_bracket):                                       return expr_bracket
	def expr_pcommas_1     (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):           return expr_commas
	def expr_pcommas_2     (self, PARENL, expr_commas, PARENR):                        return expr_commas

	def expr_bracket_1     (self, expr_bcommas):                                       return AST ('[', expr_bcommas.comma if expr_bcommas.is_comma else (expr_bcommas,))
	def expr_bracket_2     (self, expr_ufuncics):                                      return expr_ufuncics
	def expr_bcommas_1     (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):           return expr_commas
	def expr_bcommas_2     (self, BRACKL, expr_commas, BRACKR):                        return expr_commas

	def expr_ufuncics_1    (self, expr_ufunc, expr_pcommas):                           return _expr_ufuncics (expr_ufunc, expr_pcommas)
	def expr_ufuncics_2    (self, expr_ufunc):                                         return expr_ufunc

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
	def expr_neg_arg_2     (self, expr_diffpics):                                      return expr_diffpics

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

		if not self.has_error: # if no error or autocompletion has occurred to this point then remove all trivial conflicts from top of cstack because parse is good
			for i in range (len (self.cstack) - 1, -1, -1):
				if len (self.rules [-self.cstack [i] [0]] [1]) == 1:
					del self.cstack [i]

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

	a = p.parse (r"f(x)'(0)")

	print (a)

	# a = sym.ast2spt (a)
	# print (a)
