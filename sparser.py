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

	elif tail.is_diffp: # f (x)' * (0) -> \. f (x) |_{x = 0}
		diffp = _SP_USER_VARS.get (tail.diffp.var, tail.diffp)

		if arg.is_paren and diffp.is_ufunc_applied and diffp.can_apply_argskw (arg.paren.as_ufunc_argskw): # more general than necessary since diffp only valid for ufuncs of one variable
			ast = wrapa (AST ('-subs', tail, tuple (filter (lambda va: va [1] != va [0], zip (diffp.vars, arg.paren.comma if arg.paren.is_comma else (arg.paren,))))))

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
			b'eJztfW2P3DaW7p+5wLiBKkAS3/ub43hmg02cbJzM3YERBE7iXQQ3cYI4yc7F4P73e95IUSqJVVJXd6uqCatdlEjx5ZzD5xHJQ+nZm7+8fvH5p5+/+svuL//r3fsf4Ceefvryr1/BzxfPv3z56lMIfPTl8xf/joGv//r1qxdf/COG4PfV55jy78+/lNs+pvPX' \
			b'nz5//W8c/Ojl37598fz1y9cS/ux5vPpRH/x7H/yCg5RDKvevEJCfVn47TP/Jq88/i79tDGDMZ5+8+vp1zObF119++g/MJgVef4X1ff31RzEJB19+9sVX/3j9Est/9TVm/Mmrr/6GDfvkM0pO///Hlxj/Kcnpc4wVSXxEMnjx+WefPY+y+zLKDgNffvK3f/sq' \
			b'VuLLQd3w7OV/wH/PP/sC/v/4o08pDq+++lgkhqGP+uDf+6BI7OWnr19iwV9+8hn+vvzPF9jS519RUzHLr7iCULGv4i/K7ONP/v7Jx3jHC9Edp/viUxbgy6+iLP/z9csXlODjT/76VzSBV5+QtbygSj9/9TEKDCM+x/s/e/7F668+lypGA6AL/5uFjT8tawGK' \
			b'fPHvEPzwx3cf/nz724c/s/AHCH//9rd3v3/7y2/f/vDdTx9+f/tbFg3Bd//8FWJ+/PPnGH7/7r+/ffvbf8fTD3/8+u63/uQ7CP789vdvv//lJwn99sv/9CEu78O7Dx++T6FfUyhm8/a7FPzxh3+mq7//ngr6r7ff/x7Dv1IBfPmP99/3df6v//q1r1iq/08/' \
			b'puDPf/z07Y8/p0Tv+0TQ4Bj8/d1vP+d5xvD3f/z20//NhBKD3/34/pdBCRBI9fvtbarf2x9+iME/36Wr//zwrm8ZCC01YFA0Siue/PH+x1/eZwroRff+91Sp7/tWgl5zMf35Ngn1/S+puD/yJG/f/zC4/uP3qYzvvv/l55/fptNfUl7fQUv/z7teR8N0v/74' \
			b'7vt36QTs733f5F8//P5LKjnZRGrILz/1raVMBycfsju//enPtz+lCx/4zm92b57tbbsz7mbHAY8B0+B/7U77GzmFMwp1mGyn3W5vbwYX+KyN98ENXbyEQUq1p1J02D1TOxV2e7XTGLhJV+laf2EfMKAa/s8qiOVM46VOH1yyg0sYhFBr+T8LebbcJjjDIIQc' \
			b'/PmdhnOOcRiA3w7upopgAqiowTvam+GleLrXdE+rsW1Gmqa5HniRL0m91O5ZB2JReNH0l7r8tFMSwGuYCcS2OoXoWmd2z/AM9OPUjVzZdyTlruX/LKii0zdyCYOoFFIH3nmTncZwdr3jH1A2NpP+dBOjNQawknKdqw6ikIt8blAiXRKJSVfl2sEF3V+wwwt7' \
			b'RU1TeJnErZXogZNoLJxL9/yfxcqyPcHZHuqI7QFTQ8uRCDiVCG0lO2kflKO5RBBmC/eTOljSdCnkp10jAbyGt6MtQKUNm1U6deNLYhvDy/bwdHTjxOnEpVE+/vB0cNNem6xmfaeQSowuuPGFvB9pLyppdTyHTk2GCKChOqkcFK/YdNLlw0v96V4TEGkQP/YS' \
			b'7JNh56DiUDns+lLWRDTCm1WnpALjGKbaa+oI2CBIl/oHNKglpXeOu30LrTVQRMh6P8al6/0VTVdM018xfKXtr1i+kvLZdwyIHf9n21THdKnLL2EQG9DwfyC+m5s+iGk094R4CwapqxsvXUQIAFVHRg294JnvQRTBhfQB0K0o0Cr+z0HlWoZHbH1L2QZCUAkw' \
			b'MqMKdjqiAzceL/IlOW8kzwY1BCIRCxtcj1fgAjXSiPUZpiY4hw5NaegPZcC3YADla/k/C1LvOP+OgygAiHTYT7lCcOoorw5ai2UKk+06T9YEsCOoRQlaprXJWIBsqh4auo6mqAX4pC+IHXZRCXDxWdZt6dT3lXM7w3biMLMYUjHE/IABHwMxSpE1t5Bfz3V4' \
			b'RhkdXElne4a+1shpjAGBtUxGmv+zmJY1hdbVsT7CjlGh4ZNoph2qiNrbAWBjvn2fCtRaDHn+z5oeJDwFURKG/8seVyKXGc3/0ZOKsJ2mIIZUjLyRUziLEXQJVPjMOdZmF7WJZEP1tfRQpOL92CktR6gYgc9CcgVC8Bj2ptm1QNAtQBz8gOo1wS8oHS0LVOPR' \
			b'gqDrAhyFHYgJxBPggFvgEaCFXtACXrQgphZ6ZQv40oL8gY0UxkLmYIVAsFDjFnJuIWtMCikhvxZKaaGYFoptG7jcwHV4qGjh4Q1YQOE9UCYgUAvCbUH6LYi0hVYAeoLVtmDHLSg0dLugdgECZhfsLkAakGILQm/hObEF6WE18coOH8ZahCsQADyyBb8LkGsD' \
			b'j3SOugnACZTfQPJGo/6gLKgC1AmqhHkpBFuoF0imBdG0CusEsQYf09oG84J2Nd3Ow6F2Xu+82Xm7827n/c5DPOYP4kGA1Wg+0O/BPOFxCR4SAVAAvwDonUJagJ7voMe7nfM7B7e2KAwoLODzBSpMIWX4ZuexTIiHaHyyhuANPqHBOaj4GeoWL9A5RKO04RTV' \
			b'gT8dp0I9YCy27IYolWI5jzf4jEznlHe1iwu0i2eBFdyyJrtGNBuiubAdhJZP205+xS5InXTBya+X35gRKfmGnqfxJ3AGWpL3qSi6Is0VWJRiW1FdNBGxHSe67mxV9XWoGpQrfEHSvolK+YYGqKx94oo+Aq8IhjC3kNyzWCPAoyjjx2pbZnK5mY3Ma2xYYlBj' \
			b'U2ITmjIdNpncTHLjGBnFnEWALaDAmcBBgg1ha7TyaN1szdGOk9Vm1tpbaLRKqF80t8c1tYtTB6qBmZDsGPXTiNkbeeBSwpzaSQIdqbhzFSCvBiDbqsvr0OWzVgmnMUVVnV6+ThFsfVXmdSjzGQmKHzplFIpy4okKetbEuV2ozw4Krzq9DJ2q+FTbaXl80nGG' \
			b'gocPcHcLUmgtCgdFDvli9Y2rKr4IFYMmddXklWjSVE1eiSZt1eQ1aPJZcEKgRmbqlEw7CJ3GCXjT1efgK1E5NZh0zlNMgZ+GsaGs64Yfneos351n+SxN76y5H6tLE7dWnnBtd/espG83DWcpE4lLs1Hxdr/qdh6FPUPT4pVlWTQOFWCuBGDiFDZzxjMTp7jj' \
			b'lLZ4C7TiHtBqMSgj8U1b13YWre00MrHhWeCe+7nncROurGPNsT/gPAfabV3WuR9NeCOKYEv2bOjecwfwYu8RQFtZCjeCy+JkYfgnOuCIMumeXIkkBuxtkSD4Ac5y0ZaLdvyc3kBcM7SBqrSepZmBLMvduSqyoyJzvAzv2IAdm6rzc5KLIFQl2EuQ+7XjgZYL' \
			b'1eiOgauTEWrHtmf5RyZ+fRsnglvcCFLdUq/iUZL8Tjt2OO2qC+mF6hC99tk7uOrwMnWIntyd+AHDb1XWlpVF3tm1p12q8lAjnfjMY1+rarsQtVGnE0FX79rH9a5t6bGxDgGuoWd1vLU/dFWl16JS7aour0WXzHtVl5evS9pmycM86p/1KeZR5zs7GQdoI+MB' \
			b'8cnRrSiJJ8WyTXVQa0ppGknRyMKSnttj+43s4d3RvjC6SVFxVdsP/szKpFgF/lCr5p2TfkU/3Gdowwf3nY46U1XDPatBKYEdBiVeDZP1cnEL4eWe5IlIQ7uqj3vSRxB9tLK+1rIP2zPy7xUNBLlihUEMOxsEXqsJMl6zkhFlWHV0Xq6oMj27TE2V6bkp1nSM' \
			b'AcHzeKJK9K5WGkKV5JmcJoXoLDuM3MWxOr6uSMmjilg9P2Aud5CWJ1Dt2fUBNY6qNwRQ+MY8X/W9Qt8ybPY8au5drFC2XtWHyvuELc+PhnO7i3hm4q5FpR7U8juk8Nmzy/3qqkL6px3e8n4+kced2J5nrTwPrj0Tv5Yym3SGTs+dOD137PTMmEm985kMvtPU' \
			b'lufRucxgWZmmtJbJsGp37NHM0q+vUruWqfk36MlfPa82ryXCogpJky88s2fY7GLl2diGivyTYnauwsTWYQJ3z5AVu7Za8bQVd1Uw04LxtXtvv3vLzJLT1YqnrbjuIti+FeNOOsVbr/AHh4039Bkh/AHdqfiCdyXO6uom+kGr/n3e5HyieOhOdwTOrr6e7UrM' \
			b'RItdiNZbE7WveAKCztiGyLdIZS81ZqcXlb2KkbwyOCP6MZItSEtFrwyVvecP3Qc4Z5rwoIff+vrGSzEe9O3oyLejbnS5GJVh69XcXD7iuoruI524jZAbVQX1y1Jy7ZMXoy50vFLseKXY8UqJ45Waer2bnr5sJi6TB4dcVnwZfyyTs1C15jjNcUae89gnrK5W' \
			b'rxwiGV/fhbVupZkMtq7k35t8VYH9W9mrh1P3/CtTIZ4HAp4Rw3saLNKCsOLZf8IMvruuV14BJVkhIZsGgujEhKuYPFqUB3/mDMeJHNOKY8pxTCuO6cqFfsJB17mjjWsflaB50kfLpI++Ed9ynjPQPGdAP52cQus1DeLpOUL0bbwM+G18ImETMi65c+l5zyJP' \
			b'1oK4oxl3dH2ovQwbYnchXengOpRpuQfyhGBdEjnwTgUjMLJV0zBwGgFOcyOzKgychoHTCHCaG/lKkcHZdGiJ1bXHXEWP8WwRnlXuWcO7Th6b8ZrlKBCcjR8GtNUKrskKnrVWHmigQZZ246nkZmvrPpCzDGip12AHs/R8yY5o0X+8ITHnmwWwvzlBXyeqcTzl' \
			b'zU7L+CJmfAszvoIZXy1c+9n2+xkU5xhsHduCi+p3tZedabO9F/yS9SEj24ut/EZ/AX4bN/VLX2V/FoTzVZLnsWK4IVqxjlbcifUi9FeovwCod7vAGB9Ec+y41OzeNPiATZ8BRR8S/BRoyKyVhcTqCfiG8S4aaxINKxaVw4/aLT18k5xESBolgatiIUp6rpmK' \
			b'GkitmxSVmBkpw/QGIkZFKqAdWq0YkZgLqR5NQLytkgeW4qcV/AoCvs8fvxyBUkVffBQgflsEPyyCXxXBz1xg2fgmIXTkwi804rf98KtwuICIm5RxuyUousOZXhjqdw2KDPSCBg/S7PC1EPgaA9x2j288xVdOgWQ7FG2H+kP5QjpQYYciRhmDkDtECNwQAGbW' \
			b'4Yul8a3S+HZiaGuHb0bClyLhe5DwxeE4R4j+B7jFFzfl4gMa9n/cN4Y9Ft2McecntKfDDWvQpg66hwKDV00LRrEHqYG09y3UZA812kMn3UPue43hZrcPcLnBeAjCJez0e+z1e+zuezCHvaIrGAd57fEq9pI9duo9KmyP3WGPfXqvMAHoaI99Z48deo+9ea8w' \
			b'KchhD3XbY7/dY6fdg9T20Jq9xTBUeQ8GuKeboHPuMUODOVOuCu9UlCEkMngJFLKHhu89FYip4S6HmWOLLOYFFzw2FJJjdbFWnAc1gNqEZRuRANrgHg2Sm2hRZtRASOmxDdgQqjkoeW9QdnDisTTMsMH2QHqw/73DVCRwyIQqD6kDltPiSUshvAnOOhIbpqNq' \
			b'UTxkT5WCbBRVEaUHgYC/kCyQUDA5RuIfahAKB9Pdg7nsAfD2KHtUB0oczGjvqWUkUwihSYAh7R0JE9sLSaG/7qHz7sGy9g7bgjLFLOC676SuLf0HMR1aE8kM7obfgHmjyDym6EhnEOXxZv8NohViVEWoilADhKrwVOFpE/DUITzNwZLNkKkpghM9vfITbj9r' \
			b'mQFV/8h5iFXqrnCFj8r0kBwffs+JXuYQwTaHXGoFejUTCGZ6FMPdmohkuCGmiGYOleCO4JYbIpdbgl2OkisvgXkMc6egmDsnjjmukwoS4hreB5a5CTTbLIi55TDmpoAMayZg5gjOjgLa7l/2FpnU3SKXhuYWGOb/4U6YxShHA1HBOnca3DUR8VS2kHMw4OZh' \
			b'Mg+v2dWSR7/HwbAb4CEIj8fJc+NywcaDmYQIkvljnj0EyzQX4nlWAj98mObUR3MGCVTj7EecCPICsDIBFOcuioCrD6fjCXwhDX67jkAY0uFX2PDzYvRICenwS3ZTwIxfcjwZnEHrgBE9SIPmQSbrwVoJYBsBbbceuPGVwhG88c0rSwAct6AmELcC5I2AOVzD' \
			b'9z4GvBYyYMf+j0o1R7AdE+TgjnNS+LhI39TQ8hcY4zkwjfN4n2Gkj8GI9VSEwD3HSYoI/W32BEtzVgjoaEn0KzxAJ0p+Ix/gnQVCkAqHXU4KuPUNOSFeT/FTHNFXVoWs8k0YtEQkJMzB8jtgj3F5U3/EMFx9YRluro+xrTRFhEPvXYoSO6AgqohQUFblRmRg' \
			b'fbyKpJSqYYifYnCSpkhhpzNVNAjhq6j9law1kBexV2dGFIbZnMphZEJMY7ky56iMsnYpXSQ0vOyt3Nu5TKGK70kUx+TWtbf0ENWZW1K1A7IzOLd6S88szH0Irbf4HAEwektPEIBHt3sevkKERXLUJXI0D86PiwYI98SJ+pAXUR1LuXEw2BhzYuTDyoUXwIWW' \
			b'udAe4UIUpB3RIV9CU7HpRGv+nWFCSaV8CiYmtBkT2izLxIQ2Y8LSQAgjS8QnAyH8HY+FBgVPcl6KVWGQenQQ4xF6i3AT59HFSHulDMbjKb7IudGoqovCHFOb7ZltmCMPs2LzmrytKrVrktTsMlKTAiOpiSLXklqq5Qyj2QWMZntG6wUzS2iWCU3qH/nMMp/J' \
			b'MC3ZNKc/jcxGJDbBXWYNd10ra5lHZKuuMtamGAsRGStxbEUBb2yGjEWJZXqOw5p/p9kKRdYwW8VgZCvKWdiK4yRFZCtKLWxFHDLHVhhZYCuuHtUlshXdwdbYlztFVn2sCoNajo6piT1qh9BU8dYxTfFFlnWkKZbizCQgWts+b4vkbJPUXX4Z32ckjZpiqm7Z' \
			b'RGFshTBVVOJKpuprOc1U1KwTmYq0zEyVSXuOqTpeFYn1F6aimoj4uxRLb75tDpnqyHBrfphlV660XDVP1RHVU+UnXvLGnyI/EQLl5KQyclJCTmqenBTHUts5mMhJZeSk+qMnJ5WRkyqRkyqTkxJyUodDqUHBk+yUYlUYpB4dxWWn4n0H1KSEmlRGTapATURL' \
			b'wyx5CBWb1eRt7NszSUxqGTFJgZGYRIFriSnlMENMagExqZ6Y+nrOEpNiYpL6R2JSTExKiCnaMqcvE5MQ0gQPucpDlYcqD0Ue0sxD+hgP6REP6YyHtPDQvBNDJ7HKp2DiIZ3xUHb0PKQzHtIlHio7aXH1qC6HPJQXPMlDKVaF3aimg5uLPFS674CHtPCQznjo' \
			b'mJ/EKEvhIWlWk7dRpfZM8pBexkNSYOQhUeBaHkq1nOEhvYCHdM9DvWBmeUgzD0n9Iw9p5iEtPBRtmdOv5SGPPEQTgx1tVhA6IS5BFsn5IyA99OBeQvaIqoSiRhDTZ6gnaEdaMxnKBHF2QpTAPTjY0k0c6KYXFpP2E/JeeWjPFVzktZXbN8/tiJmaTL7M7Zgg' \
			b'53b6FW7H/tIxvdPvNL3HVKq/IdI7ZS70znGSItI7pRZ6lyjLhUWSpyz4J1I9hgtUz1Wleh1Q/aASU1Tfx6owSD06ilRfvA+slMXFbK+Y8DmKxe9F3F2SCdK+BOfIf1QIk39saJO3WqUWTpE/28HJ5B8LFPKP6l1J/n0tp8lfLXASJ2Ex+WeCmSN/ytml+gv5' \
			b'U02saCPFtmKPa8m/beootI5CK1NFpuLZUHVsNlSNZkNVNhuqZDZUzc+GYl+R2dAYTDSVzYZynKRINJXNhqrSbKgqz4YqmQ1VE7Ohg4InqSnFqjBIPTrK1FS6bzwKVTIbqrLZUHVsNnSUpRCRNKvJ29i3Z5KIls2GxgIjEYkC1xJRymGGiBbMhqp+NjSr5ywR' \
			b'8WxorH8kIp4NVTIbmmyZ068morYSUSWiSkSRiBwT0bENXWq0o0tlW7o4rPl3hogcxyqfgomIXEZErj96Isr2eWF4nojKe724elSXQyLKC54kohSrwiD16CgTUem+AyJyQkQuIyJ3jIiGWQoRSbOavI0qtWeSiNwyIpICIxGJAtcSUarlDBEt2G9GNiFE1Atm' \
			b'loh421msfyQix0TkhIiiLXP61US0diduJaJKRNdHRJr9F4++EUGPnBd15ryoxXlRzzsvYrcQ58UYjESkM+dFjpMUkYh05ryoS86Luuy8qMV5UTeHRDQoeIqI+lgVBqlHR5GIiveNiUiL66LOXBd1yXURiWiUJRNRbNagjSq1Z4qI9DLHxVigEFFU4Eoi6ms5' \
			b'TUR6geOi7h0XM8HMEZFmx8VYfyEizY6LWhwXky1LHdcS0fLN0pWIKhFdLRHx1Jw+NjWnR1NzOpua0zI1p+en5rA3yNRcDCYiyqbmOE5SJCLKpuZ0aWpOl6fmtEzN6YmpuUHBk0SUYlUYpMYe4H0WX2QiNXtMMJHMzelsbk4fm5sbZSlMJO1q8kb2DZpkomVz' \
			b'c7HAyESiwbVMlHKYYaIFc3O6n5vLBDPLRDw3F+sfmYjn5rTMzSVj5vSrmai4M7kyUWWip8VE7Kqoj7kq6pGros5cFbW4KhbetxRjlU/BxESZq6LOjp6JMldFXXJV1GVXRS2uinrCVXFQ8CQTpVgVBqlHR5mISvcdEJG4KurMVVEfc1UcZSlEJM1q8jaq1J5J' \
			b'IlrmqhgLjEQkClxLRKmWM0S0wFVR966KmWBmiYhdFWP9IxGxq6IWV8Vky5x+NREVtxlXIqpE9LSIyDARmWNEZEZEZDIiMkJEZp6IDMcqn4KJiExGRKY/eiIyGRGZEhGZMhEZISIzQUR5wZNElGJVGKQeHWUiKt13QERGiMhkRGSOEdEwSyEiaVaTt1Gl9kwS' \
			b'kVlGRFFLQkSiwLVElGo5Q0RmARGZnoh6wcwSkWEikvpHIjJMREaIKNoyp19NRHUTcSWiSkSJiCwTkT1GRHZERDYjIitEZOeJyHKs8imYiMhmRGT7oycimxGRLRGRLRORFSKyE0SUFzxJRClWhUHq0VEmotJ9B0RkhYhsRkT2GBENsxQikmY1eRtVas8kEdll' \
			b'RCQFRiISBa4lolTLGSKyC4jI9kTUC2aWiCwTkdQ/EpFlIrJCRFEPnH41EdVdxJWIKhElIgpMROEYEYUREYWMiIIQUZgnorCLH3OIwUREISOi0B89EYWMiEKJiEKZiIIQUZggorzgSSJKsSoMUo+OMhGV7jsgoiBEFDIiCseIaJilEJE0q8nbqFJ7JokoLCMi' \
			b'KTASkShwLRGlWs4QUVhARKEnol4ws0QUmIik/pGIAhNRECKKtszpVxORr0R0z0RUX95+eYRk2GvBHPNaMCOvBZN5LRjxWjDzXgu4HVy8FmIwEpLJvBY4TlJEQjKZ14IpeS2YsteCEa8FM+G1MCh4ipD6WBUGqUdHkZCK940JyYjTgmGnBZaZ7SVZoKVRxkxL' \
			b'sXFN3tK+VVO0ZJa5LsQChZaiGlfSUl/LaVoyC1wXTO+6kAlmjpYMuy7E+gstGXZdMOK6kPTA6VfT0vIXNlRaqrR09bTEK0fm2MqRGa0cmWzlyMjKkZlfOUKYkZWjGEy0lK0ccZykSLSUrRyZ0sqRKa8cGVk5MhMrR4OCJ2kpxaowSD06yrRUuu+AlmTlyPDK' \
			b'EcvM9pIs0dIwY6ElaVyTt1SlVk3S0rL1o6QroSVR41paSrWcoaUF60emXz/KBDNLS7x+FOsfaYnXj4ysHyU9cPq1tNTV1y5UWqq0dEBLvI5kjq0jmdE6ksnWkYysI5n5dSQ0ellHisFES9k6EsdJikRL2TqSKa0jmfI6UvzAoZlYRxoUPElLKVaFQerRUaal' \
			b'0n0HtCTrSIbXkVhmffIiLQ0zFlqSxjV5S1Vq1SQtLVtNigVGWhI1rqWlVMsZWlqwmmT61aRMMLO0xKtJsf6Rlng1ychqUtIDp19NS9t4CcPo3XaXSU6Dt9pVgroSgvJMUP4YQY0+EY7niaC8EJSfJyhJpXwKJoLKvrhrfH/0BOUzguIoy4VN05Qv05QXmvIT' \
			b'NJUXP0lTKVaFQerRUaap0n1gnCZ+uzgylXzLl2osUu6SKMpMNcxbmEra1+SNValhk0zllzGVFBiZSvS5lqlSLWeYyi9gKt8zVS+YWabyzFRS/8hU/I1g1oPr9cDpVzPVNt7SUJmqMtU2mQphGCqBP0WmwgQ5U9mmZyoOa/6dZip85XDDTBWDkakoZ2EqjpMU' \
			b'kakotTCVRFkubJKpMKLAVFxJqtEBUw2Kn2KqPlaFQerRUWSq4n1gnCyonqn4Oovci5S7JIoiU43yZqaK7Rs0VqWGTTEV3X46U8UChamiPlcyVV/LaaYiSziRqcg4mKkywcwxFeXsUv2FqagmVvTgej1IHdcy1TZe41CZqjLVRpmqZaZqjzFVO2KqNmOqVpiq' \
			b'nWcquUP5FExM1WZM1fZHz1RtxlQcZbmwaaZqy0zVClO1E0yVFz/JVClWhUHq0VFmqtJ9yFTtiKlaYaqWmaoVpooiLTHVMG9hKmlfkzdWpYZNMlW7jKmkwMhUos+1TJVqOcNU7QKmanum6gUzy1QtM5XUPzJVy0zVClNFPXD61UxVX/NQfcmvlpfwGzz4/Vb8' \
			b'htLyeb+O5/26Y/N+3Wjer+s5ihGVZv66WZbCDtAxS8Vgmvnrspm/rj+QpdASKXGc+OtKK1NdkZ72aWmqO+QnNsn+b3reL1VNhUFVR0d53q9038E3quLHErF3xQ9WUP2K5IQpOEtOmz45T5f5m/OuP1UpOD3t1y2iKCmYvvEQz9Z/qoq+c+iz9h/M+3UL5v06' \
			b'4iixqiSe2Ym/jif+KGlH5gJpsinAjqcAO6arZON854iuNH65F1oUv+Srwy0+cwAm3RKdA5DcIg0DENzS17QyAtvMV+g3/HWmNV+kRz1A69d9pany3MbHX+yibo+5qIMQ7chL3WZe6la81O28lzoavnipx2AagmVe6hwnKdIQLPNSlyjLhUWOoyz4Jw3Eyh7r' \
			b'VjzW7YTH+qASkwOxFKvCIPXomCK54HueK97a0G/IlrioeSLthjXgRehdkkx5RDYsQUZk0tAmb3XfwskR2TLv9VhgHJGJeteOyFIOMyOyBd7rtvdezwQzOyJj7/VY/zgiY+91K97rSQ+cfvWIbBuvmbgjm2kiNLuhMdrqLw5WLlvOZd1CPvMjTnNrP6HBzoTq' \
			b'mDOhGjkTqsyZUIkzoZp3JsQOJc6EMZg+oZE5E3KcpEif0MicCSXKcmGR1CgL/kmf0yg7FioZvSl2LGwNE1vL/mFMboPKTH5WI8WqMEg9OoojuOJ9+OlB29MaNVDk3bAOvIi9628qfmJjmD3TWmxik7dXpbZN0Zpa5mYYC4yf2BAFr6S1vpYzn9hY4GaIHdT2' \
			b'+4Uz4cx+ddiJ8ZHusKepzOVQscuhEpfDpBMW2WqK28YLLDY8YKvktmFye9CBmuOBmju2UOZGozTXExqHNf/OjNIcxyqfgmmU5rJRmuuPfpTmekKTKMuFpVGa41Gay0ZprjxKc0xo+HswSssrMTlKS7EqDFKPjvJyWek+HKK5nsioYSLnhmXvRdxdkkl5fDbM' \
			b'XsZn0sQmb69KbZscn7lFRBYLjOMzUeza8Vmq5cz4zC0Yn7l+fNYLZnZ85nh8JvWP4zPH4zPH5JX0wOlXk9c2XnpRyWtb5NVcEIG1D/1hQ8OjMnNsVGZGozLTk1hcR6PfmVGZ4VjlUzCNykw2KjP90Y/KTE9iEmW5sDQqMzwqM9mozJRHZYZJDH8PPnKYV2Jy' \
			b'NJZiVRikHh3l0VjpPhyNmZ7EqGEi54Zl70XcXZJJeTQ2zF5GY9LEJm+vSm2bHI2ZU0is46UlGZFFDcqITJS7dkSWajozIjMLRmSGpjfSiKwX0OyHDw2PxqQNcSRmeCRmmMySPjj9ajLbxqsyKplti8wuhcgedCTG28DssW1gdrQNzGbbwKxsA7Pz28CspFI+' \
			b'BdNILNsGZn1/9COxbBuYRFkuLI3EPI/EfDYSK28Gs7IZzE5sBhtUYnIklmJVGKQeHeWRWOk+HInlK2WeR2KyH8zyfjAr+8GSbEsjsWH2MhKTJjZ5e1Vq2+RIbNl+sFhgHImJYteOxFItZ0ZiC/aDZeSVCWZ2JMb7wWL940iM94NZ2Q+W9MDp15KX2sYLNSp5' \
			b'VfLaPHkFJq9wjLzCiLxCRl5ByCvMk1fgWOVTMJFXyMgr9EdPXiEjL46yXFgir8DkFTLyCmXyCkJeYYK88kpMkleKVWGQenSUyat0H5JXyMgrMHkFIa/A5BWEvKJsS+Q1zF7IS5rY5O1VqW2T5BWWkZcUGMlLFLuWvFItZ8grLCCvfi0sE8wseQUmL6l/JK/A' \
			b'5BWEvKIeOP1q8trkazcqeVXy2hx5Od4s5o5tFnOjzWIu2yzmZLOYm98s5uQO5VMwkpfLNotxnKSI5OWyzWISZbmwSF6UBf9E8nLlLWNOtoy5iS1jg0pMkVcfq8Ig9egoklfxPjBRl20Zo4aJnBtO4kXcXZJJkbxG2TN5xSY2eXtVatsUebllu8ZigUJeUbEr' \
			b'yauv5TR5uQW7xly/aywTzBx5Od41Fusv5OV415iTXWNJD5x+NXlt400cd9g1tsmdYiUyikQUSSgSUCSeSyCdiyEc3vnlju38cqOdXy7b+cVhzb8zhNNxrPIpmAgn2/fFcZIiEU628cuVNn658sYvrh7V5YBkpoklVUWFQdVGR5lYSveN93nxRZYufUWkSCIx' \
			b'E6EP3tHleCeXm9vF5Zbt4oqFRMoQ1ayljNR0oowBWyzYv+W6ni34zq7k9+d4/1ase6QL3rXlZNdWslBOv4QuiCa28RqMShOVJu6FJjTThD5GE3pEEzqjCS00oedpQmKVT8FEEzqjiezoaUJnNKFLNKHLNKGFJvSpNJGqosKgaqOjTBOl+w5oQgtN6FNoImYi' \
			b'NKGZJjTThJ6jCb2MJqSQSBOimrU0kZp+SBN6AU3oniY4uzJNaKYJqXukCc00oYUmooVy+sU0cfHvoKg0UWliniZ4T5I7tifJjfYkuWxPkpM9SW5+TxJutpM9STGYaCLbk8RxkiLRRLYnydkSTZT3ITnZh+TsqTSRqqLCoGqjo0wTpfsOaEJ2Gzl7Ck3ETIQm' \
			b'eFuR4w1Fbm43kVu2mygWEmlCVLOWJlLTD2liwUYiUrTQBGdXpgneQRTrHmmCdw852T2ULJTTL6aJ4pseLoEmtrBKUl9VdC2rIryk744t6bvRkr7LlvSdLOm7+SV9FzhW+RRMtJIt6bvQHz2tZEv6LpRopbyM72QZ300s4w8KnqSYFKvCIPXoKFNM6b4DipEF' \
			b'fBd26bO37tjS/ShLIRxpVpO3UaX2TJLPsqX7WGAkH1HgWvJJtZxZ/ViwdO/6pftMMLMExEv3sf6RgHjp3snSfbJlTr969WMbb2ioRFSJaAtEhAAGlcCfIhFhgpyI8DwSEYc1/04TERpsw0QUg5GIKGchIo6TFJGIKLUQEeHtHBFhZIGIuHpUlwMiGhQ8RUR9' \
			b'rAqD1KOjSETF+8ZExBdZ0pGIWIYFIhplyUQUmzVoo0rtmSIiuv10IooFChFFBa4kor6W00REbT2RiMgmmIgywcwREeXsUv2FiKgmIvwuxSIRUcxaItrGexQqEVUi2gQRsZ+YP+Yn5kd+Yj7zE/PiJ+bn/cS83KF8CiYiyvzEOE5SJCLK/MR8WyKism+YF98w' \
			b'P+EbNih4kohSrAqD1KOjTESl+w6ISLzCfJsR0TF/sFGWQkTSrCZvo0rtmSSiZf5gscBIRKLAtUSUajlDRAv8wXzvD5YJZpaI2B8s1j8SEfuDefEHS7bM6VcT0TbeiVCJqBLRJoiI/cf8Mf8xP/If85n/mBf/MT/vP4amKv5jMZiIKPMf4zhJkYgo8x/zJf8x' \
			b'X/Yf8+I/5if8xwYFTxJRilVhkHp0lImodN8BEYkvme8yIuqOEdEwSyEiaVaTt1Gl9kwS0TIvs1hgJCJR4FoiSrWcIaIFrma+dzXLBDNLROxpFusfiYg9zbx4miVb5vSriYjeZwA8sIk3gm+MjybfAg7xKI1Nc1Ozgp/cBXJU89Dv5UEHNuisiKkIrvrYFB7e' \
			b'PXJmU5kz2z597ULNu7NRoeKokMLpPT2ZQ5vKjv49PZlDmyo5tKmyQ1v64IWa8GgblDz5ch6sN1aV32yg9OwxRV0h9OzFqdBU8RVSM1mMWUyJq5vSPYupY74MoyyZxWIbm7zBKob0HJOpoiMcvmDqgM1iwfENPaLWlWxGDWVBzLyiZ4FLHPbR7H1zUrWiv4Ni' \
			b't7jYCuE0xW5xStziYpMVp884DUs0txRP/9MVIDf43wf8P1AYCY4q18IP0hsY7psSuSVayzltRGgmkhgzGLGWUNYhX82R1bzvG/PS7FjogEvsCd5qkSs65oU5Pjh5rBLxfy3u6wkPtBNxPuJ7CdcR0xOWO8Fwl48vwgLMHqD1BFTP4TQBdI/MCZYTFCccngfh' \
			b'kxD4NE+xiLXFscAhVBJOHnf0SoCIUIgIOI99Sx7hE9ytBrp9+qh3jm4nQ1vEtDKa7fO3ZiKCEXwRcEXUQvBpy+BjN4E/6dEYjbHC0Nzjpi1A0akwtOzZkR70rgSLsme/NhyZKK+YNMKkLvv2ygQuLcOk7sQHomYxJvUj+TPDUleAJb0SmswFwZM5EaLcaRDl' \
			b'1HlhagBROvPBPwdM6czR/hGgSpWhqqPevxaudOYpfzmQ1dF3iE+CLX0ibKE5ngBd6u5jOfVwj1PD2cW5la61+HUidnmMQ8GgMTePjGULZvfOMuq7C44twLA4N7fNxy2qXv5XwrM2PMzjFz1OI1+B/DqzEWzTC3b7zONa5xYNE3f/Apu+hebQbJU+y2yVXYJw' \
			b'hQWWkx7O5oBtahlEP71xYwKyqaWJfFkCPyzVZssTaElWAE73IOc9fTuYwQ7SQts7aDsvVfh8uQL+uocDQQLAwcrEOhDELO4JCMvAFyaADy3giY89E9ChYuYf4hDPaUWNl67ZEizb7Z7stO1RMK6vERp29N1WS+nlFcf7lmwDpcooiSeOHgHNA0/n3xM6VmQU' \
			b'6n/gGbXHnE17JGSbQrXmqaMaGtjZZtTs7s2WlhcLjjAPsdS4JTRqH2GpMUMiNp3NAdEqECI/JPI7MuRjtIklx00CUUcCeYwlx92/wi2wH40k3bZAaRkQQbXQQwcbeH2gtASQ0MftPAuPm388emDHB/ZrxGqb64ekZc9GLJUzPiD5i8Yi+O3w12wIk/Qj4xL8' \
			b'mrviUz9xNZ6wqlg1xipEHHK/3qNdbQ+z7OPD1h79UbGUO6JXRzOBaSpqPAEVzopl6uHhTD8MlC3aCpdvL3iMmSh/+Y9aLYLApjGMZnjbB0Uw2y2DsYRhaO6PNzd1DhgbP4RBO88JXPrhgSsDLajc4z+DPTJoVcC6b8/4AVihjjf1yLUJrLoHnGrPilPmcXEq' \
			b'VJyqOPWwOEU4UnHq3nGqOytO2UfFKahWxamKUw+LU23FqYfAKXXJk++bAaUtbXzeOBBtGoPuA3A6KvHSlvnOAjC7f0GXukXERacDaFHFmuvCmpWeT9eANzRF/ThwQ0Vfl1fBGZ2cnLslLoDed4vATNBjKvRU6Lke6AmPBz2hQs8y6NmY/3eFngo9d4AeRJpH' \
			b'gh4sqULPEujZgpf3ya9hXYNELnth6qUh0vjlpudEpUaQ6YmgE3XT9HDU8Y4UeoNu/3d2xOJCqUn26FNTt2HoOnjX55nxq5NP+HCN1uDYFjzEK45VHLt/HFMZjinBMTX4uwccU6fjmHrSONYKjqmVOHZe7/CKYxeDY08Kw3SGYVowbPh3DximT8cw/YQxjPFL' \
			b'r8Mve14n8TqVVaeyzg9QjB6X7DDw+Cj02JNZ+Mo70xHknNffu0JOhZylkMPd+7p9lM4IOfyVK/67IMgx7e2eukKHzz3YRW731EXQf8kQFJ3XpbtCUYWi5VB0/e6SZ4Wi/u+6oKh6bV85FOFGb89TjluFJQKQi3Hi5to+MCpRoXcdkknN14IS3X4UlDp6iQlE' \
			b'HYcnjRNCBj9ZGm4R66E/3RL8Qqe4RQQFA4dfHr5Vl+8rB6rNgpO6KHBSjwFO6hzgdKcnJr7pzk9MiyCpuoJXSHpASKLu9uQ2vS2CpGucwtY4eENrb3A019H3W2x1Ba/Qc//Qw7nc1/r+xUMPieeaV89UuCX2gV6EAdp7a7fgCl6h56qgh++re/1PxB4R15Uv' \
			b'3St43MEp9wAjMMWT1Vvw3q7Qc9nQw6kff//bRSLP03Aa6shR0RPkbMHRukLOZUAOdb4NOlJfBuSw9J4m4rQ40MIe63G6uaUvK7nqI12hpwA9aPVb38JxGcjzpB92yBeopYcdV12kK+KUEMdUxKmIc1bEqZ7QFXES4pB5P4hTT4WcJwY5DS6dE+JctMMzVC59' \
			b'J/LR0Qd69ma+D1lfYX1uKEId7zH9tkAJDrsBaILLpgRQi16dD5m+Iatv0BLRYDoTKMLs3kDJHi0UlQN/dNnml/GdBS1ddrs3HVS6cxoiOod27765gfCzPYzsMHNKt4eHrmaHuPgGYYBKArm+QZwAte9AGKBVsDLQFtQFrNEDWtodGCtINCCkQDeSD5D3BSJk' \
			b'QRYNrk/iMgv6RwBsIKqi8xp0DwQZBB3EWcgF32iOXhTYIUHGHbQW/qg2+s610bsT/lFZBstypdKgsoGeTo4XaxC+zcG/FnoEg606jKVa2NlaNPT1Tk2fmLJTldIH9cKPYvb4jH3Zc12hgw7rC9w0+MdfRHeDv0E8dPo8taM7EIPpk6YGr+LLliieGuYeoWEA' \
			b'8ha/rwoNhPzO8A8/IIwfDcYG+ZUN6ubaBKDTgv23YP8tYMxsG7UptBPKOPoPqX54hUk2CKnqYZwdpKa2h7zt+IDkjkgAYBiEgI893fANQYdiMUPJoDN7y74OSL1IAPQWEVxnUUo2Blt6SQO5KOHL+YA8k0Tx9SRQLksW0jstEnbzUoYy+HHETEi87aUO97Pk' \
			b'4TrUuwtRC/iclo74Vz5Gicd/szccFLP076CSo+B0yXM1mG0MMRZy4RZ7DT1TP+LBsmkHvQrsDKv9AN2rsSu6WLOFbtbt+iMfK3X3fOB46IR0OIa557qw5XQVj8uGonZP6WCjUNuEWr171INlo+/UYdwj9Bmcsnn4fuN26w+cbLrL/Y9XBtuIqaBaNg6/e0oH' \
			b'G8Xa8fmc5s+HqziTcoeDpnzveLCIXO03xX6DT/ZP6GCjGMyWHLWIk7oOKv9s3YdWIOTAWf38fN2Biyer7mSBDadYTh4GGrUzZmf8Dlp5z51KQRzuQkmdq5FPI0Aa3Dpv7BY6m9mlAwe6+Xnh4BW1/u/E2xYdw7wlRD8K/9p7KTQ7eA2gqWhdNiC7e0oHG0W7' \
			b'dbT2u20cLK47Tb+cv9+cKuZi3zjaL8IuHbjcnZ8XDlwsPzHp3Y/TC2M9qoqFRZ2j+8sTOtgo9P1gISr/bHiITknnPtDhZ9WdLLY6e3KkL/ndUzrYKOz99SVU/vn6U9jdx4H+c6vuZOnViZVyl0JfzCd0sFHc08RKrvyzdSv0lL2fA71RV93JQqz+LEd6lts9' \
			b'pYM9IZulPWv1YG7RoK0wWOs7mt8tOtDXdNEN5O0NdH4klZmNYxG3G+532Wzmo/c/3FmwmQM/bEc/4b6LYiPpHqwf5vZw9j6JW0Pu+cj3W9whHxb7mskQXn14iHWHTfZSvVt6cGPaxfedcuAum/vId/5gw1k2YSKIflYIP1PXnVe0251+4BadRTccHnHf1Mq7' \
			b'Pf/0G53glFW1ZpJmIyuMj9/bw27dwU1SK+8+euDGunvKeuZgW1o2t3OJ3R63cl7qwTpaM4NU+7toX+/qYYXjl806XWRnN7uLPVhHaya1amcX7dtdPSx7g+hlE2H30dnXODas6fRo7w9+oKWeJxEdrLM7zaxdqEsKvk/jSg5W4lP0K8I3olzJwUqsTkVHFO52' \
			b'qw9+kU3/d5e8DjI9OBsFF2Q3E8cGcre9aE/AQPzuKR1sFNV9qmwU+L6sJ3SwUdhqFGWj0LundLBRVK+wI0Zhdk/pYKPw1SjKRmF3T+lgo6hebkeMwu2e0sFvvWt2bzS9ElC2b5s2Xuh4KglU8wY3JTaKLuK2RH4cMTCyzQ2mpVcJ4vss8S2H9N1I3Mgovl5G' \
			b'T6cGpQ7/OLU5SI2KpjvwfXPDv87IXfkLETWairzaz9H10Xs7KIVFY+goved3paIZkukpMjc0J7wO5sJ5AbQOckmm67L7NN9rqSb0xtX+bav0hlN6s6m81TS90VThG0q5lIA1Qh87RZuT8d16rDCw5sHbHSE/eRIAG4fzhq6yLm2HW+Us7dbifKEq6Qpo8Zub' \
			b'/w+Z5rWf'

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
	def expr_sum_2         (self, expr_diffp):                                                                 return expr_diffp

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

	def expr_pow_1         (self, expr_diffp, expr_super):                             return AST ('^', expr_diffp, expr_super, is_pypow = expr_super.is_dblstar)
	def expr_pow_2         (self, expr_fact):                                          return expr_fact

	def expr_fact_1        (self, expr_diffp, EXCL):                                   return AST ('!', expr_diffp)
	def expr_fact_2        (self, expr_attr):                                          return expr_attr

	def expr_attr_1        (self, expr_diffp, ATTR, expr_pcommas):                     return AST ('.', expr_diffp, (ATTR.grp [0] or ATTR.grp [1]).replace ('\\', ''), expr_pcommas.comma if expr_pcommas.is_comma else (expr_pcommas,))
	def expr_attr_2        (self, expr_diffp, ATTR):                                   return AST ('.', expr_diffp, (ATTR.grp [0] or ATTR.grp [1]).replace ('\\', ''))
	def expr_attr_3        (self, expr_idx):                                           return expr_idx

	def expr_idx_1         (self, expr_diffp, expr_bcommas):                           return AST ('-idx', expr_diffp, expr_bcommas.comma if expr_bcommas.is_comma else (expr_bcommas,)) # _expr_idx (expr_diffp, expr_bcommas)
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
	def expr_neg_arg_2     (self, expr_diffp):                                         return expr_diffp

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

	a = p.parse (r"\int**y(x)(0) z dz")

	print (a)

	# a = sym.ast2spt (a)
	# print (a)
