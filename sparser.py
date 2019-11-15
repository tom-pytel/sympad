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

	if tail.is_ufunc: # ufunc ('f', ()) * (x) -> ufunc ('f', (x,)), ufunc ('f', (x,)) * (0) -> ufunc ('f', (0,)), ...
		if arg.is_paren:
			if tail.is_from_Function:
				ast = wrapa (AST ('-ufunc', tail.ufunc, (arg.paren.comma if arg.paren.is_comma else (arg.paren,)), tail.kw))

			else:
				ast2 = tail.apply_argskw (arg.paren.as_ufunc_argskw)

				if ast2:
					ast = wrapa (ast2)

	elif tail.is_diff: # {d/dx u (x, t)} * (0, t) -> \. d/dx u (x, t) |_{x = 0}, {d/dx u (x, t)} * (0, 0) -> \. d/dx u (x, 0) |_{x = 0}
		diff  = tail.diff._strip_paren (1)
		ufunc = _SP_USER_VARS.get (diff.var, diff)

		if arg.is_paren and ufunc.is_ufunc_applied and ufunc.can_apply_argskw (arg.paren.as_ufunc_argskw):
			diff = AST ('-diff', diff, tail.d, tail.dvs)
			ast  = wrapa (AST ('-subs', diff, tuple (filter (lambda va: va [1] != va [0], zip (ufunc.vars, arg.paren.comma if arg.paren.is_comma else (arg.paren,))))))

	elif tail.is_diffp: # f (x)' * (0) -> \. f (x) |_{x = 0}
		diffp = _SP_USER_VARS.get (tail.diffp.var, tail.diffp)

		if arg.is_paren and diffp.is_ufunc_applied and diffp.can_apply_argskw (arg.paren.as_ufunc_argskw): # more general than necessary since diffp only valid for ufuncs of one variable
			ast = wrapa (AST ('-subs', tail, tuple (filter (lambda va: va [1] != va [0], zip (diffp.vars, arg.paren.comma if arg.paren.is_comma else (arg.paren,))))))

	if arg.is_brack: # x *imp* [y] -> x [y] ... reapply if removed by _ast_func_reorder
		if not arg.brack:
			raise SyntaxError ('missing index')

		ast = wrapa (AST ('-idx', tail, arg.brack))

	if ast:
		return wrapt (ast)

	return AST.flatcat ('*', lhs, rhs)

def _expr_idx (obj, idx):
	tail, wrap = _ast_tail_mul_wrap (obj)

	return wrap (AST ('-idx', tail, idx.comma if idx.is_comma else (idx,)))

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

def _expr_term (var, rhs): # user_func *imp* (...) -> user_func (...)
	ast        = None
	arg, wrapa = _ast_func_reorder (rhs)

	if var.var in _SP_USER_FUNCS: # or arg.strip_paren.is_comma:
		if arg.is_paren:
			ast = wrapa (AST ('-func', var.var, _ast_func_tuple_args (arg), src = AST ('*', (var, arg))))
		elif var.var not in {'beta', 'Lambda'}: # special case beta and Lambda reject if they don't have two parenthesized args
			ast = wrapa (AST ('-func', var.var, (arg,), src = AST ('*', (var, arg))))

	elif arg.is_paren and var.is_var_nonconst and not var.is_diff_or_part and arg.paren.as_ufunc_argskw: # f (vars[, kws]) -> ('-ufunc', 'f', (vars)[, kws]) ... implicit undefined function
		ufunc = _SP_USER_VARS.get (var.var, AST.Null)

		if ufunc.op is None:
			ast = wrapa (AST ('-ufunc', var.var, *arg.paren.as_ufunc_argskw))

		elif ufunc.is_ufunc:
			if ufunc.is_ufunc_unapplied:
				ast2 = wrapa (ufunc.apply_argskw (arg.paren.as_ufunc_argskw))

				if ast2:
					ast = ast2

			elif ufunc.can_apply_argskw (arg.paren.as_ufunc_argskw):
				ast = wrapa (AST ('-subs', var, tuple (filter (lambda va: va [1] != va [0], zip (ufunc.vars, arg.paren.comma if arg.paren.is_comma else (arg.paren,))))))

	if ast:
		return ast

	raise SyntaxError ('invalid function')

def _expr_num (NUM):
	num = NUM.grp [1] or (NUM.grp [0] if NUM.text [0] != '.' else f'0{NUM.grp [0]}')

	if not NUM.grp [2]:
		return AST ('#', num)

	g2  = NUM.grp [2].replace ('{', '').replace ('}', '')

	if g2 [1] in {'-', '+'}:
		return AST ('#', f'{num}{g2.lower ()}')
	else:
		return AST ('#', f'{num}{g2 [0].lower ()}+{g2 [1:]}')

def _expr_var (VAR):
	if VAR.grp [0]:
		var = 'partial' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_'))
	elif VAR.grp [1]:
		var = 'd' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_'))
	else:
		var = AST.Var.ANY2PY.get (VAR.grp [3].replace (' ', ''), VAR.grp [3].replace ('\\_', '_'))

	return AST ('@', f'{var}{VAR.grp [4]}' if VAR.grp [4] else var, text = VAR.text) # include original 'text' for check to prevent \lambda from creating lambda functions

#...............................................................................................
class Parser (lalr1.LALR1):
	def __init__ (self):
		self.TOKENS_LONG.update ([(v, self.TOKENS [v]) for v in self.TOKENS_QUICK])

		lalr1.LALR1.__init__ (self)

	def set_quick (self, state = True):
		self.TOKENS.update (self.TOKENS_QUICK if state else self.TOKENS_LONG)
		self.set_tokens (self.TOKENS)

	_PARSER_TABLES = \
			b'eJztfWuP5Day5Z9ZYKqATEAiKVGqb+12e65x7bavH7N30DCMtt0zMNYvdNveWQzuf9+IOMGHMqVMpZRVldlFFCtFiQ8xIsg4fASpm1d/+fL5Z5989vIvm7/8rze//ECXcPvJi4++osvnz7548fIT8nz0xbPneqn1auj6wccvP/s0XOvgMZrBh59xHl9+8uzL' \
			b'/4D3pfx+8OKv3z5/9uWLL9X/6bPw9IPk/Vvyfg6v5PMBvfg/uUDRI4+ff/3FJ3/nu+j5+qOvXz7//O/BxxG/+oJ/v/4gJIL3xaeff/X3L1/wGz79+OXXXKi/PeOYL79myj5++dVfmZyPP5XE8vtfX3DsT4RPn3GovuEDSff8s08/fRZ4xw+++Piv//FVKNsX' \
			b'oexfDMrOdy/+i36effo5/X74wScSxk9ffqgcYt8Hyfu35FUOvfjkyxf84i8+/pSvH378t48/ZM9zFcRXUr7PPxEiieRA739/+eK5RPjw448+Yo69/FgqwXMpy7OXHzIfOOAzTv/ps8+//OozDvhKOPriv59/okXGC54T4V+Fa61FDAKXlP8brOdLDZlQ0uf/' \
			b'Sd53f3z37s/Xb9/9mfnfkf/712/f/P7tr2+//eG7n979/vptFkzeN//6jUJ+/PPn4P/lzT+/ff32n+H23R+/vXmbbr4j78+vf//2+19/Ut/bX/9v8uF97968e/d99P0WfSGb199F748//Cs+/f33+KJ/vP7+9+D/TV6Ax3/88n0q8z/+8VsqWCz/Tz9G789/' \
			b'/PTtjz//llGZJ44Ep7Q//vL7PzM+BO/vb97GKH++fptnT55w+0deutc//BC83//x9qf/F26++/7Xn39+Hcn/17s3idDv3r7+/v+8ibfv8kL++SZm/ccvP/76SyzD6xj/+0SpsDsS8mvK8o/E+de/xBJ+9+Mvv0YCf01CoPJEIQzL/duPb75/E2+ogmUF+u3d' \
			b'77/Gl0Shx6L9+lMqvWQ6uHmXpfz2pz9f/xQfvEPKbzavbrZNv/HV7Qaemj2u459+47pbvaU7iVHRT7txfrNtbwcPELEP6TYUEh6xV2JtvTzxmxu7sfTcbpwhz218Ks/Sg62803T4aShTi0zDI9PvPWoGj9hLvrrBT+s22xpFpTv2ko9evO02jooHaj17ODml' \
			b'loI0+Gkpu7q+HT4Kt1vXSpqWaTOV0ubcbXiqz/Cgdpsbzq3l//ikz+/qSj38jPMgn0k+KXlNNHMMYre3t/pka5Cyx09r6QlKTXfsZamJOIjA5ja7Df7sucFlKy928u+qEOzYQ1erz29xs3X6ELSLtE0dONLEp/ps74FND8zwwdZIhbDENouqVOOnAVvJt3VS' \
			b'ZOvx01DZGwic7rZWBNtw1n0MaGKAc/hptQYya4XC2mxuuL6wNFSC9KTN77xe+RGnpXDLL4dA4+3eo1Avhs/b/dudlH7/diTGTrbd/u0g0dbZrGipSWghdh743Qd5KyKf/HCl1Xtq0iII4rI1Wjh6vUGC+Hj/UbrdWtQAqtyWahXXj3rj6TkVjmqeRVUZC2bl' \
			b'RhpkRiyqGsNYWyctihUMtScfqj83YAkgEaLRs05p6g0rwNT2KTA+T09aeaI6Up54PKnTkw5PTHiyNajbFX6aNhUyPPL5I/ayr8MP8e/2NnnZZ9EQQhKmWlp602oLUSXPshPFQaW8qW1SovS+GhJpNhYxLH5abh1glCSQdtSLBlWPEFPXzDsXtIMqKnqIR3pf' \
			b'aZ6siTaNDXVs8Dw8oQdS3yx+qD7d6j01aIkj/8xOJGEPM9jip+UHqpSseJkDVBN9I4XWWy+MIjne1EG3UVUhTc/1SSrabYxgAGujoaSypXhch1yojNxY7Aalj+JhxQsp0MMbXyXx8G2dCtdsPCqK4Z86CV4yj75GfSZ62uDxwQMgpIbCrFDwk1sn5dx9lG4p' \
			b'tfhq/LTcilWP1+JF0QDPRPVN3Wf4yGwwIizT4KetohowUBBMqcVP1h2xilWNwY/0RPDixoiXfXUIvNVbugsBeERtxnsRB71ZpSUdEPa00umpQ3ouWyt8besQwH0dfUI+6ma9IvVApNeUJV1I3ztRsFzpqW74DbVKqiEkYwKxfkPcoAbfk6MkVH9qquU11Zaa' \
			b'WlxNiqHmHgJ3aIS1hPEt39MrqDISUKJrRCqAo1NselQbvlLOFfkrehm91W242bab3mx6u+ndpm82Pd1SDCpa7fhKKRouOr2fJMwio9IQn+qGaw5XaYpG9FJEiscBFNOxKuTiEnm14wf0hAjuu03PRaAM6c01vbom0muivSbia6K+JvLrilJUnIKeV5SvYRwn' \
			b'JVRXHGg2HTm76dymazZdu+n8pus2HWXAFFMRqRZQCyWtQEqI9DV13Fru4lLnlloGdZVY2VNr9u2GZOyp80RJieM1sZz0P4mThUQanV5QbTp+J4VTMPeWyXvLTZruSaw3LE9+IPcUzITSLdEqF4NYzAIOZWJvBSglFHm84n6v3EvepS5cSV246SHUGtJj/Bdp' \
			b'9qGKQPZ9jdva6FXrgohQHni9dnoNGYlg6UmvVUzrlEZPseR50SjXWYte3bRSQQY8zrgLro7xE3wE/8b5tsOrgxwCZ6i+tg71szWXVazYbLQ9ea3/RtrDo5bNViib6R69KAbKCLqEuAXuFOVwrcoBtb3I7zrld1Nb7SQ0VZHj9cqRFWlXBHi9ArypTeitV+gv' \
			b'BHYKIyPblF2BUTlPMh4onRdDX1bV9qvXpfTgmPUY4XBsjHulT8fTf8SpDRW7tKDLbUFWxwVWh63MJ3TA26IZr1eur256aYV1Q8VuqHgN84dI4dLRa2t6b5HeBUvPFeldsfSaIr0rll5bpHet0rvpvQ4IwoQ6MwYz6q4vPZorlmzdVGH2Ewsowgtei7GYO7ZG' \
			b'wxtdk7HapdXYWg+cLtOV2nDNtaHRlVldbushVCYKjb1C97eM6ZeN6WWJOxQST0JrQs/UdYNQ22iTE3EU7h5azKnVjECan1yDvlLIUkOC2mm407WxSjWZajBukpiFRvomaLhGx/JVXYRxtKp3YF6H6t2hdvOiPE+AsI7l6SyeJSmThudrAl2Dmtuhpnao+F0H' \
			b'PO96bQcB8BXgG3Tlbpqwlo121CKTFpl49N4rCquGEnzSLCduQWu0YK73hU2jbPJQuh5VzkM7+G6KW0FVPHWuQX16IJTvS+UaZ5MiP4zLMsZgMRJVrwmd2Bb3wRYxDGR1+NNJqJSOdWboD5uat3cUY9SrHdqItamBmakphqNXJDcqr4EdcJHb9ciN7bSNWvzS' \
			b'tQjo0gQkttelRV2TwFgKRq3guU0VUV2wqKRxKWOL/dTDz7XW0t0r3fVrbUG99NN5I08R4xWL0fkiv2uWH3CsyO865ScbHmUY1mIC62LweWSfJm9cMzpoFK1R+k0PLxcDzj/qtrwOoxwUhXd18aWp9KmGVl6rii7nTu///Ub3F/NckrSGUpMeYp+nhXywhKEr' \
			b'GLoSqQvsWDmLhmQtal6Ryf21LMwf9CoaMcYUIy41fYi2DnUwdgiLw3WjzQuT6D1Ou+pbzchIjkVm92LXEiZSG1GEhblnnSaQilv4uN60rfDxLHxsCh/PwUeHXqLoThludBhQFG4uGqz1hXvLAbyyGLHA8iCMVGD8azJzYLEClhhWB+2NXKmXxh20wuxZzK7B' \
			b'us6gszSwBeps6UGd3dI31NnRbSE1BuKXWPSbGpuxuRNocsu6Jy7QGicNXGLhbuqwsb7DSLbDFFEHdHcdyl/FOzZu5ghtmAXFHEMRtBhCgnnlSIJrnuF/xab5xcDqIiUjeqaom3iiTTvYb9J2qpP7opOTKbsvjfkSGzNvYJHa6utSW1NtNYUZiRldabqX2XR1' \
			b'ucu7UltTbS1m+ZdZW2tsmOD9alJrjdpB7swVdlUwj6z1iH2LzU184dHbrXwmgi8kZBsOUbdqPm5vg5WyTedDy9SkRO2RTznt7IorEpFsYQJjcQQ+ZI+nbR0EzxejccIVgY0mIXFYNZ6x2WGGbOGB51ITpeNajqW85CrBJjcyG1Z2j1y2mJgzNjtmi+foVB/b' \
			b'YLhj1GBH7G6KMr54kWImuojoUkXEpm0Wpm0Wpm02mLbZ/Fg05psN9lj2wMoX0u0doeXGHzcjj9mKwcKKQQMtAgHDeEHToDiw5StrxSeMgYLZYznRad6JTrasnZ+Zp3Zag8jSOVbW1W4kWFR36Ax06Kx3nQzmZNnT4twm0Qetdu1bsYDiVSIMA7QLCCXiEclD' \
			b'k3mM+jz0jIem8ohpDLIt+/GuGeQwCeDKxM/liUYmX5xOvrhgpY9xvMM43mEc73So7nRw7mT0LX2B0DPRkXqy3te+go/GUW6659JJDWH94qBfXOm3Xm69gcGLKzr5egXYoqVhkF/WJ8TQiyTdqLFso0qxCTMgUIoNlGIDpdioUmxu9QNU5Kn5qLe2nNl2vS2j' \
			b'Qy3oIOYOUt0Y7e7ysxZBxNQ2fMOxLZK/dsnf1PjQq7Rk/kZ5jVMbpUa0ZSvC4gGntA5uSK30C7FXOlhBV8La3GSe25VXzepVHB4HxMPIlj98y1+b5XbBBweX9nSZ7Yle56FIPeTvg8h9aU1L+yj08k51E8Zd+Az0Td3qwEo+Dy3arFHtJSkKvxdqr65wb8XW' \
			b'iSrWVhdqq9Fayqq8qO4LVd1+00Nn9yotGO9Um1cVd4blm6BseMHfBe2zWgmudCxWPr7aKvNYTEYk0XKHmHjFveQdphqhSBaTUL5c7Ltk1kKgUEdFn2SVsNIJf+XD9FEeQQ4G1ZmFryvaYnIkfXnuY5Dc+Bx5PkSeT5Dn09H56G/+NgEfvM/HyTNf+QhvZiF/' \
			b'/4A/fsDvpnpd89EwbNHE35Hjr5HxrlaqF4a3DFK5DE+N08Db8MkyFbONwvn4K67gxE/DZwXwPnfeo80ncfIhRcxe5i+Lj4RnmMXcFHgPkmWms1gpHbHb8K5OotfwgcZ8mjGfkMurwkSn4Zk54rVhqy8+qonbJtFs2EieTfWIHsO7F3nDE08M8skbvadqsCXJ' \
			b'EZe3NZVgS2LeEge3JNOtY3+12fb0uOJw8tIjbtpbbttbbtRbkua2lRsKo0JvqXZsOYClsq3ljnixpfJvqexbaqhbbqVbltKW2+fWckrOlCrNtuFXcHE4Mktzy01vy01oyw1vyy1vy+LecrvbcoXYcqvbcrXYShaUkqrOtuN3c+bEn63nnJiOlstIDzomj2I6' \
			b'LgEXkGK3zALJyoNgbtZbrldbVgdbrnFbrobbTu7oh/i/beUp5UXM3lIF23phCBeHmUc3ndDKb6SshAoK6PlhzTe1+CiXlimiJ0aeUnoK4HdaKQa9wTAL6YYU35aq4bYXyUkoUyvckzu+oddRgTiAlNi25wgsWFJMW6oq244jCuM5e2qQW8+5VVwOikstYkst' \
			b'ZUstZeuZMOYi08MsprDOoDi1iIvfaPiNXHJmM117zpv5ifolwqOgjhN337AuYg1U9M+T1z9F+RTl8+DKx7DymVI67ZjeyTqp6FRGHUQyVDXU7Gmi+l6UEbWGQed3kW5qZ+inK9VLRHPSTe2Ofqp2dFSjeqo6oquE+f6IVvLTeslvPHQTPLv6yScNNamj/MNq' \
			b'KY+iapH1brmm8nN01fWrKB+VlN9VU1y4TFV5UVZH1dXm3+0dY6K/Y1TsujtCjf/hfRpHdBiG0n3QZGGIOKnPsgH2zlIH1j+OaDing965qq4aaLs4sMUIdlLzyQzD/vi/7+NgO47GgzaU6QieUGjTpIIOvNOHBIPG3J0AMWmiJE4xdGmaIWrTsLHFp80uuoq0' \
			b'N8vN38Zjbcsff+Mvv83SunaG5qVwNgEdaGCSOp8gtEYTcxUSbVyrRrbLtTLxNGnm5kTt7DINbVRLt6qp6Rmf+S4au8m0tjR0nv05orh5/ocVKQtJrqrB5YZrS5U0OcdtoMuDl+uUKKpKgoNSR3B0UcNLmlEVzyGq42V+TKabvGa+RN1jlq3aV/khIEbIIaD2' \
			b'gIBU9EgsO06SkyYc03cJozKA2H3P2H8CERAVgETDaqVAZSMtObwqR5isXEgItNHHDDrxpY3gT/AGGJK3T8IQYh5GolAhMjwKsl+HSgN2CTqZZilEaYkUpnKOTUGVUO1jvABY/LhrNa3xmTwt0kQIA3g1dGE92/Z33A3p3B33NQBprADvtqJcqrutKASKbdr/' \
			b'kQOAD0BdM7vHfs0Il+AtQFu1AN7G5vhziFN4K9B2DdDWAtraI9DWS3dwclzCjadVNFOv6XGtJDSC2dAlMGsnwaxNYJanXAZkSLsHY3nGY6OYFBop3HeCXm0CLlbWtZmMDu4oZCl/E2i1ilmtjoFM4HCGVMOcFKeUiCqnyMZYAaPaQxDVzoCoIIQMolSiKyEq' \
			b'lnotPiGXgE+JUZPw1AKelIyATi3QSQdVsaIj/hFoOopJzRmmkNYD0mVA0akwVEZY7xEMecDQsamx+sDcGFccnR0LXtPjWiFlwCA/cAmDJufM6jRpFrJehD5Iu4c+eWFG0SeGRtr2naCP3xk2TcQFU/am3PAYYuicsjCRnEPPMCeFHqWgysmxMdasWTpcj2BP' \
			b'EEGGPSrJldgTi70We5BLwJ7EqUnswTReICNgjwf2eMWeIAfEn4U9I5jTFswpmFMw5xXrHhZkfwxz+gOYIwb8wBz1Gr1WSBkwpx+4hDn9JOb0CXM0y0WYg7R7mJMXZhRzYqjtd0ufwlqUc4A5B6KPYU6vmNMDc3rFnMDYDHOGOSnmKAVVTo6NseZhTj8Dc4II' \
			b'MsxRSa7EnFjstZiDXALmJE5NYk4PzFEyAub0wJxeMSfIAfGXYo4vmFMwp2DOK1ay/NJjhkmmmsYcJr4C5gSv6XGtkFIxB6HRRcyRqKOYwyGKOSHrJZijaXcxZ1CYMcxJoZG2fceYY3aWh6bimnxVKGGO0QUhg/Ugo8tBkbEJc3ZyAuYECgbk2BhrFuaYGQYJ' \
			b'UQQJc4Ik12FOKvZKzNFcFHMyTk1hjoFtVSBDMUdK0qocfJKDlnEh5nSnmTa8d8gzMGco4FPAh00fnRjxHAEfI3F4U46ZgCDEEAhSr+lxrSQ0QpAZuARBZhKCkhVtyHoRBCHtHgTlhRmFoBgaaRt1gkI7VmyHoo+hkFEUMkAhoygUeJuh0DAnRSElosopsjHW' \
			b'PBQyM1AoSCFDIRXmShRKUlqJQlprFIUSpyZRyACFlIyAQgYoZBSFghwQfykK9QWFCgoVFMpQyAGF3DEUchKn1csYCiFIUEi9pse1ktCIQm7gEgq5SRRyCYU060UohLR7KJQXZhSFYmikbdQJCrkdFDoQfQyFnKKQAwqprUHkbYZCw5wUhZSIKqfIxljzUMjN' \
			b'QKEghQyFVJgrUSgWey0KIZeAQolTkyjkgEJKRkAhBxRyikJBDoi/FIXqqsBQgaECQxkMwabbHLPpZmIawFAzAUOIITCkXtPjWklohKFm4BIMTRpym2TIHbJeBENIuwdDeWFGYSiGRtpGncBQswNDB6KPwZBu+JFyOuViojqHoWFOCkNKRJVTZGOseTA0wzI7' \
			b'SiGDIRXmShiKxV4LQ8glwFDi1CQMwSo7kBFgCEbZkINPckD8xTBUX9x2o0cHozUbjQogvUeABBM4c8wEjlsBrODkooDEfibPJ1hCPIEl9Zoe16pDfIUlP3AJlibN4UwyhwtZL4IlpN2Dpbwwo7AUQyNto05gCb4BMh1IMYZMahRnYBRn1CgusjdDpmFOikxK' \
			b'R5UTZWOsecg0wyguCiJDJpXnSmSKxV6LTMglIFPi1CQywSgukBGQCUZxRo3iohwQfzEyHdvMX5CpINMTRSbWy/RSvhxEJos4rcNFkclitMQXRSaNx5UkeE2Pa9UhPpAJodFFZJKoo8gkEAJkClkvQSZNu4tMg8KMIVMKjbSNOkYm9eXIdCjFCDLhsRbVKSMT' \
			b'4Rky7eQEZAp0VDlRNsaahUyIeRiZoiASMgV5rkOmVOyVyKS5KDJlnJpCJhGhj2QoMklJWpWDT3JA/MXIJEc0yM4jwIxijBV02cGVhiEkKvppmzSTVK2o1hZqlFWkqsCo9qLKUVUjHZ0K6qNvWD3YzWW4b/AliYLjBccLjo/hOKY87bEpT67tmPK02ZSnaPNK' \
			b'LgHHEU9wXL2mx7XqEF9xvBm4hOOTE582TXyGrBfhONLu4XhemFEcj6GRtlEnOA7fAMcPpBjDcZ37tJj7tDr3Gdmb4fgwJ8VxpaPKibIx1jwcnzH3GQWR4bjKcyWOx2KvxXHkEnA8cWoSxzH3GcgIOI65T6tzn1EOiL8Yx4/t9S3IVJDpqSJTD2TqjyFTL3EY' \
			b'mfoMmXogU5+QCfFqXMNRnnKtOsRXZOoHLiFTP4lMfUImzXIRMiHtHjLlhRlFphi6U3SL7nsKb+NLBtC0lyrj0Qg09QpNPaCpV2gK/M2gaZiTQpMSUuVU2RhrHjT1M6ApSCKDJhXoSmiKxV4LTcglQFPi1CQ09YAmJSNAUw9o6hWaghwQfzE0HdsSXKCpQNMT' \
			b'hSaHHVtHj5Lm6o1NW3JRaGK/RYhCk8artUXo7i2nu7dc2r2F0OgiNLnJ3Vsu7d4KWS+BJk27C02DwoxBUwqNtI06Rib15ch0KMUIMjndw+Wwh8vpHq7I3oRMOzkBmQIdA6JsjDULmdyMPVxREAmZgjzXIVMq9kpk0lwUmTJOTSGTwx6uQIYik8MeLqd7uKIc' \
			b'tIxLkenYxuGCTAWZnioyYVnOHVuW0ziMTNmynMOynEvLchpPkEm9pse16hBfkakeuIRMk8tyLi3LhawXIRPS7iFTXphRZIqhkbZRJ8gE3wCZDqQYQyZdlnNYlnO6LBfZmyHTMCdFJqWjyomyMdY8ZJqxLBcFkSGTynMlMsVir0Um5BKQKXFqEpmwLBfICMiE' \
			b'ZTmny3JRDoi/GJlO3F5ckKkg05NBJmw0dsc2GnPFxkZjl200lo/MVHIJyIR4gkzqNT2uVYf4ikxm4BIyTW43dmm7cch6ETIh7R4y5YUZRaYYGmkbdYJM8A2Q6UCKMWTSHccOO46d7jiO7M2QaZiTIpPSUeVE2RhrHjLN2HEcBZEhk8pzJTIlQa1EJq04ikyJ' \
			b'U5PIhB3HgYyATNhx7HTHcZQD4i9GphO3HBdkKsj0ZJAJJhDumAkE12eYQLjMBMLBBMIlEwiNJ8ikXtPjWnWIr8jUDFxCpkkTCJdMIELWi5AJafeQKS/MKDLF0EjbqBNkgm+ATAdSjCGTmkA4mEA4NYGI7M2QaZiTIpPSUeVE2RhrHjLNMIGIgsiQSeW5Epli' \
			b'sdciE3IJyJQ4NYlMMIEIZARkggmEUxOIKAfEX4pM5uAu5OapgVM1AVDVFYKUK0B1XouIDhYR3RGg6mEDjE+ZyiUYRXQwiuiSUQTiiVGEek2Pa4X7YBTRDVwyiuimsIpDglGEZr3IKAJp986qbbIyDcBKYtdZYKRt1PVqsYe48TMdkuGhdKOWER0QS4rglJ2J' \
			b'/NwyYpiTWkYoMVVOmY2xdhDLuEnriO44akWRZNYRKtmV1hGx6GutI5BLsI5I3Jq0juhgHaFkBOuIDtYRHVArykIrymHUGnxGagy8Du5dLuB1xeBVgOt8wNVgVao5tipFCRpEIzE12cJUg4WpJi1MaTyuJ8FrelyrDvEBXAiNLgJXM7kw1aSFqZD1EuDStLvA' \
			b'NSjM2CArhUbaRh3r5za+JgKXaO1D6caAq9HlqQbLU40uT0UmJ+DayQnAFaipctJsjDVrqNXMWJ6K4kigFaS6DrRSsVeCluaioJVxagq0GixPBTIUtBosTzW6PBXlgPiLh1pXvp/ZCFq5MhX4lIDKdSeCldsBLLt0tAUjP3vMyI+bA4z8bGbkZ2Hklx0JpXcy' \
			b'1FIvGhOGWsnID6HRpaHWpJGfTUZ+IetFQy2k7bh21oJanHmyQ88LNWqHHkMjjaNOxlvKm9wM/UCKscGWGvtZGPtZNfaLbM4GW8OcdLCldAyIsjHWPDP0GcZ+USDZQEvlunKgFYu9dqAluXCjiYOtxK3pczhUlFIvDRKlQRcM/6wa/kWZaHmX4tflfZi+LGIV' \
			b'5LqMIRYWsZpji1jc2cUiVpMtYjVYxGrSIpbGk/GVek2Pa9Uhvo6vmoFL46vJRawmLWKFrBeNr5B2b3yVF2Z0fBVDI22jTgZX8OUodSjF2MhKF7EaLGI1uogV2ZuNrIY56chK6ahyomyMNW9kNWMRKwoiG1mpPFeOrGKx146skEsYWSVOTY6ssIgVyAgjKyxi' \
			b'NbqIFeWA+IuRqZwwUZCpINM4MrVApvYYMrUSh5GpzZCpBTK1CZkQT5BJvabHteoQX5Fp6BIytZPI1CZk0qwXIRPS7iFTXphRZIqhkbZRJ8gE3wCZDqQYQ6ZWkakFMrWKTIG9GTINc1JkUjqqnCgbY81DpnYGMgVBZMik8lyJTLHYa5EJuQRkSpyaRKYWyKRk' \
			b'BGRqgUytIlOQA+IvRqZywkRBpoJMo8jUwiS9PWaSzlUUJultZpLewiS9TSbpGo8rSfCaHteqQ3wgE0Kji8jUTpqkt8kkPWS9BJk07S4yDQozhkwpNNI26rbJlyPToRQjyNSqSXoLk/RWTdIjexMy7eQEZAp0VDlRNsaahUztDJP0KIiETEGe65ApFXslMmku' \
			b'ikwZp6aQqYVJeiBDkamFSXqrJulRDoi/GJnKARNPGpnc9aGTfJfjIRGKgYVf3B9BKD7EvReEkosiFPuZxD6d/454cv67esO16hAfCGX6gUvnv/dTCMUhilAhyyUIpWn3zn/PCzN6/nsMtf1u6QeJ2/iOwfnvB1KMnf/eA6GkqE4ZmQjPz38f5gSECnRUOVE2' \
			b'xpp3/ns/jVC8aBrPgA/CSCgVZLoOpVLR154Bj4z409bhHPjEscn1p16QKpCiSCWlaVUePskD8RcjVTlw4kkj1ZWh1MOOoSzGUPbYGMpKHK6jNhtDWYyhbBpDIZ6ModRrelyrDvF1DGUHLo2h7OQYyqYxlGa9aAyFtHtjqLwwo2OoGBppG3XbNr5jMIY6kGJs' \
			b'DGV1DGUxhrI6hgrszcZQw5x0DKV0VDlRKda8MZSdMYYKgsjGUCrPlWOomNHaMRRyCWOojAdTYyiLMZSSEcZQFmMoq2OoIAfEX4xM5cCJgkwFmcaRyQGZ3DFkchInXAIyOSCTS8iECIJM6jU9rlWH+IpMbuASMrlJZHIJmTTrRciEtHvIlBdmFJliaKRt1Aky' \
			b'wTdApgMpxpDJKTI5IJNTZArszZBpmJMik9JR5UTZGGseMrkZyBQEkSGTynMlMsVir0Um5BKQKXFqEpkckEnJCMjkgExOkSnIAfEXI9OxAye6gEn2fUOj+/umsEJQgZ9HgB+691xJ/RITCEBRcwyKGuDQ6BeFuTYr/ASv6XGtkDKYPbiBS2YPY/Ajy8sJffCG' \
			b'pXYPrBGaEQBCxUz/48YPscCRwn0nlg878DMVtxmHH65VsHtwQr2Aj5Qqhx5+gDwQpOCjjxl9AjEN8Cd4Zxo+zACgQEJu+KASHQMg0DJn3k5K2GX0L7d8QHlY96AeRX5Nmj4AghDVcEXhvWuZEQTAqFEwipUeKXfBiFCHu0+KQlRn72Q2turvBI5JadwxyFKj' \
			b'v8OHjyM82YOnTjzKwKl9QmOnWnaWFBC7+DEUbPfaY7Z7XD1hu9dmtnstbPfaZLun8WQMpV7T41p1iK9jqKFLY6hJ27022e6lZMuGUUi7N4zKMx4dRsXQSN6ok2EUfINh1IEUY8MoNd9rYb7Xqvle5HAocBxMDfPTwZRSU+Wk2Rhr3mBqhhFfFEc2mFLBrhxM' \
			b'xWKvHUwps3QwlTg1OZiCEV8gIwymYMTXqhFflAbiLx1M2YPHTJRpvjLN94QhygOi/DGI8hKH66jPIMoDonyCKMQTiFKv6XGtOsRXiPIDlyDKT0KUTxCl8RbhE9Lu4VNemFF8iqGRtlEn+ATfAJ8OpBjDJ6/45IFPXvEpsDeb5hvmpMikdFQ5UTbGmodMfgYy' \
			b'BUFkyKTyXIlMsdhrkQm5BGRKnJpEJg9kUjICMnkgk1dkCnJA/MXIdOxIiQue5rukqb0B1ASYCRAT4CXAyjVCyrXACSVkOOHLQTjhCFNTdVzPKkBI8Joe1wopFUIQGl2EEIk6CiEcohASsl4CIZp2F0JGYSMVL9Kz7xgz+JIDxlRcMGIPMPAYrO92VoJiKoCD' \
			b'x8ENHkc2+NnnNfgZ5zVEtiZACNJZBwiJeAGERVigGSgW6J05NEzxOKMhkKBg4HE+g9fzGWKF1fKdAAYCAsfOZSggUEDgqkAAG4P8sY1B3hwAASPBAgLqNT2uFVIGEDADl0BgcjOQT5uBQtaLQABp54FAjB7p2XcCAjtbf6bi+vGtP163/ngzAgIhlYIA9vh4' \
			b'7O7xs7f2+BlbeyJbMxBQ6awEgcT25SCgNUBBQHl+EASwrSeQEEAA23q8buuJFRbxTwaBY0cgFBAoIHBVIIBFe39s0d4fWLTnwwp10T54TY9rhZQBBNzAJRAYW7QHCKRV+5D1IhBA2nkgEIsX6dl3AgI7S/RTcf34Ej0eg/V7IBBSKQhgMd5jEd7PXoD3Mxbg' \
			b'I1szEFDprASBSPwKEEAGAQRwdxgEsPQeSAgggAV3rwvuscIi/skgcOy0gQsGgWL1daGAcU2rER6rEf7YaoT3B0DDS7CAhnpNj2uFlAE0/MAl0JhcgfBpBSJkvQg0kHYXNAaFGQWQGBpp23cCIDtrD1Nx/fjag9e1B+8VQEyrLM2AZJiHwomWvcoJsTHWPGiZ' \
			b'seoQmZ9Bi8pwJbTEYq9cddBcAr4kTk3CC1YdAhkBXrDq4HXVIVZtxF+86nDs6IACMwVm3muY6QAz3TGY6Q7ADIIFZtRrelwr3AeY6QYuwUw3CTNdghnNehHMIO0ezOSFGYWZGBpp23cCM90OzEzEBVP2YaZTmOkymNkxJN7JQ2FGy17lhNgYax7MdDNgJjA/' \
			b'gxmV4UqYicVeCzPIJcBM4tQkzHSAGSUjwEwHmOkUZkLVRvzFMHNs33+BmQIz7zXM9ICZ/hjM9AdgppdggRn1Gr1WSBlgph+4BDP9JMz0CWY0y0Uwg7R7MJMXZhRmYqjtd0ufwlqUcwAzB6KPwYxuWJFCBpjpd2BmmIfCjJa9ygmxMdY8mOlnwExgfgYzKsOV' \
			b'MBOLvRZmkEuAmcSpSZjpATNKRoCZHjDTK8yEqo34i2Hm2Cb+AjMFZt5nmOlgc9Uds7nqDthccf1Tm6vgNT2uFVIqzCA0uggz3aTNVZdsrkLWS2BG0+7CzKAwYzCTQiNt+45hptuxv5qK243bX3Vqf9VVCWbA0gQzO3kAZkLZB4TYGGsWzHQzLLMi8xPMBBmu' \
			b'g5lU7JUwo7kozGScmoKZDtZZgQyFmQ7WWZ1aZ8WqrWVcCjOyI58U/ZHvlT4VtCFSSTOc/wOl94087QnoU18vArn2oc/aZO3ATdMKGnHbOvK1UmkXk4gk+elmx+g38Mtpm2mGzXQDl07bnJxhM2mGTSKt2rNvRibZBuUZPXCTSeJSYZpth4SUtkVhuTlJVXQA' \
			b'qB4YNZXMjM+4GZ1xM9mMm9mZcdvJAxgVCKlyqmyMtYtR/NLxUzdHZt2M28eqkHF+6qbKdh1WieCR09pjN8GI7HAzLeFBKwKD+bdAjCKWwfyb0fm3QL1F/AyxJIR/bc2/jTwh6GLUE38noQxfBuhlxLCAavCrQ9C1D1q9AJVTiFJM2gEkoNFMKDpgLyaoA3TJ' \
			b'xjF7SGFGLLwCElho/dna/tg4I9fuK7S6aPSFVltRex/S2l2mqa1qaJuPDfwJGnlSF4sSFu0rqjfo3ahoJ7RsULEr9es866qgSbe7p+ePKULRgnvGUVHdbXVrxAma7Wj3e6DM1qox1mErrJ+Cxjqsq7b5/jfWT6KcRC0FncSqpT6sWka7xA+pXWK3tis6Zq+3' \
			b'aCb0zCk65rRun3TkrlrRZN02FnJRODM6S00/pXROVzjm1L6MfySFszd2Zs3TPJD2ofCOuUH5de2VaKPqTL2eEzXSpDYK488r0khS5vxftVMtdD+ohhJ0oewNUW/cjGNuLkljCe9GNZbhlKdprc2/qQ7fEVUyFrMLxmLVDP1Vn1+FJbXlM7VlSscpqqndabXd' \
			b'KTUK5/F+nFqjcKIf6qvKVBiO8xNV1vEgnz+9Ualac/lUG/13Z1RxddAZp6s4aSGPpeaiWrNJrRnRCaXzNTXaC0Ua73zxjLHM/GKKCpWC6zOznqd8O590XJgHxnyVzEpK9RK+yrGYrfzEnZB846T75tZNRVEFmFwhuT/1F9bWeVXDz1R/7XWqQJ5jn91jc/PG' \
			b'j8Tvh+mxTfTWXK7OpGJfWK9tdwwJ6Y7P4k+oMyHrulUa16H5Y0ou66wxpcmNkKbHlc19zJHfa6esdMiSJmoefibr3LNYl9ChyjpTtnSmxrTO5PT56TNZ7ebVZazIHbIMucfVuUvSNf4RVucyPdNf/aqcmOeIOU4rpjePuEp3kWqG5woeZ5Vu8+/+jnBMJp/8' \
			b'paiceWqGlw8NF/JcXZxLUjmnqBs2Kj7PYt3TtQRgwz0jambi4ybvl8I5rV8DvtjzdW66K9M05GcTXirZ42ucXQPTxxpUseap1mmfwUz2cAb7KWsibidiObzlicKL0UjtRSmlLQUxtU2zTjfx8kk2N707I90v11RsuP8Yyqp/IEU1Z0/WriX8Yykre/ndJBbC' \
			b'dWgoFucWHyN7SP3EUU7rNvGw87H7TrLWtVZJ7XagiOLlHajqUdRSrpKMvZAR2yOqpKKOzmfEPVBFprqM7tKlaaJ70EL1Ci1UP74WGttyWLRQ0ULn0UJN0UIPo4XMCi1kHl8LNUULFS10b1qoLVroYbSQva4p7YtQOY9toH1hauZKNMz9qBMjJb62pbGzqI/N' \
			b'v6n53LE+5WV4kkjRJNesSVZY+lyvNgGW3p8ykfzf83X2Mxr1+OZO9Du1vDvWw6JYmqJYimK5dMUijy63m1JUS9vdkfIXhXIxNspFobznCkUq/Hs57rkHhYIDFfF/BQqlsXdy2F7NYyCu+vXdVqq/oWsjiubKLJOLorliReOKopmvaFz8fz8UzZUZJhdFM0PR' \
			b'UFrP5xf4S1M6EveyJ3VBzoXoHC3MZtZgSSMvVTmS/KjKMaKS6fEM5cNKp5H2eceanNrInShRagB3rB+pMtMVA6sVVsdFDV2oGros1SNq4rJVj60vSPXYE+ZpNPJi1cPJz9DbOUHhtGvsiYvCKQpnTOFI5Xw6C9jnUDg1Tra/zolhx59L4RpdiUcONGzXmAgX' \
			b'xVIUS1IstdTQJ2gZc4JiER69dytOzt0JqlArYY8sZrdrrH6LYimKxcn3qJ62zd0MzSIx3t/FbEtdFW6WPY2RrEwBt8WQtyiWRYpFEhRb3mIkw3qFuyyVfF+rLfa8RaFMKxRp8Y9udXcNCgWkPE19YnipmltnJx45r68t9rxFsQwUC9eiy7LmvQa98qQ7KjV3' \
			b'VGp0VIo5b9EnQ31iiz4p+mSxPilWu09an7AqufjtRkWhXLpCYTMWGKkU49wnrU+uY//icYXCwi0K5dEUSmfvSKWLQilmtkWhXLdCYdmWDsrj6hPePYQvqPjHNaOt7uO7TRY6hs1vrk7P2HvUNa3qm/da58iDvY850cPd/3PY+8u7+Im0ySvWSKxB7lMt8XY2' \
			b'Vk3CsaPqqb4joBDt9Li2uEU7Fe10bu3Uj2mnfu//LNqpL9pppnbyqp36k7TT4xr0Fu30gNrp/ddMnPn+RzCrvf9zaCZ5V9FM84Zzwq0TtNKVWQNz0cLX6h5tuoh3alzaV+rG1NLTnjqar3pYqluOM62EHnAWifO/Lw205kt0ZzpI3LO5MNU603KtY1GappGA' \
			b'ZvOKuyk9PWfq6V8et/lj7nZ5eew3r0zLR59UFGBIAPT/zS35b7Y0DuSHNcfbUreL+jj8Mm7y8iZi8SvWCRv+PF63ofJRtaHKQdWPWEoFJ34Tu4nb3NSpfhnHTYzHHOGFdsMagJjH1YDrEdd6biFMMrOZ9AUxq+5Yj1Ksjinu5d7wuRrEavqXwrjVhSElfPxP' \
			b'3tXwu/yht5GgSPdRyz/+2oY1dLP3V5PEoFdHQqUU7XgpGi4If1Swkq/nmLFCmb1yyXf6VCXjIw9Wy9rslJeAJ/vjKtzqJyrS/yAGNeLsjmNwkWXnN3/MgWPzSFT+hDD/CITRewx/5JEIJMg8wx++WCptlTTiMoKqKZp2vpM+SSNlO01nvzn+x6g+fAJMtYqh' \
			b'w1DGzOxeaO/HabeT5BPuEHk62MoHWPtssUPOVEY214gRuMEuedlwQ6+UQ47lrEMnR8cyLMmkZNMkjvKZHAQp4CyF83nSwuFumsuETOh51Psc515E4Drpa+E8azAqvemDFLi7uO+4kzYaoGGH/o/ndiyHwzlndzvew2UdL9FOTnIrFYeeXmKrkUI+ogNv6iWt' \
			b'ijztfbct2y1vXzyauJ82ZjYnuzAkWpD0mDPCxNmxV5cCVcZcsCJudYWovwSFbDeX44zRS3Pfr0IlsZepc93mUR144yJvuF73996M+v7aWxLP/rDrdQqqu2937y84yaHaTAwW5zcpe0+tiuW6wvEk38osjPZm2t2WRUV0D9a+KnvFbYxnlTMnxPAsqn0Ix/O6' \
			b'D/OmGQ5VaWLuYLr6zOvNnK/RtZt9x5OwowFzHE+wL0oJhnWl7S1tezw/WZwOL06e53nghsfrbRfhMJ1elWa3uNm1m+Is1Lc5eSJo/uj9fE3Pb87ueBl5UUqwzZTmt7T5sb1Ccehumon5knM0v/qcYz22MLkHx8Ybi1KCe3szKqUVzm6F7aY4pyA4McVyrlbI' \
			b'leN8LdFv7smxxdSilGDi/UzCuKfSHrvN2R2b1t1HvvfsUJ180e2L61K/Kc7BfMRM2M5M1x2/dIWS68FcNT8m2z1Vz3a8pzg23DwpgdjGUsM6Eotb03gYWNyXprq0qbKddnGYArQTBjv30FTz+nH+Zms39+1yg/YV+YDt9drmu9Qo6CwtmHemmEtoyX6zxrHh' \
			b'08os5jvD6zfm3t+D6lWmypbXqW5TXIMBgT15qozqzlkAIlaRMwHFtLj7zUmOt8WcmiZ3YQvUwtREN1/S/iW6hajcGlPB85sHzhXaofZ6VHi8xe5EF7bLLUi6zM1/GeTYFNW9VHXzdsviYJ9lJ3YavUeqm3fUXquDjE42fLo+GXWbq3WQ0clzWWeX0RJEXSSr' \
			b'fvPwjjX+eSKJg8xW7V+70r4QHyjwnjjsDT55Zup9EKLdvC8OQly05+0J7STlA0CWOjnhI/tfk9depnt3O94TspsIQwW55B1uF1FB2s1TcqgUS6adnlKl4AODnpBDpVg1wfUUKoXZPCWHSnGyFdlTqxR285QcKsWSqa8nVSnc5ik5VIolc21PqlI0m6fkUCm6' \
			b'zSuLA2JUdfTxgZ4aVvEDZrc8bPjYQQTQyDavMyQUicHnfpB4DImNDzTUPQeNGY3NX4wZ/iO23YvNgpYUVC12/k2DDhLV1+y0OMvVBs/1cLnhubccw/hO4jpUP6lyDtXMa1Xq0CNv+CS6LINUZbssXSNpqbpxrnwEZXb8JI547LKjHcOxjlw5MddK9fQVNwqq' \
			b'zLLVnfNS/nXDI++4Aiuveg6RM+50SEkvfUVVnJ/g2D0+cjA+Iel9c/v/AWFJPzQ='

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

	def expr_pow_1         (self, expr_pow, expr_super):                               return AST ('^', expr_pow, expr_super, is_pypow = expr_super.is_dblstar)
	def expr_pow_2         (self, expr_fact):                                          return expr_fact

	def expr_fact_1        (self, expr_fact, EXCL):                                    return AST ('!', expr_fact)
	def expr_fact_2        (self, expr_attr):                                          return expr_attr

	def expr_attr_1        (self, expr_attr, ATTR, expr_pcommas):                      return AST ('.', expr_attr, (ATTR.grp [0] or ATTR.grp [1]).replace ('\\', ''), expr_pcommas.comma if expr_pcommas.is_comma else (expr_pcommas,))
	def expr_attr_2        (self, expr_attr, ATTR):                                    return AST ('.', expr_attr, (ATTR.grp [0] or ATTR.grp [1]).replace ('\\', ''))
	def expr_attr_3        (self, expr_idx):                                           return expr_idx

	def expr_idx_1         (self, expr_idx, expr_bcommas):                             return _expr_idx (expr_idx, expr_bcommas)
	def expr_idx_2         (self, expr_abs):                                           return expr_abs

	def expr_abs_1         (self, LEFT, BAR1, expr_commas, RIGHT, BAR2):               return AST ('|', expr_commas) if not expr_commas.is_comma_empty else _raise (SyntaxError ('absolute value expecting an expression'))
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                            return AST ('|', expr_commas) if not expr_commas.is_comma_empty else _raise (SyntaxError ('absolute value expecting an expression'))
	def expr_abs_3         (self, expr_paren):                                         return expr_paren

	def expr_paren_1       (self, expr_pcommas):                                       return AST ('(', expr_pcommas)
	def expr_paren_2       (self, expr_frac):                                          return expr_frac
	def expr_pcommas_1     (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):           return expr_commas
	def expr_pcommas_2     (self, PARENL, expr_commas, PARENR):                        return expr_commas

	def expr_frac_1        (self, FRAC, expr_binom1, expr_binom2):                     return _expr_diff (AST ('/', expr_binom1, expr_binom2))
	def expr_frac_2        (self, FRAC1, expr_binom):                                  return _expr_diff (AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_binom))
	def expr_frac_3        (self, FRAC2):                                              return _expr_diff (AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3)))
	def expr_frac_4        (self, expr_binom):                                         return expr_binom

	def expr_binom_1       (self, BINOM, expr_subs1, expr_subs2):                      return AST ('-func', 'binomial', (expr_subs1, expr_subs2))
	def expr_binom_2       (self, BINOM1, expr_subs):                                  return AST ('-func', 'binomial', (_ast_from_tok_digit_or_var (BINOM1), expr_subs))
	def expr_binom_3       (self, BINOM2):                                             return AST ('-func', 'binomial', (_ast_from_tok_digit_or_var (BINOM2), _ast_from_tok_digit_or_var (BINOM2, 3)))
	def expr_binom_4       (self, expr_subs):                                          return expr_subs

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
	def expr_vec_2         (self, expr_bracket):                                       return expr_bracket

	def expr_bracket_1     (self, expr_bcommas):                                       return AST ('[', expr_bcommas.comma if expr_bcommas.is_comma else (expr_bcommas,))
	def expr_bracket_2     (self, expr_curly):                                         return expr_curly
	def expr_bcommas_1     (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):           return expr_commas
	def expr_bcommas_2     (self, BRACKL, expr_commas, BRACKR):                        return expr_commas

	def expr_curly_1       (self, LEFT, SLASHCURLYL, expr_commas, RIGHT, SLASHCURLYR): return _expr_curly (expr_commas, forceset = True)
	def expr_curly_2       (self, SLASHCURLYL, expr_commas, SLASHCURLYR):              return AST ('-set', expr_commas.comma) if expr_commas.is_comma else AST ('-set', (expr_commas,))
	def expr_curly_3       (self, SLASHCURLYL, expr_commas, CURLYR):                   return AST ('-set', expr_commas.comma) if expr_commas.is_comma else AST ('-set', (expr_commas,))
	def expr_curly_4       (self, CURLYL, expr_commas, CURLYR):                        return _expr_curly (expr_commas)
	def expr_curly_5       (self, expr_ufunc):                                         return expr_ufunc

	def expr_ufunc_1       (self, UFUNCPY, expr_pcommas):                              return _expr_ufunc (expr_pcommas, py = True)
	def expr_ufunc_2       (self, UFUNC, expr_var, expr_pcommas):                      return _expr_ufunc (expr_pcommas, name = expr_var.var)
	def expr_ufunc_3       (self, UFUNC, expr_pcommas):                                return _expr_ufunc (expr_pcommas)
	def expr_ufunc_4       (self, expr_term):                                          return expr_term

	def expr_term_1        (self, expr_var, expr_intg):                                return _expr_term (expr_var, expr_intg)
	def expr_term_2        (self, expr_var):                                           return expr_var
	def expr_term_3        (self, expr_num):                                           return expr_num
	def expr_term_4        (self, STR):                                                return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1].replace ('\\}', '}')))
	def expr_term_5        (self, SUB):                                                return AST ('@', '_') # special cased for last expression variable
	def expr_term_6        (self, SLASHSUB):                                           return AST ('@', '_') # special cased for last expression variable
	def expr_term_7        (self, EMPTYSET):                                           return AST.SetEmpty

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

	set_sp_user_funcs ({'N'})
	# set_sp_user_vars ({'f': AST ('-ufunc', 'u', (('@', 'x'), ('@', 't')))})

	a = p.parse (r"\int**a.b[2] x dx")

	print (a)

	# a = sym.ast2spt (a)
	# print (a)
