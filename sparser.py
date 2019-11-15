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
			b'eJztnX2P3DaWr7/MAuMGqgCJlEiq/3McZ9bY2MnGztwdGEHgJJ5FsHmDneTOxWC/+z2vJKUSq1Qv3VXVTVjuoiRKIs8hf49EkdSTt395/eyLz7949ZfVX/7t/S8/wI+ufv78szfw8+XTr56/+hwCn3z19Nl/YOBvT7+Cv19/9vWrZ1/+XUPw++qLN3LYpxR6' \
			b'/fnT1//OwU+e//XbZ09fP38t4ZdPdesnKfi3FPySg3SGeN3PICA/rfwajP/i1Rcv9bfVgNHDn3391ed/x8Nj4OWLV19jQl6/wXy8/voTjcrB5y+/fPP318/x+q++xhO/ePXmr5ixFy8pOv39z68or2SnL3Cv2OATss2zL16+fKq2+0pth4GvXvz1399oYr4a' \
			b'pRHXnv8n/Hn68kv4++knn9M+3PrqU7EYhj5Jwb+loFjs+eevn+OFv3rxEn+f/9czzPHTN5RVPOUbTiAk7I3+os0+ffG3F5/iEc/Edxzvy8/ZUs/fqNH+6/XzZxTh0xeffYbOf/WCSsszSvTTV5+iwXDHF3j8y6dfvn7zhSRRCwBt+D9sbPxp2QtwyWf/AcGP' \
			b'f3z38c93Hz7+mYU/Qvj7dx/e//7trx++/eG7nz7+/u5DthuC7//5G+z58c+fNfzL+//+9t2H/9bVj3/89v5DWvkOgj+/+/3b73/9SUIffv2/KcTX+/j+48fvY+i3GNLTvPsuBn/84Z9x6++/xwv94933v2v4N7oAb/7jl+9Tmv/xj99SwmL6f/oxBn/+46dv' \
			b'f/z5tyyXMZMpPp5Hw7+//5DbQYPf//Hhp/+XnxQCuvrdj7/8Go9598MPMakf3sWk/vPj+5SdP9/H7R/za4MFNfjHLz/++ku8OJourvycZTlZ8Zdf07G5jX785feYiT/fReu+++WHbGt+wHff//rzz+/ieX+Nh3wH2fmf98kn43i//fj++/dxBcrbLylXv338' \
			b'/dd44VgGYoZ+/SnLKp50tPIxO/Lbn/5891Pc8JGP/Gb19snaNave36w4EDDQDfCnb1ZduJFVWMNQ32K0VedXa3cz2sBrjR4HB7S6CYMUa01XgZ1P7MrCOe2qw8BN3Erb0ob1gAHb8B9nYa+5yTcZt7HJdfkmDEKodfzHwQVMcyObMAghD//DqoN1zq3HAPwa' \
			b'OJoSggd3ZtVDjJYzlTbp6rqjvLUd5q2XrHWcDtzImyRdYDPTwgbMkE2bTL5qrARwG54E9rZdDPWUQrt6gmvgH88Hwpa14X2G/zgwo+luZBMG0SnkDljtb7JVDWfbDf+AszGb9L9rdHeHAUykbOekQ3JkI69btIjp1CR93CrbNjZ0aUM/3rC2fD30OpdTI37g' \
			b'KB3agu0W+I/DxLJbYW1tqUD1sBNLjuzo446ul9NJ/uDyHeXcQH1oMRq6g4sAbRryVS5Nhrfh4ZhzOEXPdSOuuukmKRvjzW5zdbLJb67OxJgkIGyujg5ad12WslQpJBGTDX66Ia9HnReXtJ2uQ6WmEox13Uji0JlSJXXz5qa0uu7IzFAKn0CJwBLS+pWHkgOJ' \
			b'w/Ij15rZjfLm7JJYZnqudUcexUIFVS3WD0hNy07vudq3YMDerKA+ptqP++L2tKWjLX2TtvS8pU1bHG+J51kbEhlr+I9rYxrjJpNvwiCGBv4D5ru5SUEMdVwT9BDMNBX43ksVEV1H15EWGDBZElFYA1WhQ/2KS31r+Y+HxLUsj5j7lk47kIJKgJW5RctFdeDM' \
			b'40beJOuNnLNBD/VWS9hou26BDeS1TkqfajScsCP5aOk/ppwPwQDmxfEfh2Dg8xsOogHAHR4dwB6EVc/CACfDawrJViZQaeoHVS2K0DLWZveuWeg7tEOnRRErEZfUPnkHoogTYOOTPlV/Wg0pcWAiBiedTENWQyYGggY0uqXSDLL2xEfW4VqgVE23xDXIB+Wm' \
			b'4z8Oohq2Okq6IUvB8fzb84oWRiz2LV3fQJnDHanmeMoThgL/cX2UAhMoiPnt+E92U9IJsXrLf+h+hK2IpadnCBrdeSOrsKY7eBMawpNToK6Jz/pB7gsc3foYPR5royP3OKM78I5HtkAIbrbeNqsWnN4Cig2eEfCHzoZyiuUH6lDAcgKKA84eVi1CZTXAAocA' \
			b'6Fso6y2oQgtmakELW1CRFgwIWLK4F04OZQ2SCwW3hau3IEQYFUPwA+ds4UotXKqFS7cNbGtgH9i5Nfg7rLAMuBVoIpTFFtLWQuIGsxrsauhWQ78aYBVjwxnAtS3c3LVwB9iCxVqwJJgAcgoaCzdhmFSMsYL0wgWw6MPpISthNUCqmgb9BWmEJMJZ8CQNHNHg' \
			b'gaijkAEwRwv2aMEgLVgEr9FA5B5vxNoGDzCrAItdhW4V+lVwq+BXIawCHABXasEskCgoDFBsoFZDsYSbIbgFBLkAdQIZ9xZF32NlXoGffVh5OBSs3oLZwc+IAnAU3b6EZhXwmrAfduN9MwRv8P4L1sG1T9CnuIHWYTdaGFbRiPhjOBbaHvdi5m4ImLSXz/EW' \
			b'74Bpnc5dy8MVlYcnAzu2ZQ+aRjw6aDFh/w8tr7ZGfqU8kBtpg5ffIL96InLuDd0U48/AJ+gkeopFu6uyXHFJslxGrNGiIWXGi4+Nqy6+bheDUzup35bq67mSkpWMvDRMSsGc/3O/k8dnPC0ezj2be3Pqw4LvwHGI10YUs2OBVX1kAUSDUi2RfLCJ9QjSWIqp' \
			b'e5+0jGeI1dAJtDxzGdbSm8oql9G8XKayqIUPn9UuooBdjVfR/OxHqga0wfiqblevbm314XX78EnLjyZvn/RN9eV1+xJFNVQnXrcTn6C5uOlAnhQ7Raal+xtsRYXkrODa1ZWX7Uqr956duBKNwq0FfKvaQ9rhJK1DI0GcHm+70CR9de1FuxY82FUPXrkH++rB' \
			b'K/egqx68Zg8+GbRRx3CbNxmBmwfq48jVe5cyTu7trTSCyh2tOFt87SjaIW1L6DNqNXRyp+XM8afSNzV8zzZwuxV6hAtmw7dutS3w4LZAafnb1zG2YcfIM+6+hxtpT27kNNIwz83MVWeuWGd6eW/WiK7og7O8e2/lZXvbied7fl/Q9/JCv5EH7l6Oa9r6qmZR' \
			b'RQ5syMCyHviJCN9bY0qxHmCLhR2XwPo65QQvyULPJTZwiQ1c0EPgAh2kvKtgtvKiWSksXRd6/tHuLOJEOiZ3HmUfa5kilvslOL6040t7vhNvYF8z9v2jdxZYjEnj2N7eV1MVTeW5F43nAuu5aPpQspiKTbXcE8/11zMD/VALWUk8fS+NsVzWHP/IE2jQRxbT' \
			b'4qCI2nnzqm8NqXem4W6Zpna0vDLfQfoM952tvrsu32H/ZiO9ZOG3OukSnUR9lmvNujanoSeM9CDHulXddeHuokomBq69T8/T+7Sl28B6K3/NNcnwMPXBVFdeuys7X3147T5krlUfXq8PaRAhP6ZRfax3J2dpjzRyP98FcUYjr2m60jjQb2Sc6YpGQ5kUmQdD' \
			b'mWx4FI2KohiN59Nb8nn17n2NZzNePEQ/fcNrRp3dsTuqG+7WDdZK6edaxC9J5HWpvP3ntwFxeBodUP1xR/4YxB/UeZM6g8lL6z56oJfuG/TimbqTiRJyk/4gjwNOT8TCVx11Yv1ixcJeBNTcVG16ivaIrtryZLbsqy1P1lOFX3of031WJyqxwlPD6jEEfsKo' \
			b'vjnUN8NQLXjkzBJyz8F35Pt3IJZbdn5Ow47Dhm5UehIguFvBW5nqjcXeaNmcQe7bYhcl6llq683cnfTY5XvnwkCMltsajr1UrDEtz2CE944m749WHfGk5cHcpzO1jjUO3JoUuNUhMHY7z9ds4hp2BjbSGdhwZ2DWRqqNT+TpN7YiBW62kLYoJ82GzjGSqlf1' \
			b'/omtXifuuvam8bfYo732XLpY75DmVOkZTbDlTjDIw8k9rhuqso/M632Vg0uVAxw1QqXWt7XUjkutqQYZGyTUany51VjaZ3xXS+241NZe9JdbanGkmOUhRviDj3k39MkY/AGfWZ3220qnbXuj/YJtmu2ZenBYfsSmIwY+XZ0o7MqLRyflQbzd9up1yw0FtMZl' \
			b'h/rm2GzKP+o8wofRTy8nAStZ7Txis3nlsJcDn4eaIeiWtU4TeOlFBLueGOp6UodzXLyr0Ao2m6kKBdpqRxYjHVio41BV56vwZ9/VanfpbsIuX5a7fFnu8mW1y5ctvc2ijktWOi7ZuYm8uvnN/cxm7BghWy1vJXoznDve2PHGXu7fuPdafSu856OOdgesczAt' \
			b'n4PJ1jfld2BXu01bZCwaNqHzrzRdBL6hD6wMIdDDHr14tdwKT9rAR9f3g1dMJCcMcvFBDjsD4VtDftqTW3pmgudIniHimVqeseEZQ35IDQVdbeu5UK+j8TtupOmkkaa7kc7s/Kzf8bM+/RhZBTt09DhO9wd67yIlJfVu54LQ+9gtqiv31AlUSlBnOtaZrt7D' \
			b'XnbZ4e43XZX963ai4xrHDXf1FUXszQkO72UcYs8C2YtA9jfSSMIC2bNA9iKQ/Y18tgYCLU4Ejd/TrTXkimtI4JIQ2NWBPbsychuM2xzvAgO6G/kSnKvefwjef9LyBOxUo/HL3C3P7U6lwtXRC0c9kPKH1QMaFi3NHbq0f3VD5s070WP98qKyXlzieWJ77iaD' \
			b'E91jmcQJfXE231qvLrdeweU8i6rnMuDV7b7WqiNH5wfRKX4uc/LA5eSJy2mTj5OxDIGOqDY/QslCteBxpRYO0FLbaak1UlpR2quUX7CU+9XAGj6Ix7hDULN62+CNMn3gEXtt4Eceh6x0smHYLQPOTB2vgZ4LaCR0gKNbZr5f5vtoNpZmCl9JURKjyWeyaSiD' \
			b'lLuSqYaGLEmmp+fgQHZObhik5HRcisjXfdZ9Sbs0tXz7gV8SwOnfcQZznCMfZ31Hs2JndbQgfmwCvzSBXsJrY9nGSXGwhxR+yg0/BoZv7XCcLKTL4GhPeDY3OO8NpM00aDNwDJZ0MKfB+QxwHD6OH8eyhnMggWkN2tagAyEO2habdrEg4uAplAPsLY9z6EAe' \
			b'Dc5QjNMT43S3YG+Ds/HgBDw4JBT7AeCoKiwMeMeFI6Gx0mMVxQ7LkCeDwxwDOg/i4XwWOEp6QI1cd2TpdQupWIOr1+DKNdS/dYfhZrUeYHOD+yEIm7CWr7Gar7F+r6EEry1twX2Q2jW6ao31eo370SFr9Mwa3bbG6rLGaryGTK0tbobrrwdKAK71eBooPmvI' \
			b'wNrhVTAeXB+PwTq5phgNxsVTYB1cYwlYYw1c93htsP8abLKG/K4D7sFEQnlce0weZsbhCWFDwDxCTEwfpozPEzi3WKbWKEVr1CHOnKPzwyaDkaCKrwOlBP70ZBK8NFoMVgJeiAwCV4ACvwZfrD3GIjPDmSjtEHtA+7a40lIID4I1g/mjeLgB84B70T+WzgJ/' \
			b'BvwPFweXrgeMTgageBiFLAoXh2PB4esBUwYnxhyig6DwrKFyrAPGJS/iibEgQDVZezxfg4dDVKgna5CkNdTXtce8oDnxFLA9GElrS39gj8EyhPlBE8DvgOdGkwWMYciasAvLXQjfoDihJFVBqoLEglTVqKrRGdXIoBqVVMhlQtQUtIjudvkeVe5XJ7rky9LU' \
			b'nkCd8IZYb4VRGE4mVnZGsC5NqNoDxCrMCJZNooWjrVG4cJTTVvHy6AC/Q6b8WKi0Nm+TKs+xNFCULL9EtPzJZctzuuwgIU7liaXLz4jXxWqW31+1/JxuYfJEuzyp1079Wv3L3SIu/S0CMwy3wJL/xeEih4va+Pl4Xt2yNyf8OiW9XRk/RWMrDEsePSdzv8VF' \
			b'2teO5I+fhfmhd5sUtjPNA6SJ05s4n7SRzNPTQza1O8izemr1Lk2S0aa2C5zylNo0pJVj1BJR0lez2ViOWovfdcOPupHmQjz8XBl+hov0F+LhR/Fmddgt1GLwOc6SEzUZ/I4di47S5lb02YpG94frNM4sG7Xa76fXOL1C1OxOdDuIdsM2nOSRNNxnOo51Hp3Z' \
			b'75ByjJBrORaaxs5pOY2abxxrusSh40mrbAqKttOZRd55l0RQqafIqvUknNSmlTSfmqtwnUpvl/Qfj1wEAG7wshECOCgMGaDb4/45JqQUY+2IOcBD+vH6mBRiJKHF9FKj/2QfoUlMS9yDFZc3tJILsQ9NFpSOnyCHri/IyVKLIcydC7oVIRST0hOPNDiLJXLY' \
			b'IjLFosB8UscfQ6mRu4hWpp8gi86wkFlUhBhbuR9L6KJT+xhPAYabg5Njjc98aPmYiDSGmWlvyd++ucV7E+9u6baEGYdKeov3C6Cat3SnAPJzu2apgB3uf2k63i0Q7O+Lg21GwIX3/XfEPpvxz+3BwDn+zbFPuVeZdwXMc8w8t4N5A9WTMfYcbZqhnuzoOokQ' \
			b'4iabgoq87ImmzZaEPFd4vJk+4eD6MsLxsdOHnNHVZ+EW99phFHuyENqGPtFNjJf4Nn+UQk3tyg9KHGYXBQWZm2NYhrDReeX5SXPW5Nm0MUuz9HKL6aVeFXqJD4+iV0xlAV1uD3S5hK5kmCK5HJNLMqHgcgwuef6KXuP426k1odUMpPqjIPVQ8XSfWGoqmi4K' \
			b'Tai+ePFdLwBwiv5mjCbMezOHJoIS7woxlk1BgRKdT6DEuySCQokiz0GJjsygZJa+LpALCJSMPHOhQePF55iU9tphlNTJwkxyq5m2uUJ8oVE0JdOIw+wVpRFHLzTiYRlDJE3P76LRfb7Za4bngWQWN/RFjzKQ1H/HACmlch5IlK2FQCIHM5Aym5eAZPglhmZC' \
			b'gEQpEfObuJemYW32fYza8vjkDm9DfAQNiPfVeIgtAl19oLp8anEjotnViGgmjYiYydn3QbS162RviBFtCiq1stZD3iURIrXy1kNccbxN2cWx0cR9RrClDYdy+PSxapSSWYTFvXYYxZ4spXdL5fiKMDUtZ9oEWWUvBbGLcek4TXXxtdT4OvKApXls8gzbmLlZ' \
			b'ni1uHoy+Fp6JZ4/iWUxlgWd7tA2a1DaYGabIM24a1Ewoz7hlkLMZ97ZSHhc9YM3gyx/zXv/hPFWd44mqcumCuMQNfWZXQ5+ZtPJhBmdb+RhK0r6nsWwKKpSy9j2TLQlKpfY9M2nfM0vb9+QCGyDKrz4LorjXDqPYk6UIovnISiE1pDxISbOeyZr1zFyz3gg7' \
			b'oxMrdiRHTZ49G7Myi53F7XrRm4Id8d1R2ImpLGBnj3Y9k9r1MsMUscPtepoJxQ636xlp14t+4PiHYidU7FTsVOxQ3W+xJWAHdib94zBzvowdL9iRWDYFFTs+w45PS8JOqdccHZljZ2nPObnABnbyq89iJ+61wyj2ZCliZz6yYkcNKdjxgh2fYcfvws7oxIod' \
			b'yVGTZ8/GrMxixy/GjnpTsCO+Owo7MZUF7OzRe4/KhGAnGaaIHe7Ep5lQ7HjGjhfsqNs4/qHYGRA79HIKpWNQhjBAwhgaHpmQ5HyblkctHUQvHWli0jvROdQi0hjRFsq2Yb0Y8CtRBsXiEpZveKKQCukK6UcPaSQVXBx/tkKaAJ1B2vIxBUjzrhBj2RQUSNO5' \
			b'BNK2TUuENEWegzQdmUGaWLsE0nKBKaRHV5+DdNprh1HsyVKCdCGyQDoakiHNYUmpQJqjb4H0+MQCac1Rk2fPxqzMQZoOXwTp6E2GtPruGEinVM5Dml4mLoQ0uZYhnRmmBGk6s4+ZEEhTSsT4Ju5tWfcPhnTbVu5U7lTuWH5XZne9K7OTd2VY3mfflTF35EWZ' \
			b'xrIpqNzJXpTxLokQuZO/KBtxp59wZ+nLMbnABnfyq89yJ+61wyj2ZClyZz6yckcNKdyR12K2z7jT7+LO6MTKHclRk2fPxqzMcmfxq7DoTeGO+O4o7sRUFrizx6swm16FZYYpcodfhWkmlDv8KszKq7DoNo5/MHeOGuNauVO580C4E5g7YRd3JrMLWN5U4k4Q' \
			b'7kgsm4LKnZBxJ6QlcSeUuBMm3AlLucMX2OBOfvVZ7sS9dhjFnixF7sxHVu6oIYU7MhyYUqrcCbu4Mzqxckdy1OTZszErs9wJi7mj3hTuiO+O4k5MZYE7YQ/uhMSdZJgidwJzRzKh3OEBxpzNuJe4E47gzhHDkCt3KnceCnc6bmfrdrWzdZN2NjmmwJ1O2tk0' \
			b'lk1B4U6XtbN1bVoid7pSO1s3aWfrlrazyQWm3BldfY47aa8dRrGx8Ics+SXwTI6JRmHwREsyeDppaOuyhrZuV0Pb+MQCHs1Sk+fPxrzMgadb3NAW3cngUecdA56UynnwdHs0tHWpoS0zTAk8HTe0aSYEPB03tHXS0BbdxvEPBs/Wob8VPBU8jwQ8hsFjdoHH' \
			b'TMBjaFMJPEbAI7FsCip4TAYek5YEHlMCj5mAxywFD19gAzz51WfBE/faYRR7shS5Mx9ZuaOGFO4Y4Y7JuGN2cWd0YuWO5KjJs2djVma5YxZzR70p3BHfHcWdmMoCd8we3DGJO8kwRe4Y5o5kQrljmDtGuKNu4/gHc2fraN7KncqdR8Idy9yxu7hjJ9yxK9bV' \
			b'ee5Y4Y7Esimo3LEZd2xaEndsiTt2wh27lDt8gQ3u5Fef5U7ca4dR7MlS5M58ZOWOGlK4Y4U7NuOO3cWd0YmVO5KjJs9eysosd+xi7qg3hTviu6O4E09T4I7dgzs2cScltsgdy9yRTCh3LHPHCnfUbRz/YO4cMVa3cqdy58Fwp2PudLu4002406148tV57nTC' \
			b'HQnaFFTudBl3urQk7nQl7nQT7nRLucMn3eBOfvVZ7sS9dhjFnixF7sxHVu6otYQ7nXCny7jT7eLO6MTKHclRk2fPxqzMcqdbzB31pnBHfHcUd2IqC9zp9uBOl7iTDFPkTsfckUwodzrmTifcUbdx/IO5UwfZVu5U7rzteLRTt2u0UzcZ7YRluTzaqZPRThrL' \
			b'pqByJxvtxLskQuROabRTNxnt1C0d7SQX2OBOfvVZ7sS9dhjFnixF7sxHVu6oIYU7Mtqpy0Y7dbtGO41PrNyRHDV59mzMyix3Fo92it4U7ojvjuJOTGWBO3uMdurSaKfMMEXu8GgnzYRyh0c7dTLaKbqN4x/MnTrK9s64MzcJUeXPZfMHBQIujj9b+YMRcv7g' \
			b'HFtNkT+8K8RYNgWFP3Q+4Q/vkgjKH4o8xx86MuMPri/ij1xgyp/R1ef4k/baYRR7spT4U4gs/ImGZP5wmB0SxArGpYO2UGh8eqGQ5muUSRszNEchOnwRhaJPmULqwWMolFI5TyHcs5RCVDKYQplhShSiM/uYCaEQpcRJNn3yg6TxUAoNlUKVQpVCkULc26Df' \
			b'1dugn/Q2wDkey70NeultoLFsCiqFst4GvEsiRAqVehv0k94G/dLeBnKBDQrlV5+lUNxrh1HsyVKk0HxkpZAaUigkvQ167m3AJnPpoG0UGp1eKST5avJM2pihWQot7nMQfSoUEg8eRaGYygKF9uhz0Kc+B5lhihTiPgeaCaUQ9znopc9B9APHP5RCpk5mUClU' \
			b'KZQoxH0P+l19D/pJ3wMsx+W+B730PdBYNgWVQlnfA94lESKFSn0P+knfg35p3wO5wAaF8qvPUijutcMo9mQpUmg+slJIDSkUkr4HPfc9YJO5dNA2Co1OrxSSfDV5JlOGZim0uAdC9KlQSDx4FIXiaQoU2qMHQp96IGSGKVKIeyBoJpRC3AOhlx4I0Q8c/2AK' \
			b'nXVqg82pwq+HRaVJwiuPHgiPHPPI7eKRm/DI0aYSj5zwSGLZFFQeuYxH2ZJ45DIe4YrjbUolN6GSW0olPnaDSnkaZqkU99phFHuyFKlUjK9gUosKmJyAyTGYnIBJD9oGptHpFUyStSbPp415mgWTWwwmda6ASVx5FJhiKgtgcnuAySUwJcMUweQYTJIJBZNj' \
			b'MDkBk/qB4x8MprPOfVDBVMF0sWDi2RD6XbMh9JPZEHreVAKTzIagsWwKKpiy2RD6kJYEpnw2BFxxvE3BNJkToV86J4JcZgNMeRpmwRT32mEUe7IUwVSMr2BSiwqYZFqEnqdFYNu5dNA2MI1Or2CSrDV5Pm3M0yyYFk+OEJ0rYBJXHgWmmMoCmPaYHKFPkyNk' \
			b'himCiSdH0EwomHhyhF4mR4h+4PgHg+mskyNUMFUwXSyYBgbTsAtMwwRMA20qgWkQMEksm4IKpiED05CWBKYhB9PAYBoSmIYJmIalYOLLbIApT8MsmOJeO4xiT5YimIrxFUxqUQHTIGAaGEyDgEkP2gam0ekVTJK1Js+njXmaBdOwGEzqXAGTuPIoMCVXzYNp' \
			b'2ANMQwJTMkwRTAODSTKhYBoYTIOASf3A8Q8G03HfTb8LNl3Ch//2/TwtUqorkKqptHowtEK9gIuTbGyj1UDT7o+A5fiwArB4V4ixbAoKsOh8AizXpiUCiyIrsHDF8TYBlsS2VKUitjC8CFty+BRbo5TMYSvttcMo9mQhbHFWpuQqHTJkfcKjdTnrJsiqpFqs' \
			b'Y6IZtvJrnC7hl+axyTNsY+bm+EWHL+JX9DXzSz17DL9SKuf5RUVjIb+olDC/MsOU+EVn9jETwi9KiZNs+uQHjn8wv846CcNJ4GWJX/0lPmRVdN0tupo98eUmCOsPnRuVh87aXUNn7WToLFaQ8tBZK0NnNZZNQZ0bNRs6y7skQpwbNR86iyuOt+kMqbyGdbbL' \
			b'5kldOoxWDg9YVC1xDD+3HFk2StHsfKlxrx1GsSdL6RGsHF+nTFUjcuZNkFV2VVBjunTcFoqNr6Bzp0rumjyrNmZrjmJ28dDa6G2mmPr2GIqlVBbmTt1jaC1WS5eGOWXGKX/USa5AvjPigDiPKg+ztTLMNvqETXYw0er0DnWY7YXy6ohHLY/rcAx+WG3/RsKe' \
			b'Gwn7XY2E/aSRsBdtLTUT9kwsLO09E0uD2kzYZ82EfVpSM2HPxCKI5P38+kn7YL8QUqgOGHn6pMWlMf2fbySM6cNGwr64FBsJ5yNrC6Gs6mcGjTxiYV2y8nxFSdvKJYzBZ+K4QibZjGhqUyyEkwbn2wj7pXSKnpU2QvFjohPnYQ84kQH6kOV/o5Gw36ORsCc0' \
			b'4Zly8xRbCXtuJaSoBmmDz71Ze2HP7YU90ym6ko+c0KkD/OA9kWAJKsgt3m6A4twSs0E+bpHAUP1v+fPviVdnnRbiMpsP67PXg2bZ/s2GzC+3i19uwi8ssWV6OaGXxrIpqG2GGb14l0SIbYZ99ryFK1xNYpshx8Y2mj5rM1yKMjl8o80wT8lsm2Hca4dR7MlS' \
			b'olg5vrYWql050ybIKrsoiF2MS8dtay0cXUFbCyV3TZ5VG7M121q4mGTRy9JaKD49qrUwprLQWrgHyFyfWguTYYqthcwxzYS2FjK9nNAr+oHjH/xsddapJCqrLolV/rp4BXa85+8n8dAqu2tolZ0MrcKaUR5aZWVolcayKahthNnQKt4lEWIbYT60yvLoKvqR' \
			b'NkLeiDXVZm2ES4dZyeEb31LKUzLbNhj32mEUe7IU2waL8bVtUO3KvybIKrsoiF2MS8dtaxscXUHbBiV3TZ7VlK3ZtsFdg63MqH1QPS3tg+LXo9oH42kK7YN7DLiylprYY/tgSnDx+0o86Eozou2CPOjKyqCr6A+OfzC7zjoBRWXXJbHrirh1v89ZPPzK7Rp+' \
			b'5SbDr7C4lodfORl+pbFsCupzVjb8ymVLes7Kh185Hn7l0vAriY13ty57zlo6CEsO33jOylMy+5yVrjyMYk+W4nNWMb4+Z6ldOdMmyCq7KIhdTHbctues0RX0OUty1+RZtTFbs89Zi8dhRS/Lc5b49KjnrJjKwnPWHuOwMlZlhik+Z/E4LM2EPmfxOCwn47Ci' \
			b'Hzj+oayyZ52morKqsuoKWOWZVX4Xq/yEVZ42lVjlhVUSy6agsspnrPJpSazyOas8s8onVnFsVAifscovZRUfvsGqPCWzrIp77TCKPVmKrCrGV1apXTnTJsgquyiIXYxLx21j1egKyirJXZNn1cZszbLKL2aVellYJT49ilUxlQVW+T1YlfpdZIYpssozqyQT' \
			b'yirPrPLCKvUDxz+YVRc2mUVlVWXVxbFqYFYNu1g1TFg10KYSqwZhlcSyKaisGjJWDWlJrBpyVg3MqiGximOjQgwZq4alrOLDN1iVp2SWVXGvHUaxJ0uRVcX4yiq1K2faBFllFwWxi3HpuG2sGl1BWSW5a/Ks2pitWVYNi1mlXhZWiU+PYlXy1jyrhj1YNSRW' \
			b'JcMUWTUwqyQTyqqBWTUIq9QPHP9gVp11fouj+wZeWn/ArexR7ihzlDfKmWtgzLXwxfOwKr9rWJWfjKnyfEyBL17GVGksm4LCF5+NqfJtWiJffD6mKu/e59tx9z6/dByVXGDKlFmOpPTYYZS+yVLiSCGyQCQaj98meenM53m81HZmxGOZFp4HRnkeEuVL46H8' \
			b'4vFQ0U9MCPXKMYRIBiBC5HDwewyF8mkolJzObGt18zwWSjMgdPA8FsrLWKjoGI6/Dx2ICmedXKJSoVLhjqjAPRD8rh4IftIDASWo3APBSw8EjWVTUKmQ9UDgXRIhUiHvgTCigp1QYWmvA7nAMirE9NhhlL7JUqTCfGSlghpPqCB9DLxdQgU9VqjAnQk8dyPw' \
			b'pT4EflcfgkQF9ZNQQbxyFBXiaTapsEfXAXK0UIFPt50K3G9AM6BU4H4DXvoNRMdw/L2psHVmh0qFSoUrpQL3pfa7+lL7SV9qHGFd7kvtpS+1xrIpqFTI+lLzLokQqZD3pR5RoZ9QYWn/abnAMirE9NhhlL7JUqTCfGSlghpPqCC9pX2/hAp6rFCBu0V77hDt' \
			b'S72h/eLe0NFPQgXxylFUiKnepMIeHaF96ggtp9tOBe4JrRlQKnBPaC89oaNjOP7eVDjrfAl1dGl9o3EhFOH5UP2u+VD9ZD5Uz5tKFJH5UDWWTUGlSDYfqg9pSRTJ50MdUWQyE6pfOhOqXGBKkdHVZ4kS99phFHuyFIkyH1mJooYUosg0qD6s4kdc/a4JUMcn' \
			b'Vr5Ijpo8ezZmZZY1iydAjd4U1ojvjmJNTOX8mwu/xwSoPk2AmhmmyBueAFUzobzhCVC9TIAa3cbxD35zUWc1qNyp3Hnr+U263/Um3U/epGPlLr9J9/ImXWPZFFTuZG/SeZdEiNzJ36SPuDNMuLP07blcYIM7+dVnuRP32mEUe7IUuTMfWbmjhhTuyHtzP2Tc' \
			b'2fXGfHxi5Y7kqMmzZ2NWZrmz+I159KZwR3x3FHeSh+a5s8cbc5/emGeGKXKH35hrJpQ7/Mbcyxvz6DaOfzB3zjo7QeVO5c5lcAeVCy6OP1u5gxFy7mDRa4rc4V0hxrIpKNyh8wl3eJdEUO5Q5Dnu0JEZd3B9EXfkAlPujK4+x5201w6j2JOlxJ1CZOFONCRz' \
			b'h8PsEOUOR9/CnfGJhTuao1H2bMzKHHfo8EXcid5k7qjvjuFOSuU8dyivC7lDZYK5kxmmxB06s4+ZEO5QSsT4Ju5FRaQ9h3LnrDMNVO5U7lwId7hnV9jVsytMenYFPqbEHenZpbFsCip3sp5doU1L4k6pZ1eY9OwKS3t2yQU2uJNffZY7ca8dRrEnS5E785GV' \
			b'O2pI4Y708gptxp12F3dGJ1buSI6aPHs2ZmWWO4v7f0VvCnfEd0dxJ6aywJ09OoGF1AksM0yRO9wHTDOh3OE+YEH6gEW3cfyDuUOzBIDyn/ObDpeDn9J3HGAf2uLiURT2xFF3nUjqwn1PbgOVEKWm4y5mWMV2fNAhYGUYT3RjRGVLU90YhhRdS+YNiGGd7MZk' \
			b'k92YtKTJbkwBU3RkhilcXzy/KEbemOEmv/zsDDeYdghafiOUx58sRKphfpobIyXUzx6nc93IqkCLw5wChRZH3zbFzejEOsWNZK/J82o1RDSaAxe7fAZchrw+gZdeU6e5EY8eNc2NoYlGyQCz9MLw4nluDNWiOM8NH721awKd3sesCMIoOeIKE/fSRDdmhDC8' \
			b'YntL++lvj3+BZfA3BPo7UBxDuxFn1iDNoNy+3caySLENhPFkO8IsBhZDakKoiKctbNrSK40wNPukExGi6OgW9CMTNBASui3yv+RJROX+GJk3M33DFsp6lPMtMo4SHqW7F8nu86eHsIdEj8R5qzKTLJMeRyGOKhyVd152R5q7XHCX9eFSaS3d6Ud9jMpIsri7' \
			b'C1bUP1S+NfWrLkndwhv0qG7H6do6fvgzF7PFSqYStl281vkgchQsUivSKRUp1Jp2u9a4C5CbeOM7VNGZvZfstgjPUtHZ78aQbueuX3myG7s2VAVarEAm+zTWjArtp0Bm4d3O3DN7UYE2n8pPJELo+FkVMocqkb0iNbILFalfpki+Pa0qjRSJnz6PVSU6y3mV' \
			b'aSi3gpo2e9m2tzpR3q5OoQx9Q3eRSpmFKmXyJsqyUtljnsva+71XGjUMzr2Tau/4xgn24SfHAlolnFm69miYO8kT3DGytVuytFntcm+mKIn5/4J8YdPtfdxc0S0yQgkMabrF/Z7vVsrQLsc/8hmaRWLxDdfqX1CSbyFP1NDUHdnQ1O0jaNtfhSy69ZrTMTuj' \
			b'Y+bxPQRG3Zp7iZC9QACLGzB5epEAafKd6JnJNM3R55VY2yAu5N1A3lnnXP5iAQpDc+eaR3qXv0M4TPMw/l3qXlHn9F401zn0+yN/kIy6ho4p36J1Tt54icZRQXBcWlHwDHlJRE/ff5H4GcoVlodWp/hdt/QJZiwfLIq40tMNXn9vDe93I4ZVCBnx990adv8t' \
			b'YWcSsjkRq61h6KVTtYa51duLee+3rUPKHb8DvCDxgTp3/+8AM+EhvbkU3Tlcc7gr0CDdfdzZ3wVepO7g7ft53gWu/oW96Rp6LPQXpEHLdafFRnhIJaTowWnQXvqDxeg0rwQv9ObnnjsgcEdCPDD/LPQDVaD97nzYKie8/QnXKT2QNkwcpOsyJKi9ABmC3/5Y' \
			b'OcobncaNTVWaWJqw+lD35jWWpouSKHchKrWGzaRT7jixMlQQYjPStPFoOJF0tfetXqa9J+VaOpws77N/rlYkd603Ui3Kx0VLFgZQee5RsNwBN1ZYvs/crmRPoFrTWyxI/2l0yty7TmUaZfoLecg7o0ZVfbqb7uYjbULvXsoN1eVI0x3IUnsiWbJnlSVXZanK' \
			b'0r3I0gU2hj9EWTInkqXurLLkqyxVWboXWQpVlu5DluxVtpNfhAadu4PmVejORUvOXeiLodNf2wu4k+jJ6l9QkW5RYPHtP7ilSssDkZYDexxdubxQk/K9qwtd9WG93j9h5yLvbkn1oc7dog6T0vRVaarSXLfS+LMoja9Ks5/SXFKv6qo0VWkOUJpwFqUJVWn2' \
			b'U5qz951ePqfonsLTZ7N/XpsA9XcnQjigloTo4YsRVdMoSA0P66CZYNP/UwoUXw8TRpV1u1I1F6xUGxNXnliujHzUjFJ3kGydvd91la0qW3cmW20mW63IVjv6f1rZapfLVvuoZWsQ2WoPlK1T9bmusnUlsvVoJMtkkmVEsszo/2klyyyXLPOIJYvlyhwmV+5U' \
			b'Xa9rM1RthrprPRLJuPw39+cXnXM3RLlwC/QghTlVL+qqMFVh9lcYUpCH1zfo1ArDX1ji/9ehMH13u6aCT1/kwkpxu6YKYeG3J+U5VUfpqjxVeQ5RnlCVZ4nyhPj/wShP7Qv9UJXHe3q1ge2El6pCVFovvGs0z3p6ZhHiROz5fCUpP1SD6PCdGmRIemDXbjXq' \
			b'hlvCDhSUW5R2qDW3pK5QFW5RMKFYwy8/i9WO1A9Vly5Wi8wVaJG5BC06oK1HUn64Fp3kfmgvBaodrKsC3YMCUXl9LAPF9lYgss4Dam3u8IUWlu8GH8UMfUnE1Q7WVWnuTmmo5j+6IalLlYZS+xDfa3XNLTEG6gwGuLXn7B2sq9I8QKWhCvZ4R79vkxre8NDf' \
			b'oVt4nMIKOlj4ZaU5e5/oqjQPQWm4VtVpNmpnHRYavKlpAinM2bsvV4W5fIWhyn/27oDXpTBss8cpMC02CKOWBHxF3tInfXzteVyVZk5psHBdVr/j6xKaR30r02LfnJZuZXzteFwFZlZguiowVWBOIDC1f3EVmGY13Ftnmqowj0JhsDWGOsv46+xGDLmPnx88' \
			b'q9hARb6ozw6WxOdCXjhdjfKgd9cY9WI0CI1zKUoEm/tterTXrO5w0rc0eULA8oclx/SedvSrt3D1gJ++RDfBf9rs8s1Y6Qfa7OE02K/ZG9hhPJb2/psbCD9Zw2MaxcZ4a7ilalbBYySo+HQlMC5sw0oJwtauwCjgWPACpAWsCEkFS4OhobxixUeS25a+Wp0u' \
			b'CPf8qKCgFaihKKKooiij+J4VvIqKAmtQOtuAyoq12NK6AVMbKB/wnxLTHZ2YbrXgH12rx2v5bVeDhKIQmwWX7VGv+41/LRQdVth2cy+lwpVSAbUUvwxp6ANH3Vyi7Ea68IuLSZixx1YvafWT9AKJRv/4Y9rd6P9oP5T2bA1joHgjaAiNGBunGKL9lDF/hoyB' \
			b'qnf41U7IIJzsBP/wY7T4AVrMUDgwQ20pTyD4LZT/Fsp/6105j53dkk+4wM5/yPfxFiarF5Ka8T43ik15H/K8403RsMMCoLRgBJkwJ58kZ9Ms3dgyTUMvUBENSC7UT1RNmloDX47QMNpAsxVQVyHsDwWIShaF41wQy8Ix3oiF+7KV6TYP70HspsXpfkKsDseT' \
			b'5VHBIOlmUC9ggtPSyf/tSzeOPP1fPGDjMvv+30jkJDh/5bl0ddNQHpEKDmy9xFpDoDrjwrZpp7UKAv6u6xbe4e1bv/D54fx1zKxGiz4UmbtchmXx8InlbhNiuMiYKsTbC4ldPaaFC4W9TI3tVmdd2DbdURXGnaPOuHPUG786fMGmpWOOP981uIz0VVS3F46w' \
			b'ekwLF4pDH8xLnj+drmLj7BELNvAeeQp+KGz9tN4suXltVr3BCtS7FWTvrqqRzapSk6oTNqXRDS3EwzG1OMvm2asXniBb8A59smlz4ab/fhI84ZLOuBGiH7C4McOJL7qxcDkLx+jz6TV5aU3eVjB2Fwqzigu+YDDLFnzxsDDq8cvyi7EfayvSDp/b1WNa+JXE' \
			b'qIFoZ4lYhFp0/slwi83buuCLtnz9sKWlr48esLDBNlqNai0a16KwekwLFwpz4bUIu01cxMLmsrUOba1D2L/lES1cKLq7qUPtSeuRX518we49Bx3JZqutJzvq0rB6TAsXCnd3dQmdf7L6hP337mDBXnIHHcnW22hYqVVqVKWwy+UjWrhQhLutUuaUmMIOsXez' \
			b'YH/Tg45kI15wE0TeNnn+GhZWl7PgB6box9/1pbhH5N5NEgc3M+7VnLilGTFVvGG114J9Tvc6gPp2w63yjli9K+1jE+/fiKHvDe7jjcEl1kgcWrDPwjly+x20ZMGe/Cc/6YKFC87eDR0neQVw8nqKQ0TueMlHXxxxHjb7/g0mF/Oe7/w1168OWzhL7YFH71xw' \
			b'GM4dnbqwcFnar51FJP+kd1wnqs1Fj+O4r8ULjuXZ64DNRQdWHXh06OknjYaCVXbV/m07tdrHQmBWdXH86tfu1x50lXXerq52YR/t3+pUK3v0freqi5Obxf1aqq6ysofV1S7so+HsPjqkN9UhvkJNuvcF1eQ0kWjhwbHNI+wHh5MkPJCFnXhU951rdWK3eigL' \
			b'O7EOw9rhcLc6eOEBMOn/MefaOOnG2iS4x+kK+7iA1A5GOwqIXz2mhQvFcWPRHn6hwEmQHtHChaJ2n9pRKOzqMS1cKFwtFNsLRbd6TAsXitorbEeh6FePaeFCcdTYuMdQKNzqMS1cKIbVWxtomhveAJ7QDXwr2re4Ac1NG9GY3L+ihyfbvMCAU2jqFZwcE92O' \
			b'c3/htFFyXjsfG+crGf3n2N1GbHQ0HQHFYPLf9MzCfjQVHhYVORvPhefHUzRQDIeFgeM7ngSTimGQYseNvrjd8DR8OJ3f29FZYtHts+MMH9vjZJE8lSZOIQAxPQ6DxCkqcSIYna4SbEpTVbY49SRfJWCKLBZqGuDZ4KSVvGcYT+CHBZlz6RrcE2gruw4u/BaK' \
			b'Om4Z+LyQ0LgFvPjNzf8HtjLKLw=='

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
	def expr_bracket_2     (self, expr_varfunc):                                       return expr_varfunc
	def expr_bcommas_1     (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):           return expr_commas
	def expr_bcommas_2     (self, BRACKL, expr_commas, BRACKR):                        return expr_commas

	def expr_varfunc_1     (self, expr_var, expr_intg):                                return _expr_varfunc (expr_var, expr_intg)
	def expr_varfunc_2     (self, expr_ufunc):                                         return expr_ufunc

	def expr_ufunc_1       (self, UFUNCPY, expr_pcommas):                              return _expr_ufunc (expr_pcommas, py = True)
	def expr_ufunc_2       (self, UFUNC, expr_var, expr_pcommas):                      return _expr_ufunc (expr_pcommas, name = expr_var.var)
	def expr_ufunc_3       (self, UFUNC, expr_pcommas):                                return _expr_ufunc (expr_pcommas)
	def expr_ufunc_4       (self, expr_subs):                                          return expr_subs

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
