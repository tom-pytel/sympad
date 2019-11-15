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
		ast2, wrap2 = ast.base, lambda a: AST ('^', a, ast.exp)
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

def _expr_mul_imp (lhs, rhs): # rewrite certain cases of adjacent terms not handled by grammar
	def tail_mul_wrap (ast):
		tail, wrap = ast, lambda ast: ast

		while 1:
			if tail.is_mul:
				tail, wrap = tail.mul [-1], lambda ast, tail = tail, wrap = wrap: wrap (AST ('*', tail.mul [:-1] + (ast,)))

			elif tail.is_pow:
				if tail.base.src and tail.base.src.is_mul and tail.base.src.mul.len == 2 and tail.base.src.mul [1].op not in {'{', '('} and \
						 not (tail.base.src.mul [1].is_pow and tail.base.src.mul [1].base.op in {'{', '('}):

					if tail.base.is_func:
						tail, wrap = tail.base.src.mul [1], lambda ast, tail = tail, wrap = wrap: wrap (AST ('^', AST ('-func', tail.base.func, () if ast.is_comma_empty else (ast,), src = AST ('*', (('@', tail.base.func), ast))), tail.exp))
						continue

					elif tail.base.op in {'-sqrt', '-log'}:
						tail, wrap = tail.base.src.mul [1], lambda ast, tail = tail, wrap = wrap: wrap (AST ('^', AST (tail.base.op, ast, *tail.base [2:], src = AST ('*', (AST.VarNull, ast))), tail.exp))
						continue

				tail, wrap = tail.exp, lambda ast, tail = tail, wrap = wrap: wrap (AST ('^', tail.base, ast))

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

	# start here # print (f'lhs:   {lhs} - {lhs.src}\nrhs:   {rhs} - {rhs.src}\ntail:  {tail} - {tail.src}\narg:   {arg} - {arg.src}\nwrapt: {wrapt (AST.VarNull)}\nwrapa: {wrapa (AST.VarNull)}\nast:  {ast}')
	ast         = None
	arg, wrapa  = _ast_func_reorder (rhs)
	tail, wrapt = tail_mul_wrap (lhs) # lhs, lambda ast: ast

	# if tail.is_attr: # {x.y} *imp* () -> x.y(), x.{y.z} -> {x.y}.z
	# 	if arg.is_paren and tail.is_attr_var:
	# 		ast = wrapa (AST ('.', tail.obj, tail.attr, _ast_func_tuple_args (arg)))

	# elif tail.is_pow: # {x^y.z} *imp* () -> x^{y.z()}
	# 	if tail.exp.is_attr_var:
	# 		if arg.is_paren:
	# 			ast = AST ('^', tail.base, wrapa (AST ('.', tail.exp.obj, tail.exp.attr, _ast_func_tuple_args (arg))))
	# 		elif rhs.is_attr:
	# 			ast = AST ('^', tail.base, ('.', _expr_mul_imp (tail.exp, rhs.obj), rhs.attr))

	if tail.is_var: # user_func *imp* (...) -> user_func (...)
		if tail.var in _SP_USER_FUNCS: # or arg.strip_paren.is_comma:
			if arg.is_paren:
				ast = wrapa (AST ('-func', tail.var, _ast_func_tuple_args (arg), src = AST ('*', (tail, arg))))
			elif tail.var not in {'beta', 'Lambda'}: # special case beta and Lambda reject if they don't have two parenthesized args
				ast = wrapa (AST ('-func', tail.var, (arg,), src = AST ('*', (tail, arg))))

		elif arg.is_paren and tail.is_var_nonconst and not tail.is_diff_or_part and arg.paren.as_ufunc_argskw: # f (vars[, kws]) -> ('-ufunc', 'f', (vars)[, kws]) ... implicit undefined function
			ufunc = _SP_USER_VARS.get (tail.var, AST.Null)

			if ufunc.op is None:
				ast = wrapa (AST ('-ufunc', tail.var, *arg.paren.as_ufunc_argskw))

			elif ufunc.is_ufunc:
				if ufunc.is_ufunc_unapplied:
					ast2 = wrapa (ufunc.apply_argskw (arg.paren.as_ufunc_argskw))

					if ast2:
						ast = ast2

				elif ufunc.can_apply_argskw (arg.paren.as_ufunc_argskw):
					ast = wrapa (AST ('-subs', tail, tuple (filter (lambda va: va [1] != va [0], zip (ufunc.vars, arg.paren.comma if arg.paren.is_comma else (arg.paren,))))))

	elif tail.is_ufunc: # ufunc ('f', ()) * (x) -> ufunc ('f', (x,)), ufunc ('f', (x,)) * (0) -> ufunc ('f', (0,)), ...
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
			return AST ('^', ast.base, neg (ast2)), dv

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
		return AST ('^', _expr_func_func (FUNC, args), expr_super)
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
			b'eJztfW2P3DaW7p9ZYLoBCZBIihT7m+M4s8YmTtZJ5u7ACALH8SyCTeLATnLnYrD//Z43vkglVamk6u4qF2G5iyIp6pCHfB6+HFI3r/7y9dMvP//yxV+qv/zb219/hJ9w+/mzz76Bn6+evHz24nNwfPbyyVP5aeVXwe8nz198+UX4bYNDSQKffolpfP35k6//' \
			b'nZ0v6O8nz/76/dMnXz/7WtxfPAm+nyTn35LzK3ZSOp/Ai/8DBYoO8n767cvP/4530fHtZ9++ePrV34MLI37zEv9++0l4iJ3Pvvjqm79//Qzf8MXzF9+iUC++xTz97QnGf/7im79idp5/QQ/T3/98ibE/p3L6EkPlDZ/QE0+//OKLJ6Hs0OPl87/++zdBtpdB' \
			b'9pcD2fHu2X/CnydffAV/P/3kcwpD3xefSgmh65Pk/FtySgk9+/zrZ/jil8+/wN9Pn//t+afoeCqK+Ibk++pzyiRkOeT3v75+9pQifPr8s8+wxF48p0rwlGR58uJTLAcM+PKlvDCoD+XkVJ9Cbr8Jv1gTvnjy1dfffInPf0MF/+y/nqJeyOv/cNHjT8s6gVSe' \
			b'/gc4P/zxw4c/X7//8Gfm/gDuN6/fv/39+3fvv//xh58//P76fRYMzrf//A1Cfvrzl+D+9e1/f//6/X+H2w9//Pb2fbr5AZy/vP79+zfvfhbX+3f/N7n4fR/efvjwJrp+i66QzOsfovOnH/8ZfX//Pb7oH6/f/B7cv9EL2PuPX98kmf/xj9+SYFH+n3+Kzp9+' \
			b'/T3m45c/fv7+p19+y3KcJxQz/0deDsH5+9v30fvP1+/zJMERbv/IpXv944/B+eaP9z//v3Dzw5t3v/zyOmb/nx/epoz+8P71m/95G28/5IL9+TYm/cevP737NcrwOsZ/k3JHxR0z8i4l+Ucq+de/Rgl/+OnXdzGD75ISQJ6ohKHcv/309s3beAMVLBPotw+/' \
			b'v4sviUqPor37OUlPiQ5uPmRPfv/zn69/jh4f+Mnvqlc3decr299W7PDoMD3+8ZXpb+UW7ihGA39sZVxV29uBB0f04bkKQoIXOilW7cjHVTe60uCvK6PAcRt9yS951PRO1fOfDhLVnGjwUn7Hqxt4oRNcbcd/rKnqlkWFO3SCC15c95UB8Ti3Dh34ODxNgnT8' \
			b'x4FH294OvcJtbSw9YzFvqpG8GXMbfMWPPVpT3YBwrcX/0cfnd20jDvTDNMClkoskbyHPGAOK20quIFXFT3r+YzX4sNRwh07UGqkD8tPdZrfBnfkr/qnpxYb+myYEG3TArxb/W76pjXhy3knbqg0l0kVf8dvx0MlDDT1qRRVCg0CaJWr5T8fFCq7akMja8p8O' \
			b'onZcNHBXayq2DpP2MQBuJcAY/uP4jQaLlnLYquoG6wtqQzQIPja/c/KLXvgshKOcHSs03u54hXox9Le7t6Mn3e7tRIxRsv3u7eCh2uhMtNQkRIiRhxt75K3IWP6DlVbuoUmTIqDWaiXCwesVPxC9d73Sba25BkDl1lCrsH60lYOEQDioeZoVNxWM4AYIsiAW' \
			b'VI1hrNpQi0KA8ZVrQ/XHBkwBoEJu9IgpXVshAKa2D4HRP/lY8hGMJB/HPm3y6dlHBZ9acd1u+E9nk5DBy+Ve6ESX4z9Qfre3yYkuzQ0hPIK5pvreWWkhAvKoOwIOkPKm1QlEIamWNWIqgVrNfyy2Di4oeoDS9YSg4qDMtC2WnQnoIEAFnuwl942kiUhUdTrU' \
			b'sYF/8AEPqm+a/0B9upV7aNAUh/5jcfIj6MAC1vzHooeAkiYnlgAgg+tIaLl1BECgx5s2YBtUFUB6rE9U0W5jBMW0NhkKkE3iYR0yoTJiY9EVSx/Vg8DLWgDPG5vaMt36JBzwEqkCm4420dWKi3OEDhscLjiY+KBhYNaF7OjWkFxjr3QLT5Or5T8WW63gdktO' \
			b'fEFbsRCQy5vWZ3yI2VYkqer4j21is1cMCJgzzX+y7ocWbuoU/6GeB7+4U+REVxsCb+UW7kIAe0Hjdo6KH94s2qEOBzosdXLa8DzKZikjtg0B2LcRH3BBt+oVwAFkvYUk4Qfw3RCgYiWHuuAqADOoEaBTIC1fQWlAA/dwwSNQX1qo1S3UjhZaWAtA0GKPADsw' \
			b'VLTA6Rbv4RVQ+YAYuSsETR6jQ2zwahX+QsoNuBt4GbwV2mhXAY57VXldeVP5rvJwCzFAuhbEayEnLeBXC/pvQcOoMpCmQ2yDN3VYhaH0IRZEAl/wREkNQh+KC5lpIYutQU9Iv688igCPw5tbeHULWW8h7y1kvoXctw3EbLC7g/cO0A45GwCnbSCpRlU9XLrq' \
			b'TdV3VW+r3lV9X/UQGXML4kENgNYICACAYx10ZKELC/UfcRo6bE4jsEPLdbYC/bq+cvBoixlssKsIqkQFAXrDC5qqx3dCOARjzxict9h84R5UeoO6RA+6h2DIIN5i0eGP4liYdQzFjN4SKVIop/EK+7h0T2mXenAB9eDGs0Jb1hzyPGnSh+rBevct37ZKfqUe' \
			b'kPrIw8lvL78hIVIq+HipXlKfJHqKRf4FSS6vBr26sVQ5BuWblSyX6FRZchly2U2X2aic5kuHSgXqqTVcL606H5FiU5E25KTOK2oDjyaXblgu1T+qGIqBh3EDSolLpQDBJQIB1/Ciu8vT3U2rpQF2TdHhZeoQwbMvyrtM5d20KvTEG+4XhKKkQoxFJkUVCikv' \
			b'jyz/ks+zyV9WzXar1jn00rDYeeSCMXksS/02nL6DUqpA5NJyzrPlaOnzaxmKmqBBZQsaXqZOX914an0tStOB2B2I3WFWISsdlooumjtXzZmiuQvVXFc0d6Gas0Vzl6i5G++k02+k84KFwjPipozlLlWrVBA8m8mLH1QOuI6ieQ5YKwnvZE5YS9dVYksdMLK8' \
			b'5ktNuNCa0MlqqiyTeVYoZogbecPd3DJeP368TovOQUD2kcVJXqTGqhBDb9o4OpQ21sgCp+7kV1YkZQm7NRLehPjBXxC745d1oa12kn5DYhXFza33YLWmAuy5AHuGvp5HDbg8jMN2RAycgMGxfZniOk3J950UPNfUnit83zMz9VK/w7JgK1TVcYfkpgsrq9xe' \
			b'LCdiORHH/c8Gwpqh9q62uF+hERsVEResc6WIdorIMcg6rmqOEcH1cyUV4OGaS4zh0jErOV8q1W4RCaOzSVNWKLxExlWuC10wy/fB+i0Mv6Tj3lMoSYYYGXpzqsXNA8X08SI75WTbqNioURUzxQvRGciq2OK06OwydIbWwEpsS+G3KOeclEMWvqUlXYqyUANK' \
			b'7KyxLRU1namaqFFJoRYLnoedEWypW1e65JfYcjz1xXF7SFHhharQuKK7S9Ud81bR3eXpjrbO0TDL8qTUWXDxxG4/3AqlZEBISFH6Rw+rE8Wl/mgbvXoewbAYuFcIf7pGfCW0cVJFZPl1fvfod7I7FeeGqAWUGnTfOwY164aXIGQFQlYPZVGcV7yiCRPrpejj' \
			b'nloUzwl4UUsbTBA6MWWgJVtSRCdLImS0gA2nYx16ngj3fBaSt5KQohSLvk5t+mD6oCmeJigFe6qhP1XYUobbDKpKGW4uw66U4dYyZJBEo1fFJ5H0PFgoJXn0IMyXkltpo6h5NGJaGauYYKZPI9jMrNRI56ujlg89L9x7UQr4YAG3XGw9l+fQRqfXpXd0Shzo' \
			b'uZc/s8mg5UH1uYl90/L2XezcqdzK7YoV2fKe9HMT7KYNW7B7HpH2PMXTM3MH2Zt4h0bFGMGGmUvLRHX1CrZccGXj+qXOxr9CU/hi7HR2WiFsKRBDJWEH+zqszElZXzCYzcddacDn1oBxowjVUteWWsq1VJWC4ILoS3M9v+YqsyLOlFrKtbSYwJ9fLW15YwLu' \
			b'BaPaqsQGUQ/n+PommCa2cmC65s1D+IOjsls68B9/QME6HIutxVxb3wbLYJ1O/6UpRYrqOZ1y3tWFViLIrmaTFM0HmrPe2de2Qen4oyRO+OXATh4BVWgxZtHZMXZodcH+VAupc1oOIzzX6oAmMDSzVXZpnK+KsFR0dtgSzrcJButgSKPEgIbsYAoAn7U6O1Va' \
			b'27mqB03MNJuYaTYx08HETOcHY2GZ6WAbpfesVvFzOwcpmWnvbsL7hl+FFgYSqDmQaZf7Y13H4rAtXVnXXTjO6fpyCtKyNVmqZmWN+2TlqedRg5a4eQVcya/MT/RM/D13yPueBmu0VKn5jCPCACvdd0sWSbjCw1196eoxcDiO5LhT7xhFHGOLY3RyHFMpTrbs' \
			b'dbtUUuMBvikTOuelFppUMTKpYoJlPI/RDY/RDY/RjQzDjQy8DY2sifdDL8RI/yRazEu/wEXDJTPfS+mpdiCuGMYVU/qn51ln2DDFFBy+TOVZbmE8gL/6dQaipU4MVjsBwi7MbDAQdgyEHQNhJ0DY3crngzqc74Dk8EOxpUVcYIvouQb0rOKeNVop6dain+Ug' \
			b'KFAbvrhni9YvWes3rZxiiEVpqSPio0GmLVsAVg0oqVVgA7LU/+P9x8EiuaFizc3WsT05QVMnqnDclWTLKvxKKn6WFL8Him2itKPza0fwOsfg6Vj3LqjblVa0pj8CL+4Fj3hcxd8Kvmn5A7031BqofYUv9/b0RCnrFYjVl5JbuX2hibXUhFqqpHYidBeoPkOo' \
			b'dpVnjPaiKTa0aapXDXZ46cuNaCiBX2/0WW3kEulRpXiMs5aCQxUp0oLFTi+UEfaERwWqKEe0GMTy5SofZ7OlDFLuQPTZoqKilDJGEaMuvGjMsNJlFZpNg7z0JSAeni+P56jjIep4gjoeDY5HYOOZ/HjoPB6njuWKR1nj0f947j8e+o/vxgqNR6vgN9vw61+4' \
			b'UIa7RqFOKNwDCXIpnOaGQbXCk1kaLDYIx+OisHJDeSrce497x3HvM55SiYf7YIvBwsXSBeUpbAVQwAr3AGksdFQrhEFxKzy8BfKr8IBfPN0XV3NxfxAuwuNsG+RXYU3ANokHCOEeGTT6RLMs3D6Ie47w9Dg8xMJbqAI1aA086xYqTw1S1NB8atBnbdDdVLUH' \
			b'7wbDwQle2KRrbNM1NuYaNFlbuoEwELgGwWsMwJZRt3QH5VCD7DXIXUMDrbF11qilGttlrfFJTBRaYI3/WwzWFMfg4/h2yHeNDa5GTdfY3GqsBzVWhBpbWw0lUXf4ELS0GqpN3WMIJg6Nqnb4PObDoozg0WP2IDq+AkXFZC0WAYrdOM4wNuka61WNMFBj7at7' \
			b'fCtmB4q9tpgs6LuGWlxDvaodlQWk1WG5wU1PZYcvg/QoAxDg0bPFm5ZckIrFl4CPIl94HgIw05okAIfC0oMbqH01aK/2pDQKRZE7KiW8wxt4HXhiEUMlrT2VEZYPBEANqXuMSGWOyUO7qB2VHMoBcaEh1NBAamggtcOMYQFifjAJCOsVi9OSpvCNCt+IkmMJ' \
			b'w6/HtLEouWqR3iCox4f77xCCEHgK7Fw17BTMKZjzkJijEHPmsMZOwU3WHeXuY4QeUJ+gT7cDQO29YBA0hEE392hI6hbA0oXCEZ6dHyGpG8ISTigNoMkwPOEWvr0QRQXvDoCRm4cjVzmGJHaMYcklYHJz0OQeFpwciwoJuvhvHUC5JRB1+cjkIja5MTqhcBlC' \
			b'OcKogyhV/cveIQu6O+TBvr8Dnvhf3DhxALp4rOwDgIVx4CyMZSPo0ZoFL2QcADYjI9ulCNcMQC6OXnmYOgt4NIWwO8D3Po6oB0PuNsw34IyBTbMGMrpOX8gLQJkN3QkwZQYkzh+kCZQEomGXSb7zhJeCdqas8dtvBLIQD79utghs1QLAhXAkgAHwgtKhPLYB' \
			b'cC8g3AgQq/VgDGWaANkcCco6A+ZWwLkTgAY/KA8GapOBNTXyFudu9uM1Tu4gfqKC6FeAm26wpjQJwDFuxxAenFifCKQa8gtYzsHxisBOz0wiO4YItNPkF80luZUwLyKJYwz1PLmW/g+gv0Vk7ttMdmwSMS/4SJ43KjJ+D5dURgzj90z9T+TBmcI2x96tCC96' \
			b'oRYc3pIzSyYSP8gsI95INvF9HfFOcAb6oRfP0g/H3M9AoTJkPBT0vo2NBiVFrKS6tdQkEgk95SU2R1GUaxfjBaJC797KszgbG1Wp+ZlIXUxaFkgLmnpv7rBbwRSGoHeHvA8Ac1cTAADPKfu/dDLuHmrrFnfML5nREp0FKmtW0JnbQ2mBzgqVXQCVWaYye4DK' \
			b'PHX9Zocf2HCssJc4sfpYIS+byGt4JfKanTHBkEBeNr1oDXPJ+AR/d3grT31quJJCtR/nIoVZTj0wFUJ0q2ajs0DCUVLC1IyskJSVwY4Kuc6oaZiIEJPI3+SZ0TFWICW7j5PsAk4K+so4SdS5kZOi1FsJiVMJhJQKapaPLPORZCPQkWU6ktFTrHwcf4aLDpJQ' \
			b'd4Kpoe0MdB7ccyzvlCHUR8I7jnnn0JRXu2fOCyuNzHoFJ9YdJ6TjEum4wZVIZ3YurE2TYe3qgZITunETdJOLM0k3MVT7sfwpzHLqg4HRTFyWJp9MYx/Oa2+k/GyMm3PNMBHhGhG+yXOiY6xF82/8e4BsJMGcbESNG8kmir2VbDiVQDappGbJhifoQjYC2Tgm' \
			b'GydkE/TA8feSzQTJ2EIyhWSunWQ8k4w/RDJ+D8mQXT2TjDiV/Db8ZCAZP7gSyfhZkvGJZPxakvFCMn6CZHJxJkkmhmo/lj+FWU59QDJ7oo9IxgvJeCYZLyQTSjUjmWEiQjIifJPnRMdYy0jGLyAZSTAnGVHjRpKJYm8lGU4lkEwqqVmS8Uwyko1AMp5JxgvJ' \
			b'BD1w/GNJxhWSKSRz5SSDmIofozhkSaSaeZLBjDdMMsGpPP82/KSQDIfGK5IMRZ0kGQwRkuFXrCAZJSs+amLBZyDOFMmkUO3H8qcwy6nnJDMXV+UrO0QyShZ1FK/pKFnSiaWaSGaUCJNMEH6QEx1jLSIZtcCYICSYkUxQ4zaSSWJvJBlJRUgmK6k5klFsDhWy' \
			b'ISRDkkh9Uy7pQWQ8kmT648wRPjqqGZggFLa5crZRzDbqENsoioPvUzOcwzGIc8SJOVfCOSpxjhpciXPULOeoxDlqLeco4ZwJe7KBOJOcE0O1H8s/eNjyz4B29kQf0Y4S2lFMO0poJxRsRjvDRIR2RP4mz4yOsZbRjlpAO5JgTjuiyY20E8XeSjucSqCdVFKz' \
			b'tKOYdiQbgXYU044S2gl64PjH0o4vtFNop9CO0I5h2jGHaMdQHCs/U7TDQUQ74sScG6Edk2jHDK5EO2aWdkyiHbOWdozQjpmgnVycSdqJoaSk2Ytox4xoZ0/0Ee0YoR3DtCMGArFgM9oZJiK0I/I3eWZ0jLWMdswC2pEEc9oRTW6knSj2VtrhVALtpJKapR3D' \
			b'tCPZCLRjmHaM0E7QA8c/lnbapvBO4Z3CO8I7bGmtDllaYxvomHe6Gd7hGMQ74sScd8I7ybyaQ+OVeGfWvFol82p+xRre6YR3ugneycWZ5J0YSnuTZi/inW7EO3uij3inE97pmHc64Z1QsBnvDBMR3hH5mzwzOsZaxjsLDKZDgjnviCY38k4UeyvvcCqBd1JJ' \
			b'zfIOG0uHbATeYVtp1oNLeuD4R/NOe3a7fh6dfbbs9ykM9JEwEBuqqUOGapgRtlWjH2EgdGPWXOIhjkc8JE7MvxitqWS0xqHxSjw0a7SmktGaWmu0psRoTU0YrQ3EmeShGKr9WP7Bw1YF14CK9jwxoiIxXVNsuqbEdC2WbUZFw0SEiiQLTZ4fHWMto6IFpmsh' \
			b'wZyKRJkbqSiKvZWKOJVARamkZqmITddCNgIVsemaEtO1qAeOfzQVHdo7X6ioUNEVUhHCMCgRf/ZSkeY41vCPUJHm8RD+CBVJPKSi4FSef5ue4zMVcWi8IhVR1Ekq0umkE37FCipiQfh3TEUDcaaoKIVqP5Z/8LBVwZVT0b4nhlTEPhzSGylFG+NmVDRKhKko' \
			b'ZKHJ86NjrEVUxDH3U1FIMKOioMxtVJTE3khFkopQUVZSc1RE2nMxG0JFJInUOuWSHjj+0VREZyHQzh/mFSEVTXQyIpIOOSMi+7zlmEr4SnjaMXaSWR/jXsS6iDOCL4QhnjHDG8QEXZ3H9R1/a6EQdyHuQtxj4uZZTH1oFhNrOs9i6mwWkxC8oZ9A3ByPiFuc' \
			b'2GxkLlOnuUwOjVci7tm5TJ3mMvXauUwtc5l6Yi5zIM4kccdQ7cfyDx62KrgGxL3niRFxy3Sm5ulMLdOZsWwz4h4mIsQtWWjy/OgYaxlxL5jODAnmxC3K3EjcUeytxM2pBOJOJTVL3DydGbIRiJunM7VMZ0Y9cPyjifvQJttCRYWKrpGKPFORP0RFnuIgFfmM' \
			b'ijxTkU9UxPFanZxKfpue4wsV+cGVqMjPUpFPVOTXUpEXKvITVJSLM0lFMXQkPLaGXmXhNtwMuWjnqfTEiIu8cJFnLvLCRaFwMy4aJiJcJHlo8gzpGGsZF/kFXCQJ5lwk2tzIRVHsrVzEqQQuSiU1y0WeuUiyEbjIMxd54aKgB45/NBcd2otbuKhw0RVykeGd' \
			b'UwfPYMaqzZun6Ee4CN2aQ4SLJB5yUXAqz79Nz/GZizg0XpGLzOwuKpN2UZm1u6iM7KIyE7uoBuJMcVEKlbY+cyEViSunon1PDKnIyF4qw3upjOylimWbqGiUCFNRyMIgPzrGWkRFZsFeqpBgRkVBmduoKIm9kYokFaGirKTmqMjwXqqQDaEiw3upjOylinoQ' \
			b'GY+lokM7dgsVFSq6RiripTVzaGlN4iAVZUtrhpfWTFpak3hEReJEKpKlNZOW1jg0XomKZpfWTFpaM2uX1owsrZmJpbWBOJNUFEO1H8s/eNiq4BpQ0Z4nRlQkS2uGl9aMLK3Fss2oaJiIUJFkocnzo2OsZVS0YGktJJhTkShzIxVFsbdSkdQaoaJUUrNUxEtr' \
			b'IRuBinhpzcjSWtQDxz+aio7c11uoqFDRVVAR7/A1h3b4YqXmHb4m2+FLH2Fp6CdQEccjKhInUpHs8zVpny+HxitR0ew+X5P2+Zq1+3yN7PM1E/t8B+JMUlEM1X4s/+BhG10DKtrzxIiKZKuv4a2+Rrb6xrLNqGiYiFCRZKHJ86NjrGVUtGCrb0gwpyJR5kYq' \
			b'imJvpSJOJVBRKqlZKuKtviEbgYp4q6+Rrb5RDxz/aCo6cq9voaJCRVdBRWy3YA7ZLWBdZrsFk9ktGLZbMMluQeIRFYkTqUjsFkyyW+DQeCUqmrVbMMluway1WzBit2Am7BYG4kxSUQzVfiz/4GGrgmtARXueGFGR2C0YtlswYrcQyzajomEiQkWShSbPj46x' \
			b'llHRAruFkGBORaLMjVQUxd5KRZxKoKJUUrNUxHYLIRuBithuwYjdQtQDxz+WitTe7b/dtbFRM8NIaz5Z8ZispAszndaMoWczhv4AM3m20uXveNJPsGTo2ZKhT5YMHK/VyYmtqGdy0ulbejGCRIuWDP0cOWFIsGToV5ITC8K/Owe9dl0mT85OFLvNArUfy59f' \
			b'nvlJ4savWFCC+54bmzP0TFH0diNlaWPc3JxhmIiYM0g+mjxTOsYaUZQiA41Jk4b+ME2FRHOTBlHrRpOGKPpWkwZOJZg0pNKaNWno2aRBshFMGvgrgKwLl3QhdWSapgafVZpiq72bhgtbXShbFaY6HVN1vLLUHVpZgsLrOBq8sssWlzpeXOrS4pLEQ6YKTgjp' \
			b'ZHGpS4tLHBqvyFTd7OJS9oXqbu3iUieLS93E4tJAnKlhVArVfix/fiEqWxXiRqYirN733IipOlli6niJqZMlpljCialGiTBThYw0ea50jLVoMNUtWGIKCWYsFVS6jaWS2BtZKtQdZqmspOZYquMlppANYamOl5g6WWKKeuD4Rw+mLnwjsSJ6MmV271qYybgj' \
			b'2UmPGEqtHU+xKZ4+ZIqHTYFN8XRmiqfZFC87bUnuaDAlTm5IPJhKpngcGq80mJo1xdPJFE+vNcXTYoqn2RSP4BLrDYMNU9VArEnz8Biq/Tgfg4etCq6BdfieJ0bDKTHJ02ySp8UkL5ZxNpwaJiLDKcnCID86xlpmHb7AJC8kmA+lRKkbh1JR7K1DKUoFW0wc' \
			b'TqXSmj3xwnLFxSEVNymdmedpNs/TYp4XdSLyHktY5/fp9bIQVajq8QdRvBDVHVqIwh4tL0R12UJUxwtRXVqIkng0ghInjqBkIapLC1EcGq80gppdiOrSQlS3diGqk4WobmIhaiDO5Agqhmo/ln/wsFXBldPSvidGYydZiOp4IaqThahYttnYaZiIjJ0kC02e' \
			b'Hx1jLRs7LViICgnmYydR5saxUxR769iJUwljp1RSs2MnXogK2QhjJ16I6mQhKuqB4x9NReUsh0JFhYp2qcgyFdlDVGQpDlKRzajIMhXZREUcj6hInEhFVqjIJioaXomK7CwV2URFdi0VWaEiO0FFuTiTVBRDtR/LP3jYquAaUNGeJ0ZUZIWKLFORFSoKGc+o' \
			b'aJiIUJFkocnzo2OsZVRkF1BR0FZGRaLMjVQUxd5KRZxKoKJUUrNUZJmKJBuBiixTkRUqCnrg+EdTUTnLoVBRoaIdKrK8tGQPLS1ZjoP1M1tXsryuZNO6ksRDKgpOCLGyrmTTuhKHxitSkZ1dV7JpXcmuXVeysq5kJ9aVBuJMUVEK1X4s/+Bhq4Irp6J9Twyp' \
			b'yMqKkuUVJSsrSrFsExWNEmEqCllo8vzoGGsRFdkFK0ohwYyKgjK3UVESeyMVSSpCRVlJzVGR5RWlkA2hIssrSlZWlKIeOP7RVFSOcrhaKtKXR0f02YqHpCRkEoMBBygJM+KJkuhHKAndmD2fTkvneHRaujjDb9NzfKYk9o1XOi3dz1EShggl8StWUBILwr87' \
			b'p6Xn4kyelh5DtR/LP3jYquAanJa+54nRaemeKYmkNFKKNsbNT0sfJsKUFLLQ5PnRMday09L9PCXhqmc8MV0SzWgpKHQbLSXRt56YzglhlQ2npqcSm11D8kRNIStCTSSN1D7lkj44/tHUVI52uFpqujBaethREu+ntYf202L15P20NttPa3k/rU37aSUejZLE' \
			b'iaMk2U9r035aDo1XGiXN7qe1aT+tXbuf1sp+Wjuxn3YgzuQoKYZqP5Z/8HByDUZJe54YjZJkP63l/bRW9tPGss1GScNEZJQkWWjy/OgYa9koacF+2pBgPkoSZW4cJUWxt46SOJUwSkolNTtK4v20IRthlMT7aa3sp4164PhHU1E52qFQUaGiXSrSTEX6EBVp' \
			b'ioP1U2dUpJmKdKIijkdUJE6kIi1UpBMV6cGVqEjPUpFOVKTXUpEWKtITVJSLM0lFMVT7sfyDh6Ut6xEV7XliREVaqEgzFWmholC2GRUNExEqkiw0eX5SrGVUpBdQkSSYU5EocyMVxYS2UhGnEqgoK4M5KtJMRZKNQEWaqUgLFQU9cPyjqejQ0Q59ICH9sdHP' \
			b'/XxFN3BO4ZuH5xu4d/jxN7vGbsGw3YI5ZLdgiHgmv6GLNdkw3wQn2ioY5hv8DbYKZnAlWwUzwTe0LGySqYJZSTd1tFUwU1tk3eD/tL1CFFj7cR5SmOU3DCwVZuJy0Qzm4lrZG4syBUtuEihnGvTgxzlIuEa8kWxCPuhWR+dCWwVzmG+C9Lmtgihzim84L0sm' \
			b'4rAAuj7L/3pjBZYHS4KrUCyvWWsFw9YKFFX1KCqEZ3YLhu0WDHNPrO/85Ih7uuaOukpCPlBd72h6tenviH0BL+6QU6G93/GHfiMr6SM/8l4GSGWAdImEdfQAie287SE7b6yVbOdtMztvy3beNtl5SzwaIIkTB0hi522TnTeHxisNkGbtvG2y87Zr7byt2Hnb' \
			b'CTvvgTiTA6QYqv1Y/sHDVgXXYIC054nRAEnsvC3beVux845lmw2QhonIAEmy0OT50THWsgHSAjvvkGA+QBJlbhwgRbG3DpA4lTBASiU1O0BiO++QjTBAYjtvK3beUQ8c/9gBkj6/777bK2GjhjYcFlY6e1Zik297yOQbqyabfNvM5NuyybdNJt8Sj1hJnMhK' \
			b'YvJtk8m3HV6JlWZNvm0y+Y5vWUNMMpKyE1bfA4kmiSmGaj/OwuBhq4JrQEx7nhgRk1h9W7b6tmL1HTMeZI30NExK6Eky0uS50jHWMnpaYPsdEszpSbS6kZ6i2FvpSQpL6CmV1Cw9se13yEagJ7b9tmL7HbXB8Y+mp0NHOJzx/N3ZzNnlQ59AMIFcArEEQrlE' \
			b'MrkUIoFCRSLBn71EghHm5uCwjjVMHsGpPP82/KSQB4fGK5IHRZ0kDwwR8uBXrGAOFoR/x8wxyRZJQO3HMqcwyynmPDEXlyXIeYJ9OH8055MNWeIDzAaOD0pwfESCW3w+gltwPkJ4VcYAQTXbGCDlmxhgFfhLAgL+cqf2ob/jMxFCFgT9HZ+H4OQ8hFhbRb4F' \
			b'6E+of+gchIL6BfUvBvXZAM0dMkBzag/qKwom1Bcnor4YnblkdMah8UqoP2t05pLRmVtrdObE6MxNGJ1No34UUPuxzCnM8s8A9eevMeqLiZlTE6gfHhDUZ1syx1ZkbrEJmVtgQhZelaO+qGYj6sd8b0B9TiCgvhT3XtRn87GQhYD6bD7mxHws1laOvxj1Dx05' \
			b'UFC/oP7FoD6vt7tD6+1uz3o7Hv0n6+3Biagv6+0urbdzaLwS6k+ttzPqpwV3t3bBnQXh32WoHwXUfixzCrOc4gD1Z+K6nfV19uH87aB+eEBQn1fSHa+gu8Wr527B6nl4VY76opqNqB/zvQH1OYGA+ny3H/V53TxkIaA+r5Y7WS2PtZXjL0b9Q7v7zxj1i4XW' \
			b'GTLEJS0tYCtFlnCHWMLtYQlHwcQS4kSWcMISLrGEG1yJJdwsS7jEEm4tSzhhCbfLEgNxJhkjhmo/lj+FWU59wBgzcVmaAWM4YQwnjKFCZjPmGD4u/CFiN3kedIy1jEvcAi6RBHMuEQVu5JIo9saVA0klEEoqqVk+ccwnko3AJ475xAmfhHrN8Y9eOTi0Vb/w' \
			b'SuGVj5ZX+Ps47tD3cVy/h1c4mHhFnMgr8kEclz6I4/rBlXhl9oM4Ln0Qx639II6TD+K4iQ/iDMSZ5JUYqv1Y/hRmOfUBr8zEdTsfwXFi6Ov6jFdGn78ZPS68ImI3eR50jLWMVxZ8+iYkmPOKKHAjr0Sxt/IKpxJ4JZXULK/wp29CNgKv8KdvnHz6JtZrjn80' \
			b'rxzaZ194pfDKR8srnnnFH+IVv4dXPAUTr4hTyW/DTwZe8YMr8Yqf5RWfeMWv5RUvvOIneCUXZ5JXYqj2Y/lTmOXUB7yyJ/qIV7zwis94xY94Zfi48IqI3eR50DHWMl7xC3hFEsx5RRS4kVei2Ft5hVMJvJJKapZXPPOKZCPwimde8cIroV5z/KN55dCm+cIr' \
			b'hVc+Vl7p2TKqP2QZ1e+xjMK6J5ZRwak8/zb8pPAKh8Yr8ko/axnVJ8uofq1lVC+WUf2EZdRAnCleSaHaj+VPYZZTz3llLm6/YyXVi5VU3yRe4cwmXhk9zrwSxB7kQcdYi3ilX2A/FRLMeCUocBuvJLE38oqkIrySldQcr/RsQxWyIbzSsw1VLzZUsV6LjMfy' \
			b'Cu2AB2Q/8J3Oa6EXyCrAwWk/zHnfVNMdQTfN5VKO6R76uEpEBGyOmugH29OBr3RSm5ilIEpPtnZEN5aCTJqpNGmm+sGVDqycnTRTadJMrZ00i3vk1cSs2UCeyRMrMUsoFc+bjbKQnrWcPjYlqoqa+cgzJc09pnam0JRMoalsCk2NptBGjzMlhTw0eYZ0jDWm' \
			b'JOSB6WMrJ6bRFCl1SE0h4fzYSlHrNmpSvFlebZ9Lk4LIDgsTCfcu/CueUAuZEYJSPKGmZEIt5F5z/IygKAT/6hb/WnL35N+TG/lKMV0psgaAavtqH1ftspQnZjLCSUJCIwZi+lnIPXusuohmmE6ykcqAGtoJO6wA/Upgfim8HxpJ5HC+Bcb9etuqCNf7YNpl' \
			b'0KwEklXe+3dHQPAs+BLqEtwS1gagjcg6A6sBUzcC6jILqACd9fjoxBHyEeztGDBFfKtlg8IRUHawez1Ar624haC1wUIpQNR+cEJkipiEgERoRDgUQAgRpd2PKJNd34cEldh97Qu05NCC54hPwctR0HJc9446bBeNL1n3DJVccGZ/p6jr57DmeJxRx/Zc3CPh' \
			b'zM7QGAGnewDQgXAQp+2xNLrLACEc5pykj3MkEM2CUBheXhAQkcz5fwGlloDjoYCJ+AQHlSAZzjRcFFBRsU0ClcLSOA6sqn9B9b2DXNGAS68YcDULYKs9PXIltHIZWqnr7iZFdOr2dJOwnqD2bDZhBuGQf0It5zPkwrkLwwjW4+AeUc0Lmul8Ag3+uxMiG6Fa' \
			b'mDE7DtmodTwWukU0UwnNFGW3dLUmhnSoq/muFs6A0lQuWwhzfcCqLAskihFNJqBkYpdnoWiakY6tt7INpcZGX7fpQ194o6mzZrZNM4HuZ5c77g/1wso4LlG4BajXXSjy9UcMEvWyQSJOCj9I/2ymb2ZyFDvHPtp4oMjadQtRjHJ02UimumMGjrZZOHBUuSXq' \
			b'/OCxu49p73vtgpXuFwOQefhZqlPPUJ1D9ynrOpVZqjHYtKebpbLVq/NYW9tn1HFP62znBDH2EdbZMnjxF7++RpY1ZEnTkdXM46y3nSW64FzA46y3Vf/yd8BcNLHkzgVplqELLgQqFPIUHZpzQppjUAbtfk+z7Ha9S/loaoemdTVWlY8aZ47rxXCRzILN8V2Z' \
			b'/sIABtxoawuSPS7QjC1BH2vkhP/9NtAZTE4PJ6WvGYAgnZ5MfGucBDwHILJnhUU1Fji+wWyDJFwMyaabx5PMfj1AoWH9Y2CUfwB8WrJJamyp/lgYpc6/U4RKuAxgUvRK+kLXA8ESFs1xnSQcVj52T4lWrbZi07i7BMKv7y41j4JGORIpfQbDskdEooJCpzO1' \
			b'HiCQah69c3RuAHQP4NNuAJ/28cFnvAGwgE8Bn9OAjyngc+/gozaAj3p88OkK+BTwuRfw6Qr43Dv46MuapX50pHlsM+ozQ5cLAZaTo4giiS9tkeskqFH9C1rOHcIorqODMgqAXCiAbLHQuVwQYfq8FwyhpD/yhfITGuO47o4QHRrdHcIv4UlX8KTgyZniCXmd' \
			b'b6ekIIp1d4D5hCNnY0lccOQjxhGq7B/b4OYecIQPKuT/F4Ajnb6jg+waHOhgjW/uaqr1Lfx2hC8XZj9c8OVC8cUUfFmELyb+/zjw5cLMhwu+HMAXeBbKUzl7blhDcc92npZzciZQI8JUi0ZEEnkt0tDjB5FGEZyB9wLMQYzpqGneIYBD87gj7IS6f4ewqBCV' \
			b'eh49bbANLuhzhuhzXoijz3lliFI6G8RhYRYiDkdejTj4+An6NkfgjN1i9VtwpuDMGGeoYl7FCvQpcKblY+Evc67XuDtiFWgI6KDjAu0WQ96CJwVPGE9adX0WLUfgCRXPR7d2hN0V+laOx/6KoVkYu8U2t+DJteMJNalrNZFbACgU4+NdjdbQQ8HW6AFZNONJ' \
			b'MbcteHI0ntAD125xW4xbNHZQGvoOlS1WtwVHpnGEWu/ZGd2eGY6QaFcKIzgLS42yx4nalk7Ds8XqtuBJxBOsQWdjc3sJcHLV3ZIWuyUtd0uK0W2BkQQjusBIgZE1MHJhtrUoWjg+81EgZeoD6o99bGbZsLzliExsPBDnsaEG0z8vwMGCnoOdo08/sI9rZNuc' \
			b'+osDSvDGXmA3Rt1jV6YTvPmoMYc8dj5DQLsWh/83msfRa1AKanwX3ONR3f12e9DeG3GISuxQ96dv74AjqPfzuLa3BZQKKJ0SlPopUOp3/m8Fpb6A0kJQsgJK/TGg5B7XULeA0gOB0hUAkp8CJL/zfysg+QJIiyeHqLSOAKO2eoUgxAjE8MPYw8BjCXJsABsl' \
			b'MDPAGAKYiBMBG2Jb9tKGu5m267J2anfbUmw/2F6GbSM0i9giYmvASsKNwKeqT7U+1fjJyh7qeayYqSqGOoPFSXVFz1QRqghSGagS7Ogq6gd0g4Nn0PhptBDBO6qDIFtUEqB3oJr2OPUQ/E2oCSFvoCpuzg+gK8xWBJaoN5XrLqDBQIexzS/Wo4oNcKLt7ehU' \
			b'n0qn6pBam49XtSPemFZvDvgPqmI0HYICUx0VisGegKGArnqFHS0P/kgl8J+8be6N/SVL3q56paAQlcUA5bC41Xe34L6pAZ4bjI3xakAJ6KWhBrD/RG+qNfqh9nADawUqgGLGb5Z3+FFgqA2QXcgtZBZntTvsx+CMMvYtwwt1hd2qBisXwjhadPTZp8ehqkJ1' \
			b'QhsH/MU+KjyserpXmHuHPeGGhDGbhYHO7eF/9K4O3+X2vY0/ZQyt4PBrO+zqdjv/0veK+91QksJOS9GhIPhln4YOtVdTQqkdueiDObICwQcxK5HVjOSFDn32DzsEVo6QTv8HMaAfkd1hDBSZdnlhXxYQh4bRFE4Zc4+QMXhPi19aggzC2OME//iLYdRW635l' \
			b'hpq5PI2+SjqbR0h5Pp++OvwPh0lDHx6oKBmYDENxQJLdU979dN71bPZBXsgSYlU+PtwtEz0sFhwUIOG1vO8HsZKMbnVDO2L51CJDZ78hcBPE0wdepThx56xtpFghHIqLi9fNFzFSK43nmt3iRjYLRQ58TMWO8IWnzvqgAiTp3QsJdjJAwub+H05p39OHU87u' \
			b'Rs79ck5LNEqJbqnGgO85NhcS8hEvLpt2RXOC7EAJ3Gej0v36hoXdx/tpXKo6+gr92hWP7r0Uffh3cWwsz00v5MqizhV7O1nF6s8Bg3V1JpeijyHSlOA9v4qrhz5PnDXVo15cNiaWDVZqf78NyPtLb0OYMF5eZu37e73cfb/gqIsrzMyYcHlj0vfUnnCxYcOF' \
			b'iyMbk1DSd7HjNgXim4dpWY2+4NaFc3fZRZnBiTR97xfO5T3Aa5ZdXIlmJgfmK86y7svpmputdi+cVZwMWHLhkuSqJ7nA+tLqVrU6nH289otr0NFTOA/c5NBE4SwunilvSoNb1+BsdfUX16CjJ3mWD9FP1+hcdfILjW1WPcnFpkrDW9XwcDH42i+uQTMzIqdo' \
			b'eO0px3RoiHcPFxq5rXqSS29nzqS0v2Xtz1ZXf3ENmplEOVX7w5pxujboqnu60KZ01ZNciPcwzWKupSX21WkvNIw6eaL3f3FFcgXP19UiX139xTVoxvBlvta4tcuNWAmWQvuUYnfgHTc3HHOhReFRD9COARjqHYiF2yumw7iIfWmkqxopWr1e+8VWnDPmNvfQ' \
			b'SPPKcfoGq6v7vvINPhvS4WJvNzbcdSY9J2m74Idfhnj8NuyqLReaLW1MYuGl0PYeivme38MVq0yDraxNfXX1F9ego6fBoJxPQgqxfpyIHOZ17aujLtwqcuwz+RW2ga58GvKNP2n/Jtyyqsqc27rGjnudrv3iGnT0nNvFNXbciX6pF+toZqvPx6QjV13sxTo6' \
			b'2jDp5DpqjtMTYug6XfXVw18I96eJRBfr7Oj5qciYj6u2Oeo7rDpfHXvhXtcVj627lr+MFbh+d9mFKhAPUPkYLt6ze/TU08WrT1cfxcXqW7MZ7Wr2duIhR6suPr4o/V+d0FSiO3cj5xHJzYRx1TjbrWdnUTVsdTUXV4c1M0pXUx3w8LNrubg6mFId9lQHVV3N' \
			b'xdVhzRTU9VQHXV3NxdVhzWzX9VQHU13NxdVhzcTa9VSHrrqai6tDX73SHZ3HInDho4ecztWgB5Y1eXb4NQsOgPFqXltAIxQDz/sAfeGxC7hOb5iVOjUZW+G5eoP/HFvvxEYt0xNQH0b/lVhvgaqzU9kU1hn2l0PchifkYgzlHMXVXPeovmmpY1KPpKA6PPEt' \
			b'SyDVV5c9Z+hZqGuYKp2dm87N5fNp8dzZcC5tOJMWayZPe0Nir7BFQE2mveaYlpRfPzxaDp53PGsHr4CQjnw5vyDOK6jf6NNzutCIog9o77vb/w9a8Ybv'

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
	def expr_func_2        (self, SQRT, expr_super, expr_neg_arg):                     return AST ('^', _expr_func (1, '-sqrt', expr_neg_arg), expr_super)
	def expr_func_3        (self, SQRT, BRACKL, expr_commas, BRACKR, expr_neg_arg):    return _expr_func (1, '-sqrt', expr_neg_arg, expr_commas)
	def expr_func_4        (self, LN, expr_neg_arg):                                   return _expr_func (1, '-log', expr_neg_arg)
	def expr_func_5        (self, LN, expr_super, expr_neg_arg):                       return AST ('^', _expr_func (1, '-log', expr_neg_arg), expr_super)
	def expr_func_6        (self, LOG, expr_neg_arg):                                  return _expr_func (1, '-log', expr_neg_arg)
	def expr_func_7        (self, LOG, expr_super, expr_neg_arg):                      return AST ('^', _expr_func (1, '-log', expr_neg_arg), expr_super)
	def expr_func_8        (self, LOG, expr_sub, expr_neg_arg):                        return _expr_func (1, '-log', expr_neg_arg, expr_sub)
	def expr_func_9        (self, FUNC, expr_neg_arg):                                 return _expr_func_func (FUNC, expr_neg_arg)
	def expr_func_10       (self, FUNC, expr_super, expr_neg_arg):                     return _expr_func_func (FUNC, expr_neg_arg, expr_super)
	def expr_func_11       (self, expr_pow):                                           return expr_pow

	def expr_func_12       (self, SQRT, EQ, expr_mapsto):                              return AST ('=', ('@', 'sqrt'), expr_mapsto) # allow usage of function names in keyword arguments
	def expr_func_13       (self, LN, EQ, expr_mapsto):                                return AST ('=', ('@', 'ln'), expr_mapsto)
	def expr_func_14       (self, LOG, EQ, expr_mapsto):                               return AST ('=', ('@', 'log'), expr_mapsto)
	def expr_func_15       (self, FUNC, EQ, expr_mapsto):                              return AST ('=', ('@', _FUNC_name (FUNC)), expr_mapsto)

	def expr_pow_1         (self, expr_pow, expr_super):                               return AST ('^', expr_pow, expr_super)
	def expr_pow_2         (self, expr_fact):                                          return expr_fact

	def expr_fact_1        (self, expr_fact, EXCL):                                    return AST ('!', expr_fact)
	def expr_fact_2        (self, expr_attr):                                          return expr_attr

	def expr_attr_1        (self, expr_attr, ATTR, expr_pcommas):                      return AST ('.', expr_attr, (ATTR.grp [0] or ATTR.grp [1]).replace ('\\', ''), expr_pcommas.comma if expr_pcommas.is_comma else (expr_pcommas,))
	def expr_attr_2        (self, expr_attr, ATTR):                                    return AST ('.', expr_attr, (ATTR.grp [0] or ATTR.grp [1]).replace ('\\', ''))
	def expr_attr_3        (self, expr_idx):                                           return expr_idx

	def expr_idx_1         (self, expr_idx, expr_bcommas):                             return AST ('-idx', expr_idx, expr_bcommas.comma if expr_bcommas.is_comma else (expr_bcommas,))
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

	def expr_term_1        (self, expr_num):                                           return expr_num
	def expr_term_2        (self, expr_var):                                           return expr_var
	def expr_term_3        (self, STR):                                                return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1].replace ('\\}', '}')))
	def expr_term_4        (self, SUB):                                                return AST ('@', '_') # special cased for last expression variable
	def expr_term_5        (self, SLASHSUB):                                           return AST ('@', '_') # special cased for last expression variable
	def expr_term_6        (self, EMPTYSET):                                           return AST.SetEmpty

	def expr_num           (self, NUM):                                                return _expr_num (NUM)
	def expr_var           (self, VAR):                                                return _expr_var (VAR)

	def expr_sub_1         (self, WSUB, expr_frac):                                    return expr_frac
	def expr_sub_2         (self, WSUB1):                                              return _ast_from_tok_digit_or_var (WSUB1)

	def expr_super_1       (self, DBLSTAR, expr_neg_arg):                              return expr_neg_arg
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

	# set_sp_user_funcs ({'N'})
	# set_sp_user_vars ({'f': AST ('-ufunc', 'u', (('@', 'x'), ('@', 't')))})

	# a = p.parse (r"sin**-a[b][c].d(x)")
	# a = p.parse (r"sin**-a[b][c] (x)")
	a = p.parse (r"\int**-a[b][c] (x)")

	print (a)

	# a = sym.ast2spt (a)
	# print (a)
