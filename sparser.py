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
	# print (f'lhs:   {lhs} - {lhs.src}\nrhs:   {rhs} - {rhs.src}\ntail:  {tail} - {tail.src}\narg:   {arg} - {arg.src}\nwrapt: {wrapt (AST.VarNull)}\nwrapa: {wrapa (AST.VarNull)}\nast:  {ast}')
	def process_func (ast, arg, tail, make):
		# print (f'arg:  {arg}\ntail: {tail}\narg2: {arg2}\nmake: {make (AST.One)}\nwrpa: {wrapa (AST.One)}')
		# print (f'arg:  {arg}\ntail: {tail}\narg2: {arg2}\nast2: {ast2}\nwrap: {wrap (AST.One)}\nmake: {make (AST.One)}\nwrpa: {wrapa (AST.One)}')
		if tail.op not in {'{', '('}:
			arg2 = _expr_mul_imp (tail, arg)

			if arg2.is_pow:
				if arg2.base.op in {'-sqrt', '-log', '-func'} and arg2.base.src:
					return make (wrapa (arg2)), AST.Null

			ast2, wrap = arg2.tail_mul_wrap

			if (ast2.is_attr_func or ast2.op in {'-log', '-sqrt', '-func', '-idx'}) and (not arg2.is_pow or not arg2.base.op in {'{', '('}):
				return make (wrap (wrapa (ast2))), AST.Null

		return ast, arg

	# start here
	ast         = None
	arg, wrapa  = _ast_func_reorder (rhs)
	tail, wrapt = lhs.tail_mul_wrap # lhs, lambda ast: ast

	if tail.is_attr: # {x.y} *imp* () -> x.y(), x.{y.z} -> {x.y}.z
		if tail.is_attr_var:
			if arg.is_paren:
				ast = wrapa (AST ('.', tail.obj, tail.attr, _ast_func_tuple_args (arg)))

	elif tail.is_pow: # {x^y.z} *imp* () -> x^{y.z()}
		if tail.exp.is_attr_var:
			if arg.is_paren:
				ast = AST ('^', tail.base, wrapa (AST ('.', tail.exp.obj, tail.exp.attr, _ast_func_tuple_args (arg))))
			elif rhs.is_attr:
				ast = AST ('^', tail.base, ('.', _expr_mul_imp (tail.exp, rhs.obj), rhs.attr))

	elif tail.is_var: # user_func *imp* (...) -> user_func (...)
		if tail.var in _SP_USER_FUNCS: # or arg.strip_paren.is_comma:
			if arg.is_paren:
				ast = wrapa (AST ('-func', tail.var, _ast_func_tuple_args (arg)))
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

	elif tail.is_func: # sin N 2 -> sin (N (2)) instead of sin (N) * 2
		if tail.src and (not (arg.op in {'-log', '-sqrt', '-func'} and arg.src) or tail.src.mul [1].tail_mul.op in {'-log', '-sqrt', '-func'} or tail.src.mul [1].tail_mul.var in _SP_USER_FUNCS):
			ast, arg = process_func (ast, arg, tail.src.mul [1], lambda ast, tail = tail: AST ('-func', tail.func, () if ast.is_comma_empty else (ast,), src = AST ('*', (('@', tail.func), ast))))

	elif tail.op in {'-sqrt', '-log'}: # ln N 2 -> ln (N (2)) instead of ln (N) * 2, log, sqrt
		if tail.src:
			ast, arg = process_func (ast, arg, tail.src.mul [1], lambda ast, tail = tail: AST (tail.op, ast, *tail [2:], src = AST ('*', (AST.VarNull, ast))))

	elif lhs.is_pow: # f**2 N x -> f**2 (N (x))
		if lhs.base.is_func:
			if lhs.base and lhs.base.src and lhs.base.src.mul [1].op not in {'{', '('} and not (lhs.base.src.mul [1].is_pow and lhs.base.src.mul [1].base.op in {'{', '('}): # this only happens on f**p x, not f (x)**p or f x**p
				ast, arg = process_func (ast, rhs, lhs.base.src.mul [1], lambda ast, lhs = lhs: AST ('^', AST ('-func', lhs.base.func, () if ast.is_comma_empty else (ast,), src = AST ('*', (('@', lhs.base.func), ast))), lhs.exp))

		elif lhs.base.op in {'-sqrt', '-log'} and lhs.base.src and lhs.base.src.mul [1].op not in {'{', '('} and not (lhs.base.src.mul [1].is_pow and lhs.base.src.mul [1].base.op in {'{', '('}): # this only happens on f**p x, not f (x)**p or f x**p
			ast, arg = process_func (ast, rhs, lhs.base.src.mul [1], lambda ast, lhs = lhs: AST ('^', AST (lhs.base.op, ast, *lhs.base [2:], src = AST ('*', (AST.VarNull, ast))), lhs.exp))

		if arg == AST.Null:
			return ast

	if arg.is_brack: # x *imp* [y] -> x [y]
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
			b'eJztffmv3DaW7j/zgL4XUAEiKZKSf0scp8eYxMlk6TcNIwgct3sQvGywk7x5aMz//s7GTSWVSqW7VN0iLF+xxEWHh+T3cTmkbl7/5evnX3z2xau/NH/5X+9++Qfcws/PXnz6Ddy+/OirF68+A8enX330XG5K7hruH7989cXn4a6CQ0sCn3yBaXz92Udf/xs7' \
			b'X9Hfj1/89fvnH3394mtxf/5RePpxcv4tOb9kJ6XzMbz431Gg6KDHz7/96rO/46/o+PbTb189//LvwYUBv/kK/377cYjEzheff/nN379+gW/4/OWrb1GoV99inv72EYZ/+eqbv2J2Xn5Okenvf3yFoT8jPX2BvvKGjynG8y8+//yjoDt88NXLv/7bN0G2r4Ls' \
			b'XxWy468X/wF/Pvr8S/j7ycefkR8+ffWJaAhdHyfn35JTNPTis69f4Iu/evk53j95+beXn6DjuRTENyTfl59RJiHLIb//+fWL5xTgk5effooae/WSKsFzkuWjV5+gHtDji6/khaH4UE5O9Tnk9ptwx5rw+Udffv3NFxj/G1L8i/98juVCj/43qx5vissEUnn+' \
			b'7+D88McPH/588/7Dn5n7A7jfvnn/7vfvf33//T9++OnD72/eZ97ghNsbCvbuv3+DID/++XNw//Luv75/8/6/ws8Pf/z27n368QM4f37z+/dvf/1JXO9//b/JxS/+8O7Dh7fR9Vt0hWTe/JCcv/8eU//nm7e/B/dvlCo//uOXt0nQf/7ztyRNFPqnH6Pzx19+' \
			b'j8L//MdP3//4829ZNvOEYo7/yDMfnL+/ex8f//nmfZ4kOMLPP3Lp3vzjH8H59o/3P/2/8OO/P7xLOfvh/Zu3/+dd/Pkhl+TPdzGtP3758ddf4kvfxPBvU3ZIqVHyX1OSf2T6/SWK9MOPv/wac/Rr0jrIE7X+9teff34TI//247u37+IPqE+ZQL99+P3X+JJY' \
			b'tFG0X39K0lOixY8PWczvf/rzzU/xwQeO+V3z+mZn+8b1tw07BnR0Dv/4putv5Sf8IlcPf1wDXjt3WzzgXz7Egwh9eIROCrXjNGxzYxozNDvTdBoct/EpPUsPdiSM9vwHpNtp9guP9LD3yBaP0AkuZfmP65qdYlHhFzrBhRH7BvPIEnt0YHQQhgTp+I/Xt/IT' \
			b'ZKMkwANkUg7/34YnQ/5LteLAZ5hmh3nXreS9627DU3kWH+w0RVCgX4wO4jkRHNXAyQ78xxl4om7lETqxLEnjkAd7m/0M7uy55tuOXkdZbbo2eHfogLuR57f8Y9fJQ5bWUaZUyJSNT+XZ3gOTHujywU6T7g282NCbQRb6Y1kzKFpHGTSW/1iQ3fIb4NfOUD4s' \
			b'5nGIHjZ6dIb/eH5jh3mhzCjd3GCVwKLiV+ETl//ycsdHGFdBtvHlIln4acaPQtGWz93+z1FMv/9zIoQuH/X7P4tIu05noqVaL0KMHvjxg7yhgO+N0SIC1kFfPt5/lH7uDJczVG8DdQdrQdt4UBGIAPEM19Qpb0QpuI4IBRWgDLUzhAYIWUPjVajk2IapQUFB' \
			b'cetEcOgg9pA3UvCMz9MTR09sm554fqLSk56f6PBkp6kM9MB/rItCxkc+f4ROzIHjP6C/29vkRJfm6h6yipqgOmo7aQecB4tIwtgBJaJMQkN4nyLlgCINhzD8x2EbYEVRBGqVCHIqOEg4hbWj6QIGCBzBQ34kv1tJE/GmwQrS7z8PT+ABVTvNf6A+3cpvaLYU' \
			b'hv6jOjkKOlBhhv84fCDQY8iJGoDUvCWh5adnnAXdKhUpqQEowvoE5SDYRAE089OkLwAz6Q9KENCLvLku26wODkH/8PDGpbZKP4ckFgAUBTMokomu8Izzgg4XHD44mLugjmOmldRC/NlR8xg/Sj8hNrkU/3HYXgWXFTnxBW0joUCPasgpC4NTndOW/7g2Nnj4' \
			b'tWMJreI/qQcBP5h7bMt/sPMgrce25MRSH4LnrfyEX8GDw0KN9p4VP4RyoXZEDozvYnzsJTiK79rggd0TecIdFes4x4h4kBz0lV4DNEBTUdCiQSdYzwnXgZQAHAFOoUUCtgHSQEEPDegHGnvvmh6itD38h2dQhxTUdIWdA4XJKeyywDsdqVy1Dv5DNqAKWapn' \
			b'EBcuiA3lqeCxgueqBXfbQVk00NaxyXZN3zc9vLVtBtUMuhkgBAilQEgFIiroTikQSIFEmqARMqYgZwq7a0QE3G8DfaJ4HWIg1GoF+VGQIQU5UpDPoWsG2wzoAYnDyxW8XcHrFWRfQf4HCNdC0i38BO1AkUFlBtwZfDP0jYdraHrQimp63fSm6UFyCAo5Vdh7' \
			b'A21o7NBATw3AwGGvBzqn0C2FBoGQ7aHBGsR4aMTeNR4LA3PmEDIR83WDekLFQoLYvQXnLbZtCAlFeINlhw+g/OD2+gb1Az9BVLq1HKoTX8zULREj3QbyfY28SL8pqVruZ1juNwMXoBq4tFspuZ5LEksDy7nngqRSonuIprRUGyP3TgI4SYgKEZ70Up341lkJ' \
			b'FkNRRapIcf415vWNpcIv9JlpkjU4pTvWWdTVno5KvcypQ/QAldJproSuPRN5BAyxtlHt9lK7NTWKxxFKexZK20eUQcCkF/1oUxv7pTT2CsyXUlY3JBv11fpaZpdRZgiGXS2syyisG8UkigxPDBZVR0qLKhLVBI3kKohZlqw9bpaymrRfex69P4Vq5tEEhuDx' \
			b'JJERTp/5pm9AAbVlnEfLMNIVNzL8o3kB6voOFd0uowxhzE9lpSBZBZIoiznDOX7UDeSrqyV1LiU1tLWkLqSkVC2pCykpXUvqEkrqZjDSCe/C3HNYbiC11N7GRZSi6sJYSsvKU8dLBjemDeUr06iytCBdSyuF3fGkIgeqRX4BRd6FRSMuuYELdAgFOpB3HRgf' \
			b'MzDmhVWRjp/IypzhTjyu0wbfG2UEKTtuaoPMx/Nw+oZeRHdZlZNlXKo8dJfnnSCv5ec2DMutlCQJVYsqX/oYZM3Dc/F4Xmbtuf+Oa+uQG4WLojhQRhyok0WnKbqXxbeeq3rPVbrvZP1aajCvRCHpMLdYnqe4sWEpkaM5rtCOY3levmshbFuW1lWpGLTDuOBY' \
			b'd95WtbBauG07btuewdG7Oe2EZn9lWvJMNp7bp/e18rBahHuVrM9HRfDiK7c4GywJrFjRiFmODkMh6Jfq22prdxkdYTKm02xFp6td3JmWkeEtH8bVMjrTMkLzUi3Gi3CvhfHIy0e1pZxv4aDGtRjqwr0Wy5kUS0uNRpRYzUnud9ZMUX+rdpEvoWWAXjTvF6hF' \
			b'diFF1tlaVpdSVhUKL6WsaG8UDXMsDXPOgEgn9nLh9pdWRmM0KqudmfstAxTh0fbz8NQIvpzHFDyb1cvTju+tkfogq4jzGwG/k42GOOtCkWp1ueMSMwIhPNnMq1telsZkTZfXMKIlDUWo+r+rFkPQjRa23CSsLMhbmf2nFXVSvJU1edrDQ3YyvKw0ELqiPSHd' \
			b'tCTEU1+1fDaWD6bICu14QF4VebJpCs0vVZ2t0VlXdbZaZ7bqbK3OGNvQZFKzxR3Xu6q6ZdUNtqrqSIs37uooXpwL3X62UNSZzSKZKvK4lijDWjzgq2p0QqOyzOlZgaWJiB9qf2XTXEYr1XXSyFzx8UdnJfMN2YyyFWOfW1FdWckp3lt6VlLdqLB7oef11p6n' \
			b'SHqerQmC8xgDz4uhSJYHdU4mTBwHvs5SdTy3VPcNzyrrzOanX6N9dDW/efRSILy4WtggK+LMoN85wVJ/xVjqbW2Yj90wcXcA18Thmmtie82Zd7UZPnoz9LIC5vU110Rfa+Kj10TFU9e4qUfzXh4tBy8b3hOCNxzq3NLR4XiDEjPhuF0jVrzmNhiQmnTWKE23' \
			b'UVBQvuEVx3qqxSXUCs3l1Um5t1LOiu52CIWMN1CuEfMLDsQxe3nacQUw4itHcaEJAD+n6kZ1rx6gdi7Fj/YXNAVUjfPPp0hQCyY7YAYnpQRTTbDi0GK9QbN7FVDPq/j62prOpTjQfsmw/ZJh+yUT7JdMfvgP6sgEQxxzYGGG2W18hozqph/bicc38obOB0/D' \
			b'nvxaplNrWBxraa2hrlHODS2sq2fAzA67qC7VNdqT9TfMQwEt0bLdcbA/FrOCnsdKPSNF39GIiRbfKDH+WgMutlEDd9zuKfJ3dOYL98NlaY4xwnMgx/J4hjTPCXp+nfdpqNbVsfajj7VbLAUaDnfBAJdHWx2PtjoebXUyoOpkCNXRGIkYIHT2ZEiWDHOFIWy0' \
			b'zujm+arX/H5+Q08vqD2Tc6gjvB7f7Z+94lTdInUpRei4IfMA7Sond4lwrBjcWYE8G0arDHmWIc8y5FmBPHsrn6GwOFEIyeH3GGutv4Ba33OJ94ZvXIJNxDRbDVaPajiOx6SOWwa80oWvVLnaIi6pRdwoGYWi6hx1v2y0xnO1NRxnEEvVHtHEUTeXd2vG4zMd' \
			b'NxEv5OFF2577yNQXVnhcHZ5Uhx8KxI/z1abx+E2j5++y91xkfRdLsJd2IqMcL+OWXu4y9a1csGulGLUlHdOSuqqqIynYWh6mK1kUV3zWQUWOc0AO0wwMGYOUDJsetA1+5rvR9D0uXErGb3INWZVjJfRYhDhHZ0J5DKTyTjpQ0qvKtMdZsEGgvHD384WZ0pKd' \
			b'fa1w1SGNaqoVVIOiwr2UiqZCjJYR2ItAIETMw6Og8cBjPOQXT/jF433xKFs8xxbPbsXDofEkZDzvF8+exoOn8dRpLBKstXjcAX6uBz8Eg+sPuPiAhY/bpKCUNU4wgmwaT0uA+qih1DUeCoY1uEXdQTg8rAUPWcAz3HB/LRqQ4Ckb2DxQuVjVUbEaP+uOJQjP' \
			b'oXJq3PVvsDghDuRX48Y/XBTDdUvcdGWxiUA8bHRY8rjxAI250W4UTYVwbxHuY8C95wMeM7+DkoLM7fDj4PS1eyi8HbSRncFP3MMzuIFAOxB0B5nfYZvdocp32Fp3UIA7KMcdFsRO438HPzCIwUSheuywTe5A5h0+gRa4w8LZYdvbYcPDz8zvsKzoy/YKoxvy' \
			b'h8cD/cLkDcYzGMXgsxbjtPgTxYVC3llMHN4LtWXXU9KQImhl5zEmJmsxg5g5CIkSYEJQXeij9yyn4WwOKAf6YE3aQRvd9fg6lBOq0s5hsBbzDQlAHdp5FBAKcGcx/yi7wtxg1jBZSKNHmRXFIxdEsPgSDE+6h+CQEGaScov61xgP3496gN8DJYyxMAOIUjtK' \
			b'EX/Aa/A3KnFAPZCeIEGLygEPj9E0lgqmCnVi5zFai7mBOFA5dtAQdtAQdh6Do9pQffDc9ywKYvQOwXmH6VDhgduRpiFKT4lDoj0GQzX3+L/7DvEFUaViynVhSgWUCij3BSgaAWUOSNwUlvjUv5PuYZcmewRayv6ebe8eYLArSp1Q6TCuxRuzgDmXjDVqhDd2' \
			b'hDkt4w5uAjqIPR517RdQxs/jjG88Yw07xnjjE+L4Kcx5MNTxLKDxTfp3CvL4Jex5GpDjx6CDYmXA4wl6/BL4NP9yz5DI/DOksh5/uP9B2+4FROLB6hBwicZj+Wh2jE40eB1NSPMsdZq0nsMrGlmyWdMxwCWjSF2MH+eGpIJje6NqATSfRrqqxDbSiZWxOg9r' \
			b'0+LseNA8HmGHEXuap4inY0VszK3hbcLJfM4SzUNwNgG/CETYiYN5t4yh+KGnRRwFf5xdKPAUwuDHojbhaifY6gRf+/UYi589CDgLNeU4rNUZ3rYjzO0T7uIJ8T3W3yHDYGzLWHB2AYYhAGIdvItugsbo1nJjTMaKYxmVg5Pme3rGZnodwzN7xytiNcXZA2vC' \
			b'HEZrmoqi2Rp7GnKTNFja7QR680RX+r+H5kli47MctH2RHdISv4q0kyH9+A1T/yMbSD4GeepF6JZSpaMo5A05UWTCsOKZNOQxckd8lyUaCc5lNuFQhwklFHxGK6GMt5FLWS5EMuoUpqFcMtnkapojnBDAZWFz6sHkAvvkio1ExBTk4AZtmJkIoeLZjpqyfgZa' \
			b'+h86GPIAM9mju8sXSkiBjQIT5TPmx7KRPcBIgY0qE50pEzlmIrfARKg0Nz8owFbihIDEqS3fW3oU+ccVV+IfN8k/LvGPSy85gXwcc4+boJ487T3aiT7Gj2VPfo5fEOiGcFbPBidZhGhErSoUAWeZhiA6eGUMU6gh8IvI0Gd+SC4SaplbjhishMRybpGMbOSW' \
			b'JPIGYnGJWJJ6ZnlF9GVTTc1ZxWWsEhNbyyn2DuZfNhLK41PJWhqpA5oLphHPNLI0r6QOTCwpWrNmDhEncogXDvGJQ3xxJQ6ZnHBSacaJkz+BPTyzh59gj1yQPfaIPsaPpU5+jl9QDFYOBC9mrOgBP+9b0VmIXlJHnkSkDhGgz/xoTYZDLVOHP4I6JLGcOiQj' \
			b'G6kjibyBOtIEWKaeWeoQfdlUQXPq8Bl1xMTWUoer1FGp46qoY2DqGJaoYzhAHRyfKoM4kToGoY4hUcdQXIk6hknqGBJ1DCdSx8DUMUxQRy7IHnVEH+PHUic/NjQtqWMmLAlSUAevd5BkregsRC+pI08iUocI0Gd+SB0Sapk6hiOoQxLLqUPk3kgdSeQN1DEk' \
			b'6kjqmaUO0ZdNFTSnjiGjjpjYWurwlToqdVwTdRBW05rhYepAnznqwAy2TB3BiY2jZeqgNzB1sG+8InVQ0D3qQLdQBye/njroJSTgHnUUgoypI/kYP5Y6+Tm+5dQxF5YEyamDHnAe+6CzEL2gjiKJQB1BgD7zw5PqJNQidXCow9QREsuoI2RkG3VkIp9OHRhd' \
			b'qCNTzxx1BH3ZVEEz6qBCEOpIia2ljn7d8vxTIhBfOeSqOUQzh+glDtEUxsltiknYi5hEnNhKtDCJTkyiiysxyaSRJj4NTKJPZBLNTKInmCQXZI9Joo/xY6mLiI7fUZDJgeAlmWgmE81kooVMgjIzMsmTiGQiAvSZn1cx1DKZ6CPIJBRNRiaSkY1kkkTeQCY6' \
			b'kUlSzyyZiL5sqqM5meiMTGJia8lkqGRSyeQ6yaRjMumWyISuHe9DnCYTDkFkIk5sJZ2QSbK31eWVyKSbJJMukUl3IpmwAS4Zf47JJBdkj0yij/FjqYuIjt9RkMmB4CWZdEwmHZNJJ2QSlJmRSZ5EJBMRoM/8kEwk1DKZdEeQiSSWk4lkZCOZJJE3kEmXyCSp' \
			b'Z5ZMRF821dGcTDLz4JTYWjJRbWWTyibXySZsJayXrISxwltmEzvDJhyC2ESc4d7So8gmtrgSm0yaB+tkHqxPtAqml5CA+2ySC7LHJtHH+LHURUTH7yjY5EDwkk0ss4llNrHCJkGZGZvkSUQ2EQH6zA/ZREIts8kRRr8hsZxNJCMb2SSJvIFNksVvpp5ZNhF9' \
			b'pZAFm2Tmvimx1WyizmsfysXuQKm8csG8wsZaeslYCwVney26Ca9oppacXfgXsYs4sb2I4ZZOhlvsG6/ELpOGWzoZbukTDbc0G27pCcOtQpA9dok+xo+lLiK6NrgKgjkQoyQYNt/SbL6lxXwr6jMjmDyJSDAiQ5/5IcFIqGWCOcJ8KySWE4xkZCPBJJE3EEwy' \
			b'38rUM0swoi+bqmlOMJn5VkpsNcEsbb2uBFMJ5qkTjOHDLPB2kGCwiisiGLoJwaBby40JRsJhxQhOPqprJ8dZBYJh33hFguH91mOCwadCMJz8eoKhl5CAewRTCDImmORj/FjqIqJrgysnmEMxCoKhB5zTvhXNhegFwRRJBIIJMvSZn0+hFgmGQx0mmJBYRjAh' \
			b'I9sIJhP5dILB6EIwmaxzBBP0ZVM1zQiGCkEIJiW2mmBoJz1temG2EKowRBIjerBIBgm1ZyCbwDqC5yAAKcAXgY3BjMFEQISAwjEg9AM2fNOcwfUdn0Vfebjy8JXzME8gmqUJRKzWPIFosglEdGu5CQ9zOGViFOJhmUY0aRqRfeOVeHhyGtGkacRTDxcwPI1o' \
			b'JqYRC0H2eDj6GD+Wuojo2uAqePhAjJKHeSbR8EyikZnEqM+Mh/MkIg+LDH3m51UMtczDR8wkhsRyHpaMbOThJPIGHk4ziZl6ZnlY9JVCFjyczSSmxFbz8NIez0owlWCePMEMTDDDEsFwGCSYISOYgQlmSATD4YhgxIkEMwjBDIlghuJKBDNMEsyQCGY4kWAG' \
			b'JphhgmByQfYIJvoYP5Ya61vyd21wFQwzzF4jhhmYYQZmmEEYJig0Y5g8icgwIkMuEDKMhFpmmOEIhpHEcoYRuTcyTBJ5A8MMiWGSemYZRvRlUz3NGWbIGCYmtpphlraCVoapDPPUGabjLT7d0hYfrMe8y4duwjDo1nJjhpFwWDGCE9pLJ9t9urTdh33jFRmm' \
			b'm9zu06XtPt2J23063u7TTWz3KQQZM0zyMX4sdRHRRVdOMIdiFATT8aafjjf9dLLpJ+ozEUyRRCCYIEOf+QHBhFCLBNMdseknJJYRTMjINoLJRD6dYLq06SdTzxzBBH3ZVE0zgumyTT8psdUEs7RhtBJMJZgnTzC8VtUtrVVhJea1qi5bq+p4rapLa1USjghG' \
			b'nEgwslbVpbUq9o1XIpjJtaourVV1J65VdbxW1U2sVRWC7BFM9DF+LHUR0bXBVRDMgRglwfBaVcdrVZ2sVUV9ZgSTJxEJRmToMz+fQi0TzBFrVSGxnGAkIxsJJom8gWDSWlWmnlmCEX3ZVE1zgsnWqlJiqwlm5bbSSjCVYJ4ewfAG025pgynWYN5g2mUbTNGt' \
			b'5SYEwwGIYMSJBCPbTLu0zZR945UIZnKbaZe2mXYnbjPteJtpN7HNtBBkj2Cij/FjqYuIrg2ugmAOxCgJhneadrzTtJOdplGfGcHkSUSCERn6zM+rGGqZYI7YaRpLJyMYychGgkkibyCYtNM0U88swYi+bKqmOcFkO01TYqsJZuVW00owlWCeHsHwKn+3tMqP' \
			b'FZdX+btslb/jVf4urfJLOCIYcWq5t/QoEowtrkQwk6v8XVrl705c5e94lb+bWOUvBNkjmOhj/FjqIqJrg6sgmAMxSoLhVf6OV/k7WeWP+swIJk8iEozI0Gd+SDASaplgjljlD4nlBCMZ2UgwSeQNBJNW+TP1zBKM6CuFLAgmW+VPia0lGH1w96m9Go7pp2mm' \
			b'r1RzVVSDjR1XM/sFqgGFYb3uecm/z5b8e17y79OSP4ejJX9xasv3lh7FJf++uNKSfz/FNvg0LPn3p7ENvYTftXd0pzWZJHtr/tFH2vfMhTlwbQgbvx4gC//z8UYL/z0v/Pe88N8z6US1Zgv/eRJx4V+KKffDhX8Jtbzw3y+TTkgsX/iXjGxc+E8ib1j479PC' \
			b'f1LP7MK/6Mum2pov/PfZwn9MbDXpHNykWkmnks5VkY5lEwC7ZAIAysI6y1YANrMCsGwFYJMVgITDuhGc2vK9pUeBdNg3XpF07KQVgE1WAPZEKwDLVgB2wgqgEGTMOcnH+LHU+TXwATsSNnIOnd1yKF7JOZZtASzbAlixBYhaTZxTJBE4J5RSn/kB54RQi5xj' \
			b'j7AFCIllnBMyso1zMpFP5xybbAEy9cxxTtCXTZU14xyb2QKkxFZzziXvW1XEOabOpz1ZvtHrOAd0tsc7bjhlwMPcY5a4B+s9E4/JiMcw8ZhEPBKORjvixNGOEI9JxMO+8UqjnUniMYl4zInEY5h4DBOPQijFmkKpBkPnXKC9QU/0MX4sfRHRRVdh53wgRjnc' \
			b'YeoxTD1GqCfqNRvu5EnE4Y7I0Gd+ONyRUMvDnSOoJySWD3ckIxuHO0nkDcOdlppGHPIkFc0em5Dpjeqq5nijoU9GQynR1TR0Zt+Jrgs6lYAefsDDp4japVNELV002slOEUW3lpuMdjgcjXbEiaMdOUvUprNEbXml0c7kWaI2nSVqTzxL1PJZonbiLNFCkL3R' \
			b'TvQxfix1EdG1wZWTzaEY5TiHjxO1fJyoleNEoz6zcU6eRBzniAx95ofjHAm1PM454jjRkFg+zpGMbBznJJE3jHPScaKZembHOaIvm6ppPs7JjhNNia0mmHouQCWYqycYthiwSxYD+ElythiwmcWAZYsBmywGJBwRjDi13Ft6FAnGFlcimEmLAZssBuyJFgOW' \
			b'LQbshMVAIcgewUQf48dSFxFdG1wFwRyIURIMWwxYthiwYjEQ9ZkRTJ5EJBiRoc/8kGAk1DLBHGExEBLLCUYyspFgksgbCCZZDGTqmSUY0VcKWRBMZjGQEltNMPVcgEow104wjqfN3NK0GdZInjZz2bSZ42kzl6bNJBxWjOCE9uJk2sylaTP2jVckGDc5bebS' \
			b'tJk7cdrM8bSZm1ivKQQZE0zyMX4sdRExuXKCORSjIBjH02WOp8ucTJdFfSaCKZIIBBNk6DM/IJgQapFg3BHTZSGxjGBCRrYRTCby6QSTTZVl6pkjmKAvm6ppRjAumyJLia0mmHoswFURDH319lJIRj30UdYDH2U9LBCN5jD4riERDbq13OQoaw5HR1mLE9vN' \
			b'wERDb2OiYd94paOshymiwafhKOvhNKKhl5CA+0dZ54LsHWUdfYwfS11EdG1wFUdZH4hRHmU9ENGQfK1oLkQviKZIIh5lLTL0mR8eZS2hlo+yHuaJRtPOIjnOWhLMyCZkZhvZZGKfTjaYAmYgHGmd1DS7NiN6s6m65kdaD4lwUmKrCaceE3BVhHMxZPOgIxrF' \
			b'Ixq1NKJRFAarpMpGNIpHNCqNaDgcjWjEiSMaJSMalUY0qrjSiEZNjmhUGtGoE0c0ikc0amJEkwuyN6KJPsaPpS4iSqNVoxHNgRjliEbxiEbxiEbJiCboMxvR5EnEEY3I0Gd+PoVaHtGoI0Y0klg+opGMbBzRJJE3jGhUGtFkGZ8b0Yi+bKqm+YhGZSOamNhq' \
			b'gqnHBFSCuXqC0UwweolgNIUJt0AwmglGJ4LhAEQw4kSC0UIwOhGMLq5EMHqSYHQiGH0iwWgmGD1BMLkgewQTfYwfS11EdG1wFQRzIEZJMJoJRjPBaCGYoM+MYPIkIsGIDH3m51UMtUww+giCCaWTEYxkZCPBJJE3EIxOBJPUM0swoi+bqmlOMDojmJjYaoJZ' \
			b'OiagD9TylL4eGhjlLtkkMEllkYdjEfwIF34UzKxd5Te8ym+WVvkN0cnkh0Ox5hpmkeDElX3DLEJvkJV9U1xpZd+MWATrGz4MC/vmNBLZBdMxM7U70xb/91f3o5i4um+mL1raN6N1/ZmwlONiNkyJ5ZhpBEBZrII/8AFHVvmqvjxGCgk5wJ9eRecRK/tmmUVC' \
			b'geYr+5KVKRbhfBwzFYYBrMvyftrSviEakfoSlTS7ti+FFlSqsVZgzkaMQhUmrPLHwhsxSjc8o96OUApU5Gc0q9l2z4hMARCeIUVCw37GXzeNXGNWfq+6DmbqYOYiaGjVYIYtmN2SBbOjiwYzmQWzYwtmlyyYJRwNZsSJgxmxYHbJgtmVVxrMTFowu2TB7E60' \
			b'YHZMQ27CgrkQZG8wE32MH0tdRHRtcBWDmQMxysEM85BjC2YnFsxRn9lgJk8iDmZEhj7zw8GMhFoezBxhwRwSywczkpGNg5kk8obBTLJgztQzO5gRfdlUTfPBTGbBnBJbO5gxZ/YJa/v0OQZyjRvhKtecJdewMbNbMmbGqsjGzC4zZnZszOySMbOEI64Rp5Z7' \
			b'S48i19jiSlwzaczskjFzfMMJdMP2zG7CnrmQZY9uoo/xY8GLiK4NroJuDsQo6YbtmR3bMzuxZ44ZjokH0skTiqQjkvSZH5KOhFomnSOsmkNiOelIdjaSThJ5A+kkq+ZMPbOkI/pKIQvSyayaU5DVpLN0PMC5zqCdxaxZPkwJtBEoI9BFoIlLo4izpwe2EHNL' \
			b'FmJumJ8FcxyfKEGcSAliFeaSVRj7xitRwqRVmEtWYe5EqzDHVmFuwipsnwOiWMaPJU1+jhMt0H8mrBvbgDm2AXNsA1YOL0RvAePZ2MuxmZc7ysbLHbDxirgur8lxXeTaiOsxIcb11ZCezLoknYN2XaEwbKpwOaZndl1JsGMwnbB8aY99xfKK5WeJ5Z6NsPyS' \
			b'EZZX81iOhwWJ4VVwQiX3Ynjlk+EV+8YrYrmfNLzyyfDKn2h45dnwyk8YXu1heRLL+LGkyc9xojmWz4X1YzMrz2ZWXu1jedCbYLlneyrPllT+KDMqf4QZVUgsw/Ig6DYsTzk+Dct9sqCSdA5ieSgMmypchuU+M6FKgh2N5Uvb2SuWVyw/Tyzn1Wm/tDrtD6xO' \
			b'45FvsjodnIjlsjrt0+o0+8YrYfl4dZqxPC1P+xOXp+klJOARWB7FMn4safJznGiB5TNh/Xg1mh5wvvawXPQWsJzXnT2vN/uj1pr9EWvN4TU5lougG7E8ZuFELDcJyzmdw1guhWFThcuxPFtbToIdjeVLO8fPFcurldIZ4f4lTNlj+0NYckvY7w5gvyNvwn5x' \
			b'asv3lmMG7HfFlbDfTWK/S9jvTsR+x9jv9rG/EGSPB6KP8WOpk5/jFxQ8MBOWBCl4wDEPOOEBLVrI+SCPHFlBXt1nfkgPEmqZIdwRDCHBcoaQLGxkiCTy6TPy6Aw0kdQzyxKiL5uqZs4SLmOJmNjqGfmlbeCVLSpbPA228MwWfokt/AG28ORNbCFOZAsvbOET' \
			b'W/jiSmzhJ9nCJ7bwJ7KFZ7bwE2yRC7LHFtHH+LHUyc/xCwq2OBC8ZAvPbOEztvAjtsgjR7aQV/eZH7KFhFpmC38EW0hiOVtIFjayRRJ5A1v4xBZJPbNsIfqyqWrmbOEztoiJrWaLpT3clS0qWzwNtuiZLfoltugPsAVdzBbiRLbohS36xBZ9cSW26CfZok9s' \
			b'0Z/IFj2zRT/BFrkge2wRfYwfS538HL+gYIuZsCRIwRY9s0WfsUU/Yos8cmQLeXUhvYqhltmiP4ItJLGcLSQLG9kiibyBLfrEFkk9s2wh+rKpauZs0WdsERNbzRZLG7IrW1S2eBpswdZBfsk6yB+wDvIcn9hCnMgWYh3kk3UQ+8YrscWkdZBP1kH+ROsgz9ZB' \
			b'fsI6qBBkjy2ij/FjqZOf4xcUbDET1o8thTxbCvkhY4thxBZ55MgW8uo+80O2kFDLbHGEDVFILGcLkXgjWySRN7BFMiTK1DPLFqIvm6pmzhaZHVFKbDVb0O7qrrELnyx88qQBOYUqdrcfKbxPAlErSMRdIJG0D30YIbY7XDtmM6WdWRqDgNb0gWEIpSfb3qJb' \
			b'cxw6jjANRHRfXOk4wsmBiE4DEX3iQCTsv9YTI5FCkr3zCPHdKDSvc4wET/GwNHgswhVvYJYhPNWz0fR4WKJ5WKKzYYkeDUuKyPFAQpGiyIqKoXKiQcVNH0o4MTTBIzLHhBMSzQ8llKxsPJSwp43Yetv4BGWxaYwioh0+llC0Z2PeimMJs0FK0m5GO/QE/xqF' \
			b'fx096S39deSr6AeSkO6Rg6AMXh9ioH3uGYhvOmEaoZacV5hUjmOUWcsmIg8iiWxUUQD+MGGLJIBOQN4dB9qLvf4cpLeAsz3NvigA8UEA7kaAK2AbARZB5mhwnYVVwlMCUkLRAKERMycAM6DlJqhctgQKoLgbH/ddYhoC2p4hT0QuxKzdnhXmLEgtdocLXNqK' \
			b'SAhHJ1rqBPw5jDy7vQ1QEWoCwiBcqMNwMdlbfRjECD1OqF8VN+C/m8GONbixrldG/awLBI+sV4XFWkFkqi+TfZFsBCTrQUSv7XP4BweR8VAV0cTcL6KAlhUUjgKBFH5J9twR5k56JisRZhZdwnDv7BGGJM3/C9oowoX7RxwiBlC0xjEehroUBJpGH0077lch' \
			b'UPMvqKbPIDc0/jEnjH/aJSxq7xqOAgTZDILaJ9ax0SdAz3hmajwrBf44URFmpiD/GmcmIiS5DJZaOvqMZ6lwfI3jbRyH9/lsFfzXdwhbBFndetjqHgW6IlT1CaqwbJ9wB0mjtlZDFL50vpPUdTRHulNyQDhXAMt1MYKXZtxiAAvzpjL1g8JhASn6VBId72ej' \
			b'cRP+GKif1W2b28Hz/CZXDu4H28LSMc722yOwzVwYviG22SMHb/1xgzecJ3yQ7tVM16rLcYpb2jl0scYDOCxPLLtjcIpycZlYhTilSTlHDejckQM6rF1HDOrsnU8k31sv6qn2oI6dGhoefmroTqeFHrX3k/V8xmtmT6rns2JqaHaOef3UkGten8FS1Kxlw90v' \
			b'S50TfpiHnvxJ2MGV4jKXo9igZBCjEfegy1NnCR2aZH/o5anmX8MzoCCa1fFnASPL0IECgcaxkj4dGDkWQtDU6E5Wqa5uWZvNx8j05S5mX84SRI4GEFFEf3edkP5S0APcKBceW/1oKDI2ZHwMJMFzuu8AUcKUbznVe4Xoglkkm9Qd1pnHRRl3NkCzQ0Vi6u0d' \
			b'4I0mw8z0HfsmztoOp6MPGn0/KAD5+wWfo7bljK2oH2NGxZ9/d0bZc0cdTJk+rHTvmGO7td0b3DzwqHMsdwY8WUcH0ju9o9M+MNRkMKPVI4+WHglmKsRstAYu4QXL8DwGT4+MLveALGoDsqhHRJbxtrKKLBVZ1iMLll9FlvtBFr0BWfQjIoupyFKR5Q6QRVVk' \
			b'uSdkMRcy7Xt1C0VnCh3njBp3CRGa3Je0JHQnkND8C1rIM8RHXFKGMqnocDHosMES5RIRgrjwrgGCEn2ia8Z3aHTi8dP2eDyNdc8QUwksbAWLChZnABbcVM6rO3HdcOEAJSwZqdnzsHWtIPGEQEIQ4fLHHPcAEnxuHP8/c5DAMwLxjLEWxx9Y47FrgbXew90S' \
			b'eFyKhWsFjwsCD13BYxY8dPx/+eBxKQauFTxmwAPiQf405O+MgIRa/dlNfFIa54AjIkhz1ECFA58EIxR1EUY0wSs8XgaUbnhGHAEl/gxRGZrBMwJFqOPPEO+gzsKdzpO0G6xXK7ScA7ScEZwMZwknw7nAybAGTk7ulVCE7b2SNSDittilVhCpIEJnxj/Nxdi7' \
			b'ABHSziVOnnY4hMEK2+IYR9EJbm6LqWkFi6sFC6piT9xyYwVYkDqe1EpLRx0M3FhEDkVgscV6tILF1YEFNaxrsfM6Ai0o6tNcmDX41SZsBS3cyeTLVYPQChbLYEE17tpsQq/biMNgj6LtCCSqXWgFCQEJarZnZBZ6FiDBYl4fRmj1jEgDGgs6HIFFtQu9ZrDA' \
			b'en0OVqFnixVX26FQ2KFQ3KGoZqFXjRGqYkTFiCWMuBTrT5QsnFL44HgRzsl8bNwIpxPWbaxr0QPLcYeN4fFwBG7ufNAEFTiHKas3vLvHMwM99kvyx3U82uyb75fUAek3dELahY6IerqAQsnuHcKOVh+j/yfbeNELSCH6gvsqakuHhXRwsNOCFshHdVz69hlA' \
			b'PvVbHs86tCJORZwNiOOmEMft/T8dcVxFHHzBAuKYtYjjH8+UtCLOfSPOk0UbP4U2fu//6WjjK9pg4tsnZTKkUc1rRBiGF8YWBhZGFUd44hBJEEYYQ3IAIfQIOBDafmyvVtqpmmmfJmuLer+9hDbS4ycN6Pi22AZC9Y81P9Z6rMNc2S1XcardsWZP1+pQoWM1' \
			b'jDUv1hNUJdWPuWpBX3iTCkAFv1c+sUigOHAsC6V7B9pnRI5YPKRyQDwtysKvLI+JMkEMK8qFWut9FwxmhfAiFpDOC4kQIS+o2JiPLixuVRMNaq/QzJ0UmjpUbv3TKrs+4f10+QWofrAyRPsXUIQmwlU02UnfsfC41g1doB6ek+wdh3f5Y+zN0FwU6PE1f7Lb' \
			b'fYcuUL2DZMB9swNgbTE0httBO4fOU4eBoEfT0jODz3DLMxYGfZ5d0ceLLX5DFHo6kEXQODAJljb1JlSTXgY+UAFatFTo5BPrLvsMMaQGL8J1fKxG8B78SDj1F418UNyTEN0mIaCfufSP3mLxLf7Qe+Rzp8PCCy32Ou3ev/RR027sR+930++3KAJ+faSl47v1' \
			b'lDjtnkT0fY84TQ+pQudH4yGnhaTQn87+YY/NyZG66X8Rwtv8F4bA7e+0Za7lw2gRPvAfZck/cJbgNT1+/gWJuNn+j79YpCkr/YlZ6edyM/qy4WTujD2QQ0h28R8OUsonPEwYZFjQ5T62CEu5HqZzbWYzDmngEG0ox2T72lClQtqWbD2xR4wIiF1DOvgNXold' \
			b'UD5bRtOZW9jjpVlI+jxkUCT+7kWh4A8cwYq188rFmktjKVcqGjmJlK1F4a0o3dF34ln5KOzENUw+TX5z/5dTOhR7OeXs18h5WM6xOPs3/E9VBZ6cWwuhJdLHulgp6oQGBPmG+nyvzcidU1PSzeor9EFPiHrw0nee4szFtUOfK7waWehxj103THMmF0634Y2+' \
			b'xXZ/F9cLc35Q2jWPd7FSuqgU/DbecL9NBpVyua0Gv+2H18Cz3/29Xua+X3D8xRVlZiB3fOtR99CAcDFkw4UrDNuSYN24cSOCetQ9TFNq1YU2J5w4yy7KCC7amHu/cE7tAV5zxMW1Z2Y8P19jjuua3E0Dc83+hetOkx7HXLiStz4aa6qv7Wx1O8N56au+uOqs' \
			b'nnN5wEaGC/iPf/FsdVub2Pom5prrvrjqrJ6VOX6IfTfNzDd3fqEdyvporC9dm9rqpobrq1d9cdWZmcq4i6am7mpshqZo93Chxdf6aKy2vcmO2uKWW5xrrvviqjMz/XFXLQ6rxN20Ot/c04UmleujsfbqBMkJDa9vrvviqrN6dsSdunaDpX9sGxyX6H47HJpV' \
			b'F9rnropAls3QmhZCsR343sW6rfMp65slGvZd9cVVZ/V8ysnNMq8Vd9pEcWfEPV/51oNTE2GLwa3zMqfZPtxFa8VTGBHgHrfVumbLhbYdG5M48tK4rATju/t8CdcoVcF/fTXyzXVfXHVOsrC5S5OazTxwsJD7ZtWFxu9r4+RX2Iu2Oh6aPPe0jQxvvIsMnFxG' \
			b'pjbv9c17aK774qrTPenmjRtfL/Liwlk9EXVZheOay7y4cGZ2mzxc4QRIPbqAulMKyTcPfyGq300g2f9kVs8sRVZ85PKaoLflMuubtRduzzsh2mnXkS/jkpvZNvQ0Sw7PZLj4i8vt9I1Pl1huurn8i3eKzmxCevwdFY+9ywZPSjnp4nNQ0v+TE5pKdO/XyHls' \
			b'WjN+XCdO2YN1HXXCNtdxcT04291Wj10P8Mykq7i4Hqw2SbqaeqCa67i4Hpw0eXQV9UA313FxPThpnuoq6oFpruPieuCa18bSsQECED4+kJrS4wNUMj3E83gkKgwX82qi+AweXM7AvXsad3zjLiqezoEaNBkaiq/8z6HVXmgsXooBFWH0X3fc2bE6PwsIT8/h' \
			b'LFjDz8sTEzGEtnQSEA04NVc0qmRYuTxXoJAGAGeeQKqoNounKS5UNEzVYqrYxPgsRT63sEvnFcazCvHgHzmOx+L2b6rCtH0StS36cygn7fnSItHoiCNcauJ5ThAHfuMBStpzqULrATfqRUvB4zfRwxN493e3/x/cVPv2'

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

	def expr_sum_1         (self, SUM, CURLYL, varass, CURLYR, expr_super, expr_neg):                          return AST ('-sum', expr_neg, varass [0], varass [1], expr_super)
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

	def expr_attr_1        (self, expr_attr, ATTR):                                    return AST ('.', expr_attr, (ATTR.grp [0] or ATTR.grp [1]).replace ('\\', ''))
	def expr_attr_2        (self, expr_abs):                                           return expr_abs

	def expr_abs_1         (self, LEFT, BAR1, expr_commas, RIGHT, BAR2):               return AST ('|', expr_commas) if not expr_commas.is_comma_empty else _raise (SyntaxError ('absolute value expecting an expression'))
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                            return AST ('|', expr_commas) if not expr_commas.is_comma_empty else _raise (SyntaxError ('absolute value expecting an expression'))
	def expr_abs_3         (self, expr_paren):                                         return expr_paren

	def expr_paren_1       (self, expr_pcommas):                                       return AST ('(', expr_pcommas)
	def expr_paren_2       (self, expr_frac):                                          return expr_frac

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

	def expr_bracket_1     (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):           return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_2     (self, BRACKL, expr_commas, BRACKR):                        return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_3     (self, expr_curly):                                         return expr_curly

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

	def expr_pcommas_1     (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):           return expr_commas
	def expr_pcommas_2     (self, PARENL, expr_commas, PARENR):                        return expr_commas

	def varass             (self, expr_var, EQ, expr_commas):                          return (expr_var, expr_commas)

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

		if pos and rule [1] [pos - 1] == 'expr_commas' and rule [0] not in {'expr_abs', 'varass', 'expr_func', 'expr_subs', 'subsvars'}: # {'expr_abs', 'expr_ufunc', 'varass'}:
			return self._parse_autocomplete_expr_commas (rule, pos)

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_intg':
				return self._parse_autocomplete_expr_intg ()

			return self.parse_result (None, self.pos, []) if self.rederr else False

		return self._insert_symbol (rule [1] [pos])

	def parse_success (self, red):
		self.parse_result (red, self.erridx, self.autocomplete)

		if not self.has_error: # if no error or rewriting has occurred to this point then remove all trivial conflicts because parse is good
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

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: # DEBUG!
# 	p = Parser ()

# 	# set_sp_user_funcs ({'N'})
# 	# set_sp_user_vars ({'f': AST ('-ufunc', 'u', (('@', 'x'), ('@', 't')))})

# 	# a = p.parse (r"Subs(x, x, (sin(x)))")
# 	a = p.parse (r"f (x) = x**2")
# 	print (a)

# 	# a = sym.ast2spt (a)
# 	# print (a)
