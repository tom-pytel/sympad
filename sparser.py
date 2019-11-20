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
	ast = ast.strip_curly.strip_paren1 # ast = ast._strip (1) # ast = ast._strip_curly_of_paren_tex.strip_paren1 # ast = ast._strip (1)

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

def _ast_tail_differential (self, must_have_pre = False): # find first instance of concatenated differential for integral expression -> pre, dv, wrap -> wrap (\int pre dv), pre may be None, if dv is None then rest are undefined
	lself = lambda a: a

	if self.is_differential or self.is_var_null: # AST.VarNull is for autocomplete
		return None, self, lself, lself

	elif self.is_minus:
		pre, dv, wrap, wrapp = self.minus.tail_differential

		if dv:
			return pre, dv.setkw (dv_has_neg = dv.dv_has_neg or not pre), wrap, lambda a: AST ('-', wrapp (a))

	elif self.is_fact:
		pre, dv, wrap, wrapp = self.fact.tail_differential

		if dv:
			return pre, dv, lambda a: AST ('!', wrap (a)), wrapp

	elif self.is_add:
		pre, dv, wrap, wrapp = self.add [-1].tail_differential

		if dv and pre:
			return AST ('+', (*self.add [:-1], wrapp (pre))), dv, wrap, lself

	elif self.op in {'*', '*exp'}:
		for i, ast in enumerate (self.mul):
			pre, dv, wrap, wrapp = ast.tail_differential

			if dv:
				if must_have_pre and (pre or not i):
					must_have_pre = False

					continue

				if not i:
					return pre, dv, lambda a: AST (self.op, (wrap (a), *self.mul [1:])), wrapp

				if pre:
					pre = AST (self.op, (*self.mul [:i], pre))
				elif i > 1:
					pre = AST (self.op, self.mul [:i])
				else:
					pre = self.mul [0]

				if i < self.mul.len - 1:
					return pre, dv, lambda a: AST (self.op, (wrap (a), *self.mul [i + 1:])), wrapp

				else:
					return pre, dv, wrap, wrapp

	elif self.is_div:
		pre, dv, wrap, wrapp = self.numer.tail_differential

		if dv:
			return pre, dv, lambda a: AST ('/', wrap (a), self.denom), wrapp

		pre, dv, wrap, wrapp = self.denom.tail_differential_with_pre

		if dv and pre:
			return AST ('/', self.numer, wrapp (pre)), dv, wrap, lself

	elif self.is_pow:
		pre, dv, wrap, wrapp = self.base.tail_differential

		if dv:
			return pre, dv, lambda a: AST ('^', wrap (a), self.exp), wrapp

	elif self.is_func:
		if self.src:
			if self.src.mul [0].is_differential:
				return None, self.src.mul [0], lambda a: AST ('*', (a, self.src.mul [1])), lself

			pre, dv, wrap, wrapp = self.src.mul [1].tail_differential

			if dv:
				if pre:
					pre = wrapp (pre)

					return AST ('-func', self.func, (pre,), src = AST ('*', (self.func, pre))), dv, wrap, lself

				elif self.func in _SP_USER_FUNCS:
					return AST ('@', self.func), dv, wrap, wrapp

	elif self.is_diff:
		if self.src:
			pre, dv, wrap, wrapp = self.src.tail_differential

			if dv and pre:
				pre = _expr_diff (wrapp (pre))

				if pre.is_diff:
					return pre, dv, wrap, lself

	return None, None, None, None

AST._tail_differential          = _ast_tail_differential # adding to AST class so it can be cached and accessed as member
AST._tail_differential_with_pre = lambda self: self._tail_differential (must_have_pre = True)
AST._has_tail_differential      = lambda self: self.tail_differential [1]

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

def _expr_add (self, lhs, rhs):
	ast = AST.flatcat ('+', lhs, rhs)

	if self.stack_has_sym ('INTG') and lhs.has_tail_differential:
		return Reduce (ast)#, keep = True)

	return PopConfs (ast)

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
			diff = ast.diff.strip_paren1
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

# def _expr_mul_imp (self, lhs, rhs):
# 	ast = AST.flatcat ('*', lhs, rhs)

# 	if self.stack_has_sym ('INTG') and rhs.is_differential: # or lhs.mul_has_differential:
# 		return ast # KeepConf (ast)

# 	return PopConfs (ast)

# def _ast_strip_tail_differential (ast):
# 	if ast.is_intg:
# 		if ast.intg is not None:
# 			ast2, neg = ast.intg._strip_minus (retneg = True)
# 			ast2, dv  = _ast_strip_tail_differential (ast2)

# 			if dv:
# 				if ast2:
# 					return (AST ('-intg', neg (ast2), dv, *ast [3:]), ast.dv)
# 				elif neg.has_neg:
# 					return (AST ('-intg', neg (AST.One), dv, *ast [3:]), ast.dv)
# 				else:
# 					return (AST ('-intg', None, dv, *ast [3:]), ast.dv)

def _expr_intg (ast, from_to = ()): # find differential for integration if present in ast and return integral ast
	pre, dv, wrap, wrapp = ast.tail_differential

	if dv:
		if pre:
			return wrap (AST ('-intg', wrapp (pre), dv, *from_to))
		elif dv.dv_has_neg:
			return wrap (AST ('-intg', wrapp (AST.One), dv, *from_to))
		else:
			return wrap (AST ('-intg', None, dv, *from_to))

	raise SyntaxError ('integration expecting a differential')

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

	if args [0] == '-func':
		ast2     = AST (*(args [:iparm] + (_ast_func_tuple_args (ast),) + args [iparm + 1:]))
		ast2.src = AST ('*', (('@', args [1]), args [iparm]))

		if ast2.args.len != 1 and ast2.func in {AST.Func.NOREMAP, AST.Func.NOEVAL}:
			raise SyntaxError (f'no-{"remap" if ast2.func == AST.Func.NOREMAP else "eval"} pseudo-function takes a single argument')

	else: # args [0] in {'-sqrt', '-log'}:
		fargs    = ast.strip_curly.strip_paren1 if args [0] == '-log' or (not ast.is_paren_tex or ast.paren.op in {',', '-slice'}) else ast.strip_curly
		ast2     = AST (*(args [:iparm] + (fargs,) + args [iparm + 1:]))
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
	argsc      = arg # .strip_curly_of_paren_tex

	if var.var in _SP_USER_FUNCS:
		if argsc.is_paren:
			return PopConfs (wrapa (AST ('-func', var.var, _ast_func_tuple_args (arg), src = AST ('*', (var, arg)))))

		elif var.var not in {'beta', 'Lambda'}: # special case beta and Lambda reject if they don't have two parenthesized args
			return PopConfs (wrapa (AST ('-func', var.var, (arg,), src = AST ('*', (var, arg)))))

			# ast = wrapa (AST ('-func', var.var, (arg,), src = AST ('*', (var, arg))))

			# # return Reduce (ast) if rhs.is_differential and self.stack_has_sym ('INTG') else PopConfs (ast)
			# return Reduce (ast) if var.is_differential and self.stack_has_sym ('INTG') else PopConfs (ast)

	elif argsc.is_paren and var.is_var_nonconst and not var.is_diff_or_part and argsc.paren.as_ufunc_argskw: # f (vars[, kws]) -> ('-ufunc', 'f', (vars)[, kws]) ... implicit undefined function
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
			b'eJztnXmP5DaW4L/MAl0JRACSSFFU/lc+etYYX+OjdxoFwyjbNQNjfcFl9/ZgMN9930mREdSZysqISKJUGRJF8Xh8fD/x1ItXf/ny/c8+/uzTvxz+8r/e/PID/Ojl+19/8fHfP4aTj7/9/OUXH36Kp+Hk42/f++Ll+/+Kp+Hk679+/en7n/9dz+D308++gr9/' \
			b'e/kF/P3y75/QPfil5z+ge19+/PLL/82n7334L9++//LLD7+U809equt7w+nfhtPP+ZRCCGn4K5zITy2/Dfx+8tGnX1O4H3362Sf6W+tJQwmigEKmT66+oix8/Z7e4dMPP/n8q79/+SEm46NPv/oXzPHXlLuPPiHv9PffvsD7H6NIP/4M/YhwQIQkGP77/mef' \
			b'fPJSpY4OX7DUv1Cpsxtl9AuVuri95N8hyV8kGcCrD/8N/rz85HP4+8F7H9M9dP30AxEznr03nP5tOBUxf/jxlx9iUr746BP8/fDf30e5vPyKBINBfsXZgKR+pb8o4A8++ttHH+AT70uBs7/PP6byANlp0fz7lx++Tx4++Oivf0Ud+vQjVkNK9MtPP0Ah443P' \
			b'8PlPXn7+5VefSRJVa8jh/3DR4E/NZQZRvv+vcPr2z+/e/uP172//EZ2/hfPvX//+5o9vf/392x++++ntH69/j27D6Zt//gZ3fvzHz3r+y5v//Pb17/+pl2///O3N78PFd3D68+s/vv3+15/k7Pdf/99wxvG9ffP27ffh7LdwpsG8/i6c/vjDP4PrH3+EiP7j' \
			b'9fd/6PlvFAE7//nL90Oa/+M/fksuvv3x+7dDSkOGfvpxyNvg+seb38P5z3/+9O2PP4fAvv/z95/+KxKNnn734y+/xmIKqfr99fdxUHCil/94E+68/uGH4Ol1yNw/374ZckpSCjnAPEWCDzf+/OXHX38JN/4rpOjHX/4ISfp+yA2Ucyy2f7wOQv7l1xDzn7GX' \
			b'17/8kLjHcv3u+19//vl1uPw1BPYdCOH/vhkKLfX3249vvn8TLkAhfxlk8dvbP34NUQclCTn59achtxRocvE2evLbn/7x+qdBfvzkN4dXL46uObj27sAnDk/aGv80h9bdySVc0ZlBb4e2PRzlljrwVaPPwQNGnfCUfB07cqkOL6w5HM2hre+Cg0UHa9Xh2OOJ' \
			b'qfhPBwkwzV3s1LRnTl0TO+EpnNWO/3Td4Vj7O3HCUzjr4L8/tBA33+nwBH4xIPy1Hv+YgwMfNSd2cNLLo6W01vbwwlEm+ju97iiXFSepPbxo0AM6doNTctl4OUE3DARSUttwRqUET7zALECpeE4ThtFQIpqa/3Rwv+EUwhWeolipELA87qJLPY/cuaixiDGH' \
			b'9N+2etviCSZS3DnpIAVx5GtIY9NT7pvgQGVu3XBdkQdz4jD4OBrKlLX8x3FQqCqWkmCNXGrZYDI4HY7/OCgeJ/JH2ZN4HegLqo/ccJXesJ2ULScJLqF86VmIqEGlwIKRHKOTiS9ZyIbd8HEQqgEZtKwP4dKfOomWJM42c5k+aOvzy4yPLnVqzi+Th47WRSkb' \
			b'aoYk4sShPnVoYodeiqS2eg01m1QSzASKkhIH0RsuiOB87jRcHm1NgYGig4Zg6P3Bg7MDvQF/EtX5XTRuYEbmPYFmpJ6OluoD1nvwV2k9gETWnJseK36NebEHyJLUf3QOjoOLZxc/uPTsMjzVVOQi6knViPJsGv7j+pA8deqq2AlP8czzHxDb3d1wimeWa4A+' \
			b'gsaXDT8maFA9vER/wyUUKFkjz/7UomLIXC7VgUOqDf/p4Jmaa3Rt6JTkiFVWTthMY2EcGAKdmgB0FKdw3dK1RFtJHFjLD65WzUvc1QUcKIFOtFKKAMvasq2l/+CRpYVmk+Tv+E8HKWmk2BydokTAYnis8QK77uBJ9CC0F7Vlxh2gRMCLqzVbdJPzYXM3wZ5T' \
			b'ylD3vehny3JwUjtEORstD3B84aKCwks3JMsfHAUJBusFgUS4gZcc/plTuIQUkY6gn17PbCVnoplw0uiJ0RPmFkoohIdXfRKhuoSrY0Nh161c6h3IXc2ZsPynQ0mJ0Cydorf+wJrVVHylyo+VquGkQUEjFAcy1yQp9OT5T2cGk8PGCKXo+E/08uOEkW3Lf+i9' \
			b'R+61dIpnVm/eySVc6Q0mEKTIt6QHAX+ozfzaRG9YVh936Isk66zewBcrcYEzeKd7VR1qkEkNygQ5tYRv0B3QF9B8tHmgVv0B6iqYNxBYfwDp9HDagPDgMZB1jYJsMJgazsG8QVHUUM0NqXNd43+DthLqQg3veDW8CKIXf6gt/oengWg1aH9dYZHgOdwGTQRz' \
			b'bvAZ+A/JqCEdNSSkhpTUIJAaBFXDe0ANEdUYE4YP7zeAVbBSNUilBhvdm0NvD3176N2h7w49hnPAlMPDGDaECVTv4aeCoKr6gG+29BoHlaSuwGMFKe/gdesA5hWiw2LtyPJ4sN8IY0o5xF9hwPBr8RceBEnWIMoa/ELF9/YABedRPvA2Bk7+4PtDj+kH/5Bi' \
			b'tOxQ9MBFiB5sVIevJGDAO3qphTdWULWOdLmjd1QwWR1Rpm4w8/BQhYYNLhp8w4A3PkQVihPS1+DrO5zeYa2GtEHRv8AyRwcstzu4jWmGS8uumBP0hbnBu6AL6IwFcUc8x7uvEP10TWEXfbkhfXnRc8HXXMJYYlTifS1qxPqBJYuXtZXfVh6T56io6VeekwfR' \
			b'h2PdIZUqpud2VQnLuiuFfPuFXGryjRfyC8NW3DRq5Q1b9U6MurxT9KZowm1rwivsoixlfONlTNLH+t1ShY4K6xvqoWIjwG9wyU10lRfAll4AqUxOfLTcpiAR3CU5fve5jZTzVCFPFPFUBUX1skoXKRsrWUa5RKFiLYq151RvRvQFdASLpJXGHFWMu1A/tF5I' \
			b'HRC9V42P9TvSa9Vl1l9V2FJMDy4m5Ca3ikwrbfFKONpKnTJOrrWx3jopWJOtbNIOr22+sr2gbNLzbSvtMaftMFMVQ37bhvxFbbVZzi9wpbBvt7DRupQyvu0yflGHFlgjL1EudMkSSnCIDBJ2aA+ulPV1l7WxUtROXsblXUF6XFvtmKXr2uF7HUjLoYRQWJBy' \
			b'EEwNkil6cM16ACXclhK+8RJ2pYRvvIS7UsK3XMIveu0V4xZ8Lw1zzDc3tyvmdOlcebTOlbYv7Z8br2WYUa5X0q/F78ZblIb6yrDz1EkfiTMPD0pf2SvubWu1s41ba6vD4y46eNxveryRuRza4V6VDve9jI0tExtu3NZAGTPD29JPfuNF/YKHz17UVrtYpI/F' \
			b'ynAM1/ZXOJMbrz3f9twuR+OMlhYHdbBQcMpkGVl7twOgXgqqltcCz8TzPG3V9zJpUV4ejNFRESnnhnvY5OVCrhopbAoyLl2SCxqIlh+XoTUeM0/H31qJyXH6HCfLcbI6bhNWcK9CdfBJLKXYF2DYsYnuuOA6XwT6QIF2bAk7rgIdV4Gun5KrGsAi3yXyZZPR' \
			b'scnwVVHYhxn+Tgy/GGvH6tsIoHWwrLzB3fgb3Cta39LcldVMt17OlooZ1yk1ZeXRjZUtvlvzYrNStrdVtrhgsJFlZfBbCvEaC5EWAZaaeWuFWnOdpCWbWDdLcV55cdKrkQi/LAS4wFYrL4KmOlcWyN56jcSF7lrU/OvlVYiuSw29xBqKC1qpkCAaLLQyyfbG' \
			b'K2kj9rhtpJLqyJ9WVksvSSerq9pKnpKq3cg8C2nsGFKiUqcvo06/omV1WCClIJ7WuNZGa5XJ1SpbyV2ulKWYnqyYxLyZWoyilIujk1Ie77g8jBGs8P5JPJDIMxtk8jGPKrqwwpfa86Vo3gVabJH1u8N4kfU7Mjm9VZMvU4hl6hK1ftjIyNQmagfRlgU8CRpX' \
			b'rVHLiV+s+07aUwz8UmCPVjmqqkj4Ud+KKiuNPmnlOWoyPmTdwKuyGeLt9zDIdke4zITUpiXDCHJGIZT6uZ8FbAg16xfLSDdtxT1AVoDF/T4vqKfnG54C3iTTgcnRlgbRUxS1b6WBmt0ZoeZlUw+NKmhIreupqPTTeZuluJa8m/D2VvsViNF1Gdz/6rkKe37H' \
			b'bB3HacIVTfRveKI/VW65bMx5L5SXzg7e2bKQ+YbJzL3CL6Tr3zl5rZPhuVLH163I4DpYdgm99WrzCtcvlbl8V1t6ZNmKgdvQwdIVuW2Sm3/AYktc6UdY7qqC5S3rznyx1ddqq3FRJut+U3R/i+6bIrYtYitLNa7YZMjAXdcW3d/SsVgV3b9a3a9l2hLcM7xU' \
			b'FH+w8+GOvqaKP1C0Rr9XZmTxi7nT9RMm/rYNlrUJE7h5QrdeG5nQLQ/gDyiAkZnD5k5G0HmCqURI/UulZ+SWFdD2XNimZc2QzznwDFQTfYaBZkAanexoog29afadkdl3rGbi0cl1btAD54hxzFQFqIOmbAV+7QqFE/uoa7qsz7v+oqyFC/3pBrF2xL3NuSNX' \
			b'jM7MamRGFk2WLstRbkJLeJpIKcZrLkacA2l4DqThOZBSk43UZCPzyPDX8WtnK++J/EWoMj1o96Zdq4a0KZvh7rRWkvXayg+rc1uxHnvCXZka9c57MOxEK6HWyW5GJ1DJpAfPZei5Ret7ahPTHBrDYzWGd7GkonXsi1ZpfUPbWbJdk6WUFb+YdGzmOvbccRAd' \
			b'B9ixrnRsJr0YxGpomtvSCXOd6OOODhu6Sb7hHhF7J2+u3xyGfhXUbWnoWmq0kv3Q11tpQg/LC1h1WllC6I08nJ0CCFm3rM+W9dmWd6qrVyxDRV560G65kB3XWO4UK8MXK5eogJq3sosB/kJ0emnv5NOvLW4RBOnqyoaZt12TUFKlsJ9JYUOsLb/vtPy+gyV/' \
			b'aOQdHt0c36plo28Ur6PrSq5rvKaQXFlG+JgNNE+CB8k5eq/laXC6wMSQ9ONVRlRUHW8cxXPgcJN23KEd9xTHDcVLzb3amkv1rkN16PjH808vJQ7J6EptfMQ3pk47HeTLB7V8+oAqF9VP3rKf6q0vRfGYhrEvAn7cbX0MCph03qrON6LryJXCkevlCMTYMzh6' \
			b'KVHue6sOryp8E6QPxOOMEPxIfB9pNgvMS+lz6CwSnIdCxcxC5xYDNhcMNSYcyolzxGIDcTsWsZU8nuaOs9ZL6lFuKifWurgwSVdyVa8RoVApqI6J5mFVo4Fw8Bvv2YgvveGtCa5RsPhNL/xcFERdo8aDMtW43SN+dRu/y4xpwF1LcF8NUJ0G14eDFjSoMtjF' \
			b'XYHS4IZ/OOsMd8jCnYBwhxqc54XCRGk2WGTwHFYQ7C5HwaKygbY1uMkWbrCFRgTE22CXPHbH49oH3CcNd0PDrx1YLBJwx4XpuCgdV6SDVja4bLHFugfPgm41uK8A7keIHaS4RQW+LOIEcqzcOBsUpN/gyi1cyI67W+I+LThACfkxFZZ2D/pyhJhACMcaUnyE' \
			b'1B9Bz4+QgqPF8+pw7MG5wvtwCv+xdI5YPEe0EEeD/8kZHsESOYJmHbHiHNEGHLFQj1iXjlhUR8juES3AEav9Eev8ESvWsaYwQFhHg8E7jAzDQZ+OQgDvUIWPDm9DBo4gzCMI9QgCOFJEmGZUkSPW0iNW06PHEyipY49BYMgYISaywzug+kfQ3yPo/xG0EyVx' \
			b'xAAMJrTH5GGiLKajxQAwKhQDGrYj2rAjGrAjmhXOMSjisUFn0Jyjp2zRI3gLkwu3oSIcW0wIumEioCCOoLBHKLhjR+UAfzAwehRu9Jg5KgGMm1JT4y2SM5xQuVGOwbPBSDH8mjJA7vg8ZtOggEhI6AcCht8ef8ETqP6xxycqyiicYRFgQeE5lgvKE2NASXiK' \
			b'gPIHPih7cLfDVFWUJ7wCf2DTjlAJjx1KHPMIj3iSGIQD97yRpGM+sbofeywSzJihEoNUewwVk+7xgf4btHVo4Yp9K/ZtqX0rxq0Yt2sxbg0atzGjxm+5XWTdojfECRsXen25K/jU2LWj9i7/zjpr9U7e0mVe0yL7162wgdWJHWwztnCNDXTXYQexWYBbkQV7' \
			b'aM5tIi7pwqUtk7axwwLqZqxgR/8SW0gOW+xhxxaRnx+1it0Su0hh7GMbu5DHXrO22DZ2q6xjl9jHLmMhVxrG7upMI2UDkyA2sstYSSqEaUt5+G93jxTv7pHjPVwY/z+49me7+aQujbhvILGj1Hkxak1bMahxL4IYVxvZV5rjyQ37uGNiVf/AYHRz3WN5A+zT' \
			b'qXiNjLP7yCabbJdX0hskHRO0oTr20EhPR9pL4k5suHaLqS3X7jHuqQk7fi+y7zL6gV8CxS8q40eAg70Hf9g/QnYfX//BH/bOIAPw29D4YejdWQD38RMfZ0yAMFChZtlg8nzArdKJEfUDOVENrABFa6grUZnRzHMD5NfgRlvEDxsY0uC0ZpCTAfPHPOkipqCF' \
			b'oS69GaygotGRkEVcyXZ5+qX/LQOGfvOMUa8Da2p5/ZZYAm4oSiFOSAQll+mj/pVABBTsPaRfIRFdYG8l/uJmcSGUESThLaUSrtpAMuGMN6ITJbw1aXJypEo8mD65Hm4EfLFAzhAWJKI+sBs2H1Ilr2TtgLlacq+0o5yJWy2ioPMYgBSP5xKMCHgeH+NQRRCr' \
			b'SWdDxtcxkhM/D8kglgSVqhxzwBR/J8gk4VDDxz8Ynaz9TE+tp0rRSIQxSMUNd+rirBBR+ZehGj3IIhgAy2htzD296jVwiSrg4BeUyTf3+E7F4EWTfY/vOGDO7o/UVIffxv0PbV5/yUBe2OBpc22e3fBb74zgU/yeoDdgtyD3UZG7CrWrMesYs24Os6htjvwl' \
			b'nHXqiho2XLQc5BhkxVdArBPEintArIsQ66LwFbHif7KRN/gbQ6rLNPTIv0ljzZI09mD65DqWR0N6yTR1WZhq3sUDsjQfVmXFh3DURQx10mjkfJ+w0zE6XYrOs+AFnZLnOhaADTldic6FXW9BCCk6pdBn0cn+TtHpdkSnO5w1PCPRJchkNyfFaeRhxeXwEGd7' \
			b'b1y2BZfvsrVaUPkMUNkxKuc6OlGJ6EhJGVxRwYaLlkMcI6X4CqSUnk91D6SMuj9D4JRSIaX4nyZleGqMlLkuUfJv0lizpIw9mD65juWhbc4uS0nNt3hASubDqaz4EErGLc0uouRZC7NjSqZdrOfBCyUlv3GpUwXmXK6k5MJe2CCElJJS4LOUZH+nlOx2pGSX' \
			b'oeQguoSS7OakOI08rJQcHuJs701J98BBsgwfb4WMU1QsRCxERCLSTAgUzgwRw5EQUZx0/I/PxW1uAJA82TaEoRykOISDScTCQfU/ycHhqREO4q2Yg6ixOjKYxJrjYCqPPrkebkwNHYZMywDiSAj41al6ICCeKwEpA0JADiozyNikszBOwqc8u5CYLsm2Dflb' \
			b'R0BO7zwBgwQSAmpRzxFQ/J0QkGSyEwFZh1MCRiUTE1DcnFQAIw8LAaOHONtnBDwhX31PL2WKvq6/p3eVDPu6wr7CvsK+zexrmH3NHPsaOVL2sVNgn8x8od9Z9jXCPgkjsK+J2BcdgX3if5p94akx9jUp+8hrK03ANno+y744WaZProcbk+zTTCv78iEg+5qI' \
			b'fU3EviZiXzPGviZl33kULqSliwu5syF7K9HXLESfCiBFn5T0LPrY3yn6mh3R12TQNxRMgj6RpOi/kYcVfcNDnO390OcL+gr6Cvo2o4+n5jRzU3NQIHSk6GOngD6Zk9OMz8mJ0CdzcTSMgL5oLk6ItRnm4qj/afSFp8bQ12a6P0O7L442y77Yg+mT6+HGJPs0' \
			b'18q+fAiVFTkJ+9qIfW3EvrHJpU06t+Y8fO761KzG5dzZkMGV9Fs4tyaIIKWfFPYs/djfKf12nFvTRHNrAv0G0SX0YzcnVcDIw0q/SMm5DKfpJ9TLwK4vsCuwK7DbDDueINPMTZBBYdCRwo6dAuxkbkwzPjcmgp3MitEwAuyiWTEh1maYFaP+p2EX/I3BLjcr' \
			b'JsAujjYLu9iD6ZPr4cYk7DTXCrt8CAi7aDJME02GaaLJMM3pZJgAu3Q2zHn4AjvJalzOnQ0ZXAm7hbNhgghS2Elhz8KO/Z3CbsfZME1mNkwkugR27OakChh5WGE3PMTZ3gy7uroI2j18Idxjcm7ROrnnzK6xtXY7MGsNq044lWFTz2zq59jUy5GyiZ3O19+R' \
			b'6yydeqGThBLo1Ed06qOolU79HJqwhsszq9flsf4N//NwipNl+uR6uLFi8R7Losmt3qMpJqdzTAJ8+pNJJprxkPxhnglLlqpdN1zacLqWQf1CBmnxpgySIp1j0Pjqvz3w0w/UCVI7wQ6nU5cAck6iVYDocIIaZUvElHo7UyYmUj7tKsCLbVM9ZN0fThVunyGv' \
			b'bqWthYYcEos/kzzD6kNHwjNxUp6FSw5wBGh0S5nGF214VJlGMQnTQtyUSmaa+les4YXj4BRuFERFP2gLQggjhMNbo5BLkpADXOLB9Mn1cGMKcEECgrmREKrhVPAnlwpByocItomC7cLpCRIpmwMSz2NkHmrmY13ohiyvYyGnf56FIfUJC1UV5liokklpSALa' \
			b'CYis5ml7LBJdDEZxc15yJA8LG6OHONvb22MP3Yak9D6W3sfnTEQeajNzQ224LIeOlIjsFIgoQ21myVCbkaE2DSOwMBpqC7GaYahN/U828Yanxvg3NdSWRJvlX+zB9Mn1cGOSf5pr5V8+hMqKnAR+0VCbiYbazNhQm0mH2s7DF9pJVuNy7mzI4EraLRxqCyJI' \
			b'aSeFPUs79ndKux2H2kxmqC0SXUI7dnNSBYw8rLSLlJzLcDPtHrBrTKFdod2zpx2PtZm5sTbsO6EjpR07BdrJWJtZMtZmZKxNwwi0i8baQqxmGGtT/9O0C/7GaDc11pZEm6Vd7MH0yfVwY5J2mmulXT6EyoqchHbRWJuJxtrM2FibScfazsMX2klW43LubMjg' \
			b'StotHGsLIkhpJ4U9Szv2d0q7HcfaTGasLRJdQjt2c1IFjDystBse4mxvp90DtmQptCu0e/a049E7Mzd6hyadjpR27BRo1wvtlozdGRm70zAC7aKxuxCrGcbu1P807cJTY7Trp2gXB5ClXewhvkhuTNJOc620y4eAZRaN6+F5oF0f0a4fo106uHcevtBOshqX' \
			b'c2dDBlfSbuGoXhBBSjsp7Fnasb9T2vU70q7P0G4QXUI7dnNSBYw8rLSLipvLcDPtHrCjSqFdod1zp53lteJ2bq241SOhnTgp7aysFbdL1opbWSuuYSjtbLRW3MYRC+3U/yTthqdGaGfrCdol0eZol3gwfXI93JiiXci10G4kBCgzGy0Wt9FicRstFrdji8Vt' \
			b'ulj8PHymnWY1ybcNGVxHO7twtXgQQUI7Lew52om/E9rZHVeL28xq8Uh0Me3EzUkVMPKw0C56iLO9nXZlZ5RCu0K77bTjcTs7N26Hyk9HSjt2CrSTcTu7ZNzOyridhhFoF43bhdt2GLdT/9O0C0+N0W5q3C6JNku72IPpk+soS1O001wr7fIhVFbkJLSLxu1s' \
			b'NG5nx8btbDpudx6+0E6yGpdzZ0MGV9Ju4bhdEEFKOynsWdqxv1Pa7ThuZzPjdpHoEtqxm5MqYORhpV2k5FyGm2lX9kIptCu02047z7Tzc7TzcqQ7Y1bsFnDnBXd+Ce684E6eC7jzEe58FLPiTvxP4y48NYY7P4W7ONos7mIPpk+uhxuTuNNcK+7yISDudIGH' \
			b'o4QNuPMR7vwY7nyKu7PwBXeS1bigOxsyuBJ3fiHuVAQp7qSwZ3HH/k5x53fEnWYwxt0gugR37OY0R/Kw4m54iLO9HXdl/5OCu4K77bjjgTs7N3AHHvhIG3fsFGgnA3d2ycCdlYE7DSPQLhq4C7HaYeBO/U/TLjw1Rrupgbsk2iztYg+mT66HG5O001wr7fIh' \
			b'IO2igTsbDdzZaODOjg3c2XTg7jx8oZ1kNS7nzoYMrqTdwoG7IIKUdlLYs7Rjf6e023HgzmYG7iLRJbRjNydVwMjDSruouLkMN9OubIBSaFdot5l2aIYhsfgzSTvUdjoS2omT0o7PObRZ2pEn24YwlHYUh9AuxErpY9qp/0naDU+N0I6WKo/RLok2R7vEg+mT' \
			b'6+HGFO1CroV2IyFAmbGcmHZ4rrSjHAjtOKgM7UgCA+3Ow2faaVbjcu5syOA62nGC52kXRJDQTgt7jnbi74R2e65AZy1OaReJLqaduDmpAkZzxrSLHuJsb6ZdcxkboBTaFdpdJ+14mko7N02l1SOlHTsF2sk0lUXfNG9lmor6D7SLpqm0ccRKO/E/Tbvw1Bjt' \
			b'pqapJNFmaZcIpE+uhxuTtNNcK+3yISDtomkqbTRNpY2mqbRj01TadJrKefhCO8lqkm8bMriSdgunqQQRpLSTwp6lHfs7pd2O01TazDSVSHQJ7djNSRUw8rDSbniIs72ddg/YmqXQrtDu2dOOp6m0c9NUUL3pSGnHToF2Mk2lXTJNpZVpKnoaaBdNUwmxtsM0' \
			b'FfU/Tbvw1BjtpqapJNFmaRd7MH1yPdyYpJ3mWmmXD6GyIiehXTRNpY2mqbRj01TadJrKefhCO8lqXM6dDRlcSbuF01SCCFLaSWHP0o79ndJux2kqbWaaSiS6hHbs5qQKGHlYaRcpOZfhZtqVzVSeinbZ7cYK9a6UejxdpZ2broIb7NGRUo+dAvVktkq7ZLZK' \
			b'K7NVNIxAvWi2Soi1HWarqP9p6oWnxqg3NVsliTZLvdiD6ZPr4cYk9TTXSr18CEi9aLZKG81WaXm2Ct1uogBz7EvnrJzHIuyTDMel3dmQzZXsWzhnJaQ7ZZ8U+Sz72N8p+3acs9Jm5qxEokvYx25OcyQPK/uGhzjb29lXtlYp7CvsezD7HI/mubnRPNxWlo6E' \
			b'feKk7HMymueWjOY5Gc3TMJR9LhrNC7G6YTRP/U+yb3hqhH1uajQviTbHvsSD6ZPr4cYU+0KuhX0jIUCZuWg0z0WjeY5H8+h2EwWYYZ9Lx/TOY2H2aYbj0u5syOY69rmFY3oh3Qn7tMjn2Cf+TtjndhzTc5kxvUh0MfvEzUlFMJozZl/0EGd7O/vKRiuFfYV9' \
			b'D2cfj+25ubE9p0fKPnYK7JOxPbdkbM/J2J6GEdgXje25OGJln/ifZl94aox9U2N7SbRZ9iUC6ZPr4cYk+zTXyr58CMi+aGzPRWN7jsf26HYTBZhjXzrCdx6LsE8ynOTehmyuZN/CEb6Q7pR9UuSz7GN/p+zbcYTPZUb4ItEl7GM3JxXByMPKvuEhzvZ29pVt' \
			b'V8oIX2FezDyQV4Mf3ga9Wdnvabnf0871e1o50n5Pdjr/XBC5zvZ8WiaghhJ6Pi0RkLqHbBSzdnyK90kAogURj2M9n3aCgKysw/9872ecOOz9tJljuvdTc669n/kQKvnVD9qZ6JNCLQvqyF8VGu35tCdfFfISeMjg8FUhusVfFfLDpQ2naztA7SQIKfFmUKWT' \
			b'/k8p+TkOkkgyHxYapLNDD6hNSTjoJwsw6QLldDuSWEOKC7EyFDmb0hk6FDKHdgpFi1CETOoXzFt/j289YNTu6RUCLM89sh6sxT199SjC5OXt13LydaJrh2Xuu0SlsXhV4FzXWDTcWDRzjUUjR9pYZKfQWDSMSvqdbSwaRqWGERqLJmosmihibSyKf2UlXjgO' \
			b'7qzJGJ4dazKaqSZjHHm2yRh7MH1y7SLhTDQZNe/aZMyHgE1GOdVWY4RLyoTIs4nCzLUaTdpqPItIWo2S57jYu5CGta1GMwnLodWo6U5oqWU/22oUmZy0Gs2OrUZzOG81DslOWo3s5qRGGHlYW41RXvl3c6vx8jZ0KTgsOLxmHPJMUTc3UxSBQ0eKQ3YKOJSZ' \
			b'om7JTFEnM0U1jIDDaKZoiNUNM0XVf8BhyzjM9aCGZ8dwODVfNIk8i8PYg+mT6+HGJA4174rDfAiVDaeKw2jKqOMpo05mjYYwczhMJ46eRyQ4lDzHxd6FNKzF4cKJoyHdKQ6l7GdxyP5OcbjjxFGXmTgaiS7Boaij1AgjDysOI53nktyMw8vb8KXgsODwmnHo' \
			b'GIduDodOjhSH7BRw6ASHbgkOneBQwgg4dBEOXRSx4lD8Bxw6xqHL4DD4HsOhm8JhHHkWh7EH0yfXw41JHGreFYf5ECobThWHLsKhYxw6waGGmcOhS3F4FpHgUPIcF3sX0rAWh24hDjXdKQ6l7GdxyP5Oceh2xKHL4HAQXYJDdnNSI4w8rDgcHuJsb8fh5e0I' \
			b'Uz7lXsB4G2D0DEY/B0YvRwpGdgpg9AJGvwSMXsAozwUw+giMPopYwSj+Axg9g9EPYKQgKvpBUoQQxvDop/AYJyGLx9iD6ZPr4cYkHlUCisd8CIhHOVU88mUgpGdCeiGkBpsjpE8JeRaXEFKyHZd/F5KxlpB+ISE13SkhRQlmCSkyOSGk35GQmsGYkIPoEkKy' \
			b'W8iRPKyEHB7ibG8mpLm8XWQKIQshb4OQPROynyNkL0dKSHYKhOyFkP0SQvZCSAkjELKPCNlHESshxX8gZM+E7CNC9kzIngkZQhgjZD9FyDiALCFjD6ZProcbk4RUCSgh8yEgIeVUCcmXgZA9E7IXQmqwOUL2KSHP4hJCSrbj8u9CMtYSsl9ISE13SkhRgllC' \
			b'ikxOCNnvSMg+Q8hBdAkh2c1J1RCdDISMyshwErcS8vJ2nimELIS8CUKiFbCkptOERD2mIyGkOCkhO5mlSr9zhCRPtg1hKCEpDiFkFx1KSPWvhMQLx8EpISmIin6g4IYQRgiJt0YJmSQhR8jEg+mT6+HGFCGDBISQIyFA+empEFIulZCUDxFsEwWbISRJYyDk' \
			b'eVxMSM12XP5dSMZKQnLK5wkZ0p0QUpVgjpAqk5SQJJqdCMnanRIyEl1MSHFzUjVEJ5WQ0UOc7e2EvLzdagohr5CQ4Ad0ppAy+yWKir9EUc2QEusLHemXKNgpfImiYlLS7+yXKCompYYRvkRRRV+iqKKI9UsU4l9JiReOg1NSUhDsremjEEZIibfGv0oRJyH7' \
			b'VYrYg+mT6+HG5FcpVAJCypEQ8KsUcqofppA8CikpHyLYJgo2Q0qSxkDK87iYlJrtuPy7kIy1X6ioRknZQMk1PLllIGZIf0JMVYY5YqpsUmKSiHYiJmt5SsxIhMmXKtjNSRUxmjMmZvQQZ3s7MS9vj5tCzCskZiFlpk3Jyzm6ueUcqMR0pG1KdgptSlnO0S1Z' \
			b'ztHJcg4NI7Qpo+UcIdZuWM6h/kObkpdzdNFyDgqioh9sW4UQxtqUU4s6kiRk25SxB9Mn110kook2pUpA25T5ELBNKafapuTL0KbkdR2drOsIwebalOm6jvO4pE0p2Y7LvwvJWNumXLiuI6Q7IaQqwWybUmRy0qbccV1Hl1nXEYkuaVOym5OqIToZ2pRRXvl3' \
			b'MyEvbyecQshCyNsgJO8O0M3tDoAaTEdKSHYKhLRCyCV7A3SyN4CGEQhpI0LaKGIlpPgPhLRMSBsR0jIhLRMyhDBGSDtFyDgJWULGHkyfXA83JgmpElBC5kOohlMlJF8GQlompBVCarA5QtqUkGdxCSEl23H5R5ldSUi7kJCa7pSQogSzhBSZnBDS7khImyHk' \
			b'ILqEkOzmpGqITgZCDg9xtrcT8rb2y3lyEs7tkbOEeEo7pZwSTsl2jVS7CqLxmsVubs0iqh4dKdHYKRBN1ix2S9YsdrJmUcMIRIvWLIZYu2HNovqf3O5meGqMYlOrFfPkitNi+uR6uDFJLs2pkisfQmVFNoKtaHlix8sTRyiVLkgMwQmceBFix8sPu/VrD7uF' \
			b'aw9DLlMgSRnOAon9nQJJ1x4+kEWZZYca4elCC3F3otVGnlYYRXrLRbQGRgShi9+NpjTTSjPtSptpHUOtm4NaJ0cKNXYKUOsEat0SqHUCNQkjQK2LoNZFESvUxH9opnXcTOuiZlrHzbSOARdCGANcN9VMi5OQhV3swfTJ9XBjEnYqAYVdPgSEnZwq7/gyIK/j' \
			b'ZhoFHQWbA2CXAvAsLiGhZDsu/y4kYy0Vu4VU1HSnVBQlmKWiyOSEit2OzbQug8ZBdAkZ2c1J1RCdDGQcHuJsb2+mXd4GNaWZVpppT0M0z0Tzc0TzcqREY6dANC9E80uI5oVo8lwgmo+I5qOIlWjif7qZFp4ao5hf3UyL02L65Hq4MUkuzamSKx8CkstH2PIR' \
			b's/xUM82nlNLgBE6eyeSZSX49kPxCIGkuUyBJGc4Cif2dAsnv00zTvMUskgjPmmns7jQ38rTCaCguzvL6ZtrlbQtTIFQg9CQQ8jyT0s/NpAQPfCQQEieFkJeZlH7JTEovMyk1DIWQj2ZShlj9MJNS/U9CaHhqBEJ+avZkFkJJWkyfXA83piAUcioQGgkByslH' \
			b'0yV9NFfSVxMQ8unsyBAcQ8jzjEjPcyH9+omQfnwiZAKhkMsEQlqGcxASfycQ8tUuEPKZuY8a4SmExN2JVhvNFUMoKi7O8noIXd5mLOUDD6U/8Gr6Az1P2/Bz0zZQM+lIwcVOAVwybcMvmbbhZdqGhhHAFU3bCLH6YdqG+p8GV3hqDFxTUzWSaLMQiz2YPrke' \
			b'bkxCTHOtEMuHUMmvQiyapOHtIXzC3Y9Nz/Dp9Izz8IVqktW4nLshgysJt3B6RhBBSjgp7FnCsb9Twu04PcNnpmdEoksox25OqoCRh5Vyw0Oc7c39fvbyNlYptCu0ux7a8ZQOPzelA9WSjpR27BRoJ1M6/JIpHV6mdGgYgXbRlI4Qqx+mdKj/adqFp8ZoNzWl' \
			b'I4k2S7vYg+mT6+HGJO0010q7fAiVFTkJ7aLpHb6NaDfadEuneZyHL7STrMbl3NmQwZW0Wzj3I4ggpZ0U9izt2N8p7dodaZeZABKJLqEduzmpAkYeVtpFSs5luJl2l7dJSqFdod310M4x7dwc7ZwcKe3YKdDOCe3cEto5oZ2EEWjnItq5KGKlnfifpl3wN0Y7' \
			b'N0W7ONos7WIPpk+uhxuTtNNcK+3yISDtXEQ7F9HORbRzY7RzKe3OwhfaSVbjcu5syOBK2rmFtFMRpLSTwp6lHfs7pZ3bkXYuQ7tBdAnt2M1JFTDysNJueIizvZ12l7fhSaFdod310I5nNvq5mY2okHSktGOnQDuZ2eiXzGz0MrNRwwi0i2Y2hlj9MLNR/U/T' \
			b'Ljw1Rrup2YxJtFnaxR5Mn1wPNyZpp7lW2uVDQNpFUxl9NI/RdxHtxmYw+nQG43n4QjvJalzOnQ0ZXEm7hTMYgwhS2klhz9KO/Z3SbscZjD4zgzESXUI7dnNSBYw8rLQbHuJsb6fd5W1WUmhXaHc1tOt5Q5J+bkMSVD86EtqJk9Kulw1J+iUbkvSyIYmGobTr' \
			b'ow1JQqz9sCGJ+p+k3fDUCO36qU1IkmhztEs8mD657iOxjNMu5FpoNxIClFkf7UDSR9uP9GagXT+28UifbjxyHj7TTrMal3NnQwbX0a5fuPFIEEFCOy3sOdqJvxPa9TtuPNJnNh6JRBfTTtycVAEjDwvtooc429tpRxuPAGwK8TYTD+6DJl4P+ZpCv8fbuBLt' \
			b'GI7lMQWPdm7eJVYNOtIdLNlJMcjmmvawbBaAkDxRKhz/H3axbKJdLKMj7GIp8U6iEC2KeBzburKZ2royjje7dSXfwhANrwewTeaYpKF6CZtXDrut5kKqrAiNqYg/YfvKZqAiB5mhIslioOJ5+ExFzXRc7J2m6EiFs46MnOh5MgZxJGTUsp8jI+WuP9+1stlx' \
			b'18rmHI2SvLOZm+KO21Y2zEb+lW0rB6lzxmM2ohrQX1vT3+aeIQl/+5b+OvIDoCSv+EOYbKFqT0AysDGiYhaJqIpMQsKgoG8Eeqe4m10aQFgbhZdCi4CkMFIQjc3jj8GjkDEMlNUgmYPIKTzmoJEBxoPn5Z9C4gQOCAUCAsOAARCaPmsMf2LvM5Z+3syzjQ+2' \
			b'PRh2NeYLzPiYAV85dV7t9KRJHowx2dtgbIOlHZ/5HtvWYEzRjKL13GI3FxnNU3M5byhzVnKPee1npvHcKB71w2nBEJL9U+OHNsxN27D2scxY5sV91pLpOzrq/zKD1mWMWlsMW2zYglHLvfX66M0X/ECx8Bsw+IN62YBcYsPX9HiN2gHqAfIwIA82hi5+IwbV' \
			b'qcAwrnslplfWi7COdnwof62FjN5m636lpbTRYHywlqgVxWKOWUzU62AsUX5nBpN8SAOJ23mNGFGsIqLqqUUdmn0YGO37qrsJHbGZfqyH74rghYV3Tqh49yhReovspi2wu5gXycH8YqeIvYB3Sv/ADopLMMFm43vltZrP/U0nVVa2IZf0ool0nTCd9grNp3/Y' \
			b'u6aftnTdBVq69gKs3BW/YBbL9iDLhmV+YVbtZl4GH2TJ+oU9f/XlWLK9+wBPB6CegTXb3Ae40qIl1ozMyA1ZtJkZCw+xaNQyf95WraGtEzdaNmyYNveQAWyXQoKW2bhmq40bH9h/gJnrF5q5duNLW3vFps5f3svbuzF19unMXbvK3DVUNze+xNlbMXkNfW/j' \
			b'Xb3MQanvM4wrM5se72XORIZuzsg1dseWaXVFRu6SDdwm48Zm6GLe5Vza97bMuDXstGMLFQvwKo3bOzRszVPMT8ENPDe/vm1qodrS33ZdFu1iB2Ef1jLFkiz9bY9iycyTWLKHTFHZZMnK1JRiyS7DknXFkj2OJbOHV5c2X3hibcw7njt8yTasfYK5w5EdI4ty' \
			b'wWZstQmjpUq0LMnREqQLnEN8LWasoW+jbzJlD55DfPjv/h4YSyMG7eXZtk32DFKF2oJq9Txs2xa7Br9u+3va9byfPcliCFo32VBq7XO1ahsHQFlq5mFvae5GLBkoMWYUxXnZFi23TPgprBpc4wDUausWL3ZIFzkUSzdj6TAGWhR+rMleXYnFcxdk9I5Yepi2' \
			b'dr3tw4U50ZKFeKECWsJuf0sIgn8UYzi1R0N4tWuf2Bjaja94przmrTd+WGxPaQHdcjPYUHL9RRhB7LDY/uqHdeYpV8VuMYJnL4D+Ecxe/0St2cjc4ULDi3z/K+buBszdwj66xMphMV/D695NWrn+EZq51dNbOUhSsXLFyl2UlXPFyj2RlQOJ7m/l6guwcnWx' \
			b'csXKXZaV64qVeyorV9/IkMVVmLTrmRBXhh+eaMZI425taPUBc0Rq3Gy65mkikMpiqW7ZUu015e12LBZtAXbxFusGZ4PsMb/NN/dAHLJcpliuYrmei+WiVtGlvGpRYordWmW3cI9Jgk9/j3afLNgFLj8oFqxYsMeyYP6SLFh589rDgj35IoO13xd6gEFz0YeA' \
			b'bsGw1Y9s3GoxcM1tGzmq7amhq4d1VfTJqOH/Ixo+TgdJrF9kAevrsoA7fMJmgRlssJeAqnS9wRw++UqFYg6LOXxqc9icmsMmModN8v9RzWGzzhw2xRzmzGEt5rDZYA4fYblCMYc3Yg6fhSk0p6bQRKYw/f+optCsM4WmmMJ8A5lEs9oMPsLyhdLNV7r5HtvO' \
			b'kaW54TkhF2nLnr6fDzcdB8KR5XqMJQnFchXLtZvl4mCe3XS23UwXJk7/X7/pas39kasWvoVh9bpHuwxVDH7JonWPsfygWLRi0Xa0aKZYtAdZtOH/s7BoZalBsWggbhy4wt7ai7RudHGlqw84I09q3CgJuzU0JUP72TYKMGvb8BvkRyyQaStnu3viHyjUPbIE' \
			b'6t89GXSoPPdoikHx4deQvSsLFoq9u0wbZ6/Yxtmnt3F2Vxu38/sbBbj+/W2VZSsLGopluyDLVtaOPsiykfhud5jA2ntCH9Q0PHFkwcqChmLBntKCkQ0pq98fZMFYhs9goNP4eyIe1Dg8oe8sd0++oKFYsGdmwVhpywYeO5kwEeczmaxhzD0SEKod/PJ4wJOv' \
			b'QSgW7NYtGFe8C1hTeosG7HnNNjM4oFnTVkTdky8XKJbrViwX6/BlLQe4astFAi2GazBcNBMDrVOPXfx1QxaszPQvFmy7BSP9v+QFTVdtwcq716kJq6kLvybLVWb6F8v1EMv1SJMqiuUqlmvacvkyo79YrqWWCxX9MhZXFsv1TC0XNhupsehvZeI+pC182vgi' \
			b'jRhOUrmwTxpfzvDjLVkzLO4jPnkVdg2zeknWDUttu2lDi9YcXmGlsRaVFXWq6Rq6YQ6vOtxzB9wxK/CfnG3kTBvnVOTcHl41kLjG4ze7G9AY+P/NHZy/OILNRMca/R0hOjBVGBlYkZ7dDLqhlQKjgfUeqvUBxA+qDboAqgaZgIKF7KB1wZnPuE8LSAa/udxU' \
			b'mGKofSFysEIV/ke/2MoBvxXO7IPrBmfKQCRQVbCQsd7UoNNot7w8hbYBP3uEC3TALuBsX0/fcQYd3TOVYP2X/qPYW4y9Wxo/KCSCoF+QkBZ50Y7+q/tGLPvZPUqXm04XSBrEiR9ureiTX6PJrDip+AXq0+QqC+gzWGh7m5MsACjP/qG+8wdbh/9nfnr26ZOn' \
			b'0NajG336CqwM3aG8dk+dV+CLxc+NQ56B+rv9M5AaU1M9BjP88Dz6qWzWwIwaqlbt8bfPZ9tVE1mH2Bb/wxeS1IXRbwTzPr4DqYt8kjj6rDjw7aMfF4oluXQiGrSW0fZlY5KqRVpOPsPOk4wQrshzmtuNK2Vx0Qqt/TcsVVw30fKGpixhO0i5Q6lDOKDELHF8' \
			b'S21F8n5c+hAPv0j1JyVhh9LwnkqkgfQbMJym0tLBN8/zg94/Xe7OcL+KvegD8f8FT+YeywSTuTyPthrxk8tXcjcN7tQX6RW4Xnw9w9bNRRwssTpfFbEmH7BJwHUS3r3dmprZbKqcJqqg9bpKii2py6iozSFzxA1HcdQm4+Kjq9f4bqg1KGcY/ax3aJisCn/T' \
			b'wUrXFPu/Vq3M4bkerDLmCiy7PVzGwRKz+1Sy+qnrGXWIvdO65g87HNivt0tATxETa1C+dVzM9ITqYNvoeR6sMnt0XGT0Ym9TjZ3fOx3YIf+wIFhy+W6QUtnGKxsG8kwPVpl8r9KUviytb+4x6pw9nB84aJC9sfTA4a/tz7McR7qjQut3runbgkyrgzMH924q' \
			b'o4sqZM2VEocSqB0MfnDDYtdeSiXtDucHNvXlDGWd8zL4pUHU4f+0723HEK6cxT8WFaV9lHjTg0dy8l1YhQMTKuYPz/VglRnpw7tQDuDsjcs6WIr7dEo9UmVbI/3RyjRXkXBSzdmBsymyNxJPrZn3tPuxMFYu3nwHUrGrE+rQHJ7rwSoz0oO2n12td7et5vBI' \
			b'B84r2/owS7P0Jq2ugN3huR6sMvnepJ0rIKrGvpXQHx7vwLmdWx9moZaOprX1EOcVP9ODVebRO5pi1di1LuJ88Mc8cIr11odZtmUu1Orq6A7P9eCJvSNdRAuq4/YGKmnC2oboSAN0qJ3dYduB0/WX+8b1D7Q8oVrgt6uzN1jyIz0tpbKOVlZch/NMD1aZkW6l' \
			b'R62siXY8RsXFpVXv5IiXKj0sKC6Nq+kFigd0LqMiu8MFHvh1Zvox7yA2VqH1vUJ29zodK8xOdXu84LvDqgOXua195vzQdYjbA+hp7We0bhAuuQS390TJSO87HuO9SHPQH7YdnLWtT08fuGD1McKdO1it1vdWXbdhwAXVV39w0W3vE7uwuR8XYRtwmf0DDs5Y' \
			b'86AwZg9cz/6oEZwdrGnru9Ie10hsHV9ebSy6wxMeqMs7+uOi3N5zV4zGuYLglhzlSA5eIL99QlhRs4ya1YdypAer2T5dm5eCpy3vs7gL0K0dXLZlaht4uLmDy/ZqejQvZkgClzQ++KBlidH/3QIdfk5iiS4TP4uCzB2sPzstE31O+tMcnuvBKlNm8q1WGXN4' \
			b'rgerzEjfaFGZcZXxh+d6sMqUeYqrVaY/PNeDVWakc7WozKjK4A63z/RglSnTL1erTH14rgfvGVpW6K5WmebwXA9Wmfrwyra0Oxy/3LRNcGB0tQYdUOy02VeF+2PzDWifx4oEikA+oMgMTqaA4rW4C7jsZ9vmfUPhpv/ZtzvzjQVOT6B6pf8bJ2nv4i2MUW14' \
			b'z9rWs3u6YRT5QAUBUaD/jnc/R5UkFbSkdqhW6A6qw2GBWU5CIVW2J+qrqutRDTF03D892jud9yfvTvYkt7IfObhL6wT0+RVWGlBy2laEPrHAd+p0A2Z4zvPon2vwuiZXTrODImxoD2ZTydN2cAHb8c3d/wcq71VK'

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
		# ('CURLYL_L_PARENL', r'{\s*\\left\s*\('),
		# ('R_PARENR_CURLYR', r'\\right\s*\)\s*}'),
		('L_DOT',         r'\\left\s*\.'),
		('L_PARENL',      r'\\left\s*\('),
		('R_PARENR',      r'\\right\s*\)'),
		('L_BRACKL',      r'\\left\s*\['),
		('R_BRACKR',      r'\\right\s*\]'),
		('L_BAR',         r'\\left\s*\|'),
		('R_BAR',         r'\\right\s*\|'),
		('L_SLASHCURLYL', r'\\left\s*\\{'),
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

	# def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                       return PopConfs (AST.flatcat ('+', expr_add, expr_mul_exp))
	# def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                      return PopConfs (AST.flatcat ('+', expr_add, AST ('-', expr_mul_exp)))
	# def expr_add_3         (self, expr_add, SETMINUS, expr_mul_exp):                   return PopConfs (AST.flatcat ('+', expr_add, AST ('-', expr_mul_exp)))
	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                       return _expr_add (self, expr_add, expr_mul_exp)
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                      return _expr_add (self, expr_add, AST ('-', expr_mul_exp))
	def expr_add_3         (self, expr_add, SETMINUS, expr_mul_exp):                   return _expr_add (self, expr_add, AST ('-', expr_mul_exp))
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

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                            return PopConfs (AST.flatcat ('*', expr_mul_imp, expr_intg)) # _expr_mul_imp (self, expr_mul_imp, expr_intg) #
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

	def expr_attr_1        (self, expr_diffp_ics, ATTR, expr_pcommas):                 return PopConfs (AST ('.', expr_diffp_ics, (ATTR.grp [0] or ATTR.grp [1]).replace ('\\', ''), expr_pcommas.comma if expr_pcommas.is_comma else (expr_pcommas,)))
	def expr_attr_2        (self, expr_diffp_ics, ATTR):                               return PopConfs (AST ('.', expr_diffp_ics, (ATTR.grp [0] or ATTR.grp [1]).replace ('\\', '')))
	def expr_attr_3        (self, expr_idx):                                           return expr_idx

	def expr_idx_1         (self, expr_diffp_ics, expr_bcommas):                       return PopConfs (AST ('-idx', expr_diffp_ics, expr_bcommas.comma if expr_bcommas.is_comma else (expr_bcommas,)))
	def expr_idx_2         (self, expr_abs):                                           return expr_abs

	def expr_abs_1         (self, L_BAR, expr_commas, R_BAR):                          return AST ('|', expr_commas) if not expr_commas.is_comma_empty else _raise (SyntaxError ('absolute value expecting an expression'))
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                            return AST ('|', expr_commas) if not expr_commas.is_comma_empty else _raise (SyntaxError ('absolute value expecting an expression'))
	def expr_abs_3         (self, expr_paren):                                         return expr_paren

	def expr_paren_1       (self, expr_pcommas):                                       return AST ('(', expr_pcommas, is_paren_tex = expr_pcommas.is_commas_tex)
	def expr_paren_2       (self, expr_bracket):                                       return expr_bracket
	# def expr_pcommas_1     (self, CURLYL_L_PARENL, expr_commas, R_PARENR_CURLYR):      return expr_commas.setkw (is_commas_tex = True)
	def expr_pcommas_1     (self, CURLYL, L_PARENL, expr_commas, R_PARENR, CURLYR):    return expr_commas.setkw (is_commas_tex = True)
	def expr_pcommas_2     (self, L_PARENL, expr_commas, R_PARENR):                    return expr_commas
	def expr_pcommas_3     (self, PARENL, expr_commas, PARENR):                        return expr_commas

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
		'COMMA'          : ',',
		'PARENL'         : '(',
		'PARENR'         : ')',
		'CURLYR'         : '}',
		'BRACKR'         : ']',
		'BAR'            : '|',
		'SLASHCURLYR'    : '\\}',
		'L_PARENL'       : '\\left(',
		'L_BAR'          : '\\left|',
		'R_PARENR'       : ' \\right)',
		'R_CURLYR'       : ' \\right}',
		'R_BRACKR'       : ' \\right]',
		'R_BAR'          : ' \\right|',
		'R_SLASHCURLYR'  : ' \\right\\}',
		# 'R_PARENR_CURLYR': ' \\right)}',
	}

	_AUTOCOMPLETE_COMMA_CLOSE = {
		'CURLYL'         : 'CURLYR',
		'PARENL'         : 'PARENR',
		'BRACKL'         : 'BRACKR',
		'SLASHCURLYL'    : 'CURLYR',
		'SLASHBRACKL'    : 'BRACKR',
		'L_PARENL'       : 'R_PARENR',
		'L_BRACKL'       : 'R_BRACKR',
		'L_SLASHCURLYL'  : 'R_SLASHCURLYR',
		# 'CURLYL_L_PARENL': 'R_PARENR_CURLYR',
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

		# if rule [0] == 'expr_intg' and pos == len (rule [1]) - 1 and self.autocompleting:
		# 	return self._parse_autocomplete_expr_intg ()

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_sub' and stack [-1 - len (rule [1])].sym == 'INTG':
				return self._insert_symbol ('CARET1')

			return self.parse_result (None, self.pos, []) if self.rederr else False

		return self._insert_symbol (rule [1] [pos])

	def parse_success (self, red):
		self.parse_result (red, self.erridx, self.autocomplete)

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

	# a = p.parse (r"""Union(Complement(Union(Complement(Matrix([Le(Union(Complement(Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)), a), Complement(a, Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)))), ('s', 1.0, dx))])**(a[0.1, a])**partial**3 / (partialz**3*1e-100), diff(diff(FiniteSet(2, partialy)))), Complement(diff(diff(FiniteSet(2, partialy))), Matrix([Le(Union(Complement(Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)), a), Complement(a, Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)))), ('s', 1.0, dx))])**(a[0.1, a])**partial**3 / (partialz**3*1e-100))), -xyzd*FiniteSet()), Complement(-xyzd*FiniteSet(), Union(Complement(Matrix([Le(Union(Complement(Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)), a), Complement(a, Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)))), ('s', 1.0, dx))])**(a[0.1, a])**partial**3 / (partialz**3*1e-100), diff(diff(FiniteSet(2, partialy)))), Complement(diff(diff(FiniteSet(2, partialy))), Matrix([Le(Union(Complement(Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)), a), Complement(a, Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)))), ('s', 1.0, dx))])**(a[0.1, a])**partial**3 / (partialz**3*1e-100)))))""")
	# a = p.parse (r"""Union(Complement(Union(Complement(((FiniteSet(diff(partialx), -tau57, [[-28832738.092809968, 1., 's']]), Sum(xanddz*Matrix([-1, False]), (x, xyzdin1e + 100*notin*diff(partialyin)*diff(s), partial)))), (FiniteSet(-13.574245287492392, partialx, dx)**d**5 / (dy**3*dz**2*Noneord**1)) / (dz**1*partialx**{}*orz20)), Complement((FiniteSet(-13.574245287492392, partialx, dx)**d**5 / (dy**3*dz**2*Noneord**1)) / (dz**1*partialx**{}*orz20), ((FiniteSet(diff(partialx), -tau57, [[-28832738.092809968, 1., 's']]), Sum(xanddz*Matrix([-1, False]), (x, xyzdin1e + 100*notin*diff(partialyin)*diff(s), partial)))))), 0.006826903881753888), Complement(0.006826903881753888, Union(Complement(((FiniteSet(diff(partialx), -tau57, [[-28832738.092809968, 1., 's']]), Sum(xanddz*Matrix([-1, False]), (x, xyzdin1e + 100*notin*diff(partialyin)*diff(s), partial)))), (FiniteSet(-13.574245287492392, partialx, dx)**d**5 / (dy**3*dz**2*Noneord**1)) / (dz**1*partialx**{}*orz20)), Complement((FiniteSet(-13.574245287492392, partialx, dx)**d**5 / (dy**3*dz**2*Noneord**1)) / (dz**1*partialx**{}*orz20), ((FiniteSet(diff(partialx), -tau57, [[-28832738.092809968, 1., 's']]), Sum(xanddz*Matrix([-1, False]), (x, xyzdin1e + 100*notin*diff(partialyin)*diff(s), partial)))))))); Derivative(dy, y); Function('u', commutative = True, real = True); psi, y1""")

	# for v, k in sorted (((v, k) for k, v in p.reds.items ()), reverse = True):
	# 	print (f'{v} - {k}')
	# print (f'total: {sum (p.reds.values ())}')


	# a = p.parse (r"dsolve (y(x)'' + 11 y(x)' + 24 y(x), ics = {y(0): 0, y(x)'(0): -7})")

	# a = p.parse (r"\int oo + 1 dx")
	# a = p.parse (r"\int oo + 1 dx b")
	# a = p.parse (r"\int d/dx x**2 dx")
	# a = p.parse (r"\int x dx b")
	# a = p.parse (r"\int 1 / dx dy")
	# a = p.parse (r"\int dx / dx + 2")
	# a = p.parse (r"\int dy / dx + 2 dz")
	# a = p.parse (r"\int a/dx * partial**2 / partialz**2 (partialx) dx")
	a = p.parse (r"\int N N dx")
	print (a)



	# a = sym.ast2spt (a)
	# print (a)
