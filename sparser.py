# Builds expression tree from text, nodes are nested AST tuples.

import ast as py_ast
from collections import OrderedDict
import os
import re
import sys

from lalr1 import Token, State, PopConfs, Reduce, LALR1 # , KeepConf # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sxlat         # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

ALL_FUNC_NAMES = AST.Func.PY | AST.Func.TEX | {'sech', 'csch', AST.Func.NOREMAP, AST.Func.NOEVAL}
RESERVED_WORDS = {'in', 'if', 'else', 'or', 'and', 'not', 'sqrt', 'log', 'ln', 'Function', 'Symbol'} | AST.Func.PY

_SP_USER_FUNCS = set () # set of user funcs present {name, ...} - including hidden N and gamma and the like
_SP_USER_VARS  = {} # flattened user vars {name: ast, ...}

def _raise (exc):
	raise exc

def _is_valid_var_name (self, text):
	toks = self.tokenize (text)

	return toks == ['VAR', '$end'] and not toks [0].grp [4]

def _FUNC_name (FUNC):
	if FUNC.grp [1]:
		return AST.Func.TEX2PY_TRIGH_INV.get (FUNC.grp [1], FUNC.grp [1])

	else:
		func = (FUNC.grp [0] or FUNC.grp [2] or FUNC.text).replace ('\\', '')

		return f'{func}{FUNC.grp [3]}' if FUNC.grp [3] else func

def _ast_from_tok_digit_or_var (tok, i = 0, noerr = False):
	return AST ('#', tok.grp [i]) if tok.grp [i] else \
			AST ('@', AST.Var.ANY2PY.get (tok.grp [i + 2].replace (' ', ''), tok.grp [i + 1]) if tok.grp [i + 2] else tok.grp [i + 1])

def _ast_func_tuple_args (ast):
	ast = ast.strip_curly.strip_paren1 # ast = ast._strip (1) # ast = ast._strip_curly_of_paren_tex.strip_paren1 # ast = ast._strip (1)

	return ast.comma if ast.is_comma else (ast,)

def _ast_func_sxlat (func, args, **kw):
	return sxlat.xlat_funcs2asts (AST ('-func', func, args, **kw), sxlat.XLAT_FUNC2AST_SPARSER, recurse = False)

def _ast_func_reorder (ast, unconditional = False):
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
		ast3, wrap3 = _ast_func_reorder (ast2, unconditional = unconditional)

		if unconditional or ast3.op in {'{', '(', '[', '-lamb'}: # ast3.is_curly or ast3.is_paren or ast3.is_brack:
			return ast3, lambda a: wrap2 (wrap3 (a))

	return ast, lambda a: a

def _ast_var_as_ufunc (var, arg, rhs, force_implicit = False): # var guaranteed not to be in _SP_USER_FUNCS
	if var.var != '_' and arg.is_paren and var.is_var_nonconst: # f (vars[, kws]) -> ('-ufunc', 'f', (vars)[, kws]) ... implicit undefined function
		argskw = arg.paren.as_ufunc_argskw
		ufunc  = _SP_USER_VARS.get (var.var, AST.Null)

		if ufunc.is_ufunc:
			ast = ufunc.apply_argskw (argskw) # AST ('-ufunc', ufunc.ufunc_full, *argskw, src_rhs = rhs, src_var_name = var.var)

			if ast:
				return ast.setkw (src_rhs = rhs, src_var_name = var.var)

		elif ufunc.op is None and (force_implicit or AST.UFunc.valid_implicit_args (argskw [0])):
			return AST ('-ufunc', var.var, *argskw, src_rhs = rhs)

	return None

def _ast_diff_func_apply_call (var, expr, arg):
	func = _SP_USER_VARS.get (var, expr [1])
	args = arg.comma if arg.is_comma else (arg,)

	if func.is_lamb:
		if len (args) == func.vars.len:
			subs = tuple (filter (lambda va: va [1] != va [0], zip ((AST ('@', v) for v in func.vars), args)))

			return AST ('-subs', expr, subs) if subs else expr

	elif func.is_ufunc_applied:
		ast = func.apply_argskw (arg.as_ufunc_argskw)

		if ast:
			return AST ('-subs', expr, ast.ufunc_subs) if ast.ufunc_subs else expr

	return None

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
		return AST (*tuple (_ast_mulexps_to_muls (a) for a in ast))#, **ast._kw)

def _ast_tail_differential (self, want_pre = False, from_add = False): # find first instance of concatenated differential for integral expression -> pre, dv, wrap -> wrap (\int pre dv), pre may be None, if dv is None then rest are undefined
	lself = lambda a: a

	if self.is_differential or self.is_var_null: # AST.VarNull is for autocomplete
		return None, self, lself, lself

	elif self.is_minus:
		pre, dv, wrap, wrapp = self.minus.tail_differential

		if dv:
			return pre, dv.setkw (dv_has_neg = dv.dv_has_neg or not pre), wrap, lambda a: AST ('-', wrapp (a)) if (not a.is_num_pos or from_add) else wrapp (AST ('#', f'-{a.num}'))

	elif self.is_fact:
		pre, dv, wrap, wrapp = self.fact.tail_differential

		if dv:
			return pre, dv, lambda a: AST ('!', wrap (a)), wrapp

	elif self.is_add:
		pre, dv, wrap, wrapp = self.add [-1].tail_differential_from_add

		if dv and pre:
			return AST ('+', (*self.add [:-1], wrapp (pre))), dv, wrap, lself

	elif self.op in {'*', '*exp'}:
		for i, ast in enumerate (self.mul):
			pre, dv, wrap, wrapp = ast.tail_differential

			if dv:
				if want_pre and (pre or not i):
					want_pre = False

					if ast is not self.mul [-1]:
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

		pre, dv, wrap, wrapp = self.denom.tail_differential_want_pre

		if dv and pre:
			return AST ('/', self.numer, wrapp (pre)), dv, wrap, lself

	elif self.is_pow:
		pre, dv, wrap, wrapp = self.base.tail_differential

		if dv and (pre or not want_pre):
			return pre, dv, lambda a: AST ('^', wrap (a), self.exp), wrapp

		pre, dv, wrap, wrapp = self.exp.tail_differential_want_pre

		if dv and pre:
			return AST ('^', self.base, wrapp (pre)), dv, wrap, lself

	elif self.is_func:
		if self.src:
			if not want_pre and self.src.mul [0].is_differential and self.func in _SP_USER_FUNCS:
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

	elif self.op in {'-lim', '-sum'}:
		pre, dv, wrap, wrapp = self [1].tail_differential_want_pre

		if dv and pre:
			return AST (self.op, wrapp (pre), *self [2:]), dv, wrap, lself

	return None, None, None, None

AST._tail_differential          = _ast_tail_differential # adding to AST class so it can be cached and accessed as member
AST._tail_differential_want_pre = lambda self: self._tail_differential (want_pre = True)
AST._tail_differential_from_add = lambda self: self._tail_differential (from_add = True)
AST._has_tail_differential      = lambda self: self.tail_differential [1]

#...............................................................................................
def _expr_ass_lvals (ast, allow_lexprs = False): # process assignment lvalues ... {a}, {b = x}, {y} -> {a, b} = {x, y}
	def can_be_ufunc (ast):
		return (
			(ast.is_func and ast.func in _SP_USER_FUNCS and all (a.is_var_nonconst for a in ast.args)) or
			(ast.is_mul and ast.mul.len == 2 and ast.mul [1].is_paren and ast.mul [0].is_var_nonconst and ast.mul [1].paren.as_ufunc_argskw))

	def as_ufunc (ast):
		if ast.is_func:
			return AST ('-ufunc', ast.func, ast.args)
		else: # is_mul
			return AST ('-ufunc', ast.mul [0].var, *ast.mul [1].paren.as_ufunc_argskw)

	def lhs_ufunc_explicitize (ast):
		if not allow_lexprs and (ast.is_ufunc_py or (ast.is_ufunc and ast.kw)):
			return AST ('-ufunc', f'?{ast.ufunc}', *ast [2:])
		elif ast.src_var_name:
			return AST ('-ufunc', f'{ast.src_var_name}', *ast [2:])
		else:
			return ast

	# start here
	if ast.is_ass: # if assigning to function call then is assignment to function instead, rewrite
		if can_be_ufunc (ast.lhs):
			ast = AST ('=', as_ufunc (ast.lhs), ast.rhs)
		else:
			ast = AST ('=', lhs_ufunc_explicitize (ast.lhs), ast.rhs)

	elif ast.is_comma: # tuple assignment? ('x, y = y, x' comes from parsing as ('x', 'y = y', 'x')) so rewrite
		vars = []
		itr  = iter (ast.comma)

		for c in itr:
			if c.op in {'@', '-ufunc'}:
				vars.append (lhs_ufunc_explicitize (c))
			elif can_be_ufunc (c):
				vars.append (as_ufunc (c))

			elif c.is_ass:
				t = (c.rhs,) + tuple (itr)
				v = lhs_ufunc_explicitize (c.lhs) if c.lhs.op in {'@', '-ufunc'} else as_ufunc (c.lhs) if can_be_ufunc (c.lhs) else c.lhs if allow_lexprs else None

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
		return AST ('-lamb', lamb, (args.var,), is_lamb_mapsto = True)
	elif args.is_comma and all (v.is_var_nonconst for v in args.comma):
		return AST ('-lamb', lamb, tuple (v.var for v in args.comma), is_lamb_mapsto = True)

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

	if self.in_intg () and lhs.has_tail_differential:
		return Reduce (ast)#, keep = True)

	return PopConfs (ast)

def _expr_mul_exp (self, lhs, rhs): # fix side-effect of integral parsing
	if lhs.is_mulexp:
		if lhs.mul [-1].is_differential and self.in_intg ():
			return Reduce (AST.flatcat ('*exp', lhs, rhs))

	return PopConfs (AST.flatcat ('*exp', lhs, rhs))

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

		for i, n in enumerate (ns):
			if n.is_ufunc: # implicit ufunc created for last differential reverts back to differential followed by paren
				if n.is_ufunc_explicit or cp != 1:
					break

				v   = n.src_rhs # AST ('(', AST.tuple2ast (n.vars))
				n   = AST ('@', n.ufunc)
				ns  = ns [:i] + (n, v) + ns [i + 1:]
				ast = AST ('/', ast.numer, AST ('*', ns))

			if ast_dv_check (n):
				dec = 1
				ds.append ((n.var_name, 1))

			elif n.is_pow and ast_dv_check (n.base) and n.exp.strip_curly.is_num_pos_int:
				dec = n.exp.strip_curly.as_int
				ds.append ((n.base.var_name, dec))

			else:
				break

			cp -= dec

			if cp < 0:
				break

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

				break

		return None, None

	def try_apply_ics (ast, arg): # {d/dx u (x, t)} * (0, t) -> \. d/dx u (x, t) |_{x = 0}, {d/dx u (x, t)} * (0, 0) -> \. d/dx u (x, 0) |_{x = 0}
		if arg.is_paren:
			diff = ast.diff.strip_paren1
			ast2 = _ast_diff_func_apply_call (diff.var, AST ('-diff', diff, ast.d, ast.dvs), arg.paren)

			if ast2:
				return ast2

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

def _expr_div (numer, denom):
	if denom.is_mulexp: # correct for wonky \int ... dv parsing
		return AST ('*exp', (('/', numer, denom.mul [0]), *denom.mul [1:]))

	if denom.is_mul:
		for i, ast in enumerate (denom.mul):
			if ast.is_mulexp:
				return AST ('*exp', (('/', numer, ('*', (*denom.mul [:i], ast.mul [0]))), *ast.mul [1:]))

	return AST ('/', numer, denom)

def _expr_mul_imp (self, lhs, rhs): # fix side-effect of integral parsing
	if rhs.is_div:
		if rhs.numer.is_intg:
			return PopConfs (AST ('/', AST.flatcat ('*', lhs, rhs.numer), rhs.denom))
		elif rhs.numer.is_mul and rhs.numer.mul [0].is_intg:
			return PopConfs (AST ('/', AST.flatcat ('*', lhs, rhs.numer), rhs.denom))

	elif rhs.is_mulexp:
		if rhs.mul [0].is_div and rhs.mul [0].numer.is_intg:
			return PopConfs (AST ('*exp', (('/', ('*', (lhs, rhs.mul [0].numer)), rhs.mul [0].denom), *rhs.mul [1:])))

	elif lhs.is_mul:
		if lhs.mul [-1].is_differential and self.in_intg ():
			return Reduce (AST.flatcat ('*', lhs, rhs))

	return PopConfs (AST.flatcat ('*', lhs, rhs))

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
		ast = _ast_diff_func_apply_call (lhs.diffp.var, lhs, commas)

		if ast:
			return ast

	return Reduce

def _expr_func (iparm, *args, is_operatorname = False): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	is_func    = args [0] == '-func'
	is_pseudo  = is_func and args [1] in {AST.Func.NOREMAP, AST.Func.NOEVAL}
	rhs        = args [iparm]
	arg, wrapa = _ast_func_reorder (rhs, unconditional = is_pseudo)

	if is_func:
		name = args [1]

		if is_operatorname and name not in _SP_USER_FUNCS and name not in ALL_FUNC_NAMES: # \operatorname ufunc like SymPy writes out, will not catch unparend arg - shouldn't need to
			ast = _ast_var_as_ufunc (AST ('@', name), arg, rhs, force_implicit = True)

			if ast:
				return wrapa (ast)

		src = AST ('*', (('@', name), rhs))

		if arg.is_paren:
			ast2 = _ast_func_sxlat (name, _ast_func_tuple_args (arg), src = src)
		else:
			ast2 = AST ('-func', name, _ast_func_tuple_args (arg), src = src)

		if is_pseudo and ast2.is_func and ast2.args.len != 1:
			raise SyntaxError (f'no-{"remap" if ast2.func == AST.Func.NOREMAP else "eval"} pseudo-function takes a single argument')

	else: # args [0] in {'-sqrt', '-log'}:
		fargs    = arg.strip_curly.strip_paren1 if args [0] == '-log' or (not arg.is_paren_tex or arg.paren.op in {',', '-slice'}) else arg.strip_curly
		ast2     = AST (*(args [:iparm] + (fargs,) + args [iparm + 1:]))
		ast2.src = AST ('*', (AST.VarNull, rhs)) # VarNull is placeholder

	return wrapa (ast2)

def _expr_func_func (FUNC, args, expr_super = None):
	istok = isinstance (FUNC, Token)
	func  = _FUNC_name (FUNC) if istok else FUNC

	if expr_super is None:
		return _expr_func (2, '-func', func, args, is_operatorname = istok and FUNC.grp [2])
	elif expr_super.strip_curly != AST.NegOne or not AST ('-func', func, ()).is_func_trigh_noninv:
		return AST ('^', _expr_func_func (FUNC, args), expr_super, is_pypow = expr_super.is_pypow)
	else:
		return _expr_func_func (f'a{func}', args)

def _expr_ufunc_ics (self, lhs, commas): # ufunc ('f', ()) * (x) -> ufunc ('f', (x,)), ufunc ('f', (x,)) * (0) -> ufunc ('f', (0,)), ...
	if lhs.is_ufunc_py:
		ast = lhs.apply_argskw (commas.as_ufunc_argskw)

		if ast:
			return PopConfs (AST ('-ufunc', lhs.ufunc_full, (commas.comma if commas.is_comma else (commas,)), lhs.kw))#, is_ufunc_py = lhs.is_ufunc_py))

	return Reduce

def _expr_ufunc (self, args, py = False, name = ''):
	if py:
		args, kw = AST.args2kwargs (args.comma if args.is_comma else (args,))

		if len (args) != 1 or not args [0].is_str:
			raise SyntaxError ('Function() takes a single string name argument')

		name   = args [0].str_
		argskw = ((), tuple (sorted (kw.items ())))

	else:
		argskw = args.as_ufunc_argskw

		if not argskw:
			raise SyntaxError ('invalid undefined function arguments')

	if name and (name in RESERVED_WORDS or not _is_valid_var_name (self, name)):
		raise SyntaxError (f'invalid undefined function name {name!r}')

	if AST ('@', name).is_var_const:
		raise SyntaxError ('cannot use constant as undefined function name')

	return AST ('-ufunc', f'?{name}', *argskw, is_ufunc_py = py)

def _expr_varfunc (self, var, rhs): # user_func *imp* (...) -> user_func (...)
	arg, wrapa = _ast_func_reorder (rhs)

	if var.var in _SP_USER_FUNCS:
		if arg.is_paren:
			return PopConfs (wrapa (_ast_func_sxlat (var.var, _ast_func_tuple_args (arg), src = AST ('*', (var, arg)))))
		elif not (arg.is_curly and arg.strip_curly.is_paren) and var.var not in {'beta', 'Lambda'}: # special case beta and Lambda reject if they don't have parenthesized args (because they take two)
			return PopConfs (wrapa (AST ('-func', var.var, (arg,), src = AST ('*', (var, arg)))))

	else:
		ast = _ast_var_as_ufunc (var, arg, rhs)

		if ast:
			return PopConfs (wrapa (ast))

	return Reduce

def _expr_sym (self, args, py = False, name = ''):
	args, kw = AST.args2kwargs (args.comma if args.is_comma else (args,))

	if py:
		if len (args) != 1 or not args [0].is_str:
			raise SyntaxError ('Symbol() takes a single string name argument')

		name = args [0].str_

	elif args:
		raise SyntaxError ('$ does not take direct arguments, only keyword assumptions')

	if name and (name in RESERVED_WORDS or not _is_valid_var_name (self, name)):
		raise SyntaxError (f'invalid symbol name {name!r}')

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
		if not subs.comma:
			return expr

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

def _expr_vec (self, ast):
	e = ast.comma if ast.is_comma else (ast,)

	if all (r.is_brack for r in e):
		if len (e) == 0:
			return AST.MatEmpty

		elif len (e) == 1 or len (set (r.brack.len for r in e)) == 1:
			if e [0].brack.len == 1:
				return AST ('-mat', tuple ((r.brack [0],) for r in e))
			elif e [0].brack.len:
				return AST ('-mat', tuple (r.brack for r in e))
			else:
				return AST.MatEmpty

		cols = max (r.brack.len for r in e)

		if not all (r.brack.len == cols for r in e):
			return self.mark_incomplete (AST ('-mat', tuple (r.brack + (AST.VarNull,) * (cols - r.brack.len) for r in e)))

	return AST ('-mat', tuple ((r,) for r in e))

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
				return AST ('{', ast if not ast.is_paren else ('(', ast.paren, True))

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
		LALR1.__init__ (self)

		self.TOKENS_LONG.update ([(v, self.TOKENS [v]) for v in self.TOKENS_QUICK])

	def set_quick (self, state = True):
		self.TOKENS.update (self.TOKENS_QUICK if state else self.TOKENS_LONG)
		self.set_tokens (self.TOKENS)

	_PARSER_TABLES = \
			b'eJztfWmP5DiS5Z9ZoDMBOSCRFEXlt7q6tzB1TR2900gUClnHDApbF+raHjTmv6+dFCmnXPJwj/AjiFSGS5SRIs2M71G89OL1Xz575+MPPv7oL81f/td3P30LP3r5zheffvCPD+Dkg68+eevT9z7C03jywVdvf/rWO/+Gp/Hki79+8dE7n/xDz+D3o48/h7+f' \
			b'ffE2/v3grc/+t5z+40MSg1/4+/e3PqUE32VhFOPTt9/721fvvPXZe5/J+Ydvaejb0+nfp9NP+JRSiJn6K5zITye/Bn4/fP+jLyjd9z/6+EP97fTEUIYooaiF/EoK+NnnmPf3Pvzk83989h4+/P2PPv8bFvwLTPSD9z+k4tPff/8U73+Amv3g47+xCqnk/Ped' \
			b'jz/88C3VOgZ8ylr/VLXOYVSuT1XrEvYW/045/DTLL2Xx3+HPWx9+An/fffsDuoehH70rWsWzt6fTv0+notX3PvjsPQlRm2BCn3PmIYMo9OFbn3z2+ceY40/f/5DE/+Md1NZbn38exVDJ777/9/ffxfvviNE5mU8+IJuAJtU8//HZe++QwLvv//Wv6Fgfvc++' \
			b'SSV566N3UeV442OMT4/+P+xj+NOx80Hq7/wbnP72x9e//fnm19/+TM5/g/Nv3vz63e9f/fzrV99+/cNvv7/5NbkNp9/98xe48/2fP+o53JtOf/nuV7346bv/+urNr/8Flz+++f2rb37+Qc5+/fn/TWf8vN++++23b+LZL/FMk3rzdTz9/tt/xtDff48P+883' \
			b'3/yu57/QAzj4j5++mfL8n//5S3bx1fff/DZlPRboh+/j6U9T6O/f/RrPf/zjh6++/zEm9s0fv/7w34lq9PTr73/6+cdEHTFXv775Jk0KTvTyz+/inTfffhuF3sTC/fO376aSkpZiCbBMiVHijT9++v7nn+KN/445+v6n32OWwLho8cSW30zlg5upIv98M9n4' \
			b'55iXP1KRNz99m4Wnmv76m59//PFNvPw5JvY1qOX/fjeZMZf75fvvvvkuXoCL/jRp55fffv85Pjq6TSzJzz9M5adEs4vfkphf/fDnmx8mjXLML5vXL3beNt6+bPjE4Ulv8I9tev9SLuGKzhyKNX3f7OSWBvCV1XgQwWkQnpLUbqCQrnnhIBTEupcxwGGAcxqw' \
			b'G/HEdvxnQHH7Mg0yw17Q4NIgPIWzzvOfYWx2XXgpQXgKZwP8Dw2UYcd3BjyBXygvRXYj/nGNDxCDMzsF6eWubylV0ISnQowv9XqgUracJciIgXQs/Z+CxvTStnKCYZgI5KRz8aynzIXmRQeJgFW8eSkhO45pOv4zQIhhm8AVnqJayQhoy5fJpZ4n4YZ/wMRY' \
			b'Qvrver3t8AQzKeGc9WbnJJCvIY9kg6Y3UwBpx0/XhgTsLGCS2DkqlOv5j+cbmBXHWXNyqbaBvDnO3MB/hhZKwTctGoO8yoOS0H3khu/0hgti2+GlXIJ9KS48yKB3oWEkexjUp5fGywmGYXSwroPn9+IpejnOg8RL8uBu/3IW0exf7kv4PFlr9y+zSDvHdbQV' \
			b'dXZSIzGZjtwJTIxq8FIUy0rU4ELQdLlz5FmQrxdgXbjuxiZgJht8shX/2r+LwDTYDUJg1Vxo56geo13HxkcfxurMNa3FStuhCvqmH7TuYnAMjCGm5ZAwhXQcMsUyhkJ8qyE7S2W2lv8MXcxeDDJpEJ7i2ch/QG0vX06neNaz92oU9EG2GeLCZG68RLnpEgxK' \
			b'SCJyioYIFWRacDJOqbP8J0BmO/bvztIp6RGrm5xQ2boO6zYD+KDVFwMlKF73dC2PbeUZWEMbrIOFcA2BAMrgIF4pCodrqKQkQ/9BkNEGIY98buA/AziF4TioEsMwAE8KqHB2cbgMpB8DFaPzzE8NZBtEvNFi0c2Buap0E7CYcoa+P4p/9qwHrR3inFbtAYEv' \
			b'/FQv6dLFbMGlp+wC/rwgK0h1wktH6e8FzSX0kpkEgYyxCuHIGD1znZwxceKJ0xPySSj3i4kI8WrMnq8h8WpnmBl7udQ7iNjkaKbnPwPKsp8gphr2wrERwjNUCD5j38MTtnArAlJPsI4apiKACGNTAjakVBQa+c/QT+jEuIUKH/hP0sYZhAp7z3+oecPZlVM8' \
			b'6/XmS7mEK73BHgY5Cj25jFOX8drU8NSQ6jU6eoCn0vteb2D7SULgDJpur1vQAv6H5lCHDglcCG4GuAfeBXyHCDk2YD+o2SOiHAiHoQkBtAjROnTvHv4DAoJ5ug61a+G/a4C7QV1dC5ItRIMmAcg4NAjEA1EIh2d1DkPh0qEcXLdwDdrqAGwAlyxegdeBAjrI' \
			b'fQfU2EFwh+GQuw6y11lME/IBjZkOmoodPgeqaAdNmo6MDAWBA2ICRHSgrTA2Y9uMUCDTjLYZMU3IQIMFwedBelCTx74ZfTMO0EJqqFWL4N+1kPmWmo6QPFgc4BkNNhBsBQB/ZGHIzRiaEdIBxXWguQ702Tl8iMNWJAAT4GJA7YAqAahcA0YNmG+Ig0k69B0o' \
			b'EJTHA7QN2Hz0I7ZFAP0B7YHKoKkKzjeg4tEYUMdbxEAoMRQYKihUiAF1ihDTGWylwynYnswNpn+BNscA/nmN7We8RKO8JOYnKcw13kVtvyTGpLsd3X2NCEXXlHb1lzvylxcjG75jC4vXvH4RBnEj9o/ADkHWpV/xJjIzBXj5lXhoYEqIjI++QylU6LlfV0Jb' \
			b'22rk+zeyq0a+byNjjww1A4ygfMvsQOCOPmAY9cNYPeG+PQFM7auN793GpH2s3z017xJjfUk9yAwC/MqQ3cRQafg5aviRnvPovRMBTafldMSmakuxk9hFLZLqP+pddc36ZYWmynsaxSV+PvftmU/PvVm8eJv/5n7L/lrwU/HN1CVTV5w5Ycn9wOXIoC0bFDPD' \
			b'DfhemvT89lcVfRZFvxi1ykm1sFKP+k7e23t5s+q91BvrSvXPipjGlzf4jl/hC/XR6htfb+QVz+gTpROgq5j/DDDfDNXId2/krtr4vm38ghTCqG0Zz33staUAHHCD/DR946utb9vW3AIAU3uhbrG4tLC1xTZyKx6e2cFDO4/aQMXAgzw2rV31g5v2A7BwVy18' \
			b'5xY21cJ3bmFbLXzPFn4xRrYmeh75RX302q/SMk3XzqxH7Mzq6wjFvVczLBRVrIGrG7eNj/WX1Bot2slC0r6XJO35klRQaHmIrVc4kO6Yh6ZrW06X3wYfnIyRzkHp8x1D7fI9Ixy52uV252gENuZ+fR5Jq6a+X1O/6DvpfdG5cI57ZQbujhlkmBNzBTltUSsg' \
			b'iTYE9VXM3DZM1jnt4xLiHLh+BSb9wB0hOGUd56QkCq4jx09sqSB9kq20wwIbLnBtCL1MJPUy6KijkFZnlFJT44U05gwnJl3aA88tSKxLekK4ldkFMljKQ5r5gKeOanp+sueWjQ+1dp6hReO5Ng5t1eYZtDkwowzCI/aQUhXzqnK3wdMgwCMT3T2r2ghX6xha' \
			b'bbXdeavtNa2MMS/rOqh7tzM83PAKJ1PXLN2ZbUFhhpepVdvel21xqaGRBWnwW414i0ak5YO1Zt6bUdFSRhZ7wm81542bsyX6FOXX5RhX+NbKy6e5ztn6anrfNRKXyKup+ddJU4jItNbQa6yhuBSWjBSovVrn3t57JTWeK6cbpZLKsIcTP0BTmL01lI5fWNE2' \
			b'JJWNEerIYe0/P3Gs0MhSOlJyRchrMUs/SNUAMTRMNciFDWK1YWHlhY770+YLRb1IGWqCVnNdDNaEcoyQSCd28Vydqj2e1h7Wsv55boIQucxukNmTPMSoE71JvprmSV6XXdX1k+m6r7p+IsgZW4X8Qdb4BvntFWRkehO9ZdJuDjzTHJcK0nspdyONgl0jN5Gr' \
			b'yR6veoy+qviRG0Ztyw2iXsYMPTn5OdZpvK77Vd5/V47saBQnbnsBx55qLugbCl5r7FlBkV9hHr48iXvIR/5x0q8gXXE9osGXNP+e+9iE46ZOtWqmzZuA7XVIVt1t1t3evN2qu826cyetBuh449Kq+4fonnd7PSWhImZ3vA0Rrdwxmd1oolBb+7AuYe3QSc9v' \
			b'cQehjufFn98XeONgWhxkeHGQ4cVBNGBj+dljvCIgMAwExOncFY1IsNdfPUhrgB9RG+533HDv2W16dgYv4xR+qO29hy7j4lpW9/28+6rjpatkaGtleeBCMhl+G0zV4EPXOdqquod2ecpQcNtYXtyEPwjRL+lDhPgT6Iqna1uZrm1f6oxfm37HAXVj45RDnoKo' \
			b'11amIEoE/DE9pxz4QaN0uBivD6QqUfnjjvkDVW1lkpVN9ivn2T0220/cirtgiE12pqUZDVZmNLCbiaCXJEpvJTjuzk+mKkCNvbqn7a07FE6WoEZ8XVFy+6YU1tjb6dCVg/tCMJKK1aFuI0PcNPuszp6+CxfhQbZqxls2I04qsTypxPKkEqnIliuylUF5/PUs' \
			b'00uzgT93UsdWH+Gtivc6rXs2nnd5D7dQnfywT/f89jVIE7iVJXqtrNuy2rdupKeAYtUxjicf42gPvE3gEIeRoQjLQxGWhyIs32ZTy6uLl3dqz+/HNCP7S9r3yvKGTZY3bGJ/mN6/Xd3C4DYpjnszXOwL+ZK7PdxLaaF+2UydJ6BCJ2+zjt5MCSO0GSsgMc3L' \
			b'ZC/pQwQHtzwQB8V17JyOndPVttPNO5Yhk9dusns2MqThXmrXaO3pfkBPN3hILwts8RcepZdOP1LY4+4V6OF1L7f7rk2olWrsZ2JseFLPbZ6e2zxo+cZIoxzD4CmEBbJfKqrS07XM54Zie2na+7oE43HfsRypHrTnqXXLEzVlN1VIzM9m/JGxBt7VhKcg4G63' \
			b'uNUtbomA+yHUunuzdZdq3oDuYPnH8U8vFodHD7U+PmqradDOB9lEuhvkxZJ2HCGJXqZgQkaqMR4XHPuq4sfeG2FEFZPfO/V7I/6O7FLZ5HbZBJ4yMn2MYlHuh2ub1y22COnTxjgFBD9vPCaezsoJYn1OnRUAWWUzs4LZYOnLg7xXsGK4UDRWBRkVnXotWl4o' \
			b'yDoqqkvUM7OamgcHaMgN7cwV0fxtdAGag4/Ohu4X3UXcikxuZV+xcWo8oXZxfQx+JQU/kYLfR8EvcKCpcGsy/HAsfloUPz6JboSD7zjyjnkaUVugLvQWHNJoQWng3AZMbnCrSKwUOP8M54rhPgu4/h+n56OWUc0GbQnhWHOwgxw1jj6H8/ktmgHu42Id3H0G' \
			b'N57B/WVw4xncxRl3/QUDGLCAwR27cfNu3A4Pl/bhrkE41bvHhT4QjliBc75xKiu2IXFCJtZ6sIAJ6OMQhgOUUBbbgplbB06zczTqsusglzv8D4begYPvHJ63zW6E4BbvNztIZIdgsUMz7dA2O8j7Drxmh8iwQ4vsOhSC7OwQCHaIAruO0iEBCLIY0uMjezyz' \
			b'KGXpJqYDhdlhhd+hqXcW04FquxvpBP9jUvBgKOzOY2CLOYBA0OYOau+ux6w5+oPpYVGwsu4C5RIEAj0VYmAe8HEDBoCxdh5VAKKgMFTLDqNh9ih3jv5gtgEgdohw8gTKNQZRZi2dYYptKyUnMXDKHRYLHGo3UL5JGkID6RKCsWhY6AFLAXdRH2DPHdhzN6AQ' \
			b'2gHTomdAYMBf0kqLOSbrYHE7TBrugcPtDOkf/ljSOCZDZwazjVdYaMwGxcSIcHdEJUP4iJqHcHSQkcyGWoJAtByegyvvUB2oHDT+gEm3pGlKkh6HnoNFw+KA7IBycD6gBJoBNTJKTvHpHfkaPoncAIPxOYE8A4uN1uy/ROhDwKtwV+HuKLirWFex7vawziDW' \
			b'LWEct3eHBOyS9uNWyKM+46kLOcW+YRn+Sg3ZdRB0OQ5SY9weh4f6BnI0JoYZLtoEG4/BxP46cRF36cCdJSM+hgJGolf0K1g5oHWGFVTkfxk2UsCZ8FGSX0bJYQNOUhLnwcqpwFrOh2Dl8HC0zPFymBDzSKAcrh0qKdfjhJlDATVJHYeRs/mXf4X8PrxChh/h' \
			b'x4b/waVBCKcDASmj6AxCI35Sd8fUSxAhlPEzjrDN8JP6ELgDgV/+BUh9gqX0lp/2Sax2EHBPwFIfGffmHELaMXZ7TCPvA/XqTMjrBH2H2B3B6NvlCIyryamPI+nHwd6n2BMUCght8z4g6Z+JG6jKVPZpY/AgCM6jm+tIbhI07xnRA1o0zFB8juCjoDYiNlzj' \
			b'vvJ7yA1x0B1WEdwcgeJWkLw/gOb9hOi4nRcu+I/IPiToXkJ2CMMNBRDhcRt2QXkDPmFwq6BxFMQ3Ceqj8XuBL0V6DsNgwXkJoE5C/j/hvEhGjI/4PokyxNskXerj6wneYyClwiivUoL0BLroJfQriE8X+NVU/EXXjIko9FMSCvx4odiPnaOI/x2BD6aB2cwy' \
			b'WCKDNKfFY2IHLjd2j7Ju6aeXSyw068UvpdO2Up1mzNGJEhICSWO5KEC7jfTEKXxt+olc6OkD5yZhF0nG83MH9YMZqQihcNa8EgnTh2YkJxG17QqViNhGMqHCUTPFLZIKcwfzitYU5ZdEbcIuWnyuPWw4KacwTeq/LBFZx9hX1Aay3SuymA2vqH3jx1fUJHGv' \
			b'yIYBfnuCW77uKB52iA/AWwg4FgKo4kNE4/+Hdta9OHVtfA0YSm8C5yAqc2ayKhHVGkmlBFXJaTspHU1IqOg5IaFHcLgyks+OhI74ukBHIhjJaAoygZN2eZpKRiJ16LVjEovk41Py8YUXD5JO81HkHL9yEOcYfg3pJWBQDbJm5JKLx6xTTqltJYGUcXzONom0' \
			b'psdC9PaSsYxnkvE5yXBs+iAMkwwHlElGe3gyklFD5iQjNlsjGRbbSjJ+A8n4/ZeXREtKLlLsIKZRzxNiSXyRFfMUxNJXYqmk8kxIBZU5J5VBjsgpQ3YknMLXBU4RwcgpU1wTOGmXp6mcIlIHOSVGipwypJwylDhlYE6JUYucMqwcyXvMIHzCymOtaKGd/Pql' \
			b'VNpWEkj5ZMj5JJHW9Fhon08G5pO8S0xiUw1iPuGAMp9oN1jGJ1qenE/EXmt8wmJb+WTYwCdDgU8mLSmfSLGDmEbKpnyS+CEr5in4xG/lkyUmuWkaqRRy3xSCBexmFGL0UApRIRoNUfqQwH36yEZAbJIasgel6qZASoLZQ6UOsccUSdmDoih74EXKHugnOhIy' \
			b'RS2xR5qh4jEbIxGlsVrkMhsiWUikbSWxhDxoIH8ijyjdcb6IO6hkc+7Q4RTSx0Qe8iw/cmnjw4vkwbmZkYfmNicPNdcKeYjYRvKggq2QB+VlRh6JToU8tNiiNC2bkEfqhqyYSB5KGnOyIG5oE7bwGILwsc8SQ2WJyhL3yxJYuDlLGDkiS4hQzhIcuM4SU3zS' \
			b'GLOEScKVJUTqIEvESJEl0tFyvEhZggSZJNA9JGqRJczKMWcJVpqRUXT6zVminAg6oZmzhMlZYh7HssgySZicJDiaH7mwas8FkjAlktAH5yQh1lojCRbbShJmA0mYAklM6lGSkGIHsY2UTUki8UJWzFlJIlSSqCRxvySBD5mTRC9HJAkRykmCA9dJIqZGJMEj' \
			b'7THQTCPtKnWQJGKkSBLpyLrpCx1R8V0ixi2yRL9yzFmCtWZkNN30eyxRTgS9cD6UToCdsEQi7SRlFlrmiXz4XKL7kYurJl3gidLwuWZgxhNisDWeYLGtPLFh+Nwkw+eRJyY1KU9IsYNYR8qmPJE4IitmjSciPxRoYay0UGnhfmkBE53Tgpcj0oII5bTAgeu0' \
			b'EFMjWuAx7xhopjFvlTpIC1Es0kI65m1KY96RFmLcIi34lWNOC6w1I6Pdxu/RQjkR9ML5eLfJx7tTaScps9AyLeQD3hLdj1xcNekCLZQGvDV8RgtisDVaYLGttLBhwNsUBrwTNSktSLGDWEfdTmghcURWzCm00LXCC09ACqcvjXgEOjh6vcQSzN8SxB+zdmIF' \
			b'2jdDeg7nBQjHmyl8j3JE+BaBHL7HZrZQYhHAY3od+zIB+JiEK4CPK+iNdUuiTFOW0hGCZfBm1xH5In6PK8cMv/nBBxZQRAWVVlBk2eFZSTIUcACjx9mkJDIVz0rqZFqSpFjG6bGE01K2GU6LXc69kOIgRI8TMtPBKlFo5hzpQgr2pmQtRbacYsLdBG+7i7XD' \
			b'T1lEca1t8ltbOoGDQ+aZt9XRj+ddOBxmpy4cFcrAXgJXoX5KjXaQ4S6cGGinLhyVErTHc89BivkUuaUfrIsxAQV+m3bn2EPdOVPcEu6nuSseM9wXDVrpzrF73TkLibTtlF5CChKWUEMax8VThiEkB85AgR9s3rUjMf3IRVdTl7nBpl07uohHOSLmIeMINegK' \
			b'R2gBt7GE3dDFYwtdPInShDC0+EEUJmUUzkgdlRV0UlveVG55xtzyrDnFN3be/8Nhdur/UaGcUzhwnVNiasQp3P8TA+3U/6NSyimeOcUnnOKZUzxzSowSOSXtC7KH+oKmuEVO8SvHnFNYg1b6guxeX9BCIm07pZdyCoelnJLEcfHUWi6kFLzIKXm/kMT0Ixdd' \
			b'Tb3AKaV+ofjsnEvEkGtcIgXbyCUb+oVsoV8oUZZyiRQ7iKLUHYVLEgdlxZzEJZtXfdfxgjpecHt8MTR2vqiBw+y0qEGFcr7gwHW+iKkRX/B6hhhop/UMKnWox2mKFDkiXc9gS+sZIkfEuEWOGFaOOUew1qysZrB7nU4LiaAF5usZbL6eIZV2kjILLfZF2XxB' \
			b'g0T3IxdXTbrAC6UFDZqBGS+IwdZ4gcW28sKGBQ22sKAhUZPyghQ7iHWkbMoLiSOyYk7ihc1LqisvVF64PV4IDaF4xgtBjsgLIpTzAgeu80IUJV4IzAshCVdeEKmDvBAjRV4IKS+EQ7wQ4xZ5Ye2Y8wJrjfUilzkvlBNBC4Q5L4ScFxJpJymz0DIvhJwXOLof' \
			b'ubhq0gVeCCVekAzMeEEMtsYLLLaVF8IGXtCMp7wwqUl5QYqt7iZlU15IHJEVcxIvbF4R7Wv308W6n3AZpa308Wj0gb47X+jm9FD6UKG+lV9hEAnfZxCSUv6YkkP+cLzSzaWPEf5QKeEPPIdy04+wiGMiwR8zJgkol7h0TNt1B7hkilvikjR3xWPGJaJCJ8ve' \
			b'3N6yt4VE2nZKL6ETCUsYJY3j4qm1XEjVbh/vzNjF5SvhRMqPrICYdpFdXGklXMxBxi5qzhV20eJtYxe3YSWcK6yES1Qm7KLFDqIuKZuwS+qmrJg9dllYPn2QZeo66fr2ccf0YZq4H2qkDyNHpA8Ryt4+JHD17WNKjdjDMHuYJFzZQ6QOvX1MkSJjmJQxzCHG' \
			b'iHGLjGFWjjljsNaczINye0vgFhJBxpgvgXP5ErhU2knKLLT49kEaSfiBo/uRi6smXeAHU+IHycCMH8Rga/zAYlv5YcMUKcrLnB8mNSk/SLGDWEfKpvyQOCIr5qS3j7oyuvLCHfOCbQhUM16wckReEKGcFzhwnRdiasQLlnkhDVdeEKmDvBAjRV6wKS/YQ7wQ' \
			b'4xZ5wa4cc15grbFe5DLnhXIiyAt2zgv51NlU2knKfL3MCzbnBRb3IxdXTbrAC7bEC5KBGS+IwdZ4QYq0kRfsBl6wBV6Ycqm8IMUOYh0pm/JC4oismJN4oS6Grrxwx7xAn+Cb8cIgR+QFEcp5gQPXeSGmRrzAo9gx0E2j2Cp1kBdipMgL6Si2OzSKPcUt8sKw' \
			b'csx5gbXmZBTb7Y1iLyTStpJYygv5KHYq7SRlFlrmhXwUW6L7kYurJl3ghdIotmZgxgtisDVeYLGtvLBhFNsVRrETNSkvSLGDWEfKpryQOCIr5iReqKuhKy/cLy+gC7YzXuAwDNYtW9uRpTJiEJlVYpiSQ2KgZN0USEkwMajUIWKYIikxUBQlBrxYJIYpbokY' \
			b'0hwVjxkxiNpYJXKZEcNCIq0mlhADBiTEkEo7SZmFFomBNDIRg0T3bLdBbVomBs7OjBg0AzkxqMFWiEHENhIDFWyFGCgvM2JI1CTEoMUOYh0pmxBD6oismFOIwbSVGCox3C8xdE0/H5/u9VBiUKGcFzhwnRdiasQLPDzdp09RXhCpg7wQI0VeSIek+0ND0lPc' \
			b'Ii90K8ecF1hrvQxJ93tD0guJtK0klvJCPhidSjtJmYWWeSEfgJbofuTixvTKvFAagNYMzHhBDLbGCyy2lRc2DED3hQHoRE3KC1LsINaRsikvJI7IijmJFy63bLvyQuWFR+cF0/TzgWcO66eBZxXKeYED13lhim8Cp+qmwH4aeFapg7wQI0VeSAee+0MDz1Pc' \
			b'Ii+YlWPOC6y1Xgae+72B54VEkBfmA899PvCcSjtJmYWWeSEfeJbofuTiqkkXeKE08KwZmPGCGGyNF1hsKy9sGHjuCwPPiZqUF6TYQawjZVNeSByRFXMSL1xuyXXlhcoLj84LFp1vxgtWjsgLIpTzAgeu80JMjXiBB56zcOUFkTrICzFS5IV04Lk/NPA8xS3y' \
			b'gl055rzAWutl4LnfG3heSAR5YT7w3OcDz6m0k5T5epkX8oFnie5HLq6adIEXSgPPmoEZL4jB1nhBirSRFzYMPPeFgedETcoLUuwg1pGyKS8kjsiKOYkX6vLpygt3zAtD088HnjmsnwaeVSjnBQ5c54WYGvECDzzHwH4aeFapg7wQI0VeSAee+0MDz1PcIi8M' \
			b'K8ecF1hrvQw87+/Zt5AI8sJ84LnPB55TaScps9AyL+QDzxLdj1xcNekCL5QGnmORcl4Qg63xAott5YUNA899YeA5UZPyghQ7iHWkbMoLiSOyYk7ihbp8+hK8ULdjelp+wAWZ8wFoDvPTALQKZfwggav8MKWG/OB5/DkG+mn8WaUO8cMUSfnBp+PP/tD48xS3' \
			b'xA9pjorHjB9Ea17Gn/3e+PNCIq0mlvCDz8efU2kXTy3LBSlyiSV8PgotMf3IhVbDllnCl0ah47MzllCzrbCEiG1kCb9hFNoXRqETZQlLaLGDKErKJiyRuiMr5iSW2LyYurJEZYnbZQmDa/ZnLGHkiCwhQjlLcOA6S0zxTeBU3RTop1EHlTrIEjFSZIl01MEf' \
			b'GnWY4hZZwqwcc5ZgrXkZdfB7ow4LiSBLzEcdfD7qkEq7eGpZLkiRiyyRjz1ITD9yodWwCyxRGnuIz85ZQsy2xhIstpUlNow9+MLYQ6IsZQkpdhBFSdmUJRJ3ZMWcxBJ1MXRliWfAEhadbcYSVo7IEiKUswQHrrNETI1YgscgfBquLCFSB1kiRooskY5B+ENj' \
			b'EFPcIkvYlWPOEqw1L2MQfm8MYiERZIn5GMTsuxGptIunln+DFLnIEvlIhMT0IxdaDbvAEqWRiPjsnCXEbGssIQXbyBIbRiJ8YSQiUZayhBQ7iKKkbMoSiTuyYk5iiUdcGu3GShTXMxjh7owk4Br0YPDbyccNTvimn+8FzmH9tBe4CuWDE7qF9frwREyPhid4' \
			b'N3B0nXijn3YEV8lDtIHVWeSUN7rs9aI/tA84Ox7/L49T+JVjxh2dvGL0shd4v7cX+EIqOFAx3wgcXSr/6lCSW/7qkM5u8k23+GGJPt8EHCP1vAt4J+8YMdHyiMV8I3D6tTbmfTZqITZc4RAq3BEfIJqKeGDcYrYd+ORYXfqyITn0ZF6DGUSDM6H0yc7gqbOO' \
			b'7EhKKHsM0iFzBKzecCfgF+v8K/5K3cQol1tUPdvn78ZJZWmHv/oGcmVvID1uKTl7A+nliG8gIpS/gXDg+htITI3eQHp+A+mTcH0DESmhEmISDtp7D4lR43tIn76H9IfeQ2Lc4ntIv3LM30NYd6wduczfQ8qJ4HuIppe+ivT5q0gSwcVTy3JBSl18FenzVxFR' \
			b'48jlVgsvvIr0pVcRfXb+KiL2W3sVYbGtryL9hleRvvAqMilLX0Wk2EEUJWXTV5HEL1kxJ72KXG7VdSWOShwXII4BdyGeEccgRyQOEcqJgwPXiSOmRsTB06RioJ+mSamUEge/htDPnDhi1Egc6WQpf2iy1BS3SBzDyjEnDtadl8lSfm+y1EIiSByaXkoc+Xyp' \
			b'NIKLp5blgpS6SBz5rCmJ6Ucut1p4gThKs6bis3PiEPutEQeLbSWODbOmfGHWVKIsJQ4pdhBFSdmUOBK/ZMWcQhz2cquyK3FU4rgAcYSGPzGcEkeQIxKHCOXEwYHrxBFFiTgCE0dIwpU4REqJIzBxhAJxxKiROEJKHOEQccS4ReJYO+bEwbpj7chlThzlRJA4' \
			b'NL2UOEJOHEkEF08tywUpdZE4Qk4cHNOPXG618AJxhBJx6LNz4hD7rREHi20ljrCBODTjKXFMylLikGKr90nZlDgSv2TFnEQc9Wvb1/5Jikohj0Mh6GLzKbgcNkxTcFUooxAJXKWQKTWkkIGn4MbAYZqCq1JCIXgOxaYfoRCKzFJmTBJQIhnS6bjDoem4U9wS' \
			b'kaS5Kx4zIhENDjIdd9ibjruQSJuklxCJhCVcksZx8dRaLqQUvMQlQz4pV2IytCCXSECRS4bSpNz47IxL1JArXKIF28Ylw4ZJuUNhUm6iLOESLXYQRUnZhEtSB2XFnMQl9evalUueKZd06GIzLtEjcokI5VzCgetcElMjLuFto4b0KcolIqVc0jGXdAmX8BsJ' \
			b'/mCtjwlELkm3kBoObSE1xS1ySbdyzLmENTjIFlLD3hZSC4m07ZReyiUclnJJEsfFU2u5kKrdEpfk20lJTD9y0WOqZS4pbScVn51ziRhyjUukYBu5ZMN2UkNhO6lEWcolUuwgipKyKZckDsqKOYlLLrc8vHJJ5ZKLcolDz5pxiZMjcokIZVzCfrJlVGRKj9jE' \
			b'MZskh7IJJkdiQiddz3zCv0IodGHZt5BSJBLGi1O1unSIhK6W52pJMUiqSCyucMhDY4bz2Vodj5Twb68BGbukj53/J5LB4nHSCcuQxGzDwllMNwkh2XDhRWtlunH5PC4pkh9FJd2UeplyXIlyxN4zyhFrr1BOfN5G0uEyrrGOK7BOtOVEO5xFH9SKUkDhnVzZ' \
			b'huRPo57LrUCv1FOp56LU0zfDfB4Xhw3TPC4Vyl9jOHCdeGJqRDw8jysGDtM8LpXS1xiexzUk87gocks/WOtjAvE1Jp3NNRyazTXFLbJNv3LMX2NYg4PM5hr2ZnMtJNK2U3rpawyHpa8xSRwXT63lQkrBi7yST+iSmH7koqupFzilNKErPjvnFDHk2muMFGzj' \
			b'a8yGCV1DYUJXoizlEyl2EEVJ2fQ1JnFQVsxJXHK5deqVSyqXXJRLfDPMF5lw2DAtMlGhnEs4cJ1LYmrEJbzEJAYO0/ISlVIu8cwlPuESz1zimUtilMglPuWSQwtNprhFLvErx5xLWIODLDIZ9haZLCTStlN6KZdwWMolSRwXT63lQkrBi1ySrzWRmH7koqup' \
			b'F7hkvs5kZ+307JxLxJBrXCIF28glfgOXzFaYEJdMylIukWIHUZS6o3BJ4qCsmJO45DZXs18BbaxN6LIzalijBKUDf+UUcFH4H9AfZvA/yBHhX4Ry+OfAdfiPqRH888zeGDhMM3tV6tDqwimSQj6D5gT6h3qsylg/rBwzrJcHGlGJiORoX04G0X4+l3fI5/IS' \
			b'vDOwD7Lf4RzQ80m7A8/Y3S2Pa5Qm6mqOZiAu5lgDcRbbCuLSw7SE34U5uvqAFMA5yAdxJCmXAnjiYiM/cQHABa8Jpy/3qe3a5q9t/ouC/oiuNAP9UY4I+iKUgz4HroN+TI1Af2TQH5NwBX2R0jb/yG3+MWnzj9zmH5kAYgKxzT+m8D8eavPHuEUeGFeOeZuf' \
			b'Ncg6ksucBcqJtO2UXkoEHJa2+ZM4Lp5ay4WUghfb/GNOERzTS9HV1At0MZboQp+d04UYco0upGAb6WLc0OYfC5wxKUspQ4odRFFSNqWMxEH596Q2/21+nvsKaKO2+Z8e/kFZYT6jlsPCNKNWhTL4l8BV+J9SQ/gPPKM2BoZpRq1KHWrzT5EW2vzh0DzaItan' \
			b'WSkeS23+IBNow94E2oVkWk0ugfrQLrT5Q1tu84d8jmxoV9r8oTQvVnOUg7iaYwXERWwjiIf2YJs/FKbE6gOSNr8E+SCOJOUSAE9dbOQnbmjz3+bnsitOP0+chppk5jht5Ig4LUI5TnPgOk5P8U3gVN0USEkITovUQZyOkZZw2hyN02blWMRpIzht9nC6nAzi' \
			b'tJnjtFnCabOA0ybHabOG06aE05KjGU6LOdZwmsW24rQ5jNOmgNPygBSnOcgHcSQpl+J04mIjP3Edp139evVz2Ojvufa/oKPMx1w5LExjriqUAzsHrgN7TI2AncdcY2CYxlxV6iCwRzEF9pCOs4ZD46xT3CK++5Vjhu+itSDjrGFvnHUhEUT3+SBryEdYU2kn' \
			b'KbPQ4leHQj62KtH9yMVVky5Af2lsVTMwg34x2Br0s9hW6N8wthoKY6uJmhT+pdhBrKNuJ/CfOCIr5pR+Fle/Xl154Y55YUBHmfHCIEfkBRHKeYED13khpka8wIOxMTBMg7EqdZAXYqTIC+nqgXBoKHaKW+SFYeWY8wJrLciIbNgbkV1IBHlhPiIb8hHZVNpJ' \
			b'yiy0zAv5EK1E9yMXV026wAul4VrNwIwXxGBrvMBiW3lhw4KAUBizTdSkvCDFDmIdKZvyQuKIrJiTeKF+vbrywh3zQkAvmfFCkCPyggjlvMCB67wQRYkXeBelGBimXZRU6iAvxEiRF9L9k8Kh/ZOmuEVeWDvmvMBaC7J/UtjbP2khEeSF+eZJId88KZV2kjIL' \
			b'LfNCvm2SRPcjF1dNusALpW2TNAMzXhCDrfECi23lhQ3bJoXCtkmJmpQXpNjqblI25YXEEVkxJ/FC/Xp15YX75QV0iPkSZA4bpyXIKpTxggSu8sKUGvLCyAuQx+RQXlCpQ7wwRVJeoCjKC3ixyAtT3BIvjG7lmPGCaI31IpcZLywkAhbgxBJewICEF1Jp+bUs' \
			b'tMgLpJGJFyS6H7m4atIyL3B2ZrygGch5QQ22wgsitpEXqGArvEB5mfFCoibhBS12EOtI2YQXUkdkxZzEC7R2GEC7AQhu4InEEJ2ShNvjiTahCpewRZsQhss5o92jDX81XxsK2/nDb+QQkAGdXDeXwH1QRgfa6EAdHeijG+cD0F2BZ8DcbRC+aW/8I0XtmbjH' \
			b'ISLhKlSo1zjUS18bAgiQiUXc4hNO2qELYSWgQ4lph84mQcxOIWEoCm210z4SlfVLZGWYsShfnv+jR+7QTR0T1w5dK+bDTeyluVj7sJHILYxvu0MENj2zRGByi/KJpRyzbE5x58Pdba+ZMKLHgX8zNkOnAQF03FKaYFs3ZzWXs1oqLb+WhRZZzeWsJtH9yDro' \
			b'YpFx0gHmE6dgUvcRDcHsvQfRrhbMeU45jyiP9+ughcCGGRBBZGdtzHFOg2r5FRqk7G+ft+o28KAr8KDkhsfTk9XPqi6pCFpqYcPEHIYVOn0I6RVcAiXifUt/Hf4F7sPp0XQ+evpLksiS6B6WZA2JEUP2UMUP8GOkxYQQ19mQSZAZkFlvie9mTLc6J4pIbZG5' \
			b'iLUSxkI2ypioNJWpNI0pZRqdvnQsq6wxypxJ1hhkK3scms40Z4w5UwRmB2EGZoP4FuKPYIEM/Auw/yDMn4A+orwi+zqmL6H5kVOVFLcPQjTh8wycCX9z8C3POipOOUohdppsdDymbgLUOZSugugxCHpoJtIebO4D5k434Y4gSdiowIiQ5g9DWv/4qLbfhF8F' \
			b'Nm2w8/5UR+DbXmtbMS48b5yLGFdqEdukVQwyoAvCPtCHwW8IAiSkOGhAH/i5QgO6MCN+unAQbOzS1jL8B2Z+fVxzmRqw1weWzp8NMJPGLjrRA4HTzef1KHiig1QAFQA1tDWqYCdmdA8/SUJenPhtcBBMxcohTp8D7PRyiDmgJ+mGPLuOdqse4nRPvIDGwr+g' \
			b'Cr5CBVIbczgMyP76mpkTGmN/SX9lLc7hxL6MSyByeGCr8y7Q9PxIigXtxitvhiIPH0BSd/1oak9riYbDwDdcM/D5KwO9G2p+VqA7H9AZhqvrBblbbSqeBGzjxl7D7gqB7Sn6D+ejVXcEbg/uPzwS4DJwo6bCvQKceXKAc/6ZgBx65YOBDt9ih1eQX3yJhQxs' \
			b'gzxzMuQdmB7wYNSj7B7TqzicoUlnbxz52ss07S6BfO5i6Lcy2r2Ifoa6n87RxHP3hICGSnK+ph4U6REGiM1jNvVcinsbMc/4877GhvFGMe/SeHcurMvmBV2ypefzfrtjsc6Qms79Oou2vX2sOyvOmctOhGlPadyd+jo71L66mwO4KxzePedrLBq19tWdA9js' \
			b'ZYHtlLkwJwPbM54DU4HtWoHNV2A7C7C55nWdtrwKZbcCY8MjTVtOoIxA6FaQ7P6mK98kcuH80cebrtz8C9cq8gBDf69whh/ZxcmfkK3nCW1LLTT49Q9vqd1oC+3CuEarODHrHeeugtyh4VNW1Gmz4CA/9wpsIIdf14bMXT/AlRYvPwXIwTV45bFgly+zyJdX' \
			b'VOB7GPBBaoFWrO/QC28KAP3lMHCH5cSs9MdDoaVHxcUS6RIJBMbhMYGxfRxsPLRxxB4+DleAjfaBDUBTG4HHYiEa74KA6B+CioZgJlwNJmJHx8Mbhh0C2NOt1n0IJu41D8NjomB34RZiin7dFbcOK/rdOvod3b+XgR5a+1Yag/cAeuNjgp65ItAzFfQq6F0t' \
			b'6PUV9J4O9EBvjwh69opAz1bQq6B3taB3u4O7twh63b2OftwMwl3vZLurQrUbArTHRC9DervhQdsTJqNA3cNdm2jvbMjVnQIX5DQO3V4tiC3tN/2UQ7YV1J5yeBZnXuMI7a00zq5iWPaUlpm9GoA7aoP/R2ilDQc23r/l1tqhDfTX5hR7AbrhnsGOxzsV6+gq' \
			b'xTsKELjjzzSI0LHQx895UHOOo1orucOMl7ahv6PJeIf2lt8w5djgFBP6loY7hIDNv/QLKsG+ImKLX1IBYHiFNEPNwOtZZVFRsqLkhVCyz1Cyn6Nkn6BkH/8/ACX7h6NkryjZV5TchJJeULI/B0r2zevp44OMi/q1wcVPDfb0ecGzvgkXvwn4qB13pe/2zb/Z' \
			b'd4ld6krAteX9latZRKYIStln9WYwtPRVPUYfrMZP/ho6R5cn3iwzw44MN9Lv113u5XEBHza/Ovpa3e+juu+yj2pecXVHU9TqfoHq3vwrQAug74nmh1rva71/qnpPC0eeiOV5kUqt9Umt1/Z+2swPtf7X+v909d8/Yf33tf6v1//xaer/MT2d58OCY/s3L40J' \
			b'x/ZbprhwsL/ySrCBp+xN3Y5+3u04wQMbUMI2QAUn/cCeRkEKztBRPY1XAxkP6TyccEO0d2KfITy2NiZqY+JowCCp2mV4W60Jj4jQdlTvu1rva70/WO+p+taxgrTiUxNI/t9Sxe9xRi1O7wvYFEDnxpYAOjj8UqciPKviQcWDw3jQVzyY40Ef/98ZHtiH4sHZ' \
			b'J9ZfHyRccI3PKiw4mnqHE0ueGCK6u5liwNHOBBOU2GO/M9BDtkAFC86gwmA2UKeHQQPqzytEUPDPV7wprX8F0ENo4Spa3CRaPDFC+LtBCH9OhPBPgRB+K0L4IxsTh3DhgTMSH2eF3nVBwxUsGL4eeCCPutx6uat+2SDdXMei3hNnLA5Hz1h85DW714MIV7SN' \
			b'wKVRgUfyrmUp7bVCA2vpyhb9n4oPm2Y2Pu2y/uuBiCvbbeQpYaKjDXKvftn99WIFqa+7P8A4NBXycluBVMy4CGZQfbzF7TquFTcuv77ysXCjMIXyajYSuszeZ9e6LvxpkIQq61Ut9z4zpDz9dmaU2Wtfv/1I+BKyWZXXt1dZhZingxiu4dpgubptJW4eZ25j' \
			b'o4jHApquAk0FGgUaU4GmAs0jAY1pXpMve/I7dF0/0A3bvB5wSRhuWwIPhf8U7NJgXMzVUXDfvDYDAhN+RdHgqHGAG3D+YgdQ1qI0yu3gcQAjJAQVmZLcWQxDIMG631DtbMC04FHgT+AB8HR4EngmbnTVIh4iYAAQBPz8Wk9fUZ4eDvfBBWjHI6gTaNuOkBS7' \
			b'ywBYcFAS1yj1+B/TGBvcRmuQWJASWML0mCLkZcAqO1Iu3Vlz6ZrN/+jpPT592Pp88DYqUbshJz3uZdYv/uvAk3m3MTe/RxnzhzMGqsaPBXb03Rh7KJ8d5xU/ATjPr+5XS58TIA+dlQFobO8fzeegDyZM//dkIA8+u4OxcH9aDKNPCgxyhwo7XLywUK9G/PIj' \
			b'FDo05/vHX0Nli4bTCzmOx5ez7w+UFVofm//hvnhL93B/ueSayjsWywswCfi7WGqPBceGE5UdG07DtIh2URVG1DHIpy4H6tvEbnwc9kNo7mg+VU/TdXhFQs+qo3WYuGAYl24a2SwziEoNqbUDFO4gBx02LEoqBi6hho2bqZsaJqpyS2o3UAYzomOoCRBE9w9s' \
			b'8+H/4s023ptENEL6f0PMUrSFpFZutQefXbyV534uRU4EoddXa6iRfqmD1dKVKxfmvMG2N9UyaNtB6/S4uuYeUN3crMrZE6qdf8qqZ5rCkb6CSaDhl66i+NKBb1qbpfE9K7k4KiqO5ByVs5WDHcxU9N7kQrZ5Zge7h71GWHbN5Q5WiztbrbFPXHHsJSpPaM5z' \
			b'YM/WudJ6kqTZW8ovnxVj526C7x7P6mD3OEMXQNEHTsVZ7Os904F9z8dHY/WUOw1q7ZnVHkrgWR3sHuXuFjDV6RVoOEclcs3+gUM+xRtbDxy6OS4OK2uhrya+SK6+RbYNOLfvG/+EtStMNax3hVrWS03DTnZ8IbNPWeuGZv/AN2U5k2mXV344dMczp8rDFeVu' \
			b'nQreczfC4cxndbB7LHRvXQt44wyByx+sqhM6aq4dtJ+qliHDPejgKRjT/wcntP6Y+Vl2ffZns2uVO3mOA+lhuwsdA8rhcO1dcod1VzBN8cAJOEv3RAJKfljiXMfGJ7ENz9cjdddEi1O9ntfB7rHYBXU2ou1OJlvXPNKBM9uOicAqK3fL1Bo1r1Fj88wOdo/F' \
			b'bqmz1ih0gZNqFc5kfbQDp4seE4E1t9hjUytWWrFw9vHzOtg9FucTnb1imf7UyuWbRz1wGvYxEXg6aO1z2Va/QvPMDnaPh/e5nPCShxZfe5lbfImLFhubhx24RGK7NC56wB/nFu57X7zB6q0TajbVPlxP87wOdo/FvpbHrH2ZF5yjJuJSqCc50oVHx0dnld9w' \
			b'18gleklxjdt1H7hyjH768ybM7nJ8V4k/fyVNHOPBlXXRwGNz1IELuI6Ns3/oMsHjIo0d/iTL++CSzXRC9wyPh1xgJOQq6jeuXn3QQUUBRT44gcMHrh19pKT3Dnah47twbqym4xLlmzzYPid0FNUhT/EA35xyUEHgoScms3rgWvHHfoaX7pHj+5cet9ZvHec8' \
			b'vvaPzQUP9NmH3EsOXjd8QndWRQH2BNyeoh54sEstdoFVl9rsUrapBx3sUufo9ruxOTS4y809HGzAZzgJCjcouoeDDXjD3XxP2fGOKw5PO3ARofzo/61x1oX2Uz3z49hZ6pK8bc7immd2sHvUuV/b3KNvntnB7lGXJG5zj7F5Zge7R53gtsk9cEPM53Wwe9QN' \
			b's7a5R9c8s4N3KqzT97a5h2me2cHucULf5bNyD9s8s4PdA/ejHWjDKmYbMIQGCL44DEBtUyCu/pcb8E6cOg3YnCTAQg4H/8FqaIlWHuTL0mDf/D9LD3vSaGeKgV6U/zdengENqSHZqI48cO5V5E2JJ3nKB05bSfe+xrkke/tPz/aclp5AEH29vzkTPxu9GnQX' \
			b'SKGUk8B7b6e5wHD0T9TWyC+UEDRt++sppxyO+5T35Ou0hQfkxsu+sCbfERjyHBgBIBNwx1OopO7wHMttRondTyH+y5dfvvz/ZGC1Dg=='

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
	_LTRD     = fr'[a-zA-Z0-9]'
	_LTRU     = fr'(?:[a-zA-Z_]|\\_)'

	_VARTEX   = '(?:' + '|'.join (sorted ((x.replace ('\\', '\\\\').replace ('+', '\\+').replace ('*', '\\*').replace ('^', '\\^') for x in AST.Var.TEX2PY), reverse = True)) + ')'
	_VARTEX1  = fr'(?:(\d)|({_LTR})|(\\partial|\\infty))'
	_VARPY    = fr'(?:{_LTR}(?:\w|\\_)*(?<!_))'
	_VARUNI   = fr'(?:{"|".join (AST.Var.UNI2PY)})'
	_VAR      = fr'(?:{_VARTEX}(?!{_LTR})|{_VARPY}|{_VARUNI})'

	_STRS     = r"'(?:\\.|[^'])*'"
	_STRD     = r'"(?:\\.|[^"])*"'

	_FUNCPY   = f"(?:{'|'.join (sorted (AST.Func.PY, reverse = True))})"
	_FUNCTEX  = f"(?:{'|'.join (sorted (AST.Func.TEX, reverse = True))})"

	TOKENS    = OrderedDict ([ # order matters due to Python regex non-greedy or operator '|'
		('UFUNC',        fr'\?'),
		('UFUNCPY',       r'Function(?!\w|\\_)'),
		('SYM',          fr'\$|\\\$'),
		('SYMPY',         r'Symbol(?!\w|\\_)'),
		('FUNC',         fr'(@|\%|\\\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LTRU})|\\operatorname\s*{{\s*({_LTR}(?:(?:\w|\\_)*{_LTRD})?)(?:_{{(\d+)}})?\s*}}'), # AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

		('LIM',          fr'(?:\\lim)_'),
		('SUM',          fr'(?:\\sum(?:\s*\\limits)?|{_USUM})_'),
		('INTG',         fr'\\int(?:\s*\\limits)?(?!{_LTR})|{_UINTG}'),
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
	_VARPY_QUICK   = fr'(?:{_PYGREEK_QUICK}\d*|None|True|False|nan|{_LTR}\d*)'
	_VAR_QUICK     = fr'(?:{_VARTEX}|{_PYMULTI_QUICK}\d*|{_VARPY_QUICK}|{_VARUNI})'

	_FUNCPY_QUICK  = _FUNCPY.replace (r'|del|', r'|del(?!ta)|').replace (r'|det|', r'|det(?!a)|').replace (r'|Integer|', r'|Integer(?!s)|').replace (r'|Si|', r'|Si(?!gma)|')

	_IN_QUICK      = r"in(?!teger_|tegrate|teractive_traversal|terpolate|tersecti|tervals|v_quick|verse_|vert)"

	TOKENS_QUICK   = OrderedDict ([ # quick input mode different tokens (differences from normal)
		('FUNC',         fr'(@|\%|{_FUNCPY_QUICK})|\\({_FUNCTEX})|\\operatorname\s*{{\s*({_LTR}(?:(?:\w|\\_)*{_LTRD})?)(?:_{{(\d+)}})?\s*}}'), # AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

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

		('CMP',          fr'==|!=|<=|<|>=|>|{_IN_QUICK}|not\s+{_IN_QUICK}|(?:\\ne(?!g)q?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)|{"|".join (AST.Cmp.UNI2PY)}'),
		('OR',           fr'\\vee|{_UOR}|or(?!dered)'),
		('AND',          fr'\\wedge|{_UAND}|and'),
		('NOT',          fr'\\neg|{_UNOT}|not(?!_empty_in)'),
		('SQRT',          r'\\sqrt|sqrt(?!_mod|_mod_iter|denest)'),
		('LOG',           r'\\log|log(?!combine|gamma)'),
		('LN',            r'\\ln|ln'),

		('VAR',          fr"(?:(?:(\\partial\s?|partial|{_UPARTIAL})|(d(?!elta)))(partial|{_VAR_QUICK})|({_VAR_QUICK}))(?:(?<!\d)_{{(\d+)}})?"),
	])

	TOKENS_LONG    = OrderedDict () # initialized in __init__()

	_PARSER_TOP             = 'expr_scolon'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	# grammar definition and implementation

	def expr_scolon_1      (self, expr_scolon, SCOLON, expr_ass_lvals):                return expr_scolon if expr_ass_lvals == AST.CommaEmpty else AST.flatcat (';', expr_scolon, expr_ass_lvals)
	def expr_scolon_2      (self, expr_ass_lvals):                                     return AST ('(', expr_ass_lvals.curly) if expr_ass_lvals.is_curly and expr_ass_lvals.curly.ass_valid else expr_ass_lvals

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

	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                       return _expr_add (self, expr_add, expr_mul_exp)
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                      return _expr_add (self, expr_add, AST ('-', expr_mul_exp))
	def expr_add_3         (self, expr_add, SETMINUS, expr_mul_exp):                   return _expr_add (self, expr_add, AST ('-', expr_mul_exp))
	def expr_add_4         (self, expr_mul_exp):                                       return expr_mul_exp

	def expr_mul_exp_1     (self, expr_mul_exp, CDOT, expr_neg):                       return _expr_mul_exp (self, expr_mul_exp, expr_neg) # AST.flatcat ('*exp', expr_mul_exp, expr_neg)
	def expr_mul_exp_2     (self, expr_mul_exp, STAR, expr_neg):                       return _expr_mul_exp (self, expr_mul_exp, expr_neg) # AST.flatcat ('*exp', expr_mul_exp, expr_neg)
	def expr_mul_exp_3     (self, expr_neg):                                           return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                    return _expr_neg (expr_neg)
	def expr_neg_2         (self, expr_div):                                           return expr_div

	def expr_div_1         (self, expr_div, DIVIDE, expr_divm):                        return PopConfs (_expr_diff (_expr_div (expr_div, expr_divm))) # d / dx *imp* y
	def expr_div_2         (self, expr_mul_imp):                                       return PopConfs (_expr_diff (expr_mul_imp)) # \frac{d}{dx} *imp* y
	def expr_divm_1        (self, MINUS, expr_divm):                                   return PopConfs (_expr_neg (expr_divm))
	def expr_divm_2        (self, expr_mul_imp):                                       return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                            return _expr_mul_imp (self, expr_mul_imp, expr_intg) # PopConfs (AST.flatcat ('*', expr_mul_imp, expr_intg))
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

	# def expr_func_12       (self, SQRT, EQ, expr_mapsto):                              return AST ('=', ('@', 'sqrt'), expr_mapsto) # allow usage of function names in keyword arguments, dunno about this
	# def expr_func_13       (self, LN, EQ, expr_mapsto):                                return AST ('=', ('@', 'ln'), expr_mapsto)
	# def expr_func_14       (self, LOG, EQ, expr_mapsto):                               return AST ('=', ('@', 'log'), expr_mapsto)
	# def expr_func_15       (self, FUNC, EQ, expr_mapsto):                              return AST ('=', ('@', _FUNC_name (FUNC)), expr_mapsto)

	def expr_pow_1         (self, expr_diffp_ics, expr_super):                         return AST ('^', expr_diffp_ics, expr_super, is_pypow = expr_super.is_dblstar)
	def expr_pow_2         (self, expr_fact):                                          return expr_fact

	def expr_fact_1        (self, expr_diffp_ics, EXCL):                               return AST ('!', expr_diffp_ics)
	def expr_fact_2        (self, expr_attr):                                          return expr_attr

	def expr_attr_1        (self, expr_diffp_ics, ATTR, expr_pcommas):                 return PopConfs (AST ('.', expr_diffp_ics, (ATTR.grp [0] or ATTR.grp [1]).replace ('\\', ''), expr_pcommas.comma if expr_pcommas.is_comma else (expr_pcommas,)))
	def expr_attr_2        (self, expr_diffp_ics, ATTR):                               return PopConfs (AST ('.', expr_diffp_ics, (ATTR.grp [0] or ATTR.grp [1]).replace ('\\', '')))
	def expr_attr_3        (self, expr_idx):                                           return expr_idx

	def expr_idx_1         (self, expr_diffp_ics, expr_bcommas):                       return PopConfs (AST ('-idx', expr_diffp_ics, expr_bcommas.comma if expr_bcommas.is_comma else (expr_bcommas,)))
	def expr_idx_2         (self, expr_abs):                                           return expr_abs

	def expr_abs_1         (self, L_BAR, expr_commas, R_BAR):                          return AST ('|', expr_commas) if not expr_commas.is_comma else _raise (SyntaxError ('absolute value does not take a comma expression'))
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                            return AST ('|', expr_commas) if not expr_commas.is_comma else _raise (SyntaxError ('absolute value does not take a comma expression'))
	def expr_abs_3         (self, expr_paren):                                         return expr_paren

	def expr_paren_1       (self, expr_pcommas):                                       return AST ('(', expr_pcommas, is_paren_tex = expr_pcommas.is_commas_tex) if not expr_pcommas.is_lamb_mapsto else expr_pcommas.setkw (is_lamb_mapsto = False)
	def expr_paren_2       (self, expr_bracket):                                       return expr_bracket
	def expr_pcommas_1     (self, CURLYL, L_PARENL, expr_commas, R_PARENR, CURLYR):    return expr_commas.setkw (is_commas_tex = True)
	def expr_pcommas_2     (self, L_PARENL, expr_commas, R_PARENR):                    return expr_commas
	def expr_pcommas_3     (self, PARENL, expr_commas, PARENR):                        return expr_commas

	def expr_bracket_1     (self, expr_bcommas):                                       return AST ('[', expr_bcommas.comma if expr_bcommas.is_comma else (expr_bcommas,))
	def expr_bracket_2     (self, expr_ufunc_ics):                                     return expr_ufunc_ics
	def expr_bcommas_1     (self, L_BRACKL, expr_commas, R_BRACKR):                    return expr_commas
	def expr_bcommas_2     (self, BRACKL, expr_commas, BRACKR):                        return expr_commas

	def expr_ufunc_ics_1   (self, expr_ufunc, expr_pcommas):                           return _expr_ufunc_ics (self, expr_ufunc, expr_pcommas)
	def expr_ufunc_ics_2   (self, expr_ufunc):                                         return expr_ufunc

	def expr_ufunc_1       (self, UFUNCPY, expr_pcommas):                              return _expr_ufunc (self, expr_pcommas, py = True)
	def expr_ufunc_2       (self, UFUNC, expr_var, expr_pcommas):                      return _expr_ufunc (self, expr_pcommas, name = expr_var.var)
	def expr_ufunc_3       (self, UFUNC, expr_pcommas):                                return _expr_ufunc (self, expr_pcommas)
	def expr_ufunc_4       (self, expr_varfunc):                                       return expr_varfunc

	def expr_varfunc_2     (self, expr_var_or_sub, expr_intg):                         return _expr_varfunc (self, expr_var_or_sub, expr_intg)
	def expr_varfunc_3     (self, expr_sym):                                           return expr_sym

	def expr_sym_1         (self, SYMPY, expr_pcommas):                                return _expr_sym (self, expr_pcommas, py = True)
	def expr_sym_2         (self, SYM, expr_var, expr_pcommas):                        return _expr_sym (self, expr_pcommas, name = expr_var.var)
	def expr_sym_3         (self, SYM, expr_pcommas):                                  return _expr_sym (self, expr_pcommas)
	def expr_sym_4         (self, SYM, expr_var):                                      return _expr_sym (self, AST.CommaEmpty, name = expr_var.var)
	def expr_sym_5         (self, SYM):                                                return _expr_sym (self, AST.CommaEmpty, name = '')
	def expr_sym_6         (self, expr_subs):                                          return expr_subs

	def expr_subs_1        (self, L_DOT, expr_commas, R_BAR, SUB, CURLYL, subsvars, CURLYR):  return _expr_subs (expr_commas, subsvars)
	def expr_subs_2        (self, SLASHDOT, expr_commas, BAR, SUB, CURLYL, subsvars, CURLYR): return _expr_subs (expr_commas, subsvars)
	def expr_subs_3        (self, expr_cases):                                         return expr_cases
	def subsvars_1         (self, SUBSTACK, CURLYL, subsvarss, CURLYR):                return subsvarss
	def subsvars_2         (self, expr_commas):                                        return expr_commas
	def subsvarss_1        (self, subsvarsv, DBLSLASH):                                return subsvarsv
	def subsvarss_2        (self, subsvarsv):                                          return subsvarsv
	def subsvarsv_1        (self, subsvarsv, DBLSLASH, expr_ass):                      return subsvarsv + (expr_ass,) if expr_ass.is_ass else _raise (SyntaxError ('expecting assignment'))
	def subsvarsv_2        (self, expr_ass):                                           return (expr_ass,) if expr_ass.is_ass else _raise (SyntaxError ('expecting assignment'))

	def expr_cases_1       (self, BEG_CASES, casess, END_CASES):                       return AST ('-piece', casess) # AST ('{', ('-piece', casess))
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

	def expr_vec_1         (self, SLASHBRACKL, expr_commas, BRACKR):                   return _expr_vec (self, expr_commas)
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

	def expr_term_1        (self, expr_var_or_sub):                                    return expr_var_or_sub
	def expr_term_2        (self, expr_num):                                           return expr_num
	def expr_term_3        (self, FUNC):                                               return AST ('@', _FUNC_name (FUNC))
	def expr_term_4        (self, STR):                                                return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1].replace ('\\}', '}')))
	def expr_term_5        (self, EMPTYSET):                                           return AST.SetEmpty

	def expr_var_or_sub_1  (self, expr_var):                                           return expr_var
	def expr_var_or_sub_2  (self, SUB):                                                return AST ('@', '_') # special cased for last expression variable
	def expr_var_or_sub_3  (self, SLASHSUB):                                           return AST ('@', '_') # special cased for last expression variable

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

	def mark_incomplete (self, ast):
		self.incomplete = self.pos

		return ast # convenienve

	def stack_has_sym (self, sym):
		return any (st.sym == sym for st in self.stack)

	def in_intg (self):
		for st in reversed (self.stack):
			if st.sym == 'INTG':
				return True

			if st.sym in {'LIM', 'SUM', 'L_DOT', 'L_PARENL', 'L_BRACKL', 'L_BAR', 'L_SLASHCURLYL', 'TO', 'UNION', 'SDIFF', 'XSECT', 'BEG_MAT',
					'BEG_BMAT', 'BEG_VMAT', 'BEG_PMAT', 'BEG_CASES', 'SLASHDOT', 'SCOLON', 'SLASHCURLYL', 'SLASHBRACKL', 'CURLYL', 'PARENL', 'BRACKL'}:
				break

		return False

	#...............................................................................................

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
		'COMMA'        : ',',
		'PARENL'       : '(',
		'PARENR'       : ')',
		'CURLYR'       : '}',
		'BRACKR'       : ']',
		'BAR'          : '|',
		'SLASHCURLYR'  : '\\}',
		'L_PARENL'     : '\\left(',
		'L_BAR'        : '\\left|',
		'R_PARENR'     : ' \\right)',
		'R_CURLYR'     : ' \\right}',
		'R_BRACKR'     : ' \\right]',
		'R_BAR'        : ' \\right|',
		'R_SLASHCURLYR': ' \\right\\}',
	}

	_AUTOCOMPLETE_COMMA_CLOSE = {
		'CURLYL'       : 'CURLYR',
		'PARENL'       : 'PARENR',
		'BRACKL'       : 'BRACKR',
		'SLASHCURLYL'  : 'CURLYR',
		'SLASHBRACKL'  : 'BRACKR',
		'L_PARENL'     : 'R_PARENR',
		'L_BRACKL'     : 'R_BRACKR',
		'L_SLASHCURLYL': 'R_SLASHCURLYR',
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
		s               = self.stack [-1]
		self.stack [-1] = State (s.idx, s.sym, s.pos, AST ('*', (s.red, AST.VarNull)))

		if self.autocompleting:
			vars = set (filter (lambda a: not (a.is_differential or a.is_part_any or a.var == '_'), s.red.free_vars))
		else:
			vars = set ()

		if len (vars) == 1:
			self.autocomplete.append (f' d{vars.pop ().var}')
		else:
			self._mark_error ()

		return True

	def parse_getextrastate (self):
		return (self.autocomplete [:], self.autocompleting, self.erridx, self.has_error, self.incomplete)

	def parse_setextrastate (self, state):
		self.autocomplete, self.autocompleting, self.erridx, self.has_error, self.incomplete = state

	def parse_result (self, red, erridx, autocomplete, rederr = None):
		res             = (red is None, not rederr, -erridx if erridx is not None else float ('-inf'), len (autocomplete), self.parse_idx, (red, erridx, autocomplete, rederr))
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

		if self.tok != '$end':
			return self.parse_result (None, self.pos, [], self.rederr)

		irule, pos = self.strules [self.stidx] [0]
		rule       = self.rules [irule]

		if pos == 1:
			# if rule == ('expr_func', ('FUNC', 'expr_neg_arg')): # autocomplete parentheses for function name
			# 	return self._insert_symbol (('PARENL', 'PARENR'))

			if rule == ('expr_paren', ('PARENL', 'expr_commas', 'PARENR')) and stack [-2].sym == 'expr_mul_imp' and \
					(stack [-2].red.is_attr or (stack [-2].red.is_var and stack [-2].red.var in _SP_USER_FUNCS)):
				return self._insert_symbol ('PARENR')

		if pos and rule [1] [pos - 1] == 'expr_commas' and rule [0] not in {'expr_sum', 'expr_abs', 'expr_func', 'expr_subs', 'subsvars'}: # {'expr_abs', 'expr_ufunc', 'varass'}:
			return self._parse_autocomplete_expr_commas (rule, pos)

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_sub' and stack [-1 - len (rule [1])].sym == 'INTG':
				return self._insert_symbol ('CARET1')

			if rule [0] == 'expr_intg':
				return self._parse_autocomplete_expr_intg ()

		if pos >= len (rule [1]) or (pos == 2 and rule [0] == 'expr_func'):
			return self.parse_result (None, self.pos, [], self.rederr) if self.rederr else False

		return self._insert_symbol (rule [1] [pos])

	def parse_success (self, red):
		if self.incomplete is not None:
			erridx, rederr = self.incomplete, 'incomplete'
		else:
			erridx, rederr = self.erridx, None

		self.parse_result (red, erridx, self.autocomplete, rederr)

		return True # continue parsing if conflict branches remain to find best resolution

	def parse (self, text):
		def postprocess (res):
			return (_ast_mulexps_to_muls (res [0].no_curlys).flat.setkw (pre_parse_postprocess = res [0]),) + res [1:] if isinstance (res [0], AST) else res

		if not text.strip:
			return (AST.VarNull, 0, [])

		self.parse_idx      = 0
		self.parse_best     = None # (sort keys ..., (reduction, erridx, autocomplete, rederr))
		self.autocomplete   = []
		self.autocompleting = True
		self.erridx         = None
		self.has_error      = False
		self.incomplete     = None # None or index of start of incomplete

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
	RESERVED_WORDS    = RESERVED_WORDS
	set_sp_user_funcs = set_sp_user_funcs
	set_sp_user_vars  = set_sp_user_vars
	Parser            = Parser

# AUTO_REMOVE_IN_SINGLE_SCRIPT_BLOCK_START
if __name__ == '__main__': # DEBUG!
	p = Parser ()

	# p.set_quick (True)

	set_sp_user_funcs ({'N', 'O', 'S', 'beta', 'gamma', 'Gamma', 'Lambda', 'zeta'})
	# _SP_USER_FUNCS.update ({'f'})
	# set_sp_user_vars ({'f': AST ('-lamb', ('^', ('@', 'x'), ('#', '2')), ('x',))})
	# set_sp_user_vars ({'f': AST ('-lamb', ('@', 't'), ('t',))})


	# a = p.parse (r"""Limit({|xyzd|}, x, 'str' or 2 or partialx)[\int_{1e-100 || partial}^{partialx or dy} \{} dx, oo zoo**b * 1e+100 <= 1. * {-1} = \{}, \sqrt[-1]{0.1**{partial or None}}] ^^ sqrt(partialx)[oo zoo] + \sqrt[-1.0]{1e+100!} if \[d^6 / dx**1 dz**2 dz**3 (oo zoo 'str') + d^4 / dz**1 dy**3 (\[-1.0]), \int \['str' 'str' dy] dx] else {|(\lim_{x \to 'str'} zoo {|partial|}d**6/dy**2 dy**3 dy**1 partial)[(True, zoo, True)**{oo zoo None}]|} if \[[[partial[1.] {0: partialx, partialx: dx, 'str': b} {-{1.0 * 0.1}} if (False:dx, 1e+100 * 1e+100 b) else {|True**partialx|}, \[0] \[partialy] / Limit(\{}, x, 2) not in a ^^ zoo ^^ 1e-100]], [[Sum({} / {}, (x, lambda x: False ^^ partialx ^^ 0.1, Sum(dx, (x, b, 'str'))[-{1 'str' False}, partialx && 'str' && a, oo:dy])), ln(x) \sqrt['str' / 0]{d**3}/dx**3 Truelambda x, y, z:a if a else b if partialy]], [[lambda: {1e-100, oo zoo, 1e-100} / \[b || 0.1 || None, \{}, \[[dy, c]]], {}]]] else lambda x:ln({}) if {\int_b^p artial * 1e+100 dx or \['str'] or 2 if partialx else 1e+100} else [] if {|{dz,} / [partial]|} and B/a * sePolynomialError(True * {-1}, d^4 / dy**2 dz**2 (partialx), 1e-100 && 1.) Sum(\[1, 1e+100], (x, {'str', 1.}, \sqrt[1]{partial})) and {d^5 / dz**2 dy**1 dx**2 (oo zoo && xyzd), {dz 'str' * 1. && lambda x, y, (z:zoo && lambda x), (y:0)}} else {}""")
	# a = p.parse (r"""\begin{cases} \sum_{x = \lim_{x \to \left[ \right]} \left(\sqrt[1{e}{+100}]{False} + 1{e}{+100} + \infty \widetilde\infty \right)}^{\left\{\neg\ \partial x\left[1., \emptyset, \text{'str'} \right] \vee \lambda{:} \partial \vee 0.1 \vee dz \vee \frac{\left(d^2 \right)}{dx^1 dz^1} - \frac{1}{\sqrt[\infty]{\partial}} \right\}} \left(\frac{\frac{x}{y}\ zd}{dz\ c\ dz \cdot 1{e}{+100}}, -\left(\partial x + dz + 1.0 \right), {-2}{:}{-{1 \cdot 2 \cdot 1.0}}{:}\left\{\partial x, 1.0 \right\} \right) & \text{for}\: \left(\lim_{x \to -1.0} 0^o o \wedge \log_\partial\left(ypartialx \right) a! \wedge \sqrt[xyzd]{\infty}\ \widetilde\infty \cap \frac{\partial^3}{\partial x^1\partial z^2}\left(0.1 \right) \cap \frac{\partial^9}{\partial z^3\partial y^3\partial x^3}\left(a \right) \right) + \left(\lim_{x \to \begin{bmatrix} b & True & \text{'str'} \\ dx & 1.0 & 0.1 \end{bmatrix}} -1 \ne dx, \begin{cases} \infty \widetilde\infty \wedge \partial x \wedge None & \text{for}\: dz! \\ \lambda & \text{otherwise} \end{cases}{:}\partial y, \left\{\left\{dy{:} \partial y \right\}, \left(False{:}\partial x{:}\emptyset \right), \lim_{x \to \partial} \partial x \right\} \right) + \frac{\begin{bmatrix} \infty \end{bmatrix}}{\begin{bmatrix} \emptyset \\ \partial y \end{bmatrix}} \le \ln\left(\left\{None, \infty \widetilde\infty, dy \right\} \right) \\ \left(\operatorname{GeometryError}\left( \right) \wedge \ln\left(x \right) - 1.00 \right) \left\{dx{:} 0.1 \right\} \left\{1.0{:} \partial x \right\} \sum_{x = 1{e}{-100}}^p artial\ True \cdot \left\{\text{'str'}{:} \begin{bmatrix} xyzd \\ dy \end{bmatrix} \right\} \vee \left(\left\{\emptyset \right\} \cup \frac{True}{\partial y} \cup \left|\partial x \right| \right) \cap \left(\begin{bmatrix} True \\ \text{'str'} \end{bmatrix} \cup \widetilde\infty \cdot 1.\ True \cup -\partial x \right) \cap \operatorname{Sum}\left(\left(\left( \right) \mapsto 1{e}{+100} \right), \left(x, \infty \widetilde\infty\left[1{e}{-100} \right], c \vee \partial x \vee None \right) \right) \vee \left(\cot^{-1}\left(\emptyset \right), \int dx \ dx \right)! & \text{for}\: \left[\left|\left(-1 \right) \right|, \frac{\partial^4}{\partial x^2\partial z^2}\left(\log_{\emptyset}\left(-1.0 \right) \right) \right]\left[loglambda\ x, y, z{:}\begin{cases} \infty \widetilde\infty & \text{for}\: 1{e}{-100} \\ dy & \text{for}\: dy \end{cases}, \operatorname{Sum}\left(False, \left(x, False, 0 \right) \right) \cap \sqrt[False]{2} \cap \frac{1}{dx\ a!}, \gcd\left(\left(dy \vee \partial x \right)^{1.0^{\partial x}}, \operatorname{Sum}\left(b{:}None, \left(x, -1 + 1.0 + \text{'str'}, xyzd! \right) \right), \left|-1 \right| + 1.0 \cdot 1.0 \right) \right] \\ \left|\begin{cases} \left(dx\left[\partial, \emptyset \right] \wedge \left(False \vee \partial x \right) \right) \left(\neg\ -1^{dy} \right) \frac{d^2}{dx^2}\left(dx \right) & \text{for}\: 1{e}{+100} \\ dy & \text{for}\: 1{e}{-100} \end{cases} \right| & \text{otherwise} \end{cases}""")
	# a = p.parse (r"""Eq(Union(dy2 - 2.0651337529406422e-09*notinxyzd, Union(Complement(diff(z20notin)*diff(s)*partialxb, diff(diff(diff(-1.0)))), Complement(diff(diff(diff(-1.0))), diff(z20notin)*diff(s)*partialxb))), Or(Union(Complement(Union(Complement(Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))), partial.chCa.dcGNDli().XG()), Complement(partial.chCa.dcGNDli().XG(), Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))))), diff(diff(dx))**1*e - 100), Complement(diff(diff(dx))**1*e - 100, Union(Complement(Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))), partial.chCa.dcGNDli().XG()), Complement(partial.chCa.dcGNDli().XG(), Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))))))), 0.1 - bcorx0orc)); slice(None); abs(Matrix([Integers])); Matrix([[[Eq(c, 2)]], [[{Lambda: oo}]], [[lambdax, slice(y, 2)]]])""")
	# a = p.parse (r"""Union(Complement(Union(Complement(Matrix([Le(Union(Complement(Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)), a), Complement(a, Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)))), ('s', 1.0, dx))])**(a[0.1, a])**partial**3 / (partialz**3*1e-100), diff(diff(FiniteSet(2, partialy)))), Complement(diff(diff(FiniteSet(2, partialy))), Matrix([Le(Union(Complement(Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)), a), Complement(a, Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)))), ('s', 1.0, dx))])**(a[0.1, a])**partial**3 / (partialz**3*1e-100))), -xyzd*FiniteSet()), Complement(-xyzd*FiniteSet(), Union(Complement(Matrix([Le(Union(Complement(Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)), a), Complement(a, Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)))), ('s', 1.0, dx))])**(a[0.1, a])**partial**3 / (partialz**3*1e-100), diff(diff(FiniteSet(2, partialy)))), Complement(diff(diff(FiniteSet(2, partialy))), Matrix([Le(Union(Complement(Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)), a), Complement(a, Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)))), ('s', 1.0, dx))])**(a[0.1, a])**partial**3 / (partialz**3*1e-100)))))""")
	# a = p.parse (r"""Union(Complement(Union(Complement(((FiniteSet(diff(partialx), -tau57, [[-28832738.092809968, 1., 's']]), Sum(xanddz*Matrix([-1, False]), (x, xyzdin1e + 100*notin*diff(partialyin)*diff(s), partial)))), (FiniteSet(-13.574245287492392, partialx, dx)**d**5 / (dy**3*dz**2*Noneord**1)) / (dz**1*partialx**{}*orz20)), Complement((FiniteSet(-13.574245287492392, partialx, dx)**d**5 / (dy**3*dz**2*Noneord**1)) / (dz**1*partialx**{}*orz20), ((FiniteSet(diff(partialx), -tau57, [[-28832738.092809968, 1., 's']]), Sum(xanddz*Matrix([-1, False]), (x, xyzdin1e + 100*notin*diff(partialyin)*diff(s), partial)))))), 0.006826903881753888), Complement(0.006826903881753888, Union(Complement(((FiniteSet(diff(partialx), -tau57, [[-28832738.092809968, 1., 's']]), Sum(xanddz*Matrix([-1, False]), (x, xyzdin1e + 100*notin*diff(partialyin)*diff(s), partial)))), (FiniteSet(-13.574245287492392, partialx, dx)**d**5 / (dy**3*dz**2*Noneord**1)) / (dz**1*partialx**{}*orz20)), Complement((FiniteSet(-13.574245287492392, partialx, dx)**d**5 / (dy**3*dz**2*Noneord**1)) / (dz**1*partialx**{}*orz20), ((FiniteSet(diff(partialx), -tau57, [[-28832738.092809968, 1., 's']]), Sum(xanddz*Matrix([-1, False]), (x, xyzdin1e + 100*notin*diff(partialyin)*diff(s), partial)))))))); Derivative(dy, y); Function('u', commutative = True, real = True); psi, y1""")
	# a = p.parse (r"""Union(Complement(Union(Complement(Union(Complement(Union(Complement(1.0, Gamma), Complement(Gamma, 1.0)), 1e+100), Complement(1e+100, Union(Complement(1.0, Gamma), Complement(Gamma, 1.0))))**Union(Phi, partial), Or(1e+100, -6.70911653218863e+19, False)**(1 / Derivative(-1.0, z))), Complement(Or(1e+100, -6.70911653218863e+19, False)**(1 / Derivative(-1.0, z)), Union(Complement(Union(Complement(1.0, Gamma), Complement(Gamma, 1.0)), 1e+100), Complement(1e+100, Union(Complement(1.0, Gamma), Complement(Gamma, 1.0))))**Union(Phi, partial))), abs((-1.0) / partialx)), Complement(abs((-1.0) / partialx), Union(Complement(Union(Complement(Union(Complement(1.0, Gamma), Complement(Gamma, 1.0)), 1e+100), Complement(1e+100, Union(Complement(1.0, Gamma), Complement(Gamma, 1.0))))**Union(Phi, partial), Or(1e+100, -6.70911653218863e+19, False)**(1 / Derivative(-1.0, z))), Complement(Or(1e+100, -6.70911653218863e+19, False)**(1 / Derivative(-1.0, z)), Union(Complement(Union(Complement(1.0, Gamma), Complement(Gamma, 1.0)), 1e+100), Complement(1e+100, Union(Complement(1.0, Gamma), Complement(Gamma, 1.0))))**Union(Phi, partial)))))*Matrix([[FiniteSet(diff(0)), Subs(abs(True), sqrt(b), deg((x0, -0.1)))]])*And(Matrix([[And(w1, partial), Union(Complement(Union(Complement(c, partial), Complement(partial, c)), xi), Complement(xi, Union(Complement(c, partial), Complement(partial, c)))), And(oo not in b, b in Reals)]]), is_deficient((a, b))**[partial])""")

	# for v, k in sorted (((v, k) for k, v in p.reds.items ()), reverse = True):
	# 	print (f'{v} - {k}')
	# print (f'total: {sum (p.reds.values ())}')

	a = p.parse (r"\[[1],[2,3]]")
	print (a)

