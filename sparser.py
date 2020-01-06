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
			return self.mark_incomplete (AST ('-mat', tuple (c.brack for c in e [:-1]) + (e [-1].brack + (AST.VarNull,) * (e [0].brack.len - e [-1].brack.len),)))

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

	def mark_incomplete (self, ast):
		self.incomplete = True

		return ast # convenienve

	_PARSER_TABLES = \
			b'eJztnXuv4zaS6L/MBaYbsAFLpEjp/Nd5zG6wncfmMbuDRhB0kp5FcPNCOsmdxWK/+60XqaJFSZat00e2iSMfSxTFVxXrJ1JF+dmrv3zx/qcvP/3kL7u//J83P38PX+Hw/a8+f/n3l7Dz8pvPXnz+4Se4G3defvPe5y/e/zfcjTtf/fWrT97/7O9hD74/+fRL' \
			b'+P/FV+/h/5cvvvhX2f37xxQNvuH/3158Tgl+wJExGu++9+G/fPP+iy8+/EL2P34RQt/rd//W737Gu5RCLNRfYUe+Kvmu4fvjjz75itL96JNPPw7fVdipqUCUUGyFo6MvsdAffvzZl3//4kPM9aNPvvwXrPFXmNrLjz6metP/f/8cz7/EJn35KcaRxoEmpJrz' \
			b'//c//fjjF6HVMeBzbvXPQ6tzGNXr89DqEvaCv/sSfp6Ul0r67/Dvxcefwf8P3ntJ5zD0kw+kVXHvvX73b/2utOqHL7/4EIvy+Ucf4/eH//k+NsOLL6kdMMkvuRpQ1C/DN7bnBx/97aMP8Ir3Rb4c77OX1PzQdkES//nFh+9ThA8++utfUYc++YjVkAr94pMP' \
			b'sJHxxKd4/ccvPvviy0+liEFJKOA/WMfwq2Llgyzf/zfYffvHt2//fP3b2z/V/lvY/+71b29+/+aX3775/tsf3/7++jd1Gnbf/PNXOPPDnz+F/Z/f/Nc3r3/7r3D49o9f3/zWH3wLuz+9/v2b7375UfZ+++X/9Xuc39s3b99+F/d+jXshmdffxt0fvv9nDP39' \
			b'95jRP15/93vY/5Uy4OA/fv6uL/M//vFrcvDND9+97UsaK/TjD33d+tDf3/wW93/648dvfvgpJvbdH7/9+N+qacLutz/8/Itupliq315/p5OCnXD455t45vX338dIr2Pl/vn2TV9TaqVYA6yTavh44o+ff/jl53jiv2OJfvj591gkEC5KnOXFaff1g5O6If98' \
			b'HZv9519iWf7QUV7//H0Srlv62+9++emn1/Hwl5jYt9As//dNL8Y03q8/vPnuTTwAFf25b51f3/7+S8w6qk2syS8/9vWnRJODt+rKb3788/WPfYvylV/vXj3bO7NzzfMd7zjcaWr8Z3aNey6HcER7FqPtmma3l1MhgI9MuA4usCEIdynW3lNItXtmIRSiVc9j' \
			b'gMUAa0PAvsMdU/E/DwHGPNdBtR8E+VoH4S7sVY7/eYhftc8lCHdhz8On3UEd9nzG4w58Y0L4bTv8Z3cOYlRc2D4oHO6bA6UKLeGoEt3zcOyplgcuEhSkbiGAPn1Qpw/NQXYwDBOBklQ27pGUIJFnFSQCUmm5TJQsXVlX/M9DCjXLBI5wF5uVhICyfK4Ow74K' \
			b'r/lrT7pg6WObcNriDhZSwrnou72VQD6GMpIMdk3dB1DruP64pgjmKKCPsbdUKdvwP8dJYVEsF83KYZANlM1y4Tz/c5CI45MGhUFa5aCRUH3khKvCCduKbLlIFkvAeggZ1aihKBgpHgY1+rB2soNheDlI14B0Hcs/HDaDINGSJNgOD48utNXgMBOjadOgenCY' \
			b'XrS3XpWs7xlSiKOA6jigVgFQIxZJZcMx9GxSSVAT03DhMHsjahyCh0H94d6SdkJOz0CicFx1uxZrtcPSG9HR4Vk0bmBG5iOBZqSR9pZsAeoGxDuEfgBlr7i3HrDjVyjaZtf40P8xOAbGkPrAIW0fUnFIf1VdU4gIBUL2hupsDP9zXSxeCPIHHYS7uNfxP2i2' \
			b'58/7XdxruAeES7CFSe4OC92rHh5ST4mHIFCyRi3HCxYVGqMm0YJKsPZXhv95yLTiPlIZ2qV2xC4rO1S3qkL7wBDwwQRgoATF44aOJduD5IFKvsN+nAkPIRBABfSildLgcAwdneLQByKymUGzSTrn+Z+Ha2q+BpukJsMAGvysxQYXFW93LbVPDZ2hcsy4HRQb' \
			b'org6VItOeuZd7iTYcyoZ6n4r+tlwOzjpHaKcJsgDAp+5JgqKDl1frG7nSLxgw56RFKQ74aGl9AdBxzHCIdMIjSHbO7RMdR32bCV7DF/cYX2BRmxjqnjUJdmGkHi0rxmqjRyGM2jsuSoN//MQUrN61LyL0bqdsLKmsvMeqxzusGAPEkG6B3bNmikGlqE2mt01' \
			b'tSVG6vifN71RYnOF7ez5n7o98kLRxvE/ujPi4sou7jXh5HM5hKNwgnselKhtSFNs0BQX7lIc3YM14XK8WZH7uSacwFsvCYE9uOt7dYBWAGlCm4EBsgR40C4wd6BUaBVB8bodyA86dIfGDVqng11sRVTaBj4QXmMyqOFgAEFMFRgCwL7BWPgBawrpwzm4V6ng' \
			b'ThCjtKBC+EERwdXYPw6wDz20cviBy6GieA1Ehg5VgfZWUJwKylNBgSooUQXlrKCgFXSLChqpghpWYCgryLzC3DFP6KVgC4HHlcNPs+vMrrO7DnbcrvO7DtPcYW0gAYgP7VmB/e8gmwMkdajghmOHt8RwQwAxDhDx0CAe4HYLZA7Zocg82asWrD4inGoD6Rww' \
			b'YewscCE0awVxwEy0dgdCbLGtql0LQWAuul2H5Yb4UFKoDqIAKIp34tBp8QYGzD2Yd0/3t6B2YIdA5z3d0YKB88SkirQaLjqgGYQD2AfxthWCDZsWylXjzT7sgh6Q6EENnqH8MQBl+BxOY5nh0HIotjLGwpbGs6AXGIzCeE70x7Ov8EaBjintojs3qjvPOlaC' \
			b'iqWN0iPpd5WoFOsKShkPKyvfjVwm15HY6VuukwsxhmM9IvUqJuk+1Arl7ovA70vgpYffkcBxIohuG+pAAsOW34vhl3uQzhStuB+tALG7Iu97kjdJAvt9Qx1dCe5rmtBm48B3f8lJDJWbx4ZuHqnN08sbLxFkIEOCfR7lG+QqMhMZBeloWSgZhHbntg6Nqxvz' \
			b'3Tek6gPHen+k78eaLhp+mm6nOs26nNFh0VutrFpJj9XzSC1BFfl2gEcEpgkDASdDBB6NlgZftcGfkYXA5nXSV4yTvhMmBZpWAsKQz2Q7pYz7KxvEJSM6mjbIddIwj0B9kMaALuToQk6HAoW7ggLfHBaB343Ai7zvSN7Pqjjqq+UOzdkwbUw0wId+ULBds3NF' \
			b'7rcjd2NF7E5QL/ccMiscbvU6Oq4g2wryrTy2DN7mQNM4bClfdOJmdAKk3RRp35G0XZH2HUnbF2nfi7SfdWG2jmcOOpkIwPryDM6BuV4m0N7JBJqry5jqjnofVpD7m0zgsfyXKI4WCybbuK/JgZCTM+skF4YABx4CNC487+Pn/eekydODr9CR/twkapnUDE8M' \
			b'DnWZZH4Eo2SLU8cd2SSQN98DNGX+/o7E/qwJj3xklsfKoyTu/a/QNx6PW572aXn8j8YbrTA+8EPBoFtpeQL7ZLb6WStCq+R2omUytvwUsO3EsfMgE3nhIZ6RubyaAPpMHtrKUS2CpyS1pKmN0GA0fLk8CmTfgPR5YSM5OS6f42I5Lpbn8eYBzh1QNdokl6IC' \
			b'C3Ht2Hx7FqJvS+Ou2LieraTnruG5a/huqo2DkSxtvbSt2ax4NivtoSjyeqDwAgox7uw/8qwWuNdhuFfuAO/nDvAVrSWqn5dVZPckc0six/VhdVnxdcNyxvt1XvBX5Hy7csYFnLUs7YPvItBrFygtyiw99pYFXHFfpeW02GeLaG9ItHRbJYIoC1g2PirmhevU' \
			b'F8tC5nvqqfiigiB2/m7lNoqOS8/des/FhcckMEgeBVicke+o89Zis5taOm94chk6saUbrONlpgeOfQh3X7KCjhSp9PEN9nEsGAu0oUmrIpwtCceE3makQ9kq0+tsECF32iK6TYhOTKGpxICKjBx3syKbp5ONMSwLfkwnD0TZi6MV50d+gBfctSl+EdM7Hzja' \
			b'0u5P0u5NafcnMEudDePjg7wAqpIlwW1880cnIU5eDCFOXx2/lLzjm/bOy7iNb9GL8N5JpzkcSmu/u3e08BN2TKyWJR715WsyXpWXa97XLIe8QgmX9JAaNWRAoZWxkUvffRxLWROezlucJFPKB56VsgI6not6RrNPX7NbfZ24VVNgGXg9uejbRgbF2bddVLxs' \
			b'7dwsshpThfVspA2pr2sR39J7HH4V2roC4rem07KKmpdV1LysgqaMHedr4hEtqKh5QQV1fjmszXBmrJVJF36DaqH6nVCdZ7KfyaML5+QWUR47lv5//ioY7pvlzbT31J1e4Vqy4vd4E5Ik61eM4IUTPb604cVt2F6wOBZXYxLS/aEg/dL1gG2x7bdg23ERLfeJ' \
			b'uvSJS/uEKU14aROWpTI3YlbkoaRvSp+4dPLzUPrETfSJSly74JzhZb74hRMgz+k3jfELxGzC7/oZWYhknof1K0b/vhPK3URHeXacD8dGHOflAvwCZTDilW2ei9cAO+xKhjTfVWZn7kUZbceCNw1rifxMCXv0muRnRIxErWrROHnZPHkrGvFWZJWTiE6SyD2w' \
			b'QT86zpm6A00SldfU35JyoSMkTaGXNZS3JdZK2NEdv5jYjoQ3uXBkjwkea7V4qpEDOrZjWQ50UxrjihG4KZGiz6hhn1HDPqPSw430cCP+dfgtX43cY/IPoBU3qUcdLjbB2NblBcyPsLaV9d3KF6t9c2D9bgmPxVXsSWdLpkYeVXAENMGhTJw8WpZnyyPmtqMx' \
			b'N/kPGX6+ZPhNqSRmx7Fo1dzX9MpUtn2y9PXADkmeTaHnyJ6T8JygZ73xbEpbMZqHfuhvy4TP9aOSJ1VsnJL5mmdf7HO5A/5618/hoH7LQNrSoJjsShhNy0ROv3yDr2pkmWdr5OKseyRU3bJuW9ZtW+7HbkrJDIm/zNzdi8Ad92SejCuPVi5YDgTq38hbKvAb' \
			b'sgmHNvxscoOvLkGtt6WH3U0PwxYqgr9DwUOuDd8rNXyvhFqwq2UsgGGOT1XyQnRsVkfHcvMFTexkROHKss53NehrSQjQio7uj9kdMCzgMSQJvaqLxOZ5CpqddvDF9vgedvz9C/yZhtKjb6JHU3/0qBqev1r+6kT6UAxfeuk7utvyJjz2aeRFBU6+vYxr+QdS' \
			b'qD+3RSzvynh2pbHf3eudDDY29QUb+kItfQA5VLhzG9yBHDsGTSfS5fm/w+7VAe8odyB/8nqBwuEIImo8N1S4A+HUuSnQ14ZEzo3NwtMDERmjcBNxBelRGxRUWteFauoKUu2galABaTpqKlZCFKWWI5YSy5h0yo51U5qGZRG0LuhOJ9oB8cPbP+mNoHUcZVXY' \
			b'vLh4A3/WDn8lDfsA5F/hC0TxN+7xl8/x97ChHDW+NQUUp8YV/aADNb7YAyfgD3gOmg597fDdafjSZ3wvEXq3oZ8ctmmNgoNwbFycxMfmRVUDXavx9Wv46jU0Mbh6GB8U4EMCXEWCb9XDF+rhy/QsCgbyxFcJ4Lst8R0CoJM1Lh5tsDfCORBAjW+GaHAFCsaB' \
			b'a3H1Mbrco7s9dn1Qrxq7Pq6nwDcNoFsevo4Hn6tCfQzUxVQH0Jw9iBYaYV9BR99DDfbQynsoxd7i/mG37yD4gOdhFz5oPfYopj3KZm/wQ8FwCUplDzq2x66/R8uwR7Owx560xy61R+uwh3rv0TDsUXp7NAV7tAV7NAR7tAT7ipKE9tsbvBJ6777D+HjKYUwQ' \
			b'0R5DHSUMO9C+e2jnPWZM+WI1sOfusevuW9wBue07LA4minlhcT2eAYntsWTQJ/agrtgmeywzSGZvsIwNlZGKjAkcOm4QNHh7tG17NGp7tG57tDNcYyxpjedAmfYtlsdgs4CK7PE6zBTUct9gaTAMSwJ6tgcd3oMs9x4TwiJhC9GlcKLDfEggWAAqUoWnqNlh' \
			b'h8RI1YbIhhoUk6FaUDhej81msB3xg6exgeEbFQG0ZA9asu/wigNm5LBw8EHJoMRQLtiomAM2R0sZUP0gBlUPznos1YHqhEcQD3RxD/q599jsWEe4pKUWg3TgXGuk6FhPtAL7DuWCFTPUzlD0FlPFord4Qfc1GkE0fcXwFcO33PAVq1es3pVavRqt3pi14/th' \
			b'r8yeuqc81fjRnHQ/Ra2toB83hMMb3VlzeHRLT/fuZoFlbBdYxyq1kDhTMLCSS6yjvw4Lie+jw5eKRUtpM9YS4uEbaiatpkcp+Rn76OkvsZIUsJallPTH7aU/xWJSGhdbTR9r24VKLrOafpHd9Inl9BnbudBk+qszmlQNLIJYT5+xnySJaRu6+x/3gLj3Dwj8' \
			b'Dr5M+7+4bup8w0pTJXp+IWNh/aSRTWcieB5BbK5TZpcmCfTkxqK5Bp5UGJuCG7PLicuhzJCQf0CnTPVwWi2ZZQpmG3+DFl+uJrMm9AzF6hkXP5xjCjNQZN5lVilMx8nMz2km/+iJDP6wc0QAxIN2YRRAPJzpwZ9XRyzgD6vjTM/aeMCfoUFdGmAC0kCNmsWF' \
			b'HUHGQbBRX4iOqscHTk2i433EiJlHCb5HDd+eRkhpFFage0A7GbDKjJhWYQatDE4TNjOkQWWjLYGNhJLVbWUms1bUoauxazej2OkvSsjT5xfhQ5kLfyq1BRaF+IFHhAbXyLdwiQ5w/hO/8RWBMZUhoDA0MIqhd6AlLsQqKnNj0pLkuJVEMF1yrGoZYCYNqIDG' \
			b'lZJGNCGGPYylhNOvmFDT866SigfsUc0krJJWoH1NQsqnZSEqFA7zYy6GJtC64m2s+DJYcuHnaRl1JGFm0Is5ckq8I3ZS49DYqL2YodwBGKOhswacqibURJUwXFHVhdoF4TNddd8wXNxAWmZsbR7oFtBUD6QCpn2guzvXPeD9WAunoZ8xiZEVD3SnVOHpmu6L' \
			b'H/CeAowNHLv/pZ9K2D6qTxkhudwgaT0w1yvD+RjMx1AOQC4wflQYL4LwYgA7BrCbAzBqm6N4CYFdCEUtk72IXyf4deP4lUtS+PaJRvg6BV8dI8BX4k8OBvt4Gdi6zICQopo0wyxjdQTTJceqcCj4gxfOumPMOsGsE8w6oWw+rYOVGEJYp+jqZFzJVT6iqmOo' \
			b'uhSqg+QFqlLnSjeAjTVdCNUT5+2i7FOoirxnocrxjqHqVoSq2w3GpqrpEphymBNxmiBeAanScxbhY4O0KSB91yPcAtE7gKhniM7Nl6Ii0ZYyNIaiksleZKgXhvpxhsolKUP7RCND1QRqPE1lFoZK/GmGxqsyDM1NqlJUk2aYZaiOYLrkWFUmjlP9MT+98NML' \
			b'P73wM5/OwUoM4adX/PSKn/6Yn575mc7PDpMXfkp9teipJ3MtF/LzxCncKPeUnyLrWX5yvGN++hX56TP87Jsu4SeHORGnCeIVfiodZxE+Nj/dhQ/jRsl5M9gsyCzIPAWZ5IuBDTSDzLglyJSg4XPGWh410vfpDxr7XCItKUuhZVIOoWWIP0nL/qohLTFU0xJ1' \
			b'NzyBTDLM0TJtmS45VpXJP6LkcksjJQ8qR5JBDa96WOJ+gCXVQmDJ6WUeZtapH8hR+lRx18XqJnW3sZLLYMnlnYdlFHsCyyDqOVhKvCNYUpusBEtW6BSWSjIalhKGM7cVw5K/GZZaxVmER7AMkAxwRBqiI7vQsT080G1Nhoq+ULFQsVBxDSrWTMV6joq1bCkV' \
			b'OShDxVqoWC+jYsylp2KtqFirGIGKEn+aivGqDBXrlIoUq5EhpC5Sloq6RKZLjlVlRqgovjtc34SK+WRQw2tFxVpRsVZUrMeoWKdUHGbhQhUIin3VbazjQijWJ0IxSD2Fokh6Fooc7xiK9YpQrDNQ7AWTQFFaspUaBfkKFJWGswRXg2JboFigWKC4BhTZR6ie' \
			b'8xHCRqEthSIHZaAozkH1uHNQFooxlx6KyjOoVluEosSfhmK8KgPFJjOxGseKOscsFXUE0yXHqjYjVBTvn7oZUDGfzMHyd6Bio6jYKCo2Y1RM3X2G6fPMaqivFru3sZYLuXiiu08UfMpFEfYsFzneMRdXdPeplbtP5GLfdAkXOQy5KC4+tXLx0UrOMpzmovAw' \
			b'g8GuYLBgsGBwDQyyp04956mDDUJbikEOymBQnHTqcSedLAZjLj0GlY9OrWMEDEr8aQzGeBkM5nx0IgZ1jlkM6gimS45VbUYwKN45tRtgMJ8Mqrjyz6mVf06t/HPqY/+ciMHUQWeYvmBQ6qvF7m2s5UIMnuigEwWfYlCEPYtBjneMwRUddOqMg45qugSDHIYY' \
			b'FAedWjnoaCVnGZ6LweqwLQ5euLDv8Qi4ZN3fPVNtbO3gCjRbQrEBwQbU6pha3Ry1OtlSanFQhlrd7rwlhX0+Pbc6xa1OxQjc6uaghX1frlmyzpA1sf/ksaVLZLrkWFVm4WJEuia/GpG8Xo4XY0QsdUd+L62UINahd32hU+z70vaHNu4upVN3Ip2CeFM6iUjn' \
			b'6DS+mnENMHU9j2KrHQGJyxmWNHJN1KpGDDiCUKCOok21LdqssaRx4yOwW1/IiI+MbRmZZUdmhicozdwEJfYh2hLGSdCQcUYmKM2yCco+l0g4oyYojdoC4UL8ADk84KgRdYZph19oHGIKQ96ZqcnKJPcc7pIIpkuOVc3yuDMyWWkGk5UjyRxs3BUYymFAouEp' \
			b'SyNgjA2bQaNJJy6HeTEXQ921OvhYjIVMNOMTl2ENb8LGWP6EjUEZ5tgY2ialo1lxAtNkJjBVE2pQShj+tIVMYBo1gak7geEinjtyu/QFLIWlhaVldnOWoTy7aeZmN7Hj0JYylIMyDJXZTbNsdrPPpWeomt00OkZgqMSPDHXMUKcY6pihjhkar8kwdGqmM8k9' \
			b'y1AdwXTJsarZCENlptMMZjpHkkGRym5gKB9GhvJ8J8WI9R5haDrrOcxLGCp11+rgYzGWMvTEWc9Y7pSdogSz7JQ2OWLnirOeJjPrqZouYSeHITtl1tOoWU+t/IaLeC47L3jHTnn6V57+FT72fPTMRz/HRy9bykcOyvDRCx/9Mj7GXHo+esVHr2IEPkr8yYnU' \
			b'/qoME6emUpMcs0zUEUyXHKvajDDRCxP9gIn5ZFCMXgHRKxr6fp6V08tx0KccHKQvHJT6arF7G2u5kIP+RA4GwaccFGHPcpDjHXPQr8hBn+Fg33QJBzkMOeiFg15xUCk5y/BsDl7wApvCwcLBwsGegy1zsJ3jYCtbykEOynCwFQ62yzgYc+k52CoOtipG4KDE' \
			b'n+ZgvCrDwXaKgzrHLAd1BNMlx6o2IxxshYPtgIP5ZFCMreJgqzjYKg6OPW6kFlAcHKQvHJT6arF7G2u5kIPtiRwMgk85KMKe5SDHO+ZguyIHQwU1B/umSzjIYS7UKEhYOKiUnGV4NgcveP+MK9OpTzCdijJxBZdXi0vLy+zt3DJ7G7YElxIUcMn7Qkw6qA78' \
			b'nScmw0Hzss8m8pLyFF5aXRDhZYgfeGkZmfQl1KQkuCR1p1IYshNDR9mZ5J5jZxLBdMmxqlmenVwJaa+EnSPJgEzDruBTDgNBqTJc+yrWmzgado9oSm3S03SYI9M0tEDSHLEwC2nK5Z+naSx9QtOgCnM0DS2T0pQaaCWasrqnNFVNp2kqYU46jAkyZ5rqLmC4' \
			b'iHmaHr2sZoKq5a00ZXRZcLkKLmvGZT2Hy1q2FJccNBxdUigakXqUlbnRZZ9LT8ta0bJWMQItJf7k6LK/KkPIeoqQOscsIXUE0yXHqjYjhBR/Va5wQsh8MkjIWuGxVmxU3qycXmZ0SS2geDhIX3go9dVi9zbWciEP6xN5GASf8lCEPctDjnfMw3pFHtYZHvZN' \
			b'l/CQw5CHtfCwVjxUSs4yPHt0Wd5DUzhYOLgKBw1z0Mxx0MiWcpCDMhw0wkGzjIN9kpGDRnHQqBiBgxJ/moPxqgwHzRQHdY5ZDuoIpkuOVW1GOGiEg2bAwXwyyEGjOKiWdFA1AgfNGAdNysFB+sJBqa8Wu7exlgs5aE7kYBB8ykER9iwHpTWOOGhW5KDJcLAv' \
			b'dsJBDkMOGuGgURxUdeXvszlYXj1TOFg4uAoH2evGznndWC9bykEOynBQvG7sMq+bPpeeg8rrJp62vddNiD/NwXhVhoNTXjdJjlkO6gimS45VbUY4KF43duB1M5IMclB53VjldWOV140d87qxqdfNMH3hoNRXi93bWMuFHDzR6yYKPuWgCHuWgxzvmIMret3Y' \
			b'jNeNarqEgxyGHBSvG6u8brSSswzP5mB590zhYOHgGhxEswwFxq9JDqLW05b+wMWB+kMGhBRa8RULQNhnE0FIeQoI42kqL4MwxJ8EYX/VEIS0DnwMhEmOORAmEUyXHKva5EHIBQ8V1iAcSQbk2IR3IzgqXQQhVUNAyOllQEgt0INwmD6DMNRXy93bWMtlIOQC' \
			b'z4MwCj4BYRD2HAgl3hEI11zjzyqdglA1nQahhIFF5BqFmjEItZKzDM8FYb2xl88UEBYQXisI2Z+mmfOnacKWgFCCMhwUZ5pm3Jkmy8GYS89B5U7T6HIEDkr8aQ7GqzIcnHKhSXLMcjBpmi45VrUZ4aC40DQDF5qRZJCDyn+mUc4zTaU4WI1xMHWYGaYvHJT6' \
			b'JpW3sZYLOXiiw0wUfMpBEfYsBzneMQdXdJhpMg4zqukSDnIYclAcZhrlMKOVnGV4Ngc3/FqcwsHCwWviIDvKNHOOMqjvtKUc5KAMB8VRplnmKNPn0nNQOcrE003vKBPiT3MwXpXh4JSjTJJjloM6gumSY1WbEQ6Ko0wzcJQZSQY5qBxlGuUo0yhHmWbMUaZJ' \
			b'HWWG6QsHpb5a7N7GWi7k4ImOMlHwKQdF2LMc5HjHHFzRUabJOMqopks4yGHIQXGUaZSjjFZyluHZHNzwK20KBwsHr4mD7CjTzDnKoLLTlnKQgzIcFEeZZpmjTJ9Lz0HlKBNPN72jTIg/zcF4VYaDU44ySY5ZDuoIptsdXRMbKM9BcZRpBo4yI8kgB5WjTKMc' \
			b'ZRrlKNOMOco0qaPMMH3hoNRXi93bWMuFHDzRUSYKPuWgCHuWg9IaRxxc0VGmyTjKqKZLOMhhyEFxlGmUo4xWcv4+m4Pl9TSFg4WDq3CQHWWaOUcZVHDaUg5yUIaD4ijTLHOU6XPpOagcZeLppneUCfGnORivynBwylEmyTHLQR3BdMmxqs0IB8VRphk4yowk' \
			b'gxxUjjKNcpRplKNMM+Yo06SOMsP0hYNSXy12b2MtF3LwREeZKPiUgyLsWQ5yvGMOrugo02QcZVTTJRzkMOSgOMo0ylFGKznL8GwOltfTbIGD5XWmt8NDxw4zbs5hBt85QVvCQwka8tCJv4xb5i/T5xJ56JS/TDzten+ZEH+Sh/1VQx66KX+ZJMccD5MIpkuO' \
			b'VW3yPHTiLzP87YuRZECMTvnLOOUv49hfhk7HGuep6FKvmWEuTMVQay18b2Ndl1HRneg1E8udUDGIfI6KEu+Iim5FrxmX8ZpRTaepKGFIA/GaccprRqs6S/JsKl7wsppCxULFQsUhFfmpoZt7aojvYKItpSIHZagoTw3dsqeGfS49FdVTw3ja9U8NQ/xpKsar' \
			b'MlScemqY5Jiloo5guuRY1WaEivLU0A2eGo4kg1RUTw2demro+KkhnY41HqFi+uxwmItQUWqthe9trOtCKp747DCWO6WiiHyWihzvmIorPjt0mWeHqukSKnIY0kCeHTr17FCrOkvybCqWl80UKhYqrkpFfobo5p4honLTllKRgzJUlGeIbtkzxD6XnorqGWI8' \
			b'7fpniCH+NBXjVRkqTj1DTHLMUlFHMF1yrGozQkV5hugGzxBHkkEqqmeI+vcTHT9DpNOxxiNUTJ8kDnMRKkqttfC9jXVdSMUTnyTGcqdUFJHPUlHa5IiKKz5JdJkniarpEipyGNJAniQ69SRRqzp/n03F8uqZLVCxPEncJg3hGHSnBuVZ+FTR8VNFN/dU0cmW' \
			b'PlXkoMxTRcdk3C/98eA+n/65oiM2or4mEcJjRYk+iUa0LRIx81zRTbCR1FZ98s8Wdbnw2aLLbKPPFh3zkSudPFvMJ3Ow/B1++B5LGx8uOmqoPf/GcDfCRmqHno0YkROPtex/Y5hO8W8Mq0Mbd5c+ZHSTiKTCm16zjp4xiuTnCElNkvmZ4b51VnjK6FJG9vrJ' \
			b'DZg8ZuRy42NG7JR4BnJlXHI15YGj0n7Depni0gIm8R5ROAm96AHvh8DGPdDNBRiiB7wLAOPxQL+BrAC64XfWHL0W/PoxmnsheBlgXhdSFw0wGx5gNnMDzEa2dIDJQZkBZsMYpe8FA8yYSz/AbNQAU21xgCnxA0UJohw2GGbGazPDzGZqmKnzzQ4zdQTT7Y7K' \
			b'GpspP8xsGKNc7WSYmU/mYONuGGk2aqTZ8EhTHHVie+ZGmk060hxkJCNNqbjWAh/LsHSk2UxitB9phnInHA2ynx1pcrzjkWaz4kiz2Q1Hmn3TJSNNUcdWahRELSNNpfMsybNHmht+qU0BZQHldYOSvVjdnBcr/igMbSkoOSgDSvFidcu8WPtcelAqL9Z42vVe' \
			b'rCF+BKVnUPoMKOO1GVBO+bIm+WZBqSOYLjlWdRoBpfiyuoEv60gyCErZDaBU7qyO3VnpdKz0CChTp9ZhRgJKqbjWAh/LsBSUJzq1xnKnoBTZz4KS4x2DckWnVpdxalVNl4CSwxAN4tTqlFOr1nmW5LmgNBt+6U0BZQHldYOyZVC2c6BsZUtByUEZULYCynYZ' \
			b'KGMuPShbBcpWxQiglPgRlC2Dss2AMl6bAWU7BUqdbxaUOoLpkmNVpxFQtgLKdgDKfDIIStkNoGwVKFsGZSugDO2ZA2WbgnKQkYBSKq61wMcyLAVleyIoQ7lTUIrsZ0HJ8Y5B2a4IylBBDcq+6RJQclisURC1gFLpPEvybFBu+K045RcZCzJvBJmeV4T4uRUh' \
			b'qNW0JciUoCEyvawI8ctWhPS5RGR6tSIknvb9ipAQPyATDzhqRCYlwdHqTqUwBKefWh2S5J4DZxLBdMmxqlkenF5Wh/jB6pCRZECkYVfAKYeBnZ7XiHhZIxIbNsNOn64RGebF7Ax11+rgYzEWstOfuEYkljthZ1CCOXaGNknZ6VdcI+Iza0RU02l2ShgYSi9r' \
			b'RLxaI6KV33ARz2Xnht+kU9hZ2Hkr7KyYndUcO8OWspODMuyshJ3VMnbGXHp2VoqduhyBnRI/spM9gegrsLNidlbMzphChp3VFDt17ll2Js3UJceqZiPsrISd1YCd+WSQnbIb2MmHkZ0Vs7MSdoaGzbGzStk5yEvYKXVPGiIWYyk7qxPZGcqdslOUYJad0iZH' \
			b'7KxWZGeVYWffdAk7RT1bqVGQtrBTKb/hIp7Lzg2/faews7DzVthpmZ12jp1WtpSdHJRhpxV2LvOg7XPp2WkVO62KEdgp8SM7LbPTKnZaZqdldsYUMuy0U+zUuWfZqSOYLjlWNRthpxV22gE788kc+t3ATj6M7LTMTvGojQ2bY6dN2TnIS9gpddfqoGq8kJ32' \
			b'RHaGcqfsFCWYZae0yRE77YrstBl29k2XsJPDkJ1W2GkVO5XyGy7iuezc8Bt7CjsLO2+Fnew46+ccZ1GNaUvZyUEZdorjrF/mONvn0rNTOc56tUV2SvzITnac9cpx1vOTTvxChsQUMuyccp9Ncs+yU0cwXXKsajbCTnGf9QP32ZFkDjbuBnbyYWQne9B68aCN' \
			b'DZtjZ+pBO8xL2Cl11+rgYzGWsvNED9pY7pSdogSz7JQ2OWLnih60PuNBq5ouYafoZSs1CtIWdirlN1zEc9l5i+/12QYj51yATmGhcDDyL7BPmHeVvLsK1vFaSz+31hL1j7aUdRyUYZ2staTvBayLufSsc4p1OkZgncSfXGrZX5Xh29RKyzzTdDFMlxyrGoww' \
			b'TVZW+sHKypFkkGlqZSXuR5o5eWtrll/pesqYnGCL1096Xjfpl6+Z9NNrJntUBXmmqBIZzqKK4x2jygmqLqTU0WpJopRk6I4xxeGIKSeYUmsktd6yiJZgivC04RfslKFdGdrdytCOPVj9nAcrROAtxR0HZXAnHqx+mQdrn0uPO+XBGk/73oM1xI9DO/Zg9cqD' \
			b'lZLgsiD6YgoZ9E35sSa5ZzGoI5guOVY1G8Gg+LH6gR/rSDKIQdkNJOTDCEN2ZfXiyhobNofG1JV1mJcwUuqu1cHHYizl5YmurLHcKS9FCWZ5KW1yxMsVXVl9xpVVNV3CTA5zoUZB2sJMpfyGi3ju0O4WX8OzDUaWod0VD+06Zl03x7pOtpR1HJRhXSes65ax' \
			b'LubSs65TrOtUjMA6iT89tItXZfjWLR7a6QRNlxyrGowwrROmdQOm5ZNBpnUKaJ2iWTc1tOtSfoXkBFsdM6tjWnXLUdWdiKogzxRVIsNZVHG8Y1R16wztugylJMPB0I7DEVOdYKpTmFJ6yyJaPLTb8EtuCp4Knp4ITy17d7Zz3p1t2BI8SdAQT614d7bLvDv7' \
			b'XCKeWuXd2epyCJ5C/Ek89VcN8dROeXRm8ZQUw3TJsapBHk+teHG2Ay/OkWRAdK1y4WyV/2ZbTeCpTT02Y3KMp5a9NFv2z2yXO2e2JzpnRnkmeAoynMOTxDvCU1utgqc245cZMjzGk4SDDWvFMbNVjplab1lEi/G04VfLlJeYltnFK5pdbNlxpJ1zHEH1pC1F' \
			b'GgdlkCaOI+0yx5E+lx5pynGkVVtEmsSfRlq8KoO0KWeRJMcs3nQE0yXHqjYjeBNnkXbgLDKSzMHyd8CbchNpm138OcRxzKUOIsP0hXdSXy12b2MtF7LvRAeRKPiUfSLsWfZxvGP2regg0mYcRFTTJfzjMOSfOIi0ykFEKznL8NxZRLvhN8cUDhYOXhMH2amk' \
			b'nXMqQd2kLeUgB2U4KE4l7TKnkj6XnoPKqaTVMQIHJf40B2O8DAennEqSHLMc1BFMlxyr2oxwUBxM2oGDyUgyyEHlYNIqB5PWKQ66MQ6mjibD9IWDUl8tdm9jLRdy8ETvkyj4lIMi7FkOcrxjDroVOZhxQVFNl3CQw5CD4oHSKg8UreQsw7M5uOEXwxQOFg5e' \
			b'Ewc9c9DPcdDLlnKQgzIc9MJBv4yDMZeeg15x0KsYgYMSf5qD8aoMB/0UB3WOWQ7qCKZLjlVtRjjohYN+wMF8MshBrzjoFQe94qAf46BPOThIXzgo9dVi9zbWciEH/YkcDIJPOSjCnuUgxzvmoF+Rgz7Dwb7pEg5yGHLQCwe94qBScpbh2Rzc8EteCgcLB6+J' \
			b'g+x12c55XaJW0pZykIMyHBSvy3aZ12WfS89B5XUZT7e912WIP83BeFWGg1OelkmOWQ7qCKZLjlVtRjgonpbtwNNyJBnkoHKzbJWPZdsqDo55V7apd+UwfeGg1FeL3dtYy4UcPNG7Mgo+5aAIe5aDHO+Ygyt6V7YZ70rVdAkHOcyFGgUJCweVkrMMz+bghl/Y' \
			b'UjhYOHhFHMRODQXGr0kOog7SlnBQgoYcpFBofPo+nYN9LpGDlKVwMJ6m4jIHQ/xJDvZXDTmIoaMcTHLMcTCJYLrkWNUmz0EuuLRSwsGRZA7yLRzE/cBBqoZwkNPLcJBaoOfgMH3mYKivFrvva7mMg1zgeQ5GwSccDMKe46DEO+IgNcpKHGSVTjmomk5zUMLA' \
			b'IHKNgoSZg1rJWYZnc5BevgIMKixcg4UQB5rkephoChcfjYtoYRETiCc0yvYwA0jsHLQlgJSgISCtAHK/9Jd/qWCOPxGSVkEyFsT2kAzFmP3xX4k4pKSdomSSZY6ScoqKyeNFfUl/7QgnrXDSDjiJelRZ0uFccgf5Fl5axUureGnHeGlTXg7TZ16Gmmst8HEP' \
			b'ZbiQmfZEZoZypMwMsp9jJtVuuN7BrghNm4GmFG/gVSrhYDKtUNMqaqpW54prasIhQBPPG/pvHxif8L9z9J/iIEItWQr4IoA20NMn8BmpqXg5D0tmJAOSoTiGQw3C2QUNBLw81bqUZkSqQKlAqLHFB4pIkT5WFhosJcwMXQZUmaNJjiSXLiY4pscxNayQIlDC' \
			b'6dGSW0CEBAQZBJxn/3ujHy1+sPIn2PeMZV/o7x8M+JitJkN9ZKXJEEcrHE3wuLu+NrrRyu7l/cnnGNSTrOmxHZ23oDnzuYYz/sBmDq3lPvwWT7SQZBiDVUTj5qaNW/P49q1aaOLCbT3qy+mWrs1YO1csnrZ40dpl7pNB9/p7ZYgDouF7ZogHtqFu28Qi1tge' \
			b'HQ4aQUugPQy0B1tJr++h4VOBxVx2E013tVs0mzbrUrfUdKr735pMyVITapVTXDSjqCTFlI6ZUlTzaEWx/QaWlGLIkIoHisG6+v5eIDW1/bgRi0KyDm+N2KNt2Vf9ewHxwMNdKvTDB2xRuu/006bZbezWs7fLOL/SbOIutOq6y+Y6NmGb7Zl3ojdiV1e1qdSB' \
			b'D+OrTZ/y1hQpPGFT7RXa1e6yu9N22gT6zZpAtwnzd9W3pMXkrXYbWW/S3N3M7eNFJq47cXax2pqJe4x5xur+zNzZ84wLTV1i5siq3KSpG39AtI6po0H+fZu7mt5DeabJwzGueYAK4BAXCnSa8asvNn4T/gbn2T8q66n2z513m4dP/q/VBkJ9N3e79yQ20D6J' \
			b'HXTL7SCK+ezbPnsrtrCmX0J5V7d/IPVHeLhcP9rtn9UW8ATrVzcrDnKr67F+m7Z8q1k9O2353o3Vc+n83gKrV1NjrDnYRXlepdV7hxavflp3msPZN3znDnabMqd3/aZuY4+GVxjkomDLnN6jmDjztCbubI+as01c8aQpJm6TJq4tJu5xTJzdvdqmQ/TEsqAn' \
			b'cI7esnFzT+AcrQxc112VfVti2/jN/IaXY+HJjTpJX4t9Q5fUp3KS3v1P9wAspscVzVaN3tmGzmAFcC1jdydG7xyDh+tpz7+zu9o7uidZBsIrSzFT5+/V3J35WJZbzV12X+duz8RBNaCMqC+bNnXZJdVPYe7gGOq/3OzpZR7p8o5iApeZQOyOtJ5+j1p4NabQ' \
			b'bcga7lF6mFW73CjiCiW1WEMv0UAT6R/TRB4ewUqOvuji2FK6J7aSzZk3hbbcGF5sFVGCT2QaMecl9hETQl/RLVjH2pkLbhax6zzlCuJzrOPglrF9THtYPdVdo7aDh23eMRY7eFt2cMk8YGL+auq2279BvEnz1z2m+au3YP6qYv6K+du0+buO8fEtmj9o0Uc0' \
			b'f2YL5q8u5q+Yv02bv7aYv6cyf9XNPS+5Clt3PY5927Jv2zdtj2XH8LXAt/XA9wKXlgrfF16xVwuUspiw+zBha7nu3aIpo1eyXYcpu0HnlTX89FrzADwik2aKSSsm7Z5NGg1uNnVzRiUqBm2RQcOXgRrqxA8IBDJtm114UUxbMW3vxrR1mzNtXTFtK5i2jSyv' \
			b'WPprUxdaOq9+FeoWLF79yFavFstn7sX6UZ9OLWDdLzWjXxLrP49tEbkw1IDdSaaxvi7TuMLvGZ1gH2usPvXy+gw7uZE1GsVOFju5LTtpju2kUXYy/Ty+nTTL7KQpdjJnJ2uxk+YMO/moCzWKnbwRO3lnNtIe20irbKRNPo9vI+0yG2mLjcyPtan0i+3joy7c' \
			b'KFOJZSrxHRtAyuaGXVg2aeSefi7RWTRp/OD3URdjFJNWTNqjmTSOdHdueavZNGy/8Ll+m9Y0D8g46Gl434a97QENNvQ4+CZT5x914UUxdcXUPaKps8XUXWTqbPzchakriyyKqVOm7kDPz3Bu+BrMHmn7la674B+rflKrR0VYbcwqFVrP6FGCWaNXk8zh5LT5' \
			b's90DgRGU6QEhA93xgSw99KUHtNHQD+DbkCEsSzWKIbyqez7qaldr/J78lo+KsKLxa9Y2fs05d3yLTF5ZylFM3jWYPHraV9bZnmvy+GHpzT6jsGjhsENVOKqtHZm2spSjmLZNmraKXj1cXiFwiWnjNryDx68W5+1Q8SvaoR/29htZylFM272aNu6q5fUoq9s2' \
			b'adg7MW7GPiAkoRfCNz+M2Mjqi2La7sG0cRd8aq/h+7Bs9+U1Z/BuraI3QPmNLJQoJu2WTBop8mYXQly/SaP2LRatt2jkQIKGoWtxpybTVtY4FNO2hmkj+/L0Sxzuw7SVu7Vj21bhGoe6IpNW1jgUk7aOSauLSSsmbQMmrS1rGYpJW27SSN03uRK12LQ7tWk4' \
			b'BKWBZ3t7axZAleOPaW/RvEG7bu5HtDf2VPQ2zRxKf4+XX4XBw/puyeyh1M63eWjq6t0r6i8N6i4qUe0NnTC7Vx7fcgThKDb4ULDVwfiaooqCm92rGgpVt/ij8XWLZtF//Rz2n+3BmGLHoHh7yA4MGGYGhqWrKcxgGBovsCNoCqCn70C5QbVBF0AxoRFAqNDQ' \
			b'aGwOaIbB+EBIhZ3ygJ0SOmPMHM6DHqFyYzOiWmBfqmr06oFjkAKqN/YZrG0F6oGzjp1cBd3bohnAFMFMoINz21Ap7aqltLuT/yj3BnP3p+YPyogG+XA4oSQNMqQZ/as6I5beHZ+jgrnpgoHC48+iV/RrmGaqnBWXFX/v/Li8EQ64shCNsTmqA9Bz8Ed+veic' \
			b'qj6DOJC7S87gVWj8MYx+GQ06CJ2hyvonrywQp8HfuIdKw63Ban8GSmMq7qLt5ZWk7jRezwqMXAXdq2rxruGQr7erJuoO90En/+E9ShrCdwNWyJ+cgdKpY2qPLtseNQJ/vFUcNgzez1HboMVUL40bbapamstzk+HNJg6VoEnQxRpNdyXrcvhtCZabFX0NGn4h' \
			b'KTdx0zezx2aHtECPucnhHBSEmr7txpsf8qGbK0S0FgXeDAVxwPUsErj/BetpDkE8aHCHG92X+tyZ/vxBRwkX6M8JV+YuyySTORxmexiJk6tXcjZN7jgWKRaEbr+n0eBiCxs3WZXvjHhHv8OxAvVKuPWDe8wFfdOc1z2t6qL1sm5K46tNdNV6l9n0kFICKxlI' \
			b'nrz506PShmNE2ZMR93R0fCPiwiyWb6x1dUHAYr0yu3vdWGfMNRh3u9vGxk1m1+lm9dP3tMO77m3tboUNJ/xWSegpcmIVyo+Ti6We0h1M+D431pkVpjCyirG2tca58ZU2nqu/ZOOmy0+IlO420d1wrHKnG+tMfn4JdObyHucfo9fZ3XDDCfbsiVO3g7nkem7I' \
			b'kYmpOAqeHQIfdtArXLNz76g7etUla+mWBxkPQxx8qwi+Kn4b3dTvhhsO+WUPWzoX5ek3i1V27yArfqCTn8QqCJjSLXyIfJ8b68zILN5WEYD+HdvauBkvmJbamOnfRLdEZp61kTeN+pyd0EweyV769cgb61t+SmupqX8s876ku4/pybyO1Lvshm4XY+ckRmNn' \
			b'YjzGdmKuLN+V5t/uCeXo8XenG+vM6ITbaihH3VgX53b3SBu6OJ57MTdnfi6qdMGpLtjt7nVjnRmdhFu1C6JurNoN0TX60TZ0ND73Ym7V0Wmq0hPHeiK6ud/pxjoz6iq2ek+s7dq90e0edUOP/3MvZi/hMtG0vEO2u3vdWGfOn2i6YKBKqrCwb44NRPv+2e3O' \
			b'23CxyOmxcUGO5TU083F9nT3BTV98phZ3V1wadqcb68zoBNNjdtdEPR6j6+Jyv3ey6dVzlyXF4rii+aCtzSXj+s7tbfiD7PRl30FurEPL54fc+r1aa8xKvXtc8t1u0YYrLpdeM9zC4tjzE4D2hS+1mBUOWYQXzEnxY6Z3/YBpiwYBl3qftVHVoGnPTmBiw2XU' \
			b'j5Hu3MZ6tXze6spNAy70v/qNZXfB7Fh59JzRDLe7ZOOKmYvSmN3wPQuPmsFgY1VbPqn2yGbizOfNy81Ft3vCDZV5xXi8hv6CObxiNoYagm+LKVuysZ6NzvsVPTtLz8yubOnGerbOJOdWCHWWRxS+perWNhZucXd7hS8fu7WNhXtFc5tbeTyBC2sv3nhtbP9Z' \
			b'LdH+6ygXdZjEOSnJ3MYKVFaaLlcgs7vXjXWmePct1xm7u9eNdaYssV2uM93uXjfWmeK7uFhn8L26d7qxzpTX3C3XmWp3rxu/lLS4ZC7XmXp3rxvrzAVTs3erM2Z3rxvrDL6kmt44XfMNDqiEBMhS6MZiADY7BVb4Enc+AcN0rUmgCBQDRGZxQQv6V+CrB9nj' \
			b'DfQsGxuEm344th/ERoHTFahe6aeWZ2CgWf0btBtUG37O2XQcnr69jGOAgkBTYPyWX9GPKkkq2JDaoVphOKgOv5QZDHOSCqlyc6S+QXXRkxffyM0v+YcWkRf880v026MX54eX5uNqfh6igD6/wk4DSk7vt0HVZkBAtslrweG6lv3CnMHjGkPlBsRZ3G9oub1c' \
			b'3fQhYDy+fv7/AWiDPAA=' 

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
	def expr_term_3        (self, STR):                                                return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1].replace ('\\}', '}')))
	def expr_term_4        (self, EMPTYSET):                                           return AST.SetEmpty

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
			if rule == ('expr_func', ('FUNC', 'expr_neg_arg')):
				return self._insert_symbol (('PARENL', 'PARENR'))

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

			return self.parse_result (None, self.pos, [], self.rederr) if self.rederr else False

		return self._insert_symbol (rule [1] [pos])

	def parse_success (self, red):
		self.parse_result (red, self.erridx, self.autocomplete, 'incomplete' if self.incomplete else None)

		return True # continue parsing if conflict branches remain to find best resolution

	def parse (self, text):
		def postprocess (res):
			return (_ast_mulexps_to_muls (res [0].no_curlys).flat.setkw (pre_parse_postprocess = res [0]),) + res [1:] if isinstance (res [0], AST) else res

		if not text.strip:
			return (AST.VarNull, 0, [])

		self.parse_idx      = 0
		self.parse_best     = None # (reduction, erridx, autocomplete)
		self.autocomplete   = []
		self.autocompleting = True
		self.erridx         = None
		self.has_error      = False
		self.incomplete     = False

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

	a = p.parse (r"{a = a}")
	print (a)

