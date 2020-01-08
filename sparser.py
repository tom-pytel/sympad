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
RESERVED_FUNCS = {'sqrt', 'log', 'ln', 'Function', 'Symbol'} | AST.Func.PY
RESERVED_WORDS = {'in', 'if', 'else', 'or', 'and', 'not', 'Function', 'Symbol'}
RESERVED_ALL   = RESERVED_WORDS | RESERVED_FUNCS

_SP_USER_VARS  = {} # flattened user vars {name: ast, ...}
_SP_USER_FUNCS = set () # set of user funcs present {name, ...} - including hidden Gamma and the like

def _raise (exc):
	raise exc

def _is_valid_var_name (self, text, allow_funcs = False):
	toks = self.tokenize (text)

	if allow_funcs:
		return ((toks [0] == 'VAR' and not toks [0].grp [4]) or toks [0] in {'SQRT', 'LN', 'LOG', 'FUNC'}) and toks [1] == '$end'
	else:
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
	ast = ast.strip_curly.strip_paren1

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

		if unconditional or ast3.op in {'{', '(', '[', '-lamb'}:
			return ast3, lambda a: wrap2 (wrap3 (a))

	return ast, lambda a: a

def _ast_var_as_ufunc (var, arg, rhs, force_implicit = False): # var guaranteed not to be in _SP_USER_FUNCS
	if var.var != '_' and arg.is_paren and var.is_var_nonconst: # f (vars[, kws]) -> ('-ufunc', 'f', (vars)[, kws]) ... implicit undefined function
		argskw = arg.paren.as_ufunc_argskw
		ufunc  = _SP_USER_VARS.get (var.var, AST.Null)

		if ufunc.is_ufunc:
			ast = ufunc.apply_argskw (argskw)

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
		return AST (*tuple (_ast_mulexps_to_muls (a) for a in ast))

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
				first_var, wrap = lhs.comma [i].tail_lambda

				if first_var and wrap:
					ast = wrap (AST ('-lamb', rhs.stop, (first_var.var, *(v.var for v in lhs.comma [i + 1:]), rhs.start.var)))

					return ast if not i else AST (',', lhs.comma [:i] + (ast,))

				if not lhs.comma [i].is_var_nonconst:
					break

		else:
			first_var, wrap = lhs.tail_lambda

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
		return Reduce (ast)

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

				v   = n.src_rhs
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
			return PopConfs (AST ('-ufunc', lhs.ufunc_full, (commas.comma if commas.is_comma else (commas,)), lhs.kw))

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

	if name and not _is_valid_var_name (self, name):
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

	if name and not _is_valid_var_name (self, name, allow_funcs = True):
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
			b'eJztnXmP5DaW4L/MAl0FKACKpCgp/ysfPWtM+RgfvdMoGEb56IGxvuBre9CY777vpEgFFYorIyMyiFSkJIri+fh+FPVIvXjzl8/e/fj1xx/9pfnL//rup29hp6fvfvHp67+/hoPXX33y6tP3P8LDePD6q3c+ffXuv+NhPPjir1989O4nf9cj2H/08efw/7Mv' \
			b'3sH/r1999r/l8O8fkjfYw/+/vfoUj//jU/T7GmN+/fG/wX8J4/VX73EoeD8fvvP+v3317qvP3v9Mjj98pa7vTId/mw4/4UMKIab2r3Agu1b2FvYffvDRFxTuBx99/KHuWz2wlCAKKBbP7OxzzM37H37y+d8/ex9j/eCjzzE3H32Bob3+4EMqkA+5CCnn/P/d' \
			b'jz/88JWWOjp8yqX+qZY6u1HyP9VSF7dXvJ8S8mmWLErQf8C/Vx9+Av/fe+c1XUPXj96TwsOjd6bDv02HUnjvv/7sfXHRoseAPufEQwLR04evPvns848xxZ9+8CF5/893sVBeff559IZl+d4Hf/vgPbz+rtQtB/PJayp6KDethf/87P13ycN7H/z1ryhYH33A' \
			b'skk5efXRe1jAeOFjvJ+i/j8sY7hrWfgg9Hf/HQ5/++Pr3/58++tvfybHv8HxN29//e73r37+9atvv/7ht9/f/ppchsPv/vkLXPn+zx/h+Me3v3/1zc8/yNGvP/+/6YgD+u273377Jh79Eo80HAh3Ovzlu1/15Kfv/uurt7/+l56+/Tre8f23/4yuv/8eb/jH' \
			b'229+1+NfKB3s/MdP30xp/sc/fslOvvr+myQlP+rhD9/Hw58m19+/+zUe//jHD199/2MM7Js/fv3hv5Oi0cOvv//p5x+TLMVU/fr2mzQoONDTP7+LV95++2309DZm7p+/fTfllAoz5gDzlBRsvPDHT9///FO88N8xRd//9HtMElQu1nhSH99M+YOLaUH++Xaq' \
			b'p59jWv5Ivbz96dvMPS3pr7/5+ccf38bTn2NgX0Ox/N/vpmrM/f3y/XfffBdPQER/mkrnl99+/zlGHaUr5uTnH6b8U6DZyW/JnV/98OfbH6YS5Tu/bN682ATXBPey4QOPB12H/0LThZdyCmd01KO3Bh3kkjrwWdD74IZenfCQfG1o37XNC++ajWu69mV08Ojg' \
			b'vTpsRjxwLf/r0bt7mTrBNnfqfeqEh3DUBv7Xj82mHV6KEx7CESZ+aDq4j6/0eAB7C3fj3o/4zzdhgDs4sZOTnm46Q6H65kWgTIwv9bynXBpOEiTEYcAD/iYnl546LwfohoHADa2PRx0lbmheWDiDSgj2pbhsHCXCtvyvBxfLdQJneIjFSpWAd75MTvU4cbe8' \
			b'21CVe/r5Ti97PMBEijsnvdl4ceRzSKPrKPd2cqDSCdM5FVfnZg6Tj42nTPmO/wW+gEnxnDQvp1o3kDbPiev5X28gF3zRYWWQVAUoJBQQuRBaveAHqVsWXY8pYDmEiKiQMYGSPHQa01OuAefJDW+H2kVRkxKIp27uJFKSO/fbp7Mbh+3Tgg+fO43bp9lNG89t' \
			b'1EhxttIiMXUtiRNUsRslYKxRLsTovO00nW48SZa30N6hBUPoYzOA3IUGY3YiX9tXUTH1bg9PUKu5p42ndoz1OjYhyjA2Z64tg40Wk9aBHui17aJzdJxcPLsMk0vHLsldgVyCUZeNozw7x//6NiYvOtnUCQ/xaOR/UGwvX06HeNSx9Oot2Mq4zqBM2kmK8BT9' \
			b'TadQoaRJBvan2hBVBVUtFCg3uNbxvwFub1m+W0eHVI7Y3OSA8tZie2pYgffafNFRnOI5KQQv0RqJA1tog22w4K4u4EAJ7EUqRWfAOTRS8kM/8MiZRZVHMtfzvx5qxXIlwRkeYolACx6wwEXEfTNQ+UAVvrCG+dS0JGTBarboYsusKl0EXUwpgxIE8WP57Lgc' \
			b'pO2rcDqtD3B8EaZGSKd+ShYwmZIL0veCakGaE556Cn/Lae5DT5kkKMaWNRTk0rd6ZK0csTjhAZctFOLEPzwbs2jVJZ5tLEtRJ6d6BRU1BW07/tejXxYPbEmWLkLIzDk8CHoQLw16wIViKX98xGKJB1z5RjxIE8I6tUwpaBo2Y7Ol8kZPI//ru0lxsQ5DUhj+' \
			b'N3V/ghFKdiP/w+6ONH44w0M8GvTiSzmFM73A4UCKho6kyas0Be2FBMQcKC+5HYUjUAmFTi9g10pc4Ah6dW8MlAL+2gY2TwAHCQSZBMEDFAJdQaVAHUOjx8JswPPQN8MApQi3tSj5HfwC/Hr4Yek6+HnUsVBcrQGfBm6D3gL4AVS2HqsJKgiOUNTgbo9XwMnA' \
			b'sYFjKK0WWjqoLABpC+q2hQJooWBaoGYLzi26Q+paSF7rUBDgDmyFoL1aaAktNKUWSr+FHLcYL9RiC2BuqdIhY7CBj4C/rhnGZjTNCBm0zeiaEeOABDWYMUwN3APtbuyaMTRjD52phjrAyInWQMQGyq5vIHiQANDk2K/tScMNwAkENqRsHJoR0gkF2UJJtlC+' \
			b'LRQwdDZBf4H6HLCkoFhBn4F6gSRhmjG/BrUC5AQyhi0cNGCPvcwwYpcFIAFQAOJBjxYEscdKwIoBhBlUlZBbyCy0Y2hAPdYDaqLWYmceDkEOqOpBDF5g/aMD795gNxtPsXJekoYiX5BiuoolD85Y+C+Jr3j1DUKczinsKjvPVHZejCwELde2SNCbF0MvIsWy' \
			b'MrBwUE3TXiSLqpwcguzlPqxsCogEAeWIQqgq6T7ECuvd1Qq/rwr3tcLvp8LxKZO6DVZIYJggBACUB8tkGMYqFfcjFW9wKKTW9x3Vd+ula+ipoScV9yWNRbJy4CeQ7CK6SufRk8wUyzwPrpPepe9V6VAIWt9az1KHUkdaO2ldxDrQcuey5sJNC/MyBZm0gbnc' \
			b'z+R9Luki4fvJ9m6ZZlkuyLDIbSquqZjOBHQumiCOVNmGnxAwYfxgEORZgp44a6Gfv9BfjILkIE9rTh7SOh0n6KTtdvoU6Irt1Ek71ftlxKDlIYM92q3T8LtWHiutpkC7Dx09LrwIHEXgGAJHYFCpYaawjCEExAEUXBWJY9phx4NBgWWjN7WEz17C3Fx6lvWe' \
			b'xz96t6ugWxynhwKoBX5UgbPS6Fmy+66K9LlLuPbq76xXb/ta4XdV4W2t7/up7xdUGNTvtk6eEby+9yMHtOyA9DRdE2q9P5965+c7fPjWRzp5BpfnQJGBkZ8K8OEAe7HYhcVHMXxmwAc0SEuVieciE1Dbba3tO6ptW2v7jmrb1dq+l9p+MUa6E85HZvwYdMTd' \
			b'yGBffeVxmVGTYOtD1R01P8wQNTh5O8nVf5jc5DWzXfIQDXfd37zg2M4fvCoRw+PXnaoPGRI6RxzOcBz8FHqWIK28YpJXxONQXyo+klrzdWjwjrQa1De/KaSXxrXa76TaX+ibeq9WGlb2MmugZ6kY+PLAQwjyFjN7s1mtbp5MV78YpNKM9EgG7qAMPNw3dGLc' \
			b'H8QoI1qBSJ2z+dYLMdSxHJgMGPcUZFrTVGaoMMTCQF6Ds4VHbhAixh69RCyTD9hMBSdc0kUdoa565470zhuaxWRf1vlr91TnUPSWZ6bZOtfsGdczFJ7lqYa1np9vPePUUSuTCmFfK/TWK5Smg9YW+5wrGGvNykRe2NeqfUZVawi3UhF1qsyVP7TzlHlui64+' \
			b'+t5PS8UlErTaee+lG0XwrS332lsuTnmmChuo31ut6O6p8drAjTY2Yh0v10bsSThmE+O83CUDojo5S6cQ6cwWrEcKpTQ9Tu+uM17OyOBsepzWSy3hM5ZwaXqcCn6dJvcYBe6T6XGqWqpInw//rPLf4BR31PS1h3aFVRSM4Lijg1o511Q5TvtKTgaj+H3BfDGB' \
			b'IL4sPSbXqruCqgtSJ0EeVSeo1NI8pvfJDxF11vU9PULiSK2d98lq8zlqraGtB+JajkeVoz/JEKzlNQJrPZxaD7zI4vGBNOv28y3P+8aBDyJ5byrJT+8XQcFwadpamucYwnC1GM+hT9jE9nH1iaz/2sszXd/VqjvHEJO8MLC9vGaQZ+FAxVyfgZ+wbpzjumCO' \
			b'ymCrWNjL3DQmrE7HJf+1mi6u/Xwt9ycp966W+xOopVFHvPVdprx4I1sEWYl3FBdWTS9aeb88tmzHwOZIo+i3UUheq+8izWYMtbgv2MEyhjtWwcqINu3P3T1+U7+Hc1dju7rKOS7aQGLVUaumr0jW1vx4ypMfk86zwAS/kxl553uuR8+mfvQ2+UueFm2z0VCa' \
			b'PWHqw9lTS8LQyivl4oKHA5vcDjwPcRADjqLixlpYukoj5ZZHykk8+BU1DpVvvcfuRYJ4nKSC4E5A0LGIdWLiL70NqFvHE2Bxh7X/kr7TjLuBzniKjpMpOu6lzuxw6TeXUApcNCFnk3I9d2JSLjfgznYc8sARjazE8LWzREiJrKJ5J6KJxe7EgM0l3wlhaymX' \
			b'fbfDiVd0ccn6wWgBQhcCSx6NV1K/WgVeJjc41cfs3nMEPYfWi7habiy9pIcFkwY/WZolDUGkuqTbcViOM8VBUberLmr8jOQWx1WJuXXi4vOqVoHW1jKWvuzcFZyRaU5Hv6yMepHRIBZanYDzrMQlVA3wrKoUx58djz87Hn+WBu64gTsZp8O97DrpuvKHzerw' \
			b'yiM/VPN34+pim483o5R7ul52/JzWCdN6Oq3DSk86rGSWHz1oWMnxsJLjYSVHz0KW61EfnbSLArf5ulzO7XOLR058HHf5kodY/Evpjn7Z6EANPSb7lzrkUq2jTreO8jJA4Olhn9SljhLIWNj0lpu7EN0gFmpcRctN2XNT9tyUfe1qPqsma6n662DnfVQ40baT' \
			b'hRpwD0Wgp56XVuheypcvO1zEA8oD4qjicR/iwV/ArBV/hxUPMXUM+o5Bj1LQWOm3k46QlRSw/AKdS5cB8hpkme1QTbYu9wzmqRqgJAP163h2mqweDgGFmUEGVVzPo8L8Yh7XxMACxblsWHa1MT+LxkwtskfRcLzzvOuk9iHqvrbTiz2d9U7fxXRiiRxk38sT' \
			b'ma75j+VdK+ZyCrSrxX3JUYoRi5vag9f2YKUdII0qfZ4HfSCWkXEzSu3yWKBp3hjsUtJHttEWBT+0PSYtgAtG+yEcOmcekspVzoXLlZc+ifDjiTytcLlQpvhVmJRqJxnE3HHWgqQey4obu8fiYSGcV53WEb72Idl0M/nk4kGjtta2UR7i14FITrjcuV/mWMZi' \
			b'nXmR3zbpmcE5fmsIv1mD7WLARy44x28X4zdOUZ7wnT+++8B0jVh0UHYoNmh6ZKAEcRFFkHwLMmBxTWQ0vkMTNzSWw0lhOEEJl7/G9Vax6LHsLVYw+MFKwFrAJoZV4bBe4BqqJVytCBclwtWK8NMGkA+Ln7LwWHFwD678iAs9os0wLg+JxsIgrRZtADtcLgH8' \
			b'oD04VJBFw1FSKnANO6eQd4tqAerGohkx5NPijBDIp8PFYKHVu9aAVG08vf7ZYIlv8AexbiAFG4/HptmM4GzwerOBAtygZtlg9W2wzjaQlw3kZYNqZIOlv2nRE7SxDWqNDaqMDdbQZsRrAb2jS0e+0MnhkcOjDgPtMDDI3QbVxAb1xAYVxQY1xAbFYePQHfK6' \
			b'GekAf+AKGdugY0BHg9FAOkFaNpgUChkzg3Kywca9GSjRcG3AENAzRoUR9+gA9bjBxELdbaAMsZQ2UCcbTC0l1mNy0AUVZDnFplvKCqYZU0NZcVhMWCiBbiInuAm0yAYkedNThoyUImYVSwJkdTNQJcABhoUl02NWwTuVIVYa5paCh7AG3FNxGcwPVSWmrcXw' \
			b'4RpI6MZSZcGBo7RSEkk2IJxAtUmlhrdhxeOT0QaUwabHPSYAPeMFrAVH3jBADAuSjMKEggCeR6wxdKPqw9Dhh2WDIgHtZIOyg9KEaRgwexQxpxBlp8c6aCk6FEysLZIPKl6sVYwYqx8U0mbovkRFiuqzKs+qPM+rPKvmrJrzmWtOi5pzSWNyP7xPVGfStz1G' \
			b'gYa8e55q0nZZmWon+wCV6nOtSk8L7ozatduhYf2eWtYmmvYQDdteqZYFd5zKmGnbblvj4qwrqL1lzdtjrfUrOpb/Mk1LDo+obSXKZZ3b76F1KYiTNe+U/5jtR9G8/S7d2++pfRP9e6Da7a9d8VKqx1wD9wUdLIKzpIebf4UH7Fr0D9i5GGHnhv/BSV+onHtS' \
			b'y6yTZwo5amMa5JnGQqJCZm0cX0zu0MYtaWMe8qBxFFHLJtHMNPKyOhQyaenSKOG6uh7j4M5k+9TTWNakvv2CCi+p73QUKlXjVlT5wsjWfJxuPmamI2o0AuZ5lEyHG3HxjPiJDzdDgrxPimjwq3jIUTDHQLeH6g+J+keJgWu4sPIcAfiRPsj3KgpwhnMRB90M' \
			b'CW2OBbTGx+WAIx68IKKAB/y8HH40hTDRJaiADgeUh4PyYGwMCTpQKDrRaIoLdkNngYU40JAp/yZYiM8IigiJyStzwk7hphvRgeLyubsgQn0JJlAyEBW8F1zQCYop7lFkYyDb3EBXRUeL6MABTNKuGACmdwkhxeTnWVGmcL4XuDLLvWTP8N7pzTSeTEjJ/Rsu' \
			b'pj5hDLr3sdroCuKg90vJNFxUnGTmkd4pWKJSSshEaep7LlNBUw4hARCH2Ql49mFOS8Ur4HEuJjInjwrFCn/E24xAlJsJQswap+FqA1IcaQISGrETtiquM8mnkCmtTa6NSCnrHqiD5doHKmo3PFDnydsHEg2P1zu0jHkgAfHdA/ecwB1a2ABgw5cDtmXvoKvZ' \
			b'f0sB0yXPd4D4PlBXBPThw4YQB3vSKxCmDf9Dy6ldFR33eW4xBz66rLHQXpCHSyzcl4NzBt4h//bi3sHMw1dlc+ahpLC7Qi9kW0I8Pi8QTzxG3oXCxrwLzLvUXXknvnY9Fk3eCnwLhUcj8rqEtVIq8xRjDdJjgffisEC2PJ+SESOlIvc6vhzm3o1eF6gFhpoG' \
			b'JkArJ9BIHAqzMIEszEAWmGNhjWM6hHU8x1Qaco5JZa9xjL3NORZyjoWEY9PjlEac8iupFd0Lu5IrXOhXyq6usqty6865hYU551YvW8RWn20Jtvi8gC3xGLHVFzbGVs/YSt0VW+JrJ7biTQVs9SVs9TuwVUplnuL4NNbvQFaeR8mEkRKRex35I2Rl3o1eF2T1' \
			b'jCwNTJBVTpyROBRZ/YSsfoasnpHVryFLB/+OR5ZKQo4sqeg1ZLG3ObL6HFl9gqx+QpZEnCIrqRXJmyIrucKFfqXICvsiawlWN02qSqn7pBRmuJ1RyuqmlFJP9O5JCSWO24TK3jfZKbR0I0BRDD53F0Cpr12Amm7aBhS6poBCgdj5xqmYyjzFq6+gZhmUHBje' \
			b'Z++e0CXkN2AK2SPjCY/7JDTG00LSjEQieCKrDsYTFUThpRUV2y4+cXin8EkTl/NJ63mFT+JtxifKzcQnCl74RBliPmnECZ/SepG8CZ/SK1zqkU/KpX15FB64H7QXkJB1qJm2QdRXEFUQ3R+IMLNzEFnZIojEUw4idlwFEX1i1c43JpFlEqXuSiLxtZNE8aYC' \
			b'iWxOIrsGoq0UbiV4FURZTolEYgJB+5xElklUiEZBZBlEGpiAqJw0I3EoiOwEIrsAIrsGInsyiDRDOYikmtdAxN7mILI5iGwCoundlEacgiipFsmbgii5wqX+1CAaKogqiO4PRBjpHESdbBFE4ikHETuuPxF1hY05xJYVmbtySHzt5FC8qcChrjBkt5tEpWTm' \
			b'SV5/JMpzKFkwvM9BxOYT+Q2klxIUselEDE5QVE6bkVgURd2Eom4BRWvmEvZkcwlN3AxFUtNrKGJvcxTl5hI2MZegDAmKJOIURUnFSN4URckVLvVjUbQPggrkGSt5KnnujzxoPjgnT5Atkkc85eRhx3XyhMLG5GEbh8xdySO+dpIneiuQp2TjsJs8pWTmSV4n' \
			b'T55DyYLhfU4etm/IbzBefAp52L4hBifkKafNSCxKnsm+wYYF8qwZOMQ5OseTRwKZkUdqeo087G1OntzAwSYGDom9uEackiepGN0LeZIrXOoXJk9rBD0X5s7jTQ86J3FKU4VOoMyR04mujiKrU4fa/amxRYwtSiBWUkKMskVCiIecEGMzmyO0PEwWst8Ufssy' \
			b'T5wYE3flxLgCCWyWcsvJM4TSBBS3vYbJ8t+umUJSEpNXtCZwqQWcExO4KTCxKHDKBK2CtQlFVEA7aTCeTAMpoxkNpD5PnDYk5RQBoAKbAEAFSvKSThrK5g3tpcUT7d1exYPD0ROJbugh4hlOH6IXAeMzfbhA+Z4Pa7Gbm4a11FOGDnFcBUcMLd0IGo6HtTJ3' \
			b'gYb6Em6QPmMnpQfdbGiH7TUGsI0Qd/AQVzHJefJXKTLLrWSHE5xzxPEQV36D8fFQSOJ4lCsNlEmykEJjpsQyXeRUGOMWhrvc2nCXO3q4S2fCKW5iDjPcqCSs4EZzkwPH5cNeLhn2ctOwl0acsCctV8mj4Ce9wtVw6YcPW/FV8fXUTzPXha3QxJ55xFaQLWJL' \
			b'POXYYsd1bIXCxtjiMbHMXbElvhRbgbEVEmwFxlZgbMVbCtg6eHysmOQ8+evYynMr2eEEz7DFT0D5DcbHQ8UWP/+kgQq2yik0ZkqsYItPFVsLY2VubazMnTxWFnOW40okYA1XkosZrvKxMpeMlSWPShpxiqukPHUvuEqucPFfGld7r99QX9PU1zTPB0l94+YT' \
			b'e9jNTRN71FOOJHZcR1Jf2BhJPKcnc1ckia9dI3DTTQUMleb07MZQKZl5ktcxlOdQsmB4n2OI5/TkNxgvPoVBPKcnBicAKqfNSCxKn2lOj+sX0LM2qcedPKlHEzdDj9T0GnrY2xw9+aQel0zqcdOkHo04RU9SMZI3RU9yhUv90ujZe3GEip6KnueDnqEhUGTo' \
			b'GWSL6BFPOXrYcR09Q2Fj9AyMntRd0SO+dqIn3lRAz3Aweta2fdCT51CyYHifo2dg9GQ3GC8+BT0Do0eDE/SU02YkFkXPMKFn4Z0QFdxO9Awno0cSN0OP1PQaetjbHD1Djh5NOIcb0SMRp+hJKkbypuhJrnCpXxo9e69tEOo43c2N0wVaXqwS6lhCoUzP55N6' \
			b'3ZRQ6smPvFdIifs2pMiXIsq3hY0Q5XlCaeYuiFJfgihSvB3vBFSeWYU7OyYBbOMKXQ/DVTHJefJXcTXLrWTHSNmkuKJczW8wPh4KsfC4zwNlaC2k0JgpscwtORV0UbFM3mcAo6LcBTAO+BSAxfxlAFM5WAGY5iUHGOVpAhhnzGm4CrCY5QlgaalK3gRg6RWu' \
			b'hC2AHbgQwrEg23vFgwqyCrK7A5ltSN9nILOyRZCJJ6y5fNU5kp0iy9p81TnxqL8pCgKaZaDZxF2X8GHP01KrLb+D4r0wjU5opVR+DTXFUFrUZ75owh5cs4VNIokJXLfDm5UBreyjiye026sntLJ8QhIR+0KbPNtqCYtdniykECPIFqibxZynwnDBcSaYeDEE' \
			b'Xf1H1ldg3REK2LNr2LMnY0/kZYY9kZYV7MXczlcCmi21QDHoUkDJWgsaeYq+KAXMvmSO66yW6fYnw9/e6yxU/FX83R3+sNnN8edki/gTT4S/PsOfpV8Rf32Gv/w3RUH4c4w/l7hH/Fn2FvHXC/76FH+94K8X/MU0l/BnD8afK2wSSUzgHvjLy4DxZxV/dht/' \
			b'VvAXI2JfhD+rJaz4s4I/m1yM+NuugSQ4LjjOhOJPQoj4s4I/qYEt/Lk1/LmT8SfyMsOfSMsq/iS3W/izOf5cij874U8iT/EXpYDx51L8ZbVMtz8Z/vZe3aHir+Lv7vCHzW2OPy9bxJ94IvwNGf4c/Yr4y+ZaiUf9TVEQ/jzjL9km/Dn2FvE3CP6GFH+D4G8Q' \
			b'/GkMRfwdPAfL+8ImkcQE7oG/vAwYf07x57bx5wR/MSL2ZeSkTd7K0RXCn0suRvy5xZ/gb5BMKP4khIg/J/gbJOQ5/vwa/vzJ+BN5meFPpGUVf5LbLfy5HH8+xZ+b8CeRp/iLUsD48yn+slqm258Mf3svMVHxV/F3d/jDZjbHXydbxJ94IvyltiYsL76MvzHD' \
			b'n89+UxSEP541Fh19l+DPs7eIv1HwN6b4GwV/o+BPAyvizx+Mv66wSSQxgXvgLy8Dxp9X/Plt/HnBX4yIfRkJg0tY8ecFf+nFiL/ln+BvlEwo/iSEiD8v+NOKneNvbYaZP3qGWcSfyMsMfyItq/iT3G7hz+f4SyaX0TXFn0Se4i9KAeMvmV42q2Uu2yfCnzXV' \
			b'frLaT94f10Lj57PJ2M1Ps8nUU2Y/KY6r9pMxtHRjnPFsssxdjVPE1y77yemmgkHKwTPIisnMk7xukJLnULJgeJ8bpPAMsvwG48WnWKPw9LEYnJiilNNmJBa1Q5leyPmFWWN+bdaYP3nWmCZuhiKp6TXzE/Y2Nz/JZ435ZNaYn2aNacQphpKK0b2YnyRXuNQv' \
			b'bD9pr2ONjoqeip6Loqdv/HzWGLv5adaYesrRw47r6OkLG6OHZ41l7ooe8bUTPfGmAnoOnjVWTGae5HX05DmULBje5+jhWWP5DcaLT0EPzxqLwQl6ymkzEouiZ3oZ5hdmjfm1WWP+5FljmrgZeqSm19DD3uboyWeN+WTWmJ9mjWnEKXqSipG8KXqSK1zql0bP' \
			b'dayvUdFT0XNJ9KBQzm3yO90UPeopQ484rqKnawsboadjk/zMXdCjvnahZ7ppGz3dweaKxWTmSV5FzyyHkgXD+ww9HVsp5jcYLz4ZPR0bJ8bgGD0LaTMSi6Cnm0zvu7aMnm7N6L472eheE5ejR2t6BT3ibYaeLjc97BKj+26yPNSIE/SkFSN5E/SkV7jUL42e' \
			b'ulZGRc8dosc33dyOgt26yY4CRaXzW+xhP+vs8YWN2cP2E5m7skd87WRPvKnAnoPfFhWTmSd5nT15DiULhvc5e/glUX6Dkb2yh98NxeCEPeW0GYlF2eMn9vgF9qzZPnQn2z5o4mbskZpeYw97m7Mnf/PTJYYP3fTiRyNO2ZNUjORN2ZNc4VK/NHvqYhmVPXfI' \
			b'nq7p5kYM7NZNRgzqKUcPO66jpytsjB62XcjcFT3iayd64k0F9HQHo6eUzDzJ6+jJcyhZMLzP0dMxerIbjBefgp6O0aPBCXrKaTMSi6Knm9DTLaBnze6gO9nuQBM3Q4/U9Bp62NscPV2OnsTogDIk6JGIU/QkFSN5U/QkV7jUL42evRfLqOip6Hk+6AkoizP0' \
			b'BNkiesRTjh52XEdPKGyMHrYzyNwVPeJrJ3qitwJ6DrYzKCYzT/I6evIcShYM73P0sJ1BfoPx4lPQw3YGMThBTzltRmJR9Ex2Bt2CnUG3ZmfQnWxnoImboUdqeg097G2OntzOoEvsDLrJzkAjTtGTVIzuBT3JFS71S6Nn7+UtKnoqep4Pevqmm9sZsFs32Rmo' \
			b'pxw97LiOnr6wMXrYziBzV/SIr53oiTcV0HOwnUExmXmS19GT51CyYHifo4ftDPIbjBefgh62M4jBCXrKaTMSi6JnsjPoFuwMujU7g+5kOwNN3Aw9UtNr6GFvc/TkdgZdYmfQTXYGGnGKnqRiJG+KnuQKl/ql0bP30hIVPRU9zwY9KHlzO4Ogm6JHPWXoEcdV' \
			b'9IS2sBF6AtsZZO6CHvW1Cz3TTdvoCQfbGRSTmSd5FT2zHEoWDO8z9AS2M8hvMF58MnoC2xnE4Bg9C2kzEougJ0x2BmHBziCs2RmEk+0MNHE5erSmV9Aj3mboCbmdQUjsDMJkZ6ARJ+hJK0byJuhJr3CpXxo9ey/rUNFzBHrONZG1IuiREOSbMLc3YLcw2Ruo' \
			b'pxxB7LiOIF/YGEFsbpC5K4LE104ExZsKCDrY3KCYzDzJ6wjKcyhZMLzPEcTmBvkNZjpUCrHFQRqogKicQiNxKYgmo4OwYHQQ1owOwslGBzFPOYikvtdAxN7mIMqNDkJidBAmowONOAVRUpKSNwVRcoUL/tIg2nuBhQqiCqLnB6KAa3rMQBRkiyASTzmI2HEd' \
			b'RKGwMYj4DVDmriASXztBFL0VQHTwG6BiMvMkr4Moz6FkwfA+BxG/AcpvMD4eKoj4JVAaqIConEIjcSmIpvdAYeE9UFh7DxROfg8U85SDSOp7DUTsbQ6i/D1QSN4Dhek9kEacgigpSd0LiJIrXPAXBpGrSx1UEN0xiPomzN8HsVuY3geppxxE7LgOor6wMYj4' \
			b'fVDmriASXztBFG8qgOjg90HFZOZJXgdRnkPJguF9DiJ+H5TfYHw8VBDxK6E0UAFROYVG4lIQTW+FwsJbobD2Viic/FYo5ikHkdT3GojY2xxE+VuhkLwVCtNbIY04BVFSkpI3BVFyhQv+0iC61MIH7l5Z9FxeDLU3wiE4h3KwUA4HMsmgPM6YZGSLTBJPOZOM' \
			b'KL9VKrFkTL8pfCKTITK10VWuKZ3E5y46oSYQfwU8mYPxZFa2PfA0zzMhygiizBaiDC8kx4Uz3YMLyaUf1W3lq7pJqMyorFiTdBpNL0MK5TBSylCZb1PKrFHKnEIpitO5mMIZqaTuV0hF+UBBm7NK8qSsMhOrWvnAbpuUTgordbUkzhCEYMsk2ErkdmS5Umyt' \
			b'4WofToFie8B+AyiEBySu8AoVwAMglrh1Hasm5OukPjd0PeYKqfVR6kyPUiMuzzvD1ihbxJZ4yrHFjuuPUmNhY2CN/CiVuiusxJfAKvBSqGEsPFDFWwvEGg8mVimxecLXH6jyfEpGDO9zWo38QJXdYHw81AeqkR+okkDlgaqcQmOmxMozVUKrceGZalyj1Xjy' \
			b'M5VmKyeVVPzaMxV7m3NqzJ+pxuSZapyeqSTiFFNJYUreFE7JFd5f+pnqOpZVqGyqbHpaNuGK8XPbu143ZZN6ytgkjqts6tvCRmzq2fYucxc2qS9hEx5DEdBuxqbp1m029Qdb4BUTmyd8lU2zfEpGDO8zNvVsgZffYHw8FDb1bISXBspsWkihMVNimU39ZIrX' \
			b'L5ji9WumeP3JpngxWxmbtOJX2CTeZmzqc1O8PjHF6ydTPI04YVNamJI3YVN6hcv+0my6jmUXKpsqm56YTRZlbsYmK1tkk3jK2cSO62wqbcwmy2xK3ZVN4kvZZJlNtsCmeGuBTfZgNi2kN0n4OpvyfEpGDO9zNllmU3aD8fFQ2WSZTUmgwqZyCo2ZEitsshOb' \
			b'7AKb7Bqb7Mls0mzlbJKKX2MTe5uzyeZssgmb7MQmiThlU1KYkjdlU3KFy/7SbLqOdRnqt4/O/+2jSqkjKeVR4maU8rJFSomnnFLsuE4pX9iYUmw6nrkrpcSXUsozpfxEKbrZ0A6VSQygwKqDzciLSc6Tv86qPLeSHU7wjFVsRp7fYKZDZRWbkaeBCqvKKTRm' \
			b'Sqywik8VVwvG5P2aMXl/sjF5zFmOK5GANVxJLma4yo3J+8SYvJ+MyTXiFFdJeUreFFfJFS7+S+PqOtZyqLiquLoaXHUN6ZEMV51sEVfiKccVO67jqitsjKuOcZW6K67El+KqY1wl9hN0s6EdKpMYQAFX3cG4KiU5T/46rvLcSnY4wTNcdYyr7Abj46HiqmNc' \
			b'JYEKrsopNGZKrOCKTxVX3QKuujVcdSfjSnOW40okYA1XkosZrrocV12Cq27ClUSc4iopT8mb4iq5wsV/aVxdx/oPFVcVV1eDqwGlbIarQbaIK/GU44od13E1FDbG1cC4St0VV+JLcTUwroYEVwPjamBcxQAKuBoOxtXatg+u8txKdjjBM1wNjKvsBuPjoeJq' \
			b'YFwlgQquyik0Zkqs4IpPFVfDAq6GNVwNJ+NKc5bjSiRgDVeSixmuhhxXmnAON+JKIk5xlZSn5E1xlVzh4r80rq5jzYiKq4qrq8HViCI2w9UoW8SVeMpxxY7ruBoLG+OKTf0yd8WV+FJcsalfn5j60c2GdjYNoICrgw3+iknOk7+Oqzy3kh1O8AxXbPCX32B8' \
			b'PFRcscFfGqjgqpxCY6bECq74VHG1YPPXr9n89Sfb/MWc5bgSCVjDleRihqvc5q9PbP76yeZPI05xlZSn5E1xlVzh/aVxVVeWOAeiOsZSxJEX9FzrBKnnihoUkvlkKHYbpslQ6ilDjTiuoqakh6cYUEIGng4VHYdpKpT62jUVarppGzPDwTOh0lQUtz0wU3az' \
			b'khUJJcPNwLOh6IJJXjZtyGrPF5NhNDkMElK0TBHKdYEiw9o8p+HgeU4JQDRdOUC0PlcAIt5mAKGMTAAZkslNmFwliMacECSVMMmXECS9MnIMc4IIIUT7o9b317GMQ31IqQ8pV0MO2wxzuzp2Gya7OvWUk4MdV8kxlDYmBtvVZe5KDPElxBjYrm5I7OroZkM7' \
			b'VAAxgAI9DrauKyY5T/4qPWa5lexwgmfUYOu6/Abj46FAZGDrujRQfkhZSKExU2KFLXyqeFkwsBvWDOyGkw3sYs5yxogErDFGcjFjTG5gNyQGdsNkYKcRp4hJylPypohJrnDxX/ghxV9qsYf6kFIfUi6AGmhSbo4aJ1tEjXjKUcOOxz2kxBgIOY6R4xJ3RY74' \
			b'2vmQEm8qYMYdjBm3sp3ykOIEN24LN45x45YeUgrJMBKQgsRNFHELFHFrFHGnPKRIumYAkfpcA4hkYAYQlwPELTykSMwpQRIJk3wpQZIrI8ewx0PKdSyVULV+1fpn0frQbZ/bmLHbMNmYqadc67PjcVo/xkBan23NouMw2Zqpr51aP95U0PoH25elqShup2h9' \
			b'sTMbtuzMBrYzG7olrV9IhpGAVOtP5mPDgvnYsGY+NhxsPpZqfUnXTOtLfa5pffY21/q55diQWI5lWl9iTrV+ImGSL9X6yZWRY9hD61/HIgS3rvWf+6puz40OKCh+Rgd2Q2ehg3rK6CCOq3SIoaUbUYFimLkLFdTXLipMN21TAV0Po0IxmXmSV6kwy6FkwfA+' \
			b'owG6hPkNRvZCBjzu2yk4HmxaSJuRWAQVeCyooKIooIIKbhcqOLxThpk0cTkvtKZXeCHeZryg3Ey8oOCFF5QhxoVGnOAirRjJm+AivcKlfulhJlpjALjQQEgNJJUg1CqH/BaKTEIjnwDJJEzyOZbMTjKZJ111dDgeUeYJMAXXsYofCVctlEg7Yj1jRUNNQ5lY' \
			b'KJMcY30BZSAMICuMtHDji5WGM+ENFRuqMEjwBlUjQgINbORd/TAk2NugaGGDoE3Zt0EhFCcG4JBAkFyNflUgstCFJR62zeIjE6U18A8ld4Mi7dnsGYLtprT5yfZZU7a2yKn42yalP9jgWYJCEGLG3JglbErhPk9Rplu4YCVbhvcZPD3bQOeRgQj4xADaswG0' \
			b'XhV4ooxCgaDMlxJsJDaBqJ/sn/2C/bNP7Z/xhRgmEa2paEVryuEwx2vbR8R6tY52lHEjrEV9djhwW/p2lYu5yamrYrNCXcrQtgmazy2mY4Zmj2kadTt7VkvKWHMt8E2vcK1F+PYPcAoExuuW/jv67+l/R//Jjx/wf09Xx0D/yR1xTDvLO8c7uh8xjLuA4RCE' \
			b'O9AWOxAcyZsw9zDgMmcZsgzWJaSmMF0lKQH0OEr2Mzq68pAdEU1ppiQrUexYgh1Drzm5ZsRaI1WRUimhSnSaUYlIpBQK6UNVOIA4GWgKiDkbXyaoRKIoRdb5USDHgdhQWJzKhU27vQr2Rj8RtDWsRko9anRV50VdfooiP0mLzxX4XHWvKu2Sxk7VdVFXb2tp' \
			b'Us5RM5NCVm2MCjLsVpDdZXVkd6Ca1EcNWhn90bWlL2hMeydaM9WYs748lEXenwc/UGkWysVCzdlhyLSqHQdaVd1BWTgoCwdtiDVtn/bz4deC1j2so0/d7NtQvZjS09Vv0l+3Zq/hrLOrYZ98fk1VMcrQnaljbA6ZJqZySbUx+QjT8yA/+GIy8AlZWkiurqdn' \
			b'YMwiSYDORty09KwwzaHHkx562NBeH7AAqf/b71bv4Yq7wJNux3Gj7kZ6w+4RxnQeW7/7I3vEz1Y3n1UvU1M3e76Avs4uMnYBduhlf/26eTytlzzsVqP9TajRcCMq9Ja6xlVtPpbatJylW1WZt9qNPUlNjnuOtrbXrCavZdz1lLeH16gqjx13PVBdZqqSeyb3' \
			b'oS5Pfzn3eOqSBjueq8q0tBjRkWoTn9fdA6QDH9ch4P0UqD2rAt1hB3KcDqV0n0uHLpickx61T9TlHJ5/t/Na9Kh/Al1KJfFIutTv1Ke2NJp60S4oCtfT69RTuqEgC4/80j88WjfUp1r0EXuhXXvEA3v3THqil9aej6k5/W7teRHNGfLxzov2Qq0VG6/DtCYK' \
			b'wvPriZ6kNe31mEr5ozuel35wb+sY502py+t6ZX8ND+xY73WMc3816a5HTR5tLXVxNXkPVlJVTT5vNemqmjxATfrmzTWoyFs3ur9VpTicyeg+UYyk0m5ZL96Rsf2z0IOWvokkuvBkY/vmX+MDsJ1e83RVOZbGJMEtoFFqd0eKMu09osi1pynJ2+893qiWpBnW' \
			b'lGzWWfepMtOuo5TGCX3IUNVkSU1CeLgsBST2dtRlYfmBc6jMgLbJ44GqM51ylE81qmr06dUoJpTWptjg4hu3qU7D42jUDeYPbxsOU6yObMPixKF0uhCq2f5SatY/gqY9ejGZPbUtpPUimtaMj9c5pYVeagd1p2ZFW7KnUa+9vbiOJXXQXk7DWgr0sTutuFDT' \
			b'efTswRp2q+s6XEqndjfWe011aQg30HOtuvSGdOllx0UzFYpScXMd1WtWoeOlVGi4ZRXaVxVaVeizUaG2qtAzqlAoqwup0P6WVehQVWhVoc9GhbqqQs+pQtv6Duqe7ZhOM+68eh15B+rxJF1o6RsYN/4i/th56Qa/e9DSxwwgtqoGC6/iu+l1/NWrxIWvAJz1' \
			b'NXxVkbenIlE6NtjoT1WWl+84Pvqr9mN7je761OU+3295ZI057Og8uifWluFC6yivGMLj2smju06NSR/TSX7n1pYUZqoxyeGcCrOQg0VlyddTXanfGymrSU79tajK4jdEzq8p97OKt9iSubiXu5trX+MawgMRdJ/PcYHwPiDsqOt6hTORqi6uuvhEXQzRpr+z' \
			b'62I8y3SxP3PntZCDZV1M1w/QxZT6qouLuthqcT+BLu6aN9OneFn7OtW7+3x4dyRde74xgsM/lfs4A6Tlz9na5vCPnF9CT+7zZM/tMirCqAOzr83OtN4hnyJnhYea4pIP6Md/Q/zxhy1z5ZUprmM+C34xBbX3Q3WoyuNOlMcm+3L17SiPlr5WXJXHlSmP5l9D' \
			b'/wCKnbogfdUiVYtcqxbBirl0D4TirDpkXYfoQ0/6QDNUbVK1ydVqk/HyzzMUZ9Umx2mT8cLaZI9x6MdRKMePPp+mWMITK5edo8lnVDBc2tPvPMqFQsoHhduTFUwhqcvKha4fMg7cXkDLZOO7T6NqpOAuP6IL5VA7QLUDdJkOUIsttw7oPpMeUCAt0pIWaasW' \
			b'qVrk/FpEpsXU90JnVCNYpvq7BjXSjQ8IC5Bw7MGglD+glgNJx94KaRdbtUvVLo+gXbCFVO1yXu0C7vq7Ee3izqJdzjr15XkpmEuaAKZKxpDhKhpMXYHCIf/3Y+rCxXMBpUMRnevpiAJbUjySpUnxWFSuWOK7VRA0sAfUwSC8D7wsuXsAJUa6x1fd8zx1z9Pr' \
			b'G7zzjvRNuFAnh827z6VvqACX9A1nac+Ozi4tcwar3UeY33sbiuYaFi+4amVDTk8y2/aGH6soSdexwMCJVr39wVa9l1o/4Pr1yzUtkPLEOoYE/1qn9d+mouEivbLlTE7VNntZ/z7RgiXXr3CubVWmCyodViG3tqDIjWoeLmvz/NTPLnPhK1gyqWqgq9JALEu3' \
			b'v6zRbWqh613T7VQtVDAzvr7l265p/crbW6/yvHqJ2vozXnft2pekpKzc6gqUJ2qrIbMwvuL1JqvCenqFxbpBO1PPfLXIa9daj7mmzvWrrbaqraq29lZbtqqtqrauQW3Z5g024pkisF1PQrsgUrb3dLODmz1OKwXpwjWgcAyDf3TZzy8PMhV0oMtd88aiBcJg' \
			b'v8Qj1JBwHxy/2IAypUWl0N8Gkgj6q0NPoDUCuTl0Qw2GiqYhVdCAdEHkEAFIH4gClD2IORQq1g+9RO1xMUPUKvgFFGjBMXK4DsJEq9RBo0N5wKaKrYomV+L0OKjRFvy3A6YB9DboKdRNg9yJC2JD2x/whyFT4W78WVMJVNj3j2LvMPZ+3/hB8kARYPNZT0mH' \
			b'a1V2i38tBjQOtGLk7BolLOxOGBQ7SBt+6TLgl4Z2pLPltOI3gefpjcuf45dz0LzFz/IQmu2/lsxouuw394NLYIbsCt5laYZEx1/XgXZBVyiz/ZNnFnDU4TehIdPQGzjbH31UveUmOpyeyXE8PJ+h3ZFX6Pbs/Yfrmy794TqhyTnldyzm1yLt8z7cUgkYKgQn' \
			b'5QAqcrEorBRHz0Wy1TsL9PoEyYOMpCJzOGe351WPaRo3rr6JcmrIkAQ7DwhVes2Fckv29zzdsh12FLcfpYfUcdGTvM+KH6jDVQBdXdCMzmh1oELd3qhzWfgVPZt4bfKy6Dn3uRRPEt+al5XbduetkNJCtIaEC1yvrzXRU8NTbVwsbbnRYTe9wZUeqPWB3EO3' \
			b'+Lg2CF2QfZshPuEtNkVz5uZoHqtJ2qawpc+H4jjyU1/R++qGz3prnuyCa3dgXOnNWKzH3kwbS52tqv5guXLNvW4sM+4aFbhvnm7jYvFnb0pDeJzWNFxbixqaM284Cnctoey1sQiVn2mrNt4lO/h4c58by8wZhhuKgnGqRsZB7LNt9oh7uHjKAxS1Se1oUvjM' \
			b'cacby0x5vAdk5vRW1Z+jZflme8OXW8UL+274cuqwe7iwFgaL4hPrIY+rwTchNCDo/YWanMmbHY7u72x6bmp+/cBNkNY57h+rKfbN9oaP53KEbwNLXm5j6/A3nBgMv0QpDypVNb9LtvCt7n1uLDMLI27XoubRnOLpNy6q8wwT3aJ6f5Smh1w8eWNTlOl3lkDn' \
			b'EZRPyr7OkgiWt/IQk8jb+VV4KkfdeVXy/jJhm+KGtg1L18QHZHW3j3Nte8bEdXj+8bBnj2Q0nLvTjWVmcQDsbEhGWTgNy755pA3tAQ+5gYusPP5Tm9muZjY297qxzCwOip21mZEsnNLU0Gr40Ta0vD3kBi65xaGh2tqWWhvcfK8by8yiOdX5W5s9scWhSf5j' \
			b'bmjmfsgNbA1bB3cObnQ4seJON5aZ4wd3TnxwxKrdVa1LD4ZTG3TNcRvORTnoBpxIQvNAQuliX76Li7faDR3eJIfmXjeWmcVBncdukml1n948x+ZiWzrD68B7uchvaAzm0LHax26uOB3x+jacE5ichEeNjWXo8DEZ8ygtN635Y1rwck275qAN54Eeek9x00ma' \
			b'B9wBZQi7ZPYlnHI1nWcciF/RXGWDd5do9F1z+sZJDWcI6YgNJ/ueKSyWq8PHim6t+Q/NbW5cP+cZkaqvZkUacNmBM22U0H48W3jHbTjj/+RQWNQOH8h6fFWwFw4OVQnYAp50Q/k97EK+8fzs84ybVdWgUhGauuUby9niWFuVs6PkrG/qlm8sZzsHHZ+nVRAu' \
			b'ePQcNq7AOzTrwrWqnsPGFXhD44nXMuyPK5UtbDwTc/rt8Hrothi0nMyvnyUZqzezENVZjocLUd/c68YyU63cDpeZobnXjWWmTv08XGbG5l43lplq33ewzODyq3e6sczU5dIOl5m2udeNF6+sJo2Hy4xt7nVjmTnPMOt9yYxr7nVjmcEFkBPR2KpJqr3lmoPS' \
			b'phXP0BXu0oXQZ+fbC5e7fNHygUnZuTw1vMTVdppwcB1tXWhZZUyhpgplidZcGJpt94FkBGSA49panjlQqLDn613zpmvxQseGDtBG1EF89OiAAkmOkA155d5BJzFtV9BE0EeALASIJIBLwOWBuUsJcl/0DUnJf7x4sNnyjU2B7oAMz35W3swGXJ4fV2r3I60P' \
			b'gmsqsNKARGXLUAc44lxApHCOebPSkYEA4bijqeeMqdBNLhDely//P44Hrc0='

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

	def expr_mul_exp_1     (self, expr_mul_exp, CDOT, expr_neg):                       return _expr_mul_exp (self, expr_mul_exp, expr_neg)
	def expr_mul_exp_2     (self, expr_mul_exp, STAR, expr_neg):                       return _expr_mul_exp (self, expr_mul_exp, expr_neg)
	def expr_mul_exp_3     (self, expr_neg):                                           return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                    return _expr_neg (expr_neg)
	def expr_neg_2         (self, expr_div):                                           return expr_div

	def expr_div_1         (self, expr_div, DIVIDE, expr_divm):                        return PopConfs (_expr_diff (_expr_div (expr_div, expr_divm))) # d / dx *imp* y
	def expr_div_2         (self, expr_mul_imp):                                       return PopConfs (_expr_diff (expr_mul_imp)) # \frac{d}{dx} *imp* y
	def expr_divm_1        (self, MINUS, expr_divm):                                   return PopConfs (_expr_neg (expr_divm))
	def expr_divm_2        (self, expr_mul_imp):                                       return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                            return _expr_mul_imp (self, expr_mul_imp, expr_intg)
	def expr_mul_imp_2     (self, expr_intg):                                          return expr_intg

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add):               return _expr_intg (expr_add, (expr_sub, expr_super))
	def expr_intg_2        (self, INTG, expr_super, expr_add):                         return _expr_intg (expr_add, (AST.Zero, expr_super))
	def expr_intg_3        (self, INTG, expr_add):                                     return _expr_intg (expr_add)
	def expr_intg_4        (self, expr_lim):                                           return expr_lim

	def expr_lim_1         (self, LIM, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                          return AST ('-lim', expr_neg, expr_var, expr)
	def expr_lim_2         (self, LIM, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):  return AST ('-lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3         (self, LIM, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg): return AST ('-lim', expr_neg, expr_var, expr, '-')
	def expr_lim_4         (self, expr_sum):                                                                   return expr_sum

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

	def expr_varfunc_1     (self, expr_var_or_sub, expr_intg):                         return _expr_varfunc (self, expr_var_or_sub, expr_intg)
	def expr_varfunc_2     (self, expr_sym):                                           return expr_sym

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

	def expr_term_1        (self, expr_num):                                           return expr_num
	def expr_term_2        (self, expr_var_or_sub):                                    return expr_var_or_sub
	def expr_term_3        (self, STR):                                                return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1].replace ('\\}', '}')))
	def expr_term_4        (self, EMPTYSET):                                           return AST.SetEmpty

	def expr_var_or_sub_1  (self, expr_var):                                           return expr_var
	def expr_var_or_sub_2  (self, SUB):                                                return AST ('@', '_') # special cased for last expression variable
	def expr_var_or_sub_3  (self, SLASHSUB):                                           return AST ('@', '_') # special cased for last expression variable

	def expr_num           (self, NUM):                                                return _expr_num (NUM)

	def expr_var_1         (self, VAR):                                                return _expr_var (VAR)
	def expr_var_2         (self, SQRT):                                               return AST ('@', 'sqrt')
	def expr_var_3         (self, LN):                                                 return AST ('@', 'ln')
	def expr_var_4         (self, LOG):                                                return AST ('@', 'log')
	def expr_var_5         (self, FUNC):                                               return AST ('@', _FUNC_name (FUNC))

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

def set_sp_user_vars (user_vars):
	global _SP_USER_VARS
	_SP_USER_VARS = user_vars

def set_sp_user_funcs (user_funcs):
	global _SP_USER_FUNCS
	_SP_USER_FUNCS = user_funcs

class sparser: # for single script
	RESERVED_WORDS    = RESERVED_WORDS
	RESERVED_FUNCS    = RESERVED_FUNCS
	RESERVED_ALL      = RESERVED_ALL
	set_sp_user_vars  = set_sp_user_vars
	set_sp_user_funcs = set_sp_user_funcs
	Parser            = Parser

# AUTO_REMOVE_IN_SINGLE_SCRIPT_BLOCK_START
if __name__ == '__main__': # DEBUG!
	p = Parser ()

	# p.set_quick (True)

	set_sp_user_funcs ({'Gamma'})
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

	a = p.parse (r"?sin(x)")
	print (a)

