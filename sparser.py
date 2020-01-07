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

_SP_USER_VARS  = {} # flattened user vars {name: ast, ...}
_SP_USER_FUNCS = set () # set of user funcs present {name, ...} - including hidden Gamma and the like

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
			b'eJztnXmP5DaW4L/MAl0FKACJkigp/ysfPWtMle3x0TuNgmGUy9UDY33BZXt60Njvvu/kFQwproxQZBCpSEkURZHvke9HUiT17PVfvvzws5efffqX6i//693P38NOTz/8+ouXf38JBy+//fzFFx9/iofu4OW3H3zx4sN/x0N38PVfv/70w8//rkew//Szr+D/' \
			b'l19/gP9fvvjyf8vh31+RN9jD/7+9+IIC/Ig9ozc+/ODjf/v2wxdffvylHL96oa4f+MO/+cPP+ZBCcJH6KxzIrpG9gf2rTz79msL95NPPXum+0QNDEaKAnBSSs//4Ap/1EgX18rN/w5A5yV9+han5+NXnX/39y4/RyyeffoWXP/0aH/Pyk1ckkFcsQko5///w' \
			b's1evXqjU0eELlvoXKnV2o3R9oVIXtxe89zH8IoovReg/4N+LV5/D/48+eEnX0PXTj0SqePSBP/ybPxSpfvzyy4/FRXWCAX3FkYcIoqdXLz7/8qvPMMZffPKKvP/nhyitF1995byhkD/65G+ffITXPxSlczCfvySdgNxUPf/55ccfkoePPvnrXzFjffoJ501K' \
			b'yYtPP0IB44XP8H569P/hPIa7hjMfhP7hv8Ph+z++e//nm9/e/xkcv4fjt29+e/f7t7/89u333/34/vc3vwWX4fDdP3+FKz/8+ZMewzV/+Ou73/Tk53f/9e2b3/4LTn968/u3b3/5UY5+++W//RE/7/279+/fuqNf3ZEG9eY7d/jD9/90rr//7h72jzdvf9fj' \
			b'X+kB7PzHz299nP/xj1+jk29/ePveR90l6Mcf3OHP3vX3d7+545/++PHbH35ygb3947cf/ycQjR5+98PPv/wUiMPF6rc3b8Og4EBP/3znrrz5/nvn6Y1L3D/fv/MpJSm5FGCaAqW4C3/8/MMvP7sL/+Ni9MPPv7sogXJR44Eu3/r0wcVQkH++8Tr+xcXlj9DL' \
			b'm5+/j9xDSX/39peffnrjTn9xgX0HYvm/77waY3+//vDu7Tt3Aln0Zy+dX9///ot7tMs2LiW//OjTT4FGJ++DO7/98c83P3qJ8p3fVK+fbWxb2fZ5xQcdHvQG/7VVb5/LKZzRUYfeqr6vNnJJHfis1fvghk6d8JB8bQZyaapnHbiCt+a5c+jQoevUYTPhQdvw' \
			b'vwG9t89DJzNsOQ1d6ISHcNRY/jdM1aYZn4sTHsLRAL+xgjRs+MqAB7CH9NLN3YT/usqOcAdH1jvp6aavKVSQhKVETM/1fKBU1hwliIiBcFr6eacpPG1rOUA3DARi0nTuqKfIjdWzBgIBrVjzXFw2fKdp+N8ALoZ1Amd4iGIlJaAunwenehy4G96BijGF9Ot6' \
			b'vdzhAUZS3Dnq1aYTRz6HOJIOqt54B5KO9eeGPLSJg/ex6ShRXc//LF/AqHQctU5OVTcQt44jN/C/oYZU8MUWlUG5yoKQMPvIBdvohW4U3Q7P5RT0S/fCgwzmLlSMRA+d+vDUWDlAN7wdtNti7pecoqdT6iS5JHbutk+TG/vt020fNgnWbp9GN206LqO1iLOR' \
			b'EonBNJSdQMXtJAFj3mUhqnPGyZ9uOspZHViXrqngvJmqEXRuK3xyK/lr+yoapqHdwxNoNfa06agco16nyro8jMWZS1qNhbbBiPdVP2jZRWfn6FxMzS6jd2nYxd9lDLnYWl02LaW5bfnf0LjoOScTOuEhHk38D8T2/Lk/xKOec6/egnmQdYZ2wasbT9GfPwWF' \
			b'kiURf2oN0VSQakGgXOCalv+NENmG83fT0iHJEYubHFDamgbLNhvwQYsvOoqTO+/pXB5byzOwhFZYBjPu6gIOFMFBcqUIHM6hkJIf+oFHtjZo8ijPDfxvgExh+B4UiWEzAE8aUeCcxeF0JPkYKBiNZT5VDWUyazRZdHFgVuUugi2mmIEEIftx/uxZDlLWNHO2' \
			b'qg9wfGa9naDTzkULTi1FF+zPM9KCFCc87Sj8LafUh54ySdCQsa3qUGBGj7pGjhiceNDpQa8Heh9nOTxg+YOgPSPxbIqipi7ubGM4p/VyqlfQmFPQpud/A/rlLITm1tBFCFlYaCh9fMTZEg9Y+bV4kCKExdcwpcB6mDZksyF5o6eJ/w29N1xsw1AXA/8Lqj+D' \
			b'ULK3/I9qPhxdOcSjXi8+l1M40wuc+SBGY0+5qdPcZLUWYqmO1evtmDkspd72egGrVuICR1Cre12DFPAHNaUG8ypgEnIg5EnIeIBCoCuYFNAfFPoJDSB4HodqHEGKcFuDOb+HHxhHUE/ToHRb+HUVYB3E1dTgs4bboLYAfqAu0kBND72Ce4c/VBGEhGWohpBq' \
			b'8AVFrIGSDiarxXvAM1ilBnJ4A3xrwLlBd4hdA9FrWgwB3EFIDaSwwedA6W2gttOQkiEhsIEPi7++GqdqqqsJEmSqqa0mDBMiUmFC8OlwD5Szqa8mW00DVJ4qqvAiF5oaolZTrRKCB42D5UaFDWTRRuACAhrSMo3VBPECwTUguQbk2XT4ECxcEAyIuIE7oLIJ' \
			b'9gvM54iSArGCPesqUPCIacD01mgVEB0GKkBQs4E6B9Yy7YRVFoAEQAGIBzVayIgDKgEVA6agRlMJqYfEQzmGwjGgHtASNQYr83AI+YBUD9ngGeofHXj3GqvZeIpRfU4WinxhCvAqSh6cUfjPia949TVCnM4p7JJ3nmjeeTZxJmhY25KDXj8bB8lSnFdGzhyk' \
			b'adpLziKVk4OVvdyHyqaAKCNgPqIQikm6j2yFem+Lwu9L4V1R+P0oHDt6qNpghAQ1E4QAgPnBMBnGqeSK+8kVoHZb9H1P+iZNYLnvifeB4r6hDms2Dlz7iy6iq5iMnmqVJPP49l5qk71WN2syKqpf1avoTHSk2gl14XSgcmdZs3BD4V1GcEGeT/N5kr/TnC05' \
			b'er+8HOdhzruZPCv5NMyeYbZMMuRSVoTsR8qtuUWAEeOGgJW2A7coi9DPLvRnk5QnK8WllUYZFhDqF+ilGddrq6/tcuWylUad3i89BA13EWTKaavh9XKnMfpEK1cKF+6MC2YoCr8rhTdF3/ej72ckHLbsrVCn055jcsB3gxCfqq9s0fvT0TvXGLA6p5UEqdVJ' \
			b'zULywMRVenhUA89qBpQMhANPbyxKaih54snkCdB2U7R9R9o2Rdt3pO22aPtetP1scnQnnE/M+MlqH07NWC+daBfqRLOmNKruqPhhAqnADVwMWf2n5KNQSzUeW3gMV91fP+OnnT94NSI1vyLs1XxIl9A5ntHW/AxuhZ4lSCOdmPLSYRpLN/UjmbWudA3ekVUD' \
			b'ffN7CX7NV9R+H2p/xi9tn1Hc+CUwvym2XLe0bGYtv1OqMXIQ+RoFBTegWkGixbweU2vkkb3PLBe7oS4SPruEubtz4Cw+cMYe2jlBNzgVAwRQBH6UwLklOojc+5Klzzt0gM7IWkvTY2DjMfKgjZE7eCULR9m6jLK5ntZGI6PtRWkjG/6RS8nYy+B9Ua02cJpW' \
			b'RuLw8KxnMjDHcGDyOm+gIENNk8ywMPYcvIz14PFf8YCQXsKQB8vkAh6WglNq6aK+Pyy1wjuqFb6mWUrmeZmfdk86h4gYnnlmylyyJ6xnEJ7hqYRFz09Xzzg11MikQdgXhd66Qmm6ZymxT1nBqDUjE3VhX1T7hFRbE25FEWVqzMob7TwlnstiW5q+91NScQkE' \
			b'VTvvO6lGEXxLyV17ycUpzaSwkeq9ZYzzPRVeY7nQ9mq7peuVCzVPZjVb81/7mn3XknNy7z71xWh5nXFGxkbvPvWNaJHwGSWce/epL0bLO9DHEHj47lPfiJYsfcZ3oEamTZOxLjWwNarI1oLbnirPRTlrUk6rDZpWOpv4fUC6WIAVX4aqUkV1a1CdVm/NINVb' \
			b'0ZHlYlZ0cz3dtC3rgmtYUgmQkR0yYp1bEzpJh/wXNV1+jFqR+1Xk3he5X8EsTVoT0za2NAipD0xWfJrExcpqQNLvMTXcf8ZdKZPYt4mr3UV9lyk2ky3ivmAFq5aeQGukJ5D2555797qss3xf3dKymp6bXKNzP3SGgg6ct2Jkeyr1oAVQQintj2ZcuRl1nmmp' \
			b'/NZw4l03sB75bcMzer/wDc2pYqsirxJ9p2BR3zFvD1jYZc3Ce7KlOJJm60VcKT5Hrf269bqtyPEoOXYnTdRpeI32oodT9cCL3J8r0CzmG141EV9cE8mHupD89GbXIP3YgynSPMcr6LaI8Rz2hKdAPq49ke9vDPJObuiL6s5RAniUl6ctzZ6oy0uyaytmbOSV' \
			b'c3Y52pGH3I48D3GUAR5cSTKTO6OaluGaFpUafkWNVa2t99iDtMS5nJVG4n00Ep/xuJNnOgxUenVBty1PcMUdav85fUsYdyOd8RScVqbgtM915kYbfjMJc0HrhojzkHE9b2XIuNyAO9NzyCM/aJLOIGP1gRTJkjXvJGui2FsZwNYG3/3g0VJt9F2OVrIOurTB' \
			b'6u00EqSVkSCc5cSjlSByBhbHKPCTqTiQZSzrvj+lzIWDTAiMZfbg01KrkGVrpd8u79xnnBE8rQ4FMDIEgEb2oRDLLJgnlV1ssQBPSqU4GKflwTgtD8aRAt5yAW9l0ALuZddL/ZK/JlbeJT9yy5Y/1lbWI368aZ1c0+1kx42pnlt0VhpvlhtiNEyahvNo+0/m' \
			b'8rba/cDuA989cIEZpPVmuO04SN17oCeVbqOrdhvVu1s11G3UcrdRy91GLTeROIto00lrP3BbV5bDuX0kcs9J5/pdvuEulu651HS/qXxHDYizk9ZyRy1fsh3aZJbeGz/+lXnay5xhuN491/6a0jV/etd8N1uUOy7KHRflrtRin1SRNaT+0tl5Hwon2vayEAPu' \
			b'QSR62ukHh3tcnQN11ZV8cSf5gj88XBR/d4rHylQva2D3DPqeQY+ZoTJSbycbISspoFgtnUuVAURgJQhbpsZcrg3WkRpAkpZqyTy6UVYHh4BtMuCCFDdwhzO/mMc1MVCgOBYSZVfK9NMo0yigAbNGy7uOd71oHx49lHJ6sSlsQ6uveXqZ8WllP0j7Vtf0R3kX' \
			b'xVzOgPZF3JdcK2NCcVN56LQ8GCkHSKNCn6dBH3jKxLiZRLvcF1hXr2usUlagfxrmAnHCloQrASworYdw6CwMiCqrnIXNygsbJNJWYSFxouj9GkRU5Gs1aXGiOPYoKy7sHYqHM2GqStUZvlGivNkm+ZPFg4PaGtNQ3qDRxJpnKDe2cX7S/IcFmPJGLwtjciuM' \
			b'UIEfEcJv0mC5GLHlBdfxy/H4hWnMXzicAN99YLwmFB3IDrMRvmupQYK4iCLkfAN5wOCaxzj4Doe44WA5XHwDF4LA5a1R7Ch3g8oFdyxW+OIGVdCiPsAdzRFOlcEli3C1IlyUCFcrwqXtQRMGVGHwcxUdKg/8gFIMzr3E5R5x7iVOvIQcbHAcIA4JxHm1oCaD' \
			b'A0dx0gFOOMDKKaTboFkA3RhQi4F0Gpx5D+lscbFXKPVtU0Ou2nT0+meDEt/gD3LCBp6+6fC4rjYTONd4vdqAADdoWTaovg3qbANp2kCaNmhGNqidTYOeQC0btBobNBmbhsJBDxa9o0tPvtCpxaOW7sZo9HjVoBuofwNi2qBONxMd4A9cIREbdLToWGOQED6U' \
			b'yA0+lp7a0T+MFyYFS/YGi/YGy/YGC/dmpEjjAbpgAPh4TMCADqDLDUYW9LgBGaKUNhgKxpYjS4FTKlAgdb/jgehk0QclpUW5kADqWuSSuwsTiTKAHLmx5JtuBlcogBvQ8wby9mYkJaAXTD7GHJMPFyhuqDQMmh4Jd424JxHWmB5SJT60waDhGuTWjSHpgOeW' \
			b'VEEPpURggPg0lDhGg+7Ey6gaVC5chFK+mVA76EaqAgf8oUpR1VAONih6fAAKzWKMatIDBYkPwLwE5Xcz4B6TBIGNmDzyBveNHMsBdYBPbyhjorYoz1DuQa1iiJglRhRU/w0aUjSfxXgW43le41ksZ7GcT9xyGrScuywm18uHwHQGddt9DSj1kfsu89CSDruN' \
			b'aa6SfYBJ7WKrSq2H9gTravazsLgY1d5W1gSW9hAL26zTyuLqQ7gkTGRt+8Tigj+cVTVreQfU2rBgY/kvsrTkcCZrK8HvtrnDHlaXgngUy+vT75J9uuUd9re9wyHWN7C/B5rdYe2Gl2I9xRZ4SGwwCWDeDlf/sg9YtRgesHIxwa4d/x9O+kLjPJBZZpucGGRn' \
			b'jamTx/eNOIPM1ti9n0ysMfWccLcJd3OIWbaBZab+jLAnZrErxFvpXC/hsrmeXGePH740UF+WN9+dmPCc+TZiwrvYjGOvFL3tCXqvsP/N9YU182Yee8G0O9GZe8smXz/REX62wyEgeY+EH0HGLyATFsAfflh3AQ8xClIM9GL6MTPAOWaH1PxjtsApqYsYGI9E' \
			b'QSs46BMkNB4L2E2KA/0jPHSCiAwe8PNx+FEUwkQfoAIqHCCPFuTB2BgDdGCmUCunuGA3dBZYiAN1mfLPw0J8OlA4SHivzAkbhEt5qydGOMfGo0J9CS7IVGPuob1gg07wG8q4xw5IF4jyIwrZcQNPFB0NogM7MMm6YmAY310ICcPLbp4pIqI6uWwkWTXvMfUs' \
			b'ILsrwLqWMjZPmkaEEwAnCadzfpRA6D54KVFdvycmyU0hmSieA0tP0RRDSADEMZ0UPA3hRmMRQ0d1voAe8XYMfBrSnKTGQ4hZwxzSErTpOUcOk4ut0EhOcTbVpHqUdAqZQg2zXB2lTPtAFay2eSAFtuMDVZ7s9ED1ne6BVDr0D6TVwT6QYofhgXQ7wr4ns83+' \
			b'QB3sEfIm+wQrzl4hUg9UPQF7+IAVCbBLD4htsB1wbpGO3fXpeGi7pT6w6bLEQvOIPFxi4T4c3MHAe+Tf3tw7mHko/JR5mFPYXaFnoy0gHp9niCceHe/8vZh3LPMudFfeia+55pH35vgWPcHxzWaaRnTbLqzZhY2wZqj50I3iUCc+jCSgFgl0st8ZZC0+56Bm' \
			b'Y6DF9+sTBGaWYabREZDxaQQyyxyzSxzTLqyIY6rgmGOiyyWOsbeTOGZjjtm4PdVwc0pjqfziUyuq07QpuwIdshhXyq6+sKtw6865hUJNuTXI5rA1RFuALT7PYEs8Omz5ezHrDIytMEzFlviaxZa7yWErip3DVq5Hj27bha1hYQtaY4MgK7pqJPK1pL6Tvd0V' \
			b'XC0+55A1xMiK79cnCLIGRpZGR5AlogiRNTCyhiVkaedfhCxVbows0eMSstjbScgaYmQNCbIGRpbEUpHFp1ZUp2lTZAU6ZDGuFFl2X2TtgtVNk6pQ6j4phQlvEkoZ3ZRS6onePSmhxHGbUNH7JhuEhrmGQu28IwXBgFJfc4DyNymgopAcoPAkBBRmiNk3TqZZ' \
			b'2JJXUPElIzGveR+9e9oRWi1+Z/hEgzM8n8L7MT38KMYTHg9BfBhPcpp7aUUinOMTRy7hk4Yf80nVuMAn8XYKnyg1nk8Ul4BPJIXJxVL4JKd2FNlI2oRPoRZZjo5PyqV9eUSMqfcD0oAHaJm2QTQUEBUQ3R+IMNEpiIxsDkTiKQYROy6DyN9PkmQQmcBdQSS+' \
			b'ZkHkbvIdfEP4CEciE5PILIHILGwJiJLHatRr3sckygdXi985EsVvq3KhKIgMg0ijIyDi0yyIzBKITA5E+tQYRKLGJRCxt5NAZGIQmQREhkEksVQQ8akdRTaSNgVRoESW47VBNBYQFRDdH4jwoSmIetkciMRTDCJ2XAaRC41AxCMrnKPxIyvU1yyI3E2uRRSG' \
			b'5DnUZ7rs5knUL2xpkyi6ZCTqNe9jEOVDq8XvHIj6GETx/Z08S1DEQyZchARFfJpF0dJwCZMbLqHhJygSRS6hiL2dhKJ4uIQJhksQiniYhMZSUcSndhTZSNoURYEaWY7HomgfBGXIMxXyFPLcH3lsZdKRDuxm/EAH9RSThx2XyeNCI/LwGAcTuit5xNcseZw3' \
			b'R57oCY48uTEO8+SxC1tKnjhlEvWa9zF58qHV4neOPPH4huT+Tp4l5OHxDS5CQh4+zZJnaYCDm6MTkUfcE/KIIpfIw95OIk88wMEkAxxkvLjGUsnDp3YU2aiMhDyBGlmOFyZPUwt6LsCdy0wPOoU4p0wVOoUka6HIKQRJ6LEvNbaIsUUJxEpIiEk2RwjxEBNi' \
			b'EvO2zAgXXsN5nBgxBe7KiGkBEFhM5RbfSTZGv82xM4TCCGW3rW6y9MHSTZabKeSEtcdUIfpwwxSES2PdRg8DOhma8Mk63m3cQYNpiQZTjgaS7IQGorLHmjGkLIhAMMkAt5EBoBlWAMCnOmOIM1owaSiaN7SXFQ+sd3O1hsNZJhKtuBFxy9OH8HXneOeNC8zf' \
			b'abcWu7W+W0s9RegQx0Vw+NBofSnu1nKOre/WUl/CDjy27KQEoZtr2mEZdQEoRqJQHULag7u4wnCyW0KR+JKRZHBEY47sCK2ufax380W8BJRJQuncoUCm5b6uMHIMGTnNYaZd6u5qw+4uneCmuHERiHCjil7AjSbwBOC0MXPapNur5W4vjaWwR07tKDKSNAp+' \
			b'QumxSC/d+DAFXwVfpU8sxJat2rRPjN1a3yemnmJsseMytlxohC3uE2tDd8WW+FJsWcaWDbBlGVuWseVucdiKnuawdXD/WBhOdkuxFadSksERTbCVD62ufaxnsMVeQmzFoXTuULHFHWVh5ARbfJrF1lJfWZvrK3MPjnElCl7ClSTsFFzFfWVt0lfWcl+ZxlJx' \
			b'xad2FNmojARXgdRYlJfG1d7rN5TXNOU1zdNB0lC16cQedmv9xB71FCOJHZeR5EIjJPGcHufY+jk96muuF87f5DAUhuQxdHAfXBhOdksxFF0yEvWa9zGG8qHV4neOQfGcnuT+Tp4l9OE5PS5Cgh4RRQ49S5N62tykHg0/QY8ocgk97O0k9MSTetpkUk/Lk3o0' \
			b'looePrWjyEbSpugJ1MhyvDR69l4coaCnoOfpoGesWn134dAzyubQI55i9LDjMnpcaISekdEzBu6KHvE1ix53k0NPGJJHz3gwepa2FD3RJSNRr3kfoycfWi1+59AzxuiJ7+/kWYIefifkIiTo4dMsesYl9Iw59Ej4CXpEkUvoYW8noWeM0aMRV/TwCyKNpaKH' \
			b'T63KRtKm6AnUyHK8NHr2XtvAln66m+uns7S8WCHUsYTCPJ3OJ+10U0KpJ4gp7wVS4r4NKfKliPLBYXbqeEJpFz5GEKW+BFF4DPmFdgKqjlmFOzMFASiuolAdrrrmUFwlQW1vCa7iS0aSUYscQlztCK2ufax3E0u8BNBKQuncoXCr43mmYeQYXXI6+gsJwLql' \
			b'CaddbsKpe3wEMFXzAsA0eScArIsnnHbJhNOOJ5y6JDPA5NSOIiFJmwAslB0LdAtgBy6EcCzIyooHpQ11h4QyFVnDiFBGNkco8RS1ocRxsQ3lQyNAGQaUCdwVUOJrrg3lb3JQCkPyUDIHQ8ksbCmUoksa9Zr3MZTyodXid45IJsZRfH8nzxIWGWaRRkhAxKe5' \
			b'NhQJcRZBJocgCT9BkChyCUHs7SQEmRhBJkGQYQRJLBVBfGpHkY2kTREUqJHleOk2VFnjoKDnDtHTVmTxIvS0sjn0iKcYPey4jB4XGqGnZfS0gbuiR3zNosfd5NAThuTR0x6MnnZhS9ETXTIS9Zr3MXryodXidw498bju5P5OniXoaRk9GiFBD59m0dMuoafN' \
			b'oUfCT9AjilxCjyTpFPS0MXraBD0to0diqejhUzuKbCRtip5AjSzHS6OnrGpQ0HOH6KEvySboGWRz6BFPMXrYcRk9LjRCDw9acI6dH7SgvmbR425y6AlD8ug5eNBCGE52S9ETXTIS9Zr3MXryodXidw498aCF5P5OniXo4UELLkKCHhFFDj1Lgxa63KAFDT9B' \
			b'jyhyCT3s7ST0xIMWumTQQseDFjSWih4+taPIRtKm6AnUyHK8NHrKsgYFPfeHHsyadYIedkNnXQi7nthXxB7xs8geHxxmGwq2844UBLNHfc2xx9+k7IlCcuzBk8PYE4aT3RL2xJeMRF1OI/bsCK3WKO9mD14P2JPc38mzmD14PDQ+QsweOc2xh4Q4xx6OXcIe' \
			b'DT9mjypygT3i7RT2UGo8eyguAXtICpOLpbBHTu0ospG0CXtCNbIcL8weUxf2FPbcH3uaqk+HI/S6KXvUU4wedlxGj/NK6OHRCH34FEWP+JpFj7vJoScMyaPn4BEIfbOwpeiJLhmJes37GD350GrxO4eeeOxBcn8nzxL08MADFyFBD59m0bM03qDPjTfQ8BP0' \
			b'iCKX0MPeTkJPPN6gT8Yb9DzeQGOp6OFTO4psJG2KnkBqLMdLo+d6izIU9BT0XA09purTcQbs1vtxBuopRg87LqPH34/o4XEGzrH34wzU1yx63E0OPWFIHj0HjzMIw8luKXqiSxr1mvcxevKh1eJ3Dj3xOIPk/k6eJejhcQYuQoIePs2iZ2mcQZ8bZ6DhJ+gR' \
			b'RS6hh72dhJ54nEGfjDPoeZyBxlLRw6d2FNlI2hQ9gRpZjpdGz/UWVCjoKei5Gnraqk/HGbBb78cZqKcYPey4jB4XGqGHxxk4x96PM1Bfs+hxNzn0hCF59Bw8ziAMJ7ul6IkuGYl6zfsYPfnQavE7h554nEFyfyfPEvTwOAMXIUEPn2bRszTOoM+NM9DwE/SI' \
			b'IpfQI0k6BT3xOIM+GWfQ8zgDjaWih0/tKLKRtCl6AjWyHC+NnrI4QkHPHaJnqPp0nAG79X6cgXqK0cOOy+hxoRF6eJyBc+z9OAP1NYsed5NDTxiSR8/B4wzCcLJbip7okpGo17yP0ZMPrRa/c+iJxxkk93fyLEEPjzNwERL0iChy6FkaZ9Dnxhlo+Al6RJFL' \
			b'6GFvJ6EnHmfQJ+MMeh5noLFU9PCpHUU2kjZFT6BGluOl0VMWR1gbesqScZdDEM6RTscbsJv14w3UU4QgcVxEkA8Nc4/l4QbO0frhBuprDkH+JkVQFJJDkD14uEEYTnZLEBRfMhJ1OY0QtCO0WqO8G0E2Hm6Q3N+5Q6GQ5REHYbQYRHKaA5FdGnRgc4MO3IMj' \
			b'EKk6F0Ak3k4BkY0HHdhk0IHlQQcaSwGRnNpRZCNpExCFUmNRXhpEey+VUEBUQPT0QGRwpY4EREY2ByLxFIOIHZdB5O9HEPEbIOdo/Rsg9TULIneTA1EYkgfRwW+AwnCyWwqi6JJGveZ9DKJ8aLX4nQNR/AYoub9zhwoifgkURktAxKdZEC29B7K590DuwTGI' \
			b'RJ1LIGJvJ4Eofg9kk/dAlt8DaSwVRHxqR5GNpE1BFEiNRXlpEJWlDgqI7hhELWbCBEStbA5E4ikGETsug8iFRiDi90HO0fr3QeprFkTuJgeiMCQPooPfB4XhZLcURNElI1GveR+DKB9aLX7nQBS/D0ru79yhgohfCYXREhDxaRZES2+FbO6tkHtwDCJR5xKI' \
			b'JGGngCh+K2STt0KW3wppLBVEfGpHkY2kTUEUSI1FeWkQPeLCB91UWLT+F0P1E+MQfu4LzkEOB74ospg3kxdFVjb3okg8xS+K9DMEy6+KXHj0qog/7YBeomv6ukh8zpEJLYP4UzRRTgp+wTujg7/rEEYruyV42n62kTTUvI/fG+VDrGsv0V3fPk2WNsVn9TZ4' \
			b'LH3zbvKQopOhCSPGkNI7eb3P5AXS0ocd+vTDDhQMvkSSa8lLJFHvAqkocad+/k7TpK+Rks87kBxcvvPvkfjU0gVD2RmCYGz1wZcewnw8cb5SbJ2DU2DYHrDeAAbhAYkrvEID8ACIJW5db9WEZMXTJ4SufdY6LU2plTWlelx0N2lK9bK5ppR4iptS7LjclHKh' \
			b'UVOq56ZUH7hrU0p8CbCIV+y01aByt7oGVRieb1D1Bzeo+oUtbVBFl4wkoOZ93KDKh1bXPtYzbao+blPFQXTuUNtUPbepgphJm4pPs22qfqlN1efaVPrguE0lel1qU7G3k9pUfdym6pM2Vc9tKomltqkkV40iG0mbtqkCqbEoL92mut6yCoVNhU0rYtNQ2XTs' \
			b'HbtZP/ZOPcVsYsdlNrnQiE089s45Wj/2Tn0pm7g9RbuUTe5Wx6YwPM+mg0fgheFkt5RN0SUjCah5H7MpH1pd+1jPsCkehJcE0blDZROPwwtjJmwSmeTYtDQUz+aG4rkHx2wSvS6xib2dxKZ4KJ5NhuJZHoqnsVQ2SeYaRTaSNmVTIDUW5YXZ1F5v2YXCpsKm' \
			b'FbFpxPyXsGmUzbFJPMVsYsdlNrnQiE0js2kM3JVN4kvZNDKbxgyb3K2OTWF4nk3jwWxa2lI2RZeMJKDmfcymfGh17WM9w6a4ny8JonOHyqaR2RTETNjEp1k2jUtsGnNs0gfHbBK9LrGJvZ3EpjFmk0Zc2TQymySWyiY+dbKRtCmbAqmxKC/Npuuty1C+YlS+' \
			b'Nr5GSmHWS4eOs9vgh46rp4hS4rhIKR8a5qKBh447x8EPHVdfQik8hmxCO6EU3cy+zBQEoKyKQnWsGg4eRh6Gk90SVsWXjCRDTiNW7QitDmK9m1XiJcBVEkrnDgVXAw8mDyPHuJLTHK6GpcHkQ24wuXtwhCtV8AKuNGEn4GqIB5MPyWDygQeTaywFV3JqR5GN' \
			b'pE1wFUqNRXlpXF1vLYeCq4KrVeKqwayX4Eo3hyvxFOOKHZdx5bwSrhrGVfgUxZX4Ulw1jKsmwBW3q3CHBsQF4HAVhupx1RyMq2ZhS3EVXTKSDI5ogqt8aHXtYz2DK/YS4ioOpXOHiquGcRVETnDFp1lcNUu4anK40gfHuBIFL+FKEnYKrpoYV02Cq4ZxJbFU' \
			b'XPGpHUU2kjbFVSA1FuWlcXW99R8KrgquVomrDnNcgqtONocr8RThivPPPm+ofHgErI6BFWwKLAyOvAmxMCshsngvzKIT0AXtzaQ34X1u/J9EzUXRoYvODmRXl9nkoS7C8RDArccb2dtaDiKGpf7je2tOKj1mhmV0A4kkGBPoYylhdd6fGxfY8Nss91S6qGMD' \
			b'9dYs2LolsHU5sElaErBJRlgAm4vPKWjjBAVs62K2sUQmF1OFG5/aUZUqCRS6JRon/xcH3PVWmSiAK4BbJeB6zG4J4HrZHODEUwK4kX57AM6FR4Dj4YHOcegDwPFlD7heANeHgOsFcL0AbtRgPODG6BcC7uD3XmFE3SYPdRFOAJc+3sje1nKQAG7c+RPAifhm' \
			b'ATeKSELAuVhKWJ335wE3CuDG4KIDnNyaBdzSeMIhN55Qs0ICOMkIi4CT+JwGuPjV2JAMKWSJTC6mCjg+tU6pkkAHuEjj5P/igLve6hUFcAVwqwScrYZ00ha7DX7SlnpKADfRbw/AufAIcDxpawjdHeAm9uYAZwVwNgScFcBZAdykwXjATdEvBNx0MOBsZpOH' \
			b'uggngEsfb2RvazlIADft/AngRHyzgJtEJCHgXCwlrM7784CTmV36VJ6VpIATD1nALU3vGtLpXQQ4cU8AJxlhEXASn9MAN8WAS+d2kURcrnKA41M7qlI1TyvgIo1zxrg04K63KkYBXAHcKgE3YEZLADfI5gAnnmLAUZ7ZawiIC48Ax4PonePgB9FjcEMwip6e' \
			b'RYAbQsANAriBAcc3DcGAeo2ai6IHnDl8NMiQ2eShLsIx4LYeb2Rv1SEGnNm+x99bc1KHhVH2dEOy3m0QSwmr8/4c4AyPEnFPDZe/dbdmAbc06n7IjbrXrJAATjLCEuA0PicBziSjRZKB9yyRycVUAcendlSlSgIVcLHGyf/FAfeIq20UwBXA3SLgRsxlCeBG' \
			b'2RzgxFM8ZIQdl/HmQiO88Th85zj4cfjqS4eM8Dj8IRiHTzfXtEMD4gJwQ0bCUP2QkcN7JZe2dMhIdMlIMjiiyZCRfGh17WM9M2SEvYRDRuJQOneoQ0a49zGMnAwZ4dMstpYG5A+5AfnuwTG2RMFLQ0YkYacMGUl6HZMB+YN0OkosFVl8alU2kjYdMhJIjUV5' \
			b'aVytZpGNgquCq3XgasIsluBqks3hSjzFuGLHZVy50AhXE+NqCtwVV+JLcTUxrqYAVxPjamJcuQAcrkJHj6vD+xinhS3FVXTJSDI4ogmu8qHVtY/1DK7YS4irOJTOHSquuC8xjJzgik+zuJqWcDXlcKUPjnElCl7ClSTsFFwlfYhTgivpQpRYKq741I4iG0mb' \
			b'4iqQmojrwri63rob976Q4SA4UgxZQc5TwM21UIOZJJ37xW6jn/ulniLUiOMianxomBtGnvvlHEc/90t9zS1F6G9SvGTtssPMeHBPXxiz7JZgJv98I0mROyLc7Ai1lv0Ma8Z45tcovXmOLBsaM95xqjMUGZemdY25aV0awZgiqrsFioi3YygCeXyM++jGZEYX' \
			b'RnkzTC6GQhA5taPkOkmXECTMjxM/YQdBxPqj1e9Ws6JFaaSURsoqGimYrUxKDiObI4d4isnBjsvk8PcjOQyTwwTuSg7xJeTAY8gmtBN+0M017bDQuwCUIlGonh7mYHqYhS2hR3xJk8ERTaiRD62ufaxnwMFeQnbEoXTuUFCCx0MTRY4bKXKaxYtZwovJ4UUf' \
			b'HONFFLyEF0nYCY0USk3AGBMzhgQxuVgqYvjUjiIbSZsiJpAai/LCjZTueotclEZKaaScHTVQpNoUNa1sDjXiKUYNOy6jxoVGqGkZNW3grqgRX7ONFHfTno2U9mDMtAvbvo2UVnDTbuEmH2otfudY08agaXc1UtodFGmXKNLmKCIRTCgiuluiiMT6yEZKGwOk' \
			b'3dFIkRgqQfjUjpLrJF1KkCA/TvyEPRop11srolj9YvXPbvWhaKXzitht9POK1FNs9dlx2eq70Mjq86wi5zj6WUXqa9bqu5v2tPr9wVa/X9j2tfq9WP1+y+rnQ63F75zVj6cN8W05q9/vsPpLE4HG3EQgjWBi9UV3S1afvR1r9fvY6icTgJzVlxiq1edTO0qu' \
			b'k3Sp1Q/y48RP2MPqX2/JhXu3+mv4stK9dj9hRukSOrAbOgsd1FNEB3FcpIMPDXMNhdp5RwqC6aC+5ujgb1I6RCE5KuDJYVSYuoUtoUJ8yUjUa95HNNgRWi1+Z2iA1wMaJPfLXsiAx0PjI8TdTHKaQwUJcQ4VHLsEFRp+jApV5AIqxNsp3UyUGs8LikvAC5LC' \
			b'5GIpuJBTO4psJG2Ci1CNLMdLdzPRYgjAhQqsfAWRJAg1yqFuC0V1QKMuAFIdMKmLsVRvkcmu5st/4/6IskdgCvyAWG4FVw3O1ZhQz6ho0DTIxIBMYowNGZRBZoC8wkizN/7BQHsmvKE1RWOKphWbEvTlP7Ae8q5+HAPsbTBrYeGgTdm3wUwoTgzAMYAgudZb' \
			b'3xRs7S4e9gxFipflH+bSDWbfjtm4wWzm4tF5QGoslj4yKP72az91B5NSgqfY4hjrKYqsj3Xaiqr7HVExkqya9xE8MYc1I+Xm3CNquWcGol0M0eR+2QtEO4aoXhWIymkOol0IUXw5htHG0VQ014W+kDimeKVVgRixnSKWCMuLHZFEDAO3QfW2rYtQTF3NHQvU' \
			b'pTieOASti7HbJdjVZprGswnaauJmR5GppFrgG+jCsPz91wkf4BQIjNdb+t/hf2AxIpeOAcT43z4whOH/RMcTHSOOaTfyjm5EEGOmaukMKdx1BOEerMUMgh15A+YuA5c5y5BlsO5C6i6YLpKUALofJduYjkS+HdQLiZftkstR7FiCLdErodYirY7tngsJlaNT' \
			b'SCUjJFIK2bBRZQ8gTgSaDGKO4ouHiiOKUmSZH3uS40BsKCwO4QJBISECGf1Zix+a+3z3WdaWn2LI97Liqf1etNxHm+0h7lXL2urYSm/0KxPOMpNBVmuMBtLOG8j+8W3kTJtj0UxqU4MXpjjWWs60E5zF7O7bakYWM6nLg6bi+jz4AaUZkIsBzZlxjKyqmUb6' \
			b'snELsmhBFi3keLa0Q1jPh18DVvewij5Vvddnejv7WOY3qK+b+rDq+W4z3C0sFaOmGHNTMcdijg2lLrDEJMXQGpMPbR/aURq+GD62kKWExObat4ExQpQDdDbipqGqvF8FDU8GqGFDeX1AAVL9d5g373bFVWBv27HfqL+R2nB7Yp/ONex7d2SN+EnY5ke3y5hu' \
			b'U2deQN9OFRmrADN2uVu/bZ5OqyWP82Z0uAkzam/EhN5Q1biYzUeszm6ti3hLJvNWq7Enmclpz97WZs1mci39rqe8PVyhqTy63/VAcxmZSrJDd2IuxxWbS+oAeaom09B6SUeaTWyvtw8QX2yuQwT2M6DmZAM6Mw7kdBtK8T7Whtb72dGdw8pvscrZr6/aeQ07' \
			b'2q3ElpIkzmBLDRmqfe1p90SroJhVL1kNhfzxCC/9zUWqoV1oRY+woLjc76M12PsVW9A1W89zWc5u3npezXLauL/zRMtp9Ltzj9lwx4ywfst5UatprjtUqj5LxfOxGu5t6eO8OXO5/lf2l2uwYw4ofZznMJPtdc3kWUZLPZqZvONRUsVMPgkzaYqZPIuZ7KrX' \
			b'ZdD96U3uWzWK45kG3QeGkUzardjFOx9s/yTsIA50Pt9g++pf0wOwnV7z9HdlHPEDXjh9GmdOF0O54+04Dg8+vhZ5o7XHVVtJnltNkrhAh+TTMJnulTjLzZ5Wh7T3ZSYhWRBn+jzjTZnLzBIEFzGZ4A9nURxsOsMpR/FUo2JGH8OMohhpVYoNLq1xy+bUXs+i' \
			b'bjBtGPR4uGFtaWyYmzgUThdCMzs8ppmtH9nS7r2YTNpir9dlaevpuMopLvZSKqiHWVb8FsJ6zCuNjjnVxuLB0KzVwhp63LGVVixzF5xVf4yF3aq6jo9pU5sV1l4jW9pd354WW3qPtvTUftHIhGJeWJUZvS8TOj2mCTVrN6F9MaHFhD4BE9oUE3o1EwqyekQT' \
			b'2q7dhNpiQosJfQIm1BQTej0T2tzVO6hbtJcrHty5Khv5ZMzjBW2hoW9g3PCL+FPmpdf4nYSGPmYAsbonMwix9q/jb8Ekmuu/hi8mcjUmEvPEBovxZY3l+SqOq3jVfkqtsV2fudzn+y1XqDjqd1TaJ1aBbDOWco+B8Lh28tQ+ZYvJn9XxP28t6Sy0mORwrMHc' \
			b'fs456pMcUmgh9XsiHPurt7EfzUjqR0OOWILeTE4Fu6ubS5/hGvEcP/u0x+e4wMw8IMyo6rrCmUjFFhdbvA5bbKJfaItNaovNKbY4fc55bLHZaYtNscW7bLFTwRVscV+99p/iZevbqt3d9eHdnj62+zh9BMufyr1MB2n+c7amij9le43Wfc5O7tOy55LsDKGz' \
			b'gdHXZhOrt+tjs2zs0FJcu4G+3zfEr9Ntmf3c62brW6/Xa1bvMFB7N6ptMR53Yjw20Zerb8d4NPT55WI8VmY8qn+NUE/pe6qCDMWKFCuyViuCillHDYRiUmxIaEO00RM2aMZiTYo1Wa01mdbSnqGYFGuyZE2mC1uTPfqhL2dQ9ut9Xo9h2bdXOTQus73JKzEw' \
			b'rBX/CzuF27RTuD3IwGwHfZ5+4DYxLr4fuL01K3NI1643NSLMy/foQtRLBWjdduo2K0B0U+nQXZVtOm8NyKJJqhuyIk2xIsWKnGZFqPSX90JHmxGq4MnvlsxIjzUazPloTnAMNNVwsDTAnrp84bnFuhTrcqJ1GYt1Ocm6jO73xKxLe6x1ebypL7djYK655O6S' \
			b'kalp4CoOmLqwwaHie99DXTiwE4wOBXDp1hE9dJfhkSR5w2NQAijxeRMEBewBbTBk3gdelrx9ACNGtqcrtudp2p4L25up2JvpVHszXcPeTHP25pCKzpyVOXLU7iPP770NQ7OCxQvWY2woD69mtu0NN6tIkOtYYODEUb3DwaN6L7V+wPrty4oWSLm2jeHpUCud' \
			b'1n+bhoYFubLlTE61NnuN/r3SgiXrNzjXnsh5RaND4zJubkGRW7U8JOvu6ZmfueHCK1gyqVigVVkgzvi3v6zRbVqh9Uz3PrcVygwzXt/ybWtav3L9S1w8rl2isr6qlSse10CtbUlKSsqtLE5xZms1RiOMV7zeZDFY1zdYbC+0MrW69Xbuy2rd1po65zZbTTFb' \
			b'xWztbbZMMVvFbK3BbJnqNRaIfqBMinl96OhCW70GdeIszWbC9Z0gXPnR5S65TNM56UeX++q1wVEFI35o2eDK6uPwzXM4frYBQ0kLRqG/DTwebFOPnsAiWHJr0Q2tE071q6ioV6B50DtoHfIpiAP0CtkaBIuSwgyGX85ocORegyUTSr17OFyHLEGr0kGBQl03' \
			b'ZKchKTj/DYRMMxUhH6EyGwgTynTNdxmc/Yb2CK6YEX8YMglu0501ll219x89vcenD/s+H3IfFHwsSMsx6XEdyn7nX4MBTSOtBplco4jZ+YhBdsdPBDf0RbZ2Lp4NxxW/95vG1y1/jp+Zxq/adEkaAJJbf2hL+DtB/pf6weUtbXSFltfGCZdIC/x6zijXKLHD' \
			b'1RMLqOnxe8+QaCD92f7og+kNF9Hx9ERO0+HptM1MWqFKs/cfrl266w/XAA3OKb1TNr0GSb471RYTjtUySntYLYO47xSFEXEM8l3rtCZm6NWIjqRBJCLz6f03zdwZWYzAEvzuDYkT86qdZBVkrJHhNG6sfYG/sdst7nbkGlLfi+jNtviBKKwCqMaCdWxrVQca' \
			b'1O2NKpJN7oq/Xode9Ibwt8eduduWfnX2cMb3jrRtpWErgs4XZS5wXV9pohbBtTYWS5MvdLjmQoUVfCp9kP8hmx5XBqEKsncx7GaKoj1zcawfq0iaKrOFbT9x7LmFl/W+uGE7bsmT2eHaH/is8GYU8bE308a5zhRTf3C+aqt73TjPtGs04F11vY3F0p29KI32' \
			b'OqWpvnSJGqszb9jDdvZAHzN0zkL5Nm2xxnN5B5s397lxnjlDd0M2Y5xqkbGT+mybOeIeFk++g6IUqZkihQHd6cZ5Jt/fA3I9vVQN5yhZXbW94Yus7IV9N3zxdNg9LKwdnUWuxbrYXK0rayrbV/ZKRa4Jil29o+iZuPjhWwAtgrSG8YwqTyuKQ7W9YfNcjlDM' \
			b'OS+3sfX4G08Mhl+i5DuVipmfy1v4xvY+N84zO3rc1mLmcajE9TcW1QndRDdu3h+l6CEXj9p4CIr/HR3QAc9LjzIX89eP2ji/5buYDjLnB+Srg0z2cGC+2DtPmCq74VCWXdfEh529fMZtzyexDs/fH/bkkYyD4u504zyzswPsbEjGvHAalrvqkTYc63fIDSyy' \
			b'fP9PKWZzxWyq7nXjPLOzU+ysxQzzwklFDUcEP9qGo2oPuYElt7NrqJS2XaUNR3Tf6cZ5ZudwqrOXNjOeWuJs9agbDmE/5AYeDVs6dw4vdGN1rxvnmeM7d05oOGrZm1PrroahL4NTddyG80z2942zSOQIykrm+tBmb2TxlnFDBxdJnM10pxvnmZ2dOo9ZJMPs' \
			b'cJbiiTPSLrKF07sOv51F/oT6YC7dR4vTDm9nw3l7/gS1eIZQOQ8d3idjz15ywxxybAnerempOmjD6XCH3rO96QzNw24CGcIumFkJp6ymE/qB+BXNtV/OrKHQ4yzjozZOynjk3ftvOJf3sZ+hG+erw/uKbqz445zym9xYPyf0SJVXs5ncYKtTNk5Ic1IYB204' \
			b'of/xH8NZ7fCOrMc1Bfu+jz3cJEzVFTfMvMdcCzaen31Cv1kxDdu5AhccKVu0cT7b2ddW8tlR+aytyhZvnM/O0Ol4a6OCcDGjp7CxAu9wWBeuQ/UUNlbgE+pPvFS3P65CdtrGEzL971HuEU/pfceEsXvjTFRmOR6eiYbqXjfOM2WU2+F5ZqzudeM8U6Z+Hp5n' \
			b'pupeN84zZXzfwXkGl1a9043zTFku7fA801T3uvHilWVI4+F5xlT3unGeOaGb9W7zTFvd68Z5Bhc3HmjRMnFonYMso9uhA4qdHFHI3OQCeb8OcxJkBFpnC9Tf4aJXoEIc0F1zxQnyWdY3KDv+se9hyzcqnO6A7JD8jLzP6qFyFmbgrWxJWW13NoOsg0+gVdqD' \
			b'1dmT860V0dPV0EcpjlMcG16vaytO2HcyQnYGheCzrY+VW0BirLbd+a0lZGheUrhOl6IeKVTY83Vcep/GFPH6LbguAkvamngZakiXNI9si+cYKyMVGdvhcU9Tz+Xu3rtAqr95/v8BF1aQXg=='

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

	def expr_term_1        (self, expr_var_or_sub):                                    return expr_var_or_sub
	def expr_term_2        (self, expr_num):                                           return expr_num
	def expr_term_3        (self, SQRT):                                               return AST ('@', 'sqrt')
	def expr_term_4        (self, LN):                                                 return AST ('@', 'ln')
	def expr_term_5        (self, LOG):                                                return AST ('@', 'log')
	def expr_term_6        (self, FUNC):                                               return AST ('@', _FUNC_name (FUNC))
	def expr_term_7        (self, STR):                                                return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1].replace ('\\}', '}')))
	def expr_term_8        (self, EMPTYSET):                                           return AST.SetEmpty

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

def set_sp_user_vars (user_vars):
	global _SP_USER_VARS
	_SP_USER_VARS = user_vars

def set_sp_user_funcs (user_funcs):
	global _SP_USER_FUNCS
	_SP_USER_FUNCS = user_funcs

class sparser: # for single script
	RESERVED_WORDS    = RESERVED_WORDS
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

	a = p.parse (r"sin")
	print (a)

