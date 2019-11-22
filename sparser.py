# Builds expression tree from text, nodes are nested AST tuples.

import ast as py_ast
from collections import OrderedDict
import os
import re
import sys

from lalr1 import Token, State, Incomplete, PopConfs, Reduce, LALR1 # , KeepConf # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

RESERVED_WORDS      = {'in', 'if', 'else', 'or', 'and', 'not', 'sqrt', 'log', 'ln'} | AST.Func.PY

_SP_USER_FUNCS      = set () # set of user funcs present {name, ...} - including hidden N and gamma and the like
_SP_USER_VARS       = {} # flattened user vars {name: ast, ...}

_rec_valid_var_name = re.compile (fr'^(?:(?:[A-Za-z]\w*)|(?:[{"".join (AST.Var.GREEKUNI)}]))$')

def _raise (exc):
	raise exc

def _is_valid_var_name (text):
	m = _rec_valid_var_name.match (text)

	return m and not text.endswith ('_')

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

		if ast3.op in {'{', '(', '[', '-lamb'}: # ast3.is_curly or ast3.is_paren or ast3.is_brack:
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
		return AST (*tuple (_ast_mulexps_to_muls (a) for a in ast), **ast._kw)

def _ast_tail_differential (self, must_have_pre = False, from_add = False): # find first instance of concatenated differential for integral expression -> pre, dv, wrap -> wrap (\int pre dv), pre may be None, if dv is None then rest are undefined
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
				if must_have_pre and (pre or not i):
					must_have_pre = False

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

		pre, dv, wrap, wrapp = self.denom.tail_differential_with_pre

		if dv and pre:
			return AST ('/', self.numer, wrapp (pre)), dv, wrap, lself

	elif self.is_pow:
		pre, dv, wrap, wrapp = self.base.tail_differential

		if dv:
			return pre, dv, lambda a: AST ('^', wrap (a), self.exp), wrapp

	elif self.is_func:
		if self.src:
			if self.src.mul [0].is_differential and self.func in _SP_USER_FUNCS:
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
		pre, dv, wrap, wrapp = self [1].tail_differential_with_pre

		if dv and pre:
			return AST (self.op, wrapp (pre), *self [2:]), dv, wrap, lself

	return None, None, None, None

AST._tail_differential          = _ast_tail_differential # adding to AST class so it can be cached and accessed as member
AST._tail_differential_with_pre = lambda self: self._tail_differential (must_have_pre = True)
AST._tail_differential_from_add = lambda self: self._tail_differential (from_add = True)
AST._has_tail_differential      = lambda self: self.tail_differential [1]

#...............................................................................................
def _expr_ass_lvals (ast, allow_lexprs = False): # process assignment lvalues
	def can_be_ufunc (ast):
		return (
			(ast.is_func and ast.func in _SP_USER_FUNCS and all (a.is_var_nonconst for a in ast.args)) or
			(ast.is_mul and ast.mul.len == 2 and ast.mul [1].is_paren and ast.mul [0].is_var_nonconst and ast.mul [1].paren.as_ufunc_argskw))

	def as_ufunc (ast):
		if ast.is_func:
			return AST ('-ufunc', ast.func, ast.args)
		else: # is_mul
			return AST ('-ufunc', ast.mul [0].var, *ast.mul [1].paren.as_ufunc_argskw)

	def lhs_ufunc_py_explicitize (ast):
		return AST ('-ufunc', f'?{ast.ufunc}', *ast [2:]) if not allow_lexprs and (ast.is_ufunc_py or (ast.is_ufunc and ast.kw)) else ast

	# start here
	if ast.is_ass: # if assigning to function call then is assignment to function instead, rewrite
		if can_be_ufunc (ast.lhs):
			ast = AST ('=', as_ufunc (ast.lhs), ast.rhs)
		else:
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

def _expr_div (numer, denom):
	if denom.is_mulexp: # correct for wonky \int ... dv parsing
		return AST ('*exp', (('/', numer, denom.mul [0]), *denom.mul [1:]))

	if denom.is_mul:
		for i, ast in enumerate (denom.mul):
			if ast.is_mulexp:
				return AST ('*exp', (('/', numer, ('*', (*denom.mul [:i], ast.mul [0]))), *ast.mul [1:]))

	return AST ('/', numer, denom)

def _expr_mul_imp (lhs, rhs):
	if rhs.is_div:
		if rhs.numer.is_intg: # fix side-effect of integral parsing that it winds up numerator of fraction even if implicitly multiplied on the left
			return PopConfs (AST ('/', AST.flatcat ('*', lhs, rhs.numer), rhs.denom))
		elif rhs.numer.is_mul and rhs.numer.mul [0].is_intg:
			return PopConfs (AST ('/', AST.flatcat ('*', lhs, rhs.numer), rhs.denom))

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
		func = _SP_USER_VARS.get (lhs.diffp.var, lhs.diffp)
		args = commas.comma if commas.is_comma else (commas,)

		if func.is_lamb:
			if len (args) == func.vars.len:
				return AST ('-subs', lhs, tuple (filter (lambda va: va [1] != va [0], zip ((AST ('@', v) for v in func.vars), args))))

		elif func.is_ufunc_applied and func.can_apply_argskw (commas.as_ufunc_argskw): # more general than necessary since func only valid for ufuncs of one variable
			return AST ('-subs', lhs, tuple (filter (lambda va: va [1] != va [0], zip (func.vars, args))))

	return Reduce

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

def _expr_ufunc_ics (self, lhs, commas): # ufunc ('f', ()) * (x) -> ufunc ('f', (x,)), ufunc ('f', (x,)) * (0) -> ufunc ('f', (0,)), ...
	if lhs.is_ufunc:
		ast = lhs.apply_argskw (commas.as_ufunc_argskw)

		if lhs.is_ufunc_py:
			if ast:
				return PopConfs (AST ('-ufunc', lhs.ufunc_full, (commas.comma if commas.is_comma else (commas,)), lhs.kw, is_ufunc_py = lhs.is_ufunc_py))

		else:
			if ast:
				if not lhs.is_ufunc_explicit and AST ('@', lhs.ufunc).is_differential and self.stack_has_sym ('DIVIDE'): # could be derivative of form "d / dx (f)"
					return Reduce (ast)
				else:
					return PopConfs (ast.setkw (src_rhs = AST ('*', (lhs.src_rhs, ('(', commas)))))

	return Reduce

def _expr_ufunc (args, py = False, name = ''):
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

	if name and (name in RESERVED_WORDS or not _is_valid_var_name (name)):
		raise SyntaxError (f'invalid undefined function name {name!r}')

	if AST ('@', name).is_var_const:
		raise SyntaxError ('cannot use constant as undefined function name')

	return AST ('-ufunc', name if py else f'?{name}', *argskw, is_ufunc_py = py)

def _expr_varfunc (self, var, rhs): # user_func *imp* (...) -> user_func (...)
	arg, wrapa = _ast_func_reorder (rhs)
	argsc      = arg # .strip_curly_of_paren_tex

	if var.var in _SP_USER_FUNCS:
		if argsc.is_paren:
			return PopConfs (wrapa (AST ('-func', var.var, _ast_func_tuple_args (arg), src = AST ('*', (var, arg)))))
		elif var.var not in {'beta', 'Lambda'}: # special case beta and Lambda reject if they don't have two parenthesized args
			return PopConfs (wrapa (AST ('-func', var.var, (arg,), src = AST ('*', (var, arg)))))

	elif var.var != '_' and argsc.is_paren and var.is_var_nonconst and argsc.paren.as_ufunc_argskw: # f (vars[, kws]) -> ('-ufunc', 'f', (vars)[, kws]) ... implicit undefined function
		ufunc = _SP_USER_VARS.get (var.var, AST.Null)

		if ufunc.op is None:
			return PopConfs (wrapa (AST ('-ufunc', var.var, *argsc.paren.as_ufunc_argskw, src_rhs = rhs)))

		elif ufunc.is_ufunc:
			if ufunc.is_ufunc_unapplied:
				ast = ufunc.apply_argskw (argsc.paren.as_ufunc_argskw)

				if ast:
					return PopConfs (wrapa (ast))

			elif ufunc.can_apply_argskw (argsc.paren.as_ufunc_argskw):
				return PopConfs (wrapa (AST ('-subs', var, tuple (filter (lambda va: va [1] != va [0], zip (ufunc.vars, argsc.paren.comma if argsc.paren.is_comma else (argsc.paren,)))))))

	return Reduce

def _expr_sym (args, py = False, name = ''):
	args, kw = AST.args2kwargs (args.comma if args.is_comma else (args,))

	if py:
		if len (args) != 1 or not args [0].is_str:
			raise SyntaxError ('Symbol() takes a single string name argument')

		name = args [0].str_

	elif args:
		raise SyntaxError ('$ does not take direct arguments, only keyword assumptions')

	if name and (name in RESERVED_WORDS or not _is_valid_var_name (name)):
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
			b'eJztnXmv3DaW6L/MA9oGqgBJpEjp/ucsPROMs0yWnmkYQeAk7kHwsiFO8nowmO/+zkbqUEWVpCpd31oIy1cSRXE7h+cnUoeqZ6/+8sX7n7789JO/7P7yf978/D3swun7X33+8u8v4eDlN5+9+PzDT/AwHrz85r3PX7z/b3gYD77661efvP/Z38MR7D/59Ev4' \
			b'+8VX7+Hfly+++Fc5/PvHFA328PdvLz6nBD/gyBiND9/78F++ef/FFx9+Iccfvwih7w2HfxsOP+NDSiEW6q9wILta9g3sP/7ok68o3Y8++fTjsK/DQUMFooRiK4zOvsRCf/jxZ1/+/YsPMdePPvnyX7DGX2FqLz/6mOpNf//9c7z+Epv05acYRxoHmpBqzn/f' \
			b'//Tjj1+EVseAz7nVPw+tzmFUr89Dq0vYC94PJfw8KS+V9N/hz4uPP4O/H7z3kq5h6CcfSKvi0XvD4d+GQ2nVD19+8SEW5fOPPsb9h//5PjbDiy+pHTDJL7kaUNQvwx7b84OP/vbRB3jH+yJfjvfZS2p+aLsgif/84sP3KcIHH/31r6hDn3zEakiFfvHJB9jI' \
			b'eOFTvP/jF5998eWnUsSgJBTwH6xjuKtZ+SDL9/8NDt/+8e3bP1//9vZPdfwWjr97/dub37/55bdvvv/2x7e/v/5NXYbDN//8Fa788OdP4fjnN//1zevf/iucvv3j1ze/DSffwuFPr3//5rtffpSj3375f8MR5/f2zdu338WjX+NRSOb1t/Hwh+//GUN//z1m' \
			b'9I/X3/0ejn+lDDj4j5+/G8r8j3/8mpx888N3b4eSxgr9+MNQtyH09ze/xeOf/vjxmx9+iol998dvP/63appw+O0PP/+imymW6rfX3+mk4CCc/vkmXnn9/fcx0utYuX++fTPUlFop1gDrpBo+Xvjj5x9++Tle+O9Yoh9+/j0WCYSLEmd5cdpD/eCibsg/X8dm' \
			b'//mXWJY/dJTXP3+fhOuW/va7X3766XU8/SUm9i00y/99M4gxjffrD2++exNPQEV/Hlrn17e//xKzjmoTa/LLj0P9KdHk5K2685sf/3z949CifOfXu1fP9s7sXPt8xwcOD9oG/5hd657LKZzRkcVou7bd7eVSCOAzE+6DG2wIwkOKtfcUUu+eWQiFu+rnMcBi' \
			b'gLUhYN/jgan5j4cAY57roMYfBPlGB+EhHNWO/3iIX3fPJQgP4cjD/24HddjzFY8HsMeEcG97/GN3DmLUXNghKJzu24pShZaAhM3O9s/DOZZxB5epSFCQpoMA+j8E9frUVHKAYZgIlKS28YikBIk8qyERkErHZaJk6c6m5j8eUmhYJnCGh9isJASU5XN1Go5V' \
			b'eMO7PemCpf+2DZctHmAhJZyLvttbCeRzKCPJYNc2QwC1jhvOG4pgRgFDjL2lStmW/zhOCotiuWhWToNsoGyWC+f5j4NEHF80KAzSKgeNhOojF1wdLthOZMtFslgC1kPIqIHESTBSPAxq9Wnj5ADD8HaQrgHpOpZ/OG0PgkRLkmB7eDq60dYHp5kYbZcGNQen' \
			b'6U1761XJhp4hhRgF1OOARgVAjVgktQ3n0LNJJUFNTMuFw+yNqHEIPgwaTveWtBNyegYShfO633UNGQ8Ujujo4VU0bmBG5iOBZqSR9pZsAeoGxKtCP4Cy19xbK+z4NYq23bU+9H8MjoExpKk4pBtCag4Z7moaChGhQMjeUJ2N4T+uj8ULQb7SQXiIRz3/gWZ7' \
			b'/nw4xKOWe0C4BVuY5O6w0IPq4Sn1lHgKAiVr1HG8YFGhMRoSLagEa39t+I+HTGvuI7WhQ2pH7LJyQHWra7QPlvq/DyYAAyUonrd0LtlWkgcq+Q77cSY8hEAAFdCLVkqDwzl0dIpD/yEimxk0m6Rznv94uKfhe7BJGjIMoMHPOmxwUfFu11H7NNAZaqIBsAyK' \
			b'jbhrQrXoInV6KEfmIthzKhnqfif62XI7OOkdopwmyAMCn7k2CopO3VCsfudIvGDDnpEUpDvhqaX0D4Li6Z7tGlqgpglHtpYjhiwesF5AY3Xxbjzrk+RDSDzbNwzPVk7DFTTqXOSW/3gIaVgNGj7EaP1OmIh07OWIVQsPWICVRJBugF2wYVqBBWiMZnRDbYaR' \
			b'ev7jzWB82Cxhe3r+ox6DvNCydfyHnoC4uHKIR224+FxO4Sxc4B4GJepa0ggbNMKFpxFHz1ptuB0fSuS5rQ0X8BFLQuAInu5eVdAKoGXQZmBoLIEctAjMGigPWj9QsH4H8oOO26MRg9bp4RBbEZWzhf8Q3mAyqMlg6EBMNXR4wLvBWPgfrCakD9fAxteo8RCl' \
			b'29WQUQ39q7Z4DKlU8L/GGHAOOglmx+A9kEeLe4gJxamhPDUUqIYS1fCMU8MTZA3qX4MhrCHTGnPFvKAXgq0D3tbQQjVY7h42u+vbXe92vd/1mNYOawEZQHywXjXYiB4LAodVDQ8UO3zkBeBDjAoiVi2af3icAllDdigqT/aoA6uOiMa6VZBbhQnD3uIeboRW' \
			b'BTPQ2R0Ir8M2qned33VgDvpdj+WGeFBSqAaaeqAkPmlDp8QHFDDnYL49Pb+CuoGdAV339MQKBswTc2rSZripQjMHJ3AMYu1qBBc2KZSrwYd5OAT5k8hB/M9Q7hiAsnsOl7GscGo5FGuAsbAWeBX0AYNRCM+J7nj1FT4I0DmlXXTmxnTmWc/Cr1nKKDWSel+L' \
			b'KrGOoHTxtLayb+U2uY/ETXu5T27EGI71h9SqmKDbVieUty+Cvg9Blx59B4LGiRx6LGiCxTds4b0YeHnG6E3RhtvXBhC3K3K+BzmTBLCft9T/lcC+pgloNgbWHVzEUB5J1PzMR22e3t62EiE8fVZ0EOQa5CkyExkF6WhZKBmEdue2Do2rG/PdN6TS/bG+j/R8' \
			b'rOGi2cd1OtVl1uGM7oq+aiXVyjlWy5E6ggoy7lkfTBse7NtOhEhkKA29SUM/I4tA/U76hnFyLkMxKiUFeOk8PGIfd0IZt9c8cM90QiuzAtTHaOzmQg42pFwVY38Xxp4f8oqgb17QJOciyWuX5LM6jscaedhyYcbNkDnH12lQsF27c0Xe1y9vE5DsBNayk/nY' \
			b'8FDW03nt8GEEmsNjy2AL4dMztmdbdOHqdQGk3BYp34GUXZHyHUjZFynfupSf9WG+jIfuvQzNsb48l1Ixt8sU1qNOYbkynXEPvQ0ryP1LZrhoaLRKYbQ4atLTr8nFjpMz2yQXHukrng1vXXijxm/QT0mTJ+xeoav5qUk0Mu/YyriyKtO7WxohW9wj7sAGgZyZ' \
			b'8W1Bzh2I+1krxLFhWkbmZawgo+PwjoM7Hr+jkUZri6/UUCDogFnebb5zm/yskxdqtTwudEy+jt9vdr24QFYy8WbCyzGRcUOAfMYPl8/krBGB88tzJWFqGzQQ/JLtmbwKp7d7u/QNXSs5OS6f42I5LpbncWMF1ypUiS7JpYh+IY4dm2nPwvNdadQNGtWzNfTc' \
			b'FTx3Bd8fa9tgDEsbL21jNh+ezUdXFcU9HwReQCDGW4aRjUA7vHCryivUW3hme0XrZJrnZWXUPcjakqhxzVNTVjHdoHzxyZoXrxX53p58cRFiI8vUYF8Eea2CpIWFpYfeomBr7pu0FLQpD8i3IVJ6XBIBlMUZFzpu5UXW1PfK4tt76Jm4mD6Im/edPB7Reemp' \
			b'l9pTcbEsCQqSR8EVd9076KyN2Oa2ks4qs4zWSae13GtHq7Oki1fhqUpWg5EClT59QX0aC8SCbPlxqQjlAoRiglB46mDcuyq5yp2ziOpJRSWG0dRiIEU2jrtTkcm7l4kxLAN+ESavGtkPQlyZ+b2jCw7MFL+I550N+Gxp73fa3m1p73dofnobENDJ4tZe9tHg' \
			b'iDcUjZPoowXsnY1r42hkxQ/dvZfxFj8EFKE9aiepqtLKj/99EH6TjYk1srihOX81wqvygcb7mI2Qz/XgIhZSn5YMJbQ3Knnpq9taxIbwc9oynDD/07DjioDM8nQQzSV9zY7lTeJgTIG2DJyeSuRdK4PZ7PcZal6YdWoWWU2pw4ot0oLUC7SIbemzC39ma1vB' \
			b'8Be1aUFBwwsKGl5QQFO4lvM18YyWEjS8lIA6u5w25nAGq5NJEv76ZqH2jVO75Ye+VvRD3hw4ed1X+vv6dR/cF8vXTO+h+7zC1VLFb/CqJUhWrhi7EydmfGm7k9uuO2OZJ64vJFT7qqD61JVuXbHd12y7cTko94Gm9IFT+4ApTXdq05UlI1duPuRloG9LHzh1' \
			b'UrIqfeCq+0AtLlJwzfAyVtzhRMVz+p1Z3IF4TfhNNiMLcczzsI7D6N/sQXmb6EDODuXh3IhDudyAO1ACI17L5rm8nWfHVsmQ5qPKLMqtK6H1LHDTsnbIT1Kw56tJfkLC9KIbjWiafJ6cvP2MePuxqklEJ0nkXpygPxrnTN2AJnPKh81vQanQkZCmtMuawdsQ' \
			b'Zy2M6MefuLUT4W0uHBljggdYI55f5Khty7KYW9EUZ0unvwVRos+lYZ9Lwz6X0qON9Ggj/mq4F8y38uzIPyJW3I8eZdjXBqPalE/4briGk/Xbyo7VvK1YnzvCX3G9epJZDntkBFEHhzoTHLTEiaJjOXY84u16GjOTX47h9zyGv71J4nUci1aNfU0f4WQbJ0s8' \
			b'K3b08WzqPEf2nITnBD3ri2eT2YlxrIahuy0TNdeLQp4MsXEq5WueNbHP5Yn2690w94J6LQNhS4NasiPhsTcMm21Y3sDKHdaadkZuzroZQtUt67RlnbblOesmlMuQ2MtM260L2nHP5cmz8srjhGUyoO6tfG0B95BNOLXhp21b/LQRanlTetTN9yhsoSLwOxI4' \
			b'5NryM1DLz0Ao/V0jz/YY5vhSLd8px2Z1dF7LeY3nlJIryxofe/DWUeND6zl63mX3urCwxZAE9ConEpfnj17V/JU6SBO/io6fRMcveZcefNU9mPqfR5XwvOt414vUoRi+9MpHfory4e2s/IhDLT87QJ2M+il/M5/6b1fE8dhGsi+N/PifIzLYyKT7Nuh+IzqP' \
			b'nClcuW6uQI49g6QXqfI8XbV7VeET4s7sLHmXQOFwJBA1nBuqEw3g1Lkp0KeFRM2NzUKLowkZaHD7cO3ofRdqKjetC3XUtaOqQb2g9NJu1E6seShHLUQsIhYw6YE9KyQuUkD1pt5WDcqCvY7ep0Nc/QlKfB4OD1PYrri6AX+5DH8QC5Ue8q7xy5X4M+T4I9X4' \
			b'E8ZQhgY//wEa0+CSdRB+g1+qwJnxCq9Bm6ETG37cC78qjB/UQbcxdEDDxmxQYhCOrYqz69iuqGOgZA1+Hwy/DYa2BJfL4gw+zt7jMgv8zBt+4Q2aubEoEcgT18rj5xNxkTwoY4OrJlvsfnANGr/BTx60uEQD48C9uNwWnyHRPx37OOhVgwvGcOEBLqVHfzf8' \
			b'ngy+2IT6GKiLqStQmT2IFRphX0PP3kMN9tDKeyjF3uJxtdv3EFzhdTiE/2gu9iiiPcplb/A/BcMtaBL2oFx77Ot7lNUe7cAeu9Ae+9Ie5bWHeu/REuzRFOyx/+9RnnsU6L6m1KDp9gbPQLn2PaaI0R3GBOnsoR/vHV6GjryHpt1DE+8xMSoAlh576x41Zt/h' \
			b'nSCyfY8lwUSxcJifxysgrD2mC/1gD1qKzbHHe0Eoe4MVaKkCGNViOaqe2wKN2x7t2B6N2B7NCtcTS9xQTDjpsB0M1rLBS1hSuAzKuMe6thiGKYN27UFz9yDBvceEsDSYGN0KF3qsF4kB86aC1HiJGhsOSHhURmw4zBTTrqkCFI73O0wQ24baB+NAwrBH8YNu' \
			b'7EE39j3eUWFGWFi8AwWFUkORYOooVWyTjoRF9YMYVD246rFUFdUJzyAeaOAetHLvscWxjigTajFIB651Ropek7pgOVAk1LokMSh6h6li0Tu8of8abR5aumLnip1bYeeKkStG7qqMXINGbsq48dOuV1ZOPTEusnU0bZyxeH7a6B0+wK4yffRAbhaawG6FGaxT' \
			b'U4gj+gNzuMYM+uswhfjhNPwKVjSJNmMWIR5+auWoefQoIT9jCD39S8whBWxgEjmdSbPolxhGSuNs4xgq2Ye6LTaNfpVx9Il59BkDudIu+quzjFQNLIKYSJ8xkiSE44Zy9z/uAUnuH5DlPexM97+4tOh060mzHHqKIGNG09dtYkzjK7l0MoGnAsS8OmVhaZyv' \
			b'5ydWTRfwvMDUrNlggtPZksSbTyY56NV8rwzz4UxYMkEk8xTIcPoemEx80OsNPR2VzJLJpJGe7AkzZzJpEz9ivsjIy0sS/Blp/NVj/HXeaPQhHv5gORl/iIeTNfib2AgC/DVsnKzZGgj4CyaoSwdggDRQo2YBYScgUQkomjNhUQ/AwFlFXI4QwWHm4YGfAMMP' \
			b'fxFEWgUS6B7QTgbMMUOlU2BBK0MzfDNsQWWjLcGLhJLB7WQSslGcobtpqnESNMNNCXCG/CJ1KHMBT7xMBWcIhfgBRAQE18pegEQnOIWJ+6ZXqRySqVZwwhUhCKianpWxK2GZ21FJcsBKIpg+OVe1DByTtlAs48udNEYXYlRTKeEMqpXowrtaKh6wRzWTsFpa' \
			b'gY41CSmfjnVDofAwP+ZiaAKtKz4Ici0sufDztIw6kjAz6MUcOSXeiJ3UODQA6s5mKHcAxmjorAGnqgk1USUMFyX1oXaSkNBV9w3DxQ2kZcY25oEe+kz9QCrg+gd8AOsgGHomExjt9gM+7IBNe8BHCLAtcO7+lz7Gf/lkXjL2cbnhz3YcbjZm8ZjDYwYH/hb2' \
			b'Pip7VzF3NW8d89bN8Ra1zVG8BLguhKKWyVGkrRPaumnayi0pa4dEI2udYq1TMQJrJf7RQd8QL8NWlxn4UdRRhlmk6gimT85V4VABKi9YHY8QOUYn1Za9rabSqqzEEKA6BVMnw8hGRJBA1DFDXcrQg+SFoVLnWjdAENBqhi6ci4uyTxkq8p5lKMcbM9RtyFC3' \
			b'OxiKqqZL2MlhLohVbg7cVHrOItyYm23h5rsevxZm3gEzPTNzbv4TFYm2FJkxFJVMjiIyvSDTTyNTbkmROYRHZKp50XiZyizIlPjHkRnvyiDT55DpGZk6wywydQTTJ+eqMnEU6se49IJLL7j0gst8OpWVGIJLr3DpFS79GJeecZnOvh4mL7iU+mrR+yCc1bhc' \
			b'OEEb5Z7iUmQ9i0uON8al3xCXPoPLoekSXHKYC2KVmwMulY6zCDfGpTvz9dkkKG8DkcfwWNBY0IhoJGcJbKAZNMYtQaMEHb4fpFBq/EksjoA4ZBCBSLkJEJMiCBBD/KNAHO46BCKGaiCi2oZ3h0mGOSCmjdIn56oy+deLfKmT+spLxokUKst7QSEeBxRSBQSF' \
			b'nFTmRWSTOmqM0qc6uz7WNKl2EMtaFHJ551EYJZ6gMEh5DoUSb4RCapONUMhqnKJQSUajUMJckKncLCjU2s0iHKFwjMDmgZ7OAgO76oEeWjIQ9AWCBYIFgmdBsGEINnMQbGRLIchBGQg2AsHFXjJDBgMEGwXBRsUIEJT4xyEY78pAsEkhSLFaGRQ6dWsWgrpE' \
			b'pk/OVWUmIChuNlzfAMF8CpXlfYBgoyDYKAg2UxBsUggeZuFC6YmBQ62DVFYzsFnIwCDwlIEi5FkGcrwxA5sNGdhkGDgIJmGgtGQQqdwcGKiUmyW4GQO7wsDCwMLAsxjIfjzNnB8PNgptKQM5KMNAceBpph14xgyMGQwMVI478XIzOO6E+McZGO/KMPCYF2mS' \
			b'YxaCOoLpk3NVmwkIinNO02oI5lOoLO8DBFsFwVZBcMoltUkdcQ7T51nRUFUtbB8EsxqDCx1xosxTDIqcZzHI8cYY3NARp1GOOBGDQ9MlGOQwF4QqNwcMKv1mGR7HoOAvQ72+UK9Qr1DvLOqxN00z502DDUJbSj0OylBPHGmaaUeaMfViBgP1lAtNvNwMLjQh' \
			b'/nHqxXgZ6uVcaCL1dI5Z6ukIpk/OVW0mqCfOM43T1MunUFneB+opz5lGec40Y8+ZSL3UdeYwfaGeVFUL2wfBrKbeQteZKPOUeiLnWepxvDH1NnSdaTKuM6rpEupxmAtClZsD9ZR+swxPpV5dXRD2zlxJ93jAW7rW7p4hNrVebwN4rYHWAbAOINUzpPo5SPWy' \
			b'pZDioAykTljGN2QxYKpXmOpVjICpfo5R2N/lnjWr+1gJh/95SukSmT45V5VZvgiQoudXAZI/yngRRKRQP/JI6STzWPzBKYUusVdKN5zaeLgWRv1CGAXJpjASac7BaHoV4RYc6gf8xFYb8YfLGZYSck3UakIMGDEnQEbBpb4guGyxjvCCx1e3vnIQ3/PaMu7K' \
			b'jrsMzzaaudlG7Dy0JUiToEOkGZltNItnG4cMItCMmm2Ml80w2xjiB6bhieOwQDbDcMNd06sUDvFmjhEuyT1HtySC6ZNzVbM83YzMPBo98ziRQmXjobBPTgMBDc8/GuFgbNMMCU06C3mYF2MwVFsrgY/FWIlAMz0LGZbKJiiM5U9QGPRgDoWhbVIYmg1nI01m' \
			b'NlI1oeaihLkgaLlZ0Kj133ARTx2Xnfsxk4LOgs4yVTmNTJ6qNHNTldhjaEuRyUEZZMpUpVk8VTlkMCBTTVXGy2aYqgzxIzIdI9MpZDpGpmNkxnsyyDw2bZnknkWmjmD65FzVbAKZMm1p9LTlRAqVjYcBmXwakcmTlxQjVnkCmekU5mFegkyptlYCH4uxFpkL' \
			b'pzBjuVNUivxnUSltMkLlhlOYJjOFqZouQSWHuSBguTmgUum94SKeisozvlxT3tyVN3cFh4BDzzj0czj0sqU45KAMDr3g0C/GYcxgwKFXOPQqRsChxD86KzrclUGgP4ZAnWMWgTqC6ZNzVZsJBHpBoNcIzKdQWd4H/nkFPz9MmnJSOez5FHsH6Qv2pKpa2D4I' \
			b'ZjX2/ELsBZmn2BM5z2KP442x5zfEns9gb2i6BHsc5oJQ5eaAPaXfLMOTsXfGZ2EK9gr2CvYAex1jr5vDXidbij0OymCvE+x1i7EXMxiw1ynsdSpGwJ7EP469eFcGe90x7Okcs9jTEUyfnKvaTGCvE+zpF4ITKVSW9wF7ncJep7A39aqQKq+wd5C+YE+qqoXt' \
			b'g2BWY69biL3QBCn2RM6z2ON4Y+x1G2IvVFBjb2i6BHsc5kKN5OaAPaXfLMOTsXfGV13cHPme7gulFwzCc6ZHUR6uAPJqAUlf/K+xPxwHpA1bAkgJCoDkY2EkndQV7/OMpEsJJodsIiYpT8Gk1QURTIb4AZOWSUk7gSUlwSVpepXCITIxdBKZSe45ZCYRTJ+c' \
			b'q5rlkcmXpBEDMidSqGw8FGrKaQAn1YOrU8cqEz7D4Qii1BwDRA9zZIiGyictEQuzEqJc/nmIxtInEA1aMAfR0DIpRKmBNoIoa3oKUdV0GqIS5oKY5WaBqNZ+w0U8FaLlWy9l7FjQeB4aG0ZjM4fGRrYUjRx0OHakULQai71IhwwGKDYKio2KEaAo8Y+OHYe7' \
			b'MiBsjoFQ55gFoY5g+uRc1WYChOJJyhUOIMynUFneBwo2CoHKz5STyowdqfIKewfpC/akqlrYPghmNfaahdgLMk+xJ3KexR7HG2Ov2RB7TQZ7Q9Ml2OMwF4QqNwfsKf1mGZ6MvfJ1l4K9gr3zsMe/A4e749gzsqXY46AM9oxgzyzG3pBaxJ5R2FNbxJ7EP469' \
			b'eFcGe+YY9nSOWezpCKZPzlVtJrBnBHtGYy+fQmV5H7Cn1lZQDQL2zBT2TIq9g/QFe1JVLWwfBLMae2Yh9oLMU+yJnGexJ60xwp7ZEHsmg72h2An2OMwFocrNAXuqrrw/GXvlgy4FewV752GPHWTsnIOM9bKl2OOgDPbEQcYudpAZMhiwpxxk4mU7OMiE+Mex' \
			b'F+/KYO+Yg0ySYxZ7OoLpk3NVmwnsiYOM1Q4yEylUlvcBe8pBxioHGTvlIGNTB5nD9AV7UlUtbB8Esxp7Cx1kosxT7ImcZ7HH8cbY29BBxmYcZFTTJdjjMBeEKjcH7Cn9ZhmejL3yRZeCvYK9s7CHRhkKjLuj2EONpy39rYeK+kKGexRa8x3LuDfkELlH2Qn3' \
			b'4mUqKnMvxD/KveGuQ+7Rmusp7iU55riXRDB9cq5qk+ceX+qkwsK9iRQqy3vhHh4H7lENhHucVIZ7VPmBe4fpM/dCVbW0fRDMWu5xgee5F2WecC/IeY57Em/EvS2X0rMip9xTTae5J2EuCDXUjLmn9ZtleCr3mkv6pEvhXuHeNXKP/V7aOb+XNmwJ9yQogz1x' \
			b'emmnnV7G2IsZDNhTHi+tLkLAnsQ/jr14VwZ7x7xckhyz2EtapU/OVW0msCdeLq32cplIobK8D9hT/i1trbBXT2Ev9Wk5TF+wJ1VN6h0Esxp7C31aosxT7ImcZ7HH8cbY29Cnpc34tKimS7DHYS4IVW4O2FP6zTI8GXuX+rGZgr2CvWvBHvu0tHM+LajrtKXY' \
			b'46AM9sSnpV3s0zJkMGBP+bTEy+3g0xLiH8devCuDvWM+LUmOWezpCKZPzlVtJrAnPi2t9mmZSKGyvA/YUz4trfJpaad8WtrUp+UwfcGeVFUL2wfBrMbeQp+WKPMUeyLnWexxvDH2NvRpaTM+LarpEuxxmAtClZsD9pR+swxPxt6lfiimYK9g71qwxz4t7ZxP' \
			b'Cyo6bSn2OCiDPfFpaRf7tAwZDNhTPi2t2iL2JP5x7MW7Mtg75tOS5JjFno5g+t3ontg2eeyJT0urfVomUqgs7wP2lE9Lq3xa2imfljb1aTlMX7AnVdXC9kEwq7G30KclyjzFnsh5FnvSGiPsbejT0mZ8WlTTJdjjMBeEKjcH7Km68v5k7JWPvhTsFeydhz32' \
			b'aWnnfFpQuWlLscdBGeyJT0u72KdlyGDAnvJpiZfbwaclxD+OvXhXBnvHfFqSHLPY0xFMn5yr2kxgT3xaWu3TMpFCZXkfsKd8Wlrl09JO+bS0qU/LYfqCPamqFrYPglmNvYU+LVHmKfZEzrPY43hj7G3o09JmfFpU0yXY4zAXhCo3B+wp/WYZnoy98tGXJ8Ve' \
			b'+QTo7eDPsW+Lm/NtwW860JbgT4IO8efEtcUtdm0ZMoj4c8q1JV52g2tLiH8Uf8Ndh/hzx1xbkhxz+EsimD45V7XJ48+Ja4vTri0TKVSW94I/p1xbHLu20OVY2TwEXergcpgLQzBUWIvcB/GshaBb6OASy51AMEh7DoISbwRBt6GDi8s4uKim0xCUMBdEG2rG' \
			b'ENRazpI8GYJnfAKmQLBAsEBQQZDf+Lm5N374SSPaUghyUAaC8sbPLX7jN2QwQFC98YuX3fDGL8Q/DsF4VwaCx974JTlmIagjmD45V7WZgKC88XP6jd9ECpXlfYCgeuPn+I0fXY6VnYBg+t7vMBeBoFRYi9wH8ayG4ML3frHcKQRF2rMQ5HhjCG743s9l3vup' \
			b'pksgyGEuiFZuDhBUWs6SPBmC5RMuBYIFgttAkN//ubn3f6jYtKUQ5KAMBOX9n1v8/m/IYICgev+ntwhBiX8cgvGuDASPvf9LcsxCUEcw/W5Uytg2eQjK+z+n3/9NpFBZ3gcIqvd/jt//0eVY2QkIpm8BD3MRCEqFtch9EM9qCC58CxjLnUJQpD0LQWmTEQQ3' \
			b'fAvoMm8BVdMlEOQwF0QrNwcIqrry/mQIlg+6lLeABX4H8INz0JsGFGflG0HHbwTd3BtBJ1v6RpCDMm8EHYNwv+K3cYcshneCjlCIqhqvUlHllaBEn/11XImYeSfojqCQNFb9z78X1OUyfXKuajTxXtAxDrnS4b1gPoXK8l5wiOo4vBh01EZ7/gndfgKF1AQD' \
			b'CjEiJx4rOPyELouQurQ6tfFw7QtCd5SIVHgz6NPo/aAIfQ6I1CSZX9EdWmeDN4QuReKgmtyAyStCLrcj+TZUZMiV6cjVlJeFSvENq2RKRwtUxKdBwSL0pAd8/AHL9kDPEmB+HhD6YDIe6Cd+FS8v9Uswo89mXzc1cx/MLsPH6yLoquFjy8PHdm742MqWDh85' \
			b'KDN8bJmatF82fIwZDMPHVg0fWxUjDB8lfoAmMZPDDgaR8d7MILI9NojU+WYHkTqC6ZNzVaeJQWTL1ORqh0FkPoXKxsMwjmzVOLLlcaT41MSmzI0j23QceZCRjCOlzlr2PpZh7TiyPUrNYRwZyp1gM4h9dhzJ8cbjyHbDcWS7OxxHDk2XjCNFE4N05eYwjlTq' \
			b'zpI8eRx5qZ+KKVwsXLxeLrJ/qZvzL8XfR6Et5SIHZbgo/qVusX/pkMHAReVfGi+7wb80xI9c9MxFn+FivDfDxWNepkm+WS7qCKZPzlWdJrgoXqZOe5lOpFDZeBi4qBxNHTua0uVY3wkupu6mhxkJF6XOWvY+lmEtFxe6m8Zyp1wUsc9ykeONubihu6nLuJuq' \
			b'pku4yGEuSFduDlxU6s6SPJWL5lI/JVO4WLh4vVzsmIvdHBc72VIuclCGi51wsVvMxZjBwMVOcbFTMQIXJX7kYsdc7DJcjPdmuNgd46LON8tFHcH0ybmq0wQXO+Fip7mYT6Gy8TBwsVNc7JiLnXAxpJnjYpdy8SAj4aLUWcvexzKs5WK3kIuh3CkXReyzXOR4' \
			b'Yy52G3IxVFBzcWi6hIscFmskNwcuKnVnSZ7MxUv91kz5+cFCyBsgpOelGX5uaQZqNG0JISXokJBelmb4xUszhgwiIb1amhEv+2FpRogfCIkn0BFpJ4SkJDha06sUDjnpjy3TSHLPcTKJYPrkXNUsz0kvyzS8XqYxkUJl46FwUk4DKj0v1vCyWCO2aQaVPl2s' \
			b'cZgXozJUWyuBj8VYiUq/cLFGLHeCyiD/OVSGNklR6TdcrOEzizVU02lUSpgLAg41Y1RqvTdcxFNReanfpymoLKi8BVTWjMp6DpVhS1HJQRlU1oLKejEqYwYDKmuFSl2EgEqJH1HJTju0C6isGZU1ozKmkEFlfQyVOvcsKpMW6pNzVbMJVNaCylqjMp9CZeNh' \
			b'QCWfRlTWjMpaUBnaNIfKOkXlQV6CSql20gaxGGtRWS9EZSh3ikqR/ywqpU1GqKw3RGWdQeXQdAkqRTODgOXmgEql94aLeCoqL/WbNgWVBZW3gErLqLRzqLSypajkoAwqraDSLkZlzGBApVWo1DECKiV+RKVlVFqFSsuotIzKmEIGlfYYKnXuWVTqCKZPzlXN' \
			b'JlBpBZVWozKfQjUcBlTyaUSlZVSKr2ts0xwqbYrKg7wElVJtrQSqsitRaReiMpQ7RaXIfxaV0iYjVNoNUWkzqByaLkElh7kgYLk5oFLpveEinorKS/0OTkFlQeUtoJJdWv2cSyuqMG0pKjkog0pxafWLXVqHDAZUKpfWeNkPLq0hfkQlu7R65dLq+S0l7ppe' \
			b'pZBB5THH1iT3LCp1BNMn56pmE6gUx1avHVsnUqhsPAyo5NOISvZt9eLbGts0h8rUt/UwL0GlVFsrgY/FWIvKhb6tsdwpKkX+s6iUNhmhckPfVp/xbVVNl6BSVDIIWG4OqFR6b7iIp6Ly5r6W8/RInPPWWYI+wV7EXUCdIO4q8XYVaOM1jn5ujSPqHm0p2jgo' \
			b'gzZZ40j7ZWiLGQxocwptTsUIaJP4R5c4DndlcHZshWMeYboYpk/OVQ0mECYrGr1e0TiRQmV5H/jlFLycfOk0i6t0HWNMTijF6xY9r1f069cq+uNrFQcyBVGmZBLxzZKJ443J5IRMZ0JptEqRoCQZujGVONwFmcndgUpKZVlEa6hENLrUz9aUgVsZuN3CwI19' \
			b'S/2cbylE4C2lGwdl6Ca+pX6xb+mQwUA35VsaL/vBtzTEjwM39i31yreUkuBiNL1KIUO6Yx6mSe5Z6ukIpk/OVc0mqCcepl57mE6kUNl4GMDHp5F97GTqxck0tmmOhKmT6WFegkSptlYCH4uxFo8LnUxjuVM8ivxn8ShtMsLjhk6mPuNkqpouQSSHuVAjuTkg' \
			b'Uum94SKeOnC7uY/bPD0Sy8DtigduPaOtn0NbL1uKNg7KoK0XtPWL0RYzGNDWK7T1KkZAm8Q/PnCLd2Vw1q8euOkETZ+cqxpMIKwXhPUaYfkUKsv7wK9ewas/NnDrU1yF5IRSPSOqZzj168nULyRTEGVKJhHfLJk43phM/TYDtz4DJcnwYODG4S7ITO4OVFIq' \
			b'yyJaPXC71E/HFBoVGj0BjTr2u+zm/C67sCU0kqBDGnXid9kt9rscMog06pTfZaeLIDQK8Y/SaLjrkEbdMV/LLI2SYpg+OVc1yNOoE//KTvtXTqRQWd4LjTrlWdnVR2jUpb6UMTmmUcf+kx17Tnbr3Sa7hW6TUZQJjYL45mgk8UY06upNaNRlPCZDhmMaSbgL' \
			b'MpO7hUZaZVlEq2l0qR9sKR/+LFOF10Iw9vHo5nw8UDVpSwnGQRmCiY9Ht9jHY8hgIJjy8YiXu8HHI8Q/TrB4V4Zgx/w6khyzNNMRTJ+cq9pM0Ez8Ojrt1zGRQmV5H2imPDq6dhd//m+aaqkvx2H6gjepqha2D4JZjbqFvhxR5inqRM6zqON4Y9Rt6MvRZXw5' \
			b'VNMluOMwF4QqNwfcKf1mGZ46JWgv9XssBXsFe9eCPfb/6Ob8P1AvaUuxx0EZ7In/R7fY/2PIYMCe8v+Il7vB/yPEP469GC+DvWP+H0mOWezpCKZPzlVtJrAnviCd9gWZSKGyvA/YU74gnVPYc1PYS31CDtMX7ElVtbB9EMxq7C10FIkyT7Encp7FHscbY89t' \
			b'iL2Mt4hqugR7HOaCUOXmgD2l3yzDk7F3qZ9bKdgr2LsW7HnGnp/DnpctxR4HZbDnBXt+MfZiBgP2vMKeVzEC9iT+cezFuzLY88ewp3PMYk9HMH1yrmozgT0v2PMae/kUKsv7gD2vsOcV9vwU9nyKvYP0BXtSVS1sHwSzGnt+IfaCzFPsiZxnscfxxtjzG2LP' \
			b'Z7A3NF2CPQ5zQahyc8Ce0m+W4cnYu9RPpxTsFexdC/bYH7Kb84dEjaQtxR4HZbAn/pDdYn/IIYMBe8ofMl7uBn/IEP849uJdGewd84FMcsxiT0cwfXKuajOBPfGB7LQP5EQKleV9wJ7yfuw6hb0pv8cu9Xs8TF+wJ1XVwvZBMKuxt9DvMco8xZ7IeRZ7HG+M' \
			b'vQ39HruM36NqugR7HOZCjeTmgD2l3yzDk7F3qZ9BKdgr2LsS7GFvhgLj7ij2UP9oS7AnQYfYo1BofNovwt6QQcQe5SbY63UMwV6IfxR7w12H2MPQSewlOeawl0QwfXKuapPHHl/qpMKCvYkUKtkL9vA4YI9qINjjpDLYo8oP2DtMn7EXqqqF7YcKrsMeF3ge' \
			b'e1HmCfaCnOewJ/FG2KNG2Qh7rMgp9lTTaexJmAtClZsFe1q/WYYnY48+aQLUKeg7C31wHdriehBoCgYfDYNIBItuLoZwiP3xOA+xY9CW8FCCDnlohYf7FT9sS2VyfGtAolVIjEWwAxJDAWZ/2lYiHjLRHmNikmWOiXKJismDQX3LcO8EFa1Q0WoqovLUlhQ3' \
			b'l1Ile6GjVXS0io52io42peNh+kzHUGkteh+PMPOVhLQLCRnKkRIyiH2OkFS7w3UHdkNE2gwipXgH7p4S7oKI5W5hpGp1rrhmJJwCIvG6wb+ASfjbO/pLVxGVlgwD7AiULXTsI5iMdFRcnIEis5BByPCbwp4G3uySAgJbnl79QC0iUqBRINGU+78iT6SMFVf/' \
			b'tSSZocgBPeaokSPGue78Y0qM6WCFCIEGTg+C3ArLnxj8jKlfbecH6x5NezDnCwx5xoSv9LgPlnrKKJNFHswxWdxobqOtnXaY19Y1mtO9fFv4FMu5yGyODea8qczZyS3c4Q+M46FZ3IdfoYmmkCxgMH9oy9xxW9Y+sjmrV1q08LSOyrLMsHUZ4+aKgdMGLhq3' \
			b'zOMvKN3wCAxx8Pfc6VEY4oE9aLouMYANtkePg0BQD2gPA+3BRtHrR2P4X4OBXPdsjE+tl2YlbdbLba2lVM+1DZmPFRbTKj+1aDVRNYrlnLKcqNzRaGL7HRhOioFXrJNRXzCm2E9E31PLOgwCsSj0jdnwnaJ9TV9n99Hy4kkLT5/Q+x6wRemp0h+3xO6SHiwH' \
			b'M4yzJO2TP2PWfX/ejMVFmGJ74nPm9ZvRTU0oddqqXmdGH//BE1F7xITaKzSj/XnPnt1xi+cv0+K5J7d2V/3AWSzcFg+JzaVZt5t5ODzLovULZwbri7JoW88R1vdn1U6eI1xp2RKrRn3/1izb9Fucsy0bDdbv27o19I3GEy0cDljNA1QAx6tQoGW2rjnP1h1x' \
			b'ATjN3FFBl5g7d9pDHL6Mv1aTB/W9uIe5d23y7JOYPbfK7KFwT36os7di+hr6yY939XAHAt/6tW/z+A93c5auaTccrtbXY+ku2sptYeGol1/Og91C69ZQ9bccsqIEr9K6vUPL1jyhQ0v1WJYta9XaMhF31Vbtwt7WnjdURXGWibhHsWjmCS3ayT4tJ1m04stS' \
			b'LNoFWbSuWLTHsWh29+oCHY6PLK95x87Hl2zL3BM4Hyt71vfXYs7WmDL+7LzhFU148fKckK/FnDX0A+4nmbSznZB3/9M/AHDplUJ7kTbuJLtmsOS4BLC/Ext3in3D9aenP7dd4/Pau15VwcswsbJYpPu0bie+KeVWO8OyoUVzN2TRoPxQOFSUi7Zs2YXHT2Hd' \
			b'4Bzqv97K6VUT6WqJYvGWWDzsfbTWfI86eDWWz12Q8duj4DArt94G4jIftfZBr3hAi+gfzSJWj2AUJ7/+oA2je2Kj2J74yGfLY985RhAF+ESWEHNeaA4xDVS3SzCGjTNnPApix3nK5banGMODB8Lu0cxf/RTPhNrsVZf5PFjM3s2YvYVzeIm1a6iXXv7j301a' \
			b'u/7RrF3z1NauLtauWLsLtHa+WLsnsnZQ0MeyduaprV1TrF2xdhdo7bpi7Z7K2tW382rjKkzb9TjUXYw5u2hL9lhmq6HK3tKr2DN8S2r83nXN7iVQymKxbtxibeUyd2OWi749dvGW6wa9SLbwj+vMA5CHLJgpFqxYsHuzYDRaupRHLypMsV+r7Bd+5NJQ131A' \
			b'+0+W7DKXMxRLVizZo1qy/pIsWV8s2QaW7BIWLaz96aMzDJtXP1F0CwaueWQj14ihM3dg7KjXpwavGdZr0S9aDf8f0QByOajZ+kWWsLkuS7jBr+ssMIcNVp/6dnOCWbyElQ/FLBazeBFm0YzNolFmMf3/qGbRrDOLppjFnFlsxCyaE8zi4y1/KGbxBszi/ZhE' \
			b'OzaJVplEm/x/VJNo15lEW0xifuBMTbPaHD7ecogyDVimAd+NvaP8btOX5CJt2tPPAzqLFoxfyT7eEodiwYoF29qCsVm6J3e4zUwYNkf4f/0mrG0fkGbQv/CpDPvYA9pn6GewJ8vmH285Q7FsxbJtb9lssWynWjYb/9+FZStLF4plQ6tW0TsunNC9cCtHGn59' \
			b'qxn4x4+f1MhRETYbgEqFtrNxlGDWxjUkbrh43NrZ/oEQCAr1gEyBTvhAhh160AOaZNB+2Buye2UBRLF7F/9ER93rGm3dkz/QURE2tHXt1rauPeV5bpWFKwskioW7VAtHL+Pue23qiRaOX2Pe7OsEiwYNu1GNQ9TGkSUrCySKJbsYS1bT13TLKvsTLRk33x28' \
			b'GLU454ZqX9NBQ5bsEhZIFEt2j5aM+2j5YMhGpkya806cPIx9QBJC34M9vze4hDUNxZLduiXjvncpa1Zv0ZDdl7eawWexmj6B5C9h+UGxYLdiwUiDL3F5wVVbMGrVYsAGA0aeHGgK+g4PeFRZVg4US3aWJSObcvELpa7akpVnsbEpq3HlQFOTBSsrB4oFO9OC' \
			b'NcWCFQv2ZBasKysEigVbYcFIzy9t9WYxYfdnwnA8SaPI7oZWAoD6xt9ovkRrBg16cb/NfGHvK2/JqqHM93jnVdg3rOolWTkU2OkmDi1bs3tFvaRFjUX9abyhC2b3yuOXfiAcqwL/KdjqYPxcT03B7e5VA4VqOvwF8qZDK+i/fg7Hz/ZgO7E7ULw9ZAcmCzMD' \
			b'c9I3FGYwDM0VWA80ANC/d6AFoISgkNACIFE0LhXaWzA2cIo/G91U2AmhvDFbuA4ahBqNDYgKgX2nbtCxBs5BE7FXYb/BOcJeYkM3ttjdMSUwB+g53NFPUINWblMuu1v0j/JsMU8/nyuoGxraqlqQf4tcaLP/6t6I9Xbja1Qcd6Q4YB9AnfHntGv6nUVdQDsu' \
			b'Y83lxN/JHpc1GnxcfIcG1ozKDzQc/UPrRq6y6PSp/stV6PIxJpTAqWuO7kOjjmH0Y1zQBegKVdg/eYWBJC3+ODpUHHC/2T8DpTE1d8Lu/EpS95muZw1mrIbuVHf4NFDl6+3qI3WHZ5vF//DZIw1hylshenIFSqfOqT36bHs0CPLpVnHYMPiMRm2DNlF9Gm2y' \
			b'qRppLi+/Gd+Rtww6/qHzMhrnWta28DcELDcrZIvYpG+iUhO3QzN7bHZIC/SYmxyuQUGo6bt+uvkhH3poQghrUeBDThAH3M8igQdasJamCuJBw3q40bOmz10Zrlc6SrhB/19wZ+62TDKZ08Nsq4k4uXolV9PkxrFIsSD08nsaDRguYeMmq/OdEZ/UdzgGoF4J' \
			b'D3fwALmib5rTuqdVXbRZ101p3HQRXbXZZTY9TJTAMEBcvPnlUWnDsZ8cyRD6eHTyJXzsjbWuKQhYrVdmd68b64y5BuNud5excZPZbbpZ8/Q9rXrXva3bbbDhRN4mCT1FTqxC+RFysdTHdAcTvs+NdWaDaYysYmxtrXHOe6ON5+DP2bjp8hMipbsd6W44VrnT' \
			b'jXUmP78EOnN+j/OP0evs7nDDKfTshaVbZc65nxtyYmIqjoJnh8DVDnqFa3fuHXVHr7pkI92ykvEwxHFYEXcp3dTvDjcc8ssRtnQuytNvFqvs3kFW/MomP4lVEHBMt/Dl8H1urDMTs3iXigB02LisjZvxjGmpCzP9F9EtkZknbeQlo/6fnNBMHslRunvkjfUt' \
			b'P6W11tQ/lnlf092n9GReR5pddkPHiqlrEqO1MzEeY1uYK8t3o/m3e0I5uvDd6cY6MznhthnKUTe2xbndPdKGroun3szNmZ+LKl3wWBfsd/e6sc5MTsJt2gVRNzbthuju/GgbOhCfejO36uQ0VemJUz0RXdfvdGOdmXQV27wnNnbr3uh2j7qhJ/+pN7MfcJlo' \
			b'Wt8hu929bqwzp080nTFQJVVY2TenBqJD/+x3p224JGR5bFxoY3ltzHxc32QvcNMXn6nV3RWXe93pxjozOcH0mN01UY/H6Lq4hO+dbHpV3HlJsTiuaD7o0uaScc3m5W340+O0s+8gN9ah9fNDbvterTVmo949Lfl+t2rDRZRr7zncwqLX0xOA9oWdWqQKpyzC' \
			b'M+ak+DXTu37BdIkGAZdvn7RR1aBpT07gyIbLox8j3bmN9Wr9vNWVmwZcvH/1G8vujNmx8uo5oxlud87GFTNnpTG74fcTHjWDg41Vbf2k2iObiRPfN683F/3uCTdU5g3j8Zr5M+bwitk41BD8AkzZko31bHLer+jZSXpmdmVLN9azbSY5L4VQJ3lE4Zenbm1j' \
			b'4RZ3t1f4QbFb21i4VzS3eSmvJ3Bh7dkbr40d/m+W6LAb5aJOkziLksxtrEBlpel6BTK7e91YZ4p333qdsbt73VhnyhLb9TrT7+51Y50pvourdQa/lXunG+tM+czdep2pd/e68edIi0vmep1pdve6sc6cMTV7tzpjdve6sc7gZ6jpm9INP+CASkiALIVuLQZg' \
			b's1NgjR9n5wswTNeaBIpAMfCLz7igBf0r8NOD7PEGepaNDcJN/3NsfxAbBU53oHql/xt5BwaaNXwju0W14fecbc/h6dfLOAYoCDQFxu/40/uokqSCLakdqhWGg+rwh5nBMCepkCq3I/UNqouevPjNbf54P7SIfLifP47fjT6IHz6Gj6v5eYgC+vwKOw0oOX3f' \
			b'BlWbAQHZJh/+hvs69gtzBs8bDJUHEGfxuKXl9nJ3O4SA8fj6+f8HjvqOrA==' 

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

	TOKENS    = OrderedDict ([ # order matters due to Python regex non-greedy or operator '|'
		('UFUNC',        fr'\?'),
		('UFUNCPY',       r'Function(?!\w|\\_)'),
		('SYM',          fr'\$|\\\$'),
		('SYMPY',         r'Symbol(?!\w|\\_)'),
		('FUNC',         fr'(@|\%|\\\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LTRU})|\\operatorname\s*{{\s*({_LTR}(?:\w|\\_)*)(?:_{{(\d+)}})?\s*}}'), # AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

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

	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                       return _expr_add (self, expr_add, expr_mul_exp)
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                      return _expr_add (self, expr_add, AST ('-', expr_mul_exp))
	def expr_add_3         (self, expr_add, SETMINUS, expr_mul_exp):                   return _expr_add (self, expr_add, AST ('-', expr_mul_exp))
	def expr_add_4         (self, expr_mul_exp):                                       return expr_mul_exp

	def expr_mul_exp_1     (self, expr_mul_exp, CDOT, expr_neg):                       return AST.flatcat ('*exp', expr_mul_exp, expr_neg)
	def expr_mul_exp_2     (self, expr_mul_exp, STAR, expr_neg):                       return AST.flatcat ('*exp', expr_mul_exp, expr_neg)
	def expr_mul_exp_3     (self, expr_neg):                                           return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                    return _expr_neg (expr_neg)
	def expr_neg_2         (self, expr_div):                                           return expr_div

	def expr_div_1         (self, expr_div, DIVIDE, expr_divm):                        return PopConfs (_expr_diff (_expr_div (expr_div, expr_divm))) # d / dx *imp* y
	def expr_div_2         (self, expr_mul_imp):                                       return PopConfs (_expr_diff (expr_mul_imp)) # \frac{d}{dx} *imp* y
	def expr_divm_1        (self, MINUS, expr_divm):                                   return PopConfs (_expr_neg (expr_divm))
	def expr_divm_2        (self, expr_mul_imp):                                       return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                            return _expr_mul_imp (expr_mul_imp, expr_intg) # PopConfs (AST.flatcat ('*', expr_mul_imp, expr_intg))
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

	# def expr_abs_1         (self, L_BAR, expr_commas, R_BAR):                          return AST ('|', expr_commas) if not expr_commas.is_comma_empty else _raise (SyntaxError ('absolute value expecting an expression'))
	# def expr_abs_2         (self, BAR1, expr_commas, BAR2):                            return AST ('|', expr_commas) if not expr_commas.is_comma_empty else _raise (SyntaxError ('absolute value expecting an expression'))
	def expr_abs_1         (self, L_BAR, expr, R_BAR):                                 return AST ('|', expr)
	def expr_abs_2         (self, BAR1, expr, BAR2):                                   return AST ('|', expr)
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

	def expr_ufunc_1       (self, UFUNCPY, expr_pcommas):                              return _expr_ufunc (expr_pcommas, py = True)
	def expr_ufunc_2       (self, UFUNC, expr_var, expr_pcommas):                      return _expr_ufunc (expr_pcommas, name = expr_var.var)
	def expr_ufunc_3       (self, UFUNC, expr_pcommas):                                return _expr_ufunc (expr_pcommas)
	def expr_ufunc_4       (self, expr_varfunc):                                       return expr_varfunc

	def expr_varfunc_2     (self, expr_var_or_sub, expr_intg):                         return _expr_varfunc (self, expr_var_or_sub, expr_intg)
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

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_sub' and stack [-1 - len (rule [1])].sym == 'INTG':
				return self._insert_symbol ('CARET1')

			if rule [0] == 'expr_intg':
				return self._parse_autocomplete_expr_intg ()

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
	RESERVED_WORDS    = RESERVED_WORDS
	set_sp_user_funcs = set_sp_user_funcs
	set_sp_user_vars  = set_sp_user_vars
	Parser            = Parser

# AUTO_REMOVE_IN_SINGLE_SCRIPT_BLOCK_START
if __name__ == '__main__': # DEBUG!
	p = Parser ()

	set_sp_user_funcs ({'N', 'O', 'S', 'beta', 'gamma', 'Gamma', 'Lambda', 'zeta'})
	_SP_USER_FUNCS.update ({'_'})
	set_sp_user_vars ({'_': AST ('-lamb', ('^', ('@', 'x'), ('#', '2')), ('x',))})


	# a = p.parse (r"""Limit({|xyzd|}, x, 'str' or 2 or partialx)[\int_{1e-100 || partial}^{partialx or dy} \{} dx, oo zoo**b * 1e+100 <= 1. * {-1} = \{}, \sqrt[-1]{0.1**{partial or None}}] ^^ sqrt(partialx)[oo zoo] + \sqrt[-1.0]{1e+100!} if \[d^6 / dx**1 dz**2 dz**3 (oo zoo 'str') + d^4 / dz**1 dy**3 (\[-1.0]), \int \['str' 'str' dy] dx] else {|(\lim_{x \to 'str'} zoo {|partial|}d**6/dy**2 dy**3 dy**1 partial)[(True, zoo, True)**{oo zoo None}]|} if \[[[partial[1.] {0: partialx, partialx: dx, 'str': b} {-{1.0 * 0.1}} if (False:dx, 1e+100 * 1e+100 b) else {|True**partialx|}, \[0] \[partialy] / Limit(\{}, x, 2) not in a ^^ zoo ^^ 1e-100]], [[Sum({} / {}, (x, lambda x: False ^^ partialx ^^ 0.1, Sum(dx, (x, b, 'str'))[-{1 'str' False}, partialx && 'str' && a, oo:dy])), ln(x) \sqrt['str' / 0]{d**3}/dx**3 Truelambda x, y, z:a if a else b if partialy]], [[lambda: {1e-100, oo zoo, 1e-100} / \[b || 0.1 || None, \{}, \[[dy, c]]], {}]]] else lambda x:ln({}) if {\int_b^p artial * 1e+100 dx or \['str'] or 2 if partialx else 1e+100} else [] if {|{dz,} / [partial]|} and B/a * sePolynomialError(True * {-1}, d^4 / dy**2 dz**2 (partialx), 1e-100 && 1.) Sum(\[1, 1e+100], (x, {'str', 1.}, \sqrt[1]{partial})) and {d^5 / dz**2 dy**1 dx**2 (oo zoo && xyzd), {dz 'str' * 1. && lambda x, y, (z:zoo && lambda x), (y:0)}} else {}""")
	# a = p.parse (r"""\begin{cases} \sum_{x = \lim_{x \to \left[ \right]} \left(\sqrt[1{e}{+100}]{False} + 1{e}{+100} + \infty \widetilde\infty \right)}^{\left\{\neg\ \partial x\left[1., \emptyset, \text{'str'} \right] \vee \lambda{:} \partial \vee 0.1 \vee dz \vee \frac{\left(d^2 \right)}{dx^1 dz^1} - \frac{1}{\sqrt[\infty]{\partial}} \right\}} \left(\frac{\frac{x}{y}\ zd}{dz\ c\ dz \cdot 1{e}{+100}}, -\left(\partial x + dz + 1.0 \right), {-2}{:}{-{1 \cdot 2 \cdot 1.0}}{:}\left\{\partial x, 1.0 \right\} \right) & \text{for}\: \left(\lim_{x \to -1.0} 0^o o \wedge \log_\partial\left(ypartialx \right) a! \wedge \sqrt[xyzd]{\infty}\ \widetilde\infty \cap \frac{\partial^3}{\partial x^1\partial z^2}\left(0.1 \right) \cap \frac{\partial^9}{\partial z^3\partial y^3\partial x^3}\left(a \right) \right) + \left(\lim_{x \to \begin{bmatrix} b & True & \text{'str'} \\ dx & 1.0 & 0.1 \end{bmatrix}} -1 \ne dx, \begin{cases} \infty \widetilde\infty \wedge \partial x \wedge None & \text{for}\: dz! \\ \lambda & \text{otherwise} \end{cases}{:}\partial y, \left\{\left\{dy{:} \partial y \right\}, \left(False{:}\partial x{:}\emptyset \right), \lim_{x \to \partial} \partial x \right\} \right) + \frac{\begin{bmatrix} \infty \end{bmatrix}}{\begin{bmatrix} \emptyset \\ \partial y \end{bmatrix}} \le \ln\left(\left\{None, \infty \widetilde\infty, dy \right\} \right) \\ \left(\operatorname{GeometryError}\left( \right) \wedge \ln\left(x \right) - 1.00 \right) \left\{dx{:} 0.1 \right\} \left\{1.0{:} \partial x \right\} \sum_{x = 1{e}{-100}}^p artial\ True \cdot \left\{\text{'str'}{:} \begin{bmatrix} xyzd \\ dy \end{bmatrix} \right\} \vee \left(\left\{\emptyset \right\} \cup \frac{True}{\partial y} \cup \left|\partial x \right| \right) \cap \left(\begin{bmatrix} True \\ \text{'str'} \end{bmatrix} \cup \widetilde\infty \cdot 1.\ True \cup -\partial x \right) \cap \operatorname{Sum}\left(\left(\left( \right) \mapsto 1{e}{+100} \right), \left(x, \infty \widetilde\infty\left[1{e}{-100} \right], c \vee \partial x \vee None \right) \right) \vee \left(\cot^{-1}\left(\emptyset \right), \int dx \ dx \right)! & \text{for}\: \left[\left|\left(-1 \right) \right|, \frac{\partial^4}{\partial x^2\partial z^2}\left(\log_{\emptyset}\left(-1.0 \right) \right) \right]\left[loglambda\ x, y, z{:}\begin{cases} \infty \widetilde\infty & \text{for}\: 1{e}{-100} \\ dy & \text{for}\: dy \end{cases}, \operatorname{Sum}\left(False, \left(x, False, 0 \right) \right) \cap \sqrt[False]{2} \cap \frac{1}{dx\ a!}, \gcd\left(\left(dy \vee \partial x \right)^{1.0^{\partial x}}, \operatorname{Sum}\left(b{:}None, \left(x, -1 + 1.0 + \text{'str'}, xyzd! \right) \right), \left|-1 \right| + 1.0 \cdot 1.0 \right) \right] \\ \left|\begin{cases} \left(dx\left[\partial, \emptyset \right] \wedge \left(False \vee \partial x \right) \right) \left(\neg\ -1^{dy} \right) \frac{d^2}{dx^2}\left(dx \right) & \text{for}\: 1{e}{+100} \\ dy & \text{for}\: 1{e}{-100} \end{cases} \right| & \text{otherwise} \end{cases}""")
	# a = p.parse (r"""Eq(Union(dy2 - 2.0651337529406422e-09*notinxyzd, Union(Complement(diff(z20notin)*diff(s)*partialxb, diff(diff(diff(-1.0)))), Complement(diff(diff(diff(-1.0))), diff(z20notin)*diff(s)*partialxb))), Or(Union(Complement(Union(Complement(Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))), partial.chCa.dcGNDli().XG()), Complement(partial.chCa.dcGNDli().XG(), Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))))), diff(diff(dx))**1*e - 100), Complement(diff(diff(dx))**1*e - 100, Union(Complement(Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))), partial.chCa.dcGNDli().XG()), Complement(partial.chCa.dcGNDli().XG(), Union(Complement(Function('h')(x, y, z), Limit(-4.461590087263422e-22, x, partialy, dir = '+-')), Complement(Limit(-4.461590087263422e-22, x, partialy, dir = '+-'), Function('h')(x, y, z))))))), 0.1 - bcorx0orc)); slice(None); abs(Matrix([Integers])); Matrix([[[Eq(c, 2)]], [[{Lambda: oo}]], [[lambdax, slice(y, 2)]]])""")
	# a = p.parse (r"""Union(Complement(Union(Complement(Matrix([Le(Union(Complement(Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)), a), Complement(a, Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)))), ('s', 1.0, dx))])**(a[0.1, a])**partial**3 / (partialz**3*1e-100), diff(diff(FiniteSet(2, partialy)))), Complement(diff(diff(FiniteSet(2, partialy))), Matrix([Le(Union(Complement(Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)), a), Complement(a, Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)))), ('s', 1.0, dx))])**(a[0.1, a])**partial**3 / (partialz**3*1e-100))), -xyzd*FiniteSet()), Complement(-xyzd*FiniteSet(), Union(Complement(Matrix([Le(Union(Complement(Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)), a), Complement(a, Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)))), ('s', 1.0, dx))])**(a[0.1, a])**partial**3 / (partialz**3*1e-100), diff(diff(FiniteSet(2, partialy)))), Complement(diff(diff(FiniteSet(2, partialy))), Matrix([Le(Union(Complement(Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)), a), Complement(a, Union(Complement(y1, 0.001213674880465044), Complement(0.001213674880465044, y1)))), ('s', 1.0, dx))])**(a[0.1, a])**partial**3 / (partialz**3*1e-100)))))""")
	# a = p.parse (r"""Union(Complement(Union(Complement(((FiniteSet(diff(partialx), -tau57, [[-28832738.092809968, 1., 's']]), Sum(xanddz*Matrix([-1, False]), (x, xyzdin1e + 100*notin*diff(partialyin)*diff(s), partial)))), (FiniteSet(-13.574245287492392, partialx, dx)**d**5 / (dy**3*dz**2*Noneord**1)) / (dz**1*partialx**{}*orz20)), Complement((FiniteSet(-13.574245287492392, partialx, dx)**d**5 / (dy**3*dz**2*Noneord**1)) / (dz**1*partialx**{}*orz20), ((FiniteSet(diff(partialx), -tau57, [[-28832738.092809968, 1., 's']]), Sum(xanddz*Matrix([-1, False]), (x, xyzdin1e + 100*notin*diff(partialyin)*diff(s), partial)))))), 0.006826903881753888), Complement(0.006826903881753888, Union(Complement(((FiniteSet(diff(partialx), -tau57, [[-28832738.092809968, 1., 's']]), Sum(xanddz*Matrix([-1, False]), (x, xyzdin1e + 100*notin*diff(partialyin)*diff(s), partial)))), (FiniteSet(-13.574245287492392, partialx, dx)**d**5 / (dy**3*dz**2*Noneord**1)) / (dz**1*partialx**{}*orz20)), Complement((FiniteSet(-13.574245287492392, partialx, dx)**d**5 / (dy**3*dz**2*Noneord**1)) / (dz**1*partialx**{}*orz20), ((FiniteSet(diff(partialx), -tau57, [[-28832738.092809968, 1., 's']]), Sum(xanddz*Matrix([-1, False]), (x, xyzdin1e + 100*notin*diff(partialyin)*diff(s), partial)))))))); Derivative(dy, y); Function('u', commutative = True, real = True); psi, y1""")
	# a = p.parse (r"""Union(Complement(Union(Complement(Union(Complement(Union(Complement(1.0, Gamma), Complement(Gamma, 1.0)), 1e+100), Complement(1e+100, Union(Complement(1.0, Gamma), Complement(Gamma, 1.0))))**Union(Phi, partial), Or(1e+100, -6.70911653218863e+19, False)**(1 / Derivative(-1.0, z))), Complement(Or(1e+100, -6.70911653218863e+19, False)**(1 / Derivative(-1.0, z)), Union(Complement(Union(Complement(1.0, Gamma), Complement(Gamma, 1.0)), 1e+100), Complement(1e+100, Union(Complement(1.0, Gamma), Complement(Gamma, 1.0))))**Union(Phi, partial))), abs((-1.0) / partialx)), Complement(abs((-1.0) / partialx), Union(Complement(Union(Complement(Union(Complement(1.0, Gamma), Complement(Gamma, 1.0)), 1e+100), Complement(1e+100, Union(Complement(1.0, Gamma), Complement(Gamma, 1.0))))**Union(Phi, partial), Or(1e+100, -6.70911653218863e+19, False)**(1 / Derivative(-1.0, z))), Complement(Or(1e+100, -6.70911653218863e+19, False)**(1 / Derivative(-1.0, z)), Union(Complement(Union(Complement(1.0, Gamma), Complement(Gamma, 1.0)), 1e+100), Complement(1e+100, Union(Complement(1.0, Gamma), Complement(Gamma, 1.0))))**Union(Phi, partial)))))*Matrix([[FiniteSet(diff(0)), Subs(abs(True), sqrt(b), deg((x0, -0.1)))]])*And(Matrix([[And(w1, partial), Union(Complement(Union(Complement(c, partial), Complement(partial, c)), xi), Complement(xi, Union(Complement(c, partial), Complement(partial, c)))), And(oo not in b, b in Reals)]]), is_deficient((a, b))**[partial])""")

	# for v, k in sorted (((v, k) for k, v in p.reds.items ()), reverse = True):
	# 	print (f'{v} - {k}')
	# print (f'total: {sum (p.reds.values ())}')

	# a = p.parse (r"dsolve (y(x)'' + 11 y(x)' + 24 y(x), ics = {y(0): 0, y(x)'(0): -7})")

	# a = p.parse (r"\frac{d}{dx}(f)(3)")
	# a = p.parse (r"d**4 / dw dz**2 dy dx (f) (3)")
	# a = p.parse (r"d**4 / dw dz dy dx (f) (3)")
	# a = p.parse (r"d**3 / dz dy dx (f) (3)")
	# a = p.parse (r"d**2 / dy dx (f) (3)")
	# a = p.parse (r"d/dx (f) (3)")

	# a = p.parse (r"Function('')(x, y, a*b)")
	# a = p.parse (r"\. x |_{f(x, commutative = True) = 1}")
	# print (a)
