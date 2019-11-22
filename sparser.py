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
			b'//mXWJY/dJTXP3+fhOuW/va7X3766XU8/SUm9i00y/99M4gxjffrD2++exNPQEV/Hlrn17e//xKzjmoTa/LLj0P9KdHk5K2685sf/3z949CifOfXu1fP9s7sXPt8xwcOD9oG/5hd657LKZzRkcVou7bd7eVSCOAzE+6DG2wIwkOKtfcUUu+eWQiFaPXzGGAx' \
			b'wNoQsO/xwNT8x0OAMc91UOMPgnyjg/AQjmrHfzzEr7vnEoSHcOThf7eDOuz5iscD2GNCuLc9/rE7BzFqLuwQFE73bUWpQks4qkT/PJx7qmXFRYKCNB0E0P8hqNenppIDDMNEoCS1jUckJUjkWQ2JgFQ6LhMlS3c2Nf/xkELDMoEzPMRmJSGgLJ+r03Cswhve' \
			b'7UkXLP23bbhs8QALKeFc9N3eSiCfQxlJBru2GQKoddxw3lAEMwoYYuwtVcq2/MdxUlgUy0WzchpkA2WzXDjPfxwk4viiQWGQVjloJFQfueDqcMF2IlsuksUSsB5CRg1qKApGiodBrT5tnBxgGN4O0jUgXcfyD6ftQZBoSRJsD09HN9r64DQTo+3SoObgNL1p' \
			b'b70q2dAzpBCjgHoc0KgAqBGLpLbhHHo2qSSoiWm5cJi9ETUOwYdBw+neknZCTs9AonBe97sOa7XD0hvR0cOraNzAjMxHAs1II+0t2QLUDYhXhX4AZa+5t1bY8WsUbbtrfej/GBwDY0hTcUg3hNQcMtzVNBQiQoGQvaE6G8N/XB+LF4J8pYPwEI96/gPN9vz5' \
			b'cIhHLfeAcAu2MMndYaEH1cNT6inxFARK1qjjeMGiQmM0JFpQCdb+2vAfD5nW3EdqQ4fUjthl5YDqVtdoHxgCPpgADJSgeN7SuWRbSR6o5Dvsx5nwEAIBVEAvWikNDufQ0SkO/YeIbGbQbJLOef7j4Z6G78EmacgwgAY/67DBRcW7XUft00BnqB0zbgfFhiiu' \
			b'CdWii555l7sI9pxKhrrfiX623A5OeocopwnygMBnro2ColM3FKvfORIv2LBnJAXpTnhqKf2DoHi6Z7uGFqhpwpGt5YghiwesF9BYXbwbz/ok+RASz/YNw7OV03AFjToXueU/HkIaVoOGDzFavxMmIh17OWLVwgMWYCURpBtgF2yYVmABGqMZ3VCbYaSe/3gz' \
			b'GB82S9ienv+oxyAvtGwd/6EnIC6uHOJRGy4+l1M4Cxe4h0GJupY0wgaNcOFpxNGzVhtux4cSeW5rwwV8xJIQOIKnu1cVtAJoGbQZGBpLIActArMGyoPWDxSs34H8oOP2aMSgdXo4xFZE5WzhP4Q3mAxqMhg6EFMNHR7wbjAW/gerCenDNbDxNWo8ROl2NWRU' \
			b'Q/+qLR5DKhX8rzEGnINOgtkxeA/k0eIeYkJxaihPDQWqoUQ1POPU8ARZg/rXYAhryLTGXDEv6IVg64C3NbRQDZa7h83u+nbXu13vdz2mtcNaQAYQH6xXDTaix4LAYVXDA8UOH3kB+BCjgohVi+YfHqdA1pAdisqTPerAqiOisW4V5FZhwrC3uIcboVXBDHR2' \
			b'B8LrsI3qXed3HZiDftdjuSEelBSqgaYeKIlP2tAp8QEFzDmYb0/Pr6BuYGdA1z09sYIB88ScmrQZbqrQzMEJHINYuxrBhU0K5WrwYR4OQf4kchD/M5Q7BqDsnsNlLCucWg7FGmAsrAVeBX3AYBTCc6I7Xn2FDwJ0TmkXnbkxnXnWs/BrljJKjaTe16JKrCMo' \
			b'XTytrexbuU3uI3HTXu6TGzGGY/0htSom6LbVCeXti6DvQ9ClR9+BoHEihx4LmmDxDVt4LwZenjF6U7Th9rUBxO2KnO9BziQB7Oct9X8lsK9pApqNgXUHFzGURxI1P/NRm6e3t61ECE+fFR0EuQZ5isxERkE6WhZKBqHdua1D4+rGfPcNqXR/rO8jPR9ruGj2' \
			b'cZ1OdZl1OKO7oq9aSbVyjtVypI6ggox71gfThgf7thMhEhlKQ2/S0M/IIlC/k75hnJzLUIxKSQFeOg+P2MedUMbtNQ/cM53QyqwA9TEau7mQgw0pV8XY34Wx54e8IuibF3SR8x3I+VkdR2uNPIq5MB9nyNjjyzYo2K7duSLv65e3CcB2gnLZyWxteGTr6bx2' \
			b'+KgCzeGxZbCF8Nka27MtunD1ugBSbouU70DKrkj5DqTsi5RvXcrP+jCbxgP7XgbuWF+eaamY22WC61EnuFyZ7LiH3oYV5P4l8180NFqlMFocNenp1+SAx8mZbZILj/QVz5W3Lrxv4/frp6TJ03mv0BH91CQamZVsZVxZlcnfLY2QLc4Td2CDQM7M+LYg5w7E' \
			b'/awV4tgwLSPzMlaQ0XF4x8Edj9/RSKO1xRduKBB0zyxvPt+5TX7Wyeu2Wh4XOiZfx28/u14cJCuZeDPh1ZnIuCFAPuOHy2dy1ojA+dW6kjC1DRoIfgX3TF6U07u/Xfr+rpWcHJfPcbEcF8vzuLGCaxWqRJfkUkS/EMeOzbRn4fmuNOoGjerZGnruCp67gu+P' \
			b'tW0whqWNl7Yxmw/P5qOriuKeDwIvIBDjLcPIRqAdXriVJ7o7eKJ7RWtsmudlVdU9yNqSqHG9VFNWQN2gfPG5mxe+FfnennxxAWMjS9xgXwR5rYKkRYmlh96iYGvum7SMFPtoEekNiJQel0QAZWHHhY5qeYE29b2ycPceeiYuxA/i5n0nj0d0XnrqpfZUXGhL' \
			b'goLkUXDFmfcOOmsjtrmtpLPKHKR10mkt99rRyi7p4lV4qpKVZKRApU9fUJ/GArEgW35cKkK5AKGYIBSeOhj3rkqucucsonpSUYlhNLUYSJGN4+5UZPLuZWIMy4Bfk8mLSPaSEEdnfivpgnszxS/ieWcDPlva+522d1va+x2an94GBHSy9LWXfTQ44itF4yT6' \
			b'4AH7buPKORpZ8UN372W8xQ8BRWiP2kmqqrTy439bhN9kY2KNLH1ozl+r8Kp83PE+ZiPkUz+4xIXUpyVDCe2NSl766rYWsSH8nLZIJ8z/NOy4IiCzPB1Ec0lfs9t5k7gfU6AtA6enEnnXymA2+/WGmpdtnZpFVlPqsJ6LtCD1ES1iW/rswp/o2lYw/DVuWm7Q' \
			b'8HKDhpcb0BSu5XxNPKOFBg0vNKDOLqeNOZzB6mSShL/cWah949Ru+aGvFf2QNwdOXveV/r5+VQj3xfIl1HvoPq9wLVXxG7xqCZKVK8buxIkZX9ru5LbrzlgEiqsPCdW+Kqg+dR1cV2z3NdtuXCzKfaApfeDUPmBK053adGXJyJWbD3kZ6NvSB06dlKxKH7jq' \
			b'PlCLixRcM7yMFXc4UfGcfqMWdyBeE37PzchCHPM8rOMw+vd+UN4mOpCzQ3k4N+JQLjfgDpTAiNeyeS5v59mxVTKk+agyi3LrSmg9C9y0rB3ycxbs+WqSn58wvehGI5omHy8nbz8j3n6sahLRSRK5Fyfoj8Y5UzegyZzy2fNbUCp0JKQp7bJm8DbEWQsj+vEH' \
			b'cO1EeJsLR8aY4AHWiOcXOWrbsizmVjTF2dLpb0GU6HNp2OfSsM+l9GgjPdqIvxruBfOtPDvyD5AV96NHGfa1wag25QO/G67hZP22smM1byvW547wV1yvnmSWwx4ZQdTBoc4EBy1xouhYjh2PeLuexszkl2P4PY/hL3OSeB3HolVjX9MnOtnGyRLPih19PJs6' \
			b'z5E9J+E5Qc/64tlkdmIcq2HobstEzfWikCdDbJxK+ZpnTexzeaL9ejfMvaBey0DY0qCW7Eh47A3DZhuWN7Byh7WmnZGbs26GUHXLOm1Zp215zroJ5TIk9jLTduuCdtxzefKsvPI4YZkMqHsrX1vAPWQTTm34WdwWP22EWt6UHnXzPQpbqAj8jgQOubb8DNTy' \
			b'MxBKf9fIsz2GOb5Uy1fMsVkdnddyXuM5peTKssbHHrx11PjQeo6ed9m9LixsMSQBvcqJxOX5o1c1f6UO0sRvpuMH0/E736UHX3UPpv7nUSU87zre9SJ1KIYvvfKRn6J8eDsrP/FQy48SUCejfspf1Kf+2xVxPLaR7EsjP/7niAw2Mum+DbrfiM4jZwpXrpsr' \
			b'kGPPIOlFqjxPV+1eVfiEuDM7S94lUDgcCUQN54bqRAM4dW4K9GkhUXNjs9DiaEIGGtw+XDt634Wayk3rQh117ahqUC8ovbQbtRNrHspRCxGLiAVMemDPComLFFC9qbdVg7Jgr6P36RBXf4ISn4fDwxS2K65uwN81w5/LQqWHvGv8ciX+SDn+hDX+wDGUocHP' \
			b'f4DGNLhkHYTf4JcqcGa8wmvQZujEhh/3wq8K4wd10G0MHdCwMRuUGIRjq+LsOrYr6hgoWYPfB8Nvg6EtweWyOIOPs/e4zAI/84ZfeINmbixKBPLEtfL4+URcJA/K2OCqyRa7H1yDxm/wkwctLtHAOHAvLrfFZ0j0T8c+DnrV4IIxXHiAS+nR3w2/J4MvNqE+' \
			b'Bupi6gpUZg9ihUbY19Cz91CDPbTyHkqxt3hc7fY9BFd4HQ7hP5qLPYpoj3LZG/xPwXALmoQ9KNce+/oeZbVHO7DHLrTHvrRHee2h3nu0BHs0BXvs/3uU5x4Fuq8pNWi6vcEzUK59jylidIcxQTp76Md7h5ehI++haffQxHtMjAqApcfeukeN2Xd4J4hs32NJ' \
			b'MFEsHObn8QoIa4/pQj/Yg5Zic+zxXhDK3mAFWqoARrVYjqrntkDjtkc7tkcjtkezwvXEEjcUE046bAeDtWzwEpYULoMy7rGuLYZhyqBde9DcPUhw7zEhLA0mRrfChR7rRWLAvKkgNV6ixoYDEh6VERsOM8W0a6oAheP9DhPEtqH2wTiQMOxR/KAbe9CNfY93' \
			b'VJgRFhbvQEGh1FAkmDpKFdukI2FR/SAGVQ+ueixVRXXCM4gHGrgHrdx7bHGsI8qEWgzSgWudkaLXpC5YDhQJtS5JDIreYapY9A5v6L9Gm4eWrti5YudW2Lli5IqRuyoj16CRmzJu/LTrlZVTT4yLbB1NGw+zyNro+Wm7d/gMO2v9Rk/r9FhuFhrCboUxrFOD' \
			b'iOP6A6O4xhj66zCI+Pk0/BZWNIw2YxwhHn5w5aiR9CghP2MOPf1LjCIFbGAYJelp8+iXGEhK42wj6WNF+1C/xUbSrzKTPjGUPmMqV1pIf3U2kqqBRRBj6TPmkoRw3GTu/sc9INP9A1K9h53p/hcXGZ1uR2m+Q08WZAxq+uJtbFbTaQWeFBAr65ShpRG/nqlY' \
			b'NXHAMwRT82dTljjx65PpDnpJ3yvjfDgnlkwVyYwF0py+DCZTIPSiQ09MJfNlMn2kp33CHJpM38TPmS8y9PK6BH9uGn8dGX/FNxp+iIc/bE4AgHg4bYO/nY0wwF/NxmmbraGAv2WCunQAB0gDNWoWEnYCFJXAojkTGPUADZxfxIUJER5mHiD4MTD8BBiBpFUw' \
			b'ge4B7WTAIDNYOgUXtDI01zfDF1Q22hLESCgZ3E6mIxvFGrqbJh0nYTPclEBnyC9yhzIX9MTLVHDGUIgfUERAcK3sBUl0gpOZuG96lcohm2qFJ1wbgoiq6akZuxKWuR2VJIesJILpk3NVy8AxaQvFMr7cSWN0IUY1lRLOpVqJLryrpeIBe1QzCaulFehYk5Dy' \
			b'6Vg3FAoP82MuhibQuuKDINfCkgs/T8uoIwkzg17MkVPijdhJjUNDoe5shnIHYIyGzhpwqppQE1XCcHlSH2onCQlddd8wXNxAWmZsYx7owc/UD6QCrn/AR7AOgqFnMoHRbj/gww7YtAd8hADbAufuf+mz/JdP5iVDIJcbBW3H4WZjFo85PGZw4G9h76OydxVz' \
			b'V/PWMW/dHG9R2xzFS4DrQihqmRxF2jqhrZumrdySsnZINLLWKdY6FSOwVuIfHfYN8TJsdZmhH0UdZZhFqo5g+uRcFQ4VoPKC1fEIkWN0Um3Z22oqrcpKDAGqUzB1MoxsRAQJRB0z1KUMPUheGCp1rnUDBAGtZujCWbko+5ShIu9ZhnK8MUPdhgx1u4OhqGq6' \
			b'hJ0c5oJY5ebATaXnLMKNudkWbr7r8Wth5h0w0zMz5+ZAUZFoS5EZQ1HJ5Cgi0wsy/TQy5ZYUmUN4RKaaGY2XqcyCTIl/HJnxrgwyfQ6ZnpGpM8wiU0cwfXKuKhNHoX6MSy+49IJLL7jMp1NZiSG49AqXXuHSj3HpGZfp7Oth8oJLqa8WvQ/CWY3LhRO0Ue4p' \
			b'LkXWs7jkeGNc+g1x6TO4HJouwSWHuSBWuTngUuk4i3BjXLozX6RNgvI2EHkMjwWNBY2IRnKbwAaaQWPcEjRK0OE7Qgqlxp/E4giIQwYRiJSbADEpggAxxD8KxOGuQyBiqAYiqm14e5hkmANi2ih9cq4qk3+9yJc6qa+8ZJxIobK8FxTicUAhVUBQyEllXkQ2' \
			b'qcvGKH2qs+tjTZNqB7GsRSGXdx6FUeIJCoOU51Ao8UYopDbZCIWsxikKlWQ0CiXMBZnKzYJCrd0swhEKxwhsHujpLDCwqx7ooSUDQV8gWCBYIHgWBBuGYDMHwUa2FIIclIFgIxBc7CkzZDBAsFEQbFSMAEGJfxyC8a4MBJsUghSrlUGhU7dmIahLZPrkXFVm' \
			b'AoLiZsP1DRDMp1BZ3gcINgqCjYJgMwXBJoXgYRYulJ4YONQ6SGU1A5uFDAwCTxkoQp5lIMcbM7DZkIFNhoGDYBIGSksGkcrNgYFKuVmCmzGwKwwsDCwMPIuB7MfTzPnxYKPQljKQgzIMFAeeZtqBZ8zAmMHAQOW4Ey83g+NOiH+cgfGuDAOP+ZEmOWYhqCOY' \
			b'PjlXtZmAoDjnNK2GYD6FyvI+QLBVEGwVBKdcUpvUEecwfZ4VDVXVwvZBMKsxuNARJ8o8xaDIeRaDHG+MwQ0dcRrliBMxODRdgkEOc0GocnPAoNJvluFxDAr+MtTrC/UK9Qr1zqIee9M0c9402CC0pdTjoAz1xJGmmXakGVMvZjBQT7nQxMvN4EIT4h+nXoyX' \
			b'oV7OhSZST+eYpZ6OYPrkXNVmgnriPNM4Tb18CpXlfaCe8pxplOdMM/acidRLXWcO0xfqSVW1sH0QzGrqLXSdiTJPqSdynqUexxtTb0PXmSbjOqOaLqEeh7kgVLk5UE/pN8vwVOrV1QVh78wFdY8HvKXr7e4ZYlNr9jaA1xpoHQDrAFI9Q6qfg1QvWwopDspA' \
			b'6oSlfEMWA6Z6halexQiY6ucYhf1d7lmzvo+VcPifp5QukemTc1WZ5YsAKXp+FSD5o4wXQUQK9SOPlE4yj8UfnFLoEnuldMOpjYdrYdQvhFGQbAojkeYcjKZXEW7BoX7AT2y1EX+4nGEpIddErSbEgBFzAmQUXOoLgssW6wgveHx16ysH8T2vLeOu7LjL8Gyj' \
			b'mZttxM5DW4I0CTpEmpHZRrN4tnHIIALNqNnGeNkMs40hfmAanjgOC2QzDDfcNb1K4RBv5hjhktxzdEsimD45VzXL083IzKPRM48TKVQ2Hgr75DQQ0PD8oxEOxjbNkNCks5CHeTEGQ7W1EvhYjJUINNOzkGGpbILCWP4EhUEP5lAY2iaFodlwNtJkZiNVE2ou' \
			b'SpgLgpabBY1a/w0X8dRx2bmfNSnoLOgsU5XTyOSpSjM3VYk9hrYUmRyUQaZMVZrFU5VDBgMy1VRlvGyGqcoQPyLTMTKdQqZjZDpGZrwng8xj05ZJ7llk6gimT85VzSaQKdOWRk9bTqRQ2XgYkMmnEZk8eUkxYpUnkJlOYR7mJciUamsl8LEYa5G5cAozljtF' \
			b'pch/FpXSJiNUbjiFaTJTmKrpElRymAsClpsDKpXeGy7iqag848s15c1deXNXcAg49IxDP4dDL1uKQw7K4NALDv1iHMYMBhx6hUOvYgQcSvyjs6LDXRkE+mMI1DlmEagjmD45V7WZQKAXBHqNwHwKleV94J9X8PPDpCknlcOeT7F3kL5gT6qqhe2DYFZjzy/E' \
			b'XpB5ij2R8yz2ON4Ye35D7PkM9oamS7DHYS4IVW4O2FP6zTI8GXtnfBamYK9gr2APsNcx9ro57HWypdjjoAz2OsFetxh7MYMBe53CXqdiBOxJ/OPYi3dlsNcdw57OMYs9HcH0ybmqzQT2OsGefiE4kUJleR+w1ynsdQp7U68KqfIKewfpC/akqlrYPghmNfa6' \
			b'hdgLTZBiT+Q8iz2ON8ZetyH2QgU19oamS7DHYS7USG4O2FP6zTI8GXtnfNXFzZHv6b5QesEgPGd6FOXhCiCvFpD07f8a+8NxQNqwJYCUoABIPhZG0kld8T7PSLqUYHLIJmKS8hRMWl0QwWSIHzBpmZS0E1hSElySplcpHCITQyeRmeSeQ2YSwfTJuapZHpl8' \
			b'SRoxIHMihcrGQ6GmnAZwUj24OnWsMuEzHI4gSs0xQPQwR4ZoqHzSErEwKyHK5Z+HaCx9AtGgBXMQDS2TQpQaaCOIsqanEFVNpyEqYS6IWW4WiGrtN1zEUyFavvVSxo4FjeehsWE0NnNobGRL0chBh2NHCkWrsdiLdMhggGKjoNioGAGKEv/o2HG4KwPC5hgI' \
			b'dY5ZEOoIpk/OVW0mQCiepFzhAMJ8CpXlfaBgoxCo/Ew5qczYkSqvsHeQvmBPqqqF7YNgVmOvWYi9IPMUeyLnWexxvDH2mg2x12SwNzRdgj0Oc0GocnPAntJvluHJ2CtfdynYK9g7D3v8i3C4O449I1uKPQ7KYM8I9sxi7A2pRewZhT21RexJ/OPYi3dlsGeO' \
			b'YU/nmMWejmD65FzVZgJ7RrBnNPbyKVSW9wF7am0F1SBgz0xhz6TYO0hfsCdV1cL2QTCrsWcWYi/IPMWeyHkWe9IaI+yZDbFnMtgbip1gj8NcEKrcHLCn6sr7k7FXPuhSsFewdx722EHGzjnIWC9bij0OymBPHGTsYgeZIYMBe8pBJl62g4NMiH8ce/GuDPaO' \
			b'OcgkOWaxpyOYPjlXtZnAnjjIWO0gM5FCZXkfsKccZKxykLFTDjI2dZA5TF+wJ1XVwvZBMKuxt9BBJso8xZ7IeRZ7HG+MvQ0dZGzGQUY1XYI9DnNBqHJzwJ7Sb5bhydgrX3Qp2CvYOwt7aJShwLg7ij3UeNrS33qoqC9kuEehNd+xjHtDDpF7lJ1wL16mojL3' \
			b'Qvyj3BvuOuQerbme4l6SY457SQTTJ+eqNnnu8aVOKizcm0ihsrwX7uFx4B7VQLjHSWW4R5UfuHeYPnMvVFVL2wfBrOUeF3iee1HmCfeCnOe4J/FG3NtyKT0rcso91XSaexLmglBDzZh7Wr9Zhqdyr7mkT7oU7hXuXSP32O+lnfN7acOWcE+CMtgTp5d22ull' \
			b'jL2YwYA95fHS6iIE7En849iLd2Wwd8zLJckxi72kVfrkXNVmAnvi5dJqL5eJFCrL+4A95d/S1gp79RT2Up+Ww/QFe1LVpN5BMKuxt9CnJco8xZ7IeRZ7HG+MvQ19WtqMT4tqugR7HOaCUOXmgD2l3yzDk7F3qR+bKdgr2LsW7LFPSzvn04K6TluKPQ7KYE98' \
			b'WtrFPi1DBgP2lE9LvNwOPi0h/nHsxbsy2Dvm05LkmMWejmD65FzVZgJ74tPSap+WiRQqy/uAPeXT0iqflnbKp6VNfVoO0xfsSVW1sH0QzGrsLfRpiTJPsSdynsUexxtjb0Ofljbj06KaLsEeh7kgVLk5YE/pN8vwZOxd6odiCvYK9q4Fe+zT0s75tKCi05Zi' \
			b'j4My2BOflnaxT8uQwYA95dPSqi1iT+Ifx168K4O9Yz4tSY5Z7OkIpt+N7oltk8ee+LS02qdlIoXK8j5gT/m0tMqnpZ3yaWlTn5bD9AV7UlUtbB8Esxp7C31aosxT7ImcZ7EnrTHC3oY+LW3Gp0U1XYI9DnNBqHJzwJ6qK+9Pxl756EvBXsHeedhjn5Z2zqcF' \
			b'lZu2FHsclMGe+LS0i31ahgwG7Cmflni5HXxaQvzj2It3ZbB3zKclyTGLPR3B9Mm5qs0E9sSnpdU+LRMpVJb3AXvKp6VVPi3tlE9Lm/q0HKYv2JOqamH7IJjV2Fvo0xJlnmJP5DyLPY43xt6GPi1txqdFNV2CPQ5zQahyc8Ce0m+W4cnYKx99eVLslU+A3g7+' \
			b'HPu2uDnfFvymA20J/iToEH9OXFvcYteWIYOIP6dcW+JlN7i2hPhH8TfcdYg/d8y1Jckxh78kgumTc1WbPP6cuLY47doykUJleS/4c8q1xbFrC12Olc1D0KUOLoe5MARDhbXIfRDPWgi6hQ4usdwJBIO05yAo8UYQdBs6uLiMg4tqOg1BCXNBtKFmDEGt5SzJ' \
			b'kyF4xidgCgQLBAsEFQT5jZ+be+OHnzSiLYUgB2UgKG/83OI3fkMGAwTVG7942Q1v/EL84xCMd2UgeOyNX5JjFoI6gumTc1WbCQjKGz+n3/hNpFBZ3gcIqjd+jt/40eVY2QkIpu/9DnMRCEqFtch9EM9qCC587xfLnUJQpD0LQY43huCG7/1c5r2faroEghzm' \
			b'gmjl5gBBpeUsyZMhWD7hUiBYILgNBPn9n5t7/4eKTVsKQQ7KQFDe/7nF7/+GDAYIqvd/eosQlPjHIRjvykDw2Pu/JMcsBHUE0+9GpYxtk4egvP9z+v3fRAqV5X2AoHr/5/j9H12OlZ2AYPoW8DAXgaBUWIvcB/GshuDCt4Cx3CkERdqzEJQ2GUFww7eALvMW' \
			b'UDVdAkEOc0G0cnOAoKor70+GYPmgS3kLWOB3AD84B71pQHFWvhF0/EbQzb0RdLKlbwQ5KPNG0DEI9yt+G3fIYngn6AiFqKrxKhVVXglK9Nlfx5WImXeC7ggKSWPV//x7QV0u0yfnqkYT7wUd45ArHd4L5lOoLO8Fh6iOw4tBR22055/Q7SdQSE0woBAjcuKx' \
			b'gsNP6LIIqUurUxsP174gdEeJSIU3gz6N3g+K0OeASE2S+RXdoXU2eEPoUiQOqskNmLwi5HI7km9DRYZcmY5cTXlZqBTfsEqmdLRARXwaFCxCT3rAxx+wbA/0LAHm5wGhDybjgX7iV/HyUr8EM/ps9nVTM/fB7DJ8vC6Crho+tjx8bOeGj61s6fCRgzLDx5ap' \
			b'Sftlw8eYwTB8bNXwsVUxwvBR4gdoEjM57GAQGe/NDCLbY4NInW92EKkjmD45V3WaGES2TE2udhhE5lOobDwM48hWjSNbHkeKT01sytw4sk3HkQcZyThS6qxl72MZ1o4j26PUHMaRodwJNoPYZ8eRHG88jmw3HEe2u8Nx5NB0yThSNDFIV24O40il7izJk8eR' \
			b'l/qpmMLFwsXr5SL7l7o5/1L8fRTaUi5yUIaL4l/qFvuXDhkMXFT+pfGyG/xLQ/zIRc9c9BkuxnszXDzmZZrkm+WijmD65FzVaYKL4mXqtJfpRAqVjYeBi8rR1LGjKV2O9Z3gYupuepiRcFHqrGXvYxnWcnGhu2ksd8pFEfssFznemIsbupu6jLuparqEixzm' \
			b'gnTl5sBFpe4syVO5aC71UzKFi4WL18vFjrnYzXGxky3lIgdluNgJF7vFXIwZDFzsFBc7FSNwUeJHLnbMxS7DxXhvhovdMS7qfLNc1BFMn5yrOk1wsRMudpqL+RQqGw8DFzvFxY652AkXQ5o5LnYpFw8yEi5KnbXsfSzDWi52C7kYyp1yUcQ+y0WON+ZityEX' \
			b'QwU1F4emS7jIYbFGcnPgolJ3luTJXLzUb82Unx8shLwBQnpemuHnlmagRtOWEFKCDgnpZWmGX7w0Y8ggEtKrpRnxsh+WZoT4gZB4Ah2RdkJISoKjNb1K4ZCT/tgyjST3HCeTCKZPzlXN8pz0skzD62UaEylUNh4KJ+U0oNLzYg0vizVim2ZQ6dPFGod5MSpD' \
			b'tbUS+FiMlaj0CxdrxHInqAzyn0NlaJMUlX7DxRo+s1hDNZ1GpYS5IOBQM0al1nvDRTwVlZf6fZqCyoLKW0Blzais51AZthSVHJRBZS2orBejMmYwoLJWqNRFCKiU+BGV7LRDu4DKmlFZMypjChlU1sdQqXPPojJpoT45VzWbQGUtqKw1KvMpVDYeBlTyaURl' \
			b'zaisBZWhTXOorFNUHuQlqJRqJ20Qi7EWlfVCVIZyp6gU+c+iUtpkhMp6Q1TWGVQOTZegUjQzCFhuDqhUem+4iKei8lK/aVNQWVB5C6i0jEo7h0orW4pKDsqg0goq7WJUxgwGVFqFSh0joFLiR1RaRqVVqLSMSsuojClkUGmPoVLnnkWljmD65FzVbAKVVlBp' \
			b'NSrzKVTDYUAln0ZUWkal+LrGNs2h0qaoPMhLUCnV1kqgKrsSlXYhKkO5U1SK/GdRKW0yQqXdEJU2g8qh6RJUcpgLApabAyqV3hsu4qmovNTv4BRUFlTeAirZpdXPubSiCtOWopKDMqgUl1a/2KV1yGBApXJpjZf94NIa4kdUskurVy6tnt9S4q7pVQoZVB5z' \
			b'bE1yz6JSRzB9cq5qNoFKcWz12rF1IoXKxsOASj6NqGTfVi++rbFNc6hMfVsP8xJUSrW1EvhYjLWoXOjbGsudolLkP4tKaZMRKjf0bfUZ31bVdAkqRSWDgOXmgEql94aLeCoqb+5rOU+PxDlvnSXoE+xF3AXUCeKuEm9XgTZe4+jn1jii7tGWoo2DMmiTNY60' \
			b'X4a2mMGANqfQ5lSMgDaJf3SJ43BXBmfHVjjmEaaLYfrkXNVgAmGyotHrFY0TKVSW94FfTsHLyZdOs7hK1zHG5IRSvG7R83pFv36toj++VnEgUxBlSiYR3yyZON6YTE7IdCaURqsUCUqSoRtTicNdkJncHaikVJZFtIZKRKNL/WxNGbiVgdstDNzYt9TP+ZZC' \
			b'BN5SunFQhm7iW+oX+5YOGQx0U76l8bIffEtD/DhwY99Sr3xLKQkuRtOrFDKkO+ZhmuSepZ6OYPrkXNVsgnriYeq1h+lECpWNhwF8fBrZx06mXpxMY5vmSJg6mR7mJUiUamsl8LEYa/G40Mk0ljvFo8h/Fo/SJiM8buhk6jNOpqrpEkRymAs1kpsDIpXeGy7i' \
			b'qQO3m/u4zdMjsQzcrnjg1jPa+jm09bKlaOOgDNp6QVu/GG0xgwFtvUJbr2IEtEn84wO3eFcGZ/3qgZtO0PTJuarBBMJ6QVivEZZPobK8D/zqFbz6YwO3PsVVSE4o1TOieoZTv55M/UIyBVGmZBLxzZKJ443J1G8zcOszUJIMDwZuHO6CzOTuQCWlsiyi1QO3' \
			b'S/10TKFRodET0Khjv8tuzu+yC1tCIwk6pFEnfpfdYr/LIYNIo075XXa6CEKjEP8ojYa7DmnUHfO1zNIoKYbpk3NVgzyNOvGv7LR/5UQKleW90KhTnpVdfYRGXepLGZNjGnXsP9mx52S33m2yW+g2GUWZ0CiIb45GEm9Eo67ehEZdxmMyZDimkYS7IDO5W2ik' \
			b'VZZFtJpGl/rBlvLhzzJVeC0EYx+Pbs7HA1WTtpRgHJQhmPh4dIt9PIYMBoIpH494uRt8PEL84wSLd2UIdsyvI8kxSzMdwfTJuarNBM3Er6PTfh0TKVSW94FmyqOja3fx5/+mqZb6chymL3iTqmph+yCY1ahb6MsRZZ6iTuQ8izqON0bdhr4cXcaXQzVdgjsO' \
			b'c0GocnPAndJvluGpU4L2Ur/HUrBXsHct2GP/j27O/wP1krYUexyUwZ74f3SL/T+GDAbsKf+PeLkb/D9C/OPYi/Ey2Dvm/5HkmMWejmD65FzVZgJ74gvSaV+QiRQqy/uAPeUL0jmFPTeFvdQn5DB9wZ5UVQvbB8Gsxt5CR5Eo8xR7IudZ7HG8MfbchtjLeIuo' \
			b'pkuwx2EuCFVuDthT+s0yPBl7l/q5lYK9gr1rwZ5n7Pk57HnZUuxxUAZ7XrDnF2MvZjBgzyvseRUjYE/iH8devCuDPX8MezrHLPZ0BNMn56o2E9jzgj2vsZdPobK8D9jzCnteYc9PYc+n2DtIX7AnVdXC9kEwq7HnF2IvyDzFnsh5Fnscb4w9vyH2fAZ7Q9Ml' \
			b'2OMwF4QqNwfsKf1mGZ6MvUv9dErBXsHetWCP/SG7OX9I1EjaUuxxUAZ74g/ZLfaHHDIYsKf8IePlbvCHDPGPYy/elcHeMR/IJMcs9nQE0yfnqjYT2BMfyE77QE6kUFneB+wp78euU9ib8nvsUr/Hw/QFe1JVLWwfBLMaewv9HqPMU+yJnGexx/HG2NvQ77HL' \
			b'+D2qpkuwx2Eu1EhuDthT+s0yPBl7l/oZlIK9gr0rwR72Zigw7o5iD/WPtgR7EnSIPQqFxqf9IuwNGUTsUW6CvV7HEOyF+EexN9x1iD0MncRekmMOe0kE0yfnqjZ57PGlTios2JtIoZK9YA+PA/aoBoI9TiqDPar8gL3D9Bl7oapa2H6o4DrscYHnsRdlnmAv' \
			b'yHkOexJvhD1qlI2wx4qcYk81ncaehLkgVLlZsKf1m2V4MvbokyZAnYK+s9AH16EtrgeBpmDw0TCIRLDo5mIIh9gfj/MQOwZtCQ8l6JCHVni4X/HDtlQmx/8jE61iYiyDHZgYSjD727YS8RCK9hgUkyxzUJRLVEweDepbhnsnsGgFi1ZjEbWntqS5uZQq2Qse' \
			b'rcKjVXi0U3i0KR4P02c8hkpr2ft4hJmvRKRdiMhQjhSRQexziKTaHS48sBsy0mYYKcU78PeUcBdELHcLJFWrc8U1JOEUGInXDf21+BdoCX97R38pDhLTkn2AHfGyhf59hJYRkgqPM2xkJDIPmYFT9NPcm11ZQHzLQ6wf4EVgClAKQJpaBaAAFGFjxeN/LVBm' \
			b'YHIAkTl45MBxrlf/GBZjSFgBQ4CC02MhtwIAid3PWPzV5n6w8dHAB6O+wJxnDPlKx/tgr6dMM9nlwSiT3Y1GN1rcab95bWOjUd3LJ4ZPsZ+LjOfYbM4bzJy13MIr/sBEHhrHffgxmmgQyQ4GI4i2zB23Ze0jm7N6pUULD+2oLMsMW5cxbq4YOG3gonHLPAWD' \
			b'0g1PwhAHf9adnoghHtiDpusSA9hge/Q4FgT1gPYw0B5sFL1+Qob/NRjIdY/I9OB6YVbSZp3d1lpK9XTbkPlYYTGtcleLVhNVo1jOKcuJyh2NJrbfgeGkGDJW4sFfMKbYT0TfU8s6jAWxKPSp2fC5on1NH2n30fLiSQvPoND7HrBF6anSH7fE7pIeLAczjJMl' \
			b'7ZM/Y9Z9f97ExUWYYnvic+b1m9FNTSh12qpeZ0Yf/8ETUXvEhNorNKP9ec+e3XGL5y/T4rknt3ZX/cBZLNwWD4nNpVm3m3k4PMui9QtnBuuLsmhbzxHW92fVTp4jXGnZEqtGff/WLNv0u5yzLRsN1u/bujX0qcYTLRwOWM0DVADHq1CgZbauOc/WHfEEOM3c' \
			b'UUGXmDt32kMcvpO/VpMH9b24h7l3bfLsk5g9t8rsoXBPfqizt2L6Gvrlj3f1cAcC3/q1b/NoD3dWG7wZY9e0G45Y6+sxdhdt6LYwcomjz1M927l0bm6ZkWuoCbYcuaIUr9LIvUMD1zyhX0t18uPcKSPXtszHXbVlu7CXtueNWFGcZT7uUSyaeUKLdrJry0kW' \
			b'rbi0FIt2QRatKxbtcSya3b26QL/jI4tt3rEP8iXbMvcEPsjKnvX9tZizNaaMP0JveH0TXrw8X+RrMWcN/Zz7SSbtbF/k3f/0DwBcerPQXqSNO8muGSw5Lgjs78TGnWLfcDXq6c9t1/i89q4XV/CiTKwsFuk+rduJL0y51c6wbGjR3A1ZNCg/FA4V5aItW3YZ' \
			b'8lNYNziH+q+3cnrxRLpooli8JRYPex+tPN+jDl6N5XMXZPz2KDjMyq23gbjaRy2B0Asf0CL6R7OI1SMYxclvQWjD6J7YKLYnPvLZ8th3jhFEAT6RJcScF5pDTAPV7RKMYePMGY+C2HGectXtKcbw4IGwezTzVz/FM6E2e9VlPg8Ws3czZm/hHF5i7RrqpZf/' \
			b'+HeT1q5/NGvXPLW1q4u1K9buAq2dL9buiawdFPSxrJ15amvXFGtXrN0FWruuWLunsnb17bzauArTdj0OdRdjzi7akj2W2Wqosrf0KvYM35Iav35ds3sJlLJYrBu3WFu5zN2Y5aJPkF285bpBL5It/OM68wDkIQtmigUrFuzeLBiNli7l0YsKU+zXKvuF37o0' \
			b'1HUf0P6TJbvM5QzFkhVL9qiWrL8kS9YXS7aBJbuERQtrfwjpDMPm1Q8W3YKBax7ZyDVi6MwdGDvq9anBa4b1WvT7VsP/RzSAXA5qtn6RJWyuyxJu8FM7C8xhg9Wnvt2cYBYvYeVDMYvFLF6EWTRjs2iUWUz/P6pZNOvMoilmMWcWGzGL5gSz+HjLH4pZvAGz' \
			b'eD8m0Y5NolUm0Sb/H9Uk2nUm0RaTmB84U9OsNoePtxyiTAOWacB3Y+8ov9v0JblIm/b084DOogXjV7KPt8ShWLBiwba2YGyW7skdbjMThs0R/l+/CWvbB6QZ9C98KsM+9oD2GfoZ7Mmy+cdbzlAsW7Fs21s2WyzbqZbNxv93YdnK0oVi2dCqVfSOCyd0L9zK' \
			b'kYZf32oG/g3kJzVyVITNBqBSoe1sHCWYtXENiRsuHrd2tn8gBIJCPSBToBM+kGGHHvSAJhm0H/aG7F5ZAFHs3sU/0VH3ukZb9+QPdFSEDW1du7Wta095nltl4coCiWLhLtXC0cu4+16beqKF49eYN/s6waJBw25U4xC1cWTJygKJYskuxpLV9DXdssr+REvG' \
			b'zXcHL0Ytzrmh2td00JAlu4QFEsWS3aMl4z5aPhiykSmT5rwTJw9jH5CE0Pdgz+8NLmFNQ7Fkt27JuO9dyprVWzRk9+WtZvBZrKZPIPlLWH5QLNitWDDS4EtcXnDVFoxatRiwwYCRJweagr7DAx5VlpUDxZKdZcnIplz8QqmrtmTlWWxsympcOdDUZMHKyoFi' \
			b'wc60YE2xYMWCPZkF68oKgWLBVlgw0vNLW71ZTNj9mTAcT9IosruhlQCgvvE3mi/RmkGDXtxvM1/Y+8pbsmoo8z3eeRX2Dat6SVYOBXa6iUPL1uxeUS9pUWNRfxpv6ILZvfL4pR8Ix6rAfwq2Ohg/11NTcLt71UChmg5/gbzp0Ar6r5/D8bM92E7sDhRvD9mB' \
			b'ycLMwJz0DYUZDENzBdYDDQD07x1oASghqCDoJDQCCBUaGk1MhVYXTA6E4I9HNxV2RSh1zByugx6hXmMzolpgD6obdK+Bc5AC6iT2L+xBNagHzhj2chd0aoudH1ME44B+xB39IDXo6JaltLvF/yj3FnP3S/MHZUQzXFULStIiNdrJf3VvxL678TUqmDteMFB4' \
			b'/MHtmn6J0RwrZ81lxV/SHpc3IgGX56EJNqM6AC8P/pErLTqFqv8HcSB3l1zBu9DkYxj9VBd0ELpClfVPXlngTIs/nQ6VhoeBzf4ZKI2puYt251eSutN0PWswcjV0r7rDZ4UqX29XH6k7PPks/odPJmkIPwNY4X1yBUqnzqk9+mx7NIj56VZx2DD4BEdtgxZT' \
			b'fThtsqkaaS4vvyjfkS8NugWiazOa7lpWvvAXBiw3K2SLUKUvplITt0Mze2x2SAv0mJscrkFBqOm7frr5IR96pEJEa1HgI1AQB9zPIoHHXbCepgriQYN7uNGTqM9dGa5XOkq4Qf9fcGfutkwymdPDbKuJOLl6JVfT5MaxSLEg9PJ7Gg0nLmHjJqvznRGf43c4' \
			b'QqBeCY9+8Hi5om+a07qnVV20WddNaVR1EV212WU2PYiUwDB8XLz55VFpw5GhHMkA+3h08jR87I21rikIWK1XZnevG+uMuQbjbneXsXGT2W26WfP0Pa16172t222w4TTfJgk9RU6sQvlxcrHUx3QHE77PjXVmgymMrGJsba1xRnyjjWfoz9m46fITIqW7Helu' \
			b'OFa50411Jj+/BDpzfo/zj9Hr7O5wwwn27IWlW2XOuZ8bcmJiKo6CZ4fA1Q56hWt37h11R6+6ZCPdspLxMMRxWBF3Kd3U7w43HPLLEbZ0LsrTbxar7N5BVvxCJz+JVRBwTLfw1fF9bqwzE7N4l4oAdOe4rI2b8YxpqQsz/RfRLZGZJ23kQ6P+n5zQTB7JUbp7' \
			b'5I31LT+ltdbUP5Z5X9Pdp/RkXkeaXXZDt4upaxKjtTMxHmNbmCvLd6P5t3tCOTr43enGOjM54bYZylE3tsW53T3Sho6Np97MzZmfiypd8FgX7Hf3urHOTE7CbdoFUTc27YboDP1oG7oXn3ozt+rkNFXpiVM9ER3b73RjnZl0Fdu8JzZ2697odo+6oZ//qTez' \
			b'l3CZaFrfIbvdvW6sM6dPNJ0xUCVVWNk3pwaiQ//sd6dtuGBkeWxchmN55cx8XN9kL3DTF5+p1d0VF4Pd6cY6MznB9JjdNVGPx+i6uMDvnWx6zdx5SbE4rmg+6NLmknFF5+Vt+MPktLPvIDfWofXzQ277Xq01ZqPePS35frdqwyWWa+853MKS2NMTgPaFnVrC' \
			b'CqcswjPmpPg107t+wXSJBgEXd5+0UdWgaU9O4MiGi6cfI925jfVq/bzVlZsGXNp/9RvL7ozZsfLqOaMZbnfOxhUzZ6Uxu+HXFR41g4ONVW39pNojm4kT3zevNxf97gk3VOYN4/Ea+jPm8IrZONQQ/D5M2ZKN9Wxy3q/o2Ul6ZnZlSzfWs20mOS+FUCd5ROF3' \
			b'qW5tY+EWd7dX+LmxW9tYuFc0t3kprydwYe3ZG6+NHf5vluiwG+WiTpM4i5LMbaxAZaXpegUyu3vdWGeKd996nbG7e91YZ8oS2/U60+/udWOdKb6Lq3UGv6R7pxvrTPnM3XqdqXf3uvFHSYtL5nqdaXb3urHOnDE1e7c6Y3b3urHO4Eeq6YvTDT/ggEpIgCyF' \
			b'bi0GYLNTYI2fbucLMEzXmgSKQDFAZBYXtKB/BX56kD3eQM+ysUG46X+O7Q9io8DpDlSv9H8j78BAs4YvaLeoNvyes+05PP16GccABYGmwPgdf5gfVZJUsCW1Q7XCcFAd/igzGOYkFVLldqS+QXXRkxe/yM2f9ocWkc/686fzu9Hn8sOn8nE1Pw9RQJ9fYacB' \
			b'Jafv26BqMyAg2+Sz4HBfx35hzuB5g6HyAOIsHre03F7ubocQMB5fP///uqCkuw=='

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
	_VARPY_QUICK   = fr'(?:{_PYGREEK_QUICK}|{_LTR}\d*)'
	_VAR_QUICK     = fr'(?:{_VARTEX}|{_VARPY_QUICK}|{_VARUNI})'

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

	def expr_abs_1         (self, L_BAR, expr_commas, R_BAR):                          return AST ('|', expr_commas) if not expr_commas.is_comma else _raise (SyntaxError ('absolute value does not take a comma expression'))
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                            return AST ('|', expr_commas) if not expr_commas.is_comma else _raise (SyntaxError ('absolute value does not take a comma expression'))
	# def expr_abs_1         (self, L_BAR, expr, R_BAR):                                 return AST ('|', expr)
	# def expr_abs_2         (self, BAR1, expr, BAR2):                                   return AST ('|', expr)
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

	p.set_quick (True)

	set_sp_user_funcs ({'N', 'O', 'S', 'beta', 'gamma', 'Gamma', 'Lambda', 'zeta'})
	# _SP_USER_FUNCS.update ({'_'})
	# set_sp_user_vars ({'_': AST ('-lamb', ('^', ('@', 'x'), ('#', '2')), ('x',))})


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

	a = p.parse (r"\mathbb{N}_0")
	print (a)

