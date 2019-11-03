# Builds expression tree from text, nodes are nested AST tuples.

import ast as py_ast
from collections import OrderedDict
import os
import re
import sys

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

_SP_USER_FUNCS = set () # set user funcs {name, ...}
_SP_USER_VARS  = {} # user vars {name: ast, ...}

def _FUNC_name (FUNC):
	return AST.Func.TEX2PY_TRIGHINV.get (FUNC.grp [1], FUNC.grp [1]) if FUNC.grp [1] else \
			FUNC.grp [0] or FUNC.grp [2] or FUNC.grp [3].replace ('\\', '') or FUNC.text

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
def _expr_ass_lvals (ast): # process assignment lvalues
	def is_valid_ufunc (ast):
		return ast.is_func and ast.func in _SP_USER_FUNCS and all (a.is_var_nonconst for a in ast.args)

	if ast.is_ass: # if assigning to function call then is assignment to function instead, rewrite
		if is_valid_ufunc (ast.lhs):
			ast = AST ('=', ('-ufunc', ast.lhs.func, ast.lhs.args), ast.rhs)

	elif ast.is_comma: # tuple assignment? ('x, y = y, x' comes from parsing as ('x', 'y = y', 'x')) so rewrite
		vars = []
		itr  = iter (ast.comma)

		for c in itr:
			if c.op in {'@', '-ufunc'}:
				vars.append (c)
			elif is_valid_ufunc (c):
				vars.append (AST ('-ufunc', c.func, c.args))

			else:
				if c.is_ass:
					t = (c.rhs,) + tuple (itr)
					v = c.lhs if c.lhs.op in {'@', '-ufunc'} else AST ('-ufunc', c.lhs.func, c.lhs.args) if is_valid_ufunc (c.lhs) else None

					if v:
						ast = AST ('=', (',', tuple (vars) + (v,)) if len (vars) else v, t [0] if len (t) == 1 else AST (',', t))
						vars.append (c.lhs)

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
	if args.is_var:
		return AST ('-lamb', lamb, (args.var,))

	elif args.is_comma:
		for var in args.comma:
			if not var.is_var:
				break
		else:
			return AST ('-lamb', lamb, tuple (c.var for c in args.comma))

	raise SyntaxError ('invalid lambda function')

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
	def process_func (ast, arg, tail, wrapa, make):
		if tail.op not in {'{', '('}:
			arg2 = _expr_mul_imp (tail, arg)

			if arg2.is_pow and (
					(arg2.base.is_func and arg2.base.src and arg2.base.src.is_mul and arg2.base.src.mul.len == 2) or
					(arg2.base.op in {'-sqrt', '-log'} and arg2.base.src_arg)):
				return make (wrapa (arg2)), AST.Null

			ast2, wrap = arg2.tail_mul_wrap

			if (ast2.is_attr_func or ast2.op in {'-func', '-idx'}) and (not arg2.is_pow or not arg2.base.op in {'{', '('}):
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

		elif arg.is_paren and not tail.is_diff_or_part and arg.as_pvarlist: # var (vars) -> ('-ufunc', 'var', (vars)) ... implicit undefined function
			ast = wrapa (AST ('-ufunc', tail.var, arg.as_pvarlist))

	elif tail.is_func: # sin N 2 -> sin (N (2)) instead of sin (N) * 2
		if tail.src and tail.src.is_mul and tail.src.mul.len == 2:
			ast, arg = process_func (ast, arg, tail.src.mul [1], wrapa, lambda ast, tail = tail: AST ('-func', tail.func, (ast,), src = AST ('*', (('@', tail.func), ast))))

	elif tail.op in {'-sqrt', '-log'}: # ln N 2 -> ln (N (2)) instead of ln (N) * 2, log, sqrt
		if tail.src_arg:
			ast, arg = process_func (ast, arg, tail.src_arg, wrapa, lambda ast, tail = tail: AST (tail.op, ast, *tail [2:], src_arg = ast))

	elif lhs.is_pow: # f**2 N x -> f**2 (N (x))
		if lhs.base.is_func:
			if lhs.base.src and lhs.base.src.is_mul and lhs.base.src.mul.len == 2: # this only happens on f**p x, not f (x)**p or f x**p
				ast, arg = process_func (ast, rhs, lhs.base.src.mul [1], wrapa, lambda ast, lhs = lhs: AST ('^', AST ('-func', lhs.base.func, (ast,), src = AST ('*', (('@', lhs.base.func), ast))), lhs.exp))

		elif lhs.base.op in {'-sqrt', '-log'}:
			if lhs.base.src_arg:
				ast, arg = process_func (ast, rhs, lhs.base.src_arg, wrapa, lambda ast, lhs = lhs: AST ('^', AST (lhs.base.op, ast, *lhs.base [2:], src_arg = ast), lhs.exp))

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
		numer = ast.numer.strip_curlys
		d     = e = None
		p     = 1

		if numer.is_var:
			if numer.is_diff_or_part_solo:
				d = numer.var

			elif numer.is_diff_or_part:
				d = numer.diff_or_part_type
				e = numer.as_var

		elif numer.is_pow:
			if numer.base.is_diff_or_part_solo and numer.exp.strip_curlys.is_num_pos_int:
				d = numer.base.var
				p = numer.exp.strip_curlys.as_int

		elif numer.is_mul and numer.mul.len == 2 and numer.mul [1].is_var and numer.mul [0].is_pow and numer.mul [0].base.is_diff_or_part_solo and numer.mul [0].exp.strip_curlys.is_num_pos_int:
			d = numer.mul [0].base.var
			p = numer.mul [0].exp.strip_curlys.as_int
			e = numer.mul [1]

		if d is None:
			return None, None

		ast_dv_check = (lambda n: n.is_differential) if d == 'd' else (lambda n: n.is_partial)

		denom = ast.denom.strip_curlys
		ns    = denom.mul if denom.is_mul else (denom,)
		ds    = []
		cp    = p

		for i in range (len (ns)):
			n = ns [i]

			if ast_dv_check (n):
				dec = 1
				ds.append ((n.as_var.var, 1))

			elif n.is_pow and ast_dv_check (n.base) and n.exp.strip_curlys.is_num_pos_int:
				dec = n.exp.strip_curlys.as_int
				ds.append ((n.base.as_var.var, dec))

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
						return AST ('-diff', e, d, tuple (ds), src = ast), ns [i + 1:]
					elif i == len (ns) - 2:
						return AST ('-diff', ns [-1], d, tuple (ds), src = ast), None
					else:
						return AST ('-diff', AST ('*', ns [i + 1:]), d, tuple (ds), src = ast), None

		return None, None # raise SyntaxError?

	# start here
	if ast.is_div: # this part handles d/dx
		diff, tail = _interpret_divide (ast)

		if diff and diff.diff:
			if tail:
				return AST ('*', (diff, *tail))
			else:
				return diff

	elif ast.is_mul: # this part needed to handle \frac{d}{dx}
		mul = []
		end = ast.mul.len

		for i in range (end - 1, -1, -1):
			if ast.mul [i].is_div:
				diff, tail = _interpret_divide (ast.mul [i])

				if diff:
					if diff.diff:
						if i < end - 1:
							mul [0 : 0] = ast.mul [i + 1 : end]

						if tail:
							mul [0 : 0] = tail

						mul.insert (0, diff)

					elif i < end - 1:
						mul.insert (0, AST ('-diff', ast.mul [i + 1] if i == end - 2 else AST ('*', ast.mul [i + 1 : end]), diff.d, diff.dvs, src = AST ('*', ast.mul [i : end])))

					else:
						continue

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
	elif args [0] in {'-sqrt', '-log'}:
		ast2.src_arg = args [iparm]

	return wrapf (ast2)

def _expr_func_func (FUNC, args, expr_super = None):
	func = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC

	if expr_super is None:
		return _expr_func (2, '-func', func, args)
	elif expr_super.strip_curlys != AST.NegOne or not AST ('-func', func, ()).is_trigh_func_noninv:
		return AST ('^', _expr_func_func (FUNC, args), expr_super)
	else:
		return _expr_func_func (f'a{func}', args)

def _expr_subs (expr_commas, subsvars):
	if len (subsvars) == 1:
		return AST ('-func', 'Subs', (expr_commas, subsvars [0] [0], subsvars [0] [1]))
	else:
		return AST ('-func', 'Subs', (expr_commas, ('(', (',', tuple (sv [0] for sv in subsvars))), ('(', (',', tuple (sv [1] for sv in subsvars)))))

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

def _expr_ufunc (args, argspy = None, name = ''):
	kw = None

	if argspy:
		name, kw = AST.args2kwargs (args.comma if args.is_comma else (args,))

		if len (name) != 1 or not name [0].is_str:
			raise SyntaxError ('Function() takes a single string name argument')

		name = name [0].str_
		args = argspy

	args, kw2 = AST.args2kwargs (args.comma if args.is_comma else (args,))

	if kw is None:
		kw = kw2
	elif kw2:
		raise SyntaxError ('keyword arguments not allowed here')

	return AST ('-ufunc', name, tuple (args), tuple (sorted (kw.items ())))

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

	return AST ('@', f'{var}{VAR.grp [4]}' if VAR.grp [4] else var, text = VAR.text) # include original text for check to prevent \lambda from creating lambda functions

#...............................................................................................
class Parser (lalr1.LALR1):
	def __init__ (self):
		self.TOKENS_LONG.update ([(v, self.TOKENS [v]) for v in self.TOKENS_QUICK])

		lalr1.LALR1.__init__ (self)

	def set_quick (self, yes = True):
		self.TOKENS.update (self.TOKENS_QUICK if yes else self.TOKENS_LONG)
		self.set_tokens (self.TOKENS)

	_PARSER_TABLES = \
			b'eJztfWuv3DaW7Z+5QB8DdQCRlEjJ3xzH6TEmr7GTvtMwgsBxuwfBzQt2kjsXjfnvl2vvzYdUVEmqqnPqJVg+YlF8P9YiuTfJuzd/ef38q8+/+vIvm7/8r/e//MO/ws/PX3z2jX99/ezViy8/94bPXj17Li8lb+3fn7z88qsvwlsFg5YAPv0KYXxJfz958dfv' \
			b'nz97/eK1mL94Fmw/Sca/JePXbHz9+bPX//aJj+3fkYpoIOvn3776/O/4FQ3ffvbtl8+//nswweE3r/D320+CJza++OLrb/7++gUl71tk4G/P4O6Ll19+iwS+/PKbvyIPL78gz/T3P17B9edUOF/hq8TwCfl8/tUXXzwLBQaLVy//+m/fhLS9Cml/1Us7fn36' \
			b'yedkgUT9h//z7IuvYfzyUykhmD5Jxr8lo5TQi89fv0DEr15+gfenL//28lMYnnPpv/6G0vf155Qxn+WQx/98/eI5Ofj05WefocS+fEk1/5wS8OzLT1EO+PDVK4kwVB+SzKE+97n9JrxR/V88+/r1N1/B/zdU8C/+8znqhaz+Nxc9XorrxIfy/N+98eMfP3z8' \
			b'8+2Hj39m5o+Z2Rvfvf3w/vfvf/3w/T9++Onj728/eCv/5S05e//fv3n7H//8OZg//vHb+w/hxy/v/+v7tx/+K337wRt/fvv79+9+/UlMH379v8nEsX18//Hju2j6LZpCMG9/SMbff4+R/fPtu9+D+TcKla3/+OVdSug///lbSk1M9E8/RuOPv/we0/vzHz99' \
			b'/+PPv2XZzAPKMhmNKUj4hSH8/v39h/jtz7cfBs7Czz/y1L79xz+C8d0fH376f+HHf398n3L6w4e37/7P+/jzY56yP9/HsP745cdff4mRvo3u36XsUSHHnPyagvwjK+9fYpJ++PGXX2OOfk214NMTa+Hdrz///DZ6/u3H9+/exx++UWUJ+u3j77/GSGJVx6T9' \
			b'+lNKPQXa+/Ex8/n9T3++/SlafGSf323e3N037ca6Jxs2tDDUDn/aTd08kZ/+F5k6/8duYGGf9Cz4Vxv8eQ9dsIKRXN1TLLXd3JmN8fZmUytveBJtyS5Z3JM/7fhP4yPVHGiwMtWWlc9DZgWjN6mG/1izuVecVP8LRm+CR59kHx1H7GCAd58YSkjDf5x6Ij99' \
			b'2iiIenPnY1MW/58Emy7/pSoxwA5h1si76iTvtXkSbMUuWtxrjsOXqPKp9iVuJVRkkIPt+I/1KdWcOITijahLKnH/hatQfgZzZq/5dU/R1fTfdOFzDYN/G7F/wj/ua7Hk1FKF6ipkqo62YrdloZOF6lvcayp74xNkOEWK/zRcMt50X1OSjeU/DdLIReN/3Rtu' \
			b'yUhSFT808UNd8x/HMXqTr1AqOb25Q5NAVXF6YWPzX07esIJf/90gcnYQfzZDq1C1fftm++fAym7/LLgYBOu2f/Y83dcmS1pq9ZKIgYUdWrjMwnfXO6MkCT4S7XrW6ee9oV7om9Wd0Ruq8mrjvC8fPHoZJ670GZDk+/0MV/5H39V9TZ0EiNRtXBVaNDosffBN' \
			b'kbsiqrzxvtu8R/qP0T7ZNGzTJRtLNk2VbBzbqGBzr6m5ajQCbria/6DIQnKDlc2tYITJ8Z97AUYxwlRzKw9efIINNeZGPki1o4vUhAo+dXfUggUEfVCK68Z3YApTGf5j0Rm4yIA/isIFtqlgoMwohVKsQ9fncoAlW8nvSsKsUVuNDg2oZx9svAW1NsN/fMt6' \
			b'Ir99byU39B8Fy15gQAEb/mPxhf34XzCiBPxHV1Oi5afjXu9xQqnIRBvdUMtqugBJBO5MfWgvhj9zi8wq0H+UEvaWdzZ1QvrZpog9B3F5I1ITTZWYdB0MTTDYYCD40b49a1SgoqqIVoa6w9Aq/fQhkEnxH4tSk6bORkRSbZgufQR3qs35CAxDSdMN/2m62ME1' \
			b'd33kTvOfNDxAXVMGGsV/wJ6NlIUiI0xV+PhEfvpf4QNb+V7vLBW+rULdIA0NRWwRgI0BoAlYCsCq8IGcipX4ahxnGojm8+nHQm+qjfJ9QvnM+6h8HddgL9+MqXk0G4+Hvvf5duLxpQN2+P7dNpvWeqJv/X9v53uX8k1agfwVglMoK58iH68nalXBrfMVTW3N' \
			b'Z8lH5x/v21eY0hgy+HflydbHqDe+xflu3bpN225aH2m16dSm8+H4NCmfKOVTqGrE5eP2qfFV7ZHG4GPj/1vkvKYBG/DNu4HzjQcy37CVwX8fuc+QQo78N/j0MSsftTL47R37jHf1pvN/kXYEqzedD6oC8HliBgV3btO1G+efbtP6QlGbVm9as2m9f59R5XPq' \
			b'K9g3B0vd3aOLtX7U6cebvkMAnp3ynAw8993U+cGW3ThUhPfqU9rQuM63QpQRCtUHiKGrNz5BB/YuffXdod5g4evOv97c+XTiJ4oIr4pd1fLVZwvWKAS8Ovr6BhRHvymotc7PrM7vOq481XFNV1JrLVcmagJ13HKlUg3RO3hTWpqMkXctDqwERBXobVpuBpoD' \
			b'qCX4KrqiRrQixHm3ljd3DVV8ryylFLn0SuXG5RXLaat8+mUyViBSDr4xWs2Nz1ZnkBYBP7QwatFOWrSmjvD4CdKOE6SbE8UvSNFKuWizduxL6NgrAF9CPd1RCmks1q71dQn1xTwAgqCKi0VHhRaLSIomlEheBD7LMWunz1LWirZbzkmpGEXMg0/qIjT1IEzD' \
			b'coqPfuMzv/aI0/cII6M3IzOFOswBdLci2vnXn58aEvMoH7LyQasGmfMJa5B979tnea2lM6ilbq2l86+lrlpr6QJqSa21dO61dNfJuELxevQdFQIvLtbrGsQl1CBlnBeNRBBBy8TfkexV6lZWl2S1WYaQjVS0fK3dWt0XUN01ixyU5brt6OfpU3bWM1wWrknK' \
			b'2EbWnVm+hsqNX++UESg0Iq7puN903G866V3KSHczIswJUzOR6HVB+CNCGxEDop4o1Ia9N2Ha3UjwlLK16mhZvJP1cMfyL8ejcwhWtV6Xe/Yp0VZaX8ttvOVG2RoRWEoTZjEIKIUbMcZw+N4EGRL3CMvOLbdwx7KbyrutvDvKHiC+u53i9SXDBWYZX1yzFgkU' \
			b'j6hImLgcw56zYyUTuvcNlZDjzui4Mzq3Npo7J2NVJQLZWAgsdRNYCmLjRjRuRO9Cm6Bn4aBYvCpRnf2wlrSkNKtH6VXh6Qzrx7COvrFr/Zxh/UBfUItGmn+vFXFCEUKz9pCzrBiUthatS/9eq+QMqqQiOpECXJU8Hm4JTNG4ah0Gn3uPaInHofC9VtcFVFfd' \
			b'rPV0CfW0wt8l1BNtaKFpTEPTmBOTZmHzDfYuVDLTIqReBy0PV/6I/iSbMXipAxHzfIFXplr+VRmpfxH/je/U+k52gmH1hDytzeOItWQEKnihmCVRTsRYImFluUPUZ6GOu5b9MXoIwTN0WrkrNCIxb0TGXUcloibopEjVKN6BAUVLhNBV/JK6VLx8tdbNAXWD' \
			b'ELkweXC6FuJeE2ZeI1rLa2551Wt5LSqvZi2vJeVVWx6EYdANxaBOMI7lUZnylgpKjywRydW6hK06bqprce8o7q5Zy2iqjBqiiKbBeUlryWQjkE5kka7l+VtPd8PxwG9EF1nxoSnnkxdSNBSFOc0Kc5oV5micyljOE0aFkxXIU8NurQzELM9jRaHnZtrBGygG' \
			b'0mJ2t2qWb85+8e0NFDhX3YETL1OrXPfvhqCCVB2TpjFA1d1qUfAa4tmk6E4xgEO3mfnM3SifuWYFyJPKh6xM4Wx3qy2wutWM27XrnbTrOVmid/pWW6BbW+CJlQN4OtmIilTQ5vRTSN44gBemlU/oHHu8WvrFqp9GVD/Nk6B5aNLJg7RuSE5bDm49ruUCWoTP' \
			b'rGFhu+FjUbmOFb2bLlQwXsAKkemzI/bZcqUbsQ2H8xol9tTEqL2t52CdQ5VDqE9La6sG93lUh6pDr+tk710X8NME1QAtKgG0YrqC5/lUnVt70TlUBZRhDCvDGFaGMUEZxuTnuaCMTNDsMGNClDsVyIxf7LTm4U7txKOMfgz/7thtx24biaYhBapVwFUQ/dn1' \
			b'rI7tCRJB/qputLzsSOypRcpoWMpoWMpoWItU+juf3Q6BInVQy9akjfcdHcDB42ChXO3kzZqrlvu6Y0+WwcUx5jjGA8fxOpemTfU65z3pnLdCDdC0tA4alzzzqXnmU/PMp5bJTU3zFULxwBWBRaIGpnxvopS+HhfI+2zW3CBrbpD1OmI4fbtgnYN6+2AMu+5z' \
			b'uYjqs9xxebJ0c4upRCyNbJ5oBN6aMGtkeGsY3hqGt0bgrRGSbBiTGsYk//KUF7pFsyqu7S58y5xvuXR9lDbcOWKx5Ile1iRtJipvu5bpxF4xjTJCY7REsrwZKJ6mZrmgnTRjejeBahveEaHIuuUbPlsTHbe8jsJKZJh54NgjnHiEW4WyWtJwudbSzloyaxlN' \
			b'oUNTh5U7K+3TybuVASTfZoUG13FL7aQ518GfFvc9rUhYsPCl2uCKw42mSyawsI6LJrqsdJjrW4xSMDMyoUA6KggjIxoZ5mQ5pitPZcWCyz0v2O3qQ91pqbVBzfPoyJc4tZYw/mmlBGsu0ToNV1hUJNiJosKYCScj4kRAHAeIY/BwBh4OwMOBbzjtDaec4dhE' \
			b'nMqIExlxHCPOYsQ9chibYVMhJFE4Shu1jYEOxjJYeMDZmFCD9y1ZY8bn06ixN9GPwLSvTY2jNTBeq1CM3h22QGMrI3a2YACIgkWrROmiyaGIUcaYNaI5YVbp86qxzw5bitDKsAcSC7m+nLXvDxoq0AAmbNeFdhA0gyAohiYhFGZb9Dpcb9zi1lO6Mxo3J+MS' \
			b'Vdw3istovR0u8cStobiRFRedVnQ7Lt3yiitZcXkn7hmtcJE2/tNlqLihFXeLaoRc4Z5XuqrWh0ZXI8NDTVetVnInqa8j3BPOd6kafEf8HcKg7/CPir1Hf7jvKCF0FTPsq2rDF4IiAh+3r7B7yhMSg+tFHd1zypcA042vdKczkkSXPtOFoXRHKUbJlNUOaaHs' \
			b'+68Ol4jiWlF8rBAjbur1RXqPa1sdXbNKl4du7vneVdyFjpwhRO+yxZtuyK2QcMW3x9LNulRAKHVcpYoLWqlo6Mpy7w95QTH43x3FAl+oILRrvnMX/um2cbr/+x6Qcg9Mue9QGI3cvIyk+t90vW2FkFBVmJrc4x5ah6u9fdC4AdnhCnYUmdwK7VpOi6IrgRVS' \
			b'htvaqay8L7xRcC1uRKeAfXQt2or5DjADLFmR5GaQZIWRFUYeAEY0YGQMPmwJQVwadOVQYly2/NIfjD0EpmAwqLOF9pkQg13YUzBz0fDiBhCjFsCMQ9m6CUBx45DiNo5hxRWAxSVocSVwcY8JL47Tatwm/ZsPMW4WyFwJtrghuiBdsxFm8y/7FETlnoKqWvyw' \
			b'/wN1tQnY4QXWLoAPTSLz+WEPgsKi62C9lxeBJ0BJy1x4PjrJ1Ff3Jr3FSXQCq/7kNaGWC3PyeOp1la9M1zIP5rl4XPOOc9lsHpvPd+NKs86Aj/VPojJfruAXwbCwxoIbiwkgvTscez8FlDjffAoscdkYrrLqgab3ixsmDgZPLQDq3UFvcimQGp2BaTMDUJ2A' \
			b'qt4GVuhuQ3s2Aiz6KhYjmgmM9Q4AYz5MegnUwqzlxYCLlZaGIZfeJIxwjLsUF0MvO4tPxGHyswXEBCiMxHRNNa2Y6P1RmVKE6sR7iMwUQ/Z/C6lTqtG6Yy4q18sSFRNHRcWTofgwhl5s6H0pf+3gI6M+AsRu2ID+WdyVMEGINxCCOAEvxBAboohgnGYKdrWb' \
			b'LEL9Z5QhVscgjl5hQFK/B4tQNplI8jIbIxP6aoOrIanExERyYVqx/uX7IrMLuv9TcJ7vtk99qfwPHZK0g22aeePcyyWZwDBJljmfYfQEy8xhmJVdHoldLLOLnWAXFIodH8WjN1ghFSukYoVTbOIU23sSp9gip6TFg+Rlb0KxzCe2QCd5+FtUEr+gCdvyQzRi' \
			b'E4VQvvSI245KW8qTOkX6JFOGHnP0cl+Jt8AZEn0eiFPR9TRfzJhchMByvmCro/BFytueZGETWaSwRrnCMlXYElNIrhbyRHPoYsiBJHEW9DCHGtZJxwXRgmNamFrYUTtWdhTpPDEnyOKOCvMMlzjB9Z7ECcUFH5VWfDjsPdlAZhelyUWemC02iF+MG6Y8fbMc' \
			b'QW9CUXQY1ooyG2YALq+MBHJf1OvEGHhAIs6DovbOrqZ5wM3gAQks5wG2OgoPpOztyQNp9SkLa5QHZMpQnDFIrhbygF15YOWBq+OBjnmgm+KBbgcPsH/igU54oBMe6BIPdL0n8UBX5IEu8UB3AA90zANdgQfyxGzxQPyCFtyVH+KBbsADRYeRB5KN8MBwMpD7' \
			b'ol4X3AgPSMR5UE5FV9M80M3gAQks5wG2OgoPpOztyQNd4oEU1igPdMwDXYkHJFcLecCtPLDywLXxAGEvSdZ28wC+jPEAmn3FPMABsHNV8Vt4gF3FJ/IAOd3iAZiFBzjs/XiAIqIUbvFALzFDHkhfcIBuVX7AA3ogJi47DDyQ2TAPcHklHuj5UpWORuGBEHEe' \
			b'lFPR1SQPsKvdPBACy3hArI7BA1n29uMBeBUeyMIa4wHNMmmOb8ADIVcLeaBdJq2+JjZwKyFcPSFoJgQ9RQia3Fh5lWiBPxEtaKEFLbSgEy3o3pNoQRdpQSdaOEAKTRFRCrdpIU/MFi3EL6AFPfoQM+gBMxQdRmZINsIMesAMuS9iBjEGZpCI86Cciq6mmUHP' \
			b'YAYJLGcGtjoKM2R52o8ZdGKGFNYoM2hmBl1iBsnVQmboVmZYmeF6maFmZqinmIGee97DVWYGdkHMUAsziIKoTjqiuv8kZqiLzFAnZqgPYAZWGsVrixnyxGwxQ/xi3DDlPY+W4+gxQ9FhZIZkI8xQD5gh90XMIMbADBJxHpRT0dU0M9QzmEECy5mBrY7CDCl7' \
			b'ezJDnZghhTXKDDUzQ11iBsnVQmZQ1UoNKzVcLzWwKqueUmVFAhumhmaEGtgFUYMosTJU8jtQQ9N7EjUUdVh10mHlsPekhoapoSlQQ56YLWqIX0ANzehD1NAMqKHoMFJDshFqaAbUkPsiahBjoAaJOA/KqehqmhpmqKWGwHJqYKujUEPK3p7UkHRSs7BGqaFh' \
			b'amhK1CC5WkoN6ox2P5yaIJbue1hJ4oJIglWP9JTqERLG2kf0EpLQzBM5VfAvogpRQ9KihqSTGhK7ik+iiqIakk5qSPoANSTNaki6oIbUS8wWVcQvxg1T3vNoq2DqsUXRbWSLZCNsMVBG6vkithBjYAuJOw+KaptdTbPFDGWkEFjOFmx1FLZI2duTLZIyUhbW' \
			b'KFuwMpIuKSOFXC1lC9qiS9qxDP3AfU2IP8D6Gsie8HcEfAl2IzQ6gbwAZQGqGJ4YHggWfHdGrCd4vuNT+lbKXCnz+inT8JKbmVpyM/SAMk225AazlhdTprhT3OCJMo0svJm08DZ4ImWa4sKbSQtv5oCFN8MLb6aw8NZLzJAy0xfjhinvebRVMOWUWXYbKDOz' \
			b'Yco0g7W3ni/0w2AUygxx50E5FV1NUqaZsfYWAssoU6yOQZlZ9vajTJPW3rKwxijT8NqbKa29hVwtpcydG/5WtljZ4lrYomW2mDoFCC2WN5SbbEO54Q3lJm0oF3fEFq2wRSts0Sa2aHtPYou2yBZtYov2ALZomS0Kx3v0ErPFFvGL9NzsQeNK320VTD26aAtP' \
			b'ootkI3Qx2C3ec0N0IcZAFxJ3Lwsqupqmi3YGXUhgOV1ISR6DLlL29qSLNtFFCmuULlqmi7ZEF5KrpXQxte9vpYuVLq6CLjqmi26KLtgN6KLL6KJjuugSXbA7ootO6KITuugSXXS9J9FFV6SLLtFFdwBddEwXXYEu8sRs0UX8Ytww5T2PtgqmHlsU3Ua2SDbC' \
			b'Ft2ALXJfxBbBjbCFxJ0H5VR0Nc0W3Qy2kMBytmCro7BFyt6ebNEltkhhjbJFx2zRldhCcrWULaZ2B65ssbLFNbBFzRtF6qmNImirvFeEXsIWBB/yYrYQd2CLWjaN1LJppE6bRthVfCJb1MVNI3XaNFIfsGmk5k0jdWHTSC8xQ7ZIX4wbprzn0UZTzhZlt4Et' \
			b'Mhtmi3qwdaTnC/0wGIUtQtx5UE5FV5NsUc/YOhICy9hCrI7BFln29mOLOm0dycIaY4uat47Upa0jIVdL2WJqD+HKFitbXAVbKGYLNcUWityALVTGForZQiW2YHfEFkrYQglbqMQWqvcktlBFtlCJLdQBbKGYLVSBLfLEbLFF/GLcMOU9j7YKph5bFN1Gtkg2' \
			b'whZqwBa5L2ILMQa2kLjzoFzyMM0WagZbhJrJ2IKtjsIWKYI92UIltshyPsYWitlCldhCcrWULRbuNFzZYmWLy2QLFnPXU2Lumh5ii0zMXbOYu05ibnFHbCFi7lrE3HUSc9f9J7FFUcxdJzF3fYCYu2Yxd10Qc/cSs8UW8Ytxw5T3PNoqmHpsUXQb2SLZCFsM' \
			b'xNw9X8QWYgxsIXHnQTkVXU2zxQwxdwgsZwu2OgpbpOztyRZJzJ2FNcoWLOauS2LukKulbLFz92FzM4TRljnDrbxxdbxhWKPYTGkU+wJB82WlYpMpFRtWKjZJqVjckRBDlIqNKBWbpFTMruKThBhFpWKTlIrNAUrFhpWKTUGpGE0xpWZLihG/DNI9eJAcWwW3' \
			b'gT46kWWUfCRZRrIRWcZAt7jni2QZYgyyDKmfXj5UdDUty5ihWxwCy2UZbHUUWUbK3p6yjKRbnIU1Kstg3WJT0i0OuVrIIHrnJsWVQVYGuToGqVkGXk/JwDvSpq9ZDF5nYvCaxeB1EoOLO5p8iBi8FjF4ncTg7Co+afJRFIPXSQxeHyAGr1kMXhfE4L3EbE0+' \
			b'4hfjhinPn07mH+w2EkjNU5CSjzQFSTYyBRkIw3u+aAoS3MgURKonD8qp6Gp6CjJDGB4Cy6cgbHWUKUjK3p5TkCQMz8IanYKwMLwuCcNDrpYSyCVvZSzdXrwuW90aeTRlArHdrmkIi8bNlGgc7ZpF4yYTjRsWjZskGhd3NAcR0bgR0bhJonF2FZ80BymKxk0S' \
			b'jZsDROOGReOGReMEcrgfvM4VqvJEbU1F4hfjhjnoebTR1FOoKrqNk5BkI5OQgYi854smIWIMkxCJOw/KqehqehIyQ0QeAssnIWx1lElIyt6ek5AkIs/CGt3gaLm9YSKSick1Ao+TEcndUi6Zuov0nLlkFX7cNossmYLgUk7fFPHayR64NMwQe9BL2ANmLS9m' \
			b'D3EH9qC3rvld8VvYg13FJ7IHOd1iD9gKe3DY+7EHRUQp3Jp/9BIzZI30xbhhynsebRVMOWuU3QbWyGyYNbjUEmv0fKEfBqOwRog7D8qp6GqSNdjVbtYIgWWsIVbHYI0se/uxBrwKa2RhjbEGlVYj8Q1mHiFXS9li3RG+ssVNsAWLypspUXlDD7FFJipvWFTe' \
			b'JFG5uCO2EFF5I6LyJonKm/6T2KIoKm+SqLw5QFQu93c3BVF5LzFbbBG/GDdMec+jrYKpxxZFt5Etko2wxUBU3vNFbCHGwBYSdx6UU9HVNFvMEJWHwHK2YKujsEXK3p5skUTlWVijbMGi8qYkKg+5WsoW647wlS1ugi1YvNFMiTcadgO2yGQbDcs2miTbEHfE' \
			b'FiLbaES20STZBruKT2KLomyjSbKN5gDZRsOyjaYg2+glZost4hfjhinvebRVMPXYoug2skWyEbYYSDV6vogtghthC4k7D8qp6GqaLWZINUJgOVuw1VHYImVvT7ZIUo0srFG2YKlGU5JqhFwtZYt1Q/jKFmfEFqZ9yEMamTH0FGNodoMwM8bQzBg6MYa4o0Ma' \
			b'hTG0MIZOjMGu4pMOaSwyhk6MoQ9gDM2MoQuM0UvM1iGN8Ytxw5T3PNoqmHqHNBbdxkMakw0zhh4wRs8XHdIY3DBjhLjzoJyKrqYPaZzBGCGw/JBGtjrKIY0pe3se0tiRIC8e1JjCG5VjMGvoEmuEnC1ljXVj+MoaZ8QaD8YYlqXfdkr6jVbH0m+bSb8tS79t' \
			b'kn6LOzCGFem3Fem3TdJvdhWfyBi2KP22SfptD5B+W5Z+22qbMXqJGTJG+mLcMOU9j8mUM0bZbWCMzIYZww6k3j1f6IfBKIwR4s6Dciq6mmQMO0PqHQLLGEOsjsEYWfb2YwybpN5ZWGNsYVnibTOJd2SLkKulbLFuDF/Z4ibYgjeG26mN4WhyvDHcZhvDLW8M' \
			b't2ljuLgjtpCN4VY2htu0MZxdxSexRXFjuE0bw+0BG8Mtbwy3hY3hvcRssUX8Ytww5T2P0jMHG8PLbiNbJBthi8HG8J4vYgsxBraQuPOgXPIwzRYzNoaHwHK2YKujsEWKYE+2SBvDs7BG2YI3htvSxvCQq6VssW4MX9niJtiCdaPslG4UGhvrRtlMN8qybpRN' \
			b'ulHijthCdKOs6EbZpBvFruKT2KKoG2WTbpQ9QDfKsm6ULehG9RKzxRbxi3HDlPc82iqYemxRdBvZItkIWwx0o3q+iC1CyQpbSNx5UE5FV9NsMUM3KgSWswVbHYUtUvb2ZIukG5WFNcoWrBtlS7pRIVdL2WLhtbQPyhb19RGGIf33lTgeizjUCHk0QwLx/2uQ' \
			b'CKtM2SmVKUsPkUimMmVZZcomlSlxRyQiKlNWVKZsUpmy/SeRSFFlyiaVqRj8njzCWlO2oDXVS88Wj8Qvxg0T3/Noq2Dq8UjRbeSRZCM8IlpTYhvYJPdLbCLGwCaSgjxAp6KraTaZoTsVAsvZhK2OwiYpe3uySdKdysIaZRPWnYpRDgklhsCc4o3zacVMXWnb' \
			b'BkIxVzTxOOZNtnNmGythHGem4e18GWkI+aa1pjRrTekprSlNbFG8xxYNVDNJ0Fuzc9KU0klTSveepCmlBySBBgXLoCil9yeI+6BXqwvniFDbS/+3taViUo0bpj59g6qUHuhJFR1GPSn6iRYCglDDiwmRFHZCiaLe12QSDPkOYggpx090ADHO0JTS09wQKjXX' \
			b'lGKrIjdwPmaLvZH7RhKyp6qUJnKQxhKLa1RXSrOulC95qmf/sUASIYf9WQd4AMgl/OCL5ClpK1TqKVGi76VP+br1RBhTu8PPlTBOShKBIAI5qIwUhBAiEVwaCZzVUhMrPtkpxSfbjYO+Zf80MxBlJyvKTjYpO7Gr+KSZQVHZySZlJ3uAspNlZSdbUHbangrE' \
			b'pGEq0JUfmgcMVJvKDuMkINnwJCAO+6XYKp0N9VmHybL2kp2lumRnqC6FuPLhPVsdZXifSmf5yL5LI3sOY6fKkmWVJVtSWQo5mrFQRMA8tdV6BeYVmE8GzI4lxm5KYuzUODDjcBeREjuREjuRErskJWZX8YnA7IpSYpekxO4AKbFjKbErSIm3gDklzbfEQWrT' \
			b'N8uB5sBcdhiAObPpA3MothyYHQt/HYt93SyZr5sh8w2BZcAsVscA5qx0FgOzS+JeCWMnMDuW97qSvDfkaC4wT+1qXoF5BebTATMLZ92UcNaZHcBs6DMBswhknQhkXRLIsqv4JGAuCmRdEsi6AwSyjgWyriCQ3QbmmDQAsyk/BMwD8WvZYQTmZDMAZimuHjCz' \
			b'nNWxhNXNEq+6GeLVEFcOzGx1FGBOpbMcmJNkVcLYDcwsWnUl0WrI0VxgntpAfK7AvK59nwGIn5uWDboUgNxOAbndAeSWPhOQWwFyK0BuE5Db3pOA3BaB3CYgtwcAuWUgt9tA3kvMFqjHLwB1W34I1O0A1IsOI6gnGwH1fKm75wVdjUtTIF6izANxKrqehns7' \
			b'A+7FWQ73bHUUuE9522+JG8aA+SmsUci3DPm2BPmSq4XaNGZqN/AK/Sv0Xw70O4Z+NwX9bgf0O/pM0O8E+p1Av0vQ73pPgn5XhH6XoN8dAP2Ood8VoD9PzBb0xy/GDVOevlmOoAf9RYcR+pNNCfpzLwT9LoN+iTIPxKnoehr63Qzol8By6Gero0B/ytue0O8S' \
			b'9KewRqHfMfS7EvRLrpZC/9SW3hX6V+i/HOhvGfrbKehvd0A/PQz9rUB/K9DfJuhve0+C/rYI/W2C/vYA6G8Z+tsC9OeJ2YL++MW4YcrTN8sR9KC/6DBCf7IpQX/ugKC/zaBfouylWkXX09DfzoB+CSyHfim8Y0B/ytue0N8m6E9hjUJ/y9DflqBfcrUU+qf2' \
			b'567Qv0L/5UA/67q4KV0Xt0PXxbF/gn7RdXGi6+KSrgu7ik+C/qKui0u6Lu4AXRfHui6uoOvSS8wW9McvgP6u/BD0D/Reyg4j9CebEvTnXgj6uwz6Jco8EKei62non6EREwLLoZ+tjgL9KW97Qn9Si8nCGoV+1opxJa2YkKul0E+bbetNM3Ez2tUzQH2ke9Ae' \
			b'kAl81uezQX15jIADxx7u6Dd0I8hOWeEGnWPiUrRmo3dMDig82SilZXagZXag0+xAt70nnf1WnB3oNDvQB8wOghK8LkwPeqnZOvwN8SPhLBYYJD75w9lvPEFQrTAFEFHpEffx/LdkUyCLnhc6/C2bJ4SYe8lX0XVOFsD68ulvhbkCDhzcOgFOAs1PgJPSPAJp' \
			b'IJxGErPnEXAtdYB4BBynbfcZcDxr0KVZQ8hbog6ywV9L5rahv5bsPYdo1nzXLTFIt3mziz+2maMjwjBCFcINGTEIK8ymhFHdHEJ/QvlsjB/Re6BR09OkaQWFZ6Dv1Di8h7aHoqxZjqwRUXchabeNoBE50YVmo+YoXhJQEkoSRAZ8jIBYQMMAhQfj4LSKS0C8' \
			b'++HpZBG6hkoqffUU4NL9lrrgKBBNDlt72HMU1AHk7AE1AWN2owugZRtXAqJ4kPC52QkSxRHmo+FEGCj6VnTraIHRTBEx5qLFskEWDaEuFDKygRKqdYWO4SiFirMIH4ugQy0dX7hTQMdwXgkMMQ+HIz4dymF10PvxTevsceXgUchCXBnFlDBnuwhcodTm/wVj' \
			b'FIXwoDhDTOC/aKwbmRny9bPBnTLmaLsEdzb/8q3zqc8JZji+QpbPcKoJBEqrX0cEoQA8TQIen5bLH8S4AwBnuIiUA47327R94MECg88zAxDvHecFJdh7d22VHcCDuTNAqjkiQBE4MQAtAqj6ZCAVQckmUEJ9XtUASNeHgRHqZ3QQhCXMe2UHqKQpKgSABicr' \
			b'mrJig6SjqFS68wU/yANy0LQ0djKHrc34cigu3T8ccglqQeqg63HkwrL6xaAXkKtaOA1rZk7DqkcYMo0Ml+ockQiQzmbYNJyKoT5Rd+OIREm/PFQCIqGBLJ6a6ZlTM7Ss3dOz+tjLvw86MrqmUdHSpR37uEs7R13WOfnoJhvZNNc1stlracfMxI/d2NGcreho' \
			b'dGDi04cE4lhZnCurTgEkQxn+KcDEm31eNUTZtZ453WrLALM1rTr6dOoi1nq2Bi3o4C2paNzzUWd1ezLksecDPveYVSEKinXuFGt7epXJvym1vYkUT5/s5s15YNOomtNRRdxnMappT7G4nECmbS8bY1jbzIkmWf1You5zGtCAhE4k6t78q3vqaYpWjd25gMc0' \
			b'YCBZh45mzgI8lgLHcPSy17Toqkco40sqFWmOHj4qOSfo2AM2pBBG8WPRhKjdHzNwbO1jw4Y9zkRo3y0uW4rMp5gI1ecNI7iZ4/yxhMbcCPQo85wRRGnMUlhByz3tOgulaDjROQBgugMApnt8gMnARVcnHJucCFxWYDlQe7cPKqjDkw9VTo0pR8UTX7L7T3Kq' \
			b'0+KJWvFkxZMD8cSteHJcPFEH4Ik6LZ7oFU9WPDkQT85gKeW68ERfziLsTS28niFgnDtWHAkYNKX3opZYDwWCzb98x3gKRIRgxqdjxYRLwYQ9pbiXigvUnY4DC9wzr1nychyBraufEhorbPjxnY8gol4hYoWI00MEdZTzGTrcLkhY+9TDNUFDs0LDCg0PBA0E' \
			b'Axc5q7hdaGjcU4/oBA1noy66QsMVQoNdoeFyoeGClEFXaChAgzdjqyXtiDwLmKD+fG7Lkuz9DFCCEvIYIEERTYIETpK498HqnXCBU3l5d3v1FHjrW/9TgjvfRL0FnUXSHKAhugLJGQDJmYBHe47g0Z4LeLSPBR6HjjBmQcYBOp8rZNw4ZFDbu0Yx6DEggwrn' \
			b'0iYltX1KPODbOUSidAuAPUSNc4WIW4QIalTXrSmxACKoNK5m3aKGskSNtk+jCZJ72EM0M1eIuCWIIPc3ok01AyOoOK5vcdPgTiF0ENw0RIucdlW2XCFiJ0SQ2xvTt7xd8YfBMKKqCRpWncsVGhRdt3ZuKpenhgZK140hgyZVS/QZKF9WliBi1bm8UYhAUz4X' \
			b'jctzRIibHDwoIIPiwcOqcnmryKBWZFiRYQcyXJDGJaVPTg9+TJQo3vp7yhOD162fSzED9XjvfbYnQQ//smeEIYCRMSRZsjXcno1K5v6H+0IveHjr+EWMNPa4ITzihp0YcdgbwhBV+L+P6hXBESyy67gvbkCy523aAUuoEHaOTKACPDU6aaGIxeKQs1HVXAFm' \
			b'BZi9AcZs/d8LYMwKMFQIEwDTLAGYs1HsXAHmqABzO+BSb/3fC1zqFVyoEA5aV0nA4qN4A0BhNGEoYRxhEGkIPhoAB1CDISPHCwKL0O1N3j2NdMu22B25Kw663rCLULeofVdA0admH1p8bOyxoaONcvuuuVVTg46NudSQUyOOLQ+NLTYNBEtNQo20BLq9aKvO' \
			b't6qlpRqm+ahvnUcodMbdiLgtF791gypolldDXagKoFWsDuqXD10fyAohQ6wXLXWj9aB+YrddVkfchwrdJ68rfZS6UmPVZa+ryjJA36q2gMWPVnXQRPFloCzln06vbOgD5M+dH8R4e1J+rRVZN7k1RimarO3mjbbqO/ztvnvi33f3vgNXcIXv976F+IEQChkl' \
			b'QNdJ3RvYKdzj68mcrgh3dLOuHzR5uNQbX6eeFbqG7rfVtfOevQ1GTVATqPli73A1LpqaH/v4X7iEAgyA/T9oiXx51X29PDb/dfwfBdogUDcarNyb142E32A42Az+pXvwdG5P0dlCdDVi9E0H59FXdOrrduzVVgL4QomwFo7zUrFJqpGE+UFt/IeRgOUzXbP/' \
			b'PRfO9Nx35Aer2zDTiai+w1vKgXukHLSbA/5RStt9UtqOJXZwDVUx8UZnGfDBTPzDoL9vw8NvK8Ps/CsG1/4fZawrZEyP5s0DJSY4XX9Ss51h1c8zTmuqOlL2xbAK4yw6VUzzxkZAIoAKOIWzTVMZVbJwZ7m8PATipjouNzNedriJlCYidV6OgvmObhSXK8O/' \
			b'Y64aPu22Ve/b2P/pkHb5Hg9xYDMw7k7jeNTUAPynkzZtEvs92sNZVksbvR8c+LHBgzR9nyo/kjhxF9CbZQ+lul7oaecTxmVHDHLr4crXZ4d4aqTKzUNXu9mc/MFi0dAKI7gjhM3VbU4Mb/XmER/Och2zjDP4uwds55hgXUZTh7IHno6XXNuHe9SDhr774fov' \
			b'zUPmN3l1hFaPoee+D5asl3vjnNthy0eiHqP9qwvoA1iFyR5OtN4MrI/+YIXmoeMYebhRlGaZ4w1hHrfv1yvsZvBgTX3bduYDec48p1wO7do5xjsHViZv6OEWsWzy/4A9A6LXEzy8GFmt/WJHv2g2t/Rwi1i2PjB/Nrhf37Cb4z6Q+89zyqWh1/4x3j8gy7qh' \
			b'h1tEaU59jP5Bc9h9+gjUdY79QC1mnlMulK1Z99pNsm7SbG7p4RZRmocfq5ugpvfrKnbzEA+UxeY55bJZZ+q7eovb3NLDLWLZNN3uuwo/t9P0KwqV0m7mP1CDW+QBSpYTLpBx+cEltk7od/Qh6Bbd0MMtYtmEfu8+lFf23v0JCtUP+eQqy7N9sSrSQSsC+wmK' \
			b'9+5bGAfUj9jHlPSzJvQ1XyjQ5IIi374PJOCH+J98NHqEao8eapu92MQNSK3IvAOZ7eaWHm4Ry7QOTozMbnNmD5ehWXvVjl7Vbm7p4RZRL9blOabyzn4drFB32EM2+4E++SIPgyds11rgAxuusNlKNlpR0S9b3Djfom82l/BwmZc0vi+xzO3mEh4u82XLEscu' \
			b'c+MWlLueU/Zu88gPKGxvF1wHJe37GWR/wmoosPZ2VbSbRQ+2BC31s9+zIyaukD13DZx5hWDX9oU9vJmppMJ/BdWhN5f2cHUs3l5wdXtqcPLB8ocPN0j/9wtlGOJ22NnPnpu5YdHDVX1+mwkevaqbzTU+XL3LFB2usXpxYskVPly9y5cPrq561eYaH67e5UsU' \
			b'V1e9enOND1fv8tWQq6tes7nGh6vXbd6YmjYIC1q30UL6dwcLFCFZYicL72n3Zf8mbwC+oMkFqs0XNfYYQXRg5NQGVXbtK63/n13rLdeoPPLhq37wX/M5GTjHKB2UYagpsL1noLw9UhPqNZ3QbHCEAh+zAdt0+BcftBUO2WrS4Vo4WKuR8mj6seDoFDpxmDJK' \
			b'UYao0DJlCU+kLv7TG7Ru3zJpYxed1cVfHHzXLBOGPJhP9FA4QMVH3uI/j6NwMbduLG2BEb9dOiKE1xRwzaYPBTZObFSywTEiT/4/i5/oig=='

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
	_LTRU     = fr'[a-zA-Z_]'

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
		('UFUNCPY',       r'Function'),
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LTRU})|(\${_LTRU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\$?(?:{_LTR}|\\_)(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

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
		('SUBSTACK',      r'\\substack(?!{_LTRU})'),

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
		('FRAC',          r'\\frac(?!{_LTRU})'),
		('BINOM2',       fr'\\binom\s*{_VARTEX1}\s*{_VARTEX1}'),
		('BINOM1',       fr'\\binom\s*{_VARTEX1}'),
		('BINOM',         r'\\binom(?!{_LTRU})'),

		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\ne(?!g)q?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)(?!{_LTRU})|{"|".join (AST.Cmp.UNI2PY)}'),
		('IF',            r'if(?!\w|\\_)'),
		('ELSE',          r'else(?!\w|\\_)'),
		('OR',           fr'or(?!\w|\\_)|\\vee(?!{_LTRU})|{_UOR}'),
		('AND',          fr'and(?!\w|\\_)|\\wedge(?!{_LTRU})|{_UAND}'),
		('NOT',          fr'not(?!\w|\\_)|\\neg(?!{_LTRU})|{_UNOT}'),
		('SQRT',          r'sqrt(?!\w|\\_)|\\sqrt(?!{_LTRU})'),
		('LOG',           r'log(?!\w|\\_)|\\log(?!{_LTR})'),
		('LN',            r'ln(?!\w|\\_)|\\ln(?!{_LTRU})'),

		('NUM',           r'(?:(\d*\.\d+)|(\d+\.?))((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))(?:_{{(\d+)}})?"),
		('ATTR',         fr'(?<!\s)\.(?:({_LTRU}(?:\w|\\_)*)|\\operatorname\s*{{\s*({_LTR}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"((?<![.'|!)}}\]\w]){_STRS}|{_STRD})|\\text\s*{{\s*({_STRS}|{_STRD})\s*}}"),

		('WSUB1',        fr'(?<=\w)_{_VARTEX1}'),
		('WSUB',          r'(?<=\w)_'),
		('SUB',           r'_'),
		('SLASHSUB',      r'\\_'),
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

		('VAR',          fr"(?:(?:(\\partial\s?|partial|{_UPARTIAL})|(d(?!elta)))(partial|{_VAR_QUICK})|(None|True|False|{_PYMULTI_QUICK}|{_VAR_QUICK}))(?:_{{(\d+)}})?"),
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

	def expr_mul_exp       (self, expr_mul_expr):                                      return expr_mul_expr
	def expr_mul_expr_1    (self, expr_mul_expr, CDOT, expr_neg):                      return AST.flatcat ('*exp', expr_mul_expr, expr_neg)
	def expr_mul_expr_2    (self, expr_mul_expr, STAR, expr_neg):                      return AST.flatcat ('*exp', expr_mul_expr, expr_neg)
	def expr_mul_expr_3    (self, expr_neg):                                           return expr_neg

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
	def expr_intg_2        (self, INTG, expr_add):                                     return _expr_intg (expr_add)
	def expr_intg_3        (self, expr_lim):                                           return expr_lim

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

	def expr_abs_1         (self, LEFT, BAR1, expr_commas, RIGHT, BAR2):               return AST ('|', expr_commas)
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                            return AST ('|', expr_commas)
	def expr_abs_3         (self, expr_paren):                                         return expr_paren

	def expr_paren_1       (self, expr_pcommas):                                       return AST ('(', expr_pcommas)
	def expr_paren_2       (self, expr_frac):                                          return expr_frac

	def expr_frac_1        (self, FRAC, expr_binom1, expr_binom2):                     return AST ('/', expr_binom1, expr_binom2)
	def expr_frac_2        (self, FRAC1, expr_binom):                                  return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_binom)
	def expr_frac_3        (self, FRAC2):                                              return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4        (self, expr_binom):                                         return expr_binom

	def expr_binom_1       (self, BINOM, expr_subs1, expr_subs2):                      return AST ('-func', 'binomial', (expr_subs1, expr_subs2))
	def expr_binom_2       (self, BINOM1, expr_subs):                                  return AST ('-func', 'binomial', (_ast_from_tok_digit_or_var (BINOM1), expr_subs))
	def expr_binom_3       (self, BINOM2):                                             return AST ('-func', 'binomial', (_ast_from_tok_digit_or_var (BINOM2), _ast_from_tok_digit_or_var (BINOM2, 3)))
	def expr_binom_4       (self, expr_subs):                                          return expr_subs

	def expr_subs_1        (self, LEFTDOT, expr_commas, RIGHT, BAR, SUB, CURLYL, subsvars, CURLYR): return _expr_subs (expr_commas, subsvars)
	def expr_subs_2        (self, expr_cases):                                         return expr_cases
	def subsvars_1         (self, SUBSTACK, CURLYL, subsvarss, CURLYR):                return subsvarss
	def subsvars_2         (self, varass):                                             return (varass,)
	def subsvarss_1        (self, subsvarsv, DBLSLASH):                                return subsvarsv
	def subsvarss_2        (self, subsvarsv):                                          return subsvarsv
	def subsvarsv_1        (self, subsvarsv, DBLSLASH, varass):                        return subsvarsv + (varass,)
	def subsvarsv_2        (self, varass):                                             return (varass,)

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

	def expr_ufunc_1       (self, UFUNCPY, expr_pcommas1, expr_pcommas2):              return _expr_ufunc (expr_pcommas1, expr_pcommas2)
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
		self.stack [-1] = lalr1.State (s.idx, s.sym, AST ('*', (s.red, AST.VarNull)))
		expr_vars       = set ()

		if self.autocompleting:
			stack = [s [2]]

			while stack:
				ast = stack.pop ()

				if ast.is_var:
					if not (ast.is_differential or ast.is_part_any):
						expr_vars.add (ast.var)
				else:
					stack.extend (filter (lambda a: isinstance (a, tuple), ast))

		expr_vars = expr_vars - {'_'} - {ast.var for ast in AST.CONSTS}

		if len (expr_vars) == 1:
			self.autocomplete.append (f' d{expr_vars.pop ()}')
		else:
			self._mark_error ()

		return True

	def parse_getextrastate (self):
		return (self.autocomplete [:], self.autocompleting, self.erridx)

	def parse_setextrastate (self, state):
		self.autocomplete, self.autocompleting, self.erridx = state

	def parse_error (self): # add tokens to continue parsing for autocomplete if syntax allows
		if isinstance (self.rederr, lalr1.Incomplete):
			self.parse_results.append ((self.rederr.red, self.tok.pos, []))

			return False

		if self.tok != '$end':
			self.parse_results.append ((None, self.tok.pos, []))

			return False

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

		if pos and rule [1] [pos - 1] == 'expr_commas' and rule [0] not in {'expr_abs', 'varass', 'expr_func'}: # {'expr_abs', 'expr_ufunc', 'varass'}:
			return self._parse_autocomplete_expr_commas (rule, pos)

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_intg':
				return self._parse_autocomplete_expr_intg ()

			return False

		return self._insert_symbol (rule [1] [pos])

	def parse_success (self, red):
		self.parse_results.append ((red, self.erridx, self.autocomplete))

		return True # continue parsing if conflict branches remain to find best resolution

	def parse (self, text):
		def postprocess (res):
			return (_ast_mulexps_to_muls (res [0].no_curlys).flat,) + res [1:] if isinstance (res [0], AST) else res

		if not text.strip:
			return (AST.VarNull, 0, [])

		self.parse_results  = [] # [(reduction, erridx, autocomplete), ...]
		self.autocomplete   = []
		self.autocompleting = True
		self.erridx         = None

		lalr1.LALR1.parse (self, text)

		if not self.parse_results:
			return (None, 0, [])

		rated = sorted ((r is None, -e if e is not None else float ('-inf'), len (a), i, (r, e, a))
			for i, (r, e, a) in enumerate (self.parse_results))

		if os.environ.get ('SYMPAD_DEBUG'):
			rated = list (rated)

			print (file = sys.stderr)

			for res in rated [:32]:
				print ('parse:', res [-1], file = sys.stderr)

			if len (rated) > 32:
				print (f'... total {len (rated)}', file = sys.stderr)

			print (file = sys.stderr)

		res = next (iter (rated)) [-1]

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

	# p.set_quick (True)
	# print (p.tokenize (r"""{\partial x : Sum (\left|\left|dz\right|\right|, (x, lambda x, y, z: 1e100 : \partial !, {\emptyset&&0&&None} / {-1.0 : a,"str" : False,1e100 : True})),.1 : \sqrt[\partial ' if \frac1xyzd]Sum (\fracpartialx1, (x, xyzd / "str", Sum (-1, (x, partialx, \partial ))))}'''"""))

	set_sp_user_funcs ({'N'})
	set_sp_user_vars ({'N': AST ('-lamb', AST.One, ())})

	a = p.parse (r"Union(Complement(Union(Complement(Union(Complement(Union(Complement(Derivative(0/partial*x*abs(w1)*6.4380354041832416e-21**d*y, z, 3), Intersection(partial, b, 'str'**d**2 / (dz**2*146591184863111.94))), Complement(Intersection(partial, b, 'str'**d**2 / (dz**2*146591184863111.94)), Derivative(0/partial*x*abs(w1)*6.4380354041832416e-21**d*y, z, 3))), ln(y) / ln(partial)), Complement(ln(y) / ln(partial), Union(Complement(Derivative(0/partial*x*abs(w1)*6.4380354041832416e-21**d*y, z, 3), Intersection(partial, b, 'str'**d**2 / (dz**2*146591184863111.94))), Complement(Intersection(partial, b, 'str'**d**2 / (dz**2*146591184863111.94)), Derivative(0/partial*x*abs(w1)*6.4380354041832416e-21**d*y, z, 3))))), z20), Complement(z20, Union(Complement(Union(Complement(Derivative(0/partial*x*abs(w1)*6.4380354041832416e-21**d*y, z, 3), Intersection(partial, b, 'str'**d**2 / (dz**2*146591184863111.94))), Complement(Intersection(partial, b, 'str'**d**2 / (dz**2*146591184863111.94)), Derivative(0/partial*x*abs(w1)*6.4380354041832416e-21**d*y, z, 3))), ln(y) / ln(partial)), Complement(ln(y) / ln(partial), Union(Complement(Derivative(0/partial*x*abs(w1)*6.4380354041832416e-21**d*y, z, 3), Intersection(partial, b, 'str'**d**2 / (dz**2*146591184863111.94))), Complement(Intersection(partial, b, 'str'**d**2 / (dz**2*146591184863111.94)), Derivative(0/partial*x*abs(w1)*6.4380354041832416e-21**d*y, z, 3))))))), FiniteSet()*FiniteSet(True)), Complement(FiniteSet()*FiniteSet(True), Union(Complement(Union(Complement(Union(Complement(Derivative(0/partial*x*abs(w1)*6.4380354041832416e-21**d*y, z, 3), Intersection(partial, b, 'str'**d**2 / (dz**2*146591184863111.94))), Complement(Intersection(partial, b, 'str'**d**2 / (dz**2*146591184863111.94)), Derivative(0/partial*x*abs(w1)*6.4380354041832416e-21**d*y, z, 3))), ln(y) / ln(partial)), Complement(ln(y) / ln(partial), Union(Complement(Derivative(0/partial*x*abs(w1)*6.4380354041832416e-21**d*y, z, 3), Intersection(partial, b, 'str'**d**2 / (dz**2*146591184863111.94))), Complement(Intersection(partial, b, 'str'**d**2 / (dz**2*146591184863111.94)), Derivative(0/partial*x*abs(w1)*6.4380354041832416e-21**d*y, z, 3))))), z20), Complement(z20, Union(Complement(Union(Complement(Derivative(0/partial*x*abs(w1)*6.4380354041832416e-21**d*y, z, 3), Intersection(partial, b, 'str'**d**2 / (dz**2*146591184863111.94))), Complement(Intersection(partial, b, 'str'**d**2 / (dz**2*146591184863111.94)), Derivative(0/partial*x*abs(w1)*6.4380354041832416e-21**d*y, z, 3))), ln(y) / ln(partial)), Complement(ln(y) / ln(partial), Union(Complement(Derivative(0/partial*x*abs(w1)*6.4380354041832416e-21**d*y, z, 3), Intersection(partial, b, 'str'**d**2 / (dz**2*146591184863111.94))), Complement(Intersection(partial, b, 'str'**d**2 / (dz**2*146591184863111.94)), Derivative(0/partial*x*abs(w1)*6.4380354041832416e-21**d*y, z, 3)))))))))")
	print (a)

	# a = sym.ast2spt (a)
	# print (a)
