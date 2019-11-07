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

		elif arg.is_paren and not tail.is_diff_or_part and arg.paren.as_ufunc_argskw: # f (vars[, kws]) -> ('-ufunc', 'f', (vars)[, kws]) ... implicit undefined function
			ast = wrapa (AST ('-ufunc', tail.var, *arg.paren.as_ufunc_argskw))

	elif tail.is_ufunc: # ufunc ('f', ()) * (x) -> ufunc ('f', (x,)), ufunc ('f', (x,)) * (0) -> ufunc ('f', (0,))
		if arg.is_paren:
			ast2 = tail.apply_argskw (arg.paren.as_ufunc_argskw)

			if ast2:
				ast = ast2

	elif tail.is_func: # sin N 2 -> sin (N (2)) instead of sin (N) * 2
		if tail.src and tail.src.is_mul and tail.src.mul.len == 2:
			ast, arg = process_func (ast, arg, tail.src.mul [1], wrapa, lambda ast, tail = tail: AST ('-func', tail.func, (ast,), src = AST ('*', (('@', tail.func), ast))))

	elif tail.op in {'-sqrt', '-log'}: # ln N 2 -> ln (N (2)) instead of ln (N) * 2, log, sqrt
		if tail.src_arg:
			ast, arg = process_func (ast, arg, tail.src_arg, wrapa, lambda ast, tail = tail: AST (tail.op, ast, *tail [2:], src_arg = ast))

	elif lhs.is_pow: # f**2 N x -> f**2 (N (x))
		if lhs.base.is_func:
			if lhs.base.src and lhs.base.src.is_mul and lhs.base.src.mul.len == 2 and lhs.base.src.mul [1].op not in {'{', '(', '^'}: # this only happens on f**p x, not f (x)**p or f x**p
				ast, arg = process_func (ast, rhs, lhs.base.src.mul [1], wrapa, lambda ast, lhs = lhs: AST ('^', AST ('-func', lhs.base.func, (ast,), src = AST ('*', (('@', lhs.base.func), ast))), lhs.exp))

		elif lhs.base.op in {'-sqrt', '-log'} and lhs.base.src_arg.op not in {'{', '(', '^'}:
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
			b'eJztfWuP3Taa5p9ZoF2ACpB4lfzNcZweY2InYzu90zCCwHG7B8EmcWAn2Vk05r/ve+NFOtLRpU7VuRGlOqIoinc+D8n3Jfno7V9eP/3m629e/qX6y//68Os/4BYev3721Ru4ffvk1bOXX4Phq1dPnsqtkbuC+xfPX37zItybYFDiwZffoB8v6feLZ3/94emT' \
			b'189ei/nFk2D7RTL+LRm/ZePrr5+8/rcvILR/x1hEA1k//e7V13/Hp2j47qvvXj799u/BhA7fvMLf774IH7Hx2Ytv3/z99TMM4cXzl99hpF5+hwn52xN0//zlm79iGp6/oI/p9z9eoeuvKXO+wbcSwhf0xdNvXrx4EjIMLV49/+u/vQlxexXi/qoXd3z68ouv' \
			b'yQIj9R/w8+TFt2h8+aXkEJq+SMa/JaPk0LOvXz/DgF89f4H3L5//7fmXaHjKuf/6DcXv268pkZDkkN7/fP3sKTn48vlXX2GOvXxOJf+UIvDk5ZeYD/jim1cSYCg+jDL7+hRS+ybcsfhfPPn29Ztv8Ps3lPHP/vMplgtZ/W/Oerw1XCbgy9N/B+PnP378/Oe7' \
			b'T5//zMyfMzMY37/79OH3Hz5++uEfP/78+fd3n8AK3rwjZx/++zew/+nPX4L58x+/ffgUHn798F8/vPv0X+ndj2D85d3vP7z/+LOYPn38v8nEoX3+8Pnz+2j6LZqCN+9+TMbff4+B/fPd+9+D+Tfyla3/+PV9iug///lbik2M9M8/ReNPv/4e4/vLHz//8NMv' \
			b'v2XJzD2KiUz+QHqD8fcPn6L1n+8+5V6CITz+kcfu3T/+EYzv//j08/8LD//9+UNK2Y+f3r3/Px/i4+c8Jn9+iH798etPH3+Ngb6L7t+n5FCmxph/TF7+keXvrzFKP/7068eYoo8p1yE+Mdfff/zll3fx499++vD+Q3yASpRF6LfPv3+MgcSijVH7+HOKPXna' \
			b'e/icffnDz3+++zlafOYvv6/ePrq1vnL+pmJDiwbj8MdXxt7IIzyRqYUfV8GrW3fTs+AnH76DD9pghUZydct+2OqRrnRb3erKNGC4ibZklyxuOzQozz8Qu1vV3eRWqt2xsj0rNIKpsfzjdHXbcFThCY1gwg/bCtPIAXs04OcQGYqI4R/f3MgjxI28gBcQWuPw' \
			b'/ybYdPlTU4sB7dBPg2lvOkm70TfBVuyixa2iDxrI3wZiDdFz4ismkL3t+MdBTBVHDn0BI5Yl5Ti84SKUx2DO7BXfbik4Smqlu/DaoAHuWuxv+OHWiCXH1mGiVB0SZaKt2O1YqGTR9C1uFeW9hoA1hWxq/rGcM2C6NZRAbfnHYhw5tvB0qykdFtPYxhc2vjCa' \
			b'fzyHaDAtlJhGVY+wSmBRcXzRxuVPXu5ohd82kGwMXGIWHnesQtH27e3u4+BLt/s44kL1rfzuY++jW6OyqKVaL5EYWLihhc8s4OGRbiQKWGN9zzo93mouVKjLWlVU5HXlIT/Ae2xlXBZjrxGS4FrgCkq77+pWU9NHfOoqX4cajQ2WWg9URW6KWOSmqwDJshYJ' \
			b'L6N9srFs0yUbRza2TjaebZpgc6sow1XHP1QVpboHK5dboRFT4PgH8u/mJhnRpLhuh6RiqqlCWi2VntNgsW4zUECJUL0V6IMoNpQ5GpotA6TmH4dNgDMKUaehJoiI1gQDRa7BqlCZ0OA59WjJVvJci58GywgrSbtrH2zAguqY4h+oTzfyDG2U3NA/Zid/ggbM' \
			b'MM0/Dt9wxOEJjZgD4Js3FGl59AzckLdNE/mnUpbqk20DEBGkc52FMsJcwtdcW7Gmh6zvQg6D5SOXmh49tilgUznObwxUR1MtJmWCwQaDCwYqcijVRwoLsKGiiFaaGsHQKj2CD2Rq+MdhrkkFZyMGUlccEQjgUdPmLIS8QlFTln9sF5s1PN1y5GzDP6lTAA9M' \
			b'J7bmH+RyaRG2JiOWbRde3sgjPIUX7BYS5B1nfhfKBgnesu/ogYseYOQceeDq8IKcilX4ynGiEccgndADeltXDZR4A+0CgoIyNshZUI2petgKmh6AGNQTKO8OEQNadWurFj6pPfy38GkD/wr+AVFqcAM1GqIDgUKWAz03tYV/SImhugYG+A4u+BIyuVH4FbqC' \
			b'zg+EqCqocQDOra/atmoh0LrqmqoDFxrhCqILkWwglg36gBGCOtxBMYIl0A0k2xCSY08M6jR8oxHlAL4wmZCiRuMdIgCJ6nTVmaoDS4UOwQ+IQ6MxMPgKotGBG3hTo88NQB1QMZJu56rOV76tfFe1kCFN1aqq1VUL7hT+Q3VpsNk7auqALA76MNjDhMaAgOwb' \
			b'YGFEcGii3lZQ0B5ihPGEiFrqyUHmUN5UmL8KO6tgvMHGC/GHonuEZYYWUG5we/sI8wUeMWvwVrMrI28x5TfEanTr6O1bJDV6bvFWyvuEyvtRxwXXdFzKtZRYywWJJYDl23KBUunQvZXPmkaqi5K7FgdWPKLCA5tWqlHL9Ua8D8E1ZCrIcMI15e0jSyXZy0fJ' \
			b'Qc65kTyTvIp5tJM3/fyYygbJAKiITnHFc/UJxEVAD2sX1WYvtRmL4OYIEVKeI6TskcKXfAjgoFRp1KfeqBnASxmdbhk9onhR36stZXXqZaV0IAUqtJhtlGExeyRbQm7kyY/J5WQdMTmp9ozUmKNSL2YvdzTxDQ8xCMdwygSCryDxpSUctyUE0NKGOwVxMKi6' \
			b'gmKnXXYw/COmaSAWDfjeWMwHsMI0QoIbSHEpoSOXUFdK6LRLqKtLCZ14CTWlhE65hB510oegTKDpxTZMGJoyt3DqpdeYMBaS2WVKME4n6zqUq8wDy6yxdBXD3LHh+STjS1GfeFGbIEbgEuu4PDsjBdlRd7IMaPcNaFl0JjFjG5lOZekZFnJ8+6jRgogsU3vU' \
			b'BXmNtDQtchktLUtGYZ28rqWlBbmdZd9sGE1bcU4xKEVEs9udzK57znHPHXCUmKFstMzgrMvNViig5YraKr5pkTdK/WRJCooSuH5jNw3f2yAG4urt2LljR57FLzWEUGMuQLQoie31ZC/kDIOHY7GrtyVLUF+IsoQx0DPkeTeVM6FpX1EOeW6Mnhuj96XSPPJC' \
			b'oI3IdGMmsPBMYClIfi1XMRJ8fk+6YtIBRs3govt02r1YUm5SrNWkip7SiZWNZkV67UrZnFjZoHqfEiUyuJdCOJJEwJaWcXKFgjmtREES7qU4jlwcNTUSybyim3E/U1k18UDp6p5yS2iJs1EfuxTViReVsaWMTr2MmrqU0WmXEa0xoWGKJXo6MkmOrIfBJQUS' \
			b'xYbQuXRQ7ifvMfijrI/gKQwMmMcEPNvU8lOtpOxFsje9cOp7WZiFsyKaklKqxmFKSDdcBjzpy1IlLyIpkZSyDCGooWjCkpLvd20ZlI2odspNQOTRpJZFcuqk9xNUScL6VNYOQX1I9KGr+SbliAWD5VPKZVu5NCaAkmHMLBm4Wq+D5n1KXi3JK1PyanFe2ZJX' \
			b'S/PKOO5oYaea1NG4TZYsm86yzpQsmlEHC30VFkxmqnnccWcFvv6bICizVAGtxY2JSqbmmeo4gzx32/raFp67eBPKwqSuc3NCaWnCliktj/NaHvW1PGITFJehKG6tQB9Zdus054Pj16KCczX14C2q8tH0dFdUv097Wu0tqlsWqf8RJ57rXEvviiCClBKTTjCC' \
			b'qbvWrOCdX04mRo8ama50wufOXymPeVvA8WgSHydddNdda+2rrzXhrjS7ozU7L5PvXl1r7fOl9h1RzE/jEVyToXgphpL9TDWr9uMNh5A3tCU83lp6YmVNLcqa+iboC+q0tR/N7ZBTyHjNAquyg8Ap1wZIqGaxueb9Rrl8+W67ULh4gzhokc6zI/6y5QLHHM62' \
			b'MUJJMdtT9aK6VjadOnZxo3ieps+KrvXxiwJzQGebduBknmCmDkJ+JcJ9mhEtgHkSxWZK6zl6MaA6i2Z1Fs3qLDqos+h8IxXMHx30M/Qe4Qiz13BfjsaMW9sRa5SiapaiykvNLzlYIVjNjqzmaFlSlyqCrt0xgnVlh43dgRNV76JktC7fSPSpRNKoWdKoWdKo' \
			b'WVdUGilv4I5CRWqcjtss6d59T9tmcB9ZaFk5ufNAynG79/yRY3zyjE+eW73ncL1PwylTxsHHGgdD5hoZqpqgW8kjIsMjIsMjIiODHkPjGELvwCmBbaKupaC7jVJ6M805bcPhss+QXFN6FUfv3IHXZncbC1sW7J180TlusDyIurpJVSITK8sirMCaDaNJhjXL' \
			b'sMau+AbRtEKMlrHIMhbBralik7BF1W1v3stEmePMhSBdON/D4ewnuMcN44ISE2W3K1m6f/0X5R1WRUfUyot84q5njvPZSyWmuxWelc35IAM912nPHgXHLc+usJ4ZjsBwrIFbFOHuRFkhkctSSPsKSZcsmoMGHWbzrNRO2bXSBpGJ7IkFmdRxPe2kMpvwnRL3' \
			b'PU1ItGAhTF3h+YGVotMdcJIdT3jostxhjm+xd6IazDjJkI4yQktPRro3WYqxSBuZneB8zzN2WHwdFRyX2k7Jc68I9zlFrSTq9HjJNivZ2cU+CsuLAmrCOzxJCvcwxA0MceM+3LUPd6vDrepwnzrclw03ZcPNyHDfSdw8ETdOxF0TsdrhaW3YKcO1grjtOG5s' \
			b'jcWNfRucYcCtKzFuHfbgIJMgjgqXG9Z4qDDUH9wVAztpEGdVYz6CO1wti5uWYL5ixmLOYrXE7MU6h3mMmYzDQ6xPOIyEqqJwxRBWMdS2x5ldqFYKtVqhQSjEJKzdqN2JqkGon+CxOsK9xRaHZz+3dMAmniyNZ+niEat4kice29pWeEAqnviKZ622eIRojSet' \
			b'1ngQKJ6miuc04xGc2OPkw6npmFE8+xTP9lToc41HetKJruAbHTWM/hkKtJPTPg0fQ8unlJINhY1Htyq01hiGxk/IF7Sq6VhjPEez5hNMOzzlGswtHY9q+RBfT8FYOgmVjlGls64xNnT4bHXLp6yif4pT2VHs4U2Hp3vjCZ549CclBCOBR5BCTt7iWaiezi41' \
			b'dFgvHS3a0OG5eCA0+gjftninc2prMtV07CcdV6sMH35q8HxSzCJKImY3fgeWgCO3ULduOwoFY2Uo9/A7Lcc620pOMgdnYNfROwyJT1qmE15v8VRaOjO2poLELMaiwsNdPZ6SDeHgYcIe04tZhoe+gr1vOS4NHdFaY8zais4wx2TQsbqYhhaznXIGqwj+6+8R' \
			b'XhBDCoJcB4IU+CjwcVj4UAgfU7DhxpDDp05WDiHaZ9Ms/c7XwbEEsp27fTLRsRBacEH1LLycM6y4AbTUK+DFY976GSDx01Di8SXCiR8BFJ8gxY+Bin8gWPEcTe2r9LccWvwicLkQTPFDVMF4LUaW6l/uMXKTf4zs1Fq4uf9B9bQZuOEJ1C6ADg0W83FgD3rC' \
			b'pOpgPpcneWfASMmYdykqtX1gCoPb0cGygNTOIFXQysXp17qPWzTrrGWsy+PtNJ89HK+awZg2zCI3Gd6x3klU3MuV+SIGjsyi4BHEhIvgDvehn8VHO4+RqE+IJ3v1sBK+RRn8nTGzEdwEd6gjuRY/cW+UiKFmAY46wdJmF09xWQTqaEdcxXaKhWNnoBUcdAyv' \
			b'dBOERTNEt0s4izP+lpGW7jSb4hhuKSxGXHYWrwi/9M0O/japX0dnPtNsiN4ExhQZLEm8DwGZPM/+dwA6RRgrdUwAOs9S0zFqxwzKwHsYwtg/AnyWRImrgH1H/NVE0M/C5mxuYriBB8QJ0kEMxhIzBOM8QTQLOCIWfWIKsToEX/RyCAXvG8iDSpL5I8+zKQ6h' \
			b'ty64GnJJjEzkFGYTB9RijZAKtvzHSHXQYh9DrvwP7W60h2Tssm7tmXKLEEsglVycuZRY9AS5LCGWQioPRCqOScXNkApmipvus2NLcMIlTrgkUIlLVOJ6V6ISN0olLlGJSyGs5xGhkTEWyb3eYZD4Rvth1NM7xwEE5iDcVJPOG+EMFzK0Yb/jAKFHGL2E1/JB' \
			b'oAoJvs3c+Ca6nqcJt4AmQp5nNMFWB6GJlLaNHOESRyS/JilCGGKUICRVK+nB3nXK447ccHRWWMMIZYhxBmzgmQ3mZm+aPdM3DWkvMRXIDA7da74HKvC9K1HB6KxOk6Z12O/1JOCZBEbmdnrx2CGB+Eb7YaTTO8cB9IYPe5yHaaEmzQw1w8FC7p4anBgD/EvA' \
			b'bebMJ1fz8O8XwH8oyQz+JQsPAf8peRvhP00xZX5Nwr9n+Pdj8C+pWgn/rsB/gf+Lgv+O4b+bg/9uD/zz9wT/ncB/J/DfJfjveleC/24U/rsE/902+O8Y/rsR+M/jsQP/8Y32w0ind44D6MH/hFuKSID/LsH/sOufu6cGF9wI/EvAbebMJ1fz8N8tgP9Qkhn8' \
			b's9VB4D8lbyP8dwn+k1+T8N8x/Hdj8C+pWgn/vsB/gf9Lgn9sh5okZvvhn9rrBPxjYmqGf/aAnTc13wX+2VW8IvyrUUURtBX4Z79Xwz+F4ek2hP9ePIbwn95oP4x0euf4lsP/lFuKiMA/mRn+OasS/PfcN1S5xA3Dfwi4zZz55GoW/tnVfviPJZngX6wOAf9Z' \
			b'8rbBP34l8J/5NQX/isXMHN4A/kOqVsJ/u04AfTEk4AoPXDoPKOYBNccDitw4uY2xAb8iNhD1QLrXfA9soHpXYgM1ygYqsYHaxgaK2UCNsEEejx02iG+0H0a696HjMHqEsMd5JASVCEENCCF3T4QQclQIQQJuM2c+uZonBLWAEEJhZoTAVgchhJS8jYSgEiEk' \
			b'vyYJQTEhqDFCkFStJISuEEIhhMskBMOEYOYIwZAbXnE1TgjsggjBCCEYIQSTCKF/JUIwo4RgEiGYbYTAWp+EA0NCyOOxQwjxjfbDSPc+dBxGjxD2OI+EYBIhmAEh5O6JEMQYCEECbjNnPrmaJwSzgBBCYWaEwFYHIYSUvI2EYBIhJL8mCcEwIZgxQpBUrSSE' \
			b'pi6MUBjhMhmBdVHVnC4qRs4yI9gJRmAXxAiihcowyffACLZ3JUYYVUJVSQmV/V7PCJYZwY4wQh6PHUaIb7QfRrr3oeMweoywx3lkBJsYwQ4YIXdPjCDGwAgScJs588nVPCMs0CuNhZkxAlsdhBFS8jYyQlIqzfyaZATLjGDHGEFStZYRmhNatXCO6xUKN5wB' \
			b'N7ASkZpTIsJIsR6RytYpKF6nkDMEPxFDiEKREoUilRSK2FW8EkOMKhSppFCktikUKVYoUiMKRb147DBEfKP9MNK9D10dTD2S2PNFJImkVqQGakU990QSYgwkIWG3mTOfXM2TxAK1olieGUlIRh6CJFLyNpJEUivK/JokCVYrUmNqRSFVa0mCVtKSeisjPsK9' \
			b'IqAfQLxBQE/IOwW7XQJFBD4COwGxCFIMTAwMBAjQkDHQI1zf8355hSgLUV42UWqeVtNz02pYc3laTWfTamiG6NKNiVLcNQwWRJRaJtd0mlwbXJEo9ejkmk6Ta3rb5JrmyTU9MrnWi8eQKNMb7YeR7n3o6mDKiXLfF4EodZpf04P5tZ57bILBKEQZwm4zZz65' \
			b'miVKvWB+LZZnIkqxOgRRZsnbRpQ6za9lfk0Rpeb5NT02vxZStZYo9y7PKyRRSOISSKJlkpjbmQdra8sk0WYk0TJJtIkk2B2RRCsk0QpJtIkk2t6VSKIdJYk2kUS7jSRaJol2hCTyeOyQRHwjDTa7sF6l964Oph5LtJNXYok2sUQ7YIncPbGEGANLSNi9JCRX' \
			b'8yzRLmCJUKAZS7DVQVgiJW8jS7SJJZJfkyzRMku0YywhqVrLEnOr9ApLFJY4e5bomCW6OZZgN8gSXcYSHbNEl1iC3RFLdMISnbBEl1ii612JJbpRlugSS3TbWKJjluhGWCKPxw5LxDfaDyPd+9DVwdQjiT1fRJLoEkl0A5LI3RNJBDdCEhJ2mznzydU8SXQL' \
			b'SCKUZ0YSbHUQkkjJ20gSXSKJ5NckSXRMEt0YSUiq1pLE3Fq+QhKFJM6dJAyv7zBz6zuwnvISD7oJSaAZoks3JglxhyRhZK2HkbUeJq31YFfxiiQxvimoSWs9zLa1HobXepiRtR69eAxJIr3Rfhjp3ocumnKS2PdFIAmTVnyYwYqPnntsgsEoJBHCbjNnPrma' \
			b'JQmzYMVHLM9EEmJ1CJLIkreNJExa8ZH5NUUShld8mLEVHyFVa0libsVfIYlCEmdPEg2TRDNHEg25QZJoMpJomCSaRBLsjkiiEZJohCSaRBJN70ok0YySRJNIotlGEg2TRDNCEnk8dkgivtF+GOneh64Oph5J7PkikkSTSKIZkETunkhCjIEkJOw2c+aTq3mS' \
			b'aBaQRCjPjCTY6iAkkaVpG0k0iSSylE+RRMMk0YyRhKRqLUmsXBdYSKKQxPmRBEuuzZzkGusmS65NJrk2LLk2SXIt7ogkRHJtRHJtkuTa9K9EEqOSa5Mk12ab5Nqw5NqMSK578dghifhG+2Gkex+6Oph6JLHni0gSSXJtBpLrnnsiCTEGkpCw28yZT67mSWKB' \
			b'5DqWZ0YSbHUQkkjJ20gSSXKd+TVJEiy5NmOS65CqtSSxd62gvQ6e8KNU4QpdXBxdaNYI1nMawZAhWHVZKVhnSsGalYJ1UgoWdySgEKVgLUrBOikFs6t4JQHFqFKwTkrBeptSsGalYD2iFIy1MEVkR0IR3wyiPLg6Xl0ubgNrdCKnmP4uySmSbrAe6Ab33JOc' \
			b'QoxBTiFF02bOfHI1L6dYoBscizWTU0h+HkJOkZK3UU6RdIMzvyblFKwbrMd0g0OqVhKH2ruksBBHIY6LIg7DYm0zJ9aGzDDsDIcamWTbsGTbJMm2uKOhhki2jUi2TZJss6t4paHGqGTbJMm22SbZNizZNiOS7V48doYa8Y32w0jnF8Khq4PbyBuaBxzT36UB' \
			b'R5Jvm4F8u+eeBhzBjQw4pGTazJlPruYHHAvk27FUswEHWx1kwJGSt3HAkeTbmV+TAw6Wb5sx+XZI1VreONuFhxNnAZe5qWviDDPOG7RMbXLQwdJuPSftxjrN0m6dSbs1S7t1knaLOxpxiLRbi7RbJ2k3u4pXGnGMSrt1knbrbdJuzdJuzdJuwjasCRRSUI3K' \
			b'47Mz8IhvtB9Gvvehi6aeatSeL+KQI0m99UDq3XNPQw4xhiGHhN1mznxyNT/kWCD1juWaDTnY6iBDjpS8jUOOJPXO/JpcjugkxyTtQh8Kw4xDD0ndWgqZO+DzZCmkCDaumjzWDDjwtEsoHLztJQ1LF5IG3YQ00AzRpRuThrhD0qC7kuea70IaVveuSBrkdIc0' \
			b'0FZIw247WY/C4HgORxu9eAzJIr3Rfhjp3oeuDqacLPZ9EciCzEwWnGGJLHrusQkGo5BFCLvNnPnkapYs2NV+sojlmchCrA5BFlnytpEFfipkkfk1RRaUW5Lu4TgjpGotSZR124UkLp4kWPpt56TfeHAjS79tJv22LP22Sfot7ogkRPptRfptk/Tb9q9EEqPS' \
			b'b5uk33ab9FuOwrYj0u9ePHZIIr7Rfhjp3oeuDqYeSez5IpJEkn7bgfS7555IQoyBJCTsNnPmk6t5klgg/Y7lmZEEWx2EJFLyNpJEkn5nfk2SBEu/7Zj0O6RqLUmUdduFJC6eJFh0YedEF5bdIElkcgvLcgub5BbijkhC5BZW5BY2yS3YVbwSSYzKLWySW9ht' \
			b'cgvLcgs7IrfoxWOHJOIb7YeR7n3o6mDqkcSeLyJJJImFHUgseu6JJIIbIQkJu82c+eRqniQWSCxieWYkwVYHIYmUvI0kkSQWmV+TJMESCzsmsQipWksSZdl2IYkTIQnt73O7RCYKNUcUit3gdokZUSgmCpWIQtzRdolCFEqIQiWiYFfxStsljhKFSkShthGF' \
			b'YqJQI0TRi8fOdonxjfbDSPc+dHUw9bZL3PNF3C4xEYUaEEXPPW2XGNwwUYSw28yZT67mt0tcQBSxPBNRiNVBtktMydu4XWJH8rm4ZWLyb1JGwWShxsgipGwtWZTl24UsToQs7o0oHAu03ZxAG2scC7RdJtB2LNB2SaAt7pAonAi0nQi0XRJos6t4RaJwowJt' \
			b'lwTabptA27FA29W7RNGLx5Ao0hvth5HufZhMOVHs+yIQhUuCbDcQZPfcYxMMRiGKEHabOfPJ1SxRuAWC7FieiSjE6hBEkSVvG1G4JMjO/JoiCcdCbJcJsSNJhFStJYmyfLuQxMWTBC/fdnPLt7G68fJtly3fdrx826Xl2+KOSEKWbztZvu3S8m12Fa9EEqPL' \
			b't11avu22Ld92vHzbjSzf7sVjhyTiG+2Hke59KA1ysHx73xeRJNLybTdYvt1zTyQhxkASEnabOfPJ1TxJLFi+HcszIwm2OghJZGnaRhJp+Xbm1yRJ8PJtN7Z8O6RqLUnMLd9uAz3oSyGGAx7VtIQNChMchgnADmcoII8WCCMUCyPUnDBCVZMne2PlVMwEdFfs' \
			b'nAQQKgkgVO9KAgg1YAKsUGgZ5A9qExHcBim1Gltx1/X+d4UQMZbaDyOe3jmOfE/8MH2lWaWGiUBgL7EARoXdNmHBRJMvl5D3SAMh5vjom2hcIIBQ80wQyzMTQLDVKBNwOhZPK2FgVop1owRCERVIPYnZNSmCUCyCwGM3MFB4OcIKIYV9VjDtY+qYCC1Aljzm' \
			b'U9nrx0SA0EAf8zGCiSdWnvZaBhNlMHFyFDI7mGBtWDenDevouuUqlwYTrA3rkjasuKPBhGjDOtGGdUkb1unelQYTo9qwLmnDum3asI61Yd2INmwvHjuDifhG+2Gkex+6Oph6g4k9X8TBRNKGdQNt2J57GkyIMQwmJOw2c+aTq/nBxAJt2Fie2WCCrQ4ymEjJ' \
			b'2ziYSNqwmV+TgwnWhnVj2rAhVSsHE3rlAbD3ShLmsnhC0SKnwhcPxRf1BGeYIW/Av0buYCVZN6ckizWPlWRdpiTrWEnWJSVZcUfcIUqyTpRkXVKSdf0rcceokqxLSrLR+/X0wSMQN6In24vKDn3EN9oP49370NXB1KOPPV9E+kh6sk70ZMVFIJH8KyIRMQYS' \
			b'kRi0mTOfXM2TyAJt2ZjzGYmw1UFIJCVvI4kk2Xbm1ySJsLZsDHLII9EHphIwrmCTuTXcpzk1dcTpqMANwgvECYELhAci/p8b9p/UOKFlrG/nsL6dnl5ydDG+t4LvreB7m/C97V0J39tRfG8TvrfbwL1lcG93wX0X0GOstB9GNL1z7GkPyifcUuABytsI5RG8' \
			b'JcfqXITQMlq3jNPtIpBuF4B0KJ0MpNnqICCdcmc9PrcJn9mPvcpHFIikeQedJUULevmEx3MLogseFzw+Ch571hTyc5pCvp7GY9x4RbSDvGgHedEO8kk7iF3FK+KxH9UO8kk7yG/TDvKsHeRHtIN28DjFSvthRNM7x7ccj6fc+kwXyNc7eBxyLMdjz0o/ntV9' \
			b'/CJdH79A1yeWTsJjsToEHme5sxqPfVLzET/24rFnPR8/pucTUrQUj+fWHhc8Lnh8HDxm8aufE7/6PeJX3AJLxK9exK9exK8+iV/ZVbwSHg/Fr4zHSf7qt8lfKQxPt3k8jrHSfhjR9M6xpz08nr4SHqtdPJac6uExC1Y9C1T9ImGqXyBMjaWT4TFbHQSPU+6s' \
			b'x2OV8Jj92I/HLEb1Y8LTkKKleDy3zPc08bio0hwdu09NDopNC/HbzuG33YPfll4TflvBbyv4bRN+296V8NuO4rdN+G234bdl/La7+N2Lxw6WxzfaDyOd3jkOoIflE24pIgHLbcLyXOTZc4ytjDNSkF2CbPNYN9H1PMrbBSgfyjBDebY6CMqntG2bqkbrAPXJ' \
			b'r0mkt4z0dgzpJVVr5Z1za3YL4hfEPw/Ed4z4bg7x3R7Ed/SaEN8J4jtBfJcQ3/WuhPhuFPFdQny3DfEdI74bQfw8HjuIH99oP4x0euc4gB7iT7iliATEdxOInzsmxHcZ4kuQbR7rJrqeR3y3APFDPmeIz1YHQfyUto2I7xLiJ78mEd8x4rsxxJdUrUX8uYW3' \
			b'BfEL4p8H4ntGfD+H+H4P4nt6TYjvBfG9IL5PiO97V0J8P4r4PiG+34b4nhHfjyB+Ho8dxI9vtB9GOr1zHEAP8fc4j4jvJxA/d0yI7zPElyDbPNZNdD2P+H4B4ocyzBBfMu8QiJ/SthHxfUL85Nck4ntGfD+G+JKqtYg/t4q2IH5B/PNAfNZa8XNaK36P1oqn' \
			b'ixFftFa8aK34pLXi296VEH9Ua8UnrRW/TWvFs9aKH9Fa6cVjB/HjG+2HkU7vHAfQQ/wJtz7TYPHtBOLnjgnx2wzxJcherJvoeh7xF+i2xDLMEJ+tDoL4KW0bET8puGR+TSI+67f4Mf2WkKq1iE9LYk1lZ84du2jg1wc6Zew+CaBdQQL6/IgAa+f97cKGTQiX' \
			b'EjVECrd6jhUgV9QeYiD/RF9dCTMoYQaVmEG1vSttwzbKDCoxg9rGDGG9rBqhhl5EdvZhw6AxzjwBNIh3+s5x3LE9kN94yhiFMfmJyjhCTXBEzzHtw5ZxRAi5F/0mus45wtRTG7GN8ITiwx37m7GJp/lmbGx1kM3YWlo0q7aTBUYmOwRA4rZ/OzZmDDXGGCFt' \
			b'iTHIBn+BNuC3NfRryR6oQ/EiWdUScXTV2320sUsYHfGEFoYQSsj4QMhgIRNMadkQ6COK5V36iNYD5ZieUowX9F2CujPd7h7K3hVd1XpEjUi6D0HbXeSMiInNezFaTuIkASShI0FjwMUIhCMoGCDwLvg3r60SkO52uFNYBKuhvklf0+RWdLAXAtBsL7WHOQdB' \
			b'G4SaDRATsGU/qiCk7OJJQBIAB8iJveAw2qF8GHwI/UKoVdeOEth7GUWKpSixrlNFXabzg4qsY4QlWiBj2CvJzj8dwMYqyGjW9if8g0NGf/jI2KHuET/AjceF5Fjz2tPHkzv3OlbiySSWhLHZqeMJRTT/F2zBEfw94wuBP45RtaXB9/ngzTjWKLsGb6p/QcV8' \
			b'DCnBkQzEfP1Ipp5BnjS5dSjwCYBjEuBAes+/0+LuADTDSaIcaOBbSHcPcCCfFaSZgaehvaR4wggPUQV3uC1U3OcAB8gITuaAwESgRI1kHTCZY4BTBKOss4NFeVEdHoX5ewcQwgAnOz2KKoGcnxLRSFGu09laTZyslBkZTAPCIs4Jh20Ebhs6xBFDhJZMfSV9' \
			b't7kXKLvRGfl7QixBK4wZxGgSsXC6/GxQC2fEupXDLbNsuAV5fv9dpInukcmRiBrTKXSThkMuLspuDxJR1M8PjRCJsG6sHYJhshcNwbBS7R+GmUNP695fT+iSekFrp27sw07dHHTa5pi9mawnYy6rJ7Nl6ka2Yb3r1I09TVHQZEcE4wfPOA2Nu/Q1RwCQHVn8' \
			b'MUAEzHg4GYqkTbNwWOXHgWVn+HTwYdOpz+XsdFKocZOWxS3vbmz80RBnsMzhqPM3OHrCIChUt3AotTuMyuTYNDzqDZh4mOSqt6eASVNaSocVVZ9CL8YfY9I4gUvrzxZbeI8OJ0pg+qFE1qfUgUHeOZLIuvpX9xiYiWaD/WmAxixQYLTu3Hs5BdBYCxjD3sqm' \
			b'4c+l9kimeyMdKXvevRdySpCxAS4kE9xBBj7tdqzAkykeFC7sgQY8G1ei7CgeH2PAo08bPpr8UJ0TxBCKGkLFYcYzE0iy5HybPpxgpT3uPAoV0HBAcwdg6e4ALN0DA0sGKk13xL7IkUClAMp2bds+mGDxHb1rcmwsOSiOQFq2D2bq4+GIqguOFBzZjiOu4Mhh' \
			b'caS5A440R8SRpuBIwZHtOHICUyWXhSPqTCZXr2pC9QSB4oQx4kCAoCiqZzV1elcAqP4FbeIxIiEKWiAeBQvOAgs2SmPPEA+oGR0GDrhFXrIk5TCCV68fEwo3uCAH2h1BgynQUKDheNDADeNkugrXCw7OPgaYJkiwBRIKJBwGEqT9n/Po4R4ggbY2k/8ThgTb' \
			b'PKYtsmq8Y53GEQXWa+xHWIKKE1H7LFBxAVDBKFGgog8VtAMi/583VJyLsmeBihGoADNuH4hrJk8DNqiRn9D0JH9+AqhBEXmIIQcFNAsailIO1nvhw7SPiQcgeY8Rf6HiPyb4g9oJFrR3iL2DBmgBkGMDyImAhj8x0PCnAhr+oUDD37GnsQgq7qDTWaDimqGC' \
			b'Kt6FiT8PARWUL+c2pWncY4J+qOJoIGhwd1HTLNBwddBANepiNSNWQANlxMVIO7CvgKAPVR8nLOh8DncXzcsCDVcDDeT+8rWmFmAD5cTliUI19Bs0tgO8a4KGokxZoGEaGsjt9ehTXq+ShMZuQ82QUHQqrx4SsJGejkblsRGBInhdeKBQ3Iln2ZFqZU2CTlc0' \
			b'Kq8RGLAun4A+5SkCw1V2FRqDc47cVSgKldeICFh9CyIURBhDhHPRm4Rkxj18HxIdRs/QPcY2VmHf3rJwcwVWYBHeYjs4CmpgVp4QdiB8TCHImgXd7kQUKLdvsdtWO2d3n0XPYsM52xEv7EwPw14HdvCB7P3/LQpT+NnwUOuz64BsPJM6YAhlwt6eCOrqzi4G' \
			b'RfUp7oyciGJlAZYCLBuAZfd/E7CoAiyUCTPAYtYAy4moYRZgOSSwXAWo6J3/TaCiC6hQJtxt24oIKBDEWwQSRhGGEMYPBg9LsGERMBAtGCpynCCQCC0eW3lsmUpapJ9oiV3W6qS1DVsHtQiI8FvaSyzW+FDZYz2PdRwNXLU1V2iqy7Eej9XhVH9jzcPKFqsG' \
			b'5iJViWaiJmAlCGWeynqnWPh4D4XjTqidB8h0htwItp6zHwGzVwRmQzH4caCKxXHLLeh+ywOTQsgQy0VJ2ZACaV4+sdmuKyMKfaz55GWlDlJW9VRxXViRZYC+U2z2oYsO9UmQty2ln7aVNPQC5cnQc/FgTyqrpiZrm1tjB6Uha1e9Va7+Hn/b72/g/ugWGjBa' \
			b'0PtbqCFQvJjJUFCODm+61WiHy3ehXFo6cNvTebXQWdIVpAtyGPihM3RwrDIOPoZH7DCBH7Xmk7LDmbPoA1QRePJYVaAK4IFleIIrHxV1a9aHBm+n/8hTi576SW/lgLp2wn/qCdrBXzpwrsntKTg3EpzBEKHW4a7wNe3FuhM61JVhBOhEhzjdjRuZ4lImIxGD' \
			b'zmz8w56Ak83f03/PhVc99y19gxPYaKatSqHNO0qBf6AUwCfb/yim7ZaY+qnIDg5/Go28brIEgB8zf9jf79twz9tyD1vnb7FfDXdKWDeSMDWZNgBJHNu0vfHMSILrXpq7jrQTsduNvSrsZtEWYIpXH9IuJLS9ADwbl7IIN2SgeTrL2WUx2zrJNjWddYCQPATR' \
			b'eTYy5OPBUy6ew/09U9Xw8rtWvXdT//M+7ft62seBzcC4P47TQVP5w6uj1mw6mPPBLk5ys7bOQ78Ahmn3WfOxs2SO1QJUte6i2NqVHy24Qt/s4B7TxWWvTg3v6okSV/dd6ro6+oWTREMrdRi/ubT1kcHNVA94cZJNTDLuit/dZzV3Z1LT8WO8Op5pvcervlff' \
			b'919c/GNjkOU1vj5ApcfJ3q0XzlSv/4xT7oYVHyeTH6D612fQBHACJrs40k01sD74hZMz9x3GxMV1YmyAOV0PFhH7tjbhqsGFs+m7tgsvFOIsc8rZ0JamMdk0cEryii6uEOtG/ffXLlDUeoSLJyHr0iqmW4WtruniCrFuXmDxMHBby3DVYS8U9C9zypmhSuuY' \
			b'bB0owLqiiyvE2Fj6AK2DdHG2tBBUzTn0hVowy5xynuwMtksjSY3EVtd0cYUYG34fqJFgQW9rKK66jws1w5Y55awp4/M9bcVX13RxhVg3OHcbJ96XNpl+OWGZtNXyC9XeVn2A+pQzLpBn5IEzrAzjp1sQqhJd0cUVYt0wfmsLyst6c2tCten7vHLd5MVfseLR' \
			b'neYBNsqFN7Ys7ALoB2xhtbQyE1oa5AmqbaHW3tYLBd13+X72Ug3++4P76rMbm7j+NAWWp2HZVdd0cYVYr2NwQKWCbQg9VnS+Wn6hfuuqDwZXWEay4gs62KGOCz8o53VpitNNsa2u6eIKYS6iKeLasjO4OMvXTYGcbJbb6hwuzvIxTfAHy3LtVmR7syTrXfXA' \
			b'F4LoZhdcBOsmMyLbHK8URmhjtyR8terCRStrv9l27QmJy2NMYf/8y6Orzu3i0ti4yuC0SwMXd5/ZxWufxlT+r2rNB67JX3/xsvv0v82XoY+7fmePPTdL/aKLS3r1SoeLK2lTXeLFpXtyaxkevHS76hIvLt11+hYXWLq4BPwCLy7d9RMTl1a6TXWJF5fu+jmQ' \
			b'SytdVV3ixaXrqrfa0NJhgWofLBpp3S1aYBaSJS604PlIyPu3eflDRpMLyG48I1BBEdB+VNx9gx7dqGtcVt/7Z9fNjmssPPoCin7wr3gHB9xpKG3hoKkqsD3QT14duQrlVSdUG5xi5w0g0DbtSMW7PzWy85PJdnzCbRg4P8B5LxTc1AO3uzWUUAwyBEU1Uybu' \
			b'RM4Cr95i7YaaScuOaAMpfuPwa80CTBRe8l4T2BwdroiD/1a2bICiU9bSEg35tk2bV/BcAp7kCr6gjWcbPMAx2OAGFzf/H8EYFEo='

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

	def expr_frac_1        (self, FRAC, expr_binom1, expr_binom2):                     return _expr_diff (AST ('/', expr_binom1, expr_binom2))
	def expr_frac_2        (self, FRAC1, expr_binom):                                  return _expr_diff (AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_binom))
	def expr_frac_3        (self, FRAC2):                                              return _expr_diff (AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3)))
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
		return (self.autocomplete [:], self.autocompleting, self.erridx, self.has_error)

	def parse_setextrastate (self, state):
		self.autocomplete, self.autocompleting, self.erridx, self.has_error = state

	def parse_result (self, red, erridx, autocomplete):
		res             = (red is None, -erridx if erridx is not None else float ('-inf'), len (autocomplete), self.parse_idx, (red, erridx, autocomplete))
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

	def parse_error (self): # add tokens to continue parsing for autocomplete if syntax allows
		self.has_error = True

		if isinstance (self.rederr, lalr1.Incomplete):
			self.parse_result (self.rederr.red, self.tok.pos, [])

			return False

		if self.tok != '$end':
			self.parse_result (None, self.tok.pos, [])

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

		res = self.parse_best [-1] if self.parse_best is not None else (None, 0, [])

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
# 	# set_sp_user_vars ({'N': AST ('-lamb', AST.One, ())})

# 	a = p.parse (r"?f(x)(")
# 	print (a)

# 	# a = sym.ast2spt (a)
# 	# print (a)
