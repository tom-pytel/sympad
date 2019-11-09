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

def _raise (exc):
	raise exc

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
def _expr_ass_lvals (ast, allow_lexprs = False): # process assignment lvalues
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

			elif c.is_ass:
				t = (c.rhs,) + tuple (itr)
				v = c.lhs if c.lhs.op in {'@', '-ufunc'} else AST ('-ufunc', c.lhs.func, c.lhs.args) if is_valid_ufunc (c.lhs) else c.lhs if allow_lexprs else None

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

		elif arg.is_paren and not tail.is_diff_or_part and arg.paren.as_ufunc_argskw: # f (vars[, kws]) -> ('-ufunc77', 'f', (vars)[, kws]) ... implicit undefined function
			ast = wrapa (AST ('-ufunc', tail.var, *arg.paren.as_ufunc_argskw))

	elif tail.is_ufunc: # ufunc ('f', ()) * (x) -> ufunc ('f', (x,)), ufunc ('f', (x,)) * (0) -> ufunc ('f', (0,))
		if arg.is_paren:
			ast2 = tail.apply_argskw (arg.paren.as_ufunc_argskw)

			if ast2:
				ast = wrapa (ast2)

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
			b'eJztffuv3DaW5j+zQPsCKkDiU/JvieP0GBM7mTx6p2EEgeN2D4JN4sBOsrNozP++PA/ykCqpVFLdR9UtwvIVi28ekt/HxyH15PVfvnn25RdfvvpL85f/9e7Xf4RX/PnF88+/Da+vPvn6+asvguHzrz95xq+O3yq8P33x6suX8d1Fg+IIPvsS4vjmi0+++Tcy' \
			b'vsK/nz7/6w/PPvnm+TdsfvlJtP1UjH8T41dkxHg+DQn/O2QoGdD62Xdff/F3+JUM333+3atnX/09msDjt1/D3+8+jYHI+PzlV9/+/ZvnkMLLF6++g0y9+g7K9LdPwP+LV9/+FYrz4iUGxr//8TX4/gLl9CW4cgqfYohnX758+UmUHVh8/eKv//ZtzNvXMe9f' \
			b'F3mHX8//I/z55OVX4e9nn36BbmD76jOWEJg+FePfxMgSev7FN88h4a9fvIT3Zy/+9uIzMDzjivgW8/fVF1jIUORY3v/85vkz9PDZi88/B4m9eoGN4Bnm5ZNXn4EcwOHLrznBWH2QT4r1WSjtt/ENLeHlJ1998+2XEP5bFPzz/3wG9YJW/5tED6+O6iTE8uzf' \
			b'g/HjHz9+/PPNh49/ZuaPwfz2zYd3v//w/sMP//jx54+/v/mQOQdjeL1Bb+/++7fg5ac/f4nmj3/89u5D/PHru//64c2H/xK3H4Pxlze///D2/c9s+vD+/4qJEv747uPHt8n0WzLFaN78KMbff0+J/fPN29+j+TeMlaz/+PWtZPSf//xNcpMy/fNPyfjTr7+n' \
			b'/P7yx88//PTLb1kx84hSISWeUN5o/P3dh2T955sPeZTBEH/+kefuzT/+EY1v//jw8/+LP/774zsp2Y8f3rz9P+/Sz495Tv58l+L649ef3v+aEn2T/L+V4qBQU87fS5R/ZPL9NWXpx59+fZ9K9F6kHvKTpP72/S+/vEmBf/vp3dt36UdoT1mGfvv4+/uUSKra' \
			b'lLX3P0vuMdLix8cs5A8///nm52TxkUJ+37x+srN94/qbhgwDGIyDP74x/Q3/DL/Q1Ic/rglOO3dTWNAvH8OFAH20AiP62lEctnmiGz00O90YFQw3yRbtxGKHmVGe/oTc7RS5RSs17FnZwgqMwdRZ+uNMs+soq+EXGIMJAvYNlJFy7MEAwUNmMCOG/nh1wz9D' \
			b'3jCK4BDy1Dn4fxNthvxX17IB7CBOA2VXLZfdmJtoy3bJYqcwQBfkC8FD9hxnHMRA0Q70x+lg092wFRihLlHioQz2JvsZzZm9otcOk8OiNqaNzgYM4a3Z/oZ+7AxbUm4dFqqLhbLJlu32LLRYqNJip1D2OiSsMeWQF/xjSTKQNYMF1Jb+2JB3SymEXzuN5bBQ' \
			b'xiE52ORgNP3xlKKBsmBhOtU8gSYBVUVJgY3Lf3l+gxWE7UKxIXGOKv40Y6tYtaW92/858uH3f074UKVVv/+zCLQzKsuatHrOxMjCjy3yjhJcn2jFWYAW6wtr+bnTVKmhLevQUKDK28aHECG9UAGamuWUM0BSeI7wFWq79LXT2PUBn4bGd7FFQ4fF3hNqhboi' \
			b'IIEJoYe8RwbHZC82Dm1sKzaebDqx6clGRZudQoGrgf5YlzKZrHxuBUYogaM/QX43N2IEk6K2HYsKksAGaTU3eqpsC22bgCLUSKcF+kJ6HQonCFKTD01/HDR4EhQGwC4IiNZFA2aug6bQmNjhGXuCJVnx75bjBHBpIDf9vn20CRbYxhT92cXuHowGXTr8D+Kk' \
			b'IGAAgWn648CCcUajESQQYvMWM80/PYFqkG3XJf5pAu5Aewr1wECEHhSR0aRrQGGUX6jBAFXoTG0Z+kGsmCHKP1g+cdIx8ecg2QrUgt40ZEknU7SjsoDBRYOPBiKq0Mah0B23QvhpsHuMreRnCI2mjv446K8Mwh0aIYG2YV9Bjt2Q8xN4xzanLP1xberw4deO' \
			b'cmg7+iPDhfCDiMa29AdGCtx7bItGqPUhOt7wz/ArOpDf0KK9J8EPsV6wH6EBwrsUHoYEDsO7NjrAWIRtaFRiHZUY4C1EFwZGrwM0hKruQncJMoF2jiAeGCggYcDO0CMDtgWkCRU9NEE+obP3tulDkNaH/30I2oX/KvzX4XfwExp6yExI06HIu9aG/6F5hSZk' \
			b'sZ2FcOEJIUPJulCnnYIxBPgMTTGkGpprMJim903fN31IuG2GrhmCj5CvLmSsC7nsQjY7iAUyhdCowTEkFkpnEPVpkBbkCVkzgIFQVA3/QwZCoToolW4G0wzBDcKH9LuQgS7koAtZ6IIIhr4ZQhRt+BXkE2os9PLQnAfXDL7xfeOHpg9C6ZpeNb1u+uAvFLQL' \
			b'JQ0NIXTHMHIJQ7IABA6GN2EUGsafoTMAXPvQWTXge+jA3jWhsjvIZ8ioxaFgEBDIB+ooRAjj2GC8gX4dyhCq7wnUG1iEuguv109CBuEniAdeLfky7BoKA9YggBsciILrayBA/N3Dq9b5mdX5k4EqrxuopluutZ4qE2oB6rinSsUawnfPwbqOm4zit2YPliPC' \
			b'Cgw2PTelntoORx+T69BUEeLMW8vrJxZrs5BlJkWS3pTcSF5JTnvyKWUyJwoWQmiQTlEDdO2Z5IdBEFoatmzPLRva1s0DZUp5ypSyD5gHlkcEDKVqR7+Ejk7AXuvpvOvpCeYLx2Z9ra/zry8AQF0r6vwr6klHxA2MjoyVxIYCS+JhsURp5MVPxaViPWBxpAVN' \
			b'tJoHHzuBiGnWgFiGc0YkH1geC8k3QQC1Rzx8j9A85NaGRnQmTt7UUBHt/OsvzOlxiNCFmLsQdWehYCFzFooeQofi1lo6g1oaai2dfy0Nba2lC6ilrtbSudfSk4HHFZ2Ja8l9XBU2da50CTWIhabtgIHHhrT8/0S3sW55GZC3B3gIGTcJ2NX4Wt0XUN0m7hlR' \
			b'rQ1Up4PhyhxwmFknvUuTXtoo5dyRDe+u0V4pVHRyfdJpRkdNXWzgHTTNe7aaN+Di7Ix3YwfukG2ctDHYWgpm44zbkvuAearVlLYvBt5C8bRv6WlwDtuksCleV3vWS7RnSuipPffUbnvNG83cTmnLCpZLCWRgCAfuNu77Eeg48u6osXvaa2tDCi1IAooICD9c' \
			b'l4iDdEhojvDE2yoWEgt1YkeY6AkCvZuTTuzmVyYlTx3TU8f0vjYeEgsPXWnsmgmCdksJgWzc9rfU1HC3+3vULeQBMmiQV2W48x/lorabIjU3VRXXzrB+NB280K7WzxnWD+h9KtYsDO9aEQ+4o2BrDznLigFpK9aeDe9aJWdQJS12FhZg1fm4Q50P5IU6DD73' \
			b'HtEjj4Pifq2uC6guY2s9XUI9dW2tp/OvJzyYhNMYi3R1BsQ5cZAKzp9wNjtE6zpwuTv5QxYe7DANLXlA4jRvoBWqnm01vVvFbYG3BudP4H3PJ/xgNQUD16Zyi7WlO6oHWjimnSrP21y8C0v7EUndBTtxlf1t9BSEa1B5pa5geffc8jY56jCg0HknHBXCsEPQ' \
			b'SRrQw4QYhpZeXJdQOdhPat1srhuIkYRJg9UqxE0TaBRildfR8jJVXqvkZau81sjLOBqMwQAc1eCof1axHRbbYKqYjlBD4yE+bXbGIT2pDKpMiRB1B2m+is3PWrgtq4pzLE5HQvI0mCt1OfzAsp5UVUaloJszK08Xb+jpaUbY0/yw5zkdHzymwRbcmIGBLPl1' \
			b'PBhzNK9lRZ+rag+vQYEQF7mHqoB+/otyr0HRs+oUPPDydZvrBV4ZXKAqpGglA7j6axYHrSmeVa6edATmoAtN/OavmN+8rYD5oPtIjoflbrjmVthec+Fd7YIP2gU9L+F7dc2t0NdW+MAKBTh3gZMiig6IKL5yV9NhA3jBlPMGL4yGV4+/SF1Us7qovonailpu' \
			b'm8R1IfQaBK9p+6vef3DuLSIUVNOGvKYrcamO6W2HWMHwAqzg/X/yRCF7ttVU+VrT73hBs+7YHpsatrt6pdY5VD0oAOASXNX+Po/q6EzsfT2f2xsijuqoRqBYfQBXViuInk/V+dqLzqEqQHFGk+KMJsUZHRVndH41DMhHRy0QfWDDhdhsfMtIZ6at7YQ17M1q' \
			b'2ptlR02OlCzZWs6ORaWsunE2PX+wrt4TMj2xwuZdVZnWyw63VBXvXmravdS0e6lJQ5Xxge76h41K7KiOrFHT73u8/IPGzy1rw3p+09a5o17uKZAjjPKEUZ7gwVO63st0y9S58kPOlYOADU9nTdTmpBmToRmToRmT4UmR4WmQwXkOonrkGJ5HiZYnu9ukCWDm' \
			b'OajvKH1KoccE6kjjodsH6TSY/cs4XD1bcxHV56gD0yTrKhdkkWQsa3RZhjobZ5wEdZagjnzRK2TV3vDHBCws8EF7sLXFn32L76m2e0Uvqr0mYZmtmpCLHcbRmM1RjwhJuvhdIVd7wqX0hCcdTbMRwRwOtUzSYHS1FyxON3ts7oAgDoezdLQv3Z3oqGt4JgvP' \
			b'kva0iEmanjCVh/vK4KoyW7vEg3eJkIonbvBUs7H2eu4fvATteG7i+c1L1Z1lnfAeQ9QetNSDdBXTEXQbhGJiu1Pc3gA9Klo8MFqoZiCYGLhWSCWgbeCjy43CryfBNi98QWnImhsJoIfqUx1EynUxoLgND5R49JRJjooQWgFlKK/Y/XJBoRQXZyQSajOhRlGU' \
			b'sf0PmaA9tU2sXUebbKi9YJmzghtc/wuX3MINt3CrK1zpCve5wt2lcHEpXNYJtwHD1bdw0TDcMgxXDEOVQIuFs/DwoRX4jAfsFcBGAVQ83F0+QNMOwglzUQVH6Vv4xH1osnAzFLTekF/VgvyCP7gdAk7hwwVeoNgBQoWqArFCMwfZgnBhMRKaJixWhsal4Gi4' \
			b'hv4d3OHgWGhLCvYWQzkV0DMsS0GHAwwAfaVQHgU6nKC+E+SpYCWsh8WOXailHj9L7hv87jh8Qd3At8/hY+N9Ax+cV/AVc9Xsevjoegtfrg/Z30Ev3cFHy+G779AtdwqiwA+zw7fk4WvoCmIO5d9p+JJ7+BF63g4qZgd9btfhF80h9lAG/MY4ftddgzukP8CH' \
			b'49EdwkPl7qAb7Qbw2cIv/E59S998D31oF8q2w+JAPoIwdh4/yh7ChCaHn6WHdCGUho+Mw0fR4avpkE6rqJQD5h7zAcUPBg8fP4evpkNcLWROwefMgwt8Ud6DRag7/Pa5gkigEAFedpBVKGEPb4gaAGwHqIbfQ0eJoxSCd/gcPMgJRQNZgnDBsgcxhN8DpgJZ' \
			b'gwoCcNp1aAj/gxnlF+ILbXE3oJg8fOu+gW+q70Lf2nmsCaxIqED4/Hxo+7vQJnah7e88fIMdigoig6DB3veUDYDlHfQw/Gg9phx8O3iD4HqMLyTVo2SgncB//T3ACoBJhZLrgZKKIxVH7gBHFODIHH64KQjxMpLjgaCRJRxGlHJkB8Ox28YVGHGqbCN3Bcyg' \
			b'nuUC1FwqxID2UwEzuoQaGK8C3MCR0oOQ40HOfgFc/Dy8eHCEaiDDGGa8AI2fghp/T2DjKX/aN/JvJeD4oyDn8pHGj7EGspThjUfE8UuY0/zLPQXq8k+BvHr44f4HFKsXgIhmo0OEI5x05dPVMSjh7HS0ukxLzrICPQdTOHckPaNj8IqniqqYJE5OOgW+yjmz' \
			b'4BiPmGjDrYA0lImliTh8eiX/HMbejHi0mIDwFxchIgz2TVI5z9XQeZ1+bxESdDyCBDpYLkC4hHqxy7AJE+ZF6AzusHRQQGjwA9/4OQlKNcEp3JgC33dYC6tw9VqCVn8kvLYCsXC2rIBZl0EtLAYFO7jFNcEu9F+oMLuAvB0ueQD64osBGMyhKPgiGIYGYwmI' \
			b'oxEXcnqCY0yOEJmc05PgGcPs4TPiDAE0ri/ByhRC3HqwxswMtE61B9i0/Cb/9wBcMgztPRWg7YvSoJAoKRROBu7jFKb+JwLgMkZbIgJ0hIE5E0KWOMm5SwlHjmAvQBUpHYusEY3L5NEdwR+xzjMWYasTuaSQDmiJbSAWrEXillxcc/wSPbjMb840WComm1yo' \
			b'iXeIcVx4hS5LxAPo8HSHPbd9GiT0P3gb4AEiskcPii+UfyL57K9+H08+doaAjiGfSjwPRDyOiMctEA8Iy80P+6F3OOYbNipD7xatEt244hG6cZN0I4sPEmQL1ziiGjfBNHnUeyyTXLQfZ13cHCUQ2WVggpnxjnlhXmGpYndxMsMoWKUoesuSinzCGegzP75L' \
			b'vpe5xB3BJRxZziVkdSqXSLE2EokTIpG4ZnmEZWUl1ZxFXMYiKbK1HGJvYVXlRAJ5eOpYSxt1vnKBtOGJNpZWiroDS0Ud7jUTZ7AR2otnzvDCGb54hDMml5A6WUOi6NezhSe2mFhIKvKxxxbJRftxpsXNUQLFXOSA92INCi2IJEheGU/kgZAnokyZKjj1PvPm' \
			b'xdcyVfgjqIIjy6mC5XgiVUjJNlKFrGdlcc1SBcvKSqo5VfiMKlJka6nCVaqoVHEVVDEQVQxLVDEcoAoKjw2BjdBeBqaKQahiKB6himGSKgahimEbVQxEFcMEVeT52KOK5KL9ONPi5iiBgipm/GJGCqoYhCrGU4o8EFJF9MNUwan3mTcvvpapYjiCKjiynCrI' \
			b'6lSqkJJtpIpBqELimqUKlpWVVHOqGDKqSJGtpQpfqaJSxTVQBXRYjVt9h6kCO/YMVUAhW6KKaISytkQVmAJRBbmmJ1EFet2jCrBlqqDoV1MFpuHxNaaKIh9jqhAX7ceZFjdHr5wq5vxiRnKqQAuiCpKXUEURqMMGyH6IKmLqfebNi69FqiBfh6kiRpZRBVud' \
			b'SBVZybZRBYRiqsjimqOKKCsrqWZUgeVhqpDI1lJFv243/TERhq+ccZWcoYgz1BJnKPTj+DXFHOSEzMFGLDEzhxLmUMUjzKEmmUMJc6htzKGIOdQEc+T52GOO5KL9ONNFQEdpFORxwHtJHkrIQ43IIw+E5BHFyuTBqfeZNy++lslDHUEeHFlOHmR1KnlIyTaS' \
			b'hxLykLhmyYNlZSXVnDxURh4psrXkMVTyqORxXeRhiDzMEnkY9EPn/6bJg3wgebAxvlu0SuRRPkIeZpI8jJCH2UYepBILrz3yyPOxRx7JRftxpouAjtIoyOOA95I8jJCHGZFHHgjJI4qVyYNT7zNvXnwtk4c5gjw4spw8yOpU8pCSbSQPI+Qhcc2SB8vKSqo5' \
			b'eZiMPFJka8mjayt7VPa4LvYgpV21pLQLGbfEHnaGPcgHsgcbSced2EO0dck1PcIek9q6SrR11TYlXUzD42uPPfJ87LFHctF+nOkioKM0CvY44L1kDyvsYUfskQdC9ohiZfbg1PvMmxdfy+xxhBJujCxnD7I6lT2kZBvZQzRws7hm2YNllaWas0emfiuRrWaP' \
			b'7ryOgVzsAZDKIxfII6RMpZaUqSDDpE+FL+YRpBFyiWxCv5BN2AjlZsUqJYpV5JoeYZNJxSolilVqm2KVIsUqNaFYVeRjj02Si/bjTBcBXRtNBaEcCFESiqhXqZF6VREICSVKlgmFM9Bn3rz4WiaUI9SrYmQ5obA0TyQUKdlGQhH1qiyuWUJhWVlJNSeUTL1K' \
			b'IltNKEsHnCuhVEJ5rISi6ZYIeB0kFGjaHRIKvphQwByKgi8iFPYHjSIalaE3XQsVCYVc05MIRU/eKwG2TCgU/WpCwTQoq2NCKfIxJhRx0X6c6SKga6MpJ5RDIQpCQQsiFJKaEEoRCLpokiwRSsxAn3nz4muRUMjXYUKJkWWEwlYnEkoW9zZCgaBMKFlcc4QS' \
			b'ZWUl1YxQsDxMKBLZakLBg+p46ITYgalBIymM6MAC+AtKz0A0gnMCz55BkcEugRkBGIFIBI+eb3Jw0PGhw+vmDJ7v6Z72yruVd6+Ud2lBUC8tCEJzpgVBnS0Ighl41wrvkr9OpyDIu7wsqGVZkFzTI7w7uSyoZVlw49l9TcuCemJZsMjHHu8mF+3HmS4Cujaa' \
			b'Ct49EKLkXVkZ1KOVwSIQ8m6ULPMuZ6DPvHnxtcy7R6wMxshy3iWrU3lXSraRd2VlMItrlndZVlmqOe9mK4MS2WreXTpTWQmlEsqjJZSBCGVYIhTyA4QyZIQyEKEMQijkDwmFjUAoAxPKIIQyFI8QyjBJKIMQyrCNUAYilGGCUPJ87BFKctF+nGloauLu2mgq' \
			b'GGWYfUaMMgijDCNGyQMho0Q/zCicgT7z5sXXMqMMRzAKR5YzClmdyihSso2MMgijSFyzjMKyspJqzihDxigpstWMsnT0sjJKZZTHyiiGjtiYpSM20H7plA2+mFEQXjy9iFHYHzSKaFSG3i1aRUYh1/QkRjGTx22MHLcx247bGDpuYyaO2xT5GDOKuGg/znQR' \
			b'0CVTTiiHQhSEYuTQjRkduikCQRdNkiVCiRnoM29efC0Sijni0E2MLCMUtjqRULKSbSMUI4dusrjmCCXKykqqGaGY7NCNRLaaUJYOaFZCqYTyaAmF9prM0l4TNF7aazLZXpOhvSYje03sDwmFjUAovNdkZK+JXNMjhDK512Rkr8ls22sytNdkJvaainzsEUpy' \
			b'0X6c6SKga6OpIJQDIUpCkb0mM9prKgIhoUTJMqFwBvrMmxdfy4RyxF5TqpmMUMjqVELJirONUGSvKYtrllBYVlZSzQkl22uSyFYTyspjnJVQKqE8HkKhA51m6UAntFw60GmyA51gBkJRQijkAQmFjUAofKzTyLFOck2PEMrksU4jxzrNtmOdho51moljnUU+' \
			b'9ggluWg/znQR0LXRVBDKgRAlocjJTjM62VkEQkKJkmVC4Qz0mTcvvpYJ5YiTnTGynFDI6lRCkZJtJBQ52ZnFNUsoLCsrqeaEkp3slMhWE8rKo52VUCqhPB5CoV15s7QrDw2WduVNtitvaFfeyK48+0NCYaMy9G7RKhGKLR4hlMldeSO78mbbrryhXXkzsStf' \
			b'5GOPUJKL9uNMFwFdG00FoRwIURKK7Mqb0a58EQgJJUqWCYUz0GfevPhaJpQjduVjZDmhkNWphCIl20gosiufxTVLKCyrLNWcULJdeYlsLaGog6c97dVwSj9NK1tuz6/UcnnUAp+Fgl3IfoFagqCgPfe0Rd9nW/Q9bdH3skVP/nCLno2wRd8Tu2CCvEXfF49s' \
			b'0fdT7AK2cYu+38QumAZlde+qSzNkGdnbo08u3K1nHoBN10a/kWEG/FrhoXCjjfpeNur7kmSKQLhRHwXMG/VcRbk3L76WN+r7ZZKJkeUb9WR16ka9lGzjRn0vG/US1+xGPcvKSqr5Rn2fbdRLCdeSzMFDoZVkKslcBclY2rK3S1v2QUjQVmnX3ma79pZ27a3s' \
			b'2rM/aBfRqAy9W7SKJEOu6UkkYyd37a3s2tttu/aWdu3txK59kY8xx4iL9uNM5w8gpkt+E8dgMofClRxjZe/ejvbui0DQX5N8iWNiDfWZNy++FjnGHrF3HyPLOIatTuSYrGTbOMbK3n0W1xzHRFlZSTXjGJvt3Utkqznmks+Jdsgxuq6PPTp+aVdyjJ/gGb9l' \
			b'QkNco5e4Bto7EY3OiEYT0WghGvaHsxk2wmyGiUYL0ZBremQ2M0k0WohGbyMaTUSjiWgwBWgktFzCisd5fvYmNclF+3Hmi4AumQq94wMhyumMUI0eUU0RCKczUcI8neEM9Jk3L76WpzNHUE2MLJ/OkNWp0xkp2cbpTItdIk1pJL7ZawmcSTLD0kN30WPa0Rnt' \
			b'SKSraefMPntcN2SunHDudUJjaEJjFkgGPoZqaDZjstmModmMkdkM+cPZDBsVv1u0SrOZ8pHZjJmczRiZzZhtsxlDsxkzMZvJ87E3m0ku2o8zXQR0bTTl5HIoRDmPMTKPMaN5TB4I5zFRsjyP4Qz0mTcvvpbnMeaIeQxHls9jyOrUeYyUbOM8xsg8RuKancew' \
			b'rKykms9jTDaPSZGtJpR67r4SytUSCu3w26Udfvi0Nu3w22yH39IOv5UdfvaHhMJGZejdolUiFFs8QiiTO/xWdvjtth1+Szv8dmKHv8jHHqEkF+3HmS4CujaaCkI5EKIkFNnht6Md/iIQEkqULBMKZ6DPvHnxtUwoR+zwx8hyQiGrUwlFSraRUGSHP4trllBY' \
			b'VlmqOaFkO/wS2WpCqefuK6FcK6E4WgZzS8tg0BJpGcxly2COlsGcLIOxP2gU0RjK7XgZzMkyGLmmJxGKm1wGc7IM5rYtgzlaBnMT+y1FPsaEIi7ajzNdBBRTTiiHQhSE4mT5y42Wv4pA0EWTZIlQYgb6zJsXX4uE4o5Y/oqRZYTCVicSSlaybYTiZKcli2uO' \
			b'UKKsrKSaEYrLlrwkstWEUo/dXw+h9JdBKnq476ueB7rqeVggFkV+IJ1BiAXMUJxBrnomf3jVMxuh7AMRC6ZGxEKu6ZGrnocpYgHbeNXzsIlYMA3K6t5Vz3k+9q56Ti7ajzNdBHRtNBVXPR8IUV71PCRiIakJsRSB8Krn6IeIJWagz7x58bV81fMwTywKLx7g' \
			b'6545wvy6Z7I69bpnKd3G654H3HJMVz5LfLN7KywzKylnBINlYoKRyFYTTD2Gfz0EcwHkcr8zFjqG75aO4UMzpGP4LjuG7+gYvpNj+OwPZyxshBkLH8N3cgyfXNMjM5bJY/hOjuG7bcfwHR3DdxPH8It87M1Ykov240wXAbmvjo7hHwpRzljkGL4bHcMvAuGM' \
			b'JUqWZyycgT7z5sXX8ozliGP4MbJ8xkJWp85YsuJsm7HIMfwsrtkZC8vKSqr5jCU7hi+RrSaUegy/EsrVEooiQlFLhKLQT3xFQlFEKEoIhTwgobARCEUxoSghFFU8QihqklCUEIraRiiKCEVNEEqejz1CSS7ajzNdBHRtNBWEciBESShKCEWNCCUPhIQSJcuE' \
			b'whnoM29efC0TijqCUDiynFDI6lRCkZJtJBQlhCJxzRIKy8pKqjmhqIxQUmSrCWXpGH4fqUQ/IhKJDHJb7HEMc1TWuDXWCE1BeVCG7NbuymvalddLu/Ia6WPyw5iWnHEnno2wE6+JNTAF3onXxSM78XrEGtDOwDJuxOtNpLGLql164jQktkT5v78bn3Kp/Tjj' \
			b'4gZb8Xq0Dz/jFwtcrG4BwEIDVKMjkJAfCoA5w2GdzaYg7A6UEbMPP70Yj9iJ18usESsz34knq0nWoHIcs7QFnixX68ateI20we0kSWp2L55ry7JJeSh18DJiECxb3JVPtTZiEDM8xVENU0howE9xhbLVT5E4Q0d+Sl/tTJyiV353uU5S6iTlnOlm3SSFNInd' \
			b'kiYxtD7SJHaZJrEjTWInmsTsDycpbFT8btEqTVLKRyYpk5rETjSJ3TZNYkd04yY0iYt87E1Skov240wXAV0bTcUk5UCIcpIimsRupElcBMJJSpQsT1I4A33mzYuv5UnKEZrEMbJ8kkJWp05SpGQbJymiSZzFNTtJYVlZSTWfpGSaxBLZ2kmKPrNPMdtHyCl0' \
			b'0qxyy1lzCykVuyWlYmiCpFTsMqViR0rFTpSK2R9yCxuVoXeLVolbbPEIt0wqFTtRKk4prKcX0it2E3rFRVb26CW5aD/OdxHQtdFU0MuBECW9iF6xY71i9hZJJg+KJBNFzCTD2egzb158LZPMEdrFMbKcZMjqVJKRkm0kGdEuzuKaJRmWVZZqTjKZdrF4WU0y' \
			b'S8fuz3Ul7MFXvyJlRLpQGUVEeoi0cEGUcP50QJpbbklzyw3zq1mOwiMFsBEogLW1nGhrkWt6hAImtbWcaGu5bdpajrS13IS21j7mp1xpP86ouDmKtED7Gb9urJvlRDcr4TuLq823y0kJy5H6lTtK98od0L1KOM5p5ThOVqfiuEhnPYQPAuEUx0F9q5iOlYaW' \
			b'Y3imbyWZOgbDEbuXzq5X7K7YfVbY7Uk5yi8pR/luHrvhsh1WiIrGUFbPClFeFKLINT0Ju/2kQpQXhSi/TSHKk0KUn1CI2sNuyZX244yKm6NIc+ye8+vH6k++28PuKK4cuz3pOXnScPJHqTf5I9SbYmQZdrPVididSWc1dnvRbOI4DmJ3TMdKQ8uw22eqTZKp' \
			b'o7F76Zh4xe6K3eeF3bSL7Jd2kf2BXWRPzojdbATs5l1kL7vIXhePYPd4F5mwW7aR/bZtZEzD42sZu1OutB9nVNwcRVpg94xfP9419nofu1lcBXbT/rCnfWF/1J6wP2JPOKaVYzdZnYrdIp312K0FuymOw9jN6VhpaDl2Z3vAkqmjsXvpRPa5YnfVHnp4nL+I' \
			b'JXfod4D1bgnr3QGsd+iMWM9GwHrHWO8E613xCNa7Sax3gvVuG9Y7wnq3j/VFPvZwP7loP860uDlKoMD9Gb+YkQL3neB+vnNbhAAKIGkyC3C6fZ71LvleZgR3BCNwZDkjkNWpjCDF2raiDsZICxLXLCuwrKykmrOCy1ghRbZ6RX3peHVlh8oOl80OntjBL7GD' \
			b'P8AOHp2RHdgI7OCZHbywgy8eYQc/yQ5e2MFvYwdP7OAn2CHPxx47JBftx5kWN0cJFOxwwHvJDn6GHfIQyA4+YwdOt8+z3iXfy+zgj2AHjixnB5bgiewgxdrIDnI2Ootrlh1YVlZSzdnBZ+yQIlvNDktnoys7VHa4bHboiR36JXboD7ADPsQObAR26JkdemGH' \
			b'vniEHfpJduiFHfpt7NATO/QT7JDnY48dkov240yLm6MECnaY8YsZKdihn2GHPASyQ5+xA6dbZL1LvpfZoT+CHTiynB3I6lR2kGJtZIde2EHimmUHlpWVVHN26DN2kBKuZYelg86VHSo7XDY7kPaOX9Le8Qe0dzyFR3ZgI7ADa+940d4h1/QIO0xq73jR3vHb' \
			b'tHc8ae/4Ce2dIh977JBctB9nWtwcJVCww4xfP9bk8cMMO+QhkB2GjB043T7Pepd8L7PDETo+MbKcHcjqVHaQYm1kB1H0yeKaZQeWlZVUc3bI9HwkstXsgKeWTWMXPsX36EkilDRAwu19fO8uCaNdQRr2sogDzrfe76V90N9gr5fUiHZ6aY4xQAzzRILx8TGz' \
			b'ZIbS80RDyURD9cUj1/ZNTjSUTDTUtolGPNesJmYaRUb27u2DpCHPtE8xyreEg4qguQa1uZ5YBTOoZoOp8bRDzUw7ihB4d1827YhZKMrRJd85seA1fFPkoiamHnCN5JhgYqT55X1kderlfT0ecFbb5x+QDyv7F5ytw9f3seRsKldxfV82CRHJZjSDNvBXd/DX' \
			b'oU1v8a9D18A6io41qx44J4jt9SHG2eeaAfnFMLMwleQ8QiRyHIPMah4hWSApZLOGAuBH+kKFntDAgH0EUC+O7HNgPgWQzXoQjuB7CHQBbAuQjQAbQRV61dGAOguliKEInoicETYTTk6AZETIU+BxWVsnAuFufPV1iWNjfZtS0wagarenHDmLTYuj3gKOTgUi' \
			b'QKEN6BNh5zDg7PbOHSWEicACKNEdRonJQen9AEUcWIb6vXa4gGHMJGSsgYt1AzAcUl0eZmQDKKjRih3jkQtIbRo/1mOHWjvC8PeOHeOJKICIvlsg8XDAH9xDGPgw6jkDy62MQ1YCyyyoxAnduQMLZjT/zyDT9fcDNEgHsNAEs0R9xEbOOQDPNOgokMU64Gn+' \
			b'FVro01ASnOToDZOcdgmC2ttGoYg8NkOe9vKHMSDerYizt+Q0Wm6y0Di6bMkJqs9lSGQEjWAKDnd8ISrBwgFMomFS7fJlqFD37S2iFSJVXHdagVbmIRArIZQXhIJqfVTDIQWRn4BMUDXzQyJD6567jj/zQ3UPTdZnmAVtMOFWXAvlZR2QMoitQ6HgV0xtUlOF' \
			b'Hz2Oqsxp6zZwB97kLsDdQFrc9oWVe3sY0nB1/gJgDSGtWzlDc8fN0GCB9V4GUzMDKZPDE7bgcxhQjWdpUJVQbQvwhFm/KIgCeIL2sXrWZo6ctam9E1OTMzd762vDdzZmekTjpdXLPv7+l31udcnnIcc62ThnrI994eOcTcs+9vaWfVzz+gw2lWZ1Em5/g+mh' \
			b'p1nDQy3sCGTgLvNlbiyRRkjP2h72XjeazgQxYLb9kBtNzb+Gp4F0cMXGnwV6LCMGZChUHWgIXDR6rEYOUCy9lf2ma9uXJnUvPE91GysrZ4IdG3CDhTALIOuHHP2lgEYwQ77geucHA4+x0uF9A0h4m9sAkriKW6zeXh+ohFR7VB3dwUjmYcHFnQW+7CA0xD7c' \
			b'AsyoPi7Jjhdih+2gAzrZ94o7/m4x56iTMmNF5/teLbHnP3jp8g8rnSPYwA8IcvdQc8w3jkqwwa8IPdT6ib4tvMmGNUHG24c17T0jTIYuqnvgKdEDoEtFltN0dktUgeo7jxnSA4LKHQBKdwKgdA8IKOMzXhVQKqCsBJShAsodAIo6AVDUAwKKroBSAeUUQIFq' \
			b'q4By+4CiL2Ql96q2fM4UMc4YLG4TGRSW/lI2d24FCZp/hY7xFCAR9oRDfVRQuAhQOEGD5AKBAeO7RVzA+B7rpu8tKosgNMBdMFY9BSxFjLAVIypGPCxGYJ8+s8HD9aKEc08DaCM2nIdGasWGR4INDAsXP7G4A2ygK9no/xljAw4coEHDSAIauX0KiBYaeXhb' \
			b'xIxL0UOtmHEhmKEqZsxhhkr/LxszLkUNtWLGxMnbEC5IUcF1heeDH9jIz20tEzN1DvBBEHC3sxH0uIgeCu+ND9bLOGKGpzvqbd1TAOLQ+p8iDoZmGizw3hJ7gm5pRZI6+kjoMZwjepzJ4AOTvXP0GG5j7HEMZrhTtEUrZlw5ZmDPfoy7p7eBGViES1v/NP4p' \
			b'EkFo52AgjDhFAbRixFViBFk+ag2LFRiB0ng0eyQG1jKgbw04nsDdEneKTmfFiKvCCOyqV6KGdQRIYKYe306qhs8YQYcIsxCtESOqmmbFiMMYgX3kyjQ1r1fZQsNAoiVsqNqaFRvg62nQDs9HWfMssIH65nVBg4LlB/iqn4cN0xZ3Sl3V1rxWjIC2fAa6mmcL' \
			b'EVc5fOjwsAcNH6qy5tVCQ1ehoULDAWi4FJ1MyFm86u/eYWLqu8IPdcVfPTi6EjSgCnchZP9w8AHyPA8QgdBzULL6ZLk7D+XME68lb/c/bH7uY40tHyFPX4HqD4858CtQVwIi9LX68v9mHSwIO/6y9yUNSTZ+mDuCCZb/4NgEdIGPGp/07dMA7zg8OQ+lzYow' \
			b'FWG2IozZ+78dYcyVI4xZRJhuLcL481DxrAhzmwhzPehi9/5vRxd75ehib2NtJUOWrnkNiEJwQlhCQEIo4hA/HCAHwAZhRg4YiBax68funrqooa6J3XKqSyrpft1EN4ldo4cr/vshb/qx1acGnxo7tFNq44ZaNjbq1KCnGrM05NQEU6tLbQTixrbRzTQJ/KAa' \
			b'Vz5W+l79pCoJ1QFz01C7tyB9AuEEv4PUA0BoURduZX2009BV1MuOutPdVgwUBbEiVZDKKwlad1FRqSMfXVnYq6Y61F6l6VuptO5QvT2yuvOC9dP1F2H63uoQdFWCEDqPQsA1S48OsEE9hDFOsMe8G/LvcmsYwODaUkDm1/hVameCgwrlDP+/vwnmJ7sArCDh' \
			b'DvztQj8P4yX0FMQxoJ0GOxhgAO/j18c7/EivhY9mhhoP4g4UEqoaaho+i42fxo6JBZfQIAKvg5jpC+Iu+9xuiC2MlmDzHUZRoWnByAJGifjtbBgnWsyEOSkTYVy59A9TsZCKP5QOf99zWEjQwkDT7v2Tr3jqsRum76bTt5AF+CRHi7dcq6nstHs5wo9epNV2' \
			b'uNAVPsfpRzkN4+fsH4xFHF9BK/8LH97kv8AHDEChCQLAwAWuACLwD4vk77lIIRkH30QBIm5O/4df8BlaLEq/sSj9XGlGH/abLJ3WB0oYol38B/OS0oZmCZ5nA7krzAEyn1jqYbrUerbgAchhSjaU07B9aXSlQNoWVTJhwI3qmYrOccOIE4bMdGkL3WGFF2Yn' \
			b'AXa82uhZmIATHQvVzAsWrkjAqZMdCbllQbck7MBvJHD6FjoJHjI68QyTtuI29385pkOh52Mc2YyMh/M4zsr+C/5jEwk259YzcIfzoR4SSreh44QBUBj/3Gn3cefShVSz+onjzg1BDz6KV6ru9qFmoc4RT9VMgzD33Sh0cw4PrKeNrXC4ersPNQh9fuBpmod7' \
			b'SCgmCQU+DTfcbV8Z/KV2F5h7wzPQsnZ/p4+66wSOfKiFzMzVju823R30HJi5nvDAvsFpUZBs3Lj3wLrB/fShtrvAfgTrYtmDhYB1Kn3nDyyZ3UMySw81m5m5+nxTOW4Ucjs9yzX7D6wITjoc88DG3PpgJKm+drBVHQzWm6/3oTazeiHlHnsX7MI//ENL0G3t' \
			b'W+v6lmuu+KE2s3qt5fj58+30L9/c+gOKJOuDkbxU7WOr+hjslF7vQ21mZp3iNvpYd1vzL9Agu4MHdLXWByOx7a1k1K52uKu55oofajMzaxu31dWgLdxOd/PNHT2gBbk+GEmvrn6s7HF9c8UPtZnVSx9u6x7MsR1vryr3Ot/QrHpAl3ZVANBAXvABmDXhQDKt' \
			b'iyTr+iFo4V3vQ21m9SLJ5n6YN4db65NwXuGOn/xMwKYYSKnv1FWWbWoKm/snjFjsufRT15zygArGiVEcflQHJRzuNhF8qCl1FefXtR/fXPFDbWaTFsxtqr2cBPkHa7dvVj2gu742TP7E82DrAnlFLzxZx0e5gpEqR9cOva5DD80VP9RmzKPt0HDW9PIeqpXV' \
			b'C0mXUyuuucCHamXmmMf91YruV9SM3lI7vrn/BwD8VB/4UC2tXhJKzPeAFTVFYYuV1TdrHzhMtyHY3aVEVTZzQufxVRncdnDZD1XY9sNFl1Zhqrnwh45hzpz0ue7TYHDryKaH7hWR/5sjKmLcjzv7Wfg5Nq69hxrDlhNOj78x2OYKHmoAZ3mW6aEbANw49Pgf' \
			b'agCrdYKuogF0zRU81AA2Lfs8+gagmit4qAFsWmF69A1AN1fwUANwzWtt8cQ9Q4JPFtxEerAACaMlyJJ9htlf3j5CPaAPqFU4jw1npuFwEg02guAnfYc6Lf+T727PN9QthggtY/RfsY6rVfn1OdhSyD7wXN5csYXlLSu1Krj+BK/TwVsD5bZAup1P8818LruR' \
			b'D+65IUFZU6bSt3gZoTKUnT5LChquo8bpiIqthdPTcKeSxnOIeMEfuTgIbdGWhTO6Dgj6Ll+A04PLgLa0sB/y/zo0cLBhzIfveEebkPHvb/4/h5idnA=='

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
		('UFUNCPY',       r'Function(?!\w|\\_)'),
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

		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\ne(?!g)q?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)(?!{_LTRU})|{"|".join (AST.Cmp.UNI2PY)}'),
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

		if pos and rule [1] [pos - 1] == 'expr_commas' and rule [0] not in {'expr_abs', 'varass', 'expr_func', 'expr_subs', 'subsvars'}: # {'expr_abs', 'expr_ufunc', 'varass'}:
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

# 	# a = p.parse (r"\. x+y |_{x, y = 1, 2}")
# 	# a = p.parse (r"\. x+y |_{x = 1, y = 2}")
# 	# a = p.parse (r"\. x+y |_{x = 1}")
# 	# a = p.parse (r"\.x+y|_{\substack{x=1\\y=2}}")
# 	a = p.parse (r"\[?g(x)and(\sqrt[2]-1.0,'str'or-.1or.1,-.1!),\left.-{-.1:1e+100}\right|_{-.1.kZSI2A,\pi&&\partialx&&\partialx=lambdax:1/\fracTrueFalse},]")
# 	print (a)

# 	# a = sym.ast2spt (a)
# 	# print (a)
