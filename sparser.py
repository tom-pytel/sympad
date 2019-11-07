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
			b'eJztfWuP3Daa7p85wHQDakAiRVLyN8dxZo21naztzNmBEQSOx7MIThIHtpOzB4P97+e98aaSSpfq7qquIlpdoiiS4vV5SL4vyau3f3n95Nvn3778S/WX//Xht3/AzT8+f/rNG7h99/jV05fPwfDNq8dP5NbIXcH9q2cvv33h7403KAng628xjJf0+9XTv/74' \
			b'5PHrp6/F/OKxt/0qGv8Wjd+x8fXzx6//7Sv42r9jLIKBrJ98/+r53/EpGL7/5vuXT777uzehwzev8Pf7r7wnNj598d2bv79+il948ezl9xipl99jQv72GN0/e/nmr5iGZy/IM/3+xyt0/Zwy51t8K1/4inw8+fbFi8c+w9Di1bO//tsbH7dXPu6vsrjj09df' \
			b'PScLjNR/wM/jF9+h8eXXkkNo+ioa/xaNkkNPn79+ih9+9ewF3r9+9rdnX6PhCef+6zcUv++eUyIhyT69//n66RNy8PWzb77BHHv5jEr+CUXg8cuvMR/wxbev5IO++DDKHOoTSO0bf8fif/H4u9dvvkX/byjjn/7nEywXsvrfnPV4a7hMIJQn/w7Gz3/89PnP' \
			b'd58+/5mYPydmML5/9+nDlx8/fvrxHz/98vnLu09gBW/ekbMP//072P/856/e/PmP3z988g+/ffivH999+q/47icw/vruy4/vP/4ipk8f/2808dc+f/j8+X0w/R5MPph3P0Xjly/hY/989/6LN/9OobL1H7+9jxH95z9/j7EJkf7l52D8+bcvIb6//vHLjz//' \
			b'+nuSzDSgkMgYDqTXG798+BSs/3z3KQ0SDP7xjzR27/7xD298/8enX/6ff/jvzx9iyn769O79//kQHj+nMfnzQwjrj99+/vhb+Oi74P59TA5laoj5xxjkH0n+/hai9NPPv30MKfoYcx3iE3L9/cdff30XPP/+84f3H8IDVKIkQr9//vIxfCQUbYjax19i7CnQ' \
			b'7OFz4vPHX/5890uw+Mw+f6jeXt0YV1l3XbGhQ0Nr8cdVrbmWR3giUwc/toJXN/Y6s+An5/2Bh85boZFc3XAYprrSle6qG121DRiugy3ZRYubHg3K8Q/E7kb116mV6nasTGaFRjA1hn+srm4ajio8oRFM6LGrMI38YYcG9A6RoYi0/OOaa3mEuFEQ8AK+1lj8' \
			b'v/Y2ffrU1GJAOwyzxbQ3vaS91dfeVuyCxY0iDw3kbwOxhuhZCRUTyMH2/GMhpoojh6GAEcuSchzecBHKozcn9opvN/Q5Smqle/+6RQPctdhf88NNK5YcW4uJUrVPVBtsxW7HQkWLJre4UZT3Gj6s6cttzT+GcwZMNy0lUBv+MRhHji083WhKh8E0duGFCS9a' \
			b'zT+Ov9hiWigxjaqusEpgUXF80camT07uaIV+G0g2flxi5h93rHzR5vZm93Hg0+4+jrhQuZXbfcw83bQqiVqs9RKJgYUdWrjEAh6udCNRwBrrMuv4eKO5UKEua1VRkdeVg/yA4LGVcVmMvUZIgmuBKyjt3NWNpqaP+NRXrvY1GhsstR6oitwUscjbvgIkS1ok' \
			b'vAz20cawTR9tLNmYOto4tmm8zY2iDFc9/1BVlOrurWxqhUZMgeUfyL/r62hEk+K67ZOKqaYKabRUek6DwbrNQAElQvVWoA+i2FDmaGi2DJCafyw2Ac4oRJ2GmiAiWuMNFLkGq0LV+gbPqUdLtpLnWsJssYywknS79t4GLKiOKf6B+nQtz9BGyQ39Y3ayFzRg' \
			b'hmn+sfiGIw5PaMQcgNBcS5GWR8fADXnbNIF/KmWoPpnOAxFBOtdZKCPMJXzNtRVrus/63ucwWF7Z2PTosYsfbivL+Y0f1cFUi0m13mC8wXoDFTmU6pVSVAzhUVMDGFrFR/BNpoZ/LOaYVG424gfqiiMBgV81XcpAyCkULWX4x/ShScPTDUfMNPwTOwTwwFRi' \
			b'av5BHpfWYGoyYrn2/uW1PMKTf8FuIUHOcsb3vlyQ3A2HjgHYEABGzlIAtvYvyKlYeV+WE40YBumE3s/bumqgtBtoE/ApKN8W+QqqMFUNU0GzAwCDOgJl3SNaQIvuTNWBl9rBfwdeG/hX8A9oUoMbqM0QHfgoZDlQc1Mb+IeUtFTPwAD+4AKfkMmNQl/oCjo+' \
			b'8EVVQW0DYO5c1XVVBx+tq76penChEaoguhDJBmLZYAgYIai/PRQjWALVQLJbQnHshUF9Bj8aEQ6gC5MJKWo03iECkKheV31b9WCp0CGEAXFoNH4MfEE0enADb2oMuQGYAxpGwu1t1bvKdZXrqw4ypKk6VXW66sCdwn+oLg02eUvNHFDFQv8Fe5fQEBCMXQMM' \
			b'jOgNzdOZCgraQYwwnhBRQ704yBzKmwrzV2FHFYzX2HAh/lB0V1hmaAHlBre3V5gv8IhZg7eaXbXyFlN+TYxGt57evkVCo+cOb6W8T6i8r3ouuKbnUq6lxDouSCwBLN+OC5RKh+6deGsaqS5K7locGAmICg9sOqlGHdcbCd5/riFTQYYTrilvrwyVZJaPkoOc' \
			b'cyN5JnkV8mgnb/L8mMoGyQCoiFZxxbP1CcRFQA9rF9VmJ7UZi+D6CBFSjiOkzJG+L/ngwUGp0qhPvVEzgJcyOt0yuqJ4Ud+rK2V16mWltCcFKrSQbZRhIXskW3xupMkPyeVkHTE5sfaM1JijUi9mL3c08Q0PMQjHcLoEPl9B4ktLOG5L8KClW+4UhMGg6guK' \
			b'nXbZwfCPmKaBWDQQemMwH8AK0wgJbiDFpYSOXEJ9KaHTLqG+LiV04iXUlBI65RK66qUPQZlA04udnzBsy9zCqZde0/qxkMwuU4JxOlnXvlxlHlhmjaWr6OeOW55Pal0p6hMv6taLEbjEei7PvpWC7Kk7WQa0+wa0LDqTmLGNTKey9AwLOby9arQgIsvUrnov' \
			b'r5GWpkUuo6VlySisl9e1tDQvtzMcmvGjaSPOKQaliGh2u5fZdcc57rgDjhIzlI2WGZx1udkJBXRcUTvFNy3yRqmfLElBUQLXb+ym4XvjxUBcvS07t+zIsfilhi/UmAsQLUpidznZCznD4GFZ7OpMyRLUFaIsYQx0DHnOTuWMb9oXlEOOG6PjxuhcqTRXTgi0' \
			b'EZluyAQWngksecmv4SpGgs8fSFdMOsCoFVx0n067F0vKTYq1mlTRUzqxstGsRK9tKZsTKxtU71OiRAb3UghHkgiY0jJOrlAwp5UoSMK9FMeRi6OmRiKZV3Qz7mYqqyYeKF3dU24JHXE26mOXojrxompNKaNTL6OmLmV02mVEa0xomGKIno5MkiPrYXBJgUSx' \
			b'IXQuHZS7yXv8/FHWR/AUBn6YxwQ829TxU62k7EWyN71w6gdZmIWzIpqSUqrG7ZSQbrgMeNKXpUpORFIiKWUZgldD0YQlJd8PbRmUjah2yk1A5NGklkVy6qj341VJ/PpU1g5BfUgMoa/5JuWIBYPlU8plW7k0rQelljGzZOBqvQ6a9yl5tSSv2pJXi/PKlLxa' \
			b'mlet5Y4WdqpJHY3bZMmy6Szr25JFM+pg0m0XuaR011ltTyWKfKS/x+NOqnbG4FZEJSvTrLScQY47a7mOhesln0dVhElJ5/qE0tL4jVI6Ht11PNbreJwm2C0DUNxQgTwZdms154Pl16J4czH14C0q8NGkdF8Uvk97Mu0tKlkWWf8Rp5vrVDfvgiCCVBGjJjCC' \
			b'qb3UrOD9Xk4mRleNTFJa4XPrLpTHnCngeDQ5j5VJRNtfau2rLzXhtjS7ozU7J1PuTl1q7XOl9h1RuE/jEVyJoXgBhpJdTDUr9OMNh5DXtAk83jp6YhVNLSqa+tprCeq4oR/N7ZBTyHjNYqqyb8Ap1wZIqGZhueZdRrl8+W56X7h4gzhokcmzI/bZcYFjDieb' \
			b'F6F8mO2pelFdK1tNHbu4UShP02dFw/r4RYE5oJOtOnAyTzBTe9G+EpE+zYgWwDyJYmtL6zl6MaASi2YlFs1KLNorseh0+xTMH+21MvQe4Qiz13A3jqYdtzYj1ig71Sw7lZeaX/Jn+aXRHB1DylFFwLU7NjC27KexO2Cial1UitblG4k8lUgYNUsYNUsYNWuG' \
			b'SuPk7dpRmEiN03LzJk27H2iTDO4bCx0rK3ceQFlu7449WcYlx7jkuNU7/q5zcRjVlvHvsca/kLmtDFFbr0nJI6GWR0Itj4RaGey0NH4h9PZc4lkmaFYKupsgnW+nuaZr+LscMiS3Lb2Jo3fqIOh2d9MKU5bnnXzRWW6wPHi6uMlUIhMjWlVGYM34USTDmmFY' \
			b'Y1d8g2gaIUbDWGQYi+DWVKFJmKLYtjfvZYLMcubCJ60/zcPirCe4x+3hvPISZbctWbp/tRflHVZFS9TKS3rCHmeW89lJJaa7EZ6VrfggAx3XaccBeccdz6qwfhmOwHCsgRsS4V5ESSGRy1JI+wpJlyyagwbtZ/GM1E7Zo9J4UYnsgAWZ1HM97aUyt96fEveZ' \
			b'BiRasPClrvC0wErRWQ44uY7nOfRJ7jDHd9g7UQ1mnGRITxmhpScj3ZskxVikjcxOcL6nGTssvp4Kjkttp+S5V4S7mqI2EnV6XJJtRrK0D/0UlhV55IR3eHYU7lqIWxbiVn24Tx/uT4eb0+HOdLgTG27DhtuP4U6TuF0ibpWI+yRi1cPz2bBjhqsDcaNx3Moa' \
			b'ixz7NzjLgJtVYvx67MVBRkE8FS4wrPEIYahDuA8GdtQg3qrGvAR3uB6RTmgEM2Yu5i5WTcxirHeYz5jROETEOoVDyRbP1cRqiZ0+sMdZXZzhRY1WaBQKyxnVWVGzExUyUDqMGr0dbnGKpzx3dJwmniGNp+biYap4Zice0NpVeBQqnu2Kp6p2eFhojWeq1njk' \
			b'J56biicy44Gb2OPkY6jpQFE85RRP8VQYco0HeNLZrRAaHSqM4bX00V7O9mz5wFk+j5Rs6Nt4SKtCa43f0OiFQkGrmg4wxlMzaz6rtMfzrMHc0UGoho/rdfQZQ2ee0oGpdKo1xoaOma1u+DxVDE9xKnuKPdrg6x4P88ZDO/G0T0oNxgRPHYUqc4NHnzq0wCN0' \
			b'6dhuOrsUz8rF858xEPDb4Z2Opa3JVNNJn3Q6rcK4Yq7jkaSYT5ROzHP0B5YAJjdQuW56+gpGraUsRH9aTnE2lRxcDs7Arqd3dKYyneV6g+fP0umwNRUkZjEWFR7j6vA8bPgEHhvsMKmYZXi8K9i7jqOBHcEbBEI6bLWlvAJfVDYQaofZTpmCVQT/9Q8IL4gh' \
			b'BUEuA0EKfBT4uF34UAgfU7Bhx5DDxU5WCiHaJdMseefr1rEEcpy7fTLRsQJacAn1LLw8VFgxObRA1i+HF4d562aAxE1DicOXmO1uBFBchBQ3BirunmDFcTS1q+LfSmhxi8Dl4WOKG6IKRmkxslT/so+Qm9wjZKfOwM3+D6qlzcANT6D2HnRosJiOAzPo8ZOq' \
			b'g/lcnuSdASMlY96lqNTlwOQHt6ODZQGpnUGqoJUN0691jls066xlrMvj7TifPRyvtoMxrZ9FbhKsY32ToLCXKvEF/BuZRcEDhwkTwR3uOj+LjWYeH1GPEM/xynAS/KLs/SC8rAUzwR3uP7AWOyFPI37qBRhqBEfrESyFZ1wOETAVmycWjJmBVXDQM7TSTdAV' \
			b'zRDVPmIszvYbRlm600yKZailbzHasrNwBeglPzvY28Q+HZ3uTDMhehMQU2SwFPE+BGMKPPnfAecYYazQIQHoPElNz4gdMigB7uEXxv4DuEsyJLIC8j2RVxPAPvk453MTPuzxX5wgDYTvGGIEb5wnhmYBN4SyjwwhVgfyRJY7KHDfQBpUiswbaXZNcQe9td7V' \
			b'kENCZAKXMItYoBTTCplgq3+EFAet9RFkyP/QHkZ7yMUs684+UE4RQvFkkooxlxKKniCVJYRSyOQeyMQymdgZMsEMsdP9dGwFVjjECod4CrGRQmx2RQqxoxRiI4XY+IX1/CH0McYeadA7zBHeaDeMenxn+QOeMQgu1aTzJuEKydKGQw8jgowpsqTX4sFzhESg' \
			b'S9y4Jrie5we7gB98rif8wFaH8kNM1kZysJEcYliT3CDUMMoMkqCVvGAOneM4kBSOTgdrqaCMK06cChxTwdx0TbNnvqYhdSXmAZmyoXvNd88DLrsiD4xO4zRxHofDXs8AjhlgZDIni8cOA4Q32g0jHd9Z/kA2ZtjjPJsHauJUUDMcJaSeqNWJ0cO/fL1LnLno' \
			b'ah7+3QL498WZwL/k44HwH1O2Ef7jnFIS1iT8O4Z/Nwb/kqCV8G8L/Bf4Pyv47xn++zn47/fAP/unAu8F/nuB/z7Cf59dEf77UfjvI/z32+C/Z/jvR+A/jccO/Ic32g0jHd9Z/kAG/xNuKSIZ/PcR/odd/9QTtTrvRuBfvt4lzlx0NQ///QL498WZwD9bHQr/' \
			b'MWUb4b+P8B/DmoT/nuG/H4N/SdBK+HcF/gv8nxP8YzvUJCLbD//UXifgHxNSM/xzAOy8qfku8M+uwhXgX41qhqCtwD+HvRr+6RuObkP4z+IxhP/4RrthpOM7y7cU/qfcUkRS+CcLhn/Orwj/maeGape4Yfj3X+8SZy66moV/drUf/kNxRvgXqwPhP0nZNvhH' \
			b'XwL/SVhT8K9YrszfG8C/T9BK+O/WSZzPhgRs4YFz5wHFPKDmeECRGyu3MTbgV8QGog9I95rvng1UdkU2UKNsoCIbqG1soJgN1AgbpPHYYYPwRrthpDOPlr+REcIe5zkhqEgIakAIqSciBJ+tQgjy9S5x5qKreUJQCwjBl2hCCGx1KCHElG0kBBUJIYY1SQiK' \
			b'CUGNEYIkaCUh9IUQCiGcJyG0TAjtHCG05IaXWI0TArsgQmiFEFohhDYSQn5FQmhHCaGNhNBuIwRW8yQcGBJCGo8dQghvtBtGOvNo+RsZIexxnhNCGwmhHRBC6okIQYyeEOTrXeLMRVfzhNAuIARfogkhsNWhhBBTtpEQ2kgIMaxJQmiZENoxQpAErSSEpi6M' \
			b'UBjhPBmBFVDVnAIqRswwI5gJRmAXxAiiesowyXfPCCa7IiOMap6qqHnKYa9nBMOMYEYYIY3HDiOEN9oNI515tPyNjBH2OM8ZwURGMANGSD0RI4jRM4J8vUucuehqnhEWKJSGEk0Yga0OZYSYso2MELVJk7AmGcEwI5gxRpAErWWE5oSWKTzUBQqFG06cG1iJ' \
			b'SM0pEWGEWI9IJYsTFC9OSBmCn4ghRKFIiUKRigpF7CpckSFGFYpUVChS2xSKFCsUqRGFoiweOwwR3mg3jHTm0dbelJHEHh85SUS1IjVQK8o8EUmI0ZOERKBLnLnoap4kFqgVhUJNSEJy80CSiCnbSBJRrSgJa5IkWK1IjakV+QStJQlaOkvqrYz4CPeKgH4A' \
			b'8S0CekTeKdjtIyAi6BHQCYAFgGJQYmAgQICGjB89wvUDb5BXiLIQ5XkTpeZpNT03rYY1l6fVdDKthmaIKt2YKMVdw2BBRKllck3HybXBFYhSj06u6Ti5prdNrmmeXNMjk2tZPIZEGd9oN4x05tHW3pQS5T4fGVHqOL+mB/NrmSdsh94oROkj0CXOXHQ1S5R6' \
			b'wfxaKNRIlGJ1IFEmKdtGlDrOryVhTRGl5vk1PTa/5hO0lij3rssrJFFI4hxIomOSmNuKB2trxyTRJSTRMUl0kSTYHZFEJyTRCUl0kSS67Iok0Y2SRBdJottGEh2TRDdCEmk8dkgivJEGm1xYp+J7W3tTxhLd5DVgiS6yRDdgidQTsYQYPUtIBLJ0RFfzLNEt' \
			b'YAlfqglLsNWhLBFTtpElusgSMaxJluiYJboxlpAErWWJuVV6hSUKSzx4luiZJfo5lmA3yBJ9whI9s0QfWYLdEUv0whK9sEQfWaLPrsgS/ShL9JEl+m0s0TNL9CMskcZjhyXCG+2Gkc482tqbMpLY4yMniT6SRD8gidQTkYR3IyQhEegSZy66mieJfgFJ+EJN' \
			b'SIKtDiWJmLKNJNFHkohhTZJEzyTRj5GEJGgtScyt5SskUUjioZNEy+s72rn1HVhPeYkH3YQk0AxRpRuThLjDwm9lrUcraz3auNaDXYUrkMT4LqBtXOvRblvr0fJaj3ZkrUcWjyFJxDfaDSOdebTBlJLEPh8ZSbRxxUc7WPGRecJ26I1CEj4CXeLMRVezJNEu' \
			b'WPERCjWShFgdSBJJyraRRBtXfCRhTZFEyys+2rEVHz5Ba0libsVfIYlCEg+eJBomiWaOJBpygyTRJCTRMEk0kSTYHZFEIyTRCEk0kSSa7Iok0YySRBNJotlGEg2TRDNCEmk8dkgivNFuGOnMo629KSOJPT5ykmgiSTQDkkg9EUmI0ZOERKBLnLnoap4kmgUk' \
			b'4Qs1IQm2OpQkkuRsI4kmkkSS6CmSaJgkmjGSkAStJYmV6wILSRSSeHgkwZLrdk5yjXWTJddtIrluWXLdRsm1uCOSEMl1K5LrNkqu2/yKJDEquW6j5LrdJrluWXLdjkius3jskER4o90w0plHW3tTRhJ7fOQkESXX7UBynXkikhCjJwmJQJc4c9HVPEkskFyH' \
			b'Qk1Igq0OJYmYso0kESXXSViTJMGS63ZMcu0TtJYk9q4VNJfBE26UKmyhi7OjC80awXpOIxgyA6suKwXrRClYs1KwjkrB4o4EFKIUrEUpWEelYHYVriigGFUK1lEpWG9TCtasFKxHlIKxBsaI7EgowptBlAdXz6vLxa1njV7kFNP+BnKKqBusB7rBmSeSU4jR' \
			b'yymkfLrEmYuu5uUUC3SDQ9kmcgrJ1APlFDFlG+UUUTc4CWtSTsG6wXpMN9gnaCVxqL1LCgtxFOI4K+JoWazdzom1ISNadoZDjUSy3bJku42SbXFHQw2RbLci2W6jZJtdhSsONUYl222UbLfbJNstS7bbEcl2Fo+doUZ4o90w0umFSGhr7zbwhuYBx7S/wYAj' \
			b'yrfbgXw780QDDu9GBhxSPF3izEVX8wOOBfLtULTJgIOtDh1wxJRtHHBE+XYS1uSAg+Xb7Zh82ydoLW882IWHE4f/lrmpS+IMPcEbbt+gg6Xdek7ajXWapd06kXZrlnbrKO0WdzTiEGm3Fmm3jtJudhWuOOIYlXbrKO3W26TdmqXdmqXdBGtYC+hLXjUqjc/O' \
			b'wCO80W4Y+cyjDaZMNWqPj3zIEaXeeiD1zjzRkEOMfsghEegSZy66mh9yLJB6h8JNhhxsdeiQI6Zs45AjSr2TsKbXrHP+Wkm20IfCYg9DD0nYWgqZO9HzZCmkCDYumjzWDDjweEsoGLztJQ1DF5IG3YQ00AxRpRuThrjDwqe7kuea70IaRmdXIA1yukMaaCuk' \
			b'YbYdp0ff4HgORxtZPIZkEd9oN4x05tHW3pSSxT4fGVmQBZMF51oki8wTtkNvFLLwEegSZy66miULdrWfLEKhRrIQqwPJIknZNrKg01mZLJKwpsiCMkqSPBxn+AStJYmybruQxNmTBEu/zZz0G09sZOm3SaTfhqXfJkq/xR2RhEi/jUi/TZR+m/yKJDEq/TZR' \
			b'+m22Sb/l7GszIv3O4rFDEuGNdsNIZx5t7U0ZSezxkZNElH6bgfQ780QkIUZPEhKBLnHmoqt5klgg/Q6FmpAEWx1KEjFlG0kiSr+TsCZJgqXfZkz67RO0liTKuu1CEmdPEiy6MHOiC8NukCQSuYVhuYWJcgtxRyQhcgsjcgsT5RbsKlyRJEblFibKLcw2uYVh' \
			b'uYUZkVtk8dghifBGu2GkM4+29qaMJPb4yEkiSizMQGKReSKS8G6EJCQCXeLMRVfzJLFAYhEKNSEJtjqUJGLKNpJElFgkYU2SBEsszJjEwidoLUmUZduFJE6EJLCG3hlRKCYKNUcUit3gdokJUSgmChWJQtzRdolCFEqIQkWiYFfhitsljhKFikShthGFYqJQ' \
			b'I0SRxWNnu8TwRrthpDOPtvambLvEPT7y7RIjUagBUWSeaLtE74aJwkegS5y56Gp+u8QFRBEKNRKFWB26XWJM2cbtEnuSz4UtE2N4kzIKJgs1RhY+UWvJoizfLmRxImRxZ0RhWaBt5wTaWONYoG0TgbZlgbaNAm1xh4VvRaBtRaBto0CbXYUrEIUdFWjbKNC2' \
			b'2wTalgXatt4liiweQ6KIb7QbRjrzGE0pUezzkRGFjYJsOxBkZ56wHXqjEIWPQJc4c9HVLFHYBYLsUKiRKMTqQKJIUraNKGwUZCdhTZGEZSG2TYTYgSR8gtaSRFm+XUji7EmCl2/bueXbWN14+bZNlm9bXr5t4/JtcUckIcu3rSzftnH5NrsKVySJ0eXbNi7f' \
			b'ttuWb1tevm1Hlm9n8dghifBGu2GkM4/SIAfLt/f5yEkiLt+2g+XbmSciCTF6kpAIdIkzF13Nk8SC5duhUBOSYKtDSSJJzjaSiMu3k7AmSYKXb9ux5ds+QWtJYm75djnVe4YRlrBBYYLDmQDscC4IJyjmhRGKhRFqThihqsmTvbFyKmYCuit2TgIIFQUQKrui' \
			b'AEINmAArFFp6+YPaRAQ3Xkqtxlbc9dn/rhAixFK7YcTjO8uRz8QP09dgVqnh0YJgX2QBjA97aPyCiSZdLiHvkQZ89PHRNcG4QACh5pkgFGoigGCrUSbgdCyZVqLvSrFulEAoogKpJyGnJkUQikUQWP3RCbwcYQWfuJwV2u4RdUyEFiA3HvGB7PUj4j5ooI/4' \
			b'GMHIEytPey2DiTKYODkKmR1MsDasndOGtXTdcJWLgwnWhrVRG1bc0WBCtGGtaMPaqA1rdXbFwcSoNqyN2rB2mzasZW1YO6INm8VjZzAR3mg3jHTm0dbelA0m9vjIBxNRG9YOtGEzTzSYEKMfTEgEusSZi67mBxMLtGFDoSaDCbY6dDARU7ZxMBHFEklYk4MJ' \
			b'1oa1Y9qwPkErBxN65QGwd0oS7fnxhKKFToUv7oEvIJ/GOUMPeQP+FXIHK8naOSVZrHmsJGsTJVnLSrI2KsmKO+IOUZK1oiRro5Ksza/IHaNKsjYqyYbg19MHj0DsiJ5sFpUd+ghvtBvGO/Noa2/K6GOPj5w+op6sFT1ZceZJJPVKJCJGTyISjS5x5qKreRJZ' \
			b'oC0bsj8hEbY6lERiyjaSSNSWTcKaJBHWlg2fHPJICIGpBIwr2GRuDfdpTk0deTrKc4PwAnGC5wLhgYD/Dwn7T2qc0DHWd3NY301PL1m6GN87wfdO8L2L+N5lV8T3bhTfu4jv3TZw7xjcu11w3wX0ECvthhGN7ywHmkH5hFv6eAblXYDyAN6SbXUqQugYrTvG' \
			b'6W4RSHcLQNoXUQLSbHUoSMfcWY/PXcRnDmOv8hF9RJK7g86SmAW9fMLjuQXRBY8LHh8Fjx1rCrk5TSFXT+Mxbrwi2kFOtIOcaAe5qB3ErsIV8NiNage5qB3ktmkHOdYOciPaQTt4HGOl3TCi8Z3lW4rHU27dUBfI1Tt47LMtxWPHSj+O1X3cIl0ft0DXJxRR' \
			b'xGOxOhCPk9xZjccuqvlIGHvx2LGejxvT8/GJWYrHc2uPCx4XPD4OHrP41c2JX90e8StugSXiVyfiVyfiVxfFr+wqXBGPh+JXxuMof3Xb5K/0DUe3eTwOsdJuGNH4znKgGR5PXwM8Vrt4LNmV4TELVh0LVN0iYapbIEwNRZTgMVsdiscxd9bjsYp4zGHsx2MW' \
			b'o7ox4alPzFI8nlvme5p4XFRpjo7dpyYHxaaF+G3m8NvswW9Drwm/jeC3Efw2Eb9NdkX8NqP4bSJ+m234bRi/zS5+Z/HYwfLwRrthpOM7yx/IsHzCLUUkw3ITsTwVeWY+sKlxbgqyy3e7NOpNcD2P8mYByvuCTFCerQ5F+ZisbVPVaO2hPoY1ifSGkd6MIb0k' \
			b'aK28c27NbkH8gvgPA/EtI76dQ3y7B/EtvSbEt4L4VhDfRsS32RUR344ivo2Ib7chvmXEtyOIn8ZjB/HDG+2GkY7vLH8gQ/wJtxSRDPHtBOKnPgjxbYL48t0ujXoTXM8jvl2A+D6zE8Rnq0MRPyZrI+LbiPgxrEnEt4z4dgzxJUFrEX9u4W1B/IL4DwPxHSO+' \
			b'm0N8twfxHb0mxHeC+E4Q30XEd9kVEd+NIr6LiO+2Ib5jxHcjiJ/GYwfxwxvthpGO7yx/IEP8Pc5zxHcTiJ/6IMR3CeLLd7s06k1wPY/4bgHi+4JMEF9y8EDEj8naiPguIn4MaxLxHSO+G0N8SdBaxJ9bRVsQvyD+w0B81lpxc1orbo/WiqOLEV+0Vpxorbio' \
			b'teK67IqIP6q14qLWitumteJYa8WNaK1k8dhB/PBGu2Gk4zvLH8gQf8KtG2qwuG4C8VMfhPhdgvjy3SzqTXA9j/gLdFtCQSaIz1aHIn5M1kbEjwouSViTiM/6LW5Mv8UnaC3i05LYtjIz546dNfDrWzxl7C4JoFtBAvphEYE2d7kLGzYhXErUECnc6DlWgBxR' \
			b'e4iBwhN9dSXMoIQZVGQG1WVX3IZtlBlUZAa1jRn8elk1Qg1ZRHb2YcNPY5x5AmgQ7+jPctyxPVDYeMoYfWPSixpyhJrgiMwH7cOWcIT/fJaGJrhOOaKtpzZiG+EJ3PtvZzM2CTTdjI2tDt2MraNFs2o7WWA8TJT4SrT2b8fGjKHGGMMnKzIG2eAv0Ab8di39' \
			b'GrIH6lC8SFZ1RBx99XYfbewSRk88oYUhhBISPhAyWMgEU1o2BPqIYGmXPkPrgXJMphTjBH2XoO5MtztD2UPQtVmPqAFJ9yGoG0FOj5jYvBej5SROEkASOhI0elwMQDiCgh4CD8G/eW0Vj3Q3w53CcrAa6pvkmiY3ooO9EIBme6kZ5hyKNgg1GyDGY8t+VEFI' \
			b'2cUTjyQADpAJe8FhtEN5P/jg+4VQqy4dJZDtxpBiMUqs61RRl+nhQUXSMcLSLJAx7JW03RRsrIKMZm1/wt07ZOTDR8YOdcf4AW4cLibH2tedNp4c3OtYiSeTWOLHZqeOJxTR9F+wBUfv94EvxACQKIWDVf1A8GYca5RZ00Wp/gUV8xEkAkcyEOn1I5l6Bnni' \
			b'5NZtgY8HnDYCDqT34XdazAFAY/Z0XHCnDTsAHHjGSQQCnpr2kmIAQjYBdzioDvsc4FQADpL1LQITgRK1j3XA1B4DnAIYJZ0dLMaz6vAogt3tIITeJzs9inY4lvNTAhop0r+ns7WaMFkpMzIYCMIizgf7bQRuGjrEEb8IrZj6SvqwuRcottEZ+TtCLEErjBnE' \
			b'aC9i4XT5g0AtRKxu5XBLLxtume4eukgT3aM2RSJqR6fQTRoOubgY+zkkovg/KDRCJMK6sXYIZuqFQzA1Owxrb3ta9+56QufUC1o7ddPe79TNrU7bHLM3k/Rk2vPqyWyZusGU3sLUjTlNUdBkRwTjB884DY279DVHApAdWfx9gwiYoekpPKCsrRcOq4ZDKg8s' \
			b'w+HTrQ+bTn0uZ6eTQu2aNCxueHfjdqgie8+IM1jmcKz5Gxw9Yej0QbtwKLU7jErk2DSeygZMPEyy1dtTwKQpLaXbF1UfuxdjjzFpHMGlcw8WW3h/DisKYPpeRdYn0oFB3jmSyLr6V/8ImIlmg91pgMYsUGC0bqX3cmzQWNtrGfZWNg1/zrVHMt0b6UnR85Z6' \
			b'IScCGRvgQjLB3srAp9uOFXgyxb3ChbnFAc/GlSg7isf3DR3qtOGjSQ/VOUEMoaghStzieGYCSZacb5PDCdbao6nAUHYMBzQHAEt/ALD09wwsCag0/ZH7IscAlQIom7VtczDBojuNrskRseRWcQSSsX0wUx8PR9RwhVXBkYIjK3DEFhy5XRxpDsCR5og40hQc' \
			b'KTiyHUdOZarkbHBEPZDJ1UuaUD1FoDhhjLhNQFCUhIcydXooAFT/gvbwCEEQBS0Qj4IFDwELtkpjHyAeUAu6RTjgFnmmkpTbEbw6/YhQGJrSI0RPgoa2QEOBhuNBAzeM0+oqXCQ4WPMIYJogwRRIKJBwO5Ag7f/Bjx7uABJofzP5P01IMM0j2iKrxjvWZxxR' \
			b'YJ3GfoQhqDgRtc8CFWcAFYwSBSpGoIK2QeT/BwsVD0XZs0DFCFSAGfJV4e6BpwEb1MhPbXqSwzgB1KCI3PGQg74xCxqKTiQF673w0XaPiAcgZY8QeqHSPyLkg9oJFrR3iDlAA7QAyLEB5ERAw50iaLhTAQ13D6DhDuxpLIKKA3Q6C1RcMlRQxTtH8edtQAVl' \
			b'zgOa0sSt90lPukfMaAga7CFqmgUaLg4aqEadt2bECmig3DgHaUeL8xItVnnsPWg6n8MeonlZoOFioIHcX4jW1AJsoOw4K1Gohn6DxjaAd03QUJQpCzRMQwO5vTB9yotUktDYbagZEopO5cVDAjbS09GoPAlEoFheDB4oFHfiWXakWlmToNMWjcpLBAasxieg' \
			b'T3mywHBpXYWmxTlH7ioUhcpLRASsuQURCiKMIcJD0ZuEZIY9fO8bHUbP0L3vFd6yb29ZuLkGK7D4brAdHA81MD9PAzsQPqYQZM2CbnsiCpSHbbHbVTtnd598z2LDOdsBL9qZHkZ7GdjBh7Hn/5sVptDv8FDrh9QB2XgmtccQSv/enoii6rC/N+JQfYo7Iyei' \
			b'WFmApQDLBmDZ/d8OLOrCgUXNAoteAywnooZZgOU2geUiQEXv/G8HFX3hoKIPnDeJgAKfeItAwijCEML4weBhCDYMAgaiBUNFihMEEr7F+1YeWqaSFukmWmKftLput3XQahcFrYC2EQs13lf2UM9DHUcDV23NFZrqcqjHY3U41t9Q80JlC1UDs5KqRDNRE7AS' \
			b'+DKnst4pFj7eQ+G4EyrmLWQ6Q24AWxezHwEzK4J2ZTHYcaAKxXHDjeduywOTQcgQykWlZUNapGn5hGa7uIzo62PNJy0rdStlVe8rrjMqsgTQx4vN3GPRoT4J5FHTUvqJjmnex6E8GXouDuxJZbWtydqk1tg5acjaVm+V6cFSWffDNdyvbqABIznT+xuoIVC8' \
			b'eGQYFJKlw5tuNNrh8l3g9o4O3HZ0Xi10lnQFSYIcBmroWzo0VrUGPMMjdpggjFrzSdn+zFkMAaoHPDmsJlD8eFgZVkZj6Wvt+q/B2+k/CtRgoG4yWDmgrpsIn3qCZvAXD5trUnv6nB35XItfhFqHu8LXtBfrztehmgwjQKc5hKlu3MQUO2BaIgad2fCHnQAr' \
			b'm7/H/8yFU5n7jvzgBDaaaatS6PJwKbh7SgF42f5HMe22xNRNRXZw+NNo5HWdJADCmPnDvn5uwz3vVnrY2RuIA9wpYf1IwtRk2gAgcWzTZeOZkQTXWZr7nrQTsduNvSrsZtEWYIoXHtIGJLSzADy3NmYRbshA83SGs8tgtvWSbWo663CQSEMQlWYjQ74xdEy3' \
			b'nMP9A1PV8HK7Vtm7qf/5kPb5ng5xYDMw7o/j9Kep/OHVUWs2Hcx5bxcnuVlb52H4gJh1hzW/PVbtV9W6y3fB1vqbu7BPduuB0sVlrk4N5+qJ0lZ3XeK6OvqlRqyUupWwubT1kUGtre7x4iS3Icm4G35/l9XcPpCajp7x6nmG9Q6v+k5D339x8Y+NPZbX+PoW' \
			b'Kj1O8G69cHZ6vTdOuR1WfJxAvofqXz+AJoATL8nFkW6qgfWtXzghc9ffmLi4TowNLKfrwSJi39YmbDW4cAJ913bhhYKbZU45G7rSNCabBk5FXtDFFWLdaP/u2gWKWI9w8eRjXVrFdKsw1SVdXCHWzQcsHgZuaxm2ut0LhfvLnHJmqNI6JlsHCq4u6OIKMTaW' \
			b'voXWQTo4W1oIquTc9oWaL8uccp7sDLZLI4mNxFSXdHGFGBt+31IjwYLe1lBsdRcXaoMtc8pZU8bne9qKqy7p4gqxbnBuN068L20yeTlhmXTV8gs13VZ5QB3KGRfIvfLAGVaG8dMtCFWILujiCrFuGL+1BaVlvbk1obr0XV6pPvJiX6xwdNA8wEZ58MaWhV0A' \
			b'fX8tDMLgVqZ9S4M8QZ041NbbeqGQ+xD/s5fCwx6gNG87VJvc2MT1pymwPA3LtrqkiyvEeh2DW1Qq2IbQY0XnquUX6rWu8jC4/NKRFT5o4UcfFnxQzuvSFKebYldd0sUVoj2Lpohryh7AxVm+bgrkZLPcVA/h4iwf0wC/tyzXdkW210uy3lb3fCGIbnbBRbBu' \
			b'MiOwzfFKYYQ2dkvCVasuXKey1s+2a8+XuDzGFPUffnn01UO7uDQ2ri447dLARd0P7OI1T2Oq/he11gPX4q+/eKl9/N8WyjDE3bCTx8zN0rDo4pJevcLh7Eq6rc7x4tI9ubUM9166fXWOF5fuOn2LMyxdXPp9hheX7vqJiXMr3aY6x4tLd/0cyLmVrqrO8eLS' \
			b'tdVb3dKSYYFq5y0aad0dWmAWkiUutOBhKeT927T8G16g1EB249mACoqA9qHiD0GPbtQ1LqfP/tl1s+MaC498QNEP/pXmuBuVbN2gqSqwPdBPWh25CqVVx1cb2omWFruhbdyFinZ9Cjs+6WSnJ9x+gfMDnGdfwY08aItbyk38pP8U1UyZuDM87QWv3mLthpqJ' \
			b'Syxq2jiK31j0rVmAicJLElqqBmsphI57QPA+pripxltlWlqiIX67uGmFZCwUGoSCNo5t8OBGb4MbW1z/f7O4DUw='

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

# 	a = p.parse (r"\log_y1-4.390610224900228;notb(\lim_{x\to\partialx}3062306634092707.0,partialx&&\emptyset&&Naturals0,d^{4}/dx^{2}dy^{1}dz^{1}2)=\left|\partial\right|andc**y1and\tilde\infty[xyzd]''")
# 	print (a)

# 	# a = sym.ast2spt (a)
# 	# print (a)
