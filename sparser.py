# Builds expression tree from text, nodes are nested AST tuples.

import ast as py_ast
from collections import OrderedDict
import os
import re
import sys

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

class AST_MulExp (AST): # for isolating explicit multiplications from implicit mul grammar rewriting rules, appears only in this module
	op, is_mulexp = 'mulexp', True

	def _init (self, mul):
		self.mul = mul

	@staticmethod
	def to_mul (ast): # convert explicit multiplication ASTs to normal multiplication ASTs
		if not isinstance (ast, AST):
			return ast

		if ast.is_mulexp:
			return AST ('*', tuple (AST_MulExp.to_mul (a) for a in ast.mul))

		return AST (*tuple (AST_MulExp.to_mul (a) for a in ast))

AST.register_AST (AST_MulExp)

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
		ast2, wrap2 = ast.diffp, lambda a, count = ast.count: AST ('diffp', a, count)
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
		return AST ('slice', pre, post, None)
	elif post.step is None:
		return AST ('slice', pre, post.start, post.stop)

	raise SyntaxError ('invalid slice')

#...............................................................................................
def _expr_comma (lhs, rhs):
	if not rhs.is_slice or rhs.step is not None or not rhs.stop or not rhs.start or not rhs.start.is_var:
		return AST.flatcat (',', lhs, rhs)

	if lhs.is_mul:
		if lhs.mul.len == 2 and lhs.mul [0].is_var_lambda and lhs.mul [1].is_var:
			return AST ('lamb', rhs.stop, (lhs.mul [1].var, rhs.start.var))

	elif lhs.is_ass:
		if lhs.rhs.is_mul and lhs.rhs.mul.len == 2 and lhs.rhs.mul [0].is_var_lambda and lhs.rhs.mul [1].is_var:
			return AST ('=', lhs.lhs, ('lamb', rhs.stop, (lhs.rhs.mul [1].var, rhs.start.var)))

	elif lhs.is_comma:
		for i in range (lhs.comma.len - 1, -1, -1):
			if lhs.comma [i].is_mul:
				if lhs.comma [i].mul.len == 2 and lhs.comma [i].mul [0].is_var_lambda and lhs.comma [i].mul [1].is_var:
					ast = AST ('lamb', rhs.stop, (lhs.comma [i].mul [1].var, *(c.var for c in lhs.comma [i + 1:]), rhs.start.var))

					return AST (',', lhs.comma [:i] + (ast,)) if i else ast

			elif lhs.comma [i].is_ass:
				if lhs.comma [i].rhs.is_mul and lhs.comma [i].rhs.mul.len == 2 and lhs.comma [i].rhs.mul [0].is_var_lambda and lhs.comma [i].rhs.mul [1].is_var:
					ast = AST ('=', lhs.comma [i].lhs, ('lamb', rhs.stop, (lhs.comma [i].rhs.mul [1].var, *(c.var for c in lhs.comma [i + 1:]), rhs.start.var)))

					return AST (',', lhs.comma [:i] + (ast,)) if i else ast

			if not lhs.comma [i].is_var:
				break

	return AST.flatcat (',', lhs, rhs)

def _expr_colon (lhs, rhs):
	if lhs.is_ass:
		l, wrap_ass = lhs.rhs, lambda rhs, lhs = lhs.lhs: AST ('=', lhs, rhs)
	else:
		l, wrap_ass = lhs, lambda rhs: rhs

	if l.is_var:
		if l.is_var_lambda:
			return wrap_ass (AST ('lamb', rhs, ()))

	elif l.is_mul:
		if l.mul.len == 2 and l.mul [0].is_var_lambda and l.mul [1].is_var:
			return wrap_ass (AST ('lamb', rhs, (l.mul [1].var,)))

	return _ast_pre_slice (lhs, rhs)

def _expr_mapsto (args, lamb):
	if args.is_var:
		return AST ('lamb', lamb, (args.var,))

	elif args.is_comma:
		for var in args.comma:
			if not var.is_var:
				break
		else:
			return AST ('lamb', lamb, tuple (c.var for c in args.comma))

	raise SyntaxError ('invalid lambda function')

def _expr_piece (expr, expr_if, expr_else):
	if expr_else.is_piece:
		return AST ('piece', ((expr, expr_if),) + expr_else.piece)
	else:
		return AST ('piece', ((expr, expr_if), (expr_else, True)))

def _expr_cmp (lhs, CMP, rhs):
	cmp = AST.Cmp.ANY2PY.get (CMP.text.replace (' ', ''), CMP.text.replace (' ', ''))

	if lhs.is_cmp:
		return AST ('<>', lhs.lhs, lhs.cmp + ((cmp, rhs),))
	else:
		return AST ('<>', lhs, ((cmp, rhs),))

def _expr_neg (expr): # conditionally push negation into certain operations to make up for grammar higherarchy missing negative numbers
	if expr.op in {'!', 'diffp', 'idx'}:
		if expr [1].is_num_pos:
			return AST (expr.op, expr [1].neg (), *expr [2:])

	elif expr.is_mul:
		# return AST ('*', (expr.mul [0].neg (stack = True),) + expr.mul [1:])
		return AST ('*', (_expr_neg (expr.mul [0]),) + expr.mul [1:])

	return expr.neg (stack = True)

def _expr_mul_imp (lhs, rhs, user_funcs = {}): # rewrite certain cases of adjacent terms not handled by grammar
	ast         = None
	arg, wrap   = _ast_func_reorder (rhs)
	last, wrapl = lhs, lambda ast: ast

	while 1:
		if last.is_mul:
			last, wrapl = last.mul [-1], lambda ast, last = last: AST ('*', last.mul [:-1] + (ast,))
		elif last.is_pow:
			last, wrapl = last.exp, lambda ast, last = last, wrapl = wrapl: wrapl (AST ('^', last.base, ast))
		elif last.is_minus:
			last, neg = last._strip_minus (retneg = True)
			wrapl     = lambda ast, last = last, wrapl = wrapl, neg = neg: wrapl (neg (ast))
		else:
			break

	if last.is_attr: # {x.y} *imp* () -> x.y(), x.{y.z} -> {x.y}.z
		if last.is_attr_var:
			if arg.is_paren:
				ast = wrap (AST ('.', last.obj, last.attr, _ast_func_tuple_args (arg)))
			elif rhs.is_attr:
				ast = AST ('.', _expr_mul_imp (last, rhs.obj), rhs.attr)

	elif last.is_pow: # {x^y.z} *imp* () -> x^{y.z()}
		if last.exp.is_attr_var:
			if arg.is_paren:
				ast = AST ('^', last.base, wrap (AST ('.', last.exp.obj, last.exp.attr, _ast_func_tuple_args (arg))))
			elif rhs.is_attr:
				ast = AST ('^', last.base, ('.', _expr_mul_imp (last.exp, rhs.obj), rhs.attr))

	elif last.is_var: # user_func *imp* () -> user_func (), var (tuple) -> func ()
		if last.var in user_funcs or arg.strip_paren.is_comma:
			if arg.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg)))
			else:
				ast = wrap (AST ('func', last.var, (arg,)))

	if arg.is_brack: # x * [y] -> x [y]
		if not arg.brack:
			raise SyntaxError ('missing index')

		ast = wrap (AST ('idx', last, arg.brack))

	if ast:
		return wrapl (ast)

	return AST.flatcat ('*', lhs, rhs)

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast.numer.is_diff_or_part_solo:
			p = 1
			v = ast.numer

		elif ast.numer.is_pow and ast.numer.base.is_diff_or_part_solo and ast.numer.exp.no_curlys.is_num_pos_int:
			p = ast.numer.exp.no_curlys.as_int
			v = ast.numer.base

		else:
			return None

		ast_dv_check = (lambda n: n.is_differential) if v.is_diff_solo else (lambda n: n.is_partial)

		ns = ast.denom.mul if ast.denom.is_mul else (ast.denom,)
		ds = []
		cp = p

		for i in range (len (ns)):
			n = ns [i]

			if ast_dv_check (n):
				dec = 1
			elif n.is_pow and ast_dv_check (n.base) and n.exp.no_curlys.is_num_pos_int:
				dec = n.exp.no_curlys.as_int
			else:
				return None

			cp -= dec

			if cp < 0:
				return None # raise SyntaxError?

			ds.append (n)

			if not cp:
				if i == len (ns) - 1:
					return AST ('diff', None, tuple (ds))
				elif i == len (ns) - 2:
					return AST ('diff', ns [-1], tuple (ds))
				else:
					return AST ('diff', AST ('*', ns [i + 1:]), tuple (ds))

		return None # raise SyntaxError?

	# start here
	if ast.is_div: # this part handles d/dx
		diff = _interpret_divide (ast)

		if diff and diff [1]:
			return diff

	elif ast.is_mul: # this part needed to handle \frac{d}{dx}
		tail = []
		end  = ast.mul.len

		for i in range (end - 1, -1, -1):
			if ast.mul [i].is_div:
				diff = _interpret_divide (ast.mul [i])

				if diff:
					if diff.expr:
						if i < end - 1:
							tail [0 : 0] = ast.mul [i + 1 : end]

						tail.insert (0, diff)

					elif i < end - 1:
						tail.insert (0, AST ('diff', ast.mul [i + 1] if i == end - 2 else AST ('*', ast.mul [i + 1 : end]), diff.dvs))

					else:
						continue

					end = i

		if tail:
			tail = tail [0] if len (tail) == 1 else AST ('*', tuple (tail))

			return tail if end == 0 else AST.flatcat ('*', ast.mul [0], tail) if end == 1 else AST.flatcat ('*', AST ('*', ast.mul [:end]), tail)

	return ast

def _ast_strip_tail_differential (ast):
	if ast.is_differential or ast.is_null_var: # null_var is for autocomplete
		return None, ast

	if ast.is_intg:
		if ast.intg is not None:
			ast2, neg = ast.intg._strip_minus (retneg = True)
			ast2, dv  = _ast_strip_tail_differential (ast2)

			if dv:
				if ast2:
					return (AST ('intg', neg (ast2), dv, *ast [3:]), ast.dv)
				elif neg.has_neg:
					return (AST ('intg', neg (AST.One), dv, *ast [3:]), ast.dv)
				else:
					return (AST ('intg', None, dv, *ast [3:]), ast.dv)

	elif ast.is_diff:
		ast2, neg = ast.diff._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			if ast2:
				return (AST ('diff', neg (ast2), ast.dvs), dv)
			elif ast.dvs.len == 1:
				return (neg (AST ('/', ('@', ast.diff_type or 'd'), ast.dvs [0])), dv)
			else:
				return (neg (AST ('/', ('@', ast.diff_type or 'd'), ('*', ast.dvs))), dv)

	elif ast.is_div:
		ast2, neg = ast.denom._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('/', ast.numer, neg (ast2)), dv

		ast2, neg = ast.numer._strip_minus (retneg = True)

		if dv:
			return AST ('/', neg (ast2) if ast2 else neg (AST.One), ast.denom), dv

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
			return AST ('intg', neg (ast), dv, *from_to)
		elif neg.has_neg:
			return AST ('intg', neg (AST.One), dv, *from_to)
		else:
			return neg (AST ('intg', None, dv, *from_to))

	raise SyntaxError ('integration expecting a differential')

def _expr_func (iparm, *args, strip = 1): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	ast, wrap = _ast_func_reorder (args [iparm])

	return wrap (AST (*(args [:iparm] + ((_ast_func_tuple_args (ast) if args [0] == 'func' else ast._strip (strip)),) + args [iparm + 1:])))

def _expr_func_func (FUNC, args, expr_super = None):
	func = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC

	if expr_super is None:
		return _expr_func (2, 'func', func, args)
	elif expr_super.no_curlys != AST.NegOne or not AST ('func', func, ()).is_trigh_func_noninv:
		return AST ('^', _expr_func_func (FUNC, args), expr_super)
	else:
		return _expr_func_func (f'a{func}', args)

def _expr_subs (expr_commas, subsvars):
	if len (subsvars) == 1:
		return AST ('func', 'Subs', (expr_commas, subsvars [0] [0], subsvars [0] [1]))
	else:
		return AST ('func', 'Subs', (expr_commas, ('(', (',', tuple (sv [0] for sv in subsvars))), ('(', (',', tuple (sv [1] for sv in subsvars)))))

def _expr_mat (mat_rows):
	if not mat_rows:
		return AST.MatEmpty
	elif len (mat_rows [0]) > 1:
		return AST ('mat', mat_rows)
	else:
		return AST ('mat', tuple ((c [0],) for c in mat_rows))

def _expr_vec (ast):
	e = ast.comma if ast.is_comma else (ast,)

	if all (c.is_brack for c in e):
		if len (e) == 0:
			return AST.MatEmpty

		elif len (e) == 1 or len (set (c.brack.len for c in e)) == 1:
			if e [0].brack.len == 1:
				return AST ('mat', tuple ((c.brack [0],) for c in e))
			elif e [0].brack.len:
				return AST ('mat', tuple (c.brack for c in e))
			else:
				return AST.MatEmpty

		elif e [-1].brack.len < e [0].brack.len:
			raise lalr1.Incomplete (AST ('mat', tuple (c.brack for c in e [:-1]) + (e [-1].brack + (AST.VarNull,) * (e [0].brack.len - e [-1].brack.len),)))

	return AST ('mat', tuple ((c,) for c in e))

def _expr_curly (ast, forceset = False):
	e   = ast.comma if ast.is_comma else (ast,)
	kvs = []

	for kv in e:
		if not kv.is_slice or kv.step is not None or kv.start is False or kv.stop is False:
			if ast.is_comma:
				return AST ('set', ast.comma)
			elif forceset:
				return AST ('set', e)
			else:
				return AST ('{', ast)

		kvs.append ((kv.start, kv.stop))

	return AST ('dict', tuple (kvs))

def _expr_ufunc (UFUNC, args, argspy = None):
	name, kw = None, None

	if argspy:
		name, kw = AST.args2kwargs (args.comma if args.is_comma else (args,))

		if len (name) != 1 or not name [0].is_str:
			raise SyntaxError ('Function() takes a single string name argument')

		args = argspy

	args, kw2 = AST.args2kwargs (args.comma if args.is_comma else (args,))

	if any (not a.is_var for a in args):
		raise SyntaxError ('undefined functions only take variables')

	if kw is None:
		kw = kw2
	elif kw2:
		raise SyntaxError ('keyword arguments not allowed here')

	return AST ('ufunc', name [0].str_ if name else UFUNC.grp [0] or UFUNC.grp [1] or '', tuple (a.var for a in args), tuple (sorted (kw.items ())))

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

	return AST ('@', var)

#...............................................................................................
class Parser (lalr1.LALR1):
	def __init__ (self):
		self.TOKENS_LONG.update ([(v, self.TOKENS [v]) for v in self.TOKENS_QUICK])

		lalr1.LALR1.__init__ (self)

	def set_quick (self, yes = True):
		self.TOKENS.update (self.TOKENS_QUICK if yes else self.TOKENS_LONG)

		self.set_tokens (self.TOKENS)

	_USER_FUNCS = set () # set or dict of names of user functions to map to AST ('func', ...)

	def set_user_funcs (self, user_funcs):
		self._USER_FUNCS = user_funcs

	_PARSER_TABLES = \
			b'eJztffuP3DaW7j9zgekG1ECJT8m/OY4za2zsZONksAMjCByPZxHcJA7sZO4ugv3f73nxIRWrpGI/qrqKaHVJokjpkIf8PpKHj6s3f3n97Ksvv3r1l+4v/+f9r/+AU7j98vkX38Lp66ffPH/1JVx88c3TZ3Lq5azg/NmLV1+9DOc+XCh5wedf4Tte0e9nz//6' \
			b'w7Onr5+/luuXT4PrZ+nyb+nya758/eXT1//2GXzt31GKeEHOz7775su/4128+O6L7149+/rv4Qo9fvsN/n73Gfw+f/n1t39//Zxk+g6l/ttTfPjyxavvUKoXr779Kwr+4iWFoN//+AZ9f0kp8hU+ldd+RiGfffXy5dOQSujwzYu//tu3QaBvgsB48flnX5LM' \
			b'KMZ/wM/Tl1/j5avPJSHw6rN0+bd0KQnx/MvXz/FT37x4iefPX/ztxed48YwT+fW3JNHXX1JUIJIhVv/5+vkz8vD5iy++wIR59YIU/IwEePrqc4w5PvjqG/lg0BKKzG99BvH7NpxRyy+ffv36268w/LeUvs//8xkmPzlBWvcTDYkC4F3P/h0uP/3x46d/vf34' \
			b'6V/Z9Se4fvf24/vff/jw8Yd//Pjzp9/ffswewyWc3pK39//9G3j56V+/hOtPf/z2/mO4+fX9f/3w9uN/pWc/wuUvb3//4d2Hn+Xq44f/l674w5/ef/r0Ll79Fq/Ca97+mC5//z1+7J9v3/0ern+jt7LzH7++S4L+85+/JWmi0D//FC9/+vX3KO8vf/z8w0+/' \
			b'/JZFM39RFslw+a+3Kerp7fgavAj3v7//OH8Wbv/IpX37j3+Ey3d/fPz5f8LNf396n2L648e37/7v+3j7KZfsX+/ju/749acPv8aPvo3+36XoUSJH8T+kV/6RpfevUaQff/r1Q4zGh6QFkCdqAfLQr+8+/PLL2/iC3356/+795HkS6rdPv3+IH4rqjuJ9+DnF' \
			b'gF46uYlf+MQev+/eXN3YoXP2uuMLhxfG4Y/vjL6WW7ijqwG9dcZ2N/Z64sB3PoSDAENwwkvydcMvt92V7jS4q85s4OI6upJbcrihcMrxjwUHxS8NTmrccrIud8JLuOoN/7i+u+ndtTjhJVxhQBAZ7vnDDi9QAMM/bryWW5CJguruaoDQFv+vg8uY3/UbuUA3' \
			b'FEVjnPtR4mzUdXAVt+hwo/gbkJIYHJLemWtxuelHuhr4x23A9+ZanPASxaSUVhDyOrsN15m74tMNfU7Tvx7CY/wyCSTuLF13o8WR70mRaiOR8jq6ilufHPqpw42iJNbwfU0CQHj6sewFrm7AN3qx/GPh65bTF+5uNKnO4qvH+MDGB0bzj+fkofxIEer77gr1' \
			b'hpphedHF5XdezuiEYeG5Bu9WykK4NXOnoMmpu9m+nTnZ7duCj9lr3fbtJNCNUZloKXOLEDMHO3dwmQOUyiu9ERHAVbmJc7q90VTYIBdd6b4DLaPWteo8nOALeMPy7fCB+GPXegS1Tz3eaCociEBQNGJOBrG40IxSArHgGwjssoKID6N7crHs4pOLY5chuXh2' \
			b'GYPLjaJsq1AgKpB6wz9WJ2mDk8md8BKvHP/cCA7KJV5pzu0hCL6QMrWVB6J+/JJhAIJ39SphHuZz1hEkKudzxT8OC4QAjaJLSscbBjK8oGj1G0xFE6BbYg2O5CT3o7wS3gN4vAn5KHcWB7inLKf4B7LXtdxDkaVX0z/mMv4SXmDqKv6xCHscBu7wEqMPDxFi' \
			b'eoYSuPUUCNR51feRdUKusj7gEgE6pzRmFhV9OMpqubbGkMLgeOVSCaZbl74N7EEvJLX18UrJFQuMFzZcEHwpyMUQIUnULk9ceqRJMXILwehqwz8W86DQyYYuUWCIDJMppCiRRaQcTBGGdcM/1sdCrbi4Y0x6/knMb3vhDrvhHwRZgW9UuqXomjE8vJZbuAsP' \
			b'2C9EyBtO6DGoAmWw/GF8gYsvwNg5eoHbhAfkVZxCKMeRRhSDeEI1582m60HBfU/KhBwG4TBpISuYDgAQihnkCcCREUECUm7Q3WCAyB38ewiH4Xv4V3A/wP+ICYWINSIR9xv0C/kFCNFQxoFwEAx8Qsx6haHgvAE9whf7DmSD8jvYbnDd4Lth6IaxG+E9IEcP' \
			b'gvQakQq/id8GuIP8SqDXg/S9oZiBLhDF0DOiGsYOA8MNRKmHOI34ZZQAgml8N9zDh0c4dDeiwOgXouy7cQBUA/ZFnh0hpOs8HL7zQ+fHboDk6LsBIgHx6yGCoD1QKlSnHEGHg3xuoe4IuR2h141AvIjVHsoekLDpPKY8BAUxAeFBO5AolCYdpqnCaihcXmMB' \
			b'BZ+grytUFDi8ucL4wgOIMp4wWfCx2fBTjOk1MRidBnr6BgmM7j2emoJPQMFXIyuspzPWEFlToAXSu2K9DqxP0gqdvQTrQ/7o5azEg5EXkdLAZeCsoDxnm/C+6Iu+3yDg9HLImytLOpukn6Qcp1gprTiNYtpM0ySlQykRJO6Q65ygiR2OJIANpWPDuRdVTvlV' \
			b'UfF4ICmUQK4yD/lRifEgKaD6VkBPtYD2TTcnqpsrEo7qS67p6FR1pFSAeVJWTC5KqJgskhwhFfKYQ2xjzI4eo5RxCpnl4UkUk1UaCSo0A4jXscMCvtZBXFvOP07OD+CkpbZP7TOq3wwNrU5TZ9A0IybpMToG4QijCqGQYAzGzzTNHEszvmnmRDUzNM2cqGbG' \
			b'pplT1MzVKJ0vPffWXvWx84OSotUOTlJrfeiB77nn5ooiil24KvRlSZd9L3U+6Ym1olxjm25PVLdGCqJ0B450e3TBTqy5edVzYwZhivtLWSx6YiXl2FgxckEYtZi2lJQYLilXvRbbhhZ/wWYRGkvsfZQeUsO3tpeCZCUUffOSFTJKfvVsO/JcSUaDE1qbWi/K' \
			b'ulT0ks08Z86B8+Yg4D4IpquQ99lWcGXELmuFFRznfMfeHedkT3cjeN2AN+z4p2j5M09SSA1OJMemDq8vNRm4YDqmF8c45s2O1Agl9+xThQua54Lm7YVmDt9L7V8snjHmbHjiEmRD7dFyVlKhzhk61nsc7NpqlSdYq6SRPIqH8Kg2KOdEdKJ5ILi2TScnohMc' \
			b'u6ZkpBScW+I/cDehbiXhZJSBKaxk1B+cmxKOooQNcYQkWhuycMdDFoZWYT3VnD9QrQiHEjcVnaiKjGm6OVXdMHk33ZyebmgaBDUyLGHbMZivME8D+48HafyQXK22cbdprqhx81AD+7lrAb/GdXg6Gcd3m14ULbav3bN3vpfZQdhboUj+lg9upxm94bRnqwz3' \
			b'rHqx78hEGO6hj+MwSGktvWtLAoEajqfkLB/s6yaMnAi92j0P3r+iEUmU8WX+2uD5DfIiAe9eULLp41DLfUhA7pJuCbe6uUoE0tJobxqZlkaLaWRbGi2AlOHOh9ELVGndWlOn2poSK5pUYt/ggC/VRsxtF/tRt3QppYulaojVuCLQxScHjmRUMo5PbY0E8VwT' \
			b'3jGouO/DkEoaTXLseqbaxLF0isfSKR5Lp7hVq7lJzE+dtIgdgwePADpvVb/BkYHUxd6mAZ4oub3BUZttHMKDp/o4ZuMAzx0FaKxjGkWMw4rtJUWfF145OlvJuFwjPGQviIe8biD34O0mJx2izl9QTnPDBUXWm1asHr5YSe+231xSTrMtpz18xxfbA3BahuLZ' \
			b'GErW8NQ80J9Ohk4934GGdFjQUcvQTn0dxhnqtPYd9aaR14Ff15YjOdFcABHUbKzXvNQmn1jf1gel4klpvlO9KJ9DOlY0pmy2OhDaqdmdshVVEtoaTkdcnpO7qYhUmgqOM6ROOyk4ApJqCNiow9ACJUMKaGRAA8ajqsvoVlqOxksDc84gRWQMFQ9hpLBeSa/D' \
			b'EyOsVLItoCsH4xPXSYyVEPxwZAIb+c72/F5L72vWnWDsMm29CmmzEGq30Ufr0ouMe0rMaZrNaZrNaZSK0pVKZa/H+eG8tLfiQui4TNJQvO9pKQoqqaOMUbVy5tGpjou15zCOAcMxjngGAM8f9zY1Z0xrfz74MPYBU52aiCaMsOQWieEWieEWiZFGh6F2BIFz' \
			b'wHxB8DTiUkdIR99WR2O02W13hugazpGGc6QJBl4KxKsVUCY016HSdhEdM1QwrIyNsaIqG2qsrCrLqmJffALZbBj1ZJth+BQLH2V6y5necqa3rap7tJaGooIyXzbFujZo8DRVhlxgecKLC/teOKy4gA9c2i1WYDB+Tmo9joub4+KG3ruofdcG1m2Tj+XuEviA' \
			b'F1qhM69SdkUJLVzvJYl9S8bCXL0NpduAyYfJynO04kpwIW0HysiWzE49LkuILV9s7uGyTTFDYwJyPh74nYOohCtkspxhb6WmZcMcMFr7iYUZm5IKSupbuhQxYMNtBMxZSnKUypuIuMThhrMindEDm6Q2HW4b2CnaQgJND7iNxJhFVRPnEX1CTCRqA0VJCc8K' \
			b'+Wayc4LbkHx5+hS0MFD6c+JPFciEDQmHC7RuAiU7Tg9KCyvUOvD8MOoNHoRflBRLiA6u0ohLNOIyhbhGIa7Th4v04Qp9uDodLk2Hy7Phipq4PCQuDYmJhpkI92/DagNO3MTFz3GZbVQeLnaKjIvdPLgwJ8qIK5hiixtkVTj/EyoHChcXwWoEyK1wLQy0KOLs' \
			b'kB7zFWgeqwKYwJTCmNEgDOYiTGtMbIibwulc2NOKiwFgxzd2gkM8FQ6sRdMkjqjFsSYedz2FaxyVMOC/BSXj5sADbnlKm7vizqO4FStu34pbx3a0iSZuiTrghtEb3NtzgzsxoxPtN4m7mG5wR2PcbRp3EMXNUjVuH6zwrRvcNZk2qoW34avwtZitb3rahxOD' \
			b'01fRmfYhhneMFBxfRM81hQNPI8lAexfDwxE3uR14Y94Rd62Ga4qJwq2Acd9VfE1vaAdT2iCV9kFGYWijZNpHl/b4xKoaRXJEKXCTYlDbjfcSE9y1k7bO3lBagDPklBvc59SheD3uwIkpQJ/DV+Mep/haOA8oLe2mvKEPjbTjKu1mregR7XGNe3XecDRp024I' \
			b'B2dAg5sBr+krJA0lVy8bOBvehBv3JB1ReNqAlDdqxV1mPbrRJrOoFtQP7tQK5ejGYRTgxR43OcaEoh1c4Swfx8rvDeIX7a9qSHAIAT4G2jwaP07SY5Q9xhIeD/33CB4IGQ0wzhwwGlo0tLgLtFCIFjtwwpagwqXqUI4ZOtvVeIIcw92DB6QzZM1kqShgSayM' \
			b'lfDErsCUx4wlboYnuH+9WYErDtPXLaCI240jrnNcAl0BTVzCE1dCFPcwmOJYSu269FfEFbcHWdwqbDkTSEExMlihBFuGlu5P+wRpyT1BYhoMnOz/4li8/XgTu/AYdahdlzfZJtgT+vRm3Yncx7iARr2Yw1dhkp/CErVAiy3aBFHTlmTCKivt47C+9ibv8FTS' \
			b'JOVmcepKzQFNTVueAdyoqRoAzmQDE7PBirFnr9Axgjsf4+bDBITgD5fPXwREvQIU4d24WdgEHCEs7khRBZKegRKXj8LlvQ4FTMxDq0FTZcC5SeCJswUmAArPcEplBFIslsQ4C1gKHkbGUzwFSMVrEHNMwIpdzYYhiM7U2WEZX+lbDLHsLR4RbynMFuCiqyAu' \
			b'bfpMdcCDkZfkGPkVW+hL783+t9A4yYqd8FF29J5FZGSIjmmTIfX8C5OvjRJ1bWbuDOkj0dQmonr2WU7cTfxkAHrxgngf32gI+sPlMgP0K0ggKjxRgTjVEcIk+jiK4XB2IK0xQchbdhBE0iliB3oNTMHhcraIMkXWYL5wQB5Q+pg2EOCeUOaHkv8EuQ1K7hNI' \
			b'l/+ltaN284lZV4W9JY2oIzEJ0UjiEHsgj/S35JLGIwrS6wG4xDKX2AUuwQSxu+vmWBKsUIgVCgkMYhOD2MmRGMQWGcQmBrGctWwVhwiFlBgkl2aLPeIT7eaip2eWPxBYY+QULPsdJapQIsZN7p43AiackYemwmgztmBnlwlHVCG+l5nCrmCKoNeMKdipkilS' \
			b'bOpowlJ+j1SxlylSqmgWORDFFk9IlPaxRIEc7C07N27JDEfnhNauOLN2hWMuWOqj6fd00iBYSzdNL/00dN7wORCBmxyJCIp9N33qvKnrv6FPcOAtBsjF2GKA+ES7uczpmeUPTNoNRY+jRBALQXJk7O/nrYU8IBU5uQzgz7cu94aZXHwtg79bAf4hvTPwZ6dK' \
			b'8E8RqgN/l4Df7QP+lCKaxQ3A7+bAL9GpbR64xgCNAc6JAQZmgGGJAYY9DMDhiQEGYYBBGGBIDDBMjsQAQ5EBhsQAQxUDDMwAQ4EBcjG2GCA+0W4uc3pm+TRhgKLHUSKIhSA5CgMMMwbIA1KRk8vAAHzrMrmIAcTXMgMMKxgg6DJjAHaqZIAUoToGGBID7LMi' \
			b'ZCmiWdzAAMOcASQ6tQzgGwM0BjgnBhiZAcYlBhj3MACNuGcGGIUBRmGAMTHAODkSA4xFBhgTA4xVDDAyA4wFBsjF2GKA+ES7uczpmeUPTBig6HGUCGIhSI7CAOOMAfKAVOTkMjAA37pMLmIA8bXMAOMKBgi6zBiAnSoZIJOvigHGxADjPgZIKaJZ3MAA45wB' \
			b'JDq1DDAcZHI+Gx6wjQrOnAoIN1CQBSpAAXtiAzyVCEF8UAGSoYB03vBZCIF9xSMSAnndIgR0FUJQVaZl+gQHnhPCRIw5IaQn2s1lngS0/I2cE8oeR4kjrrKeHJkT1MwiMAmIZS9cCicEZWSiIScEX4ucwK/dzwlRnYkTxKmOE7IIVXGCSgYBfskOTshSRLO4' \
			b'wgmcgBknhOjUcsLYOKFxwllygmZO0EucoMkPz4gqcwL7oAKkhRO0cIJOnDA9EifoIifoxAm6ihM0c4IucEIuxhYnxCfazWWeBLT8jQknFD2OEkfkhOQonKBnnJAHJE6Qy8AJooxMNOIE8bXMCXoFJwR1ZpzATpWckCJUxwk6cYLexwkpRUTcwAnzoachOrWc' \
			b'0G8aKTRSOEtS4PGoamk8KgplmBTMDlJgH1SCZCQqQyWfAymYyZFIoTgQVaWBqPzug0nBMCmYAinkYmyRQnyi3VzmSUDL35iQQtHjKHHUE0chBTMjhdwPkYJcBlIQZWSiESmIr2VSWDHONKozIwV2qiSFFKE6UkiDTPklu0ghpYhmcQMpmDkpSHSqSaE/nQkL' \
			b'bbZCY4f7YAceVaSWRhWhMDywSGWzFRTPVsg5gu+oQMkIIyUjjFQaYcS+4pE4ojjCSKURRqpqhJHiEUaqMMJoIsYWR8Qn2s1lngS0MeITmij6HSWaSBPJUWhiNs5oEpBoQi4DTYhWcm9IE+JrmSZWjDOKGs1ogp0qaSJFqI4m0jgjtW+cUZYimsUNNDEfZxSi' \
			b'U00TNI+WxrsK6I8E93oL5TViegLfXcgrIBqAkcBvYKBDIAtAJeBEQJFAAAo1fvxox/e8TmEjzkac50ycmvva9FJfG2Zc7mvTWV8bXoOYdGLiFH89AwcRp5YeN5163GZHJE5d7HHTqcdNV/W4ae5x04Uet4kYc+JMT7SbyzwJaGPEc+Is+x0lmogDyZGJU886' \
			b'3SYBsRCGSyHOoJVMOiTO4GuROPWKTreo0USc4lRHnFmEqohTp043va/TLUsREVeIc2u+d4hONXHum8DXaKLRxBnQhGeaWFqfBzOrZ5rwGU14pgmfaIL9EU14oQkvNOETTfjJkWiiuJ4Pugaa8FU04ZkmfIEmcjG2aCI+keKaHZil0nMbYz7hCV84iCe88ERy' \
			b'FJ7wM57IAxJPBD/CE6KWTDziCfG1zBN+BU8EeTOeYKdKnkgRquMJn3jC7+OJlCKaxQ084ec8IdGp5omFuXyNJxpPPHae4Lkdemluh/hBnhgynhiYJ4bEE+yPeELmeWiZ56HTPA89TI7EE8V5HjrN89BV8zw0z/PQhXkeEzG2eCI+0W4u8ySgjVcTmij6HSWa' \
			b'iAPJUWhiNttjEpBoQi4DTYhWMumIJsTXMk2smO0RNZrRBDtV0kSKUB1NpNkeet9sjyxFNIsbaGI+2yNEp5omFib8NZpoNPHYaYIngOilCSC4qRjPAcFTpImRaWJMNMH+iCZkMoiWySA6TQZhX/FINFGcDKLTZBBdNRlE82QQXZgMMhFjiybiE+3mMk8C2hjx' \
			b'CU0U/Y4STcSB5Cg0MZsSMglINCGXgSZEK5l0RBPia5kmVkwJiRrNaIKdKmkik6+KJtKUEL1vSkiWIprFDTQxnxISolNNEwuzAhtNNJp45DQhy0LjaS9NYB7dEE2YbLYgXoOYdGKaEH9YoOisFJ83fBaaYF/xiDRBXrdoAh2EJvjdh9IEfYIDz2liIsacJtIT' \
			b'7eYyTwLaGPGcJsp+R4kmFIvMkWmCkyzRxCQgbcIml0ITQSuZdEgTwdciTfBr99NE1GiiCXGqo4ksQlU0QenNNMEv2UETWYpoFldoghMwo4kQnWqaOGzqYKOJRhOPjibYhm2WbNiYNdmGbTIbtmEbtkk2bPFHNCE2bCM2bJNs2GZ6JJoo2rBNsmGbKhu2YRu2' \
			b'KdiwJ2Js0UR8ot1c5klAGyM+oYmi31GiiTSRHIUmZjbsSUCiCbkMNCFayaQjmhBfyzSxwoYdNZrRBDtV0kSKUB1NJBu22WfDzlJExA00Mbdhh+hU08S+2YTmMpjClcjCNsI4O8LQPFpYL40WhoTAnMsDhnU2YFjzgGGdBgyLP+qBkgHDWgYM6zRgmH3FI/VA' \
			b'FQcM6zRgWFcNGNY8YFgXBgzTls1Rjq0uqPhkJvHsGHkGuvgNvDFKR1QpBHVEybjhzFE6ombjhicBqSNKLkNHlCgn94YdUeJruSNqxbjhqNisI4qdKjuiUoTqOqLSuGG9b9xwliKaxQ0dUfNxwyE6tdSh9s05bNTRqOOcqMOwgdssGbghEQx7w+ZGZuM2bOM2' \
			b'ycYt/qi5ITZuIzZuk2zcZpgcqblRtHGbZOM2VTZuwzZuU7BxT8TYam7EJ9rNZc4PREQb/UbmUNzoKIWgRodYujNHaXTMLN2TgNTokMvQ6BDdZDJSo0N8LTc6Vli6o16zRgc7VTY6UoTqGh3J0m32WbqzFNEsbmh0zC3dITrVzNEmJt5X3xTW8PrGG3fKG5s9' \
			b'3GHWTlRky7dasnyDB8WWb5VZvhVbvlWyfIs/KmBi+VZi+VbJ8s2+4pEmKhYt3ypZvlWV5Vux5VsVLN8TMbYmKsYn2s1lngS0MeKTiYpFv6NEEycqJkeZqCiWb9XjWkwqTVjMX0ATFuUyTFgU7WRS0oRF8bU8YXGFBTxqNpuwyE6VExYz+WroQyULuNpnAVfW' \
			b'56miWWQI7zXTiJpbwkO0qmlkYQPQRiOt2XEC9HGbZgfuDQofoS1C99GGpQNpA0+BNvAaxKQT04b4wwJFZyX3Gz4LbVg1OSJtkNct2kBXoQ1+96G0IRug4mlOGxMx5rSRnmg3l3kS0MaI57RR9jtKNKFYZI5MG5xkqbUxCYiFMFwKXQStZNIhXQRfi3TBr91P' \
			b'F1GjiS7EqY4usghV0QWlN9MFv2QHXWQpollcaW1wAmY0EaJTTRNtNnejiTOnCbaE2yVLOO72yJZwm1nCLVvCbbKEiz+iCbGEW7GE22QJt9Mj0UTREm6TJdxWWcItW8JtwRI+EWOLJuIT7eYyTwLaGPEJTRT9jhJNpInkKDQxs4RPAhJNyGWgCdFKJh3RhPha' \
			b'pokVlvCo0Ywm2KmSJlKE6mgiWcLtPkt4liIibqCJuSU8RKeaJtps7kYTZ04TbMSwS0YMy36QJjILhmULhk0WDPFHNCEWDCsWDJssGHaYHIkmihYMmywYtsqCYdmCYQsWjIkYWzQRn2g3l3kSMF1NaKLod5RoIk0kR6GJme1iEpBoQi4DTYhWMumIJsTXMk2s' \
			b'sF1EjWY0wU6VNJEiVEcTyXZh99kushTRLG6gibntIkSnmiYe6WRuyCnIFH0jizMhC/UQyysyYaglwlDsB9+dEYZiwlCJMMQfFS0hDCWEoRJhqGFyJKtFkTBUIgxVRRiKCaOXed30BcwBBG3BfEHeekmLLftFFFW7ufSTmNh4NbFfFP2OEmG0XyRHsV/MqGMS' \
			b'kOwWchnsFqKfTDqyW4ivZbvFCuqIus3sFuxUabdIEaqzWwxkuou2i330kaWKZpHDYotz+ghRqqaPNsm7EceZtzLY1G2XTN3gwbKp22ambsumbptM3eKPWhli6rZi6rbJ1M2+4pFaGUVTt02mbltl6rZs6rYFU/dEjK1WRnyi3VzmSUAbIz5pZRT9jhJNbGUk' \
			b'R2lljLNWRh6QWhlyGVoZopVMOmpliK/lVsYKE3fUaNbKYKfKVkYmX1UrI5m47T4Td5YimsUNrYy5aTtEp5om2iTvRhPnTROuJ5rA016awKzWE03gKdAEXoOYdGKaEH9YoOisFJ83fBaaYF/xiDRBXrdoAl2FJvjdh9IEfYIDz2liIsacJtIT7eYyTwLaGPGc' \
			b'Jsp+R4kmFIvMkWmCkyzRxCQgFsJwKTQRtJJJhzQRfC3SBL92P01EjSaaEKc6msgiVEUTlN5ME/ySHTSRpYhmcYUmOAEzmgjRqaaJNsm70cTd0QQPhnwwusABgzspQ89oQ+fUwaOi3NKoKEcHUUc2KsrxqCiXRkWJP6IOGRXlZFSUS6OinJociTqKo6JcGhXl' \
			b'qkZFOR4V5QqjoiZibFFHfKLdXOZJQBsjPqGOot9RoonUkRyFOmajoiYBiTrkMlCHaCWTjqhDfC1Tx4pRUVGjGXWwUyV1pAj1UdTDCSSNjXL7xkZl6aKj3IFD8uFRJMGY+a9nkoVdZX3gEHUu7HGkfQPPjTOO1LSAtFDYgw1psdAbxc0Mu9TMsNzGKO4ciBlU' \
			b'mhZWmhZWmhY2NS3YVzxSD9S8aYGZyqaWha1qWdyEUbOFpgXnuPS/3QsVhdRuLnd6ZjnZJv1PRY+jRBL7n8gFswnSA6OinrUtUCT2R8JRGaQLIQh5jgwRYmC5eREuV3RDrWhfRLVm3VDsVCQJicxOjqBIW/l0XT8UNzAIdChBdnZExaR3mgUOHVFYFDBbg/dZ' \
			b'WyNEbcoQxj+h6kqkCLj3hANPiBShoD7hLQ0jVeiFvWZPkyqOTw+RGgItDBkdBCoIFPAY4P8ke5U8Nw38UtPA74Z7zDpemgNemgNemgM+NQf85EjNAV9sDvjUHPBVzQHPzQG/DffbTYAolHZzOdMzyy+dVP6LHseQHiZ35Mo/o3uo+YvHTbYaICU0y42VfL+q' \
			b'hu9X1PCDUFkNn50qa/gxZodX632s1t/sNTNn39AsaqjU+xlYh6jsq85LLZ4geWFCdYPkBsnHg2S2B7sle7Ab90DySI8JksUG7MQG7JINmH3FI0Fy0Qbskg3YVdmAHduAXcEGvA3JUSjt5nKmZ5ZfOoHkosdRIoWQnBxLkCwJN4Fktu86tuy6VWZdt8KsG5WU' \
			b'QTI7VUJyjNnhkDyuheT0Dc2iBkiem3RDVNZC8sLk5AbJDZKPBsmeO0X8UqeI39MpgkOJpVPES6eIl04RnzpF2Fc8IiT7or3Vp14RX9Ur4tne6gudIluQnITSbi5nemb5pTkklz2OEinI0JljAZJDwuWQ7Lm7w3M3h1/VxeFXdHFEJSVIFqc6SE4xOxiSfb8S' \
			b'krNvaBZVINnPzachKmsheWEi8GlCcuvjvtQ+7v0QbhjCzRKEmz0QbugxQbgRCDcC4SZBuJkcCcJNEcJNgnBTBeGGIdxsQ/hEjC04j0+0m8ucnln+wATOix5HiaCeOOZwnndpT4JigeP0FHBnZ5eJRSgvvpeB3qwA+qDKDOjZqRLoU2yqurIprRnt+SW7wD6l' \
			b'iGZxA9ibOdhLdFaA/aS3emFabwP9BvqPB/Qtg75dAn27B/QtPSbQtwL6VkDfJtC3kyOBvi2Cvk2gb6tA3zLo2wLo52JsgX58ot1c5vTM8gcmoF/0OEoEtckdd4J+HpRA32agz84uE4tAX3wvg75dAfpBlRnos1Ml6KfY1IG+TaBv94F+ShHN4gbQt3PQl+gc' \
			b'CvoLk3Qb6DfQfzyg7xj03RLouz2g7+gxgb4T0HcC+i6BvpscCfRdEfRdAn1XBfqOQd8VQD8XYwv04xPt5jKnZ5Y/MAH9osdRIoignxx3gn4elEDfZaDPzi73g6AvvpdB360A/ZDcGeizUyXop9jUgb5LoO/2gX5KEc3iBtB3c9CX6BwK+gtTaxvoN9B/PKDP' \
			b'41j80jgWv2ccC2YpgTAv41i8jGPxaRwL+4pHAv3iOBafxrH4qnEsnsex+MI4lokYW6Afn2g3lzk9s/yBCegXPY4hbUzuuBP086AE+tlwRXF2mVgE+uJ7GfRXjHaJqsxAn50qQT/Fpg7005AXfsku0E8polncAPrzES8hOoeCPk2UBVTevxHNWWO/OsK+M7Uc' \
			b'4A7ggf6RcEH/ECvxYJnCKUUb4gUsGwsb0eAEqt3cQO/TDHVKyEEJOahEDlhGsiMtxVMkB5XIQVWRQxjUrgrsMJFjawUe/DKKzD1BM7FTOMsxxyJB78a9ZwiEdvgfJaq4CE9y3EUTk6C0DE9GE+LsMuloDR7xPaGJcdc6PAWqwJWgttbiCWJna/GwU+VaPJ5G' \
			b'tqtqvsCvm7VjcrL04UwcV+OZk0aIVCINcsFfYA74HTT9GnIH9iA50I24Y+je7GGObc4YiCqUkISwQk4JzAcryWDXuBvCfQSvvGJPq09tdgyVyYfIWAHfNaC7VPHOQbYGXIfDAXUVkNoEnBPQDGCJZWY1UO6EyFC+ZSZogMSIgQUADOh3C+hbHrcSQO5mvgQl' \
			b'ohVBVXHYyXTACeLQzfbQv13As1hBnWBNJcogxBwOLeswBaEk4sgURAJ8ICKMexGhWJF8GFAI9UHIOyVoiHW6U4cHfXuIQAwvwsS8roVTzIcFqDisUkVVpkeHF1nFqJdG8jZuhH29HxF2KNLXbfED884ODMnxQzbjxpy0jCOg6MNqFu7BcWTalmRA6e+5vgF+' \
			b'IOF7jzjqzrj+cSCo7ASU0EA7cVAhOfN/ARhswT9E5YQYATcTw5aPXjEq9tQqK8oeXFnp/oRs+QTkx4YMiHpoQ0a6vfbAzXDXiBNQRmco4y+wZdPvqbaElXHgGvsTCGWQdOw22lCrGt2wxYvdGrg4rcpXyoF/d4doxOVVH4xG+giIFBFIJwRCLV52E0nR3jbL' \
			b'VRyUxnI9B7PbTc/LJMyxKPVSkh98gqmEa2Pd9GnLLrwxVCtSt+pvwY2lix3x9wNTAlEomVILMGUfAVSZA1tZ44pWliXqepjK0I6KkMnhh9DpBCpE8xYWa9AvwQ+J/1ggCHPFoS0tv6alRRCk1rSy9En23+5CEtBNTwJC6cWVGftjVX7m9rOHqgChrQKu0ZCr' \
			b'd42hKFSGYkVoXgEKlZ57q+yceLNrG2WwUJNB9AYttjdovj1qjWc2Tu1hKz0INvhO+tEH9PHEyk+xzhOqOfPKjenenAAQ7RpScPdGpcfW7FK37dRJiDK4xwooNJCDBmwMNDjjQY1LR6+y1LaazO2NS92fwxMgIuqtsSeBFIvogGLdST3lsSDF2nrJAUhxVnWP' \
			b'3fUOTyOw7qq+8chwQqK+qoaxygoNsaoFCFzR8UExwtxhe6Z2fPh8LOAD4QX2op86ZuBgzRMGDpIM33WXzZUyfJjxUAyhJVgfEkgUJ8L69so6NPH1aDI8MJpkSIK7Vhy11vGASNJQ5FbD3qYIglo7jUrIgwPIPYDHUA8e4xHBY2zg0cCjCjxOpQVzDuAx1nd0' \
			b'bI4HHiBWA48GHjXgYRt43BV4gCIeRS/pRfSMnig6nC4w3CUK4CTTU+8DvZNS3/0JpeAJgh6aSUCWBgCnDAC3MKA+PhCg190hBtD7zssOcmcT8bo/vXpCqAsF6AmiJeGBanjQ8OAYeECF+MQqBZeGCM48AVgmHNANBxoO3B0OUJl/tI2DS8MBa58AcBMOnMaA' \
			b'y4YDZ4MDuuHAY8SBRzKcsuHANg7s3MX7KJhARfh0+g0p+MlAgkhzD4hAb16PCIrMDd3W/tYJG8Ke1rs2sybUqB9j2VDj4msPlK1PCSncSSGFuzekuJO6wyp8qB812fDhUvGB8tsZWiDvAh+4LD6KtoWxTwjpIVPjBa0VausHQjY8uCw8oAx11iMSDsADSoxH' \
			b'3tdg0BqpadUEvOD6wS3GNjY8uAg8IP+XMURpBSBQapxL76OGGoKmXA9nhXjg2nDFhgdFPCC/lzVi8dKMERorCBvGgTZq8ZJxAAvkyYxZPAkYQNkuAgQUDl3GPZh8jxeG0KCNWbwwNMCMe/wRiyeLBhdUKeg1dh5ypaANWbw0GBgbDDQYmMPAIxmxCFGNi9U+' \
			b'OCSUNnh86AVq23THQxeAw4IHoY8HFViOjwkY4LQTNg6e++xOY0hj/VqyLoHFZDfZU61DVOz8uqoeobPtPM4fMGhn4Nl/zWgmDFbcX/URVDXqtkddV9+ghKHV8cfleocfngCAU7XjNIY6NjRpaHIQmhT+a9CEajINTbbRxHJ1BAffH4ImpzEwsqHJHaHJRSBJ' \
			b'v/VfhSR9Q5IykvTr+kIyFBm6N2OADsYNBg1GDENYYQglRsKHHBwIGUIZx3IdyiGVQS1lr1TuPJexeXmIZUDh5uE+z98ha8dcHXM0XvD6xRvOvpRztS3n2JRbYx7Tuf4xwUjvmx3qRk3TGltzBWSJzo3H8bZJy1AaQdQJeA4MhJPEVisTXJdBaJLwVODuMeVR' \
			b'eirtUQMqaAHfSKM2c3XEorikEvpoqX9wrhooVbdUTSS6onb0o9eQTphc1lKA0/vWVN+9oT3ONhRtJFSr6IGCB1DnwL2mqP6gR3LW3Rul0TOkHDkYuLQeHZz5/hrOVzfwTvRBH7iB9yBy0tbPnrZjdbSx4dCByvLdmWlvd1QN7Wlu8I24Czzv1qx4P9W4SSFW' \
			b'UtAEjfkr7bRM267jBoC0HTp/X9d/X3cLf/QBgx9wOz8h26T5hW9Rfc7M/tLWZ+P8GX3aFj6t8etQ5wBV4srEm5WS0A4EoVOaVuZUIp0SCaHmGv+Q2K0sQZz+7Y4/ft5TpzNe40qc3L6zFA1XFw3I9XUxgWy9+Id13z3PSW5fI7fbJ/ps16JiVPBbk+jA2xf+' \
			b'sEI//6OKNlWsNVWmsycAFnRFkRwKkex3xhMEw0aMnzRctiMPYDXZmH2g0YNYx8bKFNaqaFUsxVP+KHm0opULECFpDdKQXIC41AeH0+Yo6VBWL0m42Z2MG8/tjs3ISYrEkJIVIruhDWJl79fvkdDSH3LDOPtjk1L5f1fYfWHYX+lNZR/bUm37K36V1DyeRl7G' \
			b'WvZDHxR/uDown0OGO9esTjtiHXLozYEBjnywyvsThDayO5d0vnkIvavuFA5FBvmZ03BXr2fdqxPBO909+MEJoGMC4Hrww30WAfvISoHv+Bi5h/Uej+Fe377m4MxQasOsLg0zdd+uQGCNtPbAvurawJwOdl4osNFy70VjHB9R6aA++HSQ7Jtu5nrnB/bx3Pc3' \
			b'9h6cP0ot1d15YlXl4HalxXazA3vbt11XHmjgOSQAJ4pvhWap0GCv58UdnDsO6z+4/yKDVtqjHZwkYyswiwXGdJd3cH/5YR0Rqxugtys0trvbA4cOHBKAk6ZvBWep4KBl7eIOzh2lJv0dFBxS+20KD44FuusDh9wcEoBTaKvN38rPVvkx3eUdnDtKnQB3VX76' \
			b'25Yh293HgSPUDgnACdV6CZaLkesu7+DccVgfgau1IRxQmoLWpiXKd+sPHMR4WACQedETjt3M7jn5Wm/CcuEau8s7OHcc1ptQXbhmmr9VQcOB3/d55COrDwzLadq6IxZLHI5RvLiDh88d1h1xGiXOdid5cIK2Tozl4ua6yzs4d6iLzh04SLRX5VwC74o5Bd4j' \
			b'uQX+NeYY353roUDDyqhtZ1W64lykDx7ZdMdDmerxuwAHOEtu9YED7w8KsH2EuWmHBaKJZWlSGenhsC6Vk9eD7h7PwQoojZB/xAow3eM5WAGH9YbcgwK0OUAJfq0ibPfwB7LkbXywQkqTFlZUKo6rk2GtXlx30IFTtQ4NU33s/xhrp3K2xSPRztA9zoN1U5oi' \
			b'cTa6welOj/LgOXgHz94416kbuGzE4QetCpH9172l8NLt12e3Ez/Lb5kerPdTnMJxHL3r7nwP1vVh4zvOWddDd74H6/rwDoxz1fXYne/Buj68k+RMdY0rXpztwbo+vD/mXHXdd+d7sK5d90ZrmtMtoO6jg5T8AR0wMWnO8QZXJuYH0NTKcwMkOfnA5SNAET0o' \
			b'iFYu4PfaTdk3Ljwx+Wff/ZZvVCOFAKXO/pUMPbaT5VAoU7A7EFWeOTkz5ZlIMhBmAENy4SJs2eJrvOhZWPAMs09Y6AxtHvJ1M/0KzhvU2KLjF5r0Kcqj0p3ouMzBd95gPoc8SvPrMFKScKAhMrfYYFLRtLALCICdSTgZaOB+CfAQV3lhFeE+ocqO5CJvA6Up' \
			b'SnrlOXFwr7DgAn6+v/7/1hBqmg=='

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

	_VARTEX   = '(?:' + '|'.join (reversed (sorted (x.replace ('\\', '\\\\').replace ('+', '\\+').replace ('*', '\\*').replace ('^', '\\^') for x in AST.Var.TEX2PY))) + ')'
	_VARTEX1  = fr'(?:(\d)|({_LTR})|(\\partial|\\infty))'
	_VARPY    = fr'(?:{_LTR}(?:\w|\\_)*)'
	_VARUNI   = fr'(?:{"|".join (AST.Var.UNI2PY)})'
	_VAR      = fr'(?:{_VARPY}|{_VARTEX}(?!{_LTRU})|{_VARUNI})'

	_STRS     = r"'(?:\\.|[^'])*'"
	_STRD     = r'"(?:\\.|[^"])*"'

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY)))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('UFUNC',        fr'\?({_LTR}\w*)?|\\operatorname\s*{{\s*\?((?:{_LTR}|\\_)(?:\w|\\_)*)?\s*}}'),
		('UFUNCPY',       r'Function'),
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LTRU})|(\${_LTRU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\$?(?:{_LTR}|\\_)(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)(?!{_LTRU})|{"|".join (AST.Cmp.UNI2PY)}'),
		('IF',            r'if(?!{_LTRU})'),
		('ELSE',          r'else(?!{_LTRU})'),
		('OR',           fr'or\b|\\vee(?!{_LTRU})|{_UOR}'),
		('AND',          fr'and\b|\\wedge(?!{_LTRU})|{_UAND}'),
		('NOT',          fr'not\b|\\neg(?!{_LTRU})|{_UNOT}'),
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LTRU})'),
		('LOG',           r'log\b|\\log(?!{_LTR})'),
		('LN',            r'ln\b|\\ln(?!{_LTRU})'),

		('LIM',          fr'\\lim(?!{_LTR})'),
		('SUM',          fr'\\sum(?:\s*\\limits)?(?!{_LTR})|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?(?!{_LTR})|{_UINTG}'),
		('LEFTDOT',      fr'\\left\s*\.'),
		('LEFT',         fr'\\left(?!{_LTRU})'),
		('RIGHT',        fr'\\right(?!{_LTRU})'),
		('CDOT',         fr'\\cdot(?!{_LTRU})'),
		('TO',           fr'\\to(?!{_LTRU})'),
		('UNION',        fr'\\cup(?!{_LTRU})|\|\|'),
		('SDIFF',        fr'\\ominus(?!{_LTRU})|\^\^'),
		('XSECT',        fr'\\cap(?!{_LTRU})|&&'),
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

		('NUM',           r'(?:(\d*\.\d+)|(\d+\.?))((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))"),
		('ATTR',         fr'\.\s*(?:({_LTRU}\w*)|\\operatorname\s*{{\s*({_LTR}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"((?<![.'|!)}}\]\w]){_STRS}|{_STRD})|\\text\s*{{\s*({_STRS}|{_STRD})\s*}}"),

		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
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

	_PYGREEK_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.GREEK))) + ')'
	_PYMULTI_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.PY2TEXMULTI))) + ')'
	_VARPY_QUICK   = fr'(?:{_PYGREEK_QUICK}|{_LTR})'
	_VAR_QUICK     = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK   = OrderedDict ([ # quick input mode different tokens
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})|(\${_LTRU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LTR}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)|{"|".join (AST.Cmp.UNI2PY)}'),
		('OR',           fr'or\b|\\vee|{_UOR}'),
		('AND',          fr'and\b|\\wedge|{_UAND}'),
		('NOT',          fr'not\b|\\neg|{_UNOT}'),
		('SQRT',          r'sqrt\b|\\sqrt'),
		('LOG',           r'log\b|\\log'),
		('LN',            r'ln\b|\\ln'),

		('LIM',          fr'\\lim'),
		('SUM',          fr'\\sum(?:\s*\\limits)?|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?|{_UINTG}'),
		('LEFT',         fr'\\left'),
		('RIGHT',        fr'\\right'),
		('CDOT',         fr'\\cdot'),
		('TO',           fr'\\to'),
		('UNION',        fr'\\cup|\|\|'),
		('SDIFF',        fr'\\ominus|\^\^'),
		('XSECT',        fr'\\cap|&&'),
		('MAPSTO',       fr'\\mapsto'),
		('EMPTYSET',     fr'\\emptyset'),
		('SETMINUS',     fr'\\setminus'),
		('SUBSTACK',      r'\\substack'),

		('VAR',          fr"(?:(?:(\\partial\s?|partial|{_UPARTIAL})|(d(?!elta)))({_VAR_QUICK})|(None|True|False|{_PYMULTI_QUICK}|{_VAR_QUICK}))"),
	])

	TOKENS_LONG    = OrderedDict () # initialized in __init__()

	_PARSER_TOP             = 'expr_scolon'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	# grammar definition and implementation

	def expr_scolon_1      (self, expr_scolon, SCOLON, expr_commas):                   return expr_scolon if expr_commas == AST.CommaEmpty else AST.flatcat (';', expr_scolon, expr_commas)
	def expr_scolon_2      (self, expr_commas):                                        return expr_commas

	def expr_commas_1      (self, expr_comma, COMMA):                                  return expr_comma if expr_comma.is_comma else AST (',', (expr_comma,))
	def expr_commas_2      (self, expr_comma):                                         return expr_comma
	def expr_commas_3      (self):                                                     return AST.CommaEmpty
	def expr_comma_1       (self, expr_comma, COMMA, expr_colon):                      return _expr_comma (expr_comma, expr_colon)
	def expr_comma_2       (self, expr_colon):                                         return expr_colon

	def expr_colon_1       (self, expr, COLON, expr_colon):                            return _expr_colon (expr, expr_colon)
	def expr_colon_2       (self, expr, COLON):                                        return AST ('slice', expr, False, None)
	def expr_colon_3       (self, COLON, expr_colon):                                  return _ast_pre_slice (False, expr_colon)
	def expr_colon_4       (self, COLON):                                              return AST ('slice', False, False, None)
	def expr_colon_5       (self, expr):                                               return expr

	def expr               (self, expr_ass):                                           return expr_ass

	def expr_ass_1         (self, expr_mapsto1, EQ, expr_mapsto2):                     return AST ('=', expr_mapsto1, expr_mapsto2)
	def expr_ass_2         (self, expr_mapsto):                                        return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr_colon):                     return _expr_mapsto (expr_paren.strip, expr_colon)
	def expr_mapsto_2      (self, expr_piece):                                         return expr_piece

	def expr_piece_1       (self, expr_or, IF, expr_ass, ELSE, expr_mapsto):           return _expr_piece (expr_or, expr_ass, expr_mapsto)
	def expr_piece_2       (self, expr_or, IF, expr_ass):                              return AST ('piece', ((expr_or, expr_ass),))
	def expr_piece_3       (self, expr_or):                                            return expr_or

	def expr_or_1          (self, expr_or, OR, expr_and):                              return AST.flatcat ('or', expr_or, expr_and)
	def expr_or_2          (self, expr_and):                                           return expr_and

	def expr_and_1         (self, expr_and, AND, expr_not):                            return AST.flatcat ('and', expr_and, expr_not)
	def expr_and_2         (self, expr_not):                                           return expr_not

	def expr_not_1         (self, NOT, expr_not):                                      return AST ('not', expr_not)
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
	def expr_mul_expr_1    (self, expr_mul_expr, CDOT, expr_neg):                      return AST.flatcat ('mulexp', expr_mul_expr, expr_neg)
	def expr_mul_expr_2    (self, expr_mul_expr, STAR, expr_neg):                      return AST.flatcat ('mulexp', expr_mul_expr, expr_neg)
	def expr_mul_expr_3    (self, expr_neg):                                           return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                    return _expr_neg (expr_neg)
	def expr_neg_2         (self, expr_diff):                                          return expr_diff

	def expr_diff          (self, expr_div):                                           return _expr_diff (expr_div)

	def expr_div_1         (self, expr_div, DIVIDE, expr_divm):                        return AST ('/', expr_div, expr_divm)
	def expr_div_2         (self, expr_mul_imp):                                       return expr_mul_imp
	def expr_divm_1        (self, MINUS, expr_divm):                                   return _expr_neg (expr_divm)
	def expr_divm_2        (self, expr_mul_imp):                                       return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                            return _expr_mul_imp (expr_mul_imp, expr_intg, self._USER_FUNCS)
	def expr_mul_imp_2     (self, expr_intg):                                          return expr_intg

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add):               return _expr_intg (expr_add, (expr_sub, expr_super))
	def expr_intg_2        (self, INTG, expr_add):                                     return _expr_intg (expr_add)
	def expr_intg_3        (self, expr_lim):                                           return expr_lim

	def expr_lim_1         (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                          return AST ('lim', expr_neg, expr_var, expr)
	def expr_lim_2         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):  return AST ('lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg): return AST ('lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                        return expr_sum

	def expr_sum_1         (self, SUM, SUB, CURLYL, varass, CURLYR, expr_super, expr_neg):                          return AST ('sum', expr_neg, varass [0], varass [1], expr_super)
	def expr_sum_2         (self, expr_diffp):                                                                      return expr_diffp

	def expr_diffp_1       (self, expr_diffp, PRIME):                                  return AST ('diffp', expr_diffp.diffp, expr_diffp.count + 1) if expr_diffp.is_diffp else AST ('diffp', expr_diffp, 1)
	def expr_diffp_2       (self, expr_func):                                          return expr_func

	def expr_func_1        (self, SQRT, expr_neg_arg):                                 return _expr_func (1, 'sqrt', expr_neg_arg)
	def expr_func_2        (self, SQRT, expr_super, expr_neg_arg):                     return AST ('^', _expr_func (1, 'sqrt', expr_neg_arg), expr_super)
	def expr_func_3        (self, SQRT, BRACKL, expr_commas, BRACKR, expr_neg_arg):    return _expr_func (1, 'sqrt', expr_neg_arg, expr_commas)
	def expr_func_4        (self, LN, expr_neg_arg):                                   return _expr_func (1, 'log', expr_neg_arg)
	def expr_func_5        (self, LN, expr_super, expr_neg_arg):                       return AST ('^', _expr_func (1, 'log', expr_neg_arg), expr_super)
	def expr_func_6        (self, LOG, expr_neg_arg):                                  return _expr_func (1, 'log', expr_neg_arg)
	def expr_func_7        (self, LOG, expr_super, expr_neg_arg):                      return AST ('^', _expr_func (1, 'log', expr_neg_arg), expr_super)
	def expr_func_8        (self, LOG, expr_sub, expr_neg_arg):                        return _expr_func (1, 'log', expr_neg_arg, expr_sub)
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

	def expr_attr_1        (self, expr_attr, ATTR):                                    return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1].replace ('\\', ''))
	def expr_attr_2        (self, expr_abs):                                           return expr_abs

	def expr_abs_1         (self, LEFT, BAR1, expr_commas, RIGHT, BAR2):               return AST ('|', expr_commas)
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                            return AST ('|', expr_commas)
	def expr_abs_3         (self, expr_paren):                                         return expr_paren

	def expr_paren_1       (self, expr_parencommas):                                   return AST ('(', expr_parencommas)
	def expr_paren_2       (self, expr_frac):                                          return expr_frac

	def expr_frac_1        (self, FRAC, expr_binom1, expr_binom2):                     return AST ('/', expr_binom1.no_curlys, expr_binom2.no_curlys)
	def expr_frac_2        (self, FRAC1, expr_binom):                                  return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_binom.no_curlys)
	def expr_frac_3        (self, FRAC2):                                              return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4        (self, expr_binom):                                         return expr_binom

	def expr_binom_1       (self, BINOM, expr_subs1, expr_subs2):                      return AST ('func', 'binomial', (expr_subs1.no_curlys, expr_subs2.no_curlys))
	def expr_binom_2       (self, BINOM1, expr_subs):                                  return AST ('func', 'binomial', (_ast_from_tok_digit_or_var (BINOM1), expr_subs.no_curlys))
	def expr_binom_3       (self, BINOM2):                                             return AST ('func', 'binomial', (_ast_from_tok_digit_or_var (BINOM2), _ast_from_tok_digit_or_var (BINOM2, 3)))
	def expr_binom_4       (self, expr_subs):                                          return expr_subs

	def expr_subs_1        (self, LEFTDOT, expr_commas, RIGHT, BAR, SUB, CURLYL, subsvars, CURLYR): return _expr_subs (expr_commas, subsvars)
	def expr_subs_2        (self, expr_cases):                                         return expr_cases
	def subsvars_1         (self, SUBSTACK, CURLYL, subsvarss, CURLYR):                return subsvarss
	def subsvars_2         (self, varass):                                             return (varass,)
	def subsvarss_1        (self, subsvarsv, DBLSLASH):                                return subsvarsv
	def subsvarss_2        (self, subsvarsv):                                          return subsvarsv
	def subsvarsv_1        (self, subsvarsv, DBLSLASH, varass):                        return subsvarsv + (varass,)
	def subsvarsv_2        (self, varass):                                             return (varass,)

	def expr_cases_1       (self, BEG_CASES, casess, END_CASES):                       return AST ('piece', casess)
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
	def expr_curly_2       (self, SLASHCURLYL, expr_commas, CURLYR):                   return AST ('set', expr_commas.comma) if expr_commas.is_comma else AST ('set', (expr_commas,))
	def expr_curly_3       (self, CURLYL, expr_commas, CURLYR):                        return _expr_curly (expr_commas)
	def expr_curly_4       (self, expr_ufunc):                                         return expr_ufunc

	def expr_ufunc_1       (self, UFUNCPY, PARENL1, expr_commas1, PARENR2, PARENL3, expr_commas2, PARENR4): return _expr_ufunc (None, expr_commas1, expr_commas2)
	def expr_ufunc_2       (self, UFUNC, expr_parencommas):                            return _expr_ufunc (UFUNC, expr_parencommas)
	def expr_ufunc_4       (self, expr_term):                                          return expr_term

	def expr_term_1        (self, expr_num):                                           return expr_num
	def expr_term_2        (self, expr_var):                                           return expr_var
	def expr_term_3        (self, STR):                                                return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_4        (self, SUB):                                                return AST ('@', '_') # for last expression variable
	def expr_term_5        (self, EMPTYSET):                                           return AST.SetEmpty

	def expr_num           (self, NUM):                                                return _expr_num (NUM)
	def expr_var           (self, VAR):                                                return _expr_var (VAR)

	def expr_sub_1         (self, SUB, expr_frac):                                     return expr_frac
	def expr_sub_2         (self, SUB1):                                               return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1       (self, DBLSTAR, expr_neg_arg):                              return expr_neg_arg
	def expr_super_3       (self, CARET, expr_frac):                                   return expr_frac
	def expr_super_4       (self, CARET1):                                             return _ast_from_tok_digit_or_var (CARET1)

	def expr_neg_arg_1     (self, MINUS, expr_neg_arg):                                return _expr_neg (expr_neg_arg)
	def expr_neg_arg_2     (self, expr_diffp):                                         return expr_diffp

	def expr_parencommas_1 (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):           return expr_commas
	def expr_parencommas_2 (self, PARENL, expr_commas, PARENR):                        return expr_commas

	def varass             (self, expr_var, EQ, expr_commas):                          return (expr_var, expr_commas)

	def caret_or_dblstar_1 (self, DBLSTAR):                                            return '**'
	def caret_or_dblstar_2 (self, CARET):                                              return '^'

	#...............................................................................................
	# autocomplete means autocomplete AST tree so it can be rendered, not necessarily expression

	_AUTOCOMPLETE_SUBSTITUTE = {
		'CARET1'          : 'CARET',
		'SUB1'            : 'SUB',
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
					(self.stack [-2].red.is_attr or (self.stack [-2].red.is_var and self.stack [-2].red.var in self._USER_FUNCS)):
				return self._insert_symbol ('PARENR')

		if pos and rule [1] [pos - 1] == 'expr_commas' and rule [0] not in {'expr_abs', 'varass'}: # {'expr_abs', 'expr_func', 'expr_ufunc', 'varass'}:
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
		if not text.strip:
			return (AST.VarNull, 0, [])

		self.parse_results  = [] # [(reduction, erridx, autocomplete), ...]
		self.autocomplete   = []
		self.autocompleting = True
		self.erridx         = None

		lalr1.LALR1.parse (self, text)

		if not self.parse_results:
			return (None, 0, [])

		rated = sorted ((r is None, -e if e is not None else float ('-inf'), len (a), i, (r, e, a)) \
				for i, (r, e, a) in enumerate (self.parse_results))

		if os.environ.get ('SYMPAD_DEBUG'):
			rated = list (rated)

			print (file = sys.stderr)

			for res in rated [:32]:
				res = res [-1]
				res = (AST_MulExp.to_mul (res [0].no_curlys).flat (),) + res [1:] if isinstance (res [0], AST) else res

				print ('parse:', res, file = sys.stderr)

			if len (rated) > 32:
				print (f'... total {len (rated)}', file = sys.stderr)

			print (file = sys.stderr)

		res = next (iter (rated)) [-1]

		return (AST_MulExp.to_mul (res [0].no_curlys).flat (),) + res [1:] if isinstance (res [0], AST) else res

class sparser: # for single script
	Parser = Parser

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: # DEBUG!
# 	p = Parser ()
# 	# p.set_user_funcs ({'f': 1})
# 	# a = p.parse (r'x - {1 * 2}')
# 	# a = p.parse (r'x - {{1 * 2} * 3}')

# 	a = p.parse (r'')
# 	print (a)

# 	# a = sym.ast2spt (a)
# 	# print (a)
