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

#...............................................................................................
def _expr_comma (lhs, rhs):
	if not rhs.is_slice or rhs.step is not None or not rhs.stop or not rhs.start or not rhs.start.is_var:
		return AST.flatcat (',', lhs, rhs)

	if lhs.is_mul:
		if lhs.mul.len == 2 and lhs.mul [0].is_var_lambda and lhs.mul [1].is_var:
			return AST ('-lamb', rhs.stop, (lhs.mul [1].var, rhs.start.var))

	elif lhs.is_ass:
		if lhs.rhs.is_mul and lhs.rhs.mul.len == 2 and lhs.rhs.mul [0].is_var_lambda and lhs.rhs.mul [1].is_var:
			return AST ('=', lhs.lhs, ('-lamb', rhs.stop, (lhs.rhs.mul [1].var, rhs.start.var)))

	elif lhs.is_comma:
		for i in range (lhs.comma.len - 1, -1, -1):
			if lhs.comma [i].is_mul:
				if lhs.comma [i].mul.len == 2 and lhs.comma [i].mul [0].is_var_lambda and lhs.comma [i].mul [1].is_var:
					ast = AST ('-lamb', rhs.stop, (lhs.comma [i].mul [1].var, *(c.var for c in lhs.comma [i + 1:]), rhs.start.var))

					return AST (',', lhs.comma [:i] + (ast,)) if i else ast

			elif lhs.comma [i].is_ass:
				if lhs.comma [i].rhs.is_mul and lhs.comma [i].rhs.mul.len == 2 and lhs.comma [i].rhs.mul [0].is_var_lambda and lhs.comma [i].rhs.mul [1].is_var:
					ast = AST ('=', lhs.comma [i].lhs, ('-lamb', rhs.stop, (lhs.comma [i].rhs.mul [1].var, *(c.var for c in lhs.comma [i + 1:]), rhs.start.var)))

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
			return wrap_ass (AST ('-lamb', rhs, ()))

	elif l.is_mul:
		if l.mul.len == 2 and l.mul [0].is_var_lambda and l.mul [1].is_var:
			return wrap_ass (AST ('-lamb', rhs, (l.mul [1].var,)))

	return _ast_pre_slice (lhs, rhs)

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
				ast = wrap (AST ('-func', last.var, _ast_func_tuple_args (arg)))
			else:
				ast = wrap (AST ('-func', last.var, (arg,)))

	if arg.is_brack: # x * [y] -> x [y]
		if not arg.brack:
			raise SyntaxError ('missing index')

		ast = wrap (AST ('-idx', last, arg.brack))

	if ast:
		return wrapl (ast)

	return AST.flatcat ('*', lhs, rhs)

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('-diff', expr, 'dx')
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
					return AST ('-diff', None, tuple (ds))
				elif i == len (ns) - 2:
					return AST ('-diff', ns [-1], tuple (ds))
				else:
					return AST ('-diff', AST ('*', ns [i + 1:]), tuple (ds))

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
						tail.insert (0, AST ('-diff', ast.mul [i + 1] if i == end - 2 else AST ('*', ast.mul [i + 1 : end]), diff.dvs))

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
					return (AST ('-intg', neg (ast2), dv, *ast [3:]), ast.dv)
				elif neg.has_neg:
					return (AST ('-intg', neg (AST.One), dv, *ast [3:]), ast.dv)
				else:
					return (AST ('-intg', None, dv, *ast [3:]), ast.dv)

	elif ast.is_diff:
		ast2, neg = ast.diff._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			if ast2:
				return (AST ('-diff', neg (ast2), ast.dvs), dv)
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
			return AST ('-intg', neg (ast), dv, *from_to)
		elif neg.has_neg:
			return AST ('-intg', neg (AST.One), dv, *from_to)
		else:
			return neg (AST ('-intg', None, dv, *from_to))

	raise SyntaxError ('integration expecting a differential')

def _expr_func (iparm, *args, strip = 1): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	ast, wrap = _ast_func_reorder (args [iparm])

	return wrap (AST (*(args [:iparm] + ((_ast_func_tuple_args (ast) if args [0] == '-func' else ast._strip (strip)),) + args [iparm + 1:])))

def _expr_func_func (FUNC, args, expr_super = None):
	func = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC

	if expr_super is None:
		return _expr_func (2, '-func', func, args)
	elif expr_super.no_curlys != AST.NegOne or not AST ('-func', func, ()).is_trigh_func_noninv:
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

def _expr_ufunc (UFUNC, args, argspy = None):
	name, kw = None, None

	if argspy:
		name, kw = AST.args2kwargs (args.comma if args.is_comma else (args,))

		if len (name) != 1 or not name [0].is_str:
			raise SyntaxError ('Function() takes a single string name argument')

		args = argspy

	args, kw2 = AST.args2kwargs (args.comma if args.is_comma else (args,))

	if kw is None:
		kw = kw2
	elif kw2:
		raise SyntaxError ('keyword arguments not allowed here')

	return AST ('-ufunc', name [0].str_ if name else UFUNC.grp [0] or UFUNC.grp [1] or '', tuple (args)) + \
		((tuple (sorted (kw.items ())),) if kw else ())

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

	_USER_FUNCS = set () # set or dict of names of user functions to map to AST ('-func', ...)

	def set_user_funcs (self, user_funcs):
		self._USER_FUNCS = user_funcs

	_PARSER_TABLES = \
			b'eJztXWuP3DaW/TMLTDegBkp8Sv5mO86MsbaTsZ1gBkYQOB7PINgkDmwnO4tg/vveFx9SsUoqVXfXi2h1SaJI6fJe8hy+efXmT68ef/Xsqxd/av70X+9/+Qecwu2zJ1++htPXD18+efEMLr58+fCxnFo5Kzg/evriq+fh3IYLJS/44it8xwv6ffTkz98/fvjq' \
			b'ySu5fv4wuD5Kl9+my6/58tWzh6/+8gi+9t8oRbwg58ffvHz2d7yLF998+c2Lx1//PVyhx9cv8febR/D75PnXr//+6gnJ9A1K/e1DfPj86YtvUKqnL17/GQV/+pxC0O9fX6LvZ6SRr/CpvPYRhXz81fPnD4OW0OHl0z//5XUQ6GUQGC++ePSMZEYx/go/D59/' \
			b'jZcvvhBF4NWjdPltuhRFPHn26gl+6uXT53j+4um3T7/Ai8es5FevSaKvn1FUIJIhVn979eQxefji6ZdfomJePCUDPyYBHr74AmOOD756KR8MVkKR+a2PIX6vwxmt/Pzh169ef4XhX5N+n/ztMaqfnEDX7cBCYgB41+P/hstPv/3w6fe3Hz/9nl1/gut3bz++' \
			b'//z9h4/f/+OHnz59fvsxewyXcHpL3t7/+1fw8uPvP4frT7/9+v5juPnl/b++f/vxX+nZD3D589vP37/78JNcffzwv+mKP/zp/adP7+LVr/EqvObtD+ny8+f4sX++ffc5XP9Kb2Xn3355lwT95z9/TdJEoX/6MV7++MvnKO/Pv/30/Y8//5pFM39RFslw+fvb' \
			b'FPX0dnwNXoT7z+8/jp+F299yad/+4x/h8t1vH3/6v3Dz70/vU0x/+Pj23f+8j7efcsl+fx/f9dsvP374JX70bfT/LkWPlBzF/5Be+Vum71+iSD/8+MuHGI0PyQogT7TCuw8///w2Bv71x/fv3scbSF+ZQL9++vwhfiSaOor24ackPb10cBO/8Ik9fte8ubqx' \
			b'XePsdcMXDi+Mwx/fGH0tt3BHVx16a4xtbuz1wIHvfAgHAbrghJfk64Zfbpsr3WhwV41ZwcV1dCW35HBD4ZTjHwsOil8anFS/5mRd7oSXcNUa/nFtc9O6a3HCS7jCgCAy3POHHV6gAIZ/XH8ttyATBdXNVQehLf5fB5c+v2tXcoFuKIrGOLe9xNmo6+AqbtHh' \
			b'RvE3QJMYHFTvzLW43LQ9XXX841bge3UtTniJYpKmFYS8zm7Ddeau+HRDn9P0r7vwGL9MAok7S9fcaHHkezKkWkmkvI6u4tYmh3bocKNIxRq+r0kACE8/lr3A1Q34Ri+Wfyx83bJ+4e5Gk+ksvrqPD2x8YDT/eFYPpUeKUNs2V2g3tAzLiy4uv/NyRicMC881' \
			b'eLeSF8KtGTsFSw7dzfrtyMmu3xZ8jF7r1m8HgW6MykRLiVuEGDnYsYPLHCBXXumViACuyg2c0+2NpswGqehKtw1YGa2uVePhBF/AG5Zvgw/EHzvXI5h96PFGU+ZABIKsEVMyiMWZppcciBnfQGCXZUR8GN2Ti2UXn1wcu3TJxbNLH1xuFCVbhQJRhtQr/rE6' \
			b'SRucTO6El3jl+OdGcFAu8Upzag9B8IWUqK08EPPjlwwDELyrVQnzMJ2zjUCpnM4V/zjMEAI0ii5JjzcMZHhB0WpXqEUToFtiDY7kJPe9vBLeA3i8CukodxYHuKckp/gHkte13EOWpVfTP6Yy/hJeoHYV/1iEPQ4Dd3iJ0YeHCDEtQwncegoE5rxq28g6IVVZ' \
			b'H3CJAJ01jYlFRR+OklpurT5oGByvXMrBdOvSt4E96IVktjZeKbligfHChguCLwWpGCMEmkULRCed34J3ulrxj8W0JzSyoksUFCLBJAqaJJKIVIOaYDg3/GN9zMyKsznGoOWfxPi2Fc6wK/5BcBXYRmNbiqbpw8NruYW78ID9QoS8YQX3wQQog+UP4wtcfAHG' \
			b'ztEL3Co8IK/iFEI5jjSiF8QTijdvVk0Lhm1bMiKkLAgH5sMkYBoAPshekBYAP3oEB9Bcp5vOAIE7+PcQDsO38K/gvoP/HhWFSNUjAbcr9AvpBIjQUIKBcBAMfELMWoWh4LyCzAFfbBuQDfJtZ5vONZ1vuq7p+qaH94AcLQjSakQo/CZ+G2AO0imBXQvSt4Zi' \
			b'BrZA9ELPiGYYOwwMNxClFuLU45dRAgim8d1wDx/u4dBNjwKjX4iyb/oO0AxYF/m1h5Cu8XD4xneN75sO1NE2HUQC4tdCBMF6YFQoRjmCDAfp20KZEVI5Qq7rgXARoz3kOSBf03jUPAQFMQHZwTqgFNJJgzpVWPyEy2vMmOAT7HWFhgKHN1cYX3gAUcYTqgUf' \
			b'mxU/xZheE3PRqaOnb5C46N7jqRr4CAx81bPBWjpjyZAtBVYguyu2a8f2JKvQ2UuwNqSPVs5KPBh5ERkNXDpOCspzsgnvi77o+xUCji+FvLmyZLOB/kRzrLGSrlhHUTdDnSQ9lJQgcYdU5wRNbHcgAWzIHStOvWhySq+Kssc9SaEEcpW5z49KjDvRgGprBj3W' \
			b'DNpW2xypba5IOCovuWqjY7WRUgHmyVhRXaSoqBZRR9BCHnOIbYzZwWOUEk4hsdw/iaJapZKgQjWAeB0bKuBrDcS1pvzDpPwATlpK+1Q/o/JNV9HqOG0GVTNikhajYxCOMKoQCgnGYPxMtcyhLOOrZY7UMl21zJFapq+WOUbLXPXS+NJya+1VGxs/SBW1dHCU' \
			b'VmtDC3zLLTdXFFFswlWhLUua7Fsp80lLrBXjGltte6S2NZIRpTmwp9uDC3Z81U2uzYg47GIGLlctd0yBDrnboucs0Wvp5FKSdzjPXLVaejm0+Au9F6HaxN57aSs1fGtbyVJWQtE3L9g0V72kXM+9SJ6Ly9j1hP1OtT1lnha9JDPPibPjtNkJzHeC7txDgQ33' \
			b'nFiN9NBa4QfHKd+xd8cp2dNdD15X4A27ACha/sxVCtpgJTnu9PD6UtXAGdMx0TjGMW82aCPk3LPXCmc0zxnN2wtNHL6VeoD0fcaYcxcU5yAbypGWk5IKpc/QxN7icNdavjzC8iWN6VE8mEfV4TlHYhPNQ8G1rTY5EpvgKDYlY6bgXJV/zw2GuuaEozEGaljJ' \
			b'+D84VyMcxAgr4ghRWh28cMuDF7paYD3WlN9RqQgHFVcTHamJjKm2OVbbMHlX2xyfbWhCBFUyLGHbIZivMGMD2487qfyQXLW0cbs6V1S5ua8h/ty0gF/jMjydjOO7VSuGlr6vzfN4vpN5QthaoUj+mg72s4xese65V4ZbVr3078iUGG6hjyMyyGhV30tzAoEa' \
			b'jqzkJB962k0YQxFatVsexn9FY5Mo4ctMts7zG+RFAt6toGS1x272aHVQIDdJV8XNrq4SgVQdbdWRqTqa1JGtOpoAKcOND70XqNJcdkuDjKTE1HIXzhscZaTqgK31tNbrqpeSXixxn9W4EM3FqwOHzykZPKbWhh94Ln5tGNPatmEcHw1hOHThRq3iAC7FA7gU' \
			b'D+BSXJXSXA/jp06qYY7Bg4ednLep3+BwNGrXrbPQjrR96g0OFayd3/eu9b7PBp+dOwrQALs0dBXHstpLij6v+3FwtpLBoFKIdfaCeMjrCnL33vXhpBXO+QtKaa67oMh6U7PV/WcraVL1q0tKabamtPvvu+ZGaJwLoHgKgJIlJDWPLqeToVPLd2AhHdYT1DKe' \
			b'UF+HwW06Lb1GrWrktePX1dUwjjQVQAQ19xBrXumRT2xv64NR8aQ036lWjM8hHRsaNZstToOdo+xOyYoKCXUJoQOuDsnNVEQq1QSHGcelnWQcAUnVBWzUoT9bST82dUdXYDyouYyuueVgvNQx53SSRfpQ8BBGCstltDo8McJKpb4FdOVgfOIyibESgh/2TGA9' \
			b'39mW32vpfbV3J3R2mbpIgtRZCLXrkJd5+qLOPSXdaZq70zR3p5EWpSmV8l6Lk5J5ZWnFmdBxnqTxX9/R+geUU3sZGGnlzEMiHWdrz2EcA4ZjHPEMAJ4/7m2qzpha/7z3sdMdap2qiCYM6+MaieEaieEaiZFKh6F6BIFzwHxB8DTMT8Bbx05os7m/GaJpOCUa' \
			b'TokmdOxSIJ4aT4nPXIfC2kU0yFCGsDKa2IqJbCipsoksm4h98Qlks5LDLevVsl5tLUUdrBALr7bry0BYV6eUHKfJEG4sD+B3YUV/h5wIPnCpqsCNlM0cZzPH2Qy9NdHqro7VWsc1yzVw+IAXxKIzr7Z0RQoWBPNVfYW5RivSV4dqQ3XyHJO4klXQaUcJ11IP' \
			b'RovLqmElCmsOuOxMLNyhAjn9dvzOTkzB3C7LsbVWyNuGOSy0dg0L01cjFYzUVr0U8/6Ki5uYspSkKJXXNnCJthUnRTqjB+7dWDW4AVqjaDF8bMXGBfH7LKqaOI7oEmIiUesoSkp4Vcg2k50VboP6cv0UrNCR/ln5QwMyQYPicKnJVaBgx/ogPVih0o7nt1DD' \
			b'Yid8oiRbQnRwlTlcYg6XWcM11nCdMVxkDFcYw9W1cGktXF4KVwTE5e1waTtUGiYi3IkKiwk48QyXccYFg9F4uFgjMiy2GODCgigjrsCIlTeQVeH8NSgMqBXugQp6w6IDyK5wPj92UOEI9xbTFlgf6R+VTFrGxAbhMCWhvlHhuB0hxFEZNAGmMHDHeXLYrgrx' \
			b'VVgtsLg7INxjTz72seKwzq4FI+P2ph3uFkjbU+LeibiZJG5AiZtfNrQdIG7q2OGWtyvcnXCFe8miE+2ch/swrnBPVtwvF/dAxO0eNW6AqmgPQtz3lbbahLfhq/C1mKxvWtpREIPTV9GZdlKFd/QUHF9EzzWFA089yUC7r8LDHrfp7Hhr0R733YVrionCzUxx' \
			b'50h8De7MSdv60raQDW1vynvA0k6gtFshFs0okj1KgdusgtluvJeY4P6DtPnvinQBzpBSbnCnRofitbiXIGqAPoevxl0a8bVw7lBa2g92RR/qac9I2o9X0SPapRd3HbzhaNK2wxAOzoAGNx1e01dIGlJXK1vQGt5G2NCWtKhfjAHtp8j7TeJmmR7daK9M9IVG' \
			b'wg0nITPdOIwHvN3jXq2oLdqIEs4iQcv7R6KKcJtSwxtK4lafHb0KJcAoe4wlPIHUhOCBkFEB48wBo6JFRYvbQAuFaLEBJ2wJKlwqDuWYobP9WQfI0d0+eICeIWmmRu9dsMTOwJNTxxE7whI1gScO9eom0MNtxg/XOM55roAiLuGIKyGJux8scSyldk362xFP' \
			b'3CxEOScgQVkyMHETcNL8YR8gFbkHSEadgZP9Dw7l2o4xsZmOkYbqcnk1bYA3od1u1GTI7YgTCET1Ue5QnQVFfohGVPEsVmQTMg0rkAmirFSLw7LAq7xdU0lNlGvDqcU0VCqlQplXOAOuUQ01YJvJhrZlw91iA16hPQS3bsXdUwkDwR+u+j2JhXoGHsK7cbej' \
			b'AS5CWFxIfzE+esZIXPkGVybaFSsxKc3Cy1WGmV5wUw+xEycZ4pzCiKGYJ4loJmAUPPQMpXgKaIrXIF6fMBVbkw3jD52pfcMytNK3GF3ZWzwi1FKYNaxFVwFb2rGWmitWS4CXZOn5NWvgS+/O/tfAOMmLbe1RfvSeRaZnhI76yYB6/IXB1zA9sfRm9IBBvSea' \
			b'WkVcz77LGl7FbwaoFy+I+PGNhsA/XE5zQDuDBqLVExmI0x6UMNAB9obvzg9kO6YIecsGihBpET7QXxe+mtNFlCXSBhOGA/aAfMe8gfD2gJI/5PkHyGqQZx+AUv5DC95sJhQzr9x6ojxCJJIYxO7AIqtbYJLKInfMIpZZxE6wCCrCbi6QYw6wQh5WyCNwh03c' \
			b'YQdH4g5b5A6buMOmL+xMHMIbJdrIhVmjjPhEu7Hk6ZnlDwSq6FmBZb89xbQPRJHc86L/gCfy0JQHbcYQ7Oxy7WByF9/T7GBnsENQesYO7LQPO6QoLaOGVHtotzKD6ESzwPLJAS9IXLaxQoEM7J4tGHsywcE5YAb+1xrEKWC/Y+yfaohpt7TEIDhLW0wrjTF0' \
			b'XvE5AL8bHAn4iw00bWqhWdZIQ5/gwGuQn4uxBvnxiXZjmdMzyx8Y1A6KHkPbTubCSN+O6wN5KMpnchmgnm9d7g1Tt/iahno3A+qDsjOoZ6d9oD7FahnUuwT1bhvUi040C2xFeznUS1yWVgBcxfyK+eeA+R1jfjeF+d0WzOfwZPBOML8TzO8S5neDI2F+V8T8' \
			b'LmF+twjzO8b8roD5uRhrmB+faDeWOT2zfBpgftFjxPzkIpjfjTA/D0X5TC4D5vOty4QizBdf05jfzcD8YMgM89lpH8xPsVqG+V3C/G19A0EnmgW2or0c8yUuSzHfV8yvmH8OmN8z5vdTmN9vwXwaIs+Y3wvm94L5fcL8fnAkzO+LmN8nzO8XYX7PmN8XMD8X' \
			b'Yw3z4xPtxjKnZ5Y/MMD8oseI+clFML8fYX4eivKZXAbM51uXCUWYL76mMb+fgfnBkBnms9M+mJ8JuQjz+4T5/TbMF51oFtiK9nLMl7gsxfxup57js0F+W8H/TMGfwAIFmAB/FKwl/MdTiQLEB2UcGb1H5xWfhQLYVzwiBZDXNQpAV6EAfveuFECf4MBjChiI' \
			b'MaaA9ES7scyDgJa/kbNA2WNggcyFWUCNWvUHoTDDhUthgWCJTC5kgeBrkgX4tdtZINoysYA47cECWawWsQCpm1mAX7KBBYJONAtsRXsZC4S4LGWBvrJAZYGzYgHNLKCnWECTH562VGYB9kEZRwsLaGEBnVhgeCQW0EUW0IkF9CIW0MwCusACuRhrLBCfaDeW' \
			b'eRDQ8jcGLFD0GFkguQgL6BEL5KGIBeQysIBYIpOLWEB8TbOAnsECwZYZC7DTPiyQYrWMBXRiAb2NBUQnIrAV7eUsII+WskC7qjRQaeCsaIDHjKqpMaMojGEaMBtogH1QzpHRogyOfA40YAZHooHiYFGVBovyu3emAcM0YAo0kIuxRgPxiXZjmQcBLX9jQANF' \
			b'j5EGkovQgBnRQO6HaEAuAw2IJTK5iAbE1zQNzBgDGm2Z0QA77UMDKVbLaCANAOWXbKIB0Ylmga1oL6cBictiGmiPZzbB6cwjqHxwCnzAI4DU1AggFIIHAalsDoHiOQQ5K/AdZSQZDaRkNJBKo4HYVzwSKxRHA6k0GkgtGg2keDSQKowGGoixxgrxiXZjmQcB' \
			b'bYz4gBiKfiMxJBchhtGYoEEoIga5DMQgJsm9ITGIr2limDEmKJozIwZ22ocYUqyWEUMaE6S2jQkKOtEssBXt5cQgcVlMDDSVlUahCsz3BPB6Ddc1oniC201Y2yUoJLjrGNoQugI0CRwRLHCWh2yMHz3A8R2vN1fJsZLjOZKj5jYzPdVmhgmW28x01maG1yAe' \
			b'nZgcxV/LEEHkqKXlTKeWs9ERyVEXW850ajnTi1rONLec6ULL2UCMMTmmJ9qNZR4EtDHiOTmW/QZyzFyYHPWo8WwQCnNeuBRyDCbJRENyDL4myVHPaDyL5kzkKE57kGMWq0XkqFPjmd7WeBZ0IgJb0V5GjiEui8lx25S5SgyVGE6YGDwTw9TyN5hIPRODz4jB' \
			b'MzH4RAzsj4jBCzF4IQafiMEPjkQMvkgMPhGDX0QMnonBF4ghF2ONGOITyabZgckpPbcx5gNm8IUjMUNyEWbwI2bIQxEzBD/CDGKTTDZiBvE1zQx+BjMEe2bMwE77MEOK1TJm8IkZ/DZmEJ1oFtiK9nJmkLgsZoaJ+XOVGSoznCoz8OwKPTW7QvwgM3QZM3TM' \
			b'DF1iBvZHzCAzLbTMtNBppoXuBkdihuJMC51mWuhFMy00z7TQhZkWAzHWmCE+0W4s8yCgjVcDYij6jcSQXIQYRvMtBqGIGOQyEIOYJBONiEF8TRPDjPkW0ZwZMbDTPsSQYrWMGNJ8C71tvkXQiWaBrWgvJwaJy2JimJhkV4mhEsOpEgNPwdBTUzBwiyeehYGn' \
			b'SAw9E0OfiIH9ETHIdAwt0zF0mo7BvuKRiKE4HUOn6Rh60XQMzdMxdGE6xkCMNWKIT7QbyzwIaGPEB8RQ9BuJIbkIMYwmZQxCETHIZSAGMUkmGhGD+JomhhmTMqI5M2Jgp32IIRNyETGkSRl626SMoBPNAlvRXk4MEpfFxDAxE68SQyWGEyUGWUsZT1uJAdPm' \
			b'iojBZDP08BrEoxMTg/hD49NZKT6v+CzEwL7iEYmBvK4RAzoIMZhFa/fRJzjwmBgGYoyJIT3RbizzIKCNEc+Joew3EEPmwsTA+krEMAhFO2HJpRBDMEkmGhJD8DVJDPza7cQQzZmIQZz2IIYsVouIgTTOxMAv2UAMQSeaBbaivYwYQlwWE8Nu0/UqMVRiOBli' \
			b'4N5nM9X7jEmSe59N1vtsuPfZpN5n8UfEIL3PRnqfTep9NsMjEUOx99mk3mezqPfZcO+zKfQ+D8RYI4b4RLuxzIOANkZ8QAxFv5EYkosQw6j3eRCKiEEuAzGISTLRiBjE1zQxzOh9jubMiIGd9iGGFKtlxJB6n8223uegExHYivZyYpBHi4lh2ww+cxnc4Er0' \
			b'YCtFnA1FaB69q6dG74ISMMXyAF6dDeDVPIBXpwG84o/alWQAr5YBvDoN4GVf8UjtSsUBvDoN4NWLBvBqHsCrCwN4aVvcKMdaw1J8MpJ4dPQ8z1v8BqbopXmpFCI1LyUXaV4ajeMdhKLmJbkMzUtimdwbNi+Jr+nmpRnjeKNVs+YldtqneSnFalnzUhrHq7eN' \
			b'4w060SywFe3lzUsSl6VkobbN86tkUcniHMjCcNe0meqaBgUY9oZViqx32nDvtEm90+KPqhTSO22kd9qk3mnTDY5UpSj2TpvUO20W9U4b7p02hd7pgRhrVYr4RLuxzPmBCGij38gViisWpRCpYpFcpGIx6qMehKKKhVyGioUYJhOQKhbia7piMaOPOho1q1iw' \
			b'0z4VixSrZRWL1EdttvVRB51oFtiK9vKKhcRlMVfUyYB30eKEJbm2MsVtMwXorMwW7ZzJgdxnrab6rMGD4j5rlfVZK+6zVqnPWvxRxpI+ayV91ir1WbOveKTJgcU+a5X6rNWiPmvFfdaq0Gc9EGNtcmB8ot1Y5kFAGyM+mBxY9BsnByYXmRwofdaqxYWNVJok' \
			b'mIemSYJyGSYJimkyEWmSoPianiQ4o+86mjWbJMhO+0wSzIRcQhgq9V2rbX3XytqoF81CI0wHLWbEEeK0mDgm9r2sxFGrFocnjEVVC9wSE15MO2NuIwpLBxIFngJR4DWIRycmCvGHxqezkvsVn4UorBockSjI6xpRoKsQBb97V6KQfT/xNCaKgRhjokhPtBvL' \
			b'PAhoY8Rzoij7DUSRuTBRsL5SjWIQCnNeuBSCCCbJREOCCL4mCYJfu50gojkTQYjTHgSRxWoRQZDGmSD4JRsIIuhEs8BWtJcRQ4jLYmKoM6grMZwpMXAftp3qw8adDbkP22Z92Jb7sG3qwxZ/RAzSh22lD9umPmw7PBIxFPuwberDtov6sC33YdtCH/ZAjDVi' \
			b'iE+0G8s8CGhjxAfEUPQbiSG5CDGM+rAHoYgY5DIQg5gkE42IQXxNE8OMPuxozowY2GkfYkixWkYMqQ/bbuvDDjoRga1oLycGebSYGOoM6koMZ0oM3BlhpzojLPtBYsh6Iiz3RNjUEyH+iBikJ8JKT4RNPRG2GxyJGIo9ETb1RNhFPRGWeyJsoSdiIMYaMcQn' \
			b'2o1lHgRMVwNiKPqNxJBchBhGfRCDUEQMchmIQUySiUbEIL6miWFGH0Q0Z0YM7LQPMaRYLSOG1Adht/VBBJ1oFtiK9nJikLgsJoYTnUANyQS5oa30cCb0oO5yaUKmCDVFEYr9YO9DRhGKKUIlihB/lKWEIpRQhEoUobrBkXofihShEkWoRRShmCJamUtNX0Dr' \
			b'E56Fbgjy1oou1vohoqjajaUfxMTGq0E/RNFv7IdILtIPMSKLQSjqf5DL0P8gxslEo/4H8TXd/zCDLKJhs/4Hdtqn/yHFaln/A3e+xT6IbYQR9KJZaCsazPseJD6LCaNOrK5UcaY1Ce6ktlOd1ODBcie1zTqpLXdS29RJLf6oJiGd1FY6qW3qpGZf8Ug1iWIn' \
			b'tU2d1HZRJ7XlTmpb6KQeiLFWk4hPtBvLPAhoY8QHNYmi31iTSC5Sk+hHNYk8FNUk5DLUJMQkmWhUkxBf0zWJGZ3T0ZxZTYKd9qlJZEIuqkkkYrDbOqeDTjQLbEV7eU1C4rKYGOrE6koM50kMriViwNNWYsAk1hIx4CkQA16DeHRiYhB/aHw6K8XnFZ+FGNhX' \
			b'PCIxkNc1YkBXIQZ+967EQJ/gwGNiGIgxJob0RLuxzIOANkY8J4ay30AMmQsTA+srEcMgFOa8cCnEEEySiYbEEHxNEgO/djsxRHMmYhCnPYghi9UiYiCNMzHwSzYQQ9CJZoGtaC8jhhCXxcRQJ1ZXYrg9YuBRi/dDELZMEtjskBMFVasjWfAIJjc1gsnRQWSR' \
			b'jWByPILJpRFM4o/IQkYwORnB5NIIJqcGRyKL4ggml0YwuUUjmByPYHKFEUwDMdbIIj7RbizzIKCNER+QRdFvJIvkImQxGsE0CEVkIZeBLMQkmWhEFuJrmixmjGCK5szIgp32IYsUqzbKuztlpHFMbts4pvB+HSW3okZhDfpyn0m1nDsmdk/1gTXOZsO8A+yW' \
			b'd44scd/VB9wEB1Ofm2pj4qqEnapKWK5HFPfLw4Qp1Qcr1Qcr1Qebqg/sKx6pXWlcfcDEZFPtwS6qPdyEMa2F6gOntvS/3rYUhdRuLHd6Zlltg1alosfYqkS3mDaQEBgC9aj+gPKwP5KMMh5dCCXIc+SEIL7lKkS4nNG4NKMOEW2aNS6xU5EWJDLbWYFibuX7' \
			b'y1qXuBJBcENa2di8xLI6zSJTSIWfQoON6hMhXkNOMP4BFU0iKcC9p9z/gDhQIUvQBn6RHPTEnqrHSQ6HJYRIBoEIuowAAvgH0D8VwD+qtiLPxX8/Vfz3mwEek4yXIr+XIr+XIr9PRX4/OFKR3xeL/D4V+f2iIr/nIr9fB/j1Yn4USruxnOmZ5ZcOCvhFj7GA' \
			b'n1y4gM94Hkr3EvVVtq4eaZmFxoK8n1WK9zNK8cFCWSmenfYpxcfo7V5097HofrO1gzh8QLOwVhJY3twj8dhWZJeSOoHwxCTmCsIVhO8fhLkn10315Lp+Cwj39JhAWHpvnfTeutR7y77ikUC42HvrUu+tW9R767j31hV6b9dBOAql3VjO9MzySwcgXPQYQTi5' \
			b'lEBYtDYAYe6Zddwn62Z1yLoZHbLRQhkIs9M+IByjtzsI93NBWD6gWVgrCSwHYYnHXBCemBBcQbiC8L2DsOemDj/V1OG3NHXgAF9p6vDS1OGlqcOnpg72FY8Iwr7YU+pTW4df1NbhuafUF5o61kA4CaXdWM70zPJLcxAuewwgnLkUQDhoLQdhz40Ynhsv/KyG' \
			b'Cz+j4SJaKIGwOO0Bwil6O4Owb2eCcPiAZmGtJLAMhEM85oLwxOTb4wTh2lZ9cW3VW0HbMGibKdA2W0Db0GMCbSOgbQS0TQJtMzgSaJsiaJsE2mYRaBsGbbMO2gMx1gA8PtFuLHN6ZvkDAwAveowAnlxyAM+bpgfhMJexMgXO2dllMhGui+9paDczoD3YMYN2' \
			b'dtoH2lOUFjVJk7YZ3/klm+BddKJZYCvay+Fd4jID3getzhNTaSvMV5g/fpi3DPN2CubtFpi39Jhg3grMW4F5m2DeDo4E87YI8zbBvF0E85Zh3hZgPhdjDebjE+3GMqdnlj8wgPmixwjzyWUjzOfhCOZtBvPs7DKZCObF9zTM2xkwH+yYwTw77QPzKUrLYN4m' \
			b'mLfbYF50ollg+eQA5iUuu8L8xMTYCvMV5o8f5h3DvJuCebcF5h09Jph3AvNOYN4lmHeDI8G8K8K8SzDvFsG8Y5h3BZjPxViD+fhEu7HM6ZnlDwxgvugxwnxy2QjzeTiCeZfBPDu73A/CvPiehnk3A+aDrjOYZ6d9YD5FaRnMuwTzbhvMi040C2xFeznMS1x2' \
			b'hfmJ6awV5ivMHz/M85gTPzXmxG8Zc4JJSXDLy5gTL2NOfBpzwr7ikWC+OObEpzEnftGYE89jTnxhzMlAjDWYj0+0G8ucnln+wADmix4jzCeXjTCfhyOY9xnMs7PLZCKYF9/TMD9jZEq0Ywbz7LQPzKcoLYP5NDyFX7IJ5kUnmgW2or0c5iUuu8I8TU4FHN6+' \
			b'NctZo726551YlqK+2wH52xNC//YuV7jBPISTelbEBJgnJrZm0Y3awgb0Ps34poQOlNCBSnSAeSM70hI3RTpQiQ7UIjoIg8xVgQ8GcqytbINfRpG5fWckdgpnOeaYFejduBsLgc8G/3Fxm+SyiRgG4Wh5m4wYxNllotHaNuJ7QAz9pvVtCuSAyyqtrXEjL83X' \
			b'uGGnfda48TTSXC1mCMWpf17XbdAQp+HOii7zVW4kRokmyAV/gSvgt9P0a8gd+IK+r+BEbNE1b7ZwxTpLdEQOSmhBeCAnAWaAmfC/aYwMIT1CVl54j1BdGtqSD2mxArlzoHaqgJ1D61JI7XaH0VnwqQUyM7iMMIkZZjZEbgTHkLllFmYAw4h+BegLuLcH6E2P' \
			b'NQnwdjNexjHiVHG0yHCcCILQzfoYvU2oM1keHQDNPhCD+LI7rswDFIQSxJEhiAT4QETotyJCseh4P6AQSoCQdi4ZGhC/i/AwFxp2Kz5R4ejk8CErArVSAa44IeUPYzZhxS44AYbdreTg7h0nhrVDBoz2jkED/ICuW4846Y4XRPYuX+wIIhsBJFS9jhxESM78' \
			b'XwAF6+X3ASqE+riZFlZr9IzBqkdZGFH4rtkg0/wBSfIByI8VFRB114qKNGRtgZvuthEnoIzOUMZfVvEkIstqS/EkNPqAGzZEEMqAf4j3sPGHp1Yrj9VfrHNj/bfLV6GBf3WLaMT5Ve+MRvoAiBQRSCcEQitecNEmLhxMqydsLNpQiVZTW+MNNtTy7oXo3Y4H' \
			b'xqeFj+gxBUBB0Dpt2sAKbwyVitRe7Sm4iXKxaf1uYEogCiVTagKm7IlAldmxNtXPrE2ZeygMbSgImRx+CJ2OoEA0rlGxBf0U/JD4JwVBmCx2rWG5mTUsJUvUbq5l6aNsn92EJGCblgSE3IurHbaHKvyMe8XuswCEnRFwjd2zetNYiFJhqFtHmFDoubvCzpFX' \
			b'u9ZRBjM1dXPeYD/sDXbKHrTEMxpodoBCDzZv4YvpR89BHikAxcLPuMzTSzFnXLgxzZsjAKJNgwRuv9Po0GWZJdWudp9GnYQonTtVQKHhGTQMo6MhF/faeXQcRZaltSa1V+dR80f3AIiIWmvsUSDFJDqgWLdSTjklpJhbLpmJFGdV9thc7vA0ruq2yhuniBMS' \
			b'/1kljMneI7cYIHAFxXvFCHOL9Zml47zHI/zus7+5O27MwCGYRwwcJBm+6zarK2X4MP2uGEJLnR6gB3rH+sokmvjlaNLdM5pkSII7QRy01HHPSFJRZPGwtiGCoNWOoxByGAC5XfDoloNHf0Dw6Ct4VPBYBB7HUoM5B/Dolzd0rA4HHiBWBY8KHkvAw1bwuC3w' \
			b'AEOcRCvpxbSMHiE6HC8w3CYK4LTRk2gD3TfXN39ALniAoIfdJCBGBYBjB4CFHainBwL0ulvEAHrfGfaD3MZEu+YPrx4Q6kIGeoBoSXigKh5UPDgEHlAmPrJCwaUhgjMPAJYJB3TFgYoDt4cDlOdPtnJwaThg7QMAbsKB4xhwWXHgbHBAVxw4RRw4keGUFQcK' \
			b'OLBhv+zDYAJl4eNpN6TgRwMJIs1dIQK9fhYiKNJms7afdMKGsIf0ps2jCTWWj7GsqHFo1DgCpHDHhRTuqJDC3S1S7Ft2mIUPy0dNVny4VHyg9HaGPZC3gQ+cF0+iboEL69D4497hBa0FapcPhKx4cFl4QAnqrEck7IAHpIwTb2vA9eMpM3VYTtBcPthjbGPF' \
			b'g4vAA/J/GUOUZgACaeNcWh81lBA0pXo4K8QDV4crVjwo4gH5vawRi5fWGaGxgLBiHKijFi8ZBzBDHs2YxaOAAZTtIkBA4dBl3FXJt3hhCA3qmMULQwNMuIcfsXi0aHBBhYJWY+MhFwrqkMVLg4G+wkCFgTEMnMiIRYhlXKz23iGhtG3jIRaordMdd1kADjMe' \
			b'hD4cVGAWPjhggNNG2Nhl7rM7jiGNy9eSdQksBnvEHnMZYnVH5Yg2287jvAGD9vsd/S8ZzYTBipunnkpRY9nep/PKG6Qd2qDDbi13eBzKRAOk3XEMdaxoUtFkJzQp/C9BEyrJVDTZgCZ2JWji5qLJcQyMrGhym2hy7kjSrv0vQpK2IskWJGkn20IyFOmaN32A' \
			b'DsYNBg1GDENYYQglesKHHBwIGUIe11k+pDyoJe+V8p1PeWycHygPdLg5uM/Td0jaMVXHFI0XvH7xipMvpVxtyyk2pdaYxnRuf1QY2X21wdxo6WjYNQOw0rny2O+rWobSCKJOwLNjIBwoW+2gcLUBhILiKcPdoeZResrt0QIqWAHfSKM2c3PErDjLJPTlUvtg' \
			b'ZhrIUHuaJhJd0Tr65C2kEyaXrRTg9K4t1TZvcHsz3VO0kUjtih4oeABlDgfuVH4AH+ismzdKr8ARtEYOBi6tRQcHb4Tz1Q28E33QB27gPQiatPWzp+1YHW1s2DVgsnx3ZlxUT1nc20rh7u68S7PifVTj5oRYOMGuZ0xXaYdl2vDPdvQ9vfv3dLPlj15q8KVu' \
			b'42tlKzS/4f1UVjOjv7StWZ+70+ds4XMavwhlCTARrji8mvF12lUgNDTTapu4y9hKpIKSaPxDoraypHD6t8U/ftpS8zFe05qamINJdLdMdEjBu0kPSXPyD8uvG56RrH6JrG6TuKMdh4ri43diFOCtE39YEB/+UdGYisKair/ZExAUzhSxrhCxdmPcoECDFQ8/' \
			b'qGysRxgAZrCZekcj/rBcjAUgLAnRSlaKp+kh4CEKIaLRmqFBRYCQ1GaGM9xIXSinF7WtNqtu5bmOsOpZjSamBvj3tI+r7NP6HZJP+kMc70d/3P1T/t8UdluYTe8Z3g+vNsnTF0PDP5m2P2yaxQLw/R0UY7jaMTVDkoDUdQdpGmfEHjRd01ZVuxwk8a6Bth6K' \
			b'+PjuDrZ5e2QIRt3BJWuv7triqjn4oaiDfOTU3cq72drqwKCmm3s8OMo6RhmXY+/uMpnbE0npvuGj54bNOzy6O3379oPNX6pQzE7xIwMvS/RYiFx6YKPw7sE45nac8LEmcefJv+9PIAdQ03Y6SOZVM3K99QObT+76GxsOThGlKuPmVDCL1pflCNuMDmy6Xned' \
			b'eWBvyTyvrAZfM8amjIGNhhd0cHrYrRJ/d9kCuzUPcLAS+popNmYK01zSwY3Ju7UFzK4CLssYtrndA/vT53llZbQ1c2zKHNjBdEEHp4dSNfoWMgcaelEGwUEwt33gWJN5Xlkna/XsmkdiHjHNJR2cHkoV71vKI2joZfnENndx4PCreV5ZNbVmvjmruOaSDk4P' \
			b'u9XL3cIW97k5Jtgp5RrfzD9wFN5uAUDW7T5w1GG4YYXVGvzmDNQ3l3RwetitBr80A+W2XpyZcHTyXR758N/ZoViLtQlgY67CoXMXdPD4rt2aAA6bq2xzZAersDYcbM5Srrmkg9ODutj0gANaWlVIFzalDdeH9AH/OE4Wxyqf46HAssq0Q7d4P7jidKN3HqVz' \
			b'i8NylqFyIcvjJKzZB47r3inA6AhznnYIgTOWstlKpPndmjGOVvO6OYWDVV4alH2CKjfNKRys8t1aIG5Z5drsoHY/R/W2uecDaW6xDzZBaYz8jOLA4azQzbGEa3Y6cEbPrmGWHVu+xPZYOLT/yO3RNad2sDVKo/FP3ho4a+bEDp6ktfNEgXOb9oJrBux+0JIA' \
			b'2f+yt4zfuP7u7HbgZ/ot2cGWPrbpAfdvad2c48HW3W0cwzlat2vO8WDr7t5ocG7W7ZtzPNi6uzdMnJl1cdmCMzzYuru3gZybddvmHA+2rmveaE2TfAWqfXSQ3N2hA6qQ5qKucBlZfgAVodz+oGjygSsEgPpb3BYRZ5nwe0G7Rd+4tsDgn323a77ReBQCTDn6' \
			b'VzI41g7Wr6CkwO5AP3ly5CSUJx1JNtjyamh2IK6ala2WxStUhdWp+mxVKpwswvqA9PdmtHRXS8skkNj4yfApSpnScBdEtCgyNhPTpCBcHEvLE7AQdVdg9wR1S/S0Egc2EoOrx5XIuIQMMYjLcnDexY0dlXXkIqtM9HhNb5CSF27uFFzAz3fX/w/+3O9K'

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

		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\ne(?!g)q?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)(?!{_LTRU})|{"|".join (AST.Cmp.UNI2PY)}'),
		('IF',            r'if(?!{_LTRU})'),
		('ELSE',          r'else(?!{_LTRU})'),
		('OR',           fr'or\b|\\vee(?!{_LTRU})|{_UOR}'),
		('AND',          fr'and\b|\\wedge(?!{_LTRU})|{_UAND}'),
		('NOT',          fr'not\b|\\neg(?!{_LTRU})|{_UNOT}'),
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LTRU})'),
		('LOG',           r'log\b|\\log(?!{_LTR})'),
		('LN',            r'ln\b|\\ln(?!{_LTRU})'),

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

		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\ne(?!g)q?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)|{"|".join (AST.Cmp.UNI2PY)}'),
		('OR',           fr'or\b|\\vee|{_UOR}'),
		('AND',          fr'and\b|\\wedge|{_UAND}'),
		('NOT',          fr'not\b|\\neg|{_UNOT}'),
		('SQRT',          r'sqrt\b|\\sqrt'),
		('LOG',           r'log\b|\\log'),
		('LN',            r'ln\b|\\ln'),

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
	def expr_colon_2       (self, expr, COLON):                                        return AST ('-slice', expr, False, None)
	def expr_colon_3       (self, COLON, expr_colon):                                  return _ast_pre_slice (False, expr_colon)
	def expr_colon_4       (self, COLON):                                              return AST ('-slice', False, False, None)
	def expr_colon_5       (self, expr):                                               return expr

	def expr               (self, expr_ass):                                           return expr_ass

	def expr_ass_1         (self, expr_mapsto1, EQ, expr_mapsto2):                     return AST ('=', expr_mapsto1, expr_mapsto2)
	def expr_ass_2         (self, expr_mapsto):                                        return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr_colon):                     return _expr_mapsto (expr_paren.strip, expr_colon)
	def expr_mapsto_2      (self, expr_piece):                                         return expr_piece

	def expr_piece_1       (self, expr_or, IF, expr_ass, ELSE, expr_mapsto):           return _expr_piece (expr_or, expr_ass, expr_mapsto)
	def expr_piece_2       (self, expr_or, IF, expr_ass):                              return AST ('-piece', ((expr_or, expr_ass),))
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

	def expr_lim_1         (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                          return AST ('-lim', expr_neg, expr_var, expr)
	def expr_lim_2         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):  return AST ('-lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg): return AST ('-lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                        return expr_sum

	def expr_sum_1         (self, SUM, SUB, CURLYL, varass, CURLYR, expr_super, expr_neg):                          return AST ('-sum', expr_neg, varass [0], varass [1], expr_super)
	def expr_sum_2         (self, expr_diffp):                                                                      return expr_diffp

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

	def expr_attr_1        (self, expr_attr, ATTR):                                    return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1].replace ('\\', ''))
	def expr_attr_2        (self, expr_abs):                                           return expr_abs

	def expr_abs_1         (self, LEFT, BAR1, expr_commas, RIGHT, BAR2):               return AST ('|', expr_commas)
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                            return AST ('|', expr_commas)
	def expr_abs_3         (self, expr_paren):                                         return expr_paren

	def expr_paren_1       (self, expr_pcommas):                                       return AST ('(', expr_pcommas)
	def expr_paren_2       (self, expr_frac):                                          return expr_frac

	def expr_frac_1        (self, FRAC, expr_binom1, expr_binom2):                     return AST ('/', expr_binom1.no_curlys, expr_binom2.no_curlys)
	def expr_frac_2        (self, FRAC1, expr_binom):                                  return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_binom.no_curlys)
	def expr_frac_3        (self, FRAC2):                                              return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4        (self, expr_binom):                                         return expr_binom

	def expr_binom_1       (self, BINOM, expr_subs1, expr_subs2):                      return AST ('-func', 'binomial', (expr_subs1.no_curlys, expr_subs2.no_curlys))
	def expr_binom_2       (self, BINOM1, expr_subs):                                  return AST ('-func', 'binomial', (_ast_from_tok_digit_or_var (BINOM1), expr_subs.no_curlys))
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

	def expr_cases_1       (self, BEG_CASES, casess, END_CASES):                       return AST ('-piece', casess)
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
	def expr_curly_2       (self, SLASHCURLYL, expr_commas, CURLYR):                   return AST ('-set', expr_commas.comma) if expr_commas.is_comma else AST ('-set', (expr_commas,))
	def expr_curly_3       (self, CURLYL, expr_commas, CURLYR):                        return _expr_curly (expr_commas)
	def expr_curly_4       (self, expr_ufunc):                                         return expr_ufunc

	def expr_ufunc_1       (self, UFUNCPY, expr_pcommas1, expr_pcommas2):              return _expr_ufunc (None, expr_pcommas1, expr_pcommas2)
	def expr_ufunc_2       (self, UFUNC, expr_pcommas):                                return _expr_ufunc (UFUNC, expr_pcommas)
	def expr_ufunc_4       (self, expr_term):                                          return expr_term

	def expr_term_1        (self, expr_num):                                           return expr_num
	def expr_term_2        (self, expr_var):                                           return expr_var
	def expr_term_3        (self, STR):                                                return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1].replace ('\\}', '}')))
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

	def expr_pcommas_1     (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):           return expr_commas
	def expr_pcommas_2     (self, PARENL, expr_commas, PARENR):                        return expr_commas

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
			return (AST_MulExp.to_mul (res [0].no_curlys).flat (),) + res [1:] if isinstance (res [0], AST) else res

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
				res = postprocess (res [-1])
				print ('parse:', res, file = sys.stderr)

			if len (rated) > 32:
				print (f'... total {len (rated)}', file = sys.stderr)

			print (file = sys.stderr)

		res = next (iter (rated)) [-1]

		return postprocess (res)

class sparser: # for single script
	Parser = Parser

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: # DEBUG!
# 	p = Parser ()

# 	# p.set_quick (True)
# 	# print (p.tokenize (r"""{\partial x : Sum (\left|\left|dz\right|\right|, (x, lambda x, y, z: 1e100 : \partial !, {\emptyset&&0&&None} / {-1.0 : a,"str" : False,1e100 : True})),.1 : \sqrt[\partial ' if \frac1xyzd]Sum (\fracpartialx1, (x, xyzd / "str", Sum (-1, (x, partialx, \partial ))))}'''"""))

# 	a = p.parse (r'?(x)')
# 	print (a)

# 	# a = sym.ast2spt (a)
# 	# print (a)
