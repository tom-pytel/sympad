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

	if ast.is_fact:
		ast2, wrap2 = ast.fact, lambda a: AST ('!', a)
	elif ast.is_pow:
		ast2, wrap2 = ast.base, lambda a: AST ('^', a, ast.exp)
	elif ast.is_attr:
		ast2, wrap2 = ast.obj, lambda a: AST ('.', a, *ast [2:])

	if wrap2:
		ast3, wrap3 = _ast_func_reorder (ast2)

		if ast3.is_paren or ast3.is_brack:
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

def _expr_mul (expr): # ONLY FOR CONSISTENCY! pull negative(s) out of first term of nested curly/multiplication
	mcs = lambda ast: ast
	ast = expr
	mul = False

	while 1:
		if ast.is_curly:
			mcs = lambda ast, mcs = mcs: mcs (AST ('{', ast))
			ast = ast.curly

			continue

		elif ast.is_mul or ast.is_mulexp:
			mcs = lambda ast, mcs = mcs, op = ast.op, mul = ast.mul: mcs (AST (op, (ast,) + mul [1:]))
			ast = ast.mul [0]
			mul = True

			continue

		elif ast.is_minus:
			mcs = lambda ast, mcs = mcs: AST ('-', mcs (ast))
			ast = ast.minus

			continue

		elif ast.is_num_neg:
			if mul:
				return AST ('-', mcs (ast.neg ()))

		break

	if mul:
		return mcs (ast)

	return expr

def _expr_neg (expr):
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

		if last.is_num_neg: # really silly, trying to index negative number, will fail but rewrite to neg of idx of pos number for consistency of parsing
			ast = AST ('-', wrap (AST ('idx', last.neg (), arg.brack)))
		else:
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
					return AST ('diff', _expr_mul (ns [-1]), tuple (ds))
				else:
					return AST ('diff', _expr_mul (AST ('*', ns [i + 1:])), tuple (ds))

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
						tail.insert (0, AST ('diff', _expr_mul (ast.mul [i + 1] if i == end - 2 else AST ('*', ast.mul [i + 1 : end])), diff.dvs))

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
		ast2, neg = ast.add [-1]._strip_minus (retneg = True)
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

def _expr_func_func (FUNC, expr_neg_func, expr_super = None):
	func = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC

	if expr_super is None:
		return _expr_func (2, 'func', func, expr_neg_func)
	elif expr_super.no_curlys != AST.NegOne or not AST ('func', func, ()).is_trigh_func_noninv:
		return AST ('^', _expr_func_func (FUNC, expr_neg_func), expr_super)
	else:
		return _expr_func_func (f'a{func}', expr_neg_func)

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

def _expr_ufunc (UFUNC, args):
	args, kw = AST.args2kwargs (args.comma if args.is_comma else (args,))

	if any (not a.is_var for a in args):
		raise SyntaxError ('undefined functions only take variables')

	return AST ('ufunc', UFUNC.grp [0] or UFUNC.grp [1] or '', tuple (a.var for a in args), tuple (kw.items ()))

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

	return AST ('@', var + '_prime' * len (VAR.grp [4]))

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
			b'eJztXWuP3DaW/TMLjBtQAeJb8jfHcWaNtZ1s7Ax2YASB4/EMgk3iwHaysxjsf1/eB59SVUvqdlV1NdHqkkRR0tW95DkkLx8PXv/p3979+rc/dX96/PWzr1/4/bMnX73yu28effvkxTN/8NW3jx7zTvBe+v0XT198/TzsRTiQ/IAvv4ZnvMDfL578+YfHj14+' \
			b'ecnHzx+F0C/S4V/S4Td0+PLZo5f//oV/23+AFPEAgx9/9+2zv8JZPPjuq+9egJgvX30Lv9994X+fPP/m1V9fPkFJvgNZ//IILj5/+uI7kOXpi1d/BnGfPsc78Pc/v4XYz1APX8NVfuwXeOfjr58/fxR0AwHfPv3zv78KYnwbxISDL794hpKCGP/pfx49/wYO' \
			b'X3zJnw9HX6TDv6RD/vwnz14+gec8/cvTL+HgMan05SuU5Jtn+An+48LX/NfLJ48xwpdPv/oKFPLiKZrzMb740Ysv4Yvhwtff8ouCTUBUeupj/12vwh5s+vzRNy9ffQ33v0K9Pvmvx6BsDPI6FoU9WPH+WY//wx9+/P3Hj3+8+fDxj+z4oz9+++bDu08/vP/w' \
			b'w99+/Pnjpzcfssv+0O/eYLR3//zNR/npj1/C8cfff3v3IZz8+u4fP/z991/fpos/+sNf3nz64e37n/now/v/SUf05o/vPn58G49+i0fhMW9+TIefPsW3/f3N20/h+Dd8KgUXAkRBf/4pHv7066d/hONffv/5h59++S37tHT4979nHxYO/3iTPjc9HR4DB+H8' \
			b'07sP9bVw+nsu4Ju//S0cvv39w8//G07++fFd+rgfP7x5+9/v4unHXLI/3sVn/f7rT+9/jS99E+O/TZ+Heo3iv0+P/D1T8a9RpB9/+vV9/Iz3SfFenqj4n969fRdPfCLKJPjt46f38anRnFGW9z8ncd++/+WXN8XJxz99371+sDOms/KqowMFB1rBj+60uOJT' \
			b'f4ZHBn46DLgqAuhMh/v8dROC4BBj7WgvuweyU6bbiU4N/uAqhHJYDNg5OJCafowPkPYqD5JuEmRUHgSH/khI+jGDfwEJ7s/gEL7a/9sOXke3GTgAAQT9WArGb0I1CX/Bv1go+L8KIUN+NvIegkASAZ8sBv5k3V+FUApLATuJNwgvFEjoFW3JBgJ0g/oQln4M' \
			b'yDBccRAc+iM0XOefQ6LwaTjOwgXtdqgCif/KhssSDuC5HE4v8cJxIEVS+FEjf5TrYyiHjSlaXwbsJKYEBe/BFylFP9rfaeQVB+0UGQgSjIsXIB3QBd3Tj3VXfOqtBEdj98DbHvVP3+4DTHZiaQcB8KbBJz0f19AXxNNJUDBWGS6np9Wdano6jYGfngXp6Wlx' \
			b'006NmWgp+bIQVYCqA3Qe4FObHFgEMLMugtPpTqHmfEJ5IMfOGxIMq7wB4GZvX3/CaW0+BiCMN9+yiN7kZcSdwvQPyd911oTE6i9g0heOMxlkTO1ztM7yGlyM4SlEU4hJIYZCbAqxFOJCyE6g4qUPl/hiryP8MX2UNgaJPAgO4VM0/ewY6fgQjgSl9PDNcDch' \
			b'c89ZgL4G30Qf7Z+F6Zw/CpI92giUis8UPf1YyIOUgwQdoh4BigMS0yf6MAoJpzv83oFuNJBGOj2EtJMHc4A/R+lH+vFJ6orPfRZF2Xr68UbeSRIJrC9RJJ8IHwBEEFj4M0tgCrjSR84IKcboACsIx6RF+II+xlCd4nQd1OqC9nzgA5vyL57GV/szS+gILDOG' \
			b'I9XzEYkLByocUHTINqKb6JXDc91KUACB+kA/BlIVJ9kBD0Fg/zHEY143mAJjsvZfJjFRSUk/RscMKyUeghYH+sl4e2Do145+kN6ITfwZHMKRDRev+NSfhQukJJ/+nCBF22AKkMGgUgw8wMQHwNcZfIBx4QJG5aBwl6KPBoTyN/pCyuseYvpzjdb0EOwzjU8F' \
			b'HhW8Nb2ORyAiL8UgusGDQO9Jrzf+3/p/5/89KvQjJDiDxGngHOIpTCa+JOFTlI/rED98lhf+cPQP7f2b/OYt5u2pusFvuhtMN9hucN0AYON5wV8UXiDhJRKetoVPi5Achs7nQuFlFF5IKBb5jANIAgjlc6rHGniTjyYwnpfe77w8wgskvEQCRPIPGvtu9GUK' \
			b'kBdeprrRdKOFTOizh8eC0YfozvnNdM52znXO8/HYDb0XBb5nhPzpAcD6JC19Gc8nbABQaz11AuLa0dN35+3oZOf8+wXcKKAs5U0JaRle7YO8NN93D3ooPLx+4A0CKc8bBXbeKsJb6oHmq6COKyzS4W7Aqz7Y0rmDXbPhyWw4kpUE7qF8RuYZyKbw/WDMQXK0' \
			b'nqw5ULlROrI8BYpwM1rrqmXUszEyapXs59hUA+9H3ku2nUHTFSpm5ZJW5/RJeoz6K/SW6WpOUawfL6MZSERjTyWACzqixA1JC1Ui8fxIUki2lNTHfCmBs2AT4Ftb/j2b/AsWaQY5I4M8ECGb6pZTzsswglF8RGILakIFRXWwGsLX51/svzJ+0Qm/pEgleco4' \
			b'Pi8CIfZUVg9lBIXnqvOq6HxNtbMtiR8xiSvBFSsupuA5llOGhkVnZChfiaIyHFSMNXyJP4VaMdSXoR7sDdTMcUxzmGaOczKHbeY4J3O4Zo6zMceDIVTFFbWqChEKX4IaVBvNn4upBDVtQyU9lMgstZrK0LiquNWNr3NzqWGL6tZaelYG1WwtruKPaJ5WGeTK' \
			b'oOSWY8l+HqHY0TNQU/JIlcVR8GXJiV5yqg9tjew7GBnfenY4cK1mDO0r9DY9huZpfjrGunfqfzBqUosjZToq0UJeg8zW2jEO6c5xknKU8BylLMfJeOiZZzl5C8ZuQ6na0mVLqdTh2eiRC14OL4aPlRept9fQMQK/nXKmE/fq2ymjWQItS05rJ+dVEDLihaqC' \
			b'8o3lfKPuVTJgNym6uPPvJecMoYJRgaQo0UimQCljPwlJHSRk6/Jwyqqu/1RJXVKaIU7akm3BANj5xO+bxo/RyiNamj+xK79H9GnV/bOxiNeCpM5szS7nZBfdMsp5GcQfN4Ocj0Gwn60M3Told+v0+2aBI2YJiRpHbbXeRrdQ1TaYpk/x5plO7dAtOFRSMIs1' \
			b'E9+CoiUWuI7Vt5kq+/A22uNO09k4BgBlL4TeN7zhex4MAc0HlOWb8beYQ/WkcdIwuzG4CZ5b3KmZMbq7BSWWpuU1iR7LAdABjZI3j83Cnh2474N6dfC7DcGdR02dg6EnUD4ZHD9IcNpvVlhgBaGC/qmlq6nrGt8y8kLTzIxmdNPMHs2YpplZ8NEE4CPtBDHC' \
			b'a+y30Srx51SFHLFE1FIt5edRNG0kbWjMrEbAZCn3VAnQ10tynyc58b07hrf5npUiBNBwvVMXB4WJPZAk9UCS1ANJYslb0LnhOqklXMAeFpdo2NfQmwodL0Pr/3pWjOT65o8/Fvm71I3qEjP5g5FbdRC3L/lL4RPFObCM5O6akmlEXTqNONHg6jgOR8vtWdZc' \
			b'epqy9tK/0MmWa46Ua7jx3A4Xn6ZUS1PHmuekp8oi912LXcth3kSoO13h7Luw8+ZQ7NtUV+TmVuQbauN9z8aeXiJFrmayFe8MmQz0rbh/j7oK/U5UmqQMek3wKewkmRiUTnt6uKWnKb6VJw4BlyyFU3MEtji1OV2OWw+kZiwqdDS9H7H/lmJ0DDNdyiGgowqe' \
			b'c8kec/TgNmg8gY2Gli+OPP0E0clA/DE4zgwiMIcNnUVCNlHMNHPt8BCqKFRRKLJR4DbKca3591xsD9IqGsivaCC/ohH4aC5DbVz32SPllSDv8ywE6IpTrTvTdQ2xglvLHBXKHZUs3Ei6oyZjgYHChJssl8Ut5TrstfE9TjiAeZG7+cue91Tts4Svju6xhK+W' \
			b'ENkRZFt+uYp1Qc11QR36CVItRFMtRFMtRIfah27V+uNU6y2qnlJMYEjN1cHUR5OsCd+neS4W2BsRPeV6v1PckZEd3evgVvY+400E8JgC9VUoD19uoxXmBcN5wYSSP+UFQ3nBUF6gHYWCbIYtYDiPG1KqIaWaVmA98gzZqPp6agbKEq1weSZ2AlQxNMDChpnm' \
			b'LbRCeoFhKu3Ig/BlljOWpYxlKWNB9C6a3La+YkFjhujfv8AxQuGeZpd7IGimclSoa0qLJdkBteQ/1SEL0rifOBVU0ORAPIytdALeAPOSwaRkMB9ZTLRebQOl1YGeObABmMYdW2Lg/ch0TpOaoTBjM000zdi0kXI33BNSkeTUI/OaA8xn1lOyw73AGjsosu9e' \
			b'97gKmcZ2fZizfcTPU0gjyFtQo5D4YRbkVGGIIxEmkSdL7sAa1ABAWstVUyvfoNrHeYtxXXGk78TvHzNStOSNQs+UoSwHFW9YoQYWiYH1WoCLYYY2mJ4N5maDOapggiqYrwkmaYPJymC2LpgvDybLgzngYP43SC6wxBHwPUwLDXMRwwS4YDAgUpjEEGYwBN6E' \
			b'Wj7MuwddtaA3E4wZ7GGlM68pGG/tywYSvHEwshCGRwGBQ9UPRibAoEMYOAoahoFsMHRQQbkBFovzYdCqDNNCQSuzhlQFi/X5Yxh0Cp0toKMFuI+hx6gbvDFpCVZYEBRX/utwDTtY+w1X8ut2A6yU1sMqoD2sdTd0uJoalFVonUJY/BIW5oMTgSvI9bhYYYfL' \
			b'bA64dik8AldghZX0JKyOCS+BxeAE3OXTxm6AUAkr2ElYaBAfK0ESfD0udwrL58EycSCCv8NrcOdghUYQFFars7jspsCV+3CFOlgBjpaWxCXkcNXWcaTP8slk5+2wc4Zlh2UGR/wQWLwS/n1sCyIKWuoP11DFZSNBQL8fQKoe7u9xZUKJa0viOo74IQJXd6Sl' \
			b'SEFG0InPCTufn3c+iewGEB5fgPqBpyrLi7/CCawXCVLCtwpeQhPk8ucOwuBWspK/CosLOtjDGrP+KQ5i+pc5VCmvUug0SQAwhCsOwhK68HlQLN1Z+B4UEKWHeGAen1J2Dp40fg8gAFm/yPZif84PkEZQlSBABxQQJRDY28QCn3Bz8JyBBjOFB6gQXwsRx4IH' \
			b'83kgAqaLm8DEsAAqDGjW1OhgluCD6TifmRmUMAknzBxSmM+PFSifsrinvznEmMEMswg1jooYnxEzhhncMEuQo/uXfgjsYh4Cv7jR78z/YcF4L5zEKilVg7FCTcWpKbSAgyGrGFfV8cNgQ8XApZCjM9TJSn3zCCRqEPLJnNu1g68jwyRsAnBc/qOSZ2p8UGUx' \
			b'LhbzAnblA9nJoxw73xQdcrhaPFfjQJwDHNcH8E4txzwoP0LZscA+fz/0E9qMgT3joE8F0FyyFg8h3SzGRFvhomZs7Ct8hPYVneGkoJIU7EqopCzDWAn50ycw3DFiwrG3MO4IN6Hm0BPa4B4yQ98TfIqEoBQtbhFO8Z4JnkIoAyo+B1F0NbCiHGAj2OfgSrKl' \
			b'/wnYspDK1nKHrSet2HiY4XD99OJNkFzqIALsEVdsN4jZrDwRYgzxPQHGg3qtzh6GwB4O9+E7mXgpxAfzZkAfLLgY7jGZJbwvPh48RuvBn1Jcwn9OcXvwnwUOHICRIZvT+zMuiFJFTiA2sPIhkDSRAsDZQ0zvPp8/BPLyefShVw6whZqwRb+i/HnHSIIYwoSG' \
			b'32UUoW9IE40ijkQRgihC1BQBXy+WlKgh3QtmBsHMIJgYRCIGUWyJGMQsMYhEDKIj/F/PC4JoQVSskIsxYQQKVrYWON1i6DuZCbCgKfdExRRhqrC83B6JoIgxsEKZAlhSnYvtotr3wf+qEn54WA7/bKfl8C9K+BdJxE3YLyrsF4egn9USoF8Q8osa+CnaQdif' \
			b'QXu9vanhplB/Mpxv1YALwnhNGK8n1QC9COA1RQRbawZ4zQCvE8DrYksAr2cBXieA31bo1wTuVXtKIcIE3CkYW9/nNwR3XRbzZ+NBOijOCdVJP4zpxfVMjQzrLGMhsIux9sG6XgXr/LAc1tk6y2Fdl7Cuk4ibYF1XsK4PwTqrJcC6JljXNaxzOthamjcN3xu+' \
			b'32V8t4TvdoLvdhG+W4ooeQ8p3jK+24TvttgSvttZfLcJ3ze1luPHaNwV+J6LMMF3Cla2FjbdYmiX4/tsvNFU54zveZm9uJ6pkfGdZdS5wC7G2ofvdhW+B+1m+M7WWY7vtsR3m0TchO+2wnd7CN9ZLQHfLeG7rfGdom3Gd9vwveH7XcZ3R/g+6Q9B/str8d1R' \
			b'ROrJSfjOjk98MuO7K7aE724W31O3CYqwGt8d4bur8D0XYYLvFKxsLWy6xZA8Ob7PxhtNdc747jJ8L65namR8Zxl1LnA82ovvbhW+88NyfGfrLMd3V+J7JuImfHcVvrtD+M5qCfjuCN9dje8UbTO+u6W+20tA+b4B/eUC/UhAP06AfsyAXhDW424O7ikGWnxk' \
			b'uB8Z7scE92OxJbgfZ+F+THA/boL7keB+rOA+F2EC9xSsbC1scZchkXLEn42HCSI/Z8QfM8QvrmeaZMRnMXUus4ux9iH+uArx+WE54rOBliP+WCL+mETchPhjhfjjIcRntQTEHwnxxxrxKdpmxB8a4jfEvwTEl+R+lRP3q8x9r5J66Egxj/jQGY09sJI9sJI9' \
			b'sDJ5YClW3CLiy1kPrEweWIqwFvEleV9l5X0tRKgRn4OVrYUt7jIkUob48/FgfvjinBBfZh1wyuuZJgnxg5g6l9nFWHsQX65yvYaHZYgfDLQY8WXpek3CbkN8Wble5SHXa1ALI74k16usXa8cbTPijw3xG+JfBOJLQnw5Qfx8fAucGIo1i/gcHVK3ZMSXjPgy' \
			b'Ib4stoT4s8NgcKAKI77chPiSEF9WiJ+LMEF8Cla2Fra4y5BIOeLPxgPEL84Z8WWG+MX1TJOM+CymzmV2MdY+xJerED9YIEN8NtByxJcl4ssk4ibElxXiy0OIz2oJiC8J8WWN+BRtM+KL/jy65Lf++A37bwv7qSOOnHTEkXlHHDgxFCtgPxxDgtaJATTdxKHI' \
			b'ANwpR6ZOORQrbokBZjvlyNQpZ1tPfEmdcmTVKacQYcIAFKxsLWxxlwmXCxKYjQokUJwzCWRdc8rrmTKZBFjSQmwXY+0jgVVdc8LDchJgGy0ngbJrThJ2IwlUXXPkoa45QS2BBKhrjqy75nC07SSAwzyxcynDukNAFzWOA4LbgLD74JWxMuKgY3zThF8RlxiL' \
			b'sDihQ36H/Dt2J9pwxOuZjFFrhNgI8ZYIUVHzl5o0f6m8+UtR85fKmr8QNi3tiBAhPXMjmOJGMMWNYCo1glGsuEVCVLONYCo1gqlNjWCKGsFU1QhWiFATIgcrWwtb3GXC5ZwQ56P6lFGeEyGqrB2svJ4pkwgxSKpzsV2MtYcQ1ap2sPCwjBCDjRYToirbwZKw' \
			b'2whRVe1g6lA7WFALE6KidjBVt4NxtO2EOB161kigkcCdJgFDJDCZ0EHlMzrAiaFYkQQMkYBJJGDoJg5FEjBMAiaRgCm2RAKzkz6oNOuD2jQODT8M81dJArkIExKgYGVTHEhMteQmXC9YwMxsyALFObOAyViguJ5pk1mARdW53C7G2scCZhUL8MNyFmAjLWcB' \
			b'U7KASSJuYgFTsYA5xAKslsAChljA1CxA0bazwIEhaY0FGgvcRRagQQxqMohB5YMYcAYtihVZwBILJO+IojPBocgCPKBBpQENFCtuiQVmBzSoNKBBbRrQoGhAg6oGNBQiTFiAgitJa8FNPMpJYDbqaKpzJoFsWEN5PVMmkwBLqnOxXYy1jwRWDWsID8tJgG20' \
			b'nATKYQ1J2I0kUA1rUIeGNQS1BBKgYQ2qHtbA0baTwIFxa40EGgncRRKgkQ7TmR9VPtIBTgzFiiTgiARcIgFHN3EokgCPelBp1APFilsigdlRD9lkkWrTqAdFox5UNeqhEGFCAhTMGXLPhiRARzkJzEYFEijOmQSysQ/l9UyZTAIsqc7Fjkd7SWDV2IfwsJwE' \
			b'2EbLSaAc+6AyETeRQDX2QR0a+xDUEkiAxj6oeuwDR9tOAgcGtzUSaCRwF0lgIBIYJiQw5CQwEAlkg97gGOB+SCRAEQSHIgkMTAJDIoGh2BIJDLMkMCQSGDaRwEAkMFQkkIswIQEKVrYWtrjLhMsFCcxGBRIozpkEhowEiuuZMpkEWFKdi+1irH0kMKwiAX5Y' \
			b'TgJso+UkMJQkkD5kGwkMFQkcmpI0qCWQAM1MSi/PSYAubSeBxSPgGgk0ErgTJKDJM6wnnmGde4Y1eYZ15hnW5BnWyTMMKZY9w5o9w5o9wzp5hilW3CIJ6FnPsE6eYb3JM6zJM6wrz3AhQk0CHKxsLWxxlwmXcxKYj+pTRnlOJKAzz3B5PVMmkUCQVOdiuxhr' \
			b'DwnoVZ7h8LCMBIKNFpOALj3DSdhtJKArz7A+5BkOamES0OQZ1rVnmKNtJ4HpoLj+fvCAmFLB0mlKGx3cDTpQ1HNWTXrOQokw7zyrqPOsyjrPKuo8q1LnWcU3cShWC7jzrEqdZylW3FK1YLbzrEqdZ9WmzrOKOs+qqvOsUEMmw6ReQMHK1tLm20AdaDkus8Kg' \
			b'qXYwdwPWDopzrh1kfWjL65lOuXbA8uaxrIux9tUOVvWhDQ/LawdsquW1g7IPbRJ2Y+2g6kOrDvWhDWoJtQPqQ6vqPrQcbTsxTMfONWJoxHAZxKDJbawnbuMBk15WVSDPsc48x5o8xzp5jjWdCQ7FqgJ7jnXyHFOsuKWqwqznWCfPsd7kOdbkOdaV57gQYVJV' \
			b'oGBla2HzbaAeRBw38IKhCsPcDVhhKM65wpD5j8vrmUq5wsDy6lx4F2PtqzCs8h+Hh+UVBrbU8gpD6T9Owm6sMFT+Y33IfxzUEioM5D/Wtf+Yo23mBdkG2N1Wq5FXFyq7scLtsoLezwwwQu76AXfkT5YTf7LM/cmS/Mky8ydL8ifL5E+GtM7+ZMn+ZMn+ZJn8' \
			b'yRQrbmnA3aw/WSZ/stzkT5bkT5aVP7kQYTLgjoKVrYUt7jLhcjHgbjbqaKpzHnDH/mTpYU72PPCuiJcplQfescQ6Fz8e7R14t8qvHB6WD7xjWy0feFf6lWUm4hZykJVfWR7yK0sjomqYICT5lqUNSTMfgEdRt5PEgXUWG0m0KsMdrDLAOoz+obgcY0EKps9I' \
			b'AU4MxQqkAMewcmQfSQGWYuqJFHDvv4MeQuFMChQrbmmNyX6OFCCUSYEirCUFXmcSdjkpFCJMlp1kgW0tbHGXCZdzUpiPCotUFudECqQlIoPyeqZMIoMgqc7FdjHWHjIg9S8lg/CwjAyCjRaTAUqfyCAJu40MSAWJDOiD9pBBUAsTAQrOj8hJgKNtJ4E28riR' \
			b'wIWRAA06M5NBZyYfdGZo0JnJBp0ZGnRm0qAzSIo86MzwoDPDg85MGnRGseKWSGB20JlJg87MpkFnhgadmWrQWSHChAQoWNla2OIuEy4XJDAbdazPmQSyMWfl9UyZTAIsqc7FdjHWPhJYNeYsPCwnAbbRchIox5wlYTeSQDXmzBwacxbUEkiAxpyZeswZR9tO' \
			b'Andx5LFFHhgaFdxdKoC089npQJIbQU7cCDL3IUjyIcjMhyDJh5DPzUdnIuzhW9iHIJMPga7GLTUUzfoQZPIhyE0+BEk+BHgD8AHiGBia3jSyFEGASZMRvVbZWuziE0w8ypuMZqOOpjrnJqPMj1Bez9TKTUV0ikaNJy7G2tdUtMqPEB6WNxWxtZY3FZV+hCTs' \
			b'xqYii62iZXPRIV9CUE1oKrLcVFSRA0fbTg5tQHKjhQurIRAlmAklmJwSDFGCySjBECWYRAmGzgSHYg2BKcEkSqBYcUs1hFlKMIkSzCZKMEQJpnIrFyJMaggUrGwtbHFXOsprCLNRR1Odcw0hI4LyeqZMriGwpDoX28VY+2oIq4ggPCyvIbCNltcQSiJIwm6s' \
			b'IVQOZXOIBIJaQg2BSMDUJMDRtpNAG5DcSODCSIDGopnJWDSTj0UzNBYtX4DN0Fg0k8aicQTBoUgCPBbNpLFoZii2RAKzY9FMGotmNo1FMzQWzVRj0QoRJiRAwcrWwhZ3mXC5IIHZqEACxTmTQDYWrbyeKZNJgCXVudguxtpHAqvGooWH5STANlpOAuVYtCTs' \
			b'RhKoxqKZQ2PRgloCCdBYNFOPReNo20mgDUhuJLCdBKivyPHIQBwgBFuRgs2JYSRiGCfEMObEMBIxjBkxjEQMYyIGiic4FIlhZGIYEzGMxZaIYZwlhjERw7iJGEYihrEihlyECTFQsLK1sMVdJlwuiGE2KhBDcc7EMGbEUFzPlMnEwJLqXGwXY+0jhnEVMfDD' \
			b'cmJgGy0nhrEkhjGJGJ+2nh7Gih7GQ/TAL+Gvl5QEBn5KYAhMDy6TbztPHBizbLrLWcvnqAv5XCIjnKpaAK3F0M6srhuBQEygJ0ygcybYuzozdC5n9NeM/prRXyf0p1hxS0MOavSHtKQT+OtN4L/jLkS6Qn9KbOl/OuyApFO2FjhJbkiofGzybDwYahBOIFHs' \
			b'cPZ+7mwV4R+koDgoDyQinfUh4su4ZifLrIkBwuHeEQerKCAYMR9xwIaaowD6jmrAQckA+MmGDbxtyEGG/ogw+lBPIhY3jjkg7EePBTzH31DVE/iGCv+13wE8RQLwuI+rrPYPkfd8lnyIPouMCA4s5nmGRHA68LcZ6IsM7BnoI8DfFXA/x/YeqxHMYVeCudVL' \
			b'wBxSiiaIwr2XnW7scc9gTrHiFsEco06K8hDKaE4R1qI5fgy9KQfzCXizNMrWAiZJDcmQgfd8PG/38pwK7oTdkLs4OGvCgXMOtqy1PdBMGl0KzcEkGTQHtS8unaOsCZvTd60GZVv5blGkvaAc3sKgjELzM3Io5mgHi+JcAkfAPbCWZgPcBrjHBVzystqJl9Xm' \
			b'Xtb9gGspouQ9AC57Vm3yrFKsuCXAnfWs2uRZtZs8q5Y8q9ZeB7j0AmVrAZOkhnY54M7GG011XgMuB+eAS15TS/5Se8BZalc5S4NJcsBltS8H3NJZmr5rPeBWftJrAJffEgCXHKW2dpRytKWAqw4MtG2A2wD3uIBLHk078Wja3KO5H3DpVgRc9mJa9mLa5MW0' \
			b'Q7ElwJ31YtrkxbSbvJiWvJh2uA5wKaqytYBJUkMy5IA7Gw8AtzivAZeDc8AlD6Ul36Q94Ji0qxyTwSQ54LLalwNu6ZhM37UecCuf5DWAy28JgEtOSVs7JTnaYsA9MGj1DAG3tS3ft7blQwANuc0/FDNdAdCuXwLQkJq4lRT3Xna6kcIZoClW3CJAY9QJQEMo' \
			b'AzRFWAvQjtqTYZcDdCFCDdYcrGwtbLrFkDwZWM/H8+mgPM/BOjQllzEG1iJBdxBR5/K6qOs9ME56Xwrj4WEZjAfjLIZxFD3BeBJ2WxMyqSBhuTvUghzUwlCOgvMjcijnaEugPG8lVgeGoDZIb5B+3pAuCNLFBNLFIkgXFBEgXTCkC4Z0kSBdFFuCdDEL6SJB' \
			b'utgE6YIgXVSQnoswgXQKVrYWNt1iSJ4c0mfjAaQX57OQXsQYWIsM6SyizuV1Udf7IF2sgnS+IYd0Ns5ySBclpIsk4iZIFxWki0OQzmoJkC4I0kUN6RRtNaQfGFDaIL1B+nlDuiRIlxNIl4sgnSMCpEuGdMmQLhOky2JLkC5nIV0mSJebIF0SpMsK0nMRJpBO' \
			b'wcrWwqZbDMmTQ/psPID04nwW0osYA2uRIZ1F1Lm8Lup6H6TLVZAetJ9BOhtnOaTLEtJlEnETpMsK0uUhSGe1BEiXBOl17w6OthrSDwwDbZDeIP28IV0RpKsJpKtFkK4oIkC6YkhXDOkqQXq5JUhXs5CuEqSrTZCuCNJVBem5CBNIp2Bla2HTLYbkySF9Nh5A' \
			b'enE+C+lFjIG1yJDOIupcXhd1vQ/S1SpI54flkM7GWQ7pqoR0lUTcBOmqgnR1CNJZLQHSFUG6qiGdwlZDOg7q9JC8fwb5i0R2d7z54rcC/LAC5NUdAXp1JLAH2NRQYKbW9h0uFVqgvv98xNZrgR8fxciPQfAxhpAf9mHGF1NsacYXM4f8+FCe8cVsQf7Qhxti' \
			b'FXMD5zLU0L/D9aUMTfVi5jec58Ug+EOSwjnjsZPFnuhjfT7HAWUM0mmc6oVl1bngLhyVHDCW072YQzwg6fZyyhd+aD7lC5trMRfgJ2Q9uQ125KaXbSEDTOymJITDXtWgJGYEFF+xBBkjcLSMETAEfj0t+F834O+I4Z4acCom53dIDNbnopoW9hGCBR4AEiAG' \
			b'IMjP8R7BfinSz3ZVQVwH/E7FckTmqoNJ0bFkYHQ9hKoLi80Fii5Fzxw5xXq0XIySAR1thYqx6DscQsIFGBhysyPYC5gXQW4G4QK83QDbDvf2CEC2q2YiAUSa9NcoemrsuBfyQXBZUcIs8GQFkuQwAhiyHjtWgEaEC8CKEigCRECudzO5/kBJ8AgZP5bp3Fz2' \
			b'N2cOAfbmMACsPgcFExgwC6DgmlIRlXTuJh5khRuw6Swu6LqWeq7YABa/OT7IejnjhBHTQoVcihHDipKBPi5GZDU+Bgt7u8UFfx1GG1qY6MJ+ZuyoK19bihD9LRYjrsOOBbgRKlJnjB0oY/7POCKwEehWyxgI7ThDisS68THKHFrdBq7ofRUWicsHrC97dP/y' \
			b'afKh/xise4zr6h7uOoSxtwkyDCxDAhZ5z+oi5kAhJG+tgUqpIUAxwDBjCSx2wOHH0sGyPbDsjb8HVxaKM7H4//F2gAczqVargUcdGXwi2JgINmC/e1upkaD9vYUWtE+a/BZCDfVigUS2E5NF9VJLIV6GK7icBuKZjnAEJ1jW8YlucyuI3tP2fetIFLyU0HDt' \
			b'5qEIGqbPHo7cysZksbBeNCIrffayzZ5yjc4hRs/6AU8CMRFe0HbjHojR6u7ADKSAteWYqgv0AaiBGWNoWtZr6kde12fVcroHLXwu9FYS6Orz5+LIhZiJa+pIBRnQOBQYgTDk0paVvFBjZlAkFF4+R6HljGtKNZJAHhjQy7iDdLMDX+gJSi72lIUXaHiCZyK0' \
			b'LW59KQoysRBTl10sF1fqQorsXp8SbPZ542/LZXMXq0j2pm0tCTUw9d8l0KAuEI67N+gjuG5OXvS4UQ1nuLnrpvsX9OjpofHEJ6+TosE1CNDbG5Y37ggarCpfrECDSyhD7C0/jNg96WblhjuGBfzBy0sKi3w0/o5NIGCOhwPjLdQ9NvaBnnSJOxYm9GePC6Dv' \
			b'8wQH/C59K1WLHCIob23DCejfeVSwgLLk+rrFMsQw2xDDHg0xcrQA0U5SejgmWjSk2NYBrEQJsNcpCxNHB4nPBRB2G0C40wCEbgDRAGIhQNgGELcBEG4bQAynAQjTAKIBxEKAcA0gbgMghrNumbzk1sgzRYCzzPy3lNMlSnq27Y63l7O7f/lk/xCADd0PY8vk' \
			b'Z5TJb+p8PNuMjmnyLDL6uXsY9uT0zZ5GKx56lIW87tXf8nrL6xvzOt1+t0j9vuV1Ix96SMa8Llpeb3l9e153La/fnbx+4g6FLa+vy+v71jI9dr7HbHrqejvedA7ZngT5bLkeH78810tcdaObLPSZ8n9Y3HPfqp6IDOfdubAhwxmVAjAlnxwNpDgTNEBBPh8a' \
			b'SHEbZYBFGLCxb2HDgHuDAZi6LqYl/4YYQFnt7tQDtM/p2MFugFZ9gUtumY29A1uev/A8LyhjX5z3blmex6+/hLq/RpqHVI0HAvP8xg5/Lc9faJ7H1HTJLvvDmR4//6Ja/KBMD9NXO+v3xPMb+/C1PH9ZeR7zwH3opXPfGvkV8HuPA4VN6453f/L62DrkYVaH' \
			b'59yLjC6wSx4Mih3hgNi99c276BwPuff0PfPOLMffI3IX0HLXowvftq55l53Vz6ITbsvq55DVz7tnHpRBwmSDx8r2s2tfHXmCwTbkZsXEP/Byf+Ox4cAH2VOCgo9o9kHDtjF29g7OBdhPF9M727LAhkXvFpcHXDV1+kWCAq2JWP6v69EDN0xWmDv/IsO21eFW' \
			b'lBtQMWkydHmw/OD0Qw/PWHw4cZe+hhgNMa5BDDX5X4kYqiHGPGKoHDHUUsQ4cQfAhhi3gxgXihZ68r8SLXRDi3m00MvaJjKkMN3rAfEBwYGRgWBBIiBIhAKHIJAjAGZ/ysuY+TDTSc5sbk8mGzFDUWaoMkBM8MYn8JiYQzqOSTgmXzAKpVpDaRWTKdprJnmm' \
			b'pBkSFSYAMDvERnP3e6wMBo7LaU2Vn3RtsX5nb6RRQkrWa8+ACGBX6Fiv0PMesCn0jdnr8yhc4NNkpnjJT5WiskLMeIsssT8r1BZxN7OI2WMUe9cNYxPkTowTMPMoBhq617D0mNL4xUCRmi6M3WuP5E76cCoVKAh2sOaThECvNAyABV2MwGXlh++v/P7BzgdB' \
			b'989O0griDpZ7goWebLEGJa5PC2svwSrpGrhV4Dq2tvMADZwf12zylqzXlhx5TSRct9yAIDu58a3e5of+8NkKnm3mn85ryMhrXqOgAKaKv7Q+jKiuoK53euatAtfOMji3rIP54ZYIAfM/x2ZfmlabBLMsnP+W+AdJXvM8cOlfz/7h1Z4adeEYZlTTWN/S+AXm' \
			b'hl8ARcPFH2G7pX9QXJ0JR5HtapHFIamr5R72fgW8LH6JL68f/IOidx2GRWIsAlss9hbXfPHW7/H73PT7vNH2faIvQEENQ5cVi/3f7VEWiom9xB6hUPyBchCWPWWPA7FoWWqLo94BjWhEVdBUz+1elrTmXw+LupD21GEN+jI1VREkaRNAnjTqP1PjCni8wh2U' \
			b'crr0B7A8VH/knZn/r+Mejp3umnvOfIw5maYxZ96MFh7OIAX7ZHBbf/hN49mlWrkn5aojpF5cE+DEG1TF6yCYP/R2Ho9G9wWW06dkaL056kafLuKnw2zN9rMl+/6OpXzT0TZia1Y8veUNKhWf6dFLN0oG8lZyANR9bpYJoInuxhs0EK64gTSgqowAy4J/PhbA' \
			b'7AANj3cmR0CdOtu87PiIz7hBdfuzvuC6jRLGTO3oQGK4nv1vlEGgRb/coMV6Erhkg/bzNTeQNkzLJoezydDds43SxUx19nS5BNxdp9lIGa5lkoOZBNpk79dG6WKmxnyjTAIGv1lGUd0tbuCBXXMDKWVsmeVwZhm7e7ZRM/tMpfzGmQUMfqMMA50nbnWD3gpr' \
			b'biDd1LX2lmfKPAPuvvu1UbqYqcbfSp4R9qb5RnW3vkGHnjU3kIpaPf+arKO7e7ZRulhXzYdUsLqdf20OCvZKuch0yzfo07Qitk+qS+JB77ZwQoprLQLXZCjX3bON0sW6FoFNGaq2+c0y19B9vi3vcLryXtJma1I4nMugX9f92ihdrGtSOH0ug17mZ7eRKltD' \
			b'xDVZTHX3bKM+ef39The9/1BeSq9MHyKlEWtDOvH/FtKK7i51kwr+bRVm544o/YjVfYpuA6VD8tiO1nMQ4LrlG3RNXnVDfT8Pyll1E42mSSNp0ALrmkXO2gIwGutubKT6mR7Nd1b1orsjG6l+XYvGbaseaWmN+vslJpDdkTegwZtEIlPM9E9fVGw4rTXEEouo' \
			b'btUGw0bW3rN5O/Ayssu6Noo7ZRfT3cGNrLJ16MAdsIrr7uBGVlnX0nCpAzrs2G3YaJx7+t/2lPqJ02dnp0WcRQ/KNrL4+Q2GOIXFYXqDy9xo8N+6fhYXa2XTXehGVl7fCHGRVrbdhW5k5fUNHRdpZddd6EZWVt1rBSPhRc/jt3UMYEw3EACaxEBovOUE4is8' \
			b'eTrw+sYYXtswJgzat2FWGx764I00F1vA8Pfin2IPk9hgQ7zDy1L9S+44rovx/5Aa6Gk+YbzOkyWmpCIFhdSDs+3g3RDq0x/PI0Tz94S5e2Q2Zw/Ov0NvEeVbYHIHGOqv6YEuexUkUG4lMjzoXMIISZggqIfYOBCD6vs+8mtsM4c2cmwbtzh2A0J8LBjX4lgA' \
			b'naY1IOvCKm/SgNokN+TAGlD+KRDiWDkuhfg431/9PxXX8SE='

	_PARSER_TOP             = 'expr_commas'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

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

	_STR      = r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY)))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('UFUNC',        fr'\?({_LTR}\w*)?|\\operatorname\s*{{\s*\?((?:{_LTR}|\\_)(?:\w|\\_)*)?\s*}}'),
		('UFUNCPY',       r'Function'),
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LTRU})|(\${_LTRU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\$?(?:{_LTR}|\\_)(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

		('SQRT',          r'sqrt\b|\\sqrt(?!{_LTR})'),
		('LOG',           r'log\b|\\log(?!{_LTR})'),
		('LN',            r'ln\b|\\ln(?!{_LTR})'),
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
		('IF',            r'if(?!{_LTRU})'),
		('ELSE',          r'else(?!{_LTRU})'),
		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)(?!{_LTRU})|{"|".join (AST.Cmp.UNI2PY)}'),
		('OR',           fr'or\b|\\vee(?!{_LTR})|{_UOR}'),
		('AND',          fr'and\b|\\wedge(?!{_LTR})|{_UAND}'),
		('NOT',          fr'not\b|\\neg(?!{_LTR})|{_UNOT}'),
		('EQ',            r'='),
		('NUM',           r'(?:(\d*\.\d+)|(\d+\.?))((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))('*)"),
		('ATTR',         fr'\.\s*(?:({_LTRU}\w*)|\\operatorname\s*{{\s*({_LTR}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"({_STR})|\\text\s*{{\s*({_STR})\s*}}"),
		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
		('COLON',         r'{:}|:'),
		('CARET1',       fr'\^{_VARTEX1}'),
		('CARET',         r'\^'),
		('DBLSTAR',       r'\*\*'),
		('CURLYL',        r'{'),
		('CURLYR',        r'}'),
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('BRACKL',        r'\['),
		('BRACKR',        r'\]'),
		('SLASHCURLYL',   r'\\{'),
		('SLASHCURLYR',   r'\\}'),
		('SLASHBRACKL',   r'\\\['),
		('BAR',           r'\|'),
		('PLUS',          r'\+'),
		('MINUS',         r'-'),
		('STAR',          r'\*'),
		('DIVIDE',        r'/'),
		('EXCL',          r'!'),
		('AMP',           r'&'),
		('DBLSLASH',      r'\\\\'),
		('COMMA',         r','),
		('ignore',        r'\\[,:;]|\\?\s+|\\text\s*{\s*[^}]*\s*}'),
	])

	_PYGREEK_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.GREEK))) + ')'
	_PYMULTI_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.PY2TEXMULTI))) + ')'
	_VARPY_QUICK   = fr'(?:{_PYGREEK_QUICK}|{_LTR})'
	_VAR_QUICK     = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK   = OrderedDict ([ # quick input mode different tokens
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})|(\${_LTRU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LTR}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

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

		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)|{"|".join (AST.Cmp.UNI2PY)}'),
		('OR',           fr'or\b|\\vee|{_UOR}'),
		('AND',          fr'and\b|\\wedge|{_UAND}'),
		('NOT',          fr'not\b|\\neg|{_UNOT}'),
		('VAR',          fr"(?:(?:(\\partial\s?|partial|{_UPARTIAL})|(d(?!elta)))({_VAR_QUICK})|(None|True|False|{_PYMULTI_QUICK}|{_VAR_QUICK}))('*)"),
	])

	TOKENS_LONG    = OrderedDict () # initialized in __init__()

	# grammar definition and implementation

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
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                      return AST.flatcat ('+', expr_add, _expr_neg (expr_mul_exp))
	def expr_add_3         (self, expr_add, SETMINUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, _expr_neg (expr_mul_exp))
	def expr_add_4         (self, expr_mul_exp):                                       return expr_mul_exp

	def expr_mul_exp       (self, expr_mul_expr):                                      return _expr_mul (expr_mul_expr)
	def expr_mul_expr_1    (self, expr_mul_expr, CDOT, expr_neg):                      return AST.flatcat ('mulexp', expr_mul_expr, expr_neg)
	def expr_mul_expr_2    (self, expr_mul_expr, STAR, expr_neg):                      return AST.flatcat ('mulexp', expr_mul_expr, expr_neg)
	def expr_mul_expr_3    (self, expr_neg):                                           return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                    return _expr_neg (expr_neg)
	def expr_neg_2         (self, expr_diff):                                          return expr_diff

	def expr_diff          (self, expr_div):                                           return _expr_diff (expr_div)

	def expr_div_1         (self, expr_div, DIVIDE, expr_divm):                        return AST ('/', _expr_mul (expr_div), _expr_mul (expr_divm))
	def expr_div_2         (self, expr_mul_imp):                                       return expr_mul_imp
	def expr_divm_1        (self, MINUS, expr_divm):                                   return _expr_neg (expr_divm)
	def expr_divm_2        (self, expr_mul_imp):                                       return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                            return _expr_mul_imp (expr_mul_imp, expr_intg, self._USER_FUNCS)
	def expr_mul_imp_2     (self, expr_intg):                                          return expr_intg

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add):               return _expr_intg (_expr_mul (expr_add), (expr_sub, expr_super))
	def expr_intg_2        (self, INTG, expr_add):                                     return _expr_intg (_expr_mul (expr_add))
	def expr_intg_3        (self, expr_lim):                                           return expr_lim

	def expr_lim_1         (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                          return AST ('lim', _expr_mul (expr_neg), expr_var, expr)
	def expr_lim_2         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):  return AST ('lim', _expr_mul (expr_neg), expr_var, expr, '+')
	def expr_lim_3         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg): return AST ('lim', _expr_mul (expr_neg), expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                        return expr_sum

	def expr_sum_1         (self, SUM, SUB, CURLYL, varass, CURLYR, expr_super, expr_neg):                          return AST ('sum', _expr_mul (expr_neg), varass [0], varass [1], expr_super)
	def expr_sum_2         (self, expr_func):                                                                       return expr_func

	def expr_func_1        (self, SQRT, expr_neg_func):                                return _expr_func (1, 'sqrt', expr_neg_func)
	def expr_func_2        (self, SQRT, expr_super, expr_neg_func):                    return AST ('^', _expr_func (1, 'sqrt', expr_neg_func), expr_super)
	def expr_func_3        (self, SQRT, BRACKL, expr_commas, BRACKR, expr_neg_func):   return _expr_func (1, 'sqrt', expr_neg_func, expr_commas)
	def expr_func_4        (self, LN, expr_neg_func):                                  return _expr_func (1, 'log', expr_neg_func)
	def expr_func_5        (self, LN, expr_super, expr_neg_func):                      return AST ('^', _expr_func (1, 'log', expr_neg_func), expr_super)
	def expr_func_6        (self, LOG, expr_neg_func):                                 return _expr_func (1, 'log', expr_neg_func)
	def expr_func_7        (self, LOG, expr_super, expr_neg_func):                     return AST ('^', _expr_func (1, 'log', expr_neg_func), expr_super)
	def expr_func_8        (self, LOG, expr_sub, expr_neg_func):                       return _expr_func (1, 'log', expr_neg_func, expr_sub)
	def expr_func_9        (self, FUNC, expr_neg_func):                                return _expr_func_func (FUNC, expr_neg_func)
	def expr_func_10       (self, FUNC, expr_super, expr_neg_func):                    return _expr_func_func (FUNC, expr_neg_func, expr_super)
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

	def expr_paren_1       (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):           return AST ('(', expr_commas)
	def expr_paren_2       (self, PARENL, expr_commas, PARENR):                        return AST ('(', expr_commas)
	def expr_paren_3       (self, expr_frac):                                          return expr_frac

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

	def expr_ufunc_1       (self, UFUNC, LEFT, PARENL, expr_commas, RIGHT, PARENR):    return _expr_ufunc (UFUNC, expr_commas)
	def expr_ufunc_2       (self, UFUNC, PARENL, expr_commas, PARENR):                 return _expr_ufunc (UFUNC, expr_commas)
	def expr_ufunc_3       (self, expr_term):                                          return expr_term

	def expr_term_1        (self, expr_num):                                           return expr_num
	def expr_term_2        (self, expr_var):                                           return expr_var
	def expr_term_3        (self, STR):                                                return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_4        (self, SUB):                                                return AST ('@', '_') # for last expression variable
	def expr_term_5        (self, EMPTYSET):                                           return AST.SetEmpty

	def expr_num           (self, NUM):                                                return _expr_num (NUM)
	def expr_var           (self, VAR):                                                return _expr_var (VAR)

	def expr_sub_1         (self, SUB, expr_frac):                                     return expr_frac
	def expr_sub_2         (self, SUB1):                                               return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1       (self, DBLSTAR, expr_neg_func):                             return expr_neg_func
	def expr_super_3       (self, CARET, expr_frac):                                   return expr_frac
	def expr_super_4       (self, CARET1):                                             return _ast_from_tok_digit_or_var (CARET1)

	def expr_neg_func_1    (self, MINUS, expr_neg_func):                               return _expr_neg (expr_neg_func)
	def expr_neg_func_2    (self, expr_func):                                          return expr_func

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
			if rule == ('expr_func', ('FUNC', 'expr_neg_func')):
				return self._insert_symbol (('PARENL', 'PARENR'))

			if rule == ('expr_paren', ('PARENL', 'expr_commas', 'PARENR')) and self.stack [-2].sym == 'expr_mul_imp' and \
					(self.stack [-2].red.is_attr or (self.stack [-2].red.is_var and self.stack [-2].red.var in self._USER_FUNCS)):
				return self._insert_symbol ('PARENR')

		if pos and rule [1] [pos - 1] == 'expr_commas' and rule [0] not in ('expr_abs', 'expr_func', 'expr_ufunc'):
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

# 	a = p.parse ('ln')
# 	print (a)

# 	# a = sym.ast2spt (a)
# 	# print (a)
