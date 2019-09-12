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
			b'yDBccRAc+iM0XOefQ6LwaTjOwgXtdqgCif/KhssSDuC5HE4v8cJxIEVS+FEjf5TrYyiHjSlaXwbsJKYEBe/BFylFP9rfaeQVB+0UGQgSjIsXIB3QBd3Tj3VXfOqtBEdj98DbHvVP3+4DTHZiaQcB8KbBJz0f19AXxNNJUDBWGS6np9WdanKK31nFqG7S09Mi' \
			b'xk6NmWgp+bIQVYCqA3Qe4FObHFgqMLMugtPpTqHmfEJ5IMfOGxIMq7wB4GZvX3/CaW0+BiCMN9+yiN7kZcSdwvQPyd911oTE6i9g0heOMxlkTO1ztM7yGlyM4SlEU4hJIYZCbAqxFOJCyE6g4qUPl/hiryP8MX2UNgaJPAgO4VM0/ewY6fgQjgSl9PDNcDch' \
			b'c89ZgL4G30Qf7Z+F6Zw/CpI92giUis8UPf1YyIOUgwQdoh4BigMS0yf6MAoJpzv83oFuNJBGOj2EtJMHc4A/R+lH+vFJ6orPfRZF2Xr68UbeSRIJrC9RJJ8IHwBEEFj4M0tgCrjSR84IKcboACsIx6RF+II+xlCd4nQd1OqC9nzgA5vyL57GV/szS+gILDOG' \
			b'I9XzEYkLByocUHTINqKb6JXDc91KUACB+kA/BlIVJ9kBD0Fg/zHEY143mAJjsvZfJjFRSUk/RscMKyUeghYH+sl4e2Do145+kN6ITfwZHMKRDRev+NSfhQukJJ/+nCBF22AKkMGgUgw8wMQHwNcZfIBx4QJG5aBwl6KPBoTyN/pCyuseYvpzjdb0EOwzjU8F' \
			b'HhW8Nb2ORyAiL8UgusGDQO9Jrzf+3/p/5/89KvQjJDiDxGngHOIpTCa+JOFTlI/rED98lhf+cPQP7f2b/OYt5u2pusFvuhtMN9hucN0AYON5wV8UXiDhJRKetoVPi5Achs7nQuFlFF5IKBb5jANIAgjlc6rHGniTjyYwnpfe77w8wgskvEQCRPIPGvtu9GUK' \
			b'kBdeprrRdKOFTOizh8eC0YfozvnNdM52znXO8/HYDb0XBb5nhPzpAcD6JC19Gc8nbABQaz11AuLa0dN35+3oZOf8+wXcKKAs5U0JaRle7YO8NN93D3ooPLx+4A0CKc8bBXbeKsJb6oHmq6COKyzS4W7Aqz7Y0rmDXbPhyWw4kpUE7qF8RuYZyKbw/WDMQXK0' \
			b'nqw5ULlROrI8BYpwM1rrqmXUszEyapXs59hUA+9H3ku2nUHTFSpm5ZJW5/RJeoz6K/SW6WpOUawfL6MZSERjTyWACzqixA1JC1Ui8fxIUki2lNTHfCmBs2AT4Ftb/j2b/AsWaQY5I4M8ECGb6pZTzsswglF8RGILakIFRXWwGsLX51/svzJ+0Qm/pEgleco4' \
			b'Pi8CIfZUVg9lBIXnqvOq6HxNtbMtiR8xiSvBFSsupuA5llOGhkVnZChfiaIyHFSMNXyJP4VaMdSXoR7sDdTMcUxzmGaOczKHbeY4J3O4Zo6zMceDIVTFFbWqChEKX4IaVBvNn4upBDVtQyU9lMgstZrK0LiquNWNr3NzqWGL6tZaelYG1WwtruKPaJ5WGeTK' \
			b'oOSWY8l+HqHY0TNQU/JIlcVR8GXJiV5yqg9tjew7GBnfenY4cK1mDO0r9DY9huZpfjrGunfqfzBqUosjZToq0UJeg8zW2jEO6c5xknKU8BylLMfJeOiZZzl5C8ZuQ6na0mVLqdTh2eiRC14OL4aPlRept9fQMQK/nXKmE/fq2ymjWQItS05rJzMVhMx3+aqg' \
			b'fGM536h7lQzYTYou7vx7yTlDqGBUIClKNJIpUMrYT0JSBwnZujycsqrrP1VSl5RmiJO2ZFswAHY+8fum8WO08oiW5k/syu8RfVp1/2ws4rUgqTNbs8s52UW3jHJeBvHHzSDnYxDsZytDt07J3Tr9vlngiFlCosZRW6230S1UtQ2m6VO8eaZTO3QLDpUUzGLN' \
			b'xLegaIkFrmP1babKPryN9rjTdDaOAUDZC6H3DW/4ngdDQPMBZflm/C3mUD1pnDTMbgxugucWd2pmjO5uQYmlaXlNosdyAHRAo+TNY7OwZwfu+6BeHfxuQ3DnUVPnYOgJlE8Gxw8SnPabFRZYQaigf2rpauq6xreMvNA0M6MZ3TSzRzOmaWYWfDQB+Eg7QYzw' \
			b'GvtttEr8OVUhRywRtVRL+XkUTRtJGxozqxEwWco9VQL09ZLc50lOfO+O4W2+Z6UIATRc79TFQWFiDyRJPZAk9UCSWPIWdG64TmoJF7CHxSUa9jX0pkLHy9D6v54VI7m++eOPRf4udaO6xEz+YORWHcTtS/5S+ERxDiwjubumZBpRl04jTjS4Oo7D0XJ7ljWX' \
			b'nqasvfQvdLLlmiPlGm48t8PFpynV0tSx5jnpqbLIfddi13KYNxHqTlc4+y7svDkU+zbVFbm5FfmG2njfs7Gnl0iRq5lsxTtDJgN9K+7fo65CvxOVJimDXhN8CjtJJgal054ebulpim/liUPAJUvh1ByBLU5tTpfj1gOpGYsKHU3vR+y/pRgdw0yXcgjoqILn' \
			b'XLLHHD24DRpPYKOh5YsjTz9BdDIQfwyOM4MIzGFDZ5GQTRQzzVw7PIQqClUUimwUuI1yXGv+PRfbg7SKBvIrGsivaAQ+mstQG9d99kh5Jcj7PAsBuuJU6850XUOs4NYyR4VyRyULN5LuqMlYYKAw4SbLZXFLuQ57bXyPEw5gXuRu/rLnPVX7LOGro3ss4asl' \
			b'RHYE2ZZfrmJdUHNdUId+glQL0VQL0VQL0aH2oVu1/jjVeouqpxQTGFJzdTD10SRrwvdpnosF9kZET7ne7xR3ZGRH9zq4lb3PeBMBPKZAfRXKw5fbaIV5wXBeMKHkT3nBUF4wlBdoR6Egm2ELGM7jhpRqSKmmFViPPEM2qr6emoGyRCtcnomdAFUMDbCwYaZ5' \
			b'C62QXmCYSjvyIHyZ5YxlKWNZylgQvYsmt62vWNCYIfr3L3CMULin2eUeCJqpHBXqmtJiSXZALflPdciCNO4nTgUVNDkQD2MrnYA3wLxkMCkZzEcWE61X20BpdaBnDmwApnHHlhh4PzKd06RmKMzYTBNNMzZtpNwN94RUJDn1yLzmAPOZ9ZTscC+wxg6K7LvX' \
			b'Pa5CprFdH+ZsH/HzFNII8hbUKCR+mAU5VRjiSIRJ5MmSO7AGNQCQ1nLV1Mo3qPZx3mJcVxzpO/H7x4wULXmj0DNlKMtBxRtWqIFFYmC9FuBimKENpmeDudlgjiqYoArma4JJ2mCyMpitC+bLg8nyYA44mP8NkgsscQR8D9NCw1zEMAEuGAyIFCYxhBkMgTeh' \
			b'lg/z7kFXLejNBGMGe1jpzGsKxlv7soEEbxyMLIThUUDgUPWDkQkw6BAGjoKGYSAbDB1UUG6AxeJ8GLQqw7RQ0MqsIVXBYn3+GAadQmcL6GgB7mPoMeoGb0xaghUWBMWV/zpcww7WfsOV/LrdACul9bAKaA9r3Q0drqYGZRVapxAWv4SF+eBE4ApyPS5W2OEy' \
			b'mwOuXQqPwBVYYSU9CatjwktgMTgBd/m0sRsgVMIKdhIWGsTHSpAEX4/LncLyebBMHIjg7/Aa3DlYoREEhdXqLC67KXDlPlyhDlaAo6UlcQk5XLV1HOmzfDLZeTvsnGHZYZnBET8EFq+Efx/bgoiClvrDNVRx2UgQ0O8HkKqH+3tcmVDi2pK4jiN+iMDVHWkp' \
			b'UpARdOJzws7n551PIrsBhMcXoH7gqcry4q9wAutFgpTwrYKX0AS5/LmDMLiVrOSvwuKCDvawxqx/ioOY/mUOVcqrFDpNEgAM4YqDsIQufB4US3cWvgcFROkhHpjHp5SdgyeN3wMIQNYvsr3Yn/MDpBFUJQjQAQVECQT2NrHAJ9wcPGegwUzhASrE10LEseDB' \
			b'fB6IgOniJjAxLIAKA5o1NTqYJfhgOs5nZgYlTMIJM4cU5vNjBcqnLO7pbw4xZjDDLEKNoyLGZ8SMYQY3zBLk6P6lHwK7mIfAL270O/N/WDDeCyexSkrVYKxQU3FqCi3gYMgqxlV1/DDYUDFwKeToDHWyUt88AokahHwy53bt4OvIMAmbAByX/6jkmRofVFmM' \
			b'i8W8gF35QHbyKMfON0WHHK4Wz9U4EOcAx/UBvFPLMQ/Kj1B2LLDP3w/9hDZjYM846FMBNJesxUNIN4sx0Va4qBkb+wofoX1FZzgpqCQFuxIqKcswVkL+9AkMd4yYcOwtjDvCTag59IQ2uIfM0PcEnyIhKEWLW4RTvGeCpxDKgIrPQRRdDawoB9gI9jm4kmzp' \
			b'fwK2LKSytdxh60krNh5mOFw/vXgTJJc6iAB7xBXbDWI2K0+EGEN8T4DxoF6rs4chsIfDffhOJl4K8cG8GdAHCy6Ge0xmCe+LjweP0XrwpxSX8J9T3B78Z4EDB2BkyOb0/owLolSRE4gNrHwIJE2kAHD2ENO7z+cPgbx8Hn3olQNsoSZs0a8of94xkiCGMKHh' \
			b'dxlF6BvSRKOII1GEIIoQNUXA14slJWpI94KZQTAzCCYGkYhBFFsiBjFLDCIRg+gI/9fzgiBaEBUr5GJMGIGCla0FTrcY+k5mAixoyj1RMUWYKiwvt0ciKGIMrFCmAJZU52K7qPZ98L+qhB8elsM/22k5/IsS/kUScRP2iwr7xSHoZ7UE6BeE/KIGfop2EPZn' \
			b'0F5vb2q4KdSfDOdbNeCCMF4TxutJNUAvAnhNEcHWmgFeM8DrBPC62BLA61mA1wngtxX6NYF71Z5SiDABdwrG1vf5DcFdl8X82XiQDopzQnXSD2N6cT1TI8M6y1gI7GKsfbCuV8E6PyyHdbbOcljXJazrJOImWNcVrOtDsM5qCbCuCdZ1DeucDraW5k3D94bv' \
			b'dxnfLeG7neC7XYTvliJK3kOKt4zvNuG7LbaE73YW323C902t5fgxGncFvuciTPCdgpWthU23GNrl+D4bbzTVOeN7XmYvrmdqZHxnGXUusIux9uG7XYXvQbsZvrN1luO7LfHdJhE34but8N0ewndWS8B3S/hua3ynaJvx3TZ8b/h+l/HdEb5P+kOQ//JafHcU' \
			b'kXpyEr6z4xOfzPjuii3hu5vF99RtgiKsxndH+O4qfM9FmOA7BStbC5tuMSRPju+z8UZTnTO+uwzfi+uZGhnfWUadCxyP9uK7W4Xv/LAc39k6y/HdlfieibgJ312F7+4QvrNaAr47wndX4ztF24zvbqnv9hJQvm9Af7lAPxLQjxOgHzOgF4T1uJuDe4qBFh8Z' \
			b'7keG+zHB/VhsCe7HWbgfE9yPm+B+JLgfK7jPRZjAPQUrWwtb3GVIpBzxZ+NhgsjPGfHHDPGL65kmGfFZTJ3L7GKsfYg/rkJ8fliO+Gyg5Yg/log/JhE3If5YIf54CPFZLQHxR0L8sUZ8irYZ8YeG+A3xLwHxJblf5cT9KnPfq6QeOlLMIz50RmMPrGQPrGQP' \
			b'rEweWIoVt4j4ctYDK5MHliKsRXxJ3ldZeV8LEWrE52Bla2GLuwyJlCH+fDyYH744J8SXWQec8nqmSUL8IKbOZXYx1h7El6tcr+FhGeIHAy1GfFm6XpOw2xBfVq5Xecj1GtTCiC/J9Spr1ytH24z4Y0P8hvgXgfiSEF9OED8f3wInhmLNIj5Hh9QtGfElI75M' \
			b'iC+LLSH+7DAYHKjCiC83Ib4kxJcV4uciTBCfgpWthS3uMiRSjviz8QDxi3NGfJkhfnE90yQjPoupc5ldjLUP8eUqxA8WyBCfDbQc8WWJ+DKJuAnxZYX48hDis1oC4ktCfFkjPkXbjPiiP48u+a0/fsP+28J+6ogjJx1xZN4RB04MxQrYD8eQoHViAE03cSgy' \
			b'AHfKkalTDsWKW2KA2U45MnXK2dYTX1KnHFl1yilEmDAABStbC1vcZcLlggRmowIJFOdMAlnXnPJ6pkwmAZa0ENvFWPtIYFXXnPCwnATYRstJoOyak4TdSAJV1xx5qGtOUEsgAeqaI+uuORxtOwngME/sXMqw7hDQRY3jgOA2IOw+eGWsjDjoGN804VfEJcYi' \
			b'LE7okN8h/47diTYc8XomY9QaITZCvCVCVNT8pSbNXypv/lLU/KWy5i+ETUs7IkRIz9wIprgRTHEjmEqNYBQrbpEQ1WwjmEqNYGpTI5iiRjBVNYIVItSEyMHK1sIWd5lwOSfE+ag+ZZTnRIgqawcrr2fKJEIMkupcbBdj7SFEtaodLDwsI8Rgo8WEqMp2sCTs' \
			b'NkJUVTuYOtQOFtTChKioHUzV7WAcbTshToeeNRJoJHCnScAQCUwmdFD5jA5wYihWJAFDJGASCRi6iUORBAyTgEkkYIotkcDspA8qzfqgNo1Dww/D/FWSQC7ChAQoWNkUBxJTLbkJ1wsWMDMbskBxzixgMhYormfaZBZgUXUut4ux9rGAWcUC/LCcBdhIy1nA' \
			b'lCxgkoibWMBULGAOsQCrJbCAIRYwNQtQtO0scGBIWmOBxgJ3kQVoEIOaDGJQ+SAGnEGLYkUWsMQCyTui6ExwKLIAD2hQaUADxYpbYoHZAQ0qDWhQmwY0KBrQoKoBDYUIExag4ErSWnATj3ISmI06muqcSSAb1lBez5TJJMCS6lxsF2PtI4FVwxrCw3ISYBst' \
			b'J4FyWEMSdiMJVMMa1KFhDUEtgQRoWIOqhzVwtO0kcGDcWiOBRgJ3kQRopMN05keVj3SAE0OxIgk4IgGXSMDRTRyKJMCjHlQa9UCx4pZIYHbUQzZZpNo06kHRqAdVjXooRJiQAAVzhtyzIQnQUU4Cs1GBBIpzJoFs7EN5PVMmkwBLqnOx49FeElg19iE8LCcB' \
			b'ttFyEijHPqhMxE0kUI19UIfGPgS1BBKgsQ+qHvvA0baTwIHBbY0EGgncRRIYiASGCQkMOQkMRALZoDc4BrgfEglQBMGhSAIDk8CQSGAotkQCwywJDIkEhk0kMBAJDBUJ5CJMSICCla2FLe4y4XJBArNRgQSKcyaBISOB4nqmTCYBllTnYrsYax8JDKtIgB+W' \
			b'kwDbaDkJDCUJpA/ZRgJDRQKHpiQNagkkQDOT0stzEqBL20lg8Qi4RgKNBO4ECWjyDOuJZ1jnnmFNnmGdeYY1eYZ18gxDimXPsGbPsGbPsE6eYYoVt0gCetYzrJNnWG/yDGvyDOvKM1yIUJMABytbC1vcZcLlnATmo/qUUZ4TCejMM1xez5RJJBAk1bnYLsba' \
			b'QwJ6lWc4PCwjgWCjxSSgS89wEnYbCejKM6wPeYaDWpgENHmGde0Z5mjbSWA6KK6/HzwgplSwdJrSRgd3gw4U9ZxVk56zUCLMO88q6jyrss6zijrPqtR5VvFNHIrVAu48q1LnWYoVt1QtmO08q1LnWbWp86yizrOq6jwr1JDJMKkXULCytbT5NlAHWo7LrDBo' \
			b'qh3M3YC1g+KcawdZH9ryeqZTrh2wvHks62KsfbWDVX1ow8Py2gGbanntoOxDm4TdWDuo+tCqQ31og1pC7YD60Kq6Dy1H204M07FzjRgaMVwGMWhyG+uJ23jApJdVFchzrDPPsSbPsU6eY01ngkOxqsCeY508xxQrbqmqMOs51slzrDd5jjV5jnXlOS5EmFQV' \
			b'KFjZWth8G6gHEccNvGCowjB3A1YYinOuMGT+4/J6plKuMLC8OhfexVj7Kgyr/MfhYXmFgS21vMJQ+o+TsBsrDJX/WB/yHwe1hAoD+Y917T/maJt5QbYBdrfVauTVhcpurHC7rKD3MwOMkLt+wB35k+XEnyxzf7Ikf7LM/MmS/Mky+ZMhrbM/WbI/WbI/WSZ/' \
			b'MsWKWxpwN+tPlsmfLDf5kyX5k2XlTy5EmAy4o2Bla2GLu0y4XAy4m406muqcB9yxP1l6mJM9D7wr4mVK5YF3LLHOxY9HewferfIrh4flA+/YVssH3pV+ZZmJuIUcZOVXlof8ytKIqBomCEm+ZWlD0swH4FHU7SRxYJ3FRhKtynAHqwywDqN/KC7HWJCC6TNS' \
			b'gBNDsQIpwDGsHNlHUoClmHoiBdz776CHUDiTAsWKW1pjsp8jBQhlUqAIa0mB15mEXU4KhQiTZSdZYFsLW9xlwuWcFOajwiKVxTmRAmmJyKC8nimTyCBIqnOxXYy1hwxI/UvJIDwsI4Ngo8VkgNInMkjCbiMDUkEiA/qgPWQQ1MJEgILzI3IS4GjbSaCNPG4k' \
			b'cGEkQIPOzGTQmckHnRkadGayQWeGBp2ZNOgMkiIPOjM86MzwoDOTBp1RrLglEpgddGbSoDOzadCZoUFnphp0VogwIQEKVrYWtrjLhMsFCcxGHetzJoFszFl5PVMmkwBLqnOxXYy1jwRWjTkLD8tJgG20nATKMWdJ2I0kUI05M4fGnAW1BBKgMWemHnPG0baT' \
			b'wF0ceWyRB4ZGBXeXCiDtfHY6kORGkBM3gsx9CJJ8CDLzIUjyIeRz89GZCHv4FvYhyORDoKtxSw1Fsz4EmXwIcpMPQZIPAd4AfIA4BoamN40sRRBg0mREr1W2Frv4BBOP8iaj2aijqc65ySjzI5TXM7VyUxGdolHjiYux9jUVrfIjhIflTUVsreVNRaUfIQm7' \
			b'sanIYqto2Vx0yJcQVBOaiiw3FVXkwNG2k0MbkNxo4cJqCEQJZkIJJqcEQ5RgMkowRAkmUYKhM8GhWENgSjCJEihW3FINYZYSTKIEs4kSDFGCqdzKhQiTGgIFK1sLW9yVjvIawmzU0VTnXEPIiKC8nimTawgsqc7FdjHWvhrCKiIID8trCGyj5TWEkgiSsBtr' \
			b'CJVD2RwigaCWUEMgEjA1CXC07STQBiQ3ErgwEqCxaGYyFs3kY9EMjUXLF2AzNBbNpLFoHEFwKJIAj0UzaSyaGYotkcDsWDSTxqKZTWPRDI1FM9VYtEKECQlQsLK1sMVdJlwuSGA2KpBAcc4kkI1FK69nymQSYEl1LraLsfaRwKqxaOFhOQmwjZaTQDkWLQm7' \
			b'kQSqsWjm0Fi0oJZAAjQWzdRj0TjadhJoA5IbCWwnAeorcjwyEAcIwVakYHNiGIkYxgkxjDkxjEQMY0YMIxHDmIiB4gkORWIYmRjGRAxjsSViGGeJYUzEMG4ihpGIYayIIRdhQgwUrGwtbHGXCZcLYpiNCsRQnDMxjBkxFNczZTIxsKQ6F9vFWPuIYVxFDPyw' \
			b'nBjYRsuJYSyJYUwixqetp4exoofxED3wS/jrJSWBgZ8SGALTg8vk284TB8Ysm+5y1vI56kI+l8gIp6oWQGsxtDOr60YgEBPoCRPonAn2rs4MncsZ/TWjv2b01wn9KVbc0pCDGv0hLekE/noT+O+4C5Gu0J8SW/qfDjsg6ZStBU6SGxIqH5s8Gw+GGoQTSBQ7' \
			b'nL2fO1tF+AcpKA7KA4lIZ32I+DKu2ckya2KAcLh3xMEqCghGzEccsKHmKIC+oxpwUDIAfrJhA28bcpChPyKMPtSTiMWNYw4I+9FjAc/xN1T1BL6hwn/tdwBPkQA87uMqq/1D5D2fJR+izyIjggOLeZ4hEZwO/G0G+iIDewb6CPB3BdzPsb3HagRz2JVgbvUS' \
			b'MIeUogmicO9lpxt73DOYU6y4RTDHqJOiPIQymlOEtWiOH0NvysF8At4sjbK1gElSQzJk4D0fz9u9PKeCO2E35C4Ozppw4JyDLWttDzSTRpdCczBJBs1B7YtL5yhrwub0XatB2Va+WxRpLyiHtzAoo9D8jByKOdrBojiXwBFwD6yl2QC3Ae5xAZe8rHbiZbW5' \
			b'l3U/4FqKKHkPgMueVZs8qxQrbglwZz2rNnlW7SbPqiXPqrXXAS69QNlawCSpoV0OuLPxRlOd14DLwTngktfUkr/UHnCW2lXO0mCSHHBZ7csBt3SWpu9aD7iVn/QawOW3BMAlR6mtHaUcbSngqgMDbRvgNsA9LuCSR9NOPJo292juB1y6FQGXvZiWvZg2eTHt' \
			b'UGwJcGe9mDZ5Me0mL6YlL6YdrgNciqpsLWCS1JAMOeDOxgPALc5rwOXgHHDJQ2nJN2kPOCbtKsdkMEkOuKz25YBbOibTd60H3MoneQ3g8lsC4JJT0tZOSY62GHAPDFo9Q8Btbcv3rW35EEBDbvMPxUxXALTrlwA0pCZuJcW9l51upHAGaIoVtwjQGHUC0BDK' \
			b'AE0R1gK0o/Zk2OUAXYhQgzUHK1sLm24xJE8G1vPxfDooz3OwDk3JZYyBtUjQHUTUubwu6noPjJPel8J4eFgG48E4i2EcRU8wnoTd1oRMKkhY7g61IAe1MJSj4PyIHMo52hIoz1uJ1YEhqA3SG6SfN6QLgnQxgXSxCNIFRQRIFwzpgiFdJEgXxZYgXcxCukiQ' \
			b'LjZBuiBIFxWk5yJMIJ2Cla2FTbcYkieH9Nl4AOnF+SykFzEG1iJDOouoc3ld1PU+SBerIJ1vyCGdjbMc0kUJ6SKJuAnSRQXp4hCks1oCpAuCdFFDOkVbDekHBpQ2SG+Qft6QLgnS5QTS5SJI54gA6ZIhXTKkywTpstgSpMtZSJcJ0uUmSJcE6bKC9FyECaRT' \
			b'sLK1sOkWQ/LkkD4bDyC9OJ+F9CLGwFpkSGcRdS6vi7reB+lyFaQH7WeQzsZZDumyhHSZRNwE6bKCdHkI0lktAdIlQXrdu4OjrYb0A8NAG6Q3SD9vSFcE6WoC6WoRpCuKCJCuGNIVQ7pKkF5uCdLVLKSrBOlqE6QrgnRVQXouwgTSKVjZWth0iyF5ckifjQeQ' \
			b'XpzPQnoRY2AtMqSziDqX10Vd74N0tQrS+WE5pLNxlkO6KiFdJRE3QbqqIF0dgnRWS4B0RZCuakinsNWQjoM6PSTvn0H+IpHdHW+++K0AP6wAeXVHgF4dCewBNjUUmKm1fYdLhRao7z8fsfVa4MdHMfJjEHyMIeSHfZjxxRRbmvHFzCE/PpRnfDFbkD/04YZY' \
			b'xdzAuQw19O9wfSlDU72Y+Q3neTEI/pCkcM547GSxJ/pYn89xQBmDdBqnemFZdS64C0clB4zldC/mEA9Iur2c8oUfmk/5wuZazAX4CVlPboMduellW8gAE7spCeGwVzUoiRkBxVcsQcYIHC1jBAyBX08L/tcN+DtiuKcGnIrJ+R0Sg/W5qKaFfYRggQeABIgB' \
			b'CPJzvEewX4r0s11VENcBv1OxHJG56mBSdCwZGF0PoerCYnOBokvRM0dOsR4tF6NkQEdboWIs+g6HkHABBobc7Aj2AuZFkJtBuABvN8C2w709ApDtqplIAJEm/TWKnho77oV8EFxWlDALPFmBJDmMAIasx44VoBHhArCiBIoAEZDr3UyuP1ASPELGj2U6N5f9' \
			b'zZlDgL05DACrz0HBBAbMAii4plREJZ27iQdZ4QZsOosLuq6lnis2gMVvjg+yXs44YcS0UCGXYsSwomSgj4sRWY2PwcLebnHBX4fRhhYmurCfGTvqyteWIkR/i8WI67BjAW6EitQZYwfKmP8zjghsBLrVMgZCO86QIrFufIwyh1a3gSt6X4VF4vIB68se3b98' \
			b'mnzoPwbrHuO6uoe7DmHsbYIMA8uQgEXes7qIOVAIyVtroFJqCFAMMMxYAosdcPixdLBsDyx74+/BlYXiTCz+f7wd4MFMqtVq4FFHBp8INiaCDdjv3lZqJGh/b6EF7ZMmv4VQQ71YIJHtxGRRvdRSiJfhCi6ngXimIxzBCZZ1fKLb3Aqi97R93zoSBS8lNFy7' \
			b'eSiChumzhyO3sjFZLKwXjchKn71ss6dco3OI0bN+wJNATIQXtN24B2K0ujswAylgbTmm6gJ9AGpgxhialvWa+pHX9Vm1nO5BC58LvZUEuvr8uThyIWbimjpSQQY0DgVGIAy5tGUlL9SYGRQJhZfPUWg545pSjSSQBwb0Mu4g3ezAF3qCkos9ZeEFGp7gmQht' \
			b'i1tfioJMLMTUZRfLxZW6kCK716cEm33e+Nty2dzFKpK9aVtLQg1M/XcJNKgLhOPuDfoIrpuTFz1uVMMZbu666f4FPXp6aDzxyeukaHANAvT2huWNO4IGq8oXK9DgEsoQe8sPI3ZPulm54Y5hAX/w8pLCIh+Nv2MTCJjj4cB4C3WPjX2gJ13ijoUJ/dnjAuj7' \
			b'PMEBv0vfStUihwjKW9twAvp3HhUsoCy5vm6xDDHMNsSwR0OMHC1AtJOUHo6JFg0ptnUAK1EC7HXKwsTRQeJzAYTdBhDuNAChG0A0gFgIELYBxG0AhNsGEMNpAMI0gGgAsRAgXAOI2wCI4axbJi+5NfJMEeAsM/8t5XSJkp5tu+Pt5ezuXz7ZPwRgQ/fD2DL5' \
			b'GWXymzofzzajY5o8i4x+7h6GPTl9s6fRioceZSGve/W3vN7y+sa8TrffLVK/b3ndyIcekjGvi5bXW17fntddy+t3J6+fuENhy+vr8vq+tUyPne8xm5663o43nUO2J0E+W67Hxy/P9RJX3egmC32m/B8W99y3qiciw3l3LmzIcEalAEzJJ0cDKc4EDVCQz4cG' \
			b'UtxGGWARBmzsW9gw4N5gAKaui2nJvyEGUFa7O/UA7XM6drAboFVf4JJbZmPvwJbnLzzPC8rYF+e9W5bn8esvoe6vkeYhVeOBwDy/scNfy/MXmucxNV2yy/5wpsfPv6gWPyjTw/TVzvo98fzGPnwtz19Wnsc8cB966dy3Rn4F/N7jQGHTuuPdn7w+tg55mNXh' \
			b'OfciowvskgeDYkc4IHZvffMuOsdD7j19z7wzy/H3iNwFtNz16MK3rWveZWf1s+iE27L6OWT18+6ZB2WQMNngsbL97NpXR55gsA25WTHxD7zc33hsOPBB9pSg4COafdCwbYydvYNzAfbTxfTOtiywYdG7xeUBV02dfpGgQGsilv/revTADZMV5s6/yLBtdbgV' \
			b'5QZUTJoMXR4sPzj90MMzFh9O3KWvIUZDjGsQQ03+VyKGaogxjxgqRwy1FDFO3AGwIcbtIMaFooWe/K9EC93QYh4t9LK2iQwpTPd6QHxAcGBkIFiQCAgSocAhCOQIgNmf8jJmPsx0kjOb25PJRsxQlBmqDBATvPEJPCbmkI5jEo7JF4xCqdZQWsVkivaaSZ4p' \
			b'aYZEhQkAzA6x0dz9HiuDgeNyWlPlJ11brN/ZG2mUkJL12jMgAtgVOtYr9LwHbAp9Y/b6PAoX+DSZKV7yU6WorBAz3iJL7M8KtUXczSxi9hjF3nXD2AS5E+MEzDyKgYbuNSw9pjR+MVCkpgtj99ojuZM+nEoFCoIdrPkkIdArDQNgQRcjcFn54fsrv3+w80HQ' \
			b'/bOTtIK4g+WeYKEnW6xBievTwtpLsEq6Bm4VuI6t7TxAA+fHNZu8Jeu1JUdeEwnXLTcgyE5ufKu3+aE/fLaCZ5v5p/MaMvKa1ygogKniL60PI6orqOudnnmrwLWzDM4t62B+uCVCwPzPsdmXptUmwSwL578l/kGS1zwPXPrXs394tadGXTiGGdU01rc0foG5' \
			b'4RdA0XDxR9hu6R8UV2fCUWS7WmRxSOpquYe9XwEvi1/iy+sH/6DoXYdhkRiLwBaLvcU1X7z1e/w+N/0+b7R9n+gLUFDD0GXFYv93e5SFYmIvsUcoFH+gHIRlT9njQCxaltriqHdAIxpRFTTVc7uXJa3518OiLqQ9dViDvkxNVQRJ2gSQJ436z9S4Ah6vcAel' \
			b'nC79ASwP1R95Z+b/67iHY6e75p4zH2NOpmnMmTejhYczSME+GdzWH37TeHapVu5JueoIqRfXBDjxBlXxOgjmD72dx6PRfYHl9CkZWm+OutGni/jpMFuz/WzJvr9jKd90tI3YmhVPb3mDSsVnevTSjZKBvJUcAHWfm2UCaKK78QYNhCtuIA2oKiPAsuCfjwUw' \
			b'O0DD453JEVCnzjYvOz7iM25Q3f6sL7huo4QxUzs6kBiuZ/8bZRBo0S83aLGeBC7ZoP18zQ2kDdOyyeFsMnT3bKN0MVOdPV0uAXfXaTZShmuZ5GAmgTbZ+7VRupipMd8ok4DBb5ZRVHeLG3hg19xAShlbZjmcWcbunm3UzD5TKb9xZgGD3yjDQOeJW92gt8Ka' \
			b'G0g3da295Zkyz4C7735tlC5mqvG3kmeEvWm+Ud2tb9ChZ80NpKJWz78m6+junm2ULtZV8yEVrG7nX5uDgr1SLjLd8g36NK2I7ZPqknjQuy2ckOJai8A1Gcp192yjdLGuRWBThqptfrPMNXSfb8s7nK68l7TZmhQO5zLo13W/NkoX65oUTp/LoJf52W2kytYQ' \
			b'cU0WU90926hPXn+/00XvP5SX0ivTh0hpxNqQTvy/hbSiu0vdpIJ/W4XZuSNKP2J1n6LbQOmQPLaj9RwEuG75Bl2TV91Q38+DclbdRKNp0kgatMC6ZpGztgCMxrobG6l+pkfznVW96O7IRqpf16Jx26pHWlqj/n6JCWR35A1o8CaRyBQz/dMXFRtOaw2xxCKq' \
			b'W7XBsJG192zeDryM7LKujeJO2cV0d3Ajq2wdOnAHrOK6O7iRVda1NFzqgA47dhs2Guee/rc9pX7i9NnZaRFn0YOyjSx+foMhTmFxmN7gMjca/Leun8XFWtl0F7qRldc3QlyklW13oRtZeX1Dx0Va2XUXupGVVfdawUh40fP4bR0DGNMNBIAmMRAabzmB+ApP' \
			b'ng68vjGG1zaMCYP2bZjVhoc+eCPNxRYw/L34p9jDJDbYEO/wslT/kjuO62L8P6QQKnz4hPE6T5aYkooUFFIPzraDd0OoT388jxDN3xPm7pHZnD04/w69RZRvgckdYKi/pgc6ehW/BiYmwgRoeNC5hBGSMEFQD7FxIAbV933k19hmDm3k2DZucewGhPhYMK7F' \
			b'sQA6TWtA1oVV3qQBtUluyIE1oPxTIMSRqmGFmBDi43x/9f8bMPEh' 

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
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LTRU})|(\${_LTRU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\$?(?:{_LTR}|\\_)(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
		('UFUNC',        fr'\?({_LTR}\w*)?|\\operatorname\s*{{\s*\?((?:{_LTR}|\\_)(?:\w|\\_)*)?\s*}}'),
		('LEFTDOT',      fr'\\left\s*\.'),

		('SQRT',          r'sqrt\b|\\sqrt(?!{_LTR})'),
		('LOG',           r'log\b|\\log(?!{_LTR})'),
		('LN',            r'ln\b|\\ln(?!{_LTR})'),
		('LIM',          fr'\\lim(?!{_LTR})'),
		('SUM',          fr'\\sum(?:\s*\\limits)?(?!{_LTR})|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?(?!{_LTR})|{_UINTG}'),
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
	def expr_func_7        (self, LOG, expr_sub, expr_neg_func):                       return _expr_func (1, 'log', expr_neg_func, expr_sub)
	def expr_func_8        (self, LOG, expr_super, expr_neg_func):                     return AST ('^', _expr_func (1, 'log', expr_neg_func), expr_super)
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
