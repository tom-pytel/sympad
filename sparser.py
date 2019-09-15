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
			b'eJztfW2P3DaW7p+5wHQDaqDEV8nfHMeZNdZ2snEy2IFhBI7HswhuEgd2kruLwf73y/PCV1FlSV3dVV1FtLpEUZREHpLPQ/Icklev//LqydfPv375l+4v/+f9r/9wJ3/5/OlX37nTN4+/ffryuXN89e3jJ3zq+Szc+YtnL79+4c+9dwh+wZdfwzte4u8XT//6' \
			b'w5PHr56+YveLx973i+j8W3R+Q85Xzx+/+rcv3Nf+HWIRHOj95Ptvn/8droLj+6++f/nkm797FwT87lv4/f4L9/v0xTff/f3VU4zT9xDrvz2Gmy+evfweYvXs5Xd/hYg/e4FP4O9/fAuhn6NEvoa7/Nov8MknX7948dhLCTy+ffbXf/vOR+hbH2FwfPnFc4wz' \
			b'ROM/3M/jF9+A8+WXLAhwfRGdf4tOFsTT56+ewqe+ffYCzl8++9uzL8HxhIT86juM0TfPMSkukT5V//nq6RMM8OWzr74Cwbx8hhn8BCPw+OWXkHK48fW3/EGfSxBleusTl77v/Bly+cXjb1599zU8/x3K9+l/PgHxo5eTdZ/lEGeAe9eTf3fOT3/8+OnPtx8/' \
			b'/Zm4Pzn3u7cf3//+w4ePP/zjx58//f72Y3LbOd3pLQZ7/9+/uSA//fmLd3/647f3H/3Fr+//64e3H/8r3vvROX95+/sP7z78zK6PH/5fdNGHP73/9OldcP0WXP41b3+Mzt9/Dx/759t3v3v3b/hW8v7j13cxov/8528xNiHSP/8UnD/9+nuI7y9//PzDT7/8' \
			b'liQzfVGSSO/8821Menw7vAYc/vr39x/Le/7yjzS2b//xD+9898fHn//HX/z3p/cxpT9+fPvu/74Pl5/SmP35Przrj19/+vBr+OjbEP5dTB4KOUT/Q3zlH4m8fw1R+vGnXz+EZHyIueDiE3Lhp/fv3ocLV6CSGPz26fcP4a0hb0NcPvwco/vuwy+/vM0uQnw+' \
			b'UcA33eurG207o687chhwKA0/plPymi/dFbosBOvAQ19nHnRl/HPuAeu9wImhbugdqruSnbTdjejUzjmugy/6RY+bARxC0492LxB0z3uJceKlTeoFTufqJf2YvrvpKaruCpzOBXG2HXyOHjPggAhI+jHjNV+6OOGjorsa3NMK/q+9z5he9Tt2gB9ERUCa+5HT' \
			b'rMS192W/4HEj6BsuVhBFJ2nDb3Xx6lEgvaUfs3M+FDl3BU6IJkravYee4kvvTvwFnW5QBhL/5eBvw5cxQuxPsetuJHvSNWak2HGirAy+7NdHjz73uBFYFKT7jsQPyZF+NAVxrhuFMpSKfrT7uubIueclFVh49Rhu6HBDCfqxu2u+dPmHgtp1V65YYM6QVMDH' \
			b'pFeWz+AFz7r7EE/NQvSXEy+fk7m/ml4WT+rpZSVEn3uZ6WX20I2TdYxaLNwcicJDlx4m8XAXV3LHUXAfETrzjpc3EkXnavGV7Duonu4J57LwoMt8d0HxmwkB+KOXBnTZnge8kVg5oG4MnQkl2d3AetEPXAOh2qqhA5QKFRFuBv/oo8nHRh9DPkP0seQzep8b' \
			b'gcVWAJThh8VIPyA6jm3wUqkXOCEpmn6cRK+voxNcgkq7TzPURyzUmm9w9kNVkZRo9y4s6ox5UPIpj3YdI2NPPwbgkCpw36MT5ehEpjxOUxKdH/qEyxvCupHf475mOr3zhSf1Zg93jeWspx9Xpq752tVTjAD+Q9Gi+IADRNTTjwYhM9b06IQ0u5uA9z1VeHdp' \
			b'6V0OIfo+UI0vSo4lGIwQxUm8kFwRQlBBTHIN0JHE6jyvTKy2eGnitx1loGwFPLALrp5dBPDg0N6B3xeuQjkCYOl2qZTxlsPhMjPYvwjqXokpG+lHAy5xYskJiXG1itjVVXcstoGDQPAkcEk/2oZaLqj+Qyp39BObApDpBL4j/QBjagbgEZ3gGvzNa750V/4G' \
			b'vcclyirKhMFnE9C6pg/DC3R4AZQGTbky+hsYlL38U5oSDbDm0unaPa93Xe8yv+8xox1su+dA7E64qnOVzgGaKy8u00dADSeVQXaDC78z7t+6/8H9u3s9vKcHIbmouA86Vu53EM6VI8eOCguUe8Y94p5w7+ldyvod/LtMc1/rO1fqHEgPuhtMN9huGLph7EYX' \
			b'0sWhd5HoJcAWfMdduxc5cIFSA57uNRB1BfkAkAaBAeJcqiCwe3MP1OSS1Ls0jS64e7gXEBP3uIRv9N0oulF2I0Qawrok224EmHN0DMQ7uidNZ91hOzt0duwGJ46+G9zbBfy7IjhCpTdY0x2WGOWalK4x6WoCYLEZHRMDeFtHybJzuWtd/KCd5GKrsdHmhAKv' \
			b'gkS6F0K71DmvofK6aLn8uoKMch6vryDN7oZLNpxANHBb7egupPQaKQ1PA959DYyG1xZOLYNPIIOvRsqwHs/QZKSccrmA+S4oXwfFwXaUgwNlrLBUCCi3e/8wZtx1q9CnmN8oYMrKkau2r+I956LibNSYi5m0Wc4k35pkSaJBkrkEc6nVRMaScvE0jCR6OGIk' \
			b'tK8dOyrvUNpQNAKrxz3GRBiKiVD3/WFOuS81iBCtap9g1X59RTW45c3p5c0VRg7bTabl0anmkeg93KMjiAyFFUTDIvGSSFM/Jik7eoqygpMWluOQKYiVOwvCdwewTkDP2X2xc2ltJf84JV9ywZfc6sd+GrZzhoZWp5lnrouGTNJDklxMegXJdU8BwShIo2o5' \
			b'c6ycsS1nTjRnhpYzJ5ozY8uZU8yZq5E7Lj2N2l5h4mmYD0d9W+vgFHOt9yPx2FWBbMMB+zeooqQbPHTfc5uPx3A1Z67SLW9PNG8V5ygPCY54efSInVh38wpDE3D5Xo3XYUnWYY004j1SRRgl32atRk+dn6te8EC55OBe2+FfS8FGHiFVdKl7P4rOb8dvXnKG' \
			b'jFxeLamQLDWSoeqD8qmNoiyTouViZqlQDqS8GRjcB8Z04cs+KSquFOtnNbOCoaJsKLihQBavRhd0B8lxsYHBf5e88xapkwbVaEOqDisvVQxUMQ3BnyEcs2pGGr7mnr1UqKJZqmhWX2jhsKwdRouANOWkeCIE0b71qKkoCd/m9HDUo8Vra1WeXqsSLXoEmfKI' \
			b'ZpxzInkiyUJc6pYnJ5InYMMm2GLKnZvw73mYULaacDKZAZJudH6imTMgZ4CJZsuiE80i1VrDJ5s3zt3y5iTzBs3LhTdhFmzC7M4tM45TURDFWHDNZO6goy4aS/qxvl6Z5QFjyAPXPoxby/HDylxgB+c+DfxpiAG+SFiKJ2Xoatd7qGWll5mb//OGZwvBqIXA' \
			b'NLSycLuckTuSPatwaPyZ9Tw8OYZG6oM9BmZak/fWmoDABnaVVOS9np01umiPRIImI/4rtEzCgs8z4AZLb+AXjfyinvKl5cdaDb4XIA1NN8EtJZEeSaTJaK+MVJPRZ2Wkm4w+A1KKhtlG3yWltk8bNzi9rioagnEmtYG3E82k12CNJ5o54xSLR9nkUh0iwbah' \
			b'lrCO08WLA8xMBRtZiomZjqXuyYzFd99zP4emZZ5AYvp+DMaOgowdBRk7ChpuEDRWQXcND1UYAhAy0Trv7H4Nppuo5WvzNE+W0KxohiJHaEaMiaHmuaMAGqNGM2+w+1aXlHxapOb4UbnqBdtQK+YifUFcZGUDunvv1BoerTb2gkqaGS4osVa1anX/1YpVD3Z3' \
			b'SSVNt5J2/6OSPfViNdtr9qyGd503mo2BJ7rq6crlkGRlvLwmOw1Jisu2hMIpZrGLpyQzCco2PlnKPRC9ZCs2ee1NqmRcbhKsgPgSToJzX/B7eno5lwXIgGQJJzAiIH8sVthIaAttHa9bSpUc22wtC45ksCgNVxyuIi7WDJ/S230ItvdAs42GnUfNLiVbbTka' \
			b'dQ3EOQNXkZGrSM9VyC8q00t/R/XMPxUdA/jSY3SiZovS/ITgV0gM1QazT7A49NwQHamVMVJ+6p5yTmOmN1Wc10yqtvILdywRLpr93jJ5oSZWsN5Tkt5Tkt4Tpchj3lgFe1hpgRbMZ/g0VCfRmPUNLuqCNZVnygRrb26IEvZaesYQ2BsCe0tV3dLHrQ59TsV9' \
			b'TuWNZamLo6iLo6iLo3zXRrURhXtfxxrFf0W5qT0xcwZGm2UZeBfzDHYo42Wy4KxlsCRQ80YDdqRiQF90KVNeM48P0TogWCjVtW9pX8RoGtYUzTVF++4F1RRNNUVTTaHTSGexo4fgW7o1gk6zfrl4a4ZnTYVfU+HXrZ9ytG6iwApTLkyk2woFJ5plwAmappIZ' \
			b'v7OMgQaNCwGLJ4aGDaTRMEEZrnaGqp2hagePdaEUmGYlOSUjTR129xHLNINnWg/wCgXObQHLIrZNjJUZsSQ3l2iL7RyaBRnWXPSyHbBAa5qVDguAQs8YuoOwQFoo2CBAKscDvXPgLKEGGy8c2mtueWk/yxJXWaPIjC2TKpnUN7lUMcD3yjRpHKFEibQLCYuJ' \
			b'7qgo4hkCkEZq18FGnZ3AzVpAfwQbtoyYVGIjg+Q3oggoeRZiC9wngW9hl98eGDjGf0CB42ARiS+VUZkLFuVPwp9kIBG3y17sWUikZpQFyoUp1s++BLkFjoEq6eINy6HCWqiwECosBgorgcJqmLAUJqyDCYtgQm7D0rWwbi0swgoLsIKgoADBbonQdICNH2CL' \
			b'AVjMHlYVhiWFgXVhCAiWv4WlmmGdYOiNux6QgNnV0IyAdZRgUQtYzwLmpcGEUWgGwDgACBXmZmPhchkH4gX5QvlxBUhA4YD5kS5tAmZtg/YCLKIBfcA2HjLbyVSApTAYCTkhCrAOB2NwsKuGWarjzmUy7K0+wK7DuOMy7NW962i7Xdi9ucMtaWEb4wH26t3B' \
			b'lsOwpS9sfw4bvILMadtb2P8X7koMDy/cCdw2GjcaH8EX3gil+gYaO7jrco8fBG/Ywhd2Wx7hSQE+At6GgeAlI34eN0p2/uOAOz/jbssj7Bnv3ANuK47b3joPTJHEzYZxZ3fcQR4igzs64+62uBc6tNgwfSMk1920lhMB2+binvU7TJF7xpWRG9hr2OA+ygL3' \
			b'KcZtkEFtj9umwxbjsM/vABHdwZtwL/Odwm2zcad4iCFIUMGe3SAhlAxuHOyec2dXmm4GcONXUC4oKdwZuqM9kzVuTn8zQrwl7w4OkXPXFvzgAUwdZAvsluyg68YVgxvYm9vC7uIgI8gyvym65RgAeuEG2gqFA/8gBxS8+xnwGZQ0/sBrIL3uPPRvADwAMhpg' \
			b'nDlgNLRoaHEItBCAFjlOiHmowKZTaBIFzHCZxLAhcuSwhwePop1WwRJoiGEjrIYpagGu3BeeyDvClKGCK5B5w0J8MSBqU6KJWYInBoM56ZsKqpiIK6aGLOZ+sMVQLKXp4l8VX/BGDWPMIpS5X3AxdwcvQwViUDYLYab7l34EFGUeAUkN0p30/4Jx5R7soVE2' \
			b'6xFox328Og4lY33FECONO+5Dph10Upfik8khyvdGq71bhqtJzzKqXw33lVMAg64r9mJ3oXsch1ZTcOuLXqgf0BwSsJMMeN4YNTFQDQBYGSSB/ccBFGEXbhh0nQXH3QqAdGHATjYDSvc8DJxuBsyBQRNKR78ePGHJiFUAagoQ1QmQigJM3T3Q0QZQhWoOmdOX' \
			b'uNr3CbAC2jiRw8nD60gIiycCWSgfPSESnnHYWxHW4mcIbilYOAL24jMT8EUYIvTFUXZC27UojPEY6RUTJKbR+/g/QeYYVyjOfe3YKRLOEJwpapdfyL422uQl0ZfwHU4w7dlDPN4PoRHu/Qc96nMQAP/wxh55wDvn6ICyfCkjhOyOvMBey9kB8z/SQyYBsHpY' \
			b'zxUUpUgXLKYZuog56zkDw3veoIdT7gixCxxC7GHUI2B6IhGAvEdYDxwOPALOc3X4kRPS/+K6bRN26dc0bm9JKv2ReIVIxTOKWs4q6djlVmZprEKsIof7ZBZBzCJKZgGpiCWtdqgVgglFMKEI5pPYfKdQ4Yh8Iqp8EkcKMDy1W7ZQCrXr4TQhlDQ6EzIJd6Qp' \
			b'4x7vafqAJ5HBEo9Uw46YVigwuXfaQ8g4JA1F+xYl7EHeJokbUgeHnmMOsYo5fL4mzEFeK5hD5MwRE7SNNqjE59Qh9jFHlI5nDpEQR9nn8OnbxxoVstC3GQa5JVMcmyNar+OMex2auEFPeh16ETFoCgh5r5kYNBODjsSgsyMSg64Sg47EoDcRgiZC0BVCSKMx' \
			b'IYRwR5oyzvGepg9kvYpqwNFOvYgJ+rIvkYZBHmCnpwK6NEmskAo41BwV6FVU4HMyoQLyWkEF+RB2kqZtVFAMOFGC5mggSsbTgE5oQJc0wGnb2nkwjQ8aH5wjH1jig4muEHwW8IGlgJD3lvnAMh/YyAc2OyIfVPWJ4PZ8YDfxgSU+sBU+SKMx4YNwR5oyzvGe' \
			b'pg9kfFANOFa8mA9swQdpGOQDdno+oEuTxAr5wL9phg/sKj7wOZnwAXmt4AOb80FM0zY+sAUf2H18ECXj+cAmfGBLPuC0beUD2/ig8cE58sFAfDBM+GBYxAf0KOb9wHwwMB8MkQ+G7Ih8MFT5YIh8MGzig4H4YKjwQRqNCR+EO9KUcY73NJ0yPqgGHO3Ui/lg' \
			b'KPggDYN8wE7PB3RpklghH3CoOT4YVvGBz8mED8hrBR8MOR/ENG3jg6Hgg3366EQyng+GhA+Gkg84bVv5YFiuuj4bVlCNGC6HGARZFcIpJwZ0emKACzCsn6EHQbeoDhE90OMCz0wPFCocgR4w6IQewJfpQWzSJ+An6OGSHrJolPQQ70hTxjl7UNM3UoaoBxzt' \
			b'1IsYQhSahCxMv4tOZgi+NEnEgCF8qBmGoJctZYiQmZEh2Gs5Q2ASI0MkadrEEBSfyBCUoBmGSCTDDIFxZ4YgaSYM4dO2lSHGxhCNIc6aIUjtLCZqZ5HqnOECGELMMISg4JKC9GTlRwwRNc8UKhyRIaqaZxE1z/Tu1QxBGmdR0Thn0ZgwRLgjTRnn7Lamb2QM' \
			b'UQ042qkXM4QoGCINgwzBTs8QdGmSiCFDcKg5hlilbg6ZmTAEea1giFzdnKRpG0OIgiH2qZoTyXiGSFTNolQ1+7RtZYh+1yiiUcRZU4QkipATipApRUiiCDlDEZKCSwrSU10gipCRIvIjUoSsUoSMFCE3UYQkipAVikijMaGIcEeaMs7Zg5q+kVFENeBop15M' \
			b'EbKgiDQMUgQ7PUXQpUkihhTBoeYoYtXshpCZCUWQ1wqKkDlFxDRtowhZUITcRxFRMp4ikukPJM2UIvj+ZoroT2SKRJsf0bjijrmCLJXExFJJpJZKguZHiGR+hCC6EHF+hCBPrFNstSTYaklEqyUKFY7IGFWrJRGtlsQmqyVBVkuiYrWURWPCGOGONGWcswd1' \
			b'SHhGGtWwo516MWkUtktZGCQNdnrSoEuTxA1Jg0PNkcYq26WQnwlpkNcK0shtl5I0bSONwnZJ7LNdSiTjSSOxXRKl7ZJP22bSwDm9puPch0qG+C8msC8A5CMaz0FxAqseLhESLcEfwJyHL4YshCKZwYKr4hCJIx9vaEXFRqqNVC+BVCWN0cnJGJ1Mx+gkjdHJ' \
			b'ZIwO3C62eCJShWLOI3WSR+okj9TJOFJHocIRSFVWR+pkHKmTm0bqJI3UycpIXRaNklTjHWnKOGcP6pDwlFTrYUc79SJSlcVgXRYGSNU7mVT50iRxA1L1oWZIVa4arAv5GUmVvZaTqswH65I0bSJVWQzWyX2DdYlkmFRlMlgny8E6n7bNpFqZTthIo5HGOZKG' \
			b'IdKYrAAi0yVA4AJIwySkYYg04tidpCskDV4RhF4i8OxJw2RHJI3qKiEyLhMiN60Ugp+ghyekkUZjQhrhThoMylaZAB1SnrGGqRzIGqUXs4YpWCMNg6zBTs8adGnSYMAaHGqONcwq1vBCT1iDvFawRr5USZKmbaxhCtYw+1gjSsazhklYw5SswWnbzBr75hU2' \
			b'1miscUasQTNLpqvQyXRmCVwAa9iENSyxho2sYekhSQGRNXiWiYyzTChUOCJrVGeZyDjLRG6aZSJplomszDLJojFhjXCHa+zMgaRBrow0qmHHiheTRjHXJAuDpMFOTxp0aZK4IWn4N82Qxqq5JiE/E9IgrxWkkc81SdK0jTSKuSZy31yTRDKeNJK5JrKca+LT' \
			b'tpk09k0+bKTRSOOMSIOmn8jJ9BOZTj+BCyCNISGNgUhjiKRBr0HS4KkokqeiyDgVRQ7ZEUmjOhVFxqkoctNUFElTUWRlKkoWjQlphDvSlHHOHtTBlZFGNexop15MGsWElCwMkgY7PWnQpUnihqTBoeZIY9WElJCfCWmQ1wrSyCekJGnaRhrFhBS5b0JKIhlP' \
			b'GsmEFFlOSPFp20wa+2YoNtJopHFGpDESaYwT0hhT0hiJNMaENEYijTGSxkgPSQqIpDEyaYyRNMbsiKQxVkljjKQxbiKNkUhjrJBGGo0JaYQ70pRxzh7UIeEZaVTDjnbqxaQxFqSRhkHSYKcnDbo0SdyQNDjUHGmMq0jD52dCGuS1gjTGnDSSKG4ijbEgjXEf' \
			b'aUTJeNIYE9IYS9LgtG0mjRXTGBtpNNJ4wKShSBOuJppwlWrCFWnCVaIJV6QJV1ETDgWZNeGKNeGKNeEqasIpVDgCaaiqJjzZV0Ft0oQr0oSriiY8i0ZJGvGONGWcswd1SHhKGvWwo516EWmoQhOehcHNSdnJpMGXJokbkIYPNUMaapUmPORnJA32Wk4aKteE' \
			b'J2naRBqq0ISrfZrwRDJMGirRhKtSE+7Ttpk0KjMb+0viDV2hjhXr7Db6eID0Ick6WU6skwfyjN0OMlCWiYGyJANlGQ2UJXlit4MNlCUbKMtooEyhwhG7HVUDZRkNlOUmA2VJBsqyYqAM5TDGY9LvCHekKSOdHgOPV7FE/Iq7A/U+ak9g76P04t5HYaechcHe' \
			b'Bzt974MuTRJD7H1wqLnexyo75ZCtSe+DvFb0PnI75SRN23ofhZ2y3GennEjG9z4SO2VZ2in7tG0lElGZ/9iIpBHJWROJIjW5mqjJXQiVasoVacpVoilXpClXUVMOZZg15Yo15Yo15SpqyilUOGJXpKopV1FTrjZpyhVpylVFU55FY9IVCXekKeOcHgMNYXHY' \
			b'wCMjdUhqT2CHpPTiDkmhL8/CYIeEnb5DQpcmiSF2SPybZjokq/TlIVeTDgl5reiQ5PryJE3bOiSFvlzt05cnkvEdkkRfrkp9uU/bZh5pkyTvYBSL9z9uLHIXLCL3MwlMoFs2aZL052KiPxep/lyQ/lwk+nNB+nMR9eeCXoN1jPXngvXnIurPxZAdcdJkVX8u' \
			b'ov5cbNKfC9Kfi4r+PIvGZNJkuCNNGefsQR1c2aTJatjRTr140iTrzwU8C9HwkyfTsDh5kp1+8iRdmiSOOHmSQ81NnlylRw/5mkyeJK8VkydzPXqSpm2TJws9utinRxepHOMEStKlCzsQqYhSn+7TuJlU9m2M2kildUlOh0xu2yWB7UJd5sApJxHwCSSiaRlg' \
			b'3FuUSQTcLrZ4IhLRFA7KAZ4FXzsSwa8QiVCocAQSwaATEgFfJhF691oSwU/QwyWJZNEoSSTekaaMc/agDglPSaQedrRTLyIRTFzSE8nCAHl4J5MHX5okbkAePtQMedDLlpJHyM9IHuy1nDwwiZE8kjRtIg+KTyQPStAMeSSSYeLAuHNPhKSZkIZP22bSaDPL' \
			b'G2lcCGmQPl1P9Ok61adr0qfrRJ+uSZ+uoz4d9slkfbpmfbpmfbqO+nQKFY5IGlV9uo76dL1Jn867ieuKPj2LxoQ0wh1pyjhnD+qQ8Iw0qmFHO/Vi0ij06VkYJA12etKgS5PEDUmDQ82Rxip9esjPhDTIawVp5Pr0JE3bSKPQp+t9+vREMp40En26LvXpPm2b' \
			b'SaPNLG+kcSGkQcoPPVF+6FTzoUnzoRPNhybNh46aDyihrPnQrPnQrPnQUfNBocIRSaOq+dBR86E3aT40aT50RfORRWNCGuGONGWcswd1SHhGGtWwY8WLSaPQeWRhkDTY6UmDLk0SNyQN/6YZ0lil8wj5mZAGea0gjVznkaRpG2kUOg+9T+eRSMaTRqLz0KXO' \
			b'w6dtM2k8yInlA/LGrlHH2VAHDMXe3xKRRB9iQh8ipQ9B9CES+hBEHyLSB5R/pg/B9CGYPkSkDwoVjqjtqNKHiPQhNtGHIProeY454hwUAvySV3vg130kJnqPEFVpythnKdFBBJneoxp2rHix3qMgkiwM6jvY6fUddGmSuKG+w79pRt+xikhCzib6DvJaoe/I' \
			b'iSRJ0zZ9h0WVX67z2EcmiXS8viMhE1GSiU/fZjJpE84bjVxID4QU5nqiMNepwlyTwlwnCnNNCnMdFeaaXoM9EFaYa1aY66gw10N2xB5IVWGuo8Jcb1KYa1KY64rCPIvGpAcS7khTxjl7MLqyHkg17GinXtwDGYoeSBoGeyDs9D0QujRJ3LAHwqHmeiCrFOUh' \
			b'P5MeCHmt6IHkivIkTdt6IIWiXO9TlCeS8T2QIemBlApyn7bNpNEmnDfSuAzSgN1vXebAKScNs0tIAy6g3O0iaYDbxRZPRBocAMoBnkXPLxF4ZtKgUOEIpIFBJ6QBvkwa9O61pIGfoIdL0siiUZJGvCNNGefsQR0SnpJGPexop15EGpi4hDSyMEAa3smkwZcm' \
			b'iRuQhg81Qxr0sqWkEfIzkgZ7LScNTGIkjSRNm0iD4hNJgxI0QxqJZJg0MO5MGiTNhDR82jaTRptw3kjjcKRB1pb3Sx79ZwhkKEhkSImELK3MxNLKpJZWhiytTGJpZcjSykRLK0PhkEjY0sqwpZWJllYUKhyRSKqWViZaWplNllaGLK1MxdIqi8aESMIdaco4' \
			b'Zw/qkPCMSKphRzv1YiIpLK2yMEgk7PREwnmSxA2JhEPNEckqS6uQnwmRkNcKIsktrZI0xQKznk4Keyuzz94qkQ8LgAphZJTU5AqLQvrQdl7Zt9uu8YzSnwuXHGUHxbNkkGN3O2BkF8bF9efGragLoiddEJ12QW7Szke6hyIUU+52aO52aO526NjtoFDhiGNV' \
			b'ZbcDypaOvQ69qddx402sKt0OKnjxfzpeFSIpTRnveE+TxLKRqmrA0WbXUE6ALAggZdHvgAhROIwaEAY5mC74PvCFj7+mrod3zg5Yrep7hExNBqzIq0oZnJiMMXTe9cB0ay5U20asks4HIpDatxp7zIAwZJX0PnCSD+Sae7Doh/h05nwBfAAQFgjDXQPCjEAc' \
			b'VGUfoe4lEofctwfvaRLH0ckiEIUnCZuQgycGJoQHQwbHJoK940+Gug1m0m0wS8AfCpDhroLhroLhroKJXQWTHbGrYKpdBRO7CmZTV8FQV8FMwX/aPQiRkqaMZ7yn6aVZx6AacLRTL+oYENb7XgEnbZcOKRnqBhjqAJg9rX+zqvXvxZi0/slrRevf5K3/8Ir1' \
			b'TX6TN/lv9k7QSz7kh5BM0uA3BXT7dO1r6nMLHwF63+TuBtANoE8CoEmrbCZaZZNqlecBmh5FgGZNsmFNsomaZDNkRwToqibZRE2y2aRJNqRJNhVN8hSgQ6SkKeMZ72k6ZQBdDTjaqVcNoFlsGUCTltiQftjsUQ6bVcrhkEUJQJPXCoDOlcMxcesButALfwag' \
			b'44c8QCeKYVMqhn26lgL0vonSDaAbQJ8CQFsaPrGT4RO7aPgETJZ5+MTy8Inl4RMbh08oVDgCQNuq1tbG8RO7afzEktbWVoZPJgAdIyVNGc94T9NLU4CuBxzt1KsC0F5sKUBbGhixNCBi9wyG2FWDISGLIkCz13KAtvloSEzcaoC2hQ52P0AnH2KAtskwiC2V' \
			b'sD5dSwF636Tk0wToNjZ+bDA/hbHxvYAuCdDlBNDlIkCXFBCAQzKgSwZ0GQE9PyKgyyqgywjochOgSwJ0OQX0LBoTcA93pCnjHO9p+kAG7tWAo516peCeDoVnoQDnSZoM9eRtkkgh5nPoOdiXq2DfZ2QC++S1AvZlDvsxQZuGwG1h6U8JmoP+KBkP/TKBfllC' \
			b'P99fAP3ZKPe+KcaNAhoFPEgKUEQBakIBahEFcEAAEcUUoJgCVKQAlR2RAlSVAlSkALWJAhRRgKpQQBqNCQWEO9KUcY73NH0go4BqwNFOvWYpIA2FFKASCiBvk0QKKYBDz1GAWkUBPiMTCiCvFRSgcgqICdpGAaqgALWPAqJkPAWohAJUSQGctrUUsG/CcKOA' \
			b'RgEPkgI0UYCeUIBeRAGaAgKIaKYAzRSgIwXo7IgUoKsUoCMF6E0UoIkCdIUC0mhMKCDckaaMc7yn6QMZBVQDjnbqNUsBaSikAJ1QAHmbJFJIARx6jgL0KgrwGZlQAHmtoACdU0BM0DYK0AUF6H0UECXjKUAnFKBLCuC0raWAfdN8GwU0CniQFEC2MXZiG2MX' \
			b'2cZAwWLbGMu2MZZtY2y0jaFQ4YgUULWNsdE2xm6yjbFkG2MrtjFZNCYUEO5IU8Y53tP0gYwCqgFHO/WapYA0FFJAYhDJ3iYNA3WcQ89RwCoLmpCRCQWQ1woKyC1okgRto4DCjMbuM4VMJOMpILGisaUVjU/bWgrASbsOo/dsu3POTNDf/y47mxlBr2CF3QNh' \
			b'hv6e2QEACDY7VKT/hTpS0IQTiVjEFPgq1hkIpgrBVCEiVUAykyMuGVSlChGpQmyiCm9ELypckcVjslIQfBmiTB0GMXPgQkHEFj3aYrtiMZL06uFHO/WaI40sFC4XlJAGe5s0DKwVxKEz0hjz9YL2EgcsWTVZM8iLP5IHe61YMygnD5Sd4rhuYQ/BL1muRk7k' \
			b'xBQiEgoRJYX4FEYKQR/4dTzifgeBvxL9HZcIspwXBplk6F5PeWSOQSwSR8+UwRyREgSxw0JqmLPlQRYAtE8a/bhYVs30JjW5UWxqsw9+lzbIU7hdCrMpxI7rYXUxnHoI9fCZQqeHzGEvXC4ASq7ngmejemAMSFiBQY+BtwDAz9vAeKi7KRevAcyq2q/klis3' \
			b'bPW9F3tWtFgzuFkBNCnKAMSsh5YVmBKgJOBIDiIePgARxhoi7GlW3g8o+NahK1UVaAgtvFOHCFd9XXm6NVSA0KtwUWt5aYYMsQA2PtPMoqbTw8WOpKnUsyptiiGQRlWaS5w0lghYTlPtDoApotwhMOLKBFOUxAIF2CJsvxRfXDRXtDj0feNL1u9koNkdvh0C' \
			b's0hdLHoXjd5lxd2CTtn92wA4ruQdtn3yOaBZADK+G3fiQBPwxP8z6EB3/04aL8gOLiUCukSyv5fGjJKHAB8916gRuOjUxkZN9y9XTB+5FEGHx0V+XYdn+Bz82EO3cBh1RII65gJ7QGpPsyYdSILeuSG0MbBqz66COjQFXQywwyDsOgh7Ntp0VR/33x8Glajy' \
			b'ytWoJI+ATAGJREQiyMjL7koJ3JhhX7MnWc8ZJKdpfEagtGhjsxKL4pgmhoHHEexwoYW47wxcKGwlie3jMi5368P3dwJTDFHQQxT9HphSDwCq9Mpe2FyjqNYg2t1Po2imQaRS+EF0OoGGUdn7wkwczR74UfIBQZDAFW/W9b7GmQZQtfEDhWlpr0ue3jjvDJK4' \
			b'Mg4J7CFqsJhkf4zGT6lxu6cGkEujAJUvqHLk0jGetDFkZhDGN3ruorFz4t2vKcqA0RVqUW9oXSOljtbiKdRV99vocV5o/Ig/xXSXhQ2g0PiptnkGbuaUjRvVvT42EM0ZIhxU+fQQu136EIM7EVGwaDw0QEHrD7TysGjRcV9KqKM3WW7VaxoOpITq/jU8ckSE' \
			b'ozX6+EjxOXRAw6vbtlMeCFKsapesRIpzaXvMtzsMmm0doL3xwHCCU728hbFcW+3StwkgnCjuFSPkgfozW+3LS+vBe8ILGD1/AJgBS+ufMnBgNOBbh+mupPCBIw4bMQSK670CiSAhrOyvrEATuxFN7P2iSYIksNHG0Vod94gkDUVuax6XI0g/nkBn5d4B5E7B' \
			b'Y9gIHsPxwGNo4NHAYwt4yAYehwWPcSN4jMcDj7GBRwOPLeBxAsMfZwUeLjdOfpT03EdGTxgdThcYDokCAmvIyY6BHrjWd/9yNeERIB+oSVysGgCcIgAcQIH6oEAA685hMICq4VnpQWYw4Ha6Uts/Quh1FekR4CbigWh40PDgnvEAS+uJNQouEhGMfOSwGXFA' \
			b'NhxoOHAQHMA6/2A7BxeJA1o9cuiNOHACBpcNB84EB0TDgQeLAw/AnLLhwAwOzO0xft+YgFX4JMYN8cmTgQSOzV0hAr5+JSIIXGKgm+y7HbHB77U9t8k2osZGG8uGGieAGsdFCn0ySKFPCin03SKFPljbYRE+bLSabPhwmfiARe0MNZC3xAeqgQ+sb6HUI4R7' \
			b'V7jBQXiw0RCy4cEl4QGWpbO2SFiGByiHsxlrUKCNhAo1QDtBEh5stG1seHAJeIDhL8NEaT8goCDOb/RRuhYCbLiAu1kIwAPTzBUbHpR4gCXtsiwWL1IZIaGBsCMcaFaLF4oDUItOxmbxJGAAXng5INCPj5AKXJUAh0I0aDaLl4MGUCyPb7F4smhwaY2CHkcR' \
			b'0UTBNJPFC4IB2WCgwUAVBh6AxaLLprBY7b1CQm1LyHteoLZNd9yyjpO7cMdwFKiAenxMwIAOzhxs3GLuszkBk8ZNa8nqmf1nT7UN0d9hO8IW23mcNWDgdsLF/0prJniiuhXrA2hqbNtGdUV7A6UTN+hQn293WPvIoTg2O07A1LGhSUOTNWgyTv7XosnY0GQP' \
			b'mowpmuhVaHIChpENTQ6IJueNJJX/lUiC3aGGJDNIAtJZvqxDRJGhez0idCBuMGgQYkjECokoMSA+JOBAyMB1HOuj5ToouO7V6p2hOob1o6gTWR2wsMm44fLti3Yo1aFES2/dA2UYSiZtMKvrJTaW1ljGWDOGs44M5Xk1uyGnlc+RaS4UQt9h53G8lWgJSj2I' \
			b'agJMAMJM2P0Kgc8A0UTwWOvuRvKQAKztIQcEv5UAKsmOUBUXZcl85ahljatft8qaYSZ3xDnkkIiYPMklD6f3l1N999qAeCQmG7ai1gZvCHfDNTu088d4ywG9ZfdaSKBMJz30UM5pYEcqYcY31+58dePeCSFwiOfGvQe3oAfuNrAjK+xwKGDnVZd16YbNYR94' \
			b'2DwUtj3G/c8HeDNsHE87Ofe0t2rYsBAaLdAoA5CMOzKHrdphU0DY/Ri3T8d03cjbx8e18z7/hx9T8DEz/znaRc0s/K6CZl/5F7dJGyb33B9GQ1eiISAmjn5dxXLZC0uRLo4V7l7gB7JxNc8+ianh2LpqHf6gNeBXHo3/evaPQuxwuBrcsIYn+EOfUGOSzO2T' \
			b'BDCxOlWuGb74D9rQM/cwDXZLGvTnklFsfzSbLJhimiXNvfAzf9BBmPpi0x2b6gqb59k912BFFyZ4qCR4N5tmB8/QJzJZP2i/IBzqQ59jRwa50DCDFhqusAVb5QodRQXWy1LgwkewsGcQHRjzwsCeiziJEcRpSJyOCfaK1DEG9Wl2JF4gnChil2KY/i38frJv' \
			b'gCTjH9DcWPyRqqr+X4b9XPj0uc/5jYVr/ivp/eKtmOXjaZVx6Mcf50BpONdp1gBUe1ZqAQxK3UtNgMbiaRwwIjHxGg/4BSoJ/YlVDNUd6SBxiCAOWKLc3mX1UA+0hpiOjhHH/vq7O6BvdacfWHpQ0ZCHqinQJzxMZYFO5iEOGGBd/RhJRZUVBsZL77zawGju' \
			b'g6s50DZNDpeGcewKz4MfMDpx199YcFBhqXUA5wvIohbGQSoS9BjyAwZKpr4LD1BUrH+MRGRafVpcn0BtcpkHlZVax/0UqhMoIY98kICGVpmWVibQGl/oQWWlNkJwy8oEheAwFUp1hz1Adb7+MRpI37VKtbRSgYrpQg8qK7XRhQNUKiwEh6hYYCJz6APMUdY/' \
			b'RvKaDD+0ujVbt2R3qQeVldp4xKHq1u5Q9Ut1d3GAZdf6x0hsbcBieRXT3aUeVFbWjVeYrUqRDTXN52Fe20y3/ACbt3UPuLgvDAoWkck1CbONbCyveEN3qQeVlXUjG5srXqUc3L4Sjt2dHqkl86Y3kITb0Mji2gjGgRd6UFlZNzRyUrUR5jqc7kGWgG1AZXlV' \
			b'1N2lHlRW+lZWXIoBiXo5U2b6WG5AD0dlx/0jHJjuvA+hQG+pp9665qIyJVYbg92B9dftkL4GFWO3/ABb+VUPVA8/qWz1czgZLE4Ew1xZN7zzUHIF5hg+sIOyo2ZCfwbZIbuHdlB2rBuZuaPskHJdlgCFLcsW1R3lAIK9ZSDKntq0iAVNk5PIobRBuj+XdLfq' \
			b'gHlRa5+55bH/k5RX68ZaHmpe2e4hH5RTG+etPLCcGruHfFBOrRsxuYAZRrCSxPoDV4tI/re9pf7e6ReSyyzMohflB826PNVZNscrBaI794Nyfp3dyyXkvO3O/aCcXz+Ycu45P3TnflDOrx+wOfecH7tzPyjn148NnXnOw+JgZ35QzuvutRQ4n5vh3wQPRgUL' \
			b'HiBW9Bxh9WO64TpzadlwwocQMDMXtsKExd1w+TF+zVgP7TI3/6d1NnaT0JCh+ITL3uJfSDLQ0X261AoWD/J3lJYWVSpWaXHyRWmEooGTeME3LvBGC6vxomqosfKLqbmva6pErky+Lhaag0gIbfGFMvkUlNaeSiOPYbjvvMa19XY4mwvWdGOLWvfAa1QVwROo' \
			b'DqL5XrBennt+cOeRQ5q4ggwJHfYkFkaBj6VhR9iV1L0FfAZq6cG+hN7HhXlz/f8BSqqNjg==' 

	_PARSER_TOP             = 'expr_scolon'
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

	# grammar definition and implementation

	def expr_scolon_1      (self, expr_scolon, SCOLON, expr_commas):                   return AST.flatcat (';', expr_scolon, expr_commas)
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
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                      return AST.flatcat ('+', expr_add, AST ('-', expr_mul_exp)) # _expr_neg (expr_mul_exp, num = False))
	def expr_add_3         (self, expr_add, SETMINUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, AST ('-', expr_mul_exp)) # _expr_neg (expr_mul_exp, num = False))
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

	def expr_ufunc_1       (self, UFUNCPY, PARENL1, expr_commas1, PARENR2, PARENL3, expr_commas2, PARENR4): return _expr_ufunc (None, expr_commas1, expr_commas2)
	def expr_ufunc_2       (self, UFUNC, LEFT, PARENL, expr_commas, RIGHT, PARENR):    return _expr_ufunc (UFUNC, expr_commas)
	def expr_ufunc_3       (self, UFUNC, PARENL, expr_commas, PARENR):                 return _expr_ufunc (UFUNC, expr_commas)
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

		if pos and rule [1] [pos - 1] == 'expr_commas' and rule [0] not in {'expr_abs', 'expr_func', 'expr_ufunc', 'varass'}:
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

_RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: # DEBUG!
	p = Parser ()
	# p.set_user_funcs ({'f': 1})
	# a = p.parse (r'x - {1 * 2}')
	# a = p.parse (r'x - {{1 * 2} * 3}')

	a = p.parse (r"""\sum_{x = {?(reals = False)} if {d^{3} / dy^{3} \partial '  {dx : \int_dy^-1.0 1e-100 dx,\partial x : -1 ["str"],1e100 : []}} else {?f(x, y, z)} if \log_\[[\[\infty zoo,],],[log\partialx,],[{\partial  : -1,None : True},],]{1e+100,.1} : {\partial x||oo||dx}}^[lambda x, y, z: Limit (\{1,xyzd,b}, x, b > 1.0),{\fracpartialx^partial{?f(x, y)}+{?f(x, y)}}] {.1 : {1e-100 : \partialx||d^{7} / dx^{2} dx^{3} dx^{2} \partial x||(partial,1,partial)}''',\partialy : {{oo [\emptyset]  {None  \partial x  a}  sqrtxyzd}*\{\fraccdz,\fracdx\partialy}}}""")
	print (a)

	# a = sym.ast2spt (a)
	# print (a)
