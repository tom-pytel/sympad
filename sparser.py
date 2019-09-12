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
			return AST ('lamb', rhs.stop, (lhs.mul [1], rhs.start))

	elif lhs.is_ass:
		if lhs.rhs.is_mul and lhs.rhs.mul.len == 2 and lhs.rhs.mul [0].is_var_lambda and lhs.rhs.mul [1].is_var:
			return AST ('=', lhs.lhs, ('lamb', rhs.stop, (lhs.rhs.mul [1], rhs.start)))

	elif lhs.is_comma:
		for i in range (lhs.comma.len - 1, -1, -1):
			if lhs.comma [i].is_mul:
				if lhs.comma [i].mul.len == 2 and lhs.comma [i].mul [0].is_var_lambda and lhs.comma [i].mul [1].is_var:
					ast = AST ('lamb', rhs.stop, (lhs.comma [i].mul [1], *lhs.comma [i + 1:], rhs.start))

					return AST (',', lhs.comma [:i] + (ast,)) if i else ast

			elif lhs.comma [i].is_ass:
				if lhs.comma [i].rhs.is_mul and lhs.comma [i].rhs.mul.len == 2 and lhs.comma [i].rhs.mul [0].is_var_lambda and lhs.comma [i].rhs.mul [1].is_var:
					ast = AST ('=', lhs.comma [i].lhs, ('lamb', rhs.stop, (lhs.comma [i].rhs.mul [1], *lhs.comma [i + 1:], rhs.start)))

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
			return wrap_ass (AST ('lamb', rhs, (l.mul [1],)))

	return _ast_pre_slice (lhs, rhs)

def _expr_mapsto (args, lamb):
	if args.is_var:
		return AST ('lamb', lamb, (args,))

	elif args.is_comma:
		for var in args.comma:
			if not var.is_var:
				break
		else:
			return AST ('lamb', lamb, args.comma)

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
			b'eJztnX2v3DaSr7/MBcYHUAPiq0T/5zjOrLG2k42TwS6MIHA8nkGwSRzYTu5eDO53X1b9ihLFlrqlPv12zhEsH6kpSiSLrEd8KZKP3vzl/7z/7e9/qf7y9OsXX7+K5xfPvvounr558u2zVy/ixVffPnkqJyVnHc9fPH/19ct0VulCywu+/Jre8Yr/fvHsrz8+' \
			b'ffL62Wu5fvkkuX7RX/6tv/wGl69fPHn9b1/E0P6dYtFdsPPT77998V/0q7v4/qvvX1E0X3/3Lf39/ov499nLb777r9fPOCbfU1z/9oRuvnz+6nuKy/NX3/2Vovv8JT/Bf//jW/L9guXwNd2V137BTz79+uXLJ0k25PDt87/+23cpGt+maNLFl1+84JhSNP4j' \
			b'/nny8hu6fPWlJJ+uvugv/9ZfSvKfvXj9TFyS8Oid3yEiMQLk6eWTb15/9zW9/jtO97P/fPoi3aY8+fL5355/Sa95igyRx795wQKIokmy+M/Xz56yhy+ff/UVifPVcy4MTznaT159SfKiG1/T8xxklLEa5IcIPobx9N/j5ac/fvr059uPn/7Mrj/F63dvP77/' \
			b'/OOHjz/+/adfPn1++zG7HS/j6S17e/8/v0cvP//5a7z+4x9//BYf+2fn/umP399/TD9+e//PH8lDf/OnePnr288/vvvwi1x9/PB/+yvE4tP7T5/edVe/d1fpNW9/6i8/f+5C+8fbd5/T9e/8VjgPIvBruvzl5+7y598+/zNd//rHLz/+/OvvWTL7y3/8I0tY' \
			b'uvzzbZ/c/u30GrpIvz+//1jeSz//yCP49u9/T5fv/vj4y/9LP/7n0/s+cT99fPvuv993Pz/lMfvzffeuP377+cNvXaBvO//v+uSxXLvof+hf+Ucm4t+6KP30828fumR86AUf49MJ/uf37953P2KBymLw+6fPH7q3dtnZxeXDL31033349de3gx+f/vJD9ebR' \
			b'xvnK1TcVLhRdWEN/bGXVjfyMv/jK0Z+KHW4GDvhl03PxvktOdMm+Njjr6pGujKs2qjJtvLhJruLWOWwautAWf1yoNtrf5E662XLyde5El/FKafzxFAAiHn/RJaU6/vcVBYfHHF1QBBT+OEkbpUnzo/FGDFgZ+n+TXNr8V5AzOVFMFCVZtZJkW98kV7j1DhvN' \
			b'D6gYKYphFLQNN+KyUSwP5fHHx+Sp9kac6DJeccZV8T2IivxM15m7wmnDItD83/h0W9MFvVfcEUiMnDjCk+FEBUlUU3eu4hZ6b/XQYaO5JBgKhwMyBn9iCdyIvOOvjUEG0Rua7obrbtgaf5yUxRiK5XSF6hEJh+SPtEcHl/3wOJEDhdTGoqeqlBUxICRF3DdO' \
			b'bTtlP/W2Dz38SWIOW07lQ2b4027/HDywMVzIos480q0EQFkEWSTn/ufGcKpjJj/SoYqZQJli6srTwzFv4g8pJ+M+mA5hpseYXUOPG8Nll4puUzmdClq8wcVWNaIgpFQ2aqPN9IRudu69i4WL610cXHzv4uHSJJeNYqHp6K454Cgj/uOaLradU5s70SUlxeLP' \
			b'Rigll3SlUEpTmknXWF9cLcUXqXEkKyQ6vovLqCSKiiznEQmV36lq/PEUc30jTnTJciSMJooiidENLunnhtPbymtIuyrbJtLlzuIQf3PsA/7EInUjv6N6cdxq/PExDzWiRLmvOUqxED4i9Yaix18eICQm1B3vU4lxLiGBUQopUgrqzgcKJpXrJNYmSS86PnK9' \
			b'svJPlYKOV47fx1+IkK5MLVeILl2YdAEQktqoiuUaS2kvWLkhzp1bfJLj3+KPJ7RJoW35kqIck4OvUJQOl8GuYNMXjYuV1vjjew3Wmi9Jji3+ZF/dVsBtG/zhjxO+BfEXXdKVTzdv5Gf8lW5ATDFVjYKom5QZ0TEKnq/o7VEN5AWkIw6yb9MN9ipO6SmdBO0s' \
			b'kk/f1viKWNl4U9Mz8XdMS8zZCNuoQLFERELEnI3iDvRBifFpmqqJNKjr+D+iuY5wqONHq44fs9rFvKUvRYxPDDXEAxCK9YFYtnwVZUwkid9PFQtWcFWIb48hxeyLeWeqJlRtXbWqanXVmqqN74wFQGmiTwyPPgU1hR0IY9E1qqOKT6r4KNVtogYRUghVUWUj' \
			b'dCJllKaXxMsYfBtPMREqpkLFIqNiRqoYvTbeaao2xpbCClWItQRNyhjVJJbjNrrEZMdDVY2umhhNWzWuauLLKZgYTqRvrN3EIhJ1L5a0+P2P9ZmovJEOkbw+BllHz3WUSvyQRmHEjCWxxWdjgD9Uj2r66L95FDOAylzMBDrFXFAxZx5ZuWssnB1OLd+Nzh6/' \
			b'GzqteXa2PAvIFcVnqkchOxrOB6oicuaR2Nlbzbn4qBHv8GWRpSo9zLlzsyrixTKVpYj8MpI1KYugdiGpnePfA5mKNCHHEQmK5DqJDSSVSWdMNJBIjKGTAuX8hcJvEH5AQaaCxPLQLK/zxEF7xEHbM4aJ/FdJn1nBV029lKZSDqwZcFFUakGl9WtGXDQjlBEk' \
			b'M6JEMCySTgCS8JTePI0xXX0azhv5QUHIM//sn7UoPKlG61St5vpaLBpVlEwV07SW4ROWYaOkjSO1Lt1VK9oVLhf9zLasB4qam9QgpcYotTipuUkN0pgPq/hPKX61iv+S4ter+C8pfrOK/3If5dZKWxcf4UecSvRToXa0fpYvVudPFSau1VPeSMWVhv1wI1Wl' \
			b'5CTdWE5y0Lo1Ay+ZgVa6iaUnK3B2PuDml9JSQDVK6COVOvladLy1aJ+1jdyWfnd+I5+VnFHeWyArpN54+A6pywJ3bUiduXhJy74egsAfBRlUamRYAtVMjqhauwe2xNVIwWlQuhoU1kbKaoOyqRJkmbJUrFDqPGTsRcYUVHxvxGKIIdj7IqM3jzzGLb257+lE' \
			b'NnuAyfuB6tzjZIOlntmJtOWpvT/plC9L7YtyjBFaSMGZ9OlAYeDPD1W/0hcmRgNj+HodlT9nkzHKWsNKYhX8WXtwPQmc7SHieZXwCYp2FOpaps87xhzFqddm8iXLPOOE7KXWfLhkPli7ZsCFUbRmwGUtA5VUcKIotVgGxvMq8ZMV+SgqEjCLZ7VqOagt67gZ' \
			b'dIGAR+ycyXg0NRL4c77m6UGi1cyfM1m9ojVNgeHMJ8vZSPZmQkTpMKmnTNx/EIN4ap/zm9bsnpsDpoaQ0fEs/c4QabIER7dcGppFVXkV7N6izV8Xsm9CITYyyG3SgGonUSODSCYVZZmC00IbWuhGa5I24LO1Cn5C8Mp0IgcLVgltjYZyWVqFAWHYVRi9MNwq' \
			b'jAQS61ANAYYV6ipv2ISAsGI7obVcX3mwgnpDVhMPWwCWuxFp7rl+QOkmgxYtVh56ayizEb0ZNxBTqVaPEc0LVxmU6uwvNOwvNOwvNIyBRPWd9BavkwYu2lfmpavMc7G7Z2YQCjZ79y5VzTWouTRpg7l3In4ULNLm9b1TCjL5gsLbe5g26bP07h6mrZG0tfcv' \
			b'bRRNDUstDQMtMciidYWoMnDDy6HRKdYBjHRgmht0Xht0Da2zTy5WidDIFCs5VctJIYtIvkZG4cyNjBaZfkEKGvmQn3TS4jtKGWe82+NlRlxl1in1ucIdtUxuOqwTgE872Ie2PBrqq5xPaEegE+xasVhtE+xM6gfX0v/NnbMr6U6fJzBaXWV8wrmMIH4L0rcm' \
			b'fUXko5FmzynTqYF8E8Z6R8jVwNXAlb8mTh7V7Nz1P3KHJLw3aSqTwVQmg0lI/JjjLo6H1kUV060f2Nwr7o4z67jXWPtfRgYb6FcD/WpYfbqOCtGutitAqK3zeO4PPNsKVTwvJgsNRglQmfNQa483eyimb7v6v5X6v01Dw6iJWtRELWqiNtVA7WrpfpoVjTSL' \
			b'GoBMWDVeiNwNwwt+tWRMTBadneo6ve10/3ZjEASebehR6Unmh2wyrkBRQCXpvjWQ68pJcXepBoji7lDcHYo7TgbnGDUnQneiqg5ydJCjWysyJ173jkVdzkuz7WoffElmOShRw0vYY31IT5+peJvW802fK1YcL4rjoTgeikPeqy6L/QMer+XSbCDNRqDDZ1kg' \
			b'WWGFZJZh84Dl9IZKT4PS0/DnC5aX3Wz0JLyWiyTmpCpLqhUDoCVAaO3GrmhGSbUokS3e2YrM8f216UMqX1KbGkNYAJIjEx52brgHLQAuKzaVFS1lRN/kRYw+MShcfFbcaCbZ1dWbmlf3t9zXSosuBk6d4a8Af3ViuDFISpenaFJi+JuDjx0+fBLxhjIAjWkI' \
			b'LZdMKW/Hkg59xuADCTHFvKSvXICMaXkR/mQp+Ww1wngjCkW/431qzVPLluaJ0xRxWi6almym5ZNpgQRaQ4AWEKDVA2hiPc2qp7U4aCEOWmyCFpqgEkLLidO3mtaBo8XIaEUsyi/6DtKSKLQeCq11Qs1nWtODRhlpHVBazpLmT9AklfhN1zQYEguQJuNU+vZS' \
			b'S4usuamEUBEhiZJdJpWBKFFNPVK8H0R0j4LVlJFkRBPjr6ls0dA+WZU0KmYetiGiTXF4B42K94KgHRR4R4xq0/DuFbTVQE07GLS8p8Em8K5BFW/WwDu8aPJBG04E2pWEdpaI1y3tvaF5Cx/akKOmh2h/GN66hbZsoA126DUtbyNDtxAs+db0gvhs4F064r1A' \
			b'kaTwo5cork1DsaM30A4lnh6uG97cgjd5oE0UsD8Lb53C2xYFhzRFLd9EoW8aJTH3vKcNBRZ90XYTtHkHbw9S89Y5FW8ixHuvUJLoUb7JqaIXt7zvBu+FQvGm/UdoYwjeiodTRDeip1gmNy2FHm+05LFm6ZAX8ss7dlAItOdK/N+SbBrZhobiSR5ZahRSoIiS' \
			b'K0WaZMAZ4bCzR1MjRCIM79JBW0bxdiE1bbfBso4uDe/Xw9v6kDjjrYZc3Q+k4KTWA5VW01qdaAUK9eptk4aroZL7Y+p5x0L0xexRez9T9e+S2usR1Vcz1N+RBF2p8W6Gzjv2FXPfbWu+63XfjWm/O7n+c+yiFFz3by8F3GwO3EkGtCMccHNIUP3LPqYvg3tM' \
			b'34YmxJP7/1xVjXiI+paw0DX5Gmmqoq5TkCHmpLQ3h+1bogQQYXs4oBY2FxE2o8RYla0nhiqJEQsa6nqEDu4pIo3sGtiNNNnbog5lUK9KjeQBZUxmcZBZIXSNyrIm36CqxRSqCxIFIZAvqEPEie+gGlmiDs3gIuOHAX3cHuo0TB5F3QW0asI+AlG37CwKhYJC' \
			b'jZDIDGlEZjpkztJRierHoBFKqqaKOYGITw2fYsB8clXnW7zTB6qGG3dZDA4CE/siKFGG1R2L+CFtD2ASKxhJtS64hHj0/7c4VcRueNRIr+8uEbmttw5CoOUI89+CuMBoY3EQ5tLtIMTDo1YiaeTs5dzgnFMQGaPAvAHvOkkL7JLcc+SBdpOgGyRAcZT3UQ8l' \
			b'oAefRHgbfBKdxD1kWUhBZfzrItBx0OvH9PWJ+v0YpS20j4nJUQEex9QSFE0Hxa6Jx3UlqSjdIRYChKkIzyGhXUjDlYQzSKgq3syQs4ivqF6WqmRSHes8aZyVSU5GyVV3MP9Uxj/V809xV8EB+FOgnyrglwe7Bb6tmA28O44OAY95MeGfYRcGqcubdSqF3d1G' \
			b'wQXpFECnwDkFzKmCcmoH5XA7UU7CX0K5LFqzEKcKxKkJwokIE+EUAKdKvsHbFt22oWaLmt4RiXYBnK2VuguhjAQDXbYTHEs+xIsMJFlwzA4O5pjNOGZ7jh1UhbNgmC0Ylge5xTC762CG2b7SNuonqDxJgBfSjrPP73NZtaAXGqh8QjBEL1vQy+6gF96R6CUR' \
			b'WEKvLFqz6GULetkJeonwEr3QNEU4Ob3k1oK6mVsxtmLs9hijhEKj/QTGkg/xQhiDE2WAHxyMMZ9hzPcYO6R3jB4iEfoCY3mQWxjzuw7GmO8xNuonqDxJgjEvGPPAWHefy6oHxjww5oEx9LZBrhnG/A6MSeQEYxKBJRjLojULY77AmJ/AmAgvYcwDY77EGLwt' \
			b'wZhfMbZi7PYYo8RAo5sJjCUf4oUwBifKgGZwMMaaDGNNj7HmEIw1wFhTYCwPcgtjza6DMdb0GBv1E1SeJMFYIxhrgLHuPpfVBhhrgLEGGGuAsWLcQKXhgjGMwXvCmERgCcayaM3CWFNgrJnAmAgvYawBxpoSY/C2BGPN9PDBHYNZvfLsCnjGBpKs2gE8ozPt' \
			b'uB2GVEv+xCNRDU6UDWFwMNVCRrXQUy0cQrUAqoWCanmQW1QLew4GW+jBNuonqDxVArYgYAsAW3efC20A2ALAFgC2ALCFAmxhB9jwygQ2icASsGXRmgW2UIAtTIBNhJfAFgC2chBUvC0BW7uCbQXb8cBGo+gYAdDS/a8xFqrVAGydP/FI69DBySi56g4Cm84G' \
			b'AXQ/CIB3LASbxgCALgYABkGWYNNbsSoj6RAbAdu4nzBIFcCmZahTo+u/v0+FVqP3X6P3X6P3X6P3Xxe9/3pH77/cFrClCCwAWx6tOWDTRe+/nuj9T8ITsGn0/uuy91+8LQFbWMG2gu2IYNMVD9LJqcaZvOsh2JI/ORPYcGmUXHUHg01nYNM92PQhYNMAmy7A' \
			b'lge5BbZ9B4NN92Ab9RNUnioBm4xpislqf5/BpgE2DbBpgE0DbLoAm94BNrwygU0isARsWbRmgU0XYNMTYBPhJbBpgE2XYIO3JWBT9XlM2VY7toeGOFslJZchTzqTd8uIoxMFbAG65Fu8K5OcKFJ2cDDosuFP3Q9/HmTBpjH8qYvhz0GQW6Czew4GHa56MYx4' \
			b'CypPmLBOBkE1BkH7+8w6DIJqDIJqDIJqDILqYhBU7xgETZET1kkElrAui9Ys1hWDoHpiEDTJL7EOg6C6HARNt5awToF1EC2VuiaBbEgxQpjfBxqBAyl2p8BQXFYuKA4pQqjOcvC0hTMZJq80f2A0p+KBlriRlrhBS9ygJc4o9ji5qvMt3mkGH5xwyg+iucna' \
			b'46Zvj5tD2uMG7XFTtMcHQZY0345VGUnn05XQfNxbGCQMNDfSJDdokvf3qfQaNMkNmuQGTXKDJrkpmuRmR5M8RQ40TxFYQPM8WnNoboomuZlokif5Cc0NmuSmbJKLt0U0NyvrVtadgnWOCgYruUwGM5gKxqeGT8Q6B9Yl3+KdWAcnKmZucDDr0qwwKoj9ZDBz' \
			b'iPExPUSscwXr8iC3WDe8T9lbxtL5dJVg50YOhl2fMoGdE9hhRll/n2HnADsH2DnAzgF2roCd2wE7iZzATiKwBHZZtGbBzhWwcxOwE/kl2DnAzpWwg7dFsCvtkFfYrbA7Cuw8lQpWcjHp41njLU4NnzT8aBQgMe8zYt4nTlTM/OBg2GXmfaY37zOHmPcZmPeZ' \
			b'wrxvEOQW7Pyeg1knybNJDCPegsoTJqwTIz8DI7/+PrMORn4GRn4GRn4GRn6mMPIzO4z8UuSEdRKBJazLojWLdYWRn5kw8kvyS6yDkZ8pjfzE2yLWlcbKK+tW1h2FdQ0VCVZysfujM7GuAesw8MInV3W+xTuxDk5UzJrBwazLbABNbwNoDrEBNLABNIUN4CDI' \
			b'LdY1ew5mnaTSJjGMeAsqT5iwTiwBDSwB+/vMOlgCGlgCGlgCGlgCmsIS0OywBEyRE9ZJBJawLovWLNYVloBmwhIwyS+xDpaAprQEFG+LWFdaNK+sW1l3FNa1VB5YyWUVIzo7uDouLMy6FqxLvsU7sQ5OVMzawcGsSwsbUUFse9a1h7CuBevagnV5kFusa/cc' \
			b'zDpcJdaNegsqT5iwrhXWtWBdd59ZhxVS+J7BCen2jUg6Y127g3USOWGdRGAJ67JozWJdsTqKmVgcJckvsa4F69qSdfC2iHU7zJ5X1q2sO5h1VAwwOGFlcMJicMJicMJicMJicKLzLd6jjomTUXLVHcQ6mw1O2H5wwh4yOGExOGGLwYlBkCXr7Fasykg6n66E' \
			b'dePewiBhYJ2VwQmLwYn+PpVei8EJi8EJi8EJi8EJWwxO2B2DEylyYF2KwALW5dGawzpbDE7YicGJJD9hncXghC0HJ8TbIta124uh3APcqYJ4c5dHWal3ghqerQzUvZWrmgsNV/JgY2NgY2NgY9M9AG9cyYOTWEBkxya9M1Xyehsbc4iNjYGNjSlsbHhx/C7M' \
			b'rVqe3XO0sLORxzUc1MSDXNfr0yd1PTG1MTC16e9zXQ+mNgamNgamNgamNqYwtTE7TG1S/KSuJxFYUtfLojWrrleY2pgJUxt5aVfXg6mNKU1txNsi/oWVfyv/Tlvr81QOmH8OV1Txw+CFxeCFxeCFxeBF9wC8ccUPTkbJVXdwxS8bvLD94IU9ZPDCYvDCFoMX' \
			b'gyC3Kn5+z9FirFYe11xcufo35pmrf33ypPonQxgWQxj9fa7+YQjDYgjDYgjDYgjDFkMYdscQRoqfVP8kAkuqf1m0ZlX/iiEMOzGEIS/tqn8YwrDlEIZ4W4I/vVpV74ZelIdxK/xMswOAao6VNf1gpdcypKExpKExpKExpKExpNH5Fu9kZQ0no+SqO9jKOhvS' \
			b'0P2Qhj5kSENjSEMXQxqDILesrJs9B1tZSyptEsOIt6DyhImVtQxp6Jr+QyI+98fW1hja0Bja0Bja0Bja0MXQht4xtJEiKdbWEpEFDMyjNcvauhja0BNDG9raTpbJ4hrDG9oFCS+3uobXRSxUKwvXCuAJKoC0JCxjB6caZ8rymtlHpxgwn1zV+RbvUdfEKUYK' \
			b'V91B7GNPwj66FvbhHQvZJ8u20yln3yDIrVXc6z0HsU+uhH3j3oLKEwb2QQI4+/w+lV5+CALwBiek2zci6Z55+D3OvBQ5MC9FYAHz8mjNYR7ypmceIrfNvCQ/4R1nS5BwMtaJt0WsW+dfrKw7Cet4fztWcrFJdrBJdrBJdrBJdrBJ7nyLd2IdnIh1bnAw6zKb' \
			b'ZNfbJLtDbJIdbJJdYZM8CHKLdW7PwazDVWLdqLeg8oQJ68Qk2cEkub/PrINJsoNJsoNJsoNJsitMkt0Ok+QUOWGdRGAJ67JozWJdYZLsJkySk/wS62CS7EqTZPG2iHXXOP8i23xsJd6piccz7086h5gc0KyT/j2N/j2N/j2N/r20WELyLd6VSU4UKT84uHWb' \
			b'9e/pvn9PH9K/p9G/x7vY0IZI3F/uuZMDzVx+L93WIz19ReS2D27nSkJtEsiIt6DyJEo7V/r4NPr4+vvcvkUfn0Yfn0Yfn0Yfny76+PSOPr4UOWnfSgSWtG+zaM1q33ruPRm2cSf6+ZIMU/sW/Xy67OcTb4sYuE7LeLD0O219z1Muc0VHyOdAPgfyOZDPgXyd' \
			b'b/FO9T04UX3PDw6u72Xkcz353CHkcyCfK0Y2BkFu1ff8nmPTX6X63qi3oPKESX1PeOfAu/4+1/fAOwfeOfDOgXeu4J3bwbsUOanvSQSW1PeyaM2q7xVjGm6CdUl+qb4H1rmSdeJtEevWaRkr607Cupbyl5VcTJUdTJVlUWYHU2UHU+XOt3gn1sGJWNcODmZd' \
			b'ZqrselNld4ipsoOpsitMlQdBbrGu3XMw63CVWDfqLag8YcI6MVV2MFXu7zPrYKrsYKrsYKrsYKrsClNlt8NUOUVOWCcRWMK6LFqzWFeYKrsJU+Ukv8Q6mCq70lRZvC1i3Toto9s5+07yTu1hngz5nYR9dpp/NKSWM9CHnIOhQlHGqcYZxYE5GMDBAA4m3+Kd' \
			b'OAgn4mAYHMzBbDFn1y/m7A5ZzNlhMWdXLOY8CHKLg2HPwRzEVeLgqLcwTF6HQlnS2WFJ5/4+oxBLOjss6eywpLPDks6uWNLZ7VjSOcVPUCgR2INC9pPRMItZ9479TAwFE8MEE0WWqXQg0U0KULDIbiaLyiI4lvM4eHOCw5dBdRdi4umWQb0UBf0V1vyoQEQ3' \
			b'6sDabc4XKPfZfE3oV27K0fkQL2S/Byey3wuDg+33MuJRXtqeevYQ6qXdt22BPeR1/3/bkC/sOtiEr4feuJ+QUkiZSMiT+MqqqBbQ62KA3dKwKiqiZOTs5dyIx9yGbwf4JBrJhk9kXIAPcdq1nj3JJOXeLEu+jHqsjnZigdQkymTKB+ZxvyI9Ef0WlUJ5oONe' \
			b'LCiPsc6sf8x9iRnvylXtb8m7W8Lu3IATuDHUjMCsEYhdqtl66SYrZQjU1dtxWHU+xIsyySlGBFfdQbDy2WQL30+28IdMtvCYbOGLyRZbXCqiUcbKIXjdJXTET1B5MlAT6xLtZR4ZUYgIRPQh8gyo43dMnJD3CnVSKAtann3c9qLGF3MmONQx1CTpCGo8Jk34' \
			b'ctKEeJvYYpa5Ui4qv3LlwXPF0xA2q5uf4EryIV6IK3AirvjBwVzJuvp939XvD+nq9+jq934fV/yug7nSd+yP+wkqT0bOFT+XKzt67+W9iSsSyhKudHHbzxU/lysincQV9Nz7sudevO3giiknH6xcefBcackohtWtneBK8iFeiCtwIq60g4O5knWr+75b3R/S' \
			b're7Rre7bfVxpdx3Mlb4TfdxPUHkycq60c7myo6dc3pu4IqEs4UoXt/1caedyRaSTuIJecl/2kou3XVwpDfkvy5W10+fuDfVRpsFkv6nHOdT5EC9RWcQpRgRX3UEcajIz/aY3028OMdNv0L/TFGb6gyBLJhVRKmPoEBVh0rifoPIkZUzirp0GJvpJLkqiiZR7' \
			b'gxNCiaJuCvv8Zod9vrxSaJXCX0CrPtbzenOawj6/mbDPT7ITYjWwz29K+3zxNkGsvAfHlGb5K7lWci0kl6qgljiNkSv5EC9ELjgZJVfdweRSGblUTy51CLkUyKUKcuVBbpFrK1YD7w5RSeQa9RMGSdoilwK5RC5KoomUe4MTQiFyqYJcage5cDuRS8JfQq4s' \
			b'WrPIpQpyqQlyiewSuRTIpUpywdsccpVG9iu5VnItJJemHGMl1hPkSj7kTOTCpVFy1R1MLp2RS/fk0oeQS4NcuiBXHuQWuXYeTC7dk2vUT1B5krbIpUGuJA+JJlLuDU4IhchVjKPh9wS58MpELgl/Cbl0H61Z5NIFuSYG0JLsErk0yFUOm4m3OeQqTeNXcq3k' \
			b'WkguQ9nFSmwmyJV8iBdlkhORywwOJpfJyGV6cplDyGVALlOQKw9yi1xm18HkMj25Rv0ElSdpi1wG5BK5KIkmUu4lUgiFyGUKcpkd5MLDiVwS/hJymT5as8hlCnKZCXKJ7BK5DMhlSnLB2xxysaF7pFEV8VJFYUWGhWwdMyMso+lTwJkZI1qdoGbGuFYntJmz' \
			b'2EDV+xkXy3cIJ1rT7BDakclt9BcTr2Lqe/pFd++Egg1IGNPf01AXRPR7qGhPZDzlFxDS32aSJKkaIYn6yKi/ntQpagj62TYx3S3ZXglAVe16iobQkXRDpZneJDjVMm+czgHPEzcNu+THBmsu4mmFbeACA3aj4LubWHnIdPJkdKWL+eSDKJSY3fBqvhRlX0a3' \
			b'f8ghRtpy2dkE1gkS2bh3mlrZp7nkrsbkcrmtRJjB4gbE4BEgZV4xs3xjyIiN5EjvTfdZlGRj0QLIxElCjWozMGtMv5Rw8zWGJKY5oeu2w7TeyWqWTyoEs6ZjmhSDGSMS8b/pciFNynSy6FCBbfHWYds9Zhf6GwlOVYCW/wb6SzCn25Hl2jHKfdSPEuRTCPdE' \
			b'bsI2mA1I54RmPM9l8+j4J5OYiOvA2sTSnJ9zxi4LNk5xcYuJGQsPYmC7n3tzeddxLgz51tf+2l1M20+zpJyGAZbo1eFqhFUJVIdTavf4ZULSJs1rDA7pCWX32ayRyJIa08gocTEAxYGIID7s58ICIHQoIA4MIZDUnzS6GdHoHfWyMyh1V8Nq7ppqk3m/Wa7i' \
			b'9I0cVfOyStPOUPM9dRdUSO6grmdVEMrEO6vzmlujJK3Fyq9N0W3eA2CrNmDdXAC0Cz7p9rwAyBpXQgJ/VBg4autExSVT/xih08LhADCQyI/2/d8Hhv1QSG2ZqwUDxzD/L5CgBu2RQcHQjiqlqe2kkm3kSSsLh0JjqtagSUIH1Bqqf2mazdbW3CIIy1oEzT58' \
			b'+GMSRKjR9tTQd6AacYsWAvUbTFUfBr0h9LsVWlDjVhe9Iopn+mhexIioT51xbT7BNv7XR6EK66A1S6lyZrIkkvCQO0hCmXVnqh23bGpou6u2AdZ2PQ8cciv9D/SMLYe9+gnbfJtrRBQV3irIdqihH1xJiaEf3O9gJ/qHj04ZQUxNnbvNCGbmGlJfEjVmRmvF' \
			b'zmutMGrMySsl4xUSm+PDplGqy1VMitYKZ1TrRvBhzZ1BCOX8nPpHMe60AyO0nIOd02iJor2qfsgJEkTtikVX8VBX/K3OXflw56mA0AouLG6qjMzsyxhURtptQqRKxykqG1fbfNmiBE3P5GG2jcJ22GPIODUu/DkrHSQZeg/5KbfdmlkB6SofZZ0jSDWjrFzo' \
			b'6s21gORYAxp3oakSbtuh0VOgVXcbAsceyLhTLQt1+4GM6l/N4/gloA6JqBbXrM21v2Vd4Fo1e8m3f4Fm3/nv++S33bHtzO2+6det55K++V/xWQMW8YmDFNydT8fDEer8M021duk6m2edqs5vrlznaf3E61R8js5RqvS5+tv6YAaQXeFJQaDxloV1+nk0cIfR' \
			b'wJ+NBjkJKGqX+OqfkgQrBQ6p2Q8JQJlzwUrAyQFwKuX3hyl/cxnlt6vyr8o/pvwXbenfWeVvDlP+9jLK71blX5V/TPnNqvwHKH971b1896pn7xq1+xoV+0harFmTrqUP73haW/0rFunHxCjupg9XrcAxSd3w/dmUeWSG5cmH7FflntlrR2HTaPx5P9bmMsPv' \
			b'R/xSR7FfVNGn5nHv+mrXxfTra/56z5g6PXsKQV0YCN8/hefp88X/RV93fmAwVflOjNXNm3U8ofhjg/Ish97k1+0enI/ffR/osx/fvdJgpcG10ID3WBv+X0YDemClAeTQ08DPpYGu3rRbi1lB9TUrPdaqaljRcy1nFYe+DtdwSus3jSmSY6VhBSgLfVe/bWOB' \
			b'brUU3mJ1pKy8UsnkciqLH6Fgaj9eILvC2G3Amy8KJAsCjWcs3bCpSrYt/772pbmyZW4lUMBQxFoL84hnk8tk7RPzBF8G4kav2CnkrVjddCZ3LS9lrxMrM83IiGllKDPE3i5D3ESe3PV80T1it/ImMfIs+eNulz8T9Yk8u+plVYdDsnTuZ38y2+uilX/i7GcZ' \
			b'DP8PP7tZmcDNhZ/XA4vOgs/iVAnj6BYNYz386Pm5Re6W/VpZITykC2tpQTzHQjf7u6IOLrRLK5VcQ53Xp5QT7sDeo+UF+lxLzczp+PXqcayDc+Fv1sJ/vYV/kty36FB98IXf0VoJvHpazJW18F9x4W/Wwn/Cwh/mFf5jjOidu/yfaZm/gQ5M7AN9K33g0n/q' \
			b'EbYRnZAQTqcTCOBoesGvm6UXmhNUbW2XPLlRMqlKjMiqKlf4ueDifwn10Cf+ZCCA46kHve5Wn40xpVAzlOJ4RiHn1IszrxZ7dN3gEnk2C40z16n4bedfwXWWbYXfO35ybFupU6nFlSykfEzVQCk4vwXTCfWDk3RFyxzPU5LdY2KnsSk8hZ5c2ub3RLrChfeS' \
			b'Jn8nUhgO4xpsdQ/Tmh0Dl6c0xl0VZ5bi8N1rsJc92ddG32XlGY4qn9me/fZTUViLrnXqya21iTL/mqzQppXqljNLKP8psdc8keQw/eqG0C80ZWRVsXEVozJ/rcaeJ1Wzq5+wdZieNaueXaeehVXP7pOetdUbWvtYN8hkWhkz8I1QvfG0e3B0hwWhIeeGlkNX' \
			b'jjYrNJYdaD1ka3n3QvXDTTw/2ijadZOKHrbSbGgldFoD3Q/2VVFYjJfezxsued63ss2WMSdFGu6TwsuE25YC3uiFocSnp/7x+2R/9tE3yjLLeuLVhuZwmMG/funkJnfnkOxISKrcWnRPwLw0Wzdvk5ZaINUOEqEY7+4flWQrS0H0/+3IP75HGKHdQWmXEaIt' \
			b'bYvBsXa3jDUxbG/EfTX3H81sKdw4mn5xNMe2U52MKfVIdLFtqt3/aCbO1D2a6RLPHOdmO86yk/ZYtCMo6MNlhzbAu7e/Nnu2gfX9FrC8W0Da7pWsYGmb1+hG27vy1q7bUhlsqcoS6vIU25+6buMFmuRQ9f+IrG3xD9Ogx/+Xfnf7Hn/DvPdvPzMSGudee8YS' \
			b'F7PyNv84vuGqSpsuSlx9olLHy2Fe8iBb+eyHv+X7OCvjd/58ZY+q4ic8kCDVJYgWLfMnK6L1lZZSV+EIPCm0+3nkg9okJ3r1+IHM1UcprTwXelaBpVbTrQ9qw03eRrpMUWhpjYvT0ZWLLrUCr670UgM9O2Icg6sKx+Me1Ko+aQDDA9k9Un/fkcX7v5WzCjN1' \
			b'ewwPypItxzkHdUdM30Ya3VqkUaTb6l4fyO2RRtPpSzT1353jQBKbtUBzgaYu0/t8ILdH2mS3KtC1nluoTXXEgzqKp28jqWEt2CjYobrXBzo9Rxp8ty7YlI2zCjeNshz1oAGQ6dtIcdkifKjlm8a37vOB3B5pIh6lfKsd3ebDMm6qox80njd9Gwlf25BSzG11' \
			b'rw/k9rImJOXt4h7XidLe50JX4l01/6BB3AW+Ywy3XWkoOv2AONbWphT+prrXB3J7WWvzoMKf5+R8RWir0x25HcdOn5DR2lyFRpANz30+kNvLmqvn0wgyn7rwAQGtjVxRB1Pd6wOWOPUV5rY7Yo6rYa7T0vsx7O3ct30JICMtlALaTppKgq2u5FDBHONJTTkb' \
			b'szb30P8eXKGUqMV2DLflZioA8/g5pr5NNf8g48dFDwweFjPR3b7Y2DMz9GS5LmuCX4VcyZz3Gg8IdMSy8OoFqqqrPCDQZa3nYwpU72pYN3MEq6tzHvSNmevKBwQ8Yus566N7Hhm3c+RsqkUHmT4vfeb2r4a0l7WHr1Larrr6A7I+1NT2imTdVFd/QNbLWrV3' \
			b'3azZh+qAA1OI+v+HvWXXG2e+ffQ28vG6DIZPnY80C+w+HJhqsmy8+M7nnavuxYG8W97AvdN556t7cSDvljei73TeNdW9OJB3sb1u2H68lvl6tnMQqjpyIJmxo6NdDXEjVuXz3I2SZR9RpjTHgXozFfmW9zajvnnz5sF/+G63fFNu8RO0Et7wv9ZoK9vBPE7q' \
			b'pEQBpc3x8sK2q3zEvOenm8Fk537i8cikYzHnoE23ip0qKBLa4oWtBJWKoUJxk3FC2qOH+10Dyz7QhEQILpa9N1ywA8+ZCDRlEcykXU+4L5X6TrnPlASkydTV0SpCpIgSNddPXIWAaXsEHcVDLjLlsaFrfoO01Wgh7eQS/fxw878dWMWG'

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
		('UFUNC',        fr'\?({_LTRU}\w+)?'),
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

	def expr_commas_1      (self, expr_comma, COMMA):                              return expr_comma if expr_comma.is_comma else AST (',', (expr_comma,))
	def expr_commas_2      (self, expr_comma):                                     return expr_comma
	def expr_commas_3      (self):                                                 return AST.CommaEmpty
	def expr_comma_1       (self, expr_comma, COMMA, expr_colon):                  return _expr_comma (expr_comma, expr_colon)
	def expr_comma_2       (self, expr_colon):                                     return expr_colon

	def expr_colon_1       (self, expr, COLON, expr_colon):                        return _expr_colon (expr, expr_colon)
	def expr_colon_2       (self, expr, COLON):                                    return AST ('slice', expr, False, None)
	def expr_colon_3       (self, COLON, expr_colon):                              return _ast_pre_slice (False, expr_colon)
	def expr_colon_4       (self, COLON):                                          return AST ('slice', False, False, None)
	def expr_colon_5       (self, expr):                                           return expr

	def expr               (self, expr_ass):                                       return expr_ass

	def expr_ass_1         (self, expr_mapsto1, EQ, expr_mapsto2):                 return AST ('=', expr_mapsto1, expr_mapsto2)
	def expr_ass_2         (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr_colon):                 return _expr_mapsto (expr_paren.strip, expr_colon)
	def expr_mapsto_2      (self, expr_piece):                                     return expr_piece

	def expr_piece_1       (self, expr_or, IF, expr_ass, ELSE, expr_mapsto):       return _expr_piece (expr_or, expr_ass, expr_mapsto)
	def expr_piece_2       (self, expr_or, IF, expr_ass):                          return AST ('piece', ((expr_or, expr_ass),))
	def expr_piece_3       (self, expr_or):                                        return expr_or

	def expr_or_1          (self, expr_or, OR, expr_and):                          return AST.flatcat ('or', expr_or, expr_and)
	def expr_or_2          (self, expr_and):                                       return expr_and

	def expr_and_1         (self, expr_and, AND, expr_not):                        return AST.flatcat ('and', expr_and, expr_not)
	def expr_and_2         (self, expr_not):                                       return expr_not

	def expr_not_1         (self, NOT, expr_not):                                  return AST ('not', expr_not)
	def expr_not_2         (self, expr_cmp):                                       return expr_cmp

	def expr_cmp_1         (self, expr_cmp, CMP, expr_union):                      return _expr_cmp (expr_cmp, CMP, expr_union)
	def expr_cmp_2         (self, expr_union):                                     return expr_union

	def expr_union_1       (self, expr_union, UNION, expr_sdiff):                  return AST.flatcat ('||', expr_union, expr_sdiff)
	def expr_union_2       (self, expr_sdiff):                                     return expr_sdiff

	def expr_sdiff_1       (self, expr_sdiff, SDIFF, expr_xsect):                  return AST.flatcat ('^^', expr_sdiff, expr_xsect)
	def expr_sdiff_2       (self, expr_xsect):                                     return expr_xsect

	def expr_xsect_1       (self, expr_xsect, XSECT, expr_add):                    return AST.flatcat ('&&', expr_xsect, expr_add)
	def expr_xsect_2       (self, expr_add):                                       return expr_add

	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                  return AST.flatcat ('+', expr_add, _expr_neg (expr_mul_exp))
	def expr_add_3         (self, expr_add, SETMINUS, expr_mul_exp):               return AST.flatcat ('+', expr_add, _expr_neg (expr_mul_exp))
	def expr_add_4         (self, expr_mul_exp):                                   return expr_mul_exp

	def expr_mul_exp       (self, expr_mul_expr):                                  return _expr_mul (expr_mul_expr)
	def expr_mul_expr_1    (self, expr_mul_expr, CDOT, expr_neg):                  return AST.flatcat ('mulexp', expr_mul_expr, expr_neg)
	def expr_mul_expr_2    (self, expr_mul_expr, STAR, expr_neg):                  return AST.flatcat ('mulexp', expr_mul_expr, expr_neg)
	def expr_mul_expr_3    (self, expr_neg):                                       return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                return _expr_neg (expr_neg)
	def expr_neg_2         (self, expr_diff):                                      return expr_diff

	def expr_diff          (self, expr_div):                                       return _expr_diff (expr_div)

	def expr_div_1         (self, expr_div, DIVIDE, expr_divm):                    return AST ('/', _expr_mul (expr_div), _expr_mul (expr_divm))
	def expr_div_2         (self, expr_mul_imp):                                   return expr_mul_imp
	def expr_divm_1        (self, MINUS, expr_divm):                               return _expr_neg (expr_divm)
	def expr_divm_2        (self, expr_mul_imp):                                   return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                        return _expr_mul_imp (expr_mul_imp, expr_intg, self._USER_FUNCS)
	def expr_mul_imp_2     (self, expr_intg):                                      return expr_intg

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add):           return _expr_intg (_expr_mul (expr_add), (expr_sub, expr_super))
	def expr_intg_2        (self, INTG, expr_add):                                 return _expr_intg (_expr_mul (expr_add))
	def expr_intg_3        (self, expr_lim):                                       return expr_lim

	def expr_lim_1         (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                          return AST ('lim', _expr_mul (expr_neg), expr_var, expr)
	def expr_lim_2         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):  return AST ('lim', _expr_mul (expr_neg), expr_var, expr, '+')
	def expr_lim_3         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg): return AST ('lim', _expr_mul (expr_neg), expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                        return expr_sum

	def expr_sum_1         (self, SUM, SUB, CURLYL, varass, CURLYR, expr_super, expr_neg):                          return AST ('sum', _expr_mul (expr_neg), varass [0], varass [1], expr_super)
	def expr_sum_2         (self, expr_func):                                                                       return expr_func

	def expr_func_1        (self, SQRT, BRACKL, expr_commas, BRACKR, expr_neg_func): return _expr_func (1, 'sqrt', expr_neg_func, expr_commas)
	def expr_func_2        (self, SQRT, expr_super, expr_neg_func):                return AST ('^', _expr_func (1, 'sqrt', expr_neg_func), expr_super)
	def expr_func_3        (self, SQRT, expr_neg_func):                            return _expr_func (1, 'sqrt', expr_neg_func)
	def expr_func_4        (self, LN, expr_super, expr_neg_func):                  return AST ('^', _expr_func (1, 'log', expr_neg_func), expr_super)
	def expr_func_5        (self, LN, expr_neg_func):                              return _expr_func (1, 'log', expr_neg_func)
	def expr_func_6        (self, LOG, expr_sub, expr_neg_func):                   return _expr_func (1, 'log', expr_neg_func, expr_sub)
	def expr_func_7        (self, LOG, expr_super, expr_neg_func):                 return AST ('^', _expr_func (1, 'log', expr_neg_func), expr_super)
	def expr_func_8        (self, LOG, expr_neg_func):                             return _expr_func (1, 'log', expr_neg_func)
	def expr_func_9        (self, FUNC, expr_neg_func):                            return _expr_func_func (FUNC, expr_neg_func)
	def expr_func_10       (self, FUNC, expr_super, expr_neg_func):                return _expr_func_func (FUNC, expr_neg_func, expr_super)
	def expr_func_11       (self, expr_pow):                                       return expr_pow

	def expr_pow_1         (self, expr_pow, expr_super):                           return AST ('^', expr_pow, expr_super)
	def expr_pow_2         (self, expr_fact):                                      return expr_fact

	def expr_fact_1        (self, expr_fact, EXCL):                                return AST ('!', expr_fact)
	def expr_fact_2        (self, expr_attr):                                      return expr_attr

	def expr_attr_1        (self, expr_attr, ATTR):                                return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1].replace ('\\', ''))
	def expr_attr_2        (self, expr_abs):                                       return expr_abs

	def expr_abs_1         (self, LEFT, BAR1, expr_commas, RIGHT, BAR2):           return AST ('|', expr_commas)
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                        return AST ('|', expr_commas)
	def expr_abs_3         (self, expr_paren):                                     return expr_paren

	def expr_paren_1       (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):       return AST ('(', expr_commas)
	def expr_paren_2       (self, PARENL, expr_commas, PARENR):                    return AST ('(', expr_commas)
	def expr_paren_3       (self, expr_frac):                                      return expr_frac

	def expr_frac_1        (self, FRAC, expr_binom1, expr_binom2):                 return AST ('/', expr_binom1.no_curlys, expr_binom2.no_curlys)
	def expr_frac_2        (self, FRAC1, expr_binom):                              return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_binom.no_curlys)
	def expr_frac_3        (self, FRAC2):                                          return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4        (self, expr_binom):                                     return expr_binom

	def expr_binom_1       (self, BINOM, expr_subs1, expr_subs2):                  return AST ('func', 'binomial', (expr_subs1.no_curlys, expr_subs2.no_curlys))
	def expr_binom_2       (self, BINOM1, expr_subs):                              return AST ('func', 'binomial', (_ast_from_tok_digit_or_var (BINOM1), expr_subs.no_curlys))
	def expr_binom_3       (self, BINOM2):                                         return AST ('func', 'binomial', (_ast_from_tok_digit_or_var (BINOM2), _ast_from_tok_digit_or_var (BINOM2, 3)))
	def expr_binom_4       (self, expr_subs):                                      return expr_subs

	def expr_subs_1        (self, LEFTDOT, expr_commas, RIGHT, BAR, SUB, CURLYL, subsvars, CURLYR): return _expr_subs (expr_commas, subsvars)
	def expr_subs_2        (self, expr_cases):                                     return expr_cases
	def subsvars_1         (self, SUBSTACK, CURLYL, subsvarss, CURLYR):            return subsvarss
	def subsvars_2         (self, varass):                                         return (varass,)
	def subsvarss_1        (self, subsvarsv, DBLSLASH):                            return subsvarsv
	def subsvarss_2        (self, subsvarsv):                                      return subsvarsv
	def subsvarsv_1        (self, subsvarsv, DBLSLASH, varass):                    return subsvarsv + (varass,)
	def subsvarsv_2        (self, varass):                                         return (varass,)

	def expr_cases_1       (self, BEG_CASES, casess, END_CASES):                   return AST ('piece', casess)
	def expr_cases_2       (self, expr_mat):                                       return expr_mat
	def casess_1           (self, casessp, DBLSLASH):                              return casessp
	def casess_2           (self, casessp):                                        return casessp
	def casessp_1          (self, casessp, DBLSLASH, casessc):                     return casessp + (casessc,)
	def casessp_2          (self, casessc):                                        return (casessc,)
	def casessc_1          (self, expr1, AMP, expr2):                              return (expr1, expr2)
	def casessc_2          (self, expr, AMP):                                      return (expr, True)

	def expr_mat_1         (self, LEFT, BRACKL, BEG_MAT, mat_rows, END_MAT, RIGHT, BRACKR): return _expr_mat (mat_rows)
	def expr_mat_2         (self, BEG_MAT, mat_rows, END_MAT):                     return _expr_mat (mat_rows)
	def expr_mat_3         (self, BEG_BMAT, mat_rows, END_BMAT):                   return _expr_mat (mat_rows)
	def expr_mat_4         (self, BEG_VMAT, mat_rows, END_VMAT):                   return _expr_mat (mat_rows)
	def expr_mat_5         (self, BEG_PMAT, mat_rows, END_PMAT):                   return _expr_mat (mat_rows)
	def expr_mat_6         (self, expr_vec):                                       return expr_vec
	def mat_rows_1         (self, mat_row, DBLSLASH):                              return mat_row
	def mat_rows_2         (self, mat_row):                                        return mat_row
	def mat_rows_3         (self):                                                 return ()
	def mat_row_1          (self, mat_row, DBLSLASH, mat_col):                     return mat_row + (mat_col,)
	def mat_row_2          (self, mat_col):                                        return (mat_col,)
	def mat_col_1          (self, mat_col, AMP, expr):                             return mat_col + (expr,)
	def mat_col_2          (self, expr):                                           return (expr,)

	def expr_vec_1         (self, SLASHBRACKL, expr_commas, BRACKR):               return _expr_vec (expr_commas)
	def expr_vec_2         (self, expr_bracket):                                   return expr_bracket

	def expr_bracket_1     (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):       return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_2     (self, BRACKL, expr_commas, BRACKR):                    return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_3     (self, expr_curly):                                     return expr_curly

	def expr_curly_1       (self, LEFT, SLASHCURLYL, expr_commas, RIGHT, SLASHCURLYR): return _expr_curly (expr_commas, forceset = True)
	def expr_curly_2       (self, SLASHCURLYL, expr_commas, CURLYR):               return AST ('set', expr_commas.comma) if expr_commas.is_comma else AST ('set', (expr_commas,))
	def expr_curly_3       (self, CURLYL, expr_commas, CURLYR):                    return _expr_curly (expr_commas)
	def expr_curly_4       (self, expr_ufunc):                                     return expr_ufunc

	def expr_ufunc_1       (self, UFUNC, LEFT, PARENL, ufuncargs, RIGHT, PARENR):  return AST ('ufunc', UFUNC.grp [0] or '', ufuncargs [0], ufuncargs [1])
	def expr_ufunc_2       (self, UFUNC, PARENL, ufuncargs, PARENR):               return AST ('ufunc', UFUNC.grp [0] or '', ufuncargs [0], ufuncargs [1])
	def expr_ufunc_3       (self, expr_term):                                      return expr_term
	def ufuncargs          (self, expr_var):                                       return (expr_var.var,), ((expr_var.var, expr_var.var),)


	# def ufunckw            (self, expr_var, EQ, expr_colon):                       return (expr_var.var, expr_colon)



	def expr_term_1        (self, expr_num):                                       return expr_num
	def expr_term_2        (self, expr_var):                                       return expr_var
	def expr_term_3        (self, STR):                                            return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_4        (self, SUB):                                            return AST ('@', '_') # for last expression variable
	def expr_term_5        (self, EMPTYSET):                                       return AST.SetEmpty

	def expr_num           (self, NUM):                                            return _expr_num (NUM)
	def expr_var           (self, VAR):                                            return _expr_var (VAR)

	def expr_sub_1         (self, SUB, expr_frac):                                 return expr_frac
	def expr_sub_2         (self, SUB1):                                           return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1       (self, DBLSTAR, expr_neg_func):                         return expr_neg_func
	def expr_super_3       (self, CARET, expr_frac):                               return expr_frac
	def expr_super_4       (self, CARET1):                                         return _ast_from_tok_digit_or_var (CARET1)

	def expr_neg_func_1    (self, MINUS, expr_neg_func):                           return _expr_neg (expr_neg_func)
	def expr_neg_func_2    (self, expr_func):                                      return expr_func

	def varass             (self, expr_var, EQ, expr_commas):                      return (expr_var, expr_commas)

	def caret_or_dblstar_1 (self, DBLSTAR):                                        return '**'
	def caret_or_dblstar_2 (self, CARET):                                          return '^'

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

		if pos and rule [1] [pos - 1] == 'expr_commas' and rule [0] != 'expr_abs':
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

# 	a = p.parse ('\int x / --1 dx')
# 	print (a)

# 	# a = sym.ast2spt (a)
# 	# print (a)
