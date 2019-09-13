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
	do  = False

	while 1:
		if ast.is_curly:
			mcs = lambda ast, mcs = mcs: mcs (AST ('{', ast))
			ast = ast.curly

			continue

		elif ast.is_mul or ast.is_mulexp:
			mcs = lambda ast, mcs = mcs, op = ast.op, do = ast.mul: mcs (AST (op, (ast,) + do [1:]))
			ast = ast.mul [0]
			do  = True

			continue

		elif ast.is_minus:
			mcs = lambda ast, mcs = mcs: AST ('-', mcs (ast))
			ast = ast.minus

			continue

		elif ast.is_diffp:
			mcs = lambda ast, mcs = mcs, count = ast.count: AST ('diffp', mcs (ast), count)
			ast = ast.diffp
			do  = True

			continue

		elif ast.is_num_neg:
			if do:
				return AST ('-', mcs (ast.neg ()))

		break

	if do:
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
			b'eJztfW2P3DaW7p+5wHQDaqDEN0n+5jjOrLG2k3WSwQ6MIHA8nkWwSRzYTu5eDO5/X54XiocUVZbU1V3VVUSrqyQWRR0eks9D8hyKV6//8n/e/faPvzR/efL1869f+u/nT7/6zn998/jV05fP/clXrx4/4a+Wv5X//uLZy69fhO82nChO4MuvIY2X+PnF07/+' \
			b'+OTxt0+/5fMXj0PoF/H0b/H0Gzr99vnjb//tC/+0fwcpxhMMfvL9q+d/h6vx5Puvvn/55Ju/hzOI+N0r+Pz+C//59MU33/3926co0/cg9d8ew48vnr38HqR69vK7v4Lgz17gHfj5H68g9nPUyNfwKyf7Bd755OsXLx4HLUHAq2d//bfvgkCvgsBw8uUXz1Fm' \
			b'EOM//MfjF9/A6csvWRFw9kU8/Vs8ZUU8ff7tU3jUq2cv4PvLZ3979iWcPCElf/sdSvTNc8yKz2TI1X9++/QJRvjy2VdfgWJePsMCfoICPH75JeQcfvj6FT8wlBKITKk+8fn7LnxDKb94/M23330N93+H+n36n09A/Rjkdd0mJcQF4NN68u/+9OMfP338882H' \
			b'j3+K84/+/O2bD+8+/fj+w4//+OmXj5/efBA/+1P/9Qajvfuf332Un//8NZx//OP3dx/CxW/v/uvHNx/+K/72kz/99c2nH9++/4XPPrz/v/GMHvzx3cePb8ez38ezkMybn+Lpp0/jw/755u2ncP47pkrBf/z2Ngr6z3/+HqUZhf7l5/H0598+jfL++scvP/78' \
			b'6+8imzIhkclw+uebmPWYOiQDJ+H607sP+W/h8g8p7Zt//COcvv3jwy//L1z8z8d3Mac/fXjz9r/fjZcfpWR/vhvT+uO3n9//Nj70zRj/bcweKnkU/31M8g+h799GkX76+bf3Yzbex1Lw8oyl8PO7t+/GC1+hhAS/f/z0fkx1LNtRlve/RHHfvv/11zfJxce/' \
			b'/NC8vrqxrnHmuqETCyfGwIdtjLrmS3+FZw4+Ggy4TgLoyob7/O8uBMEpxrqhNHRzpRrtmpu20YM/uQ6hHDYG3HRwogx9WJ+Aot9CkOonQdbKIDj1Z62iD7fzDyBR/RWcQq79v2vgcXSbhRMQQNGH66/50suEt7bNVefv1vB/HUJ6eTXwNwSBJC1kue05y6a9' \
			b'DqEUFgNuFD3CCwUSekU7TtSL1aI+WkcfdvAhJFvr8NSfaVS0T4fu4stwLsJb+rpBFSj81134WcEJpMvh9BAvHAdSJCzHduBMdWoMpTCzi9F2acCNwpqg4Tn4IN3Th6Uo/uxGow61pg/rn25Zdn+/ppKDpPvxBzv+YFr6cMM1X/rig7OhufKVAguGlOIDrLhw' \
			b'9AUB8CT/K8hoWYHhchIUSjEN19PL7E4zvSzE2KVBdnqZ3HTj9RxFi/WahcgCTB5gZYCvhmpgEfxDlEmC4+WNRs35Bnyldw20TH+HP+v8l38CXLB85RgAPXZpRF/kacQbjQ0D2kXXuLEW+x+wTbQdtz5osaZrPCTFRgg/juExxFCIiyGWQroY4iikDyE3LVZZ' \
			b'5cMVPlj19AGqY2nHIC2D4BSyYujDa/T6Op7CWUs1PeQZGjJWaMs/cPFDM9GUaZ8W1nOGO6j2WEa+4BgUd/ThAAmp8bY7PEU9AkYHiKYs+jAKCZc3mN+ek4Ha35gh1B0ZzAH+Gpvjjj58lbrma99EUbYdfViftmI82eEp5M3/CJBObdpfdXhPC4CzG8kk1BjP' \
			b'A4w3iNOkRchBO8ag+iYKBwEQtecDr1xsnXhpx0d7TiBVgphDONM7PiMIhxMTTvDxCppNy1rtG6lL/Ek1E5VzeBbVJ4kZ6+nDAgtyXukU8uLbDsXyjRor51jjoeWSuhV9WDe2ZUWtHEploA/B9QPThenpAymRIbbHUzjrwo/XfOmvwg+kP5+pTlMZdKGUgLct' \
			b'oTokYMcEoC5YKpQ+/IBROSjcZSjTAF4+n75j83oHiGwQAqG97xrfnjxW+TriC9oXwADk5aXoddN7ktw5/9/5fw8UO/+br1Stb0H++f4pnmx956HdQTzrSxgrkT/x93QILfjv79q1/t+XmH+aLzJ/4hO3Te+avmv6vumHZvDpeElaL0rrBWk13OmvPcJAVekb' \
			b'30JbL3DrJfbKh+6U755AxAai+bv8QzUk4h8F5OMfMfhTL04L8vhEWp9K65MZVDP4H0Fof7PP+NA1g1dgD3zqq/Fgm8E1nT+6puubbmh6r4626X2qXjGtr62+0C22Yg8TTvuOou8i+uoPMOt6T7CAy13r2b/xRdqZpvNS+J5L66X1RQpo7RucvwZl+gR/aK52' \
			b'0Pd4feXLBiqhLx/4gvz6Qrsy/Cso6BrZCL96/PU19BDxuoOvWpynUJwDFViL39DTo5LqqYsJ90K59oaj7agEeypY1VEloNJuw81YcNe1+Z5ieaOCqSipyFHT+N1yKRouRoulmGib9Uz6LWmWNDpqMtVgqrWSylhTXk7HSGL7IwphQ+vYUX2H2oaqUdg87lES' \
			b'5UgSZe77wZzzUGvopDbt02vaUDi1bE6zbK5QOOw3uVpGp1pG7Qj32JBGlaGyRtWwSoImZO59bsecHT1HScWRleU4ZApq5cGCCsMB5Hjd+Kw0XrjG1Zp/nJqvWx62ca9fhy6gqmx/omXmh2jIJK3PWAukAlkzkDcvJgzOfYnVkjlSyXS1ZE60ZPpaMidaMkMt' \
			b'mVMsmauBJ2JanszFzNM0n67TfKdaaphhmrDhYgtT9CoMcgzP+3Gfj+dwLReusbVsT7RsDc26tzwlOODl0QU7seHmVatH4OKJbR53XrU0zPGaox8GGpYOmn8OU54053rVspWjpZZzNQRrRxgsUbQhTPDg95Vtwyw6p46JXnKBDFxfO9JXR51kqMVt2jbrLMoe' \
			b'LXZczTqqjD2BeN+ynU5xVQ11X7GZlsHfcrijYEfRHdXkDq8GeBqoElQK0pgzV+lrcBVBNVC77/SlqoEapiO4c4RjnZnRRmi5Z68VamgdNbTOXmjl6JhE0SNA5pwMT4QgNvQeLVUlxbCk1Og0oshbRFX/j5PoTKKrjiJXnVomp1Em4Cal2CnHf1fl3/NMlK4t' \
			b'4WQKAzSt6jzEaRZOj5wBXoC1iE60iIypZXOqZePPa9mcZNmgB7MKXrKKvWT9dy2M4zQURDFWXPXKOujA3mJNP9bTCwsJYJqy59aHstUSP6zOFQ5w7tOH3DCG9vyNX8bR1a4NUMt2FTe3xOQHXpACsxYK81Drwu1KRu9I9zR9R9PgHZsSeP0FTQaPJn9C4qrv' \
			b'jS2BWkAfJngMmxoNmxqNDooOa6oMT6G2vNKu7ygFTmjghFoql1oea43EoZ9Hc9JVcUtJpEUSqTraqyNTdfRZHdmqo8+AlKFptmGEqjpvcKJDVfQ14kJStZBOs5Beg8OXqh5zUywedNVLcYoEG7XV8I6ji1cHeDIq9uNTE0+QjoYnM07FbRtcKnF0eQKZQd9D' \
			b'9qdT5E+nyJ9O0XQDXRv61TG6OwIQ8gI67+J+Dd6BaOXrq0P4qRJap6qjyBG6EYPwBTx3FEB/x+hJDK7F6pKyT298Ob4oV61ib2XDXGQviIs6XYHu3ge1jmerXXdBNc31F5TZztRmdf/Nim033e6SapqtNe0ILzbC8QEsz1C0KoNXYcCbbmEId40v/YYvXzKa' \
			b'jfD6mvwzNBks6+r8UyxaL58m9wgqNv7qqPRA9Zq91/R1cKXS8U2G4P3Dl/CluPS9/umbEue6AAUg3g4EzgMUjtUJOwf1HU7HG45S48a+Wi2CIzkqBjDld2TApBnDpw7+Hor9PGDutGLncYuL1iNW9R+FunrinJ6byMBNpOUmFN5XArrRwUVHz9kWIFRTqKZQ' \
			b'ZC7Ld+xCEshodRL7BKtDy92Lgb+oPG1LJWdp+q2a4NgiaepLRXhAidRa/faW6QstsIrtnZrsnZrsnahFnuvGwBYqGb2LXVEjdNQm0Yn1B3xfCLZUXiGjFH/TeMAR9nZ0jyOwdwT2HaF0Rw/v7DjmNDzmNMFJloY4hoY4hoY4JgxtTJ1JuPeZhB5LgUrThl5t' \
			b'4N7RV7kdeRfLzOfW8BuY4Nvq0YPAzDsLdANVA0qjhyTYIo83EQRipTTXoad9EbNo2FIstxQbhhfUUiy1FEsthb4G+oathoL/oK2doNNsX15uy/BsqfJbqvy2jlOONkxUWAr5O29sXVp9okUGnGBpCZkLm5Y4mG7xIoP/wtixgTw6JijHzc5Rs3PU7OC2ZqwF' \
			b'rnpHTsnIUmfOP6RjmsFvfg8iKpz7Ah2ruKtqLKyERf1Aneuwn0OrH8fX+QXd9tTjQut0C6/zgxdNwjsmYYQ8VmxQINXjntLsuUiow0avAbzCe/FbcceNhtkozFALqVBIbdVLCQNMz6MyS/6yUKOUHELCeyp3VBXxGyKQRWrXvN7hzpkGrUewE8iAWdRIREh9' \
			b'4IWrMHO4fSzkCGmPOJf4l6XvsFwUTxWR8qSGkjJwoH1Wfan4aAaBCJd1gPoI1MqrLdEsGrgFmqLXE2wdBnQOb9qE12zCOzbhPZPwkkl4lx68bBPeNAnvV4TShreiwrs94b2eoCxQFHQZYBk0WF/h/ehQaEDD8MJaeFstsC5MAcGbVUHOATTl9bSD3Tlhl1So' \
			b'N77iwFo9WIsG9A/jf1hWD1qFvgmqFiqXvw8UDAsioVLAekiwUsALZGCltoH9UH04eEJDfYTKBi5o4CcDXlngQgIe4TBq7ztfsLgDOG4xCpv9wua3sONsgzvCwt7YPWxpu4NdZWGfW9jaG3fE3uEG4A3uk9rCrwqj4E+41WuDO0gPkArsXAw1+AY6NrAz7k2L' \
			b'm9HCdqmwpTZGhE10MTFIFarvDdTdmwEfj3uA+/AB9j/taTdZr80bXxI3PW6s29L2yR3uOa1xA2PcZRV2i6adkxvcxlRhei3lbYCs+h+7jjOA++rCjzvMvY8L29P6+nfjcLtqhTve4g7isAU07BwMWe5Bvh0kglvk7gxuuYqbFcM23KA4A/snK9xi+QYqJu5H' \
			b'3MPeyT5SD+f4AEhQ467nA299DiGwKTLsiwsi43bXuK3uDWwp3EEYxFWoBthTGjIE3z4ZX+o3vsRvYFfnDksBcgBbvjuSAAAKt9U1qBf4BxWgvv1TerwHdQEfUNAd5Ndf9O0PgA+ACgkitPOgEBCPkCyigwkA0aYY4Q4ME74qS3gtoAYiZz+DHmoBgtwXeuzu' \
			b'CEFsAUX8PeCRsghNLKja5gBil0CIxWiqx68cSGyEkiKY2PuBE3y6v9OOf0VQwR9KwGKXQcu9wsodAktfABd84EKAaf5lHgEn2UfASn3rv+z/x+72LOqMw2Iai+OonjplUwRSQzI4z+YE9mMS9BTbxchkU3AS3ccyUOkJVu2CvSTY1SR04VzEQD1J7snGWRAB' \
			b'azidIDuMAeKcgLmWoS74jUlfsgB9hfEMvFMY4dDHg81g52ARXlu9GBp9HNjhOIFIKNj+FlBpCS7hzWG7fj1seh2ug06dwaeKEAqupQmM+t/gtaYjnLbUJ4OvFFGpNTGkQtP1SWMLZmCFc1/q+EXwCmOSHaERfuMMlSKUxccQ0FK08RhRF++ZwG4bu3GYDuLs' \
			b'avxFOQZKYoLBJF/8n2AyCwp1eFc8FGmmH08lXOfJJ4/CNhYSiaEE7ANCcDdiOyuSYyPOhwcGuA+6dk6kiAQQTud4gMp7KRWEshaEwEHLaQELP/JCogGwTq4nCRIp8gSraYYnYhUMZIHxA2HQzZI0RulG8iDacPoREDyxB+DdI2wEHgQeAdn5BvzIKwloRU9o' \
			b'ZbeiP3tbNtkdg1CITQKVqBV00h2AUiqdEJ3Y+6SUliilzSkFNNIu6ahDk2iZSVpmkpaJpI1E0iZHJJK2SCRtJJJ27LBs4ZKWqKQtMIkUZ8IiFKxdLni8xVLqgT0QidRMXKguLdaWNFiOCRLykLFaui3SBgU7IRtyBseeo4x2FWVwYpIyKGgFZbQpZcQMbeOL' \
			b'Fqt7yhntPsqI2gmUIYYYpFFJGPz7ProosITZPuVxW4o4KjnUccYZjzMMkYKZjDMWzf62HFFREsgIhhnBREYwyREZwRQZwURGMJuYwBATmAITSDEmTEDB2uUCx1sspZ6MI4oRoXLkQUQBpCdBADIOEkDQKXMAXTohFXIAx5rjALOKAzgxyQEUtIIDTMoBMU/b' \
			b'OMBk+G/24X/UTMB/I/Df5PjPeds6XLCVCCoRnBsROCICNyECt4gIHEVUlAQSgWMicJEIXHJEInBFInCRCDZN7+Mj6OYJEUgxJkRAwdrlAsdbLKWeEEExIlSOPIiJwGVEIOMgEQSdMhHQpZPR3DDGmiMCt4oIgqoFEVDQCiJwKRHEPG0jApcRgdtHBFEzgQic' \
			b'IAKXEwHnbSsRuEoElQjOjQg6IoKJMwiELCCCjiIqSgKJoGMi6CIRdMkRiaArEkEXiWCbnaEjIugKRCDFmBABBWuXCxxvsZR6QgTFiEMhiImgy4hAxkEiCDplIqBLJ6RCIggpzRBBt4oIODFJBBS0ggi6lAhinrYRQZcRQbePCKJmAhF0ggi6nAg4b1uJoFtq' \
			b'lz4TOlCVES6IEQZihGHCCINgBLgAVQ8zvDBQdEUJteEaeGGIvDAkR+SFocgLQ+SFYRMvDMQLQ4EXpBgTXqBg7XKBk7ssPSChhmJErCVZEFPDkFGDjIPUENTK1ECXTgiG1MCx5qhhWEUNnJikBgpaQQ1DSg1CxE3UMGTUMOyjhqiZQA2DoIYhpwbO21Zq6Cs1' \
			b'VGo4V2pQZFNWE5uykgZlReMFRNYCNSiKge2HzcqKzcoqmpUp1niM1KCKZmUVzcoUYS01KDInq4I5OREjpwYO1i4XOLnL0gMkNZQjwp4ieRBRA6kqUkMSB6hhVCtRA186IRhQQ4g1Qw1qlS05JCaogYOWU4NKbckiT5uoQWV2ZLXPjiw0w9SghB1Z5XbkkLet' \
			b'1DBUaqjUcLbUoIga1IQalKQGRdSgZqhBUXRFCSE1sOuqimsEKNZ4RGpQRWpQkRrUJmogp1VV8FlNxJhQAwvtcoGTuyw9IKGGYkSghjyIqUFl1CDjIDUEtTI10KUTgiE1cKw5alCrqIETk9RAQSuoQaXUEPO0jRpURg37vFKFZgI1CKdUlfukhrxtpYZ2dxor' \
			b'Heoyh0oSd0kS5H6kJu5HSrofIUzt8CuQBJxDJTeRKvgmRckhVbArkoquSBRrPCJVFF2RVHRFUptckRS5IqmCK1IixoQqKFi7XODkLjvmOmGLYlxgizyI2SJzSEriIFsEzTJb0KUTsiFbcKw5tljlkBQSk2xBQSvYInVIEnnaxhaZQ5La55AkNBPYQjgkqdwh' \
			b'KeRtM1vgalxynCX87xD52xzwAepdwOE5EBaAGoASwdAS8AHAjcBFYIUgpBJAgMY9NEc9cJnyiawYrDxaefQOeVTTPJyezMNpOQ+naR5Oi3k4OPeljl/Eo5riQT3QPBuneTZOx9k4ijUeI4/q4mycjrNxetNsnKbZOF2YjUvEyHmUg7XLBU7usmOuJY+W4/rq' \
			b'MgkiHtXZhFwSB3h01CzxKF86IRvwaIg1w6N61YRcSEzwKAct51GdTsiJPG3iUZ1NyOl9E3JCM8yjcu24zifkwu+beXS6ELCyRWWLs2MLS2wxeV2Hlu/rgAtgCyvYgmbn8IvZggKRLfj1HZSIwu/AFjY5IlsUX+mh4zs9KMJqtrDEFrbAFlKMCVtQsHYxDlSs' \
			b'XHo7ZjuhC1s4kC7yIKYLm9GFjIN0EVTLdEGXTgiHdMGx5ujCrqKLUCSCLihoBV3YlC5inrbRhc3owu6ji6iZQBdW0IXN6YLztpku9qwIrHRR6eJc6IKWhujJ0hAtl4bABdCFE3ThiC6iPUfTFdIFLxPRvExEx2UiFGs8Il0Ul4nouExEb1omommZiC4sE0nE' \
			b'mNAFBWfS5sLbMdcJWxTjAlvkQcwW2WKRJA6yRdAsswVdOhnNDWOsObZYtVgkJCbZgoJWsEW6WETkaRtbZItF9L7FIkIzgS3EYhGdLxYJedvMFnuWDVa2qGxxLmxB60emLxPVcv0IXABbdIItOmKLLrJFRzcpSg7ZgteS6LiWhGKNR2SL4loSHdeS6E1rSTSt' \
			b'JdGFtSSJGBO2oGBuqDMHsgWdJWxRjDsUgpgtshUlSRxki6BZZgu6dEI2ZIuQ0gxbrFpREhKTbEFBK9giXVEi8rSNLbIVJXrfihKhmcAWYkWJzleUhLxtZos9awsrW1S2OBe26Ikt+glb9JItemKLXrBFT2zRR7agZJAtemaLntmij2zRJ0dki77IFn1ki01v' \
			b'pcJH0M0TtpBiTNiCgrXLBU7usuNZwhbFuEM3DWK2yF5JlcRBtgiaZbagSydkQ7YIep9hi34VW3Biki0oaAVb9ClbxDxtY4s+Y4t+H1tEzQS26AVb9DlbcN42s8XiBYiVLSpbPFi2MGTmNhMzt5FmbkNmbiPM3IbM3CaauQ3Fg3pg2Mxt2MxtopmbYo3HyBam' \
			b'aOY20cxtNpm5DZm5TcHMnYiRswUHa5cLnNxlx1xLtijH9dVlEkRsYTIzdxIH9/YLmiW24EsnZAO2CLFm2MKsMnOHxARbcNBytjCpmVvkaRNbmMzMbfaZuYVmmC2MMHOb3Mwd8raZLaZrEncXQxi6wBmq8sZZ84YmN2M9cTOGbqX0NNbkaayFp7EmT2MdPY2h' \
			b'krOnsWZPY82exjp6GlOs8YgDjaKnsY6exnqTp7EmT2Nd8DSGehjlmIw0KFi7XGJ59GzIoLjji3AdjTdKd+B4Iw/i8UbmcJzEwfFGUDCPN+jSCQlxvMGx5sYbqxyOQ2JyvEFBK8YbqcOxyNO28UbmcKz3ORwLzYTxhnA41rnDccjbZgaZLl2sDFIZ5HwZxJAN' \
			b'3Exs4F4LRprBDZnBjTCDGzKDm2gGN3SFgw82gxs2g5toBqdY4xEHH0UzuIlmcLPJDG7IDG4KZvBEjMngg4K1ywWWR0+2DY47EkhHQ5DSHTgEyYN4CJIZw5M4OAQJ+uUhCF06Gc0NY6y5IcgqY3hITA5BKGjFECQ1hos8bRuCZMZws88YLjQThiDCGG5yY3jI' \
			b'21YCUXV946EnrHx6PsuVPu6CPnafoRC3dL0jGcfVxDiupHFckXFcCeO4IuO4isZxqP9sHFdsHFdsHFfROE6xxiOudywax1U0jm/b0EmRcVwVjOOJGJP1jhSsXS5wcpcdc52sdyzGHQpBvN6RjeMKX/ixi+seZVxc9xg0TCzCl07IiOseQ4oz6x5XGclDYnLd' \
			b'IwWtWPeYGslFnrate8yM5GqfkVyNRaSEoVyRoVx1Yf1jbiwPedzMJnt2I61sUgchJ8Iitx2EwMak/kHwlbKH3Qn2gAuftBUv6IVzX+r4RexhKQLuuroj9qBEFH4ze1Cs8Yg7se5K7AGhzB4UYS174CPo5pw9EjEmm7NSsHa5wMlddsy1ZI9yXNjKNQ8i9iBt' \
			b'xbFHEgdYY9QssQZfOiEbsEaINcMalNhS1giJCdbgoBWbwe4S1hB52sQaJE9kDcrQDGsIzTBjoOzMFqRNwRYhb5vZoq4Jr2xxAWxBxnI7MZZbaSy3ZCy3wlhuyVhuo7HcUjxkCzaWWzaW22gsp1jjEdmiaCy30VhuNxnLLRnLbcFYnogxYQsK1i4XOLnLjrlO' \
			b'2KIYF9giD2K2yIzlSRxki6BZZgsuECEbsgXHmmOLVcbykJhkCwpawRapsVzkaRtbZMZyu89YLjQT2EIYy21uLA9528wWdU14ZYsLYAsycNiJgcNK64Yl64YV1g1L1g0brRuWrpAt2Lph2bpho3WDYo1HZIuidcNG64bdZN2wZN2wBetGIsaELShYu1zg5C47' \
			b'5jphi2JcYIs8iNkis2skcZAtgmaZLejSyWhuGGPNscUqu0ZITLIFBa1gi9SuIfK0jS0yu4bdZ9cQmglsIewaNrdrhLxtZouHuCS8A8LwFadyxnlwxu4+3+BIvKEmvKEkbyjiDSV4QxFvyJf90hW2LOYNxbyhIm9QrPGIFo0ib6jIG2oTbyjijZZfJoIYBwVP' \
			b'Lvxs2sDEgxAT2wY9Wrtc9CQbdsx/YtsoxgXbRh7Eto2MQZI4aNMIOmabBl06Gc0NY6w5m8YqBgmJSZsGBa2waaQMIvK0zabh0KaX2jX2sYjQTrBpCBZROYuE/G1mkbpUvPLHBYw5yBpuJ9ZwK63hlqzhVljDLVnDbbSGQ91ka7hla7hla7iN1nCKNR5xzFG0' \
			b'httoDbebrOGWrOG2YA1PxJiMOShYu1zg5C475joZcxTjDoUgHnN02ZhDxsExR9Asjzno0gnZcMwRUpoZc6yygofE5JiDglaMOVIruMjTtjFHZgW3+6zgQjNhzNGJMUdu/Q5528wWdal4ZYsLYIuB2GKYsMUg2WIgthgEWwzEFkNki4FuUpQcssXAbDFEthiS' \
			b'I7LFUGSLIbLFsIktBmKLocAWUowJW1CwdrnAyV12zHXCFsW4wBZ5ELPFkLGFjINsETTLbEGXTsiGbMGx5thiWMUWnJhkCwpawRZDyhZCxE1sMWRsMexji6iZwBaDYIshZwvO22a2qEvFK1schC3Yf/JeWQOnSfYxh83YwwoGceQ/5Sb+U076Tznyn5IbnDvy' \
			b'n3LRf4ojQN1w7D/l2H/KRf8pijUeI4O4ov+Ui/5TbpP/lCP/KVfwn0rEyBmEg7XLBU7usmOuJYOU4/oqNAkiBnGZ/1QSBxhk1CwxCF86IRswSIg1wyBulf9USEwwCActZxCX+k+JPLVjaqt5xGVzVG6fF5XQDytAU2UOVOKkIxXWA3nTdkLZs8Otbc5qA8Pj' \
			b'7F54htRx9IEGOKGDY7r63Lo/GnSYyaDDyEHHjSQLuX+hj2V4oGF4oGF4oGHiQINijUdc6JcPNKBumTjOMJvGGdCscaFfYaBBFS/+Txf7kYTa5UJH6S3lNXnHSDEiLPAT11BJbnDzIUUaS3gCpKF4reFl4nTCPMG/49bnRlwO4+nsOr9Vo41QonKdHwUVuYIy' \
			b'ky3zSwcbmG8bZNwy3DBiuIHwY/YtFY8FMK70E+MNKAioFeD4lo08Qj5TojDADGYXmcI8op3r/Tdgm2+vj2i/rMgYeza+PU3GODJLBIYI7GAFKwRGCEzwQFjg6AywD/WhrcFAwU4GCnYJ6kPtsTw4sDw4sDw4sHFwYJMjDg5scXBg4+DAbhocWBoc2CnqTwcE' \
			b'JIV2uZBRWkspJkOBYkQYCuRBNBQgkA/jAM74Tvb9LXX8LXX57Z7+vl3V3w9KFv19ClrR37dpf3/M3PpOvk07+SjSfC8/PojRG+UOXXybYXbI177OPffpAZn1nmXZFZkrMh8fmclk7CYmYydNxvPI3FFERUkgMrOZ2EUzMcUaj4jMRTOxi2Zit8lM7MhM7Apm' \
			b'4ikyk0Ta5UJGaS2lmCBzMeJQCCohM+ssQWYyATsy/ro9ll+3yvIbniWRmYJWIHNq+Y2ZW4/MmdH3M8gcHxSQWVh9XW71Dflaisx7ljhXZK7IfHxkppkSN5kpcYtmSgBGeKbE8UyJ45kSF2dKKNZ4RGQummRdnCpxm6ZKHJlkXWGmZIrMJJF2uZBRWkspJshc' \
			b'jAjInAeVkDnoSCIzzYE4mvtwe+Y93Kp5j5CYRGYKWoHM6cRHzNx6ZM4MrJ9B5viggMxixsPlFtaQr6XIvGc58Wkic53/vvj5731IDi3RPwgbZILkEPJ5JIfqxTO4+O3zQzdSOCM5xRqPEckx6gTJIZSRnCKsRfKO5rzhK0fyRIwc1TlYu1zgeIul1CWqlyP6' \
			b'yjEJkqgup7uTWADwpFLCeA52QigA+xB7Bu8ppaV4HxITeM9By/EecxjxXmRo0zQ3yRNBnzI0g/lCM4z5KDtjfpfPbYe8LcB8OZOt9ywOrthfsf/hYb8m7NcT7NeLsF9TREVJIPZrxn4dsT89IvbrIvbriP16E/Zrwn5dwH4pxgT7KVi7XOB4i6XUE+wvRgTs' \
			b'z4NmsV/GQuzXAvsp2AmhEPs59hz261XYzzdI7KegFdivU+yPGdqG/TrDfr0P+6NmAvZrgf06x37O21rs37PUt2J/xf6Hh/2GsN9MsN8swn6OqCgJxH7D2G8i9pvkiNhvithvIvabTdhvCPtNAfulGBPsp2DtcoHjLZZST7C/GBGwPw+axX4ZC7Ff+LhwsBNC' \
			b'IfZz7DnsN6uwnxOT2E9BK7DfpNgfM7QN+02G/fu8W4RmAvYbgf0mx37O21rs37NAt2J/xf6Hh/3k8dJNPF66RR4vUKvY46Vjj5eOPV666PFCscYjYn/R46WLHi/dJo+XjjxeuoLHSyLGBPspWLtc4HiLpdQT7C9GBOzPg2axX8ZC7LcC+ynYCaEQ+zn2HPav' \
			b'8osJiUnsp6AV2J/6xYgMbcP+zDmGMjSH/VEzAfuFb0yX+8aEvK3Fflxu67F7fv+bM6WAYTjCbjdbmUCtYIPugTBCf8+sAEhrYOqdFk7d6InbjVeHWsQQmBRPDSmmCMUUoSJFQCsRR3y7T5EiVKQItYkigi+8KnBEIkfOETe43yaxRCZzvMlSVpXB6oVM0eNr' \
			b'g2biw3t98qA5skhi4Zt9BFlwsBOy4Wt9OHZCFkP6ap+9hAGvlpq83icUTiQNDlrxep+UNFB3hmXd9H4fw5VssYlY6ImpQwnqUDl1hBxG6sAQ+PT84T/7HX62GO45BL4M/IIM0vmmlfPHHHNAW0S2IKogbpDEgKywlBLmHHSQAADoRUcfILzoUiNdaRRD8B7o' \
			b'XdwJl1C7FGIlvLr1kLoYSgN8MnQmsBngEqrDPFQuAMnQzNnxJYDiiIIFCAz4dwvw+7xvS0A6QLSk0wuQVXRNSZ1SAIlupr4oKfSs6KgmaLMCZyTIAMKsR5YVkDIiyQgjKYYE9ABA6AuAsKc3eT+YMPYLhxIyhM7diSNEO8DKsvb2SAFd+CJalDpdilerDwtQ' \
			b'4zM9LOo1PVzoEB0lKOcyhEAeTW4TO2koUdAp1d0BIEWZbH4zwsoEUqDS8QpvqFBL4WVY0d8w9w4vcsCJOAPN9tCdEFgX6uVoYUGoF+ZuOyX5uG9Lx8QduHPyOZhZADFh/HbiMDOiSfhnyGkRWe6g54LcAK0GZneo8d55T8boQ0CPzVyqRuhR+F7BjT2a5l8K' \
			b'VgX3DgY7vgasGux0nwMfd2D8CX2bnQAdc4Gjn3ZPn0ZOIMG7bzWDDcxpdlPQwV0WIczf6/OnfP4UvBI6vo3H//eHASVqu3o1KOkjANMIREMEIijIyx5GKWs+0+cRb12GJ1iy6Cq05tLLD3IoinOZKDZo0mIm4DFx9zC4UNBF8qW0eUrGzMzY3wlKMUKhuWHY' \
			b'g1LqASCVWjkCm+sSFbpDtrufLtFMd8hI9DFFt8ajoU9EHijEQe9BH6MfEAJBfVg78nIz3Z9i1wcq08IRl69YpzbDOwMkPrNQXFCeUHFA7fff9cntbPfV/fHnGsoAzpdO78iukJ4BmNDluYuuzomPvaYgA/lD2+kNvZfIHG/a2B2zy+ODQPWIqaCx5VM+cdwV' \
			b'uj7FHo/lTk7etdHN6yPj0JznwUGtTg9xzKUOMbETAQWbw0PDE3T5QNcOi24c92V9OnqH5VZDJnsg61Pzr+6R5yGcqTFHB4rPgYOv07fvpTwUoFjTK1kJFOfS85jvdWh01TpAb+OBwQTnenn/YrmV2su3CR/svUIE2M0PMpjZ6kqeOwzeE1yAh9EDgAx4G/4p' \
			b'4wY8BqcFDjNWkeiBOdsIIVBd7xVHoD+6frCyAkzcNjBx9wsmAkhAtqP1Oe4RSCqI3NYpLgUQKLijd0HuHT/uFDu6bdjRHQ87XMWOih0bsAMErdhxSOzot2FHfzzs6Cp2VOzYgh1txY7DYsdw8hOkZz8perrgcLq4cEgQUJink53+PHCjb/7lW8IjAD4wkHit' \
			b'1/Z/gu3/AJbTB4UB2HQOAwHUCs/KAjIDAbc0ku4eIfK2uN3VjuCgrXBQ4eB+4QAr64l1CS4SEJzvFhh8H4wvjQoDFQYOAAPY5B/syOAiYcDqRx68EQaO72ZZYeA8YIDqW4WBBwkDp+9EWWFgBgbmNgW/b0jAFnwSU4Z458kgAklzZ4CAya8EBIWQ2Uz2yo7Q' \
			b'EPbHntsYG0Fjo2dlBY3jg8ZxgUKfDFDokwIKfbdAoQ/Wc1gEDxt9JSs8XCQ8YE07Q9PjLeGBGuADG1jAa6fR83hAMyRuOGk3uj9WOLggOMCqdNaeCMvgAPVwNvMMBsyQ0KB67CUQHGz0aKxwcAFwgNXrMjyT9uMBKuL8Jh617x/AlHHvgUErhIPqpFjhIIMD' \
			b'bBSX5ad4kWYIDd2DHcKAq76KlwkDwyl5Kp4ECkBil4MBbf8ImcA3CTjBIYKrnooXAwbQsI/vp3iyYHBpXYIWJxDRNcFVR8XLQYGT8FauKHCCKHD6forQewnvpb1XRAgvDjvmu2jrAscNb22CxuvvPgpSQDM+Jl74oFnUuMViZ3d8R8ZNr43VAivc6fcgtuwD' \
			b'u7gXYbJtO84aL2i74PR/pRMT3FHcbfUBdDS27ZS6oreB2hk34ugW9Do698iDOHY6ju/gWMGkgskaMOkm/2vBpKtgsgdMOgkmahWYHN8dsoLJAcHkzIGkn/yvBZK+AskeIOlXzIMIEOma1z1CB+IGgwYhhkKsUIgSHeKDBAdEBm7j2B4Nt8GB216p3WlqY9A+' \
			b'8jaRtAED24iH+h2q9lirxxoNeaWK3FP1xZqLrygr1NhYW2Md66j8cQGBozIvFjeUtAklMi2FVOltjyPH/laqJSgNIKoJMAEIE2X3KxQ+A0QTxWOruxvNQwawtY8loDhVXNMki2NsiouKZL5xFItmuF3RdDOlszuHEtpFTJ6UUoDTeyspj4SvIftmh9mG7YCt' \
			b'xh9a/4PvdoA6qB/hMBh2HFNAmV57GKD9qYWdp5TzMfz31Y2/FTxiG9ivFvZPhL0LYddCl2zCPG7tDtvTwF7GuKW5hefhXvC+zzXQfqnjLoTQPQEVig2Ww77rsMsfSg97oWMObtQtxfDXn/vD52h4jp15Eu2HZhY+UkPHTid/cbszm/2CfyiBKUjQ4o6RFl9l' \
			b'3sGLRRcKhLsQjFPUcN4LITUL6vM3/kFDMfwS0fg/94e/Q6cPOqvQ4dMUDqM9g7mxt8wNNP3VGfLd7oV/0DOe+Q3Fd6vF15/LQbZ10WyO1JDlygPp3j/o8U9DqS/ec59bp7/5TiGeYV67aV69DHPZ9bfCIMcmA5s9OvD4DR3TnUG3WuhmQX8L34/l0RN6d6OW' \
			b'YJUiuOGDL7Jpo9Y8+OEkHXSRUYOgScOa7PZr0/f0aYRCryNE+oja9RVW4UaxvAcs9Kia+AeA32d/ZHUq/+dx98eWd30urM/O5p8if89SxdLuT6hme4I45B/mbzjF2gwdn1KNhtmie6nV0I07gQMmCvIgfN/9oQ6sAr6rcTp1HKabjnCQItpREUDY7s6ahHqg' \
			b'rcI2dAw4EzdeHvjo7i7pdQdVCnWQ1gHjssM0ENjx9dYHzHKuvo30obNGApOVd8ce2FRgLvXBtRaYARCHz8PQNVngYQ+YHLjTByw7qJoUxmd7qsbn+xAHaTw4kZ4cMCU8DV1ygIVg/W2kHFvb0LI21DcXeVAtKYyqj9+EwOh3zINU09UGtKgBwdTzJR5USwqD' \
			b'91s1ICj+wzQi3RzwANv0+ttIRUNtSMsa0tBc5EFWhcIMwa0bEhT/QRoTuJ4c9AAfj/W3kabyKYTansrtCayhl3hQLSnMKRykPbX9odqUbg5+gIvU+ttIYXXSYWGzMs1FHlRL1s05uE2miw2tK5Re2sJss/wAn7EVsYfFscGdUFyTGuvsxMLG1jUXeVAtWTc7' \
			b'sa2xFWrA7Rte39zdIV1/N6VAuq3TG8taILjSXeJBtWTd9MbptEBYE3CiBym2ToosbH6muciDXCB3tZbsIMu7cm2xfawxYCqjWuP/EQJsc8aHMuBerKbBqnRGtald7Yh1aM+r2+F6CR76ZvkBHuSrbpgeYZ3V6vtwfVRcG4XlsW6K5kGUB6y5e0gHFUTB1fzB' \
			b'F4RqHtRBBbFuduUuCkK3KwvDLi0Q3dz/ASx6y0hUMIXFA0s6HydQNm5p+Zhm1QGrgtbec5tj//OolNbNlzzIUnLNgz2ojDau7XhIZdQ3D/agMlo363Hu62/grQnrD3ozQvzflkoh0Wny4jKJsyih9KDyP8kVK8cr/7Y564PWeq7zPzn7MnfNWR9U5usnRM66' \
			b'zLvmrA8q8/WTLmdd5n1z1geV+fr5nbMu86E564PK3DSvdQuL2XbkcuI7fCGA0d9BAOgUA+HdV9wV8EM0WSu85iEGGGFgzR6YYeDtK4rT7cuxfUml/xR7mMSG0sQ7fLlm/4pdqO1OvjUE6waFewKTlZTqlKxLoR7ha1rgbnxnWXxXGb0jLLwfrBPvBfO1xZKi' \
			b'fNTX2TvTQAhlURx45PgoqKoDVUWe0vPBr/EtcTtcHAWvJ9PUKr1cr9Gyg9Pjlq02ysDbCf39vrWpnmPa+DIUUjrsqasclKbiPjtsq+lTwRCqAbCzHof0Ps4P1/8LnPzZLA=='

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
		('STR',          fr"((?<![.\w')}}\]]){_STRS}|{_STRD})|\\text\s*{{\s*({_STRS}|{_STRD})\s*}}"),

		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
		('COLON',         r'{:}|:'),
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

	def expr_neg_arg_1    (self, MINUS, expr_neg_arg):                                 return _expr_neg (expr_neg_arg)
	def expr_neg_arg_2    (self, expr_diffp):                                          return expr_diffp

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

_RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: # DEBUG!
	p = Parser ()
	# p.set_user_funcs ({'f': 1})
	# a = p.parse (r'x - {1 * 2}')
	# a = p.parse (r'x - {{1 * 2} * 3}')

	a = p.parse ("{{-1}'}")
	print (a)

	# a = sym.ast2spt (a)
	# print (a)
