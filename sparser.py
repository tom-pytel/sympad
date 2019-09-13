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
			b'eJztXW2P3LZ2/jMF7i6gBUZ8k+RvjuPcGrWd1EkuemEEgeP4FkGTOLCTtMVF/3t5XigeUtRY0s7uzM4Qqx1JFEWRh+TzkDyH5NXrv/zLu19//EvzlydfPv/ypT8/f/rFN/701eNXT18+9xdfvHr8hE8tn5U/f/bs5ZcvwrkNF4oD+PxLCOMl/n729K/fP3n8' \
			b'9dOv+frF4+D6Wbz8W7z8ii6/fv7463/9zH/t3yAW4wU6P/n21fO/w9148e0X37588tXfwxV4/OYV/H77mf99+uKrb/7+9VOM07cQ6789hocvnr38FmL17OU3f4WIP3uBb+Dvv78C389RIl/CUw72M3zzyZcvXjwOUgKHV8/++q/fhAi9ChGGi88/e45xhmj8' \
			b'u/95/OIruHz5OQsCrj6Ll3+LlyyIp8+/fgqfevXsBZw/f/a3Z5/DxRMS8tffYIy+eo5J8YkMqfqPr58+QQ+fP/viCxDMy2eYwU8wAo9ffg4phwdfvuIPhlyCKFOoT3z6vglnyOUXj7/6+psv4f1vUL5P/+MJiB+dvKzbJIc4A3xYT/7NX37844ePf7758PFP' \
			b'cf3RX7998+Hd79+///D9jz/8/PH3Nx/EY3/pT2/Q27v/+c17+enPX8L1xz9+e/ch3Pz67j+//8cfv76ND3/wl7+8+f37t+9/5qsP7/87XtGXP777+PHtePXbeBWCefNDvPz99/Fr/3jz9vdw/RuGSs4iAj/+9I9//BZjM8b655/Gy59+/f0/w/Uvf/z8/U+/' \
			b'/CbSKQMSqQyXf76JaY+hQzBwEe5/f/chfxZu/5CxffPjj+Hy7R8ffv7fcPM/H9/FlP7w4c3b/3o33n6UMfvz3RjWH7/+9P7X8aNvRv9vY/JQyGP038cg/xDy/nWM0g8//fp+TMb7mAs+PmMu/PTu7bvxxpcoEYPfPv7+fgx1zNsxLu9/jtF9+/6XX94kNx//' \
			b'8l3z+urGusaZ64YuLFwYAz+2Meqab/0dXjn4adDhOnGgOxve889dcIJL9HVDYejmSjXaNTdtowd/cR1c2W10uOngQhn6sT4ARc+Ck+onTtZKJ7j0V62iH7fzH6Co+ju4hFT7f9fA5+g1CxcQAUU/rr/mWx8nfLVtrjr/tob/6+DSy7uBz+AEMWkhyW3PSTbt' \
			b'dXAlt+hwo+gTPlIQQy9ox4H6aLUoj9bRjx28C8WtdXjprzQK2odDb/FtuBbuLZ1uUAQK/3UXHiu4gHDZnT7iI8eO5AnzsR04UZ0aXcnN7KK3Xepwo7AkaPgOfkj39GPJi7+60ShDrenH+q9bjrt/X1POQdD9+MCOD0xLP2645luffXA1NFe+UGDGkFC8gxU3' \
			b'jk7gAF/yTyGOlgUYbidOIRdTdz29zd4009uCj13qZKe3yUs3Xs4xarFccyQyB5M7WOngi6EaOAr+I8okzvH2RqPkfAW+0rsGaqZ/w191/uS/ADccv7IPgB671KPP8tTjjcaKAfWia9xYiv0DrBNtx7UPaqzpGg9JsRLCw9E9uhhycdHFkksXXRy59MHlpsUi' \
			b'q7y7wg+rnn5AdBzb0UlLJ7iEpBj68RK9vo6XcNVSSQ9phoqMBdryA85+qCZUcXwKrrCcM9xBscc88hnHoLijHwdISJW33eElyhEwOkA0JdG7kUu4vcEv9RwMlP7GDKHsSGd28PdYHXf044vUNd/7Kopx29GP9WErxpMdXkLa/EOAdKrT/q7Dd1oAnN1IJqHE' \
			b'eB5gvEGcJilCCtrRB5U3kTkIgJhz3vHKxdqJt3b8tOcEEiVEcwhXesdXBOFwYcIFfl5BtWlZqn0jZYmPVDMRObtnXn2QmLCefiywIKeVLiEtvu6QL1+psXCOJR5qLolb0Y91Y11WVMshVwb6EVw/MF2Ynn6QEhlie7yEqy48vOZbfxcekPx8ojpNedCFXALe' \
			b'toTqEIAdA4CyYClT+vAAvbJTeMtQogG8fDp9w+b1DhDZIARCfd81vj55rPJlxGe0z4AByMvHotdN70ly5/x/5/89UOz8M1+oWl+D/Pf9VzzZ+sZDuwN/1ucwFiJ/4d/pEFrw37+1a/2/zzH/NZ9l/sIHbpveNX3X9H3TD83gw/ExaX1UWh+RVsOb/t4jDBSV' \
			b'vvE1tPURbn2MvfChOeWbJ+CxAW/+Lf9RDYH4TwH5+E8M/tJHp4X4+EBaH0rrgxlUM/iHEGn/sk/40DWDF2APfOqL8WCbwTWdP7qm65tuaHovjrbpfaheMK0vrT7TLdZiDxNO+4aibyL64g8w63pPsIDLXevZv/FZ2pmm87HwLZfWx9ZnKaC1r3D+HoTpA/yu' \
			b'udpB2+P1lc8bKIQ+f+AE6fWZdmX4KQjoGtkITz0+fQ0tRLzv4FSz8xSyc6AMa/EMLT3KqZ6amPAu5Gtv2NuOcrCnjFUdFQLK7Ta8jBl3XavvKeY3CpiykrIcJY3nlnPRcDZazMVE2ixnkm9JsiTRUZKpBFOplUTGkvLxdIwktj9iJGyoHTsq71DaUDQKq8c9' \
			b'xkQ5ioky9/1hTnkoNXRRq/bpVW3InJo3p5k3Vxg5bDe5mkenmkftCPdYkUaRobBG0bBIgiRk6n1qx5QdPUVJwZGF5ThkCmLlzoIK3QHkeN34pDQ+co2rJf84JV+33G3jVr8OTUBV2f5E88x30ZBJWp+wFkgFkmYgbT6a0Dn3OVZz5kg509WcOdGc6WvOnGjO' \
			b'DDVnTjFnrgYeiGl5MBcTT8N8ug7znWquYYJpwIazLQzRq9DJMTzux20+HsO1nLnG1rw90bw1NOre8pDggLdHj9iJdTevWj0CFw9sc7/zqqVujpccPRioWzpofhyGPGnM9aplLUdLNedqCNqO0Fkib0MY4MHzlW3DKDqHjoFecoYMXF47kldHjWQoxW1aN+so' \
			b'yh4pdlzMOiqMPYF437KeTnFRDWVfsZqWwd+yuyNnR94dleQO7wb4GogSRAqxMWcrzNdgJIICoBrf6csTAFVGRxDnCLs6MyOHUFvPWB5UrTqqVp29uALRMVmi5l+mmRRMhBQ2tBItFR/F8KPUaByiyCpEVTuPk2g0okmOIpOcmienkSdgDqXY+Mafq/DvecRJ' \
			b'15pwMpkBklZ1vOE0M6dHzgBrv5pFJ5pFxtS8OdW88dc1b04yb9BSWQVrWMXWsP5cM+M4FQVRjAVXra8O2rG3WNKP9fXChAEYjuy59mHcao4fVuYKOzj3aStuGEN7PuPJOLrbtQFqWX/i5qaSfMcTT2DUQmEaalm4Xc7oHcmehu9o0LtjlQHPs6AB4FG1T0hc' \
			b'5b2xJlAN6MMAj2GVomGVotFB0GHulOEh1JZn1PUdhcABDRxQS/lS82OtMji082hMugpuKYm0SCJVRntlZKqMPikjW2X0CZAyNMw2jFBVxw1OtKuKNkWcSapm0mlm0msw7FLVMm6KxYOucikOkWClthrWMrp4cYDFomJ7PTWxBOmoezJjPNy2wXQSe5cnkBi0' \
			b'MWS7OUV2c4rs5hQNN9C9oaeO0d0RgJD9z7lm9Guw/0P9Xl9Nvk+VyjpVTUSO0IAYhP3fudb/KzRuJGthdQHphXTqU6ElxQbIhgnHXgThdLqi2b33WR0PRrvuIsqY6y8imZ2pVen+qxKrY7rdZZQxW8vYEVYjwiY/zLVQNMWCp1TA8rTQK7vGlbrh5HNGs0Zd' \
			b'X5OxhSbtY51Sf4pZ6+OnydaBso1PHeUeiF6zKZq+DnZROi4/CKY8fAsnxbnv5U9nCpzLAmSAWNIHLAHIHYsTNgXqwkvH62FS5caWWc2CI1kdBjDlhS1gHIzhUwfjDcVGGzAQWrHzuNlFkwur+I9CXT1xTs9VZOAq0nIVCouMgGx0sLfRc4oCcNXkqskVmcvy' \
			b'G7sQBDJaHZc+weLQcvNi4BPlp20p5ywNs1V9GqsXTV0JhDuUSK3VCG+ZvFCdqlh5qUl5qUl5iVLkMW10bKGQ0QLqiiqhozqJFqnf4SIfWFN5uotSfKb+gCPs7egdR2DvCOw7QumOPt7Zsc9puM9pgsUrdXEMdXEMdXFM6NqYOpJw7yMJPeYC5aYNrdrAvaPh' \
			b'cTvyLuaZT63hZZPgbPVoDmDmNf/dQMWAwughCFav40sEgVgozXVoaZ/5+BnWEct1xIaOBdURS3XEUh2h00Bn2BkomAHa2vw5zZrl420ZmC0Ve0vF3tYeytE6iApzIV+6xtYZ0ieaZcAGlmaCubDHiIOBFh9lWLhsbNJAGh1Tk+Nq56jaOap28FozlgJXjRyn' \
			b'ZGSpGec/0jHN4JmXLUSBcyugYxF3VYyFCa0oHyhzHbZwaBLjuPpekG1PbS3URbew+h6sCwlLQkLfeCzYIEAqxz2F2XOWUFONVu27wnfxrLjJRh1sjMxQM6mQSW2VSwkDTM/9MUtmr1CilOw8wrKSOyqKeAYPpIvaNa93uNGlQb0RbNwxYBI1EhFSHxjTKkwc' \
			b'7vYKKULaI84l/uXYd5gvigeJSHhSQkkeOJA+i76UfTR2QITLMkB5BGrlSZOoEA3cAlXRywl2+gI6h4UxYVVMWBITFoeElSFhSTxYGxOWh4SlESG3YRFTWIoTluEEYYGgoMkAs5lB7wrLmUOmAQ3D+rKwuCywLgz+wEKoEM8BJOXltIPNNGFTUyg3vuDAlDuY' \
			b'Ugb0Dz1/mB0PUoW2CYoWCpd/DwQM8xqhUMC0RtBPwDowMOHawPal3h0MmqE8QmEDIzOwigHrKzAbAcNu6K/3nc9Y3LAbdwSFvXlhr1rYILbBDVxhK+sedqDdwSawsC0t7MSNG1jvcL/uBrc1beGpQi/4CHdmbXDD5wFCgY2GoQTfQMMGNrK9aXHvWNjdFHbA' \
			b'Ro+w5y0GBqFC8b2Bsnsz4Odxy27vPsB2pT1t/uqleeNz4qbHfXBb2u24wy2iNe43jJuiwubOtNFxg7uOKgyvpbQNkFT/sOs4AbgNLjzcYeq9X9hN1pe/G4e7SyvcoBY3/IYdm2GjX0hyD/HbQSC4o+3O4A6puLcw7JoNgjOw3bHCHZFvoGDi9sE9bHXsPfVw' \
			b'jR+AADVuUj7wTuXgAnsYwza2EGXcnRp3wb2BHYA7cAO/CsUAW0BDguDsg/G5fuNz/AY2Ye4wFyAFsEO7oxgAQOEuuAblAv8gApS3/0qP76As4AcyuoP0+pu+/Q7wAVAhQYR2HhQC4hGSRXQwASDaFCPcgWHCF2UJrwXUQOTsZ9BDLUCQ+0KP3R0hiC2giH8H' \
			b'bFEWoYkFUdscQOwSCLHoTfV4yoHERigpgom9HzjBr/s37fhXBBV8UAIWuwxa7hVW7hBY+gK44AcXAkzzT/MIOMk+AlbqW3+y/4fN7VnUGbvF1BfHXj01yqYIpIakc56NCezHJGgptouRyabgJJqPZaDSE6zaBU1J0KhJ6MKxiIFaktySjaMgAtZwOEE2GAPE' \
			b'OQFzLUNdsBiTVmQB+gr9GVgaGOHQ+4O9W+dgEVacXgyN3g9sSJxAJGRsfwuotASXsADYrl8Pm16G66BTZ/CpIoSCOWkCo/4ZrE46wmlLbTI4pYhKtYkhFaquDxprMAMrXPtcxxPBK/RJdoRGeMYRKkUoi58hoCVv4zGiLr4zgd02NuMwHMTZ1fiL8RgoiAkG' \
			b'U/zi/wSTOaJQhnfFQ5Fk+vFSwnUefPIprGMhkOhKwD4gBHcjtrMg2TfifPhggPsga+dEiEgA4XKOByi/l1JByGtBCOy0nBYw8yMvJBIAveR6kqAoRZ5gMc3wRCyCgSzQfyAMelmSxhi7kTyINpx+BARP7AF49wgrgQeBR0B2vgI/8kICWtETWtmtaM/elk12' \
			b'xyAUYpNAJWoFnXQHoJRKJ0Qn9j4ppSVKaXNKAYm0SxrqUCVaZpKWmaRlImkjkbTJEYmkLRJJG4mkHRssW7ikJSppC0wiozNhEXLWLo94fMVS6IE9EInUjF8oLi2WltRZ9gkS8pC+Wnot0gY5OxE35Az2PUcZ7SrK4MAkZZDTCspoU8qICdrGFy0W95Qz2n2U' \
			b'EaUTKEN0MUiikjD4+T66KLCE2T7kcVuKOCo51H7GGfczDJGCmfQzFo3+tuxRURDICIYZwURGMMkRGcEUGcFERjCbmMAQE5gCE8hoTJiAnLXLIxxfsRR60o8oeoTCkTsRBZCcBAFIP0gAQabMAXTrRKyQA9jXHAeYVRzAgUkOIKcVHGBSDohp2sYBJsN/sw//' \
			b'o2QC/huB/ybHf07b1u6CrURQieDciMAREbgJEbhFRODIo6IgkAgcE4GLROCSIxKBKxKBi0SwaXgfP0EvT4hARmNCBOSsXR7h+Iql0BMiKHqEwpE7MRG4jAikHySCIFMmArp10psbRl9zROBWEUEQtSACclpBBC4lgpimbUTgMiJw+4ggSiYQgRNE4HIi4LRt' \
			b'JQJXiaASwbkRQUdEMDEGAZcFRNCRR0VBIBF0TARdJIIuOSIRdEUi6CIRbNMzdEQEXYEIZDQmREDO2uURjq9YCj0hgqLHoeDERNBlRCD9IBEEmTIR0K0TsUIiCCHNEEG3igg4MEkE5LSCCLqUCGKathFBlxFBt48IomQCEXSCCLqcCDhtW4mgW6qXPhM6UJUR' \
			b'LogRBmKEYcIIg2AEuAFRDzO8MJB3RQG14R54YYi8MCRH5IWhyAtD5IVhEy8MxAtDgRdkNCa8QM7a5RFO3rL0gYQaih6xlGROTA1DRg3SD1JDECtTA906ETGkBvY1Rw3DKmrgwCQ1kNMKahhSahBR3EQNQ0YNwz5qiJIJ1DAIahhyauC0baWGvlJDpYZzpQZF' \
			b'OmU10SkrqVBW1F9AZC1QgyIfWH9YraxYrayiWpl8jcdIDaqoVlZRrUwe1lKDInWyKqiTk2jk1MDO2uURTt6y9AFJDWWPsDVI7kTUQKKK1JD4AWoYxUrUwLdORAyoIfiaoQa1SpccAhPUwE7LqUGlumSRpk3UoDI9stqnRxaSYWpQQo+scj1ySNtWahgqNVRq' \
			b'OFtqUEQNakINSlKDImpQM9SgyLuigJAa2HRVxTkC5Gs8IjWoIjWoSA1qEzWQ0aoq2Kwm0ZhQA0fa5RFO3rL0gYQaih6BGnInpgaVUYP0g9QQxMrUQLdORAypgX3NUYNaRQ0cmKQGclpBDSqlhpimbdSgMmrYZ5UqJBOoQRilqtwmNaRtKzW0u9OY6VCnOVSS' \
			b'uEuSIPMjNTE/UtL8CGFqh6dAEnANhdxEquCXFAWHVMGmSCqaIpGv8YhUUTRFUtEUSW0yRVJkiqQKpkhJNCZUQc7a5RFO3rJjqhO2KPoFtsidmC0yg6TED7JFkCyzBd06ETdkC/Y1xxarDJJCYJItyGkFW6QGSSJN29giM0hS+wyShGQCWwiDJJUbJIW0bWYL' \
			b'nI1LhrOE/x0if5sDPkC9Czg8B8ICUANQIhhaAj4AuBG4CKwQhFQCCFC5h+aoB05TPpEZg5VHK4/eIY9qGofTk3E4LcfhNI3DaTEOB9c+1/FEPKrJH5QDzaNxmkfjdByNI1/jMfKoLo7G6TgapzeNxmkajdOF0bgkGjmPsrN2eYSTt+yYasmjZb++uEyciEd1' \
			b'NiCX+AEeHSVLPMq3TsQNeDT4muFRvWpALgQmeJSdlvOoTgfkRJo28ajOBuT0vgE5IRnmUTl3XOcDcuH5Zh6dTgSsbFHZ4uzYwhJbTJbr0HK9DrgBtrCCLWh0Dk/MFuSIbMHLd1AgCs+BLWxyRLYoLumh45oe5GE1W1hiC1tgCxmNCVuQs3bRDxSsPPZ2THZC' \
			b'F7ZwIF3kTkwXNqML6QfpIoiW6YJunYgc0gX7mqMLu4ouQpYIuiCnFXRhU7qIadpGFzajC7uPLqJkAl1YQRc2pwtO22a62DMjsNJFpYtzoQuaGqInU0O0nBoCN0AXTtCFI7qI+hxNd0gXPE1E8zQRHaeJkK/xiHRRnCai4zQRvWmaiKZpIrowTSSJxoQuyDmL' \
			b'bR55O6Y6YYuiX2CL3InZIpsskvhBtgiSZbagWye9uWH0NccWqyaLhMAkW5DTCrZIJ4uING1ji2yyiN43WURIJrCFmCyi88kiIW2b2WLPtMHKFpUtzoUtaP7IdDFRLeePwA2wRSfYoiO26CJbdPSSouCQLXguiY5zScjXeES2KM4l0XEuid40l0TTXBJdmEuS' \
			b'RGPCFuTMFXXmQLagq4Qtin6HghOzRTajJPGDbBEky2xBt07EDdkihDTDFqtmlITAJFuQ0wq2SGeUiDRtY4tsRoneN6NESCawhZhRovMZJSFtm9liz9zCyhaVLc6FLXpii37CFr1ki57Yohds0RNb9JEtKBhki57Zome26CNb9MkR2aIvskUf2WLTqlT4CXp5' \
			b'whYyGhO2IGft8ggnb9nxKmGLot+hmzoxW2RLUiV+kC2CZJkt6NaJuCFbBLnPsEW/ii04MMkW5LSCLfqULWKatrFFn7FFv48tomQCW/SCLfqcLThtm9li8QTEyhaVLR4sWxhSc5uJmttINbchNbcRam5Dam4T1dyG/EE5MKzmNqzmNlHNTb7GY2QLU1Rzm6jm' \
			b'NpvU3IbU3Kag5k6ikbMFO2uXRzh5y46plmxR9uuLy8SJ2MJkau7ED7DFKFliC751Im7AFsHXDFuYVWruEJhgC3ZazhYmVXOLNG1iC5Opuc0+NbeQDLOFEWpuk6u5Q9o2s8V0TuLuYghDFzhDVd44a97QZGasJ2bG0KyUlsaaLI21sDTWZGmso6UxFHK2NNZs' \
			b'aazZ0lhHS2PyNR6xo1G0NNbR0lhvsjTWZGmsC5bGUA5jPCY9DXLWLo+xPHpWZJDfcSFcR/2N0hvY38iduL+RGRwnfrC/EQTM/Q26dSKG2N9gX3P9jVUGxyEw2d8gpxX9jdTgWKRpW38jMzjW+wyOhWRCf0MYHOvc4DikbTODTKcuVgapDHK+DGJIB24mOnAv' \
			b'BSPV4IbU4EaowQ2pwU1Ugxu6w84Hq8ENq8FNVIOTr/GInY+iGtxENbjZpAY3pAY3BTV4Eo1J54OctcsjLI+edBvsdySQjrogpTewC5I7cRckU4YnfrALEuTLXRC6ddKbG0Zfc12QVcrwEJjsgpDTii5IqgwXadrWBcmU4WafMlxIJnRBhDLc5MrwkLatBKLq' \
			b'/MZDD1j58HySK33cBX3sPkEhbul8R1KOq4lyXEnluCLluBLKcUXKcRWV41D+WTmuWDmuWDmuonKcfI1HnO9YVI6rqBzftqGTIuW4KijHk2hM5juSs3Z5hJO37JjqZL5j0e9QcOL5jqwcV7jgxy7Oe5R+cd5jkDCxCN86EUec9xhCnJn3uEpJHgKT8x7JacW8' \
			b'x1RJLtK0bd5jpiRX+5TkaswiJRTlihTlqgvzH3NleUjjZjbZsxtpZZPaCTkRFrltJwQ2JvUfglPKHnYn2ANufNBWLNAL1z7X8UTsYckD7rq6I/agQBSemT3I13jEnVh3JfYAV2YP8rCWPfAT9HLOHkk0JpuzkrN2eYSTt+yYaskeZb+wlWvuROxB0op9j8QP' \
			b'sMYoWWINvnUibsAawdcMa1BgS1kjBCZYg51WbAa7S1hDpGkTa1B8ImtQgmZYQ0iGGQPjzmxB0hRsEdK2mS3qnPDKFhfAFqQstxNluZXKckvKciuU5ZaU5TYqyy35Q7ZgZbllZbmNynLyNR6RLYrKchuV5XaTstySstwWlOVJNCZsQc7a5RFO3rJjqhO2KPoF' \
			b'tsidmC0yZXniB9kiSJbZgjNExA3Zgn3NscUqZXkITLIFOa1gi1RZLtK0jS0yZbndpywXkglsIZTlNleWh7RtZos6J7yyxQWwBSk47ETBYaV2w5J2wwrthiXtho3aDUt3yBas3bCs3bBRu0G+xiOyRVG7YaN2w27SbljSbtiCdiOJxoQtyFm7PMLJW3ZMdcIW' \
			b'Rb/AFrkTs0Wm10j8IFsEyTJb0K2T3tww+ppji1V6jRCYZAtyWsEWqV5DpGkbW2R6DbtPryEkE9hC6DVsrtcIadvMFg9xSngHhOELTuWM8+CM3X2u4Ei8oSa8oSRvKOINJXhDEW/IxX7pDmsW84Zi3lCRN8jXeESNRpE3VOQNtYk3FPFGy4uJIMZBxpMJP6s2' \
			b'MPAQiYlugz6tXR71JBl2TH+i2yj6Bd1G7sS6jYxBEj+o0wgyZp0G3TrpzQ2jrzmdxioGCYFJnQY5rdBppAwi0rRNp+FQp5fqNfaxiJBO0GkIFlE5i4T0bWaROlW88scF9DlIG24n2nArteGWtOFWaMMtacNt1IZD2WRtuGVtuGVtuI3acPI1HrHPUdSG26gN' \
			b't5u04Za04bagDU+iMelzkLN2eYSTt+yY6qTPUfQ7FJy4z9FlfQ7pB/scQbLc56BbJ+KGfY4Q0kyfY5UWPAQm+xzktKLPkWrBRZq29TkyLbjdpwUXkgl9jk70OXLtd0jbZraoU8UrW1wAWwzEFsOELQbJFgOxxSDYYiC2GCJbDPSSouCQLQZmiyGyxZAckS2G' \
			b'IlsMkS2GTWwxEFsMBbaQ0ZiwBTlrl0c4ecuOqU7YougX2CJ3YrYYMraQfpAtgmSZLejWibghW7CvObYYVrEFBybZgpxWsMWQsoWI4ia2GDK2GPaxRZRMYItBsMWQswWnbTNb1KnilS0OwhZsP3mvrIHDJPuYw2bsYQWDOLKfchP7KSftpxzZT8kNzh3ZT7lo' \
			b'P8UeoGw4tp9ybD/lov0U+RqPkUFc0X7KRfspt8l+ypH9lCvYTyXRyBmEnbXLI5y8ZcdUSwYp+/VFaOJEDOIy+6nEDzDIKFliEL51Im7AIMHXDIO4VfZTITDBIOy0nEFcaj8l0tSOoa3mEZeNUbl9VlRCPiwATYU5UImThlRYDuRL2wllzw63tjmrDQyPs3vh' \
			b'GVLH0TsaYIQOhunqU/P+qNNhJp0OIzsdN5Is5P6F3pfhjobhjobhjoaJHQ3yNR5xol/e0YCyZWI/w2zqZ0C1xol+hY4GFbz4P53sRzHULo90jL2ltCZrjBQ9wgQ/cQ+F5AY3H1IksYQnIDbkrzU8TZwumCf4OW59bsTtMF7OzvNb1dsIOSrn+ZFTkSsoMdk0' \
			b'v7Szgem2IY5buhtGdDcQfsy+qeIxA8aZfqK/ARkBpQIM37KeR0hnShQGmMHsIlOYR7RzvT8Dtvn6+oj2y4qMsWfj29NkjCOzRGCIwA5WsEJghMAED4QFjs4A+1Af6hp0FOyko2CXoD6UHsudA8udA8udAxs7BzY5YufAFjsHNnYO7KbOgaXOgZ2i/rRDQLHQ' \
			b'Lo9kjK2lEJOuQNEjdAVyJ+oKEMiHfgAnfCfb/pYa/paa/HZPe9+uau8HIYv2PjmtaO/btL0/Jm59I9+mjXyM0nwrP36I0RvjHZr4NsPskK59jXtu0wMy6z3TsisyV2Q+PjKTythNVMZOqoznkbkjj4qCQGRmNbGLamLyNR4RmYtqYhfVxG6TmtiRmtgV1MRT' \
			b'ZKYYaZdHMsbWUogJMhc9DgWnEjKzzBJkJhWwI+Wv26P5das0v+FbEpnJaQUyp5rfmLj1yJwpfT+BzPFDAZmF1tflWt+QrqXIvGeKc0XmiszHR2YaKXGTkRK3aKQEYIRHShyPlDgeKXFxpIR8jUdE5qJK1sWhErdpqMSRStYVRkqmyEwx0i6PZIytpRATZC56' \
			b'BGTOnUrIHGQkkZnGQByNfbg94x5u1bhHCEwiMzmtQOZ04CMmbj0yZwrWTyBz/FBAZjHi4XINa0jXUmTeM534NJG5jn9f/Pj3PiSHmug/hBUyQXJw+TSSQ/HiEVw8+/TQi+TOSE6+xmNEcvQ6QXJwZSQnD2uRvKMxbzjlSJ5EI0d1dtYuj3B8xVLoEtXLHn3h' \
			b'mDhJVJfD3YkvAHgSKWE8OzsRKQD74HsG7ymkpXgfAhN4z07L8R5TGPFeJGjTMDfFJ4I+JWgG84VkGPMx7oz5XT62HdK2APPlSLbeMzm4Yn/F/oeH/ZqwX0+wXy/Cfk0eFQWB2K8Z+3XE/vSI2K+L2K8j9utN2K8J+3UB+2U0JthPztrlEY6vWAo9wf6iR8D+' \
			b'3GkW+6UvxH4tsJ+cnYgUYj/7nsN+vQr7+QWJ/eS0Avt1iv0xQduwX2fYr/dhf5RMwH4tsF/n2M9pW4v9e6b6Vuyv2P/wsN8Q9psJ9ptF2M8eFQWB2G8Y+03EfpMcEftNEftNxH6zCfsNYb8pYL+MxgT7yVm7PMLxFUuhJ9hf9AjYnzvNYr/0hdgvbFzY2YlI' \
			b'Ifaz7znsN6uwnwOT2E9OK7DfpNgfE7QN+02G/fusW4RkAvYbgf0mx35O21rs3zNBt2J/xf6Hh/1k8dJNLF66RRYvUKrY4qVji5eOLV66aPFCvsYjYn/R4qWLFi/dJouXjixeuoLFSxKNCfaTs3Z5hOMrlkJPsL/oEbA/d5rFfukLsd8K7CdnJyKF2M++57B/' \
			b'lV1MCExiPzmtwP7ULkYkaBv2Z8YxlKA57I+SCdgvbGO63DYmpG0t9uN0W4/d8/vfnCkFDMMRdrvZygRqBRt0D4QR+ntmBUBaA0PvNHHqRk/Mbrw41CKGwKB4aEgxRSimCBUpAmqJOOLqPkWKUJEi1CaKCLbwqsARSTxyjrjB/TaJJbI4x5csJVUZLF7IFD0u' \
			b'GzTjH9b1yZ3myCLxhSv7CLJgZyfihsv6sO+ELIZ0aZ+9hAFLS02W9wmZE0mDnVYs75OSBsrOcFw3re9juJAtVhELOTF1KEEdKqeOkMJIHegCv54//G+/w98W3T2HwMnAE2SQzletnD/mmAPqIrIFUQVxgyQGZIWllDBnoIMEAEAvGvoA4UWTGmlKoxiC90Dv' \
			b'4ka4hNqlECvh1a2H1MVQGuCToTOBzQCXUBzmoXIBSIZqzoYvARRHFCxAYMC/W4Dfp21bAtIBoiWNXoCsomlKapQCSHQztUVJoWdFQzVBmxU4I0EGEGY9sqyAlBFJRhhJMSSgBwBCXwCEPa3J+8GEsV04lJAhNO5OHCHaAWaWtbdHCmjCF9Gi1OhSPFt9WIAa' \
			b'n2hhUavp4UKHaChBPpchBNJocp3YSUOJgkap7g4AKcpk45sRViaQAoWOZ3hDgVoKL8OK9oa5d3iRHU7EGai2h26EwLxQH48WJoT6yNxtoyTv921pmLgDN04+BTMLICb0304cZkY0Cf8MOS0iyx20XJAboNbA6A5V3jtvyRh9COixmUnVCD0K1xXc2KJp/qlg' \
			b'VnDvoLPjS8Cqzk73KfBxB8af0LbZCdAxF9j7afe0aeQAEqx9qxlsYEyzm4IO7rIIbv5dnz7l06dgSei4Go//7w8DSlR39WpQ0kcAphGIhghEkJGX3Y1S1nyizSNWXYYvWNLoKtTm0uIHORTFsUyMNkjSYiLgM3H3MLhR0ETyubR5SMbMjNjfCUoxQqG6YdiD' \
			b'UuoBIJVa2QObaxIVmkO2u58m0UxzyEj0MUWzxqOhT0QeyMRB70Efox8QAkF5WNvzcjPNn2LTBwrTwh6XL1inNsI7AyQ+sZBdkJ9QcEDs99/0yfVs99X88dca8gCulw7vyKaQngGY0OS5i6bOife9piAD6UPd6Q2tS2SON2zsjtnk8U4gesRUkNjyIZ/Y7wpN' \
			b'n2KLx3IjJ2/a6Ob1kXFozvLgoFqnh9jnUocY2ImAgtXhoeEJmnygaYdFM4770j4dvcFyqy6TPZD2qfln98jzEI7UmKMDxafAwZfp27dSHgpQrGmVrASKc2l5zLc6NJpqHaC18cBgglO9vH2xXEvt47cJH+y9QgTozQ/SmdlqSp4bDN4TXICF0QOADFgN/5Rx' \
			b'Az6DwwKH6atI9MCUbYQQKK73iiPQHl3fWVkBJm4bmLj7BRMBJBC3o7U57hFIKojc1iguBRDIuKM3Qe4dP+4UO7pt2NEdDztcxY6KHRuwAyJaseOQ2NFvw47+eNjRVeyo2LEFO9qKHYfFjuHkB0jPflD0dMHhdHHhkCCgME0nO/x54Erf/NPXhEcAfKAg8VKv' \
			b'9f8E6/8BNKcPCgOw6hwPAk5dBTKDAbfUku5gA8QWYaCtMFBh4H5hAMvoiTUFLhIHnG8OGFwHxudGhYEKAweAAazyD7ZHcJEwYPUjD94IA8c3r6wwcB4wQOWtwsCDhIHTN56sMDADA3Obgd83JGANPomhQnzzZBCBYnNngIDBrwQEhZDZTPbIjtAQ9sWe2xAb' \
			b'QWOjRWUFjeODxnGBQp8MUOiTAgp9t0ChD9ZyWAQPG20kKzxcJDxgSTtDleMt4YEq4APrWMBy02hxPKD6ETeatBvNHiscXBAcYFE6awuEZXCAcjibcQYD2keoUD22EggONloyVji4ADjA4nUZFkn78QAFcX4Dj9q3D2DIuPfAoBXCQTVOrHCQwQFWisuyT7xI' \
			b'NYSG5sEOYcBVG8XLhIHhlCwUTwIFILDLwYC2f4RM4KsEXGAXwVVLxYsBA6jYx7dTPFkwuLQmQYsDiGia4Kqh4uWgwElYK1cUOEEUOH07RWi9hPVo7xURwoJhx1yDtk5s3LBaE1Re//ZRkAKq8THxwjvNosYtJjm74xsyblouVguscKffgtiy/+viVoTJtus4' \
			b'a7ygbYLT/5VGTPBGcZfVB9DQ2LZD6orWBkpn3ICjW9Dq6NwjD+LY6Di+gWMFkwoma8Ckm/yvBZOugskeMOkkmKhVYHJ8c8gKJgcEkzMHkn7yvxZI+goke4CkXzEOIkCka173CB2IGwwahBgKsUIhSnSIDxIcEBm4jmN9NFwHB657pXqnqY5B/cjrRFIHDGwf' \
			b'Hsp3KNpjqR5LNKSVCnJPxRdLLi5NViixsbTGMtZR/uMEAkd5XsxuyGkTcmSaC6nQ2x57jv2tREtQGkBUE2ACECbC7lcIfAaIJoLHWnc3kocEYG0fc0BxqDinSWbHWBUXZcl85ShmzXC7rOlmcmd3Djm0i5g8yaUAp/eWUx4JX0PyzQ6TDdsAW40PWv/ANztA' \
			b'HNSOcOgMO40poEwvPXTQ/tLCjlPKeR/+fHXjXwWL2Ab2qYV9E2HPQtit0CWbL49busO2NLCHMW5lbuF7uAe8b3MNtE/quPsgNE9AhGJj5bDfOuzuh7GHPdAxBTfqltHw95/6w+9o+I6d+RLtg2YWflJDw04nf3GbM5s9wT+MgSnEoMWdIi0uYd7BgqILI4S7' \
			b'D4xD1HDdi0hqjqhP3/gHFcXw4qHxf+4Pn0OjDxqr0ODT5A69PYOpsbdMDVT91Qnyze6Ff9AynnmG0Xero68/lYJsy6LZFKkhS5UH0r1/0OKfulJbvOc2t06f+UYhXmFau2lafRzmkutfhU6OTTo2e2Tg8RsapjuDZrXQzIL2FjR5oXkHrbtRSjBLEczwwRbZ' \
			b'tFFqHvxwkA6ayChBkKRhSXb7pelb+tRDoWUIkT6idH2BVbhBLO/9Ci2qJv4B4PfZH2mdyv+53/2+5Vufcuuzq/mvyOdZqJjb/QmVbE8Qh/zD9A2nWJqh4VMq0TBadC+lGppxJ3DAQEHuhOvcH+rAIuCbGqdTxmG46QgHCaIdBQGE7e6sSqgHWitsQ8eAI3Hj' \
			b'7YGP7u6CXndQoVAHqR3QLztMBYGdXm99wCjn6tdIHjqrJDBYeXfsgVUFxlIfXG2BEQBx+DQMXZM5HvaAwYE7/cCyg4pJoX+2p2h8ug1xkMqDA+nJAUPCU9clB2gI1r9GwrG1Di2rQ31zkQeVkkKv+vhVCJR+xzxINF2tQIsqEAw9X+JBpaTQeb9VBYLsP0wl' \
			b'0s0BD9BNr3+NRDTUirSsIg3NRR6kVSiMENy6IkH2H6QygenJQQ+w8Vj/GkkqH0Ko9alcn0AbeokHlZLCmMJB6lPbH6pO6ebgB5hIrX+NBFYHHRZWK9Nc5EGlZN2Yg9ukuthQu0LupTXMNssPsBlb4XtY7BvMCcU9ibGOTiysbF1zkQeVknWjE9sqW6EE3L7i' \
			b'9c3dHdL0d1MIJNs6vLGsBoIp3SUeVErWDW+cTg2EOQEnepBg66DIwupnmos8yARyV0vJDpK8K5cW28cSA6oyKjX+HyHANmd8KAPmxWrqrEpXVJra1YZYh7a8uh2ul+Chb5YfYEG+6oXpEeZZrX4P50fFuVGYH+uGaB5EfsCcu4d0UEYUTM0ffEao5kEdlBHr' \
			b'RlfuIiN0uzIz7NIM0c39H8Cit/REGVOYPLCk8XECeeOW5o9pVh0wK2jtO7c59n+PcmndeMmDzCXXPNiD8mjj3I6HlEd982APyqN1ox4PMY9gJYSHelAeneSskqPNkYJlLdYftHpF/N8WSiHQafDiNvGzKKD0oLmZ6+xFzj7/XXPWB+X5+gGMs87zrjnrg/J8' \
			b'/SDJWed535z1QXm+fjzmrPN8aM76oDw3zWvdwuSzHZmIePIPDoz+DhxApugIa1VxU8B3qWSp8JIHH6A0gTl2oDaB1VIUh9uXffucSv/J9zDxDbmJb/h8zf4VmzzbnVzlA8sGuXsCk4WUypQsS6Ec4bIq8DauMRbXFqM1vcJ6Xp1Yx8uXFkuC8l5fZ2ucQSSU' \
			b'xejAJ8dPQVEdqCjyEJx3fo2ruu1wMhMsJ6apVvp4vUZNDA5nW9ayKAOrCfr3fW1TPfu0cfESEjrsgasc5Kbi9jtsg+lDQRcqAbATHrv03s931/8PaGC4mA=='

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
		('STR',          fr"((?<!{_LTRU}|[')}}]){_STRS}|{_STRD})|\\text\s*{{\s*({_STRS}|{_STRD})\s*}}"),

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

# 	a = p.parse ("Function('f', real = True)(x, y)")
# 	print (a)

# 	# a = sym.ast2spt (a)
# 	# print (a)
