# Builds expression tree from text, nodes are nested AST tuples.

import ast as py_ast
from collections import OrderedDict
import os
import re
import sys

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

def _FUNC_name (FUNC):
	return AST.Func.TEX2PY_TRIGHINV.get (FUNC.grp [1], FUNC.grp [1]) if FUNC.grp [1] else \
			FUNC.grp [0] or FUNC.grp [2] or FUNC.grp [3].replace ('\\', '') or FUNC.text

def _ast_from_tok_digit_or_var (tok, i = 0, noerr = False):
	return AST ('#', tok.grp [i]) if tok.grp [i] else \
			AST ('@', AST.Var.ANY2PY.get (tok.grp [i + 2].replace (' ', ''), tok.grp [i + 1]) if tok.grp [i + 2] else tok.grp [i + 1])

def _ast_func_tuple_args (ast):
	ast = ast.strip (1)

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
			return AST ('=', '=', lhs.lhs, ('lamb', rhs.stop, (lhs.rhs.mul [1], rhs.start)))

	elif lhs.is_comma:
		for i in range (lhs.comma.len - 1, -1, -1):
			if lhs.comma [i].is_mul:
				if lhs.comma [i].mul.len == 2 and lhs.comma [i].mul [0].is_var_lambda and lhs.comma [i].mul [1].is_var:
					ast = AST ('lamb', rhs.stop, (lhs.comma [i].mul [1], *lhs.comma [i + 1:], rhs.start))

					return AST (',', lhs.comma [:i] + (ast,)) if i else ast

			elif lhs.comma [i].is_ass:
				if lhs.comma [i].rhs.is_mul and lhs.comma [i].rhs.mul.len == 2 and lhs.comma [i].rhs.mul [0].is_var_lambda and lhs.comma [i].rhs.mul [1].is_var:
					ast = AST ('=', '=', lhs.comma [i].lhs, ('lamb', rhs.stop, (lhs.comma [i].rhs.mul [1], *lhs.comma [i + 1:], rhs.start)))

					return AST (',', lhs.comma [:i] + (ast,)) if i else ast

			if not lhs.comma [i].is_var:
				break

	return AST.flatcat (',', lhs, rhs)

def _expr_colon (lhs, rhs):
	if lhs.is_ass:
		l, wrap_ass = lhs.rhs, lambda rhs, lhs = lhs.lhs: AST ('=', '=', lhs, rhs)
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

def _expr_mul_exp (lhs, rhs): # isolate explicit multiplication so it doesn't trigger imp mul grammar rewriting
	if lhs.is_curly:
		lhs = lhs.curly

	return AST ('{', AST.flatcat ('*', lhs, rhs))

def _expr_neg (expr):
	if expr.is_mul:
		return AST ('*', (expr.mul [0].neg (stack = True),) + expr.mul [1:])
	else:
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
			last, neg = last.strip_minus (retneg = True)
			wrapl     = lambda ast, last = last, wrapl = wrapl, neg = neg: wrapl (neg (ast))

		else:
			break

	if last.is_attr: # {x.y} *imp* () -> x.y(), x.{y.z} -> {x.y}.z
		if last.args is None:
			if arg.is_paren:
				ast = wrap (AST ('.', last.obj, last.attr, _ast_func_tuple_args (arg)))
			elif rhs.is_attr:
				ast = AST ('.', _expr_mul_imp (last, rhs.obj), rhs.attr)

	elif last.is_pow: # {x^y.z} *imp* () -> x^{y.z()}
		if last.exp.is_attr and last.exp.args is None:
			if arg.is_paren:
				ast = AST ('^', last.base, wrap (AST ('.', last.exp.obj, last.exp.attr, _ast_func_tuple_args (arg))))
			elif rhs.is_attr:
				ast = AST ('^', last.base, ('.', _expr_mul_imp (last.exp, rhs.obj), rhs.attr))

	elif last.is_var: # user_func *imp* () -> user_func (), var (tuple) -> func ()
		if last.var in user_funcs or arg.strip_paren ().is_comma:
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

		elif ast.numer.is_pow and ast.numer.base.is_diff_or_part_solo and ast.numer.exp.no_curlys.is_pos_int_num:
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
			elif n.is_pow and ast_dv_check (n.base) and n.exp.no_curlys.is_pos_int_num:
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
		end  = len (ast.mul)

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
			ast2, neg = ast.intg.strip_minus (retneg = True)
			ast2, dv  = _ast_strip_tail_differential (ast2)

			if dv:
				if ast2:
					return (AST ('intg', neg (ast2), dv, *ast [3:]), ast.dv)
				elif neg.has_neg:
					return (AST ('intg', neg (AST.One), dv, *ast [3:]), ast.dv)
				else:
					return (AST ('intg', None, dv, *ast [3:]), ast.dv)

	elif ast.is_diff:
		ast2, neg = ast.diff.strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			if ast2:
				return (AST ('diff', neg (ast2), ast.dvs), dv)
			elif len (ast.dvs) == 1:
				return (neg (AST ('/', ('@', ast.diff_type or 'd'), ast.dvs [0])), dv)
			else:
				return (neg (AST ('/', ('@', ast.diff_type or 'd'), ('*', ast.dvs))), dv)

	elif ast.is_div:
		ast2, neg = ast.denom.strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('/', ast.numer, neg (ast2)), dv

		ast2, neg = ast.numer.strip_minus (retneg = True)

		if dv:
			return AST ('/', neg (ast2) if ast2 else neg (AST.One), ast.denom), dv

	elif ast.is_mul:
		ast2, neg = ast.mul [-1].strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			if ast2:
				return (AST ('*', ast.mul [:-1] + (neg (ast2),)), dv)
			elif len (ast.mul) > 2:
				return (neg (AST ('*', ast.mul [:-1])), dv)
			else:
				return (neg (ast.mul [0]), dv)

	elif ast.is_add:
		ast2, neg = ast.add [-1].strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('+', ast.add [:-1] + (neg (ast2),)), dv

	return ast, None

def _expr_intg (ast, from_to = ()): # find differential for integration if present in ast and return integral ast
	ast, neg = ast.strip_minus (retneg = True)
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

	return wrap (AST (*(args [:iparm] + ((_ast_func_tuple_args (ast) if args [0] == 'func' else ast.strip (strip)),) + args [iparm + 1:])))

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
		return AST ('vec', tuple (c [0] for c in mat_rows))

def _expr_vec (ast):
	e = ast.comma if ast.is_comma else (ast,)

	if all (c.is_brack for c in e):
		if len (e) == 1 or len (set (len (c.brack) for c in e)) == 1:
			return AST ('mat', tuple (c.brack for c in e))
		elif e [-1].brack.len < e [0].brack.len:
			return AST ('mat', tuple (c.brack for c in e [:-1]) + (e [-1].brack + (AST.VarNull,) * (e [0].brack.len - e [-1].brack.len),))

	return AST ('vec', e)

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
			b'eJztfW2P3LaS7p9Z4HgANSC+SvI3x/E5G6ydZGPn4C6MIHAcZxHcvK3tnN3Fwf3vt6qeIiWxJbV6pnvcMyOMpiWRFFksVj0qkkXq0eu//Mu73378S/WXp189/+pLOj9/9tdXdPr6yTfPvnxOF3/95slTPRk9Wzp/9sWXX71IZ5MurGbw+Vecx2fP/vb90ycv' \
			b'n73U6xdPUuhn/eXf+8uvcfny+ZOX//oZlfNvXH6+ePHFl9++TNFPv/3m+X9waL54+eob/v32M/p99uLrV//x8hln9uW3TOXfn3DkF1+++hsT+MULSSm///4Np3ouNf+KY//67Zdc38/kiadfvXjxJHGDA7754m//+ioV+00ijy+e/Tv9PHnxNf1+/tlzIZJD' \
			b'v/xcq81Xn/WXf+8vtdrPnr98piGJaZzRKxBCBHCiF0++fvnqKy7pldT32f95+jxFcyt8/sXfv/ics3mKJtDHv34O1j17lbhIWYPYp0+U5FTEVynJ01QZ5cW3fPvFX+lHKCBWm1FzKP+pyKf/Rpcf/vzhwz/evP/wj8H1B7p+++b9u4/f//7++x9/+OXDxzfv' \
			b'B9F0Sac3kuzd//zx/vsPf/7x7n26+e3df37/05+/ve0jf6DLX998/P7t77/o1fvf/7u/Qmkf3n348DZf/ZGvUjZvfugvP37Mpf305u3HdP2H5IrgEQG/pstffs6XP//28T/T9a9//vL9z7/+kW7/8aavTP/sjz//I11+fPd+EPzTT+n67Z/vf/nfAR/S5Q/v' \
			b'37z9v+8+Douji1zcu0zqmx9/zIne5PT/8+FdX0nhSq7asHRunnT9528///5bLv7n337P9L7t6/kTkZV59/O7t+/yDbX9bz0hf3z4+Hu6e/dfepXz+/2XvqS3v//665vRzYe/fFe9frTzXeXbqwoXHV+4ln/ozlzpLd1Jipp/Kjrt/NUoAAm79BzF5yC+lFS7' \
			b'ICFN9chWzlU7U7lIF1cpVMNywK7hC9PiJ1CARaYpiI4yKIyC+JLzivgJWp9I9UHepnpE2RouGMVySDu86/TMQXRlDVNvmkR9e5VCNSwH7Kw8YAJF0R0x0TdXGrIzKJ65Z2wVuXx7pUF8yVQKz/jJq8Ftuh6EG5yoRbhg+Xc+RVu+4Hw1HIUQcRqIRE4q1Wml' \
			b'YpdDNazpk9XjgJ2VRrVUoI1yFfETOEQz6oOkTXIoX9IVcWhHrKSi4hXud5KVC/gJYA1dUdPxFYkZ5S6NAoZQQBjcaCIO4OeY7E7azFcsyz5cDcJ3Pu4H9beu3kshQYNblna/HxT3gwa3dv929MDOSXtSWY+YU1IAnQ3kKwX3tzuHyrJ8NpW1FbeUbauIarPy' \
			b'KBunU7D2k4qtS0jNOE64cyJQ3NBNFeokfUShIItpVGsM19NU3g6UhyNzeB/iEOL6EI8Q34cEhIQUsjMiULbGTwiZxhwUh0F8yVcdfoiPV1f9JV+RPonM6iNEppV28QERWrZn2QRAEMckBWAu4QSSMchJSLrdCb0tFD8SbaHiVoYeDIM1gO6F4x4/JBJXek/q' \
			b'IUzw+ImsHIjMQXYYxJdMOEVyraCTdBfRYKz7dYboJAS+TaovkAk8JxaRcKQUECHfs5lFG6yhwEd+wDO+7XLRhA9gIDdak69avbImXdh0AWCziqFcJRWNFBSGQXzJDxKp4BQ1uokDzGasQykm4id0WcNSUKyHQXzJtDv8DN6LCY+9xY+8EiHL3solX5kUeaW3' \
			b'dJciEEQy0NTCWdIq5b3wUDgUWKqDSRmw4gWpQTApQpJqkD5FbSR8kHfz1RUZAa85b8ZGCiKY5TanEOKMvKhJuthEIOOganzVhKqzVeeqjoLpOlYdqbyl1mOAJ5VjDnf8NiGq6T1IgmFY8/l9TYGmDvQf6b+mf0P/JDixsowN9C6jF4mhtm1i1TRV01ZNV7V1' \
			b'1VI6iqQ4epiepWwN5dvS4arWkyiQ0lG7Vm1TtS23A0CG24QeMkwCPc8ZcA6UhRdFI050nBWVQM9GRrhIOEf1rKvGVI2tGnqsJtrqlqGDAJIMDBILEgPSsCivbpI8kjTS0q6tuo7Rj1jNNaYKUx05/++qRzW/p18/IjZzAxGr5UTEEP8fEcMRWyPY4OQl9jW/' \
			b'HeRe3vVby5y4ZTrw3qNJ+O0mTG+83DOF3ERNQLIObdFIiz2yML882o0zlWc7tNSmUudtOK9NIk3zqEOTdI02QpCWGjFNGQXmTDBEmZDrPqz1VJVRUyIlqHQEd4tlavUtBNd2kEHT6LlVPhiJOB8d1iod9ZnLMSjHGK1pnbTOpJrWYdO7s+sdt8DG5vPDmxQs' \
			b'bya7sfsW2F2rEcYVxpvf6TnZYVZSEMkV1aKiLDe235jttlGuW7zFjTJdra+QWO83HbgFZG+kNQz3Q7gTwh0PNi+YVSz8xICNyTdncrsx+fxM7jYmn53Jbb0x+dwvyDZ1e9C9bWGctE5fjK0gtpLve/LOS1ffksMGvJV+L5sKW//jNgxiq6IGU0zts7bVTsnW' \
			b'BrfQBt4pt9EGHm3gI8YkhUQZ61GjOVnNRrsyHmNBrTx2D7HgUWe0i4ahoFbrHVHvCEOr5mr6kSxkGXhAwPko6kh3A2Y14F2TBrhVhmodP6xV0QPeOwHBQVlKWUmVTNV2VVffUZZQ7TCWGOv7Va2Ito3Ah+hGenB/agm4iwJvqMqwcne2WjqRUaqazCxBXkOa' \
			b'aQoKgI2+Edo8zWgxv2i3GcPT93uIoxbztBt7T2/0ECutzsjSeePj9cdA/Caf5+BrJwK69X3OLb5RUJZJ3bh9dm77emPzbcydb2y+DdcgBxOiEwOYXYPotDH1hrIb5L13S72gCQ87dnrShrViG45bpW+NYTs89GGf1+ISxszaGDTLoHZj0CKDOvDnbK59NbSa' \
			b'W4AL2pg/ZH5tNqYUAsM5W5npkJPXEQODvsJDZ89r8VnbGCFr5EQw1IjAhAcsiTS9gSHk5EEs8vMQWfWaXe4ebt3DQ637IyAFe/4BQnUNktFFSOLQA91IKwxsmn6G7yb7s0kOYiSwT5Bk1AomPyBOvmannIdVZfY+UsMNU1azi6O+05VUlXjvyDvb6Cg/3uRe' \
			b'kPoecyqgulH7YqNZvQgNmvF9lonbq7wg4FNYWz57Dlh4Dlh4Dlhp2FqlIOiAraTu+kEuDLxgqAvDL+WA1zYac/QQV2iV6cL8uz2RL+pw5ysBEPwE6on1WPT+ufNcfNTpOunQ3XWpZp8iIL65+1XRUddo735VvFYl3PmqdLAaAl7KJrv88N4S/IK9ku02+EQv' \
			b'XQfzzF1haN3B5N+898+9vM2hHdAcBqfOoR06tFXHzcFvdG0ei0abWMlNIW565bNpJ2N45NalkVU3uaiRk07FyBgb6EAVlDqjVZozVq2fj+bxGIfxGDEg+XdbRnmauTnhqBjgGzdvPksPGS8X2xg/HRwmgh+pIjSN6o06DRqdutwg9mSNZTexP8nLqlFroYM4' \
			b'10mqHaTa6eiNw+iN09Ebd59XmLzmgSl3jwemZETKbVNFMspmdZDLYZDLYZCLuZPGKZRXXQoJMZnb5qrcuIuHZmCUdTpZiTdAi9sANYsoJ0LNYkiWuldL3afBeViTHtakhzXp1Yz0m5/0TXb+COCysD4kM1ct6n62Q21Xjza5x5BHlfLzFn4D6aPaeuiHT4PA' \
			b'eKjL68b8Xe9gU4mqhSFZctDCAC0M0EI+kb7hLugzCCYuBXApbBbKSdxnG+ZkMX/CQrdZgKeYVFBJj7yHMjZUi/y+o/z5pda/96joCPGOEG9OVuUmig9rGpQZ48C3RkFAzk4R1PXzZ82D4sxrlpAGEtLIawIzw3mpcWJXiy6yum+xhxspEG+WyjulJrFj/rWQ' \
			b'uhZ5tspl7WEHZXfUc1oV6dTZp5H93B8W/+0Dq7LIg0/yYFUO7NVQjBjQIUBy5gRObJu6ek0EyhZvPC7J27zxQ4LrQevIVQBdUd8iOpWNue6E58zpRl9IYNGQFczbVrhqpxuBe1+dVjAK+Mt+HPL2aTFYL4gcoSLsZMH7BDJz+GXCO0XwNhG8AwTvbMubhXIL' \
			b'8Gp+XsrP6/h57TsvfOfF4rxSnJdT81pqXn/MOyjw9gnMKmYTiwXviMvb4PL+Vby9Eu/+wy3F41486MUbhbBVzF4gvAMu78/Ke7Pyxqy8KysvaCZ5sey0STy1PGPBIiEMZaGgMN4+nVGAvUPYq9Nz2/N/oOaRr0nI1yj4Cw6857mreJ9/3kWcd/gm4nZU6I4K' \
			b'2/He7/gGQYVt2+VrAfJRAN4WvObNu2sO513jeafxVnZM5xsKbflJDuStth223zeyibhsfC77p3Niz1u484O8Q3fLO7dTCQ0nIf3Z8c7tVGHZeps3i+ed0bFZPoXxtxP4oQa0t/zVg1bJC3JBKcl23vGW4/yFCN7hnFgou3zzXvfyPQRsyr5rOI6ZwXvFW9mt' \
			b'f2dkQ3wuV6pd82O1wXcTeA9ylqWdwZcb9BsYXC3edJ3ODX9/g3OmZ1umk2mUB0yFncqZTi6hFqZyEq4qf8WBYnmzed5/XXazZyYxUcxIoYLu+WmKa6QdJBsKIQXYkcTtGvsdqyUr40gRzbwuCkYATEZK6ZJemrFqxhtpZ1MYfwvK2qxU2E+lrOZIhW2PVNrA' \
			b'LAulnq7QVEnE6jCpr73Ghn2dDSfUWinKWTnjb1F3V2vvJ9Xcxh6rvJzrUQpc/dM/ZpAOjxmmG0sn8//E9iOtJuMjaXPuLjUj+6BQaHUYE28xXTOZvcvq45W7Gej3wKCZ0HW/p+tGenReLShYVhjmIJlCXzOvIqpLWyWiezlCCN+jBHdJh/PxueM1YRELgpgx' \
			b'ivC+IIIeUdEioQQ9w9v/8NY/kyjB/G8OowVvsMQ7zvEuYIdQg5doZOSIM+hBrcxtLAhigCJsrY2QhNJSE/aIwkamfCZJTlQ8Szc1rJxwZy1OpkqJWchqAAmfmeH16EhwklMWmMJhC6Ai7+0hqEjAEFhgqPb/JdAU9AwPqZkbPd0Cg8pMp/4TTuEaWCWAIJsB' \
			b'CV4NcxV3MqlNrXSms9Oz1/gezqQhHBAMRhaQysbcAPsopTFLWDWqBmvTYdQyidpGqdwHLy04aCM1MeU/gLFcaoaz4B7zm4N09jHEqSVo8yLkdI6MbS5jW+oHwVJRM+WSIW2IZ2vBLBwBaBuYzYAZC7mop4ghzKJsEsEcSmmE4YphBhhmRkePYZppAWHmAISV' \
			b'CFYC2KCkErzM7AHkSje2XkzbylgA0KroFAlcGYUrZQjOAlSKUwpTilJjkDLzIKUZToAUYpZBKj+/DqGUg0rRBD4p39AEKhcFOiGqxKZ9SPKFuXWf8Wgzrk6AR9wXhQL6aTDSBCxJXsHIA4z86MhglHIswMgvg5EvwMgXYDQsqQQjP3sIGOUblpSFtMlu8hmJ' \
			b'UGPNaVAQoMgDijygyAOKPKBo3P0zfh6KNMMJKELMIhT1BK2DIuWfUjQBRVpXNEATNe8hFClVR5hJYcOkDZOOwSSuHFQxTmOSJsBIAjApApPi6MiYlHIsMCkuY1IsMKkYOhqVVGJSnD0Ek/INS8pC2oRJscekqJgUgUl97YwByTUI0pPDCQ8MMSnOY5JmOIFJ' \
			b'iFnEpP75dZik/FOKJjBJuaZFp7yHmKRRR2BS3DBpw6RjMIkJhSo205ikCSBJwKQGmDQ+MialHAtMapYxqRjL5vsRJg1LKjFpj5Y+KWNSvmFJWUjb9oxImNQoJjXApJxUMKkBJjXApAaY1ACTmjEmNfOYpBlOYBJiFjGpJ2gdJin/lKIJTFKuoQGaqHkPMUmp' \
			b'OgKTmvmh8juATHYDp08GTuLZJjrZCTjxCQ4YI4jSZAYxAlEdIKobHRmiUr4FRHXLENUVENUVEDUsqYSobukQlMo3LDILaRNKdT1KdYpSHVAqJxWU6oBSHVCqA0p1QKlujFLdPEpphhMohZhFlOoJWodSykKlaAKllGtogyZq3kOUUqqOQKl2Q6kNpa6DUvwg' \
			b'hr4txr35xK65ZoRSKZlBjDiNYfQ7R2oSRamc7xil7PLoty1Gv20x+j0qqUCpgpCSLt60NN/oDPdcWkUp249+o9LKnUFZglIWw98Ww98Ww98Ww992PPxt54e/U4b7KKUxSyg1IGgVSiUWKkX7KJW4hjZoouY9QKlE1REo1W0otaHUtVCKHZygkxYoZYFSdoxS' \
			b'mswgRlAK7kqIyUdGqZRvgVJ2GaVsgVK2QKlhSSVK2aVDUCrfqE7MpU0o1Ts/odLKnUFZQCkLlLJAKQuUskApO0YpO49SmuEESiFmEaV6gtahlLJQKZpAKeUa2qCJmvcQpZSqI1DK1Jt31IZXN8Mrz9Ih2okJPIuxKTnhDgIkqKWJDeIFtTCZh5h8ZNRKuReo' \
			b'tTyZZ4vJPFtM5o1KKlHLLx2CWsN75t1C8gRc/ZSe1Sk9iym9PqkAF6b0LKb0LKb0LKb07HhKz85P6aUMJ4ALMYvA1RO0DriUi0rRBHBpXdEMTdS8h8ClVB0DXGYDrg24bgRcLAtw63Rw6+RTCDjhziKOikiJDeIZuBzcOhGTjwRcOfcxcLllr06hZABcfD8E' \
			b'rlFJBXAVhJR0keCO7u1ycgUuuQRwod7KpkFxAlxCuJKlJ4cTHhgAl5v33UwZ7gOXxiwB14CgVcCVuKgU7QNXYhyaoYma9wC4ElXHANfmj74B1w2By7MUiHbC4nKwuBwsLgeLy8HiSokN4gW4YHEhJh8ZuFLuBXAtW1yusLhcYXGNSiqBa0wIN+IoeXDje1uX' \
			b'j4zr0WTeJORSk8vB5OqTCnLB5HIwuRxMLgeTy41NLjdvcqUMJ5ALMYvI1RO0DrmUjUrRBHJpXdEOTdS8h8ilVB2DXG5Drg25boZcgUVAtBML8vgUEBhwZxHHyKWJjZ4ZuQKQK4yOjFwp9wK5llfnuWIdjSuW0YxKKpErLB0CXMN7Bq6F5Am4+lUzTt3QHVb5' \
			b'9UkFuLBkxmHFjMOCGYf1Mm68XEZuZ4BLM5wALsQsAldP0DrgUi4qRRPApYxDMzRR8x4Cl1J1DHCVPukbcG3AdSRwRW5/0U54hPIpBJxwZxHHwKWJDeIFuOAdiph8ZOBKuRfAtewd6grvUFd4h45KKoErLh0CXMN7Bq6F5Am4eh9Rpz6iDj6ifVIBLviIOviI' \
			b'OviIOviIurGPqJv3EU0ZTgAXYhaBq39+HXApF5WiCeBSxmnRKe8hcGnUMcBVOq5vwLUB15HA1XDji3bCbdRhBwQ54c4ijoFLExvEC3DBhdSNjwxcKfcCuJZdSF3hQuoKF9JRSSVw7dEySs3ANbxn4FpI3vasScCljqQOjqR9UgEuOJI6OJI6OJI6OJK6sSOp' \
			b'm3ckTRlOABdiFoGrJ2gdcCkXlaIJ4FLGoRmaqHkPgUupOga4Su/2Dbg24DoOuLi14azl4azl4azl4azFJ4s4Kym9umx5ddnycNnyZnQk4Mq5j4HLL7ts+cJlyxcuW6OSCuAqCCnpIsEd3dt6MbkCl++9trx6bXl4bfkBU3DuapClJ4cTHhgAl5/32koZ7gOX' \
			b'xiwB14CgVcCVuKgU7QNXYhyaoYma9wC4ElXHAFezv6PCHcUud234OmabhQ3CFmwvx/IgWy00csXml4P55WB+OZhfDuaXpjeIF/PLwfxyoyObX6mAwvxyy+aXK8wvV7jHDwvcs7/c0tGoCTaklU2w+SdkAwa1wlxvhTm1whyssJxarDAHK8zBCnOwwhysMDe2' \
			b'wty8FaYZTlhhiFm0wnqC1llhSqBSNGGFIUFAazRR8x5aYUrVMWBWesofXGOYvo/46QHsnN6np8Qrvm9OiFu3gFlUT8v7V/v6kAlWVx4OEr6eXHKYEpiAM5tdte51ZTU2H9n0SrkWpteyY8TeHnq+8IxAk/b/e/ZXPXuI8ZVv7HxC3/tF8BuG0Ur2CMzbxXi4' \
			b'RmQaZF2P4pVRwDKKWEYhyxSY5afdIyDyaogpCycMMcQc2o7Pr3aSkGaJKH0GuxIT0SaNnCxv5cdmbGmSKX0JxUgKHmPNAZ8bQa1uM8E2E+xUvchYeYzbE7keQ/ceQ/ceQ/ceQ/ceQ/cpvUG8IBqG7hGTj4xmqYACzZaH7n0xdO+LoftRSSWQxaWDNZ/hbJgB' \
			b'I9r8E2KBtYD5fgDf6wC+xwB+n1q6kxjA9xjA9xjA9xjA9+MBfD8/gJ8ynEAxxCx2J/vn1+GY8lIpmkAxJAhadMp7iF0adYQFZjf3+ikEIxbo1+geJpK5GTQLa9ztm8qqTzkG9C0G9C0G9C0G9C0G9FNig3hxt8eAfnFkd/uUe+FuvzygbwvbzBYD+qOSSnf7' \
			b'PVpGqdndfnjPPFxI3vasSe72OqBveMPsrkamg2Lhdo+BfYuBfYuBfYuBfTse2LfzA/spwwm3e8Qsut33BK1zu1duKkVT64W6zEQ0ibjeOy1j6H6v1B0DbJv7/Waa3cw04/bEAH/AAH/AAH/AAH/AAH/AAH9KbBDPQBYwwB/M6MibtKfcx0AWlgf4QzHAH4oB' \
			b'/lFJ5b7tZulgIBvd23oxuQJZ6Af4gw7wBwzwhwFTcO5qkKUnhxMeGABYmB/gTxnuA5jGLAHYgKBVAJa4qBTtA1hiHJqhiZr3ALgSVccA1+W438995WaDrxPDl2zgcJalj/I5ITE40LW06FpadC0tupYWXcuU2CBev0UktlgcHdkWS7kXtthy19IWXUv5dgNz' \
			b'nR9nbqPwVrM3+K7QnlUWlw6xyob3zMWF5Mkq67uXVruXFt3LPqlYY+heWnQvLbqXFt1LO+5e2vnuZcpwwhpDzKI11j+/zhqLMOvRxbTTXczEPC0+5T+0xDTqGEDbvPIfEJSdxxKzlegPTviGmlhiFpaYhSWGMf+U2CBeLDELS8yOjmyJpdwLS8wuW2K2sMRs' \
			b'YYkNSyotMbt0iCU2vGdLbCF5ssRsb4lZtcQsLLGcVCwxC0vMwhKzsMQsLDE7tsTsvCWmGU5YYohZtMR6gtZZYspFpWjCElPGoRmaqHkPLTGl6hjg2rzyN+C6IXB5bknRTiyEDJijDFgIqTOVAQshU2KDeAEuLIRETD4ycKXcC+BaXggZioWQoVgIOSqpBC6/' \
			b'dOxUcPM9A9dC8gRc/TrIoOsgA9ZB9kkFuLAOMmAdZMA6yIB1kGG8DjLMr4NMGU4AF2IWgasnaB1wKReVogng0rqiGZqoeQ+BS6k6Brg2r/x7Alw6JHxyAOOR10kQcwWQuSGYBW5a0VisjQxYG6k+FwFrIwPWRqbERs8MZlgbiZh8ZDBLuRdgtrw2MhRrI0Ox' \
			b'NnJUUglmYekQMBveM5gtJE9g1q+NDOpzEbA2sk8qYIa1kQFrIwPWRgasjQzjtZFhfm1kynACzBCzCGY9QXWq6wpIU14qXROQphll6pqohSiqBQW2nNdR2HYR29Lfso+YItehL6beFjIdhUYnM6WaKqiKNZO+XikBI45OJQZMJYbxkREn5VggzvJUYiimEkMx' \
			b'lbiHMnvl94SwfOUbxpeFtG1f+dHXVTFbuDv0edUwPyuY+DABIohZBJG+MgeRA+lmvp+acgFHm6iNOLSElJoSLSZAotwnfgOJBwISHU9aiJ500yChCVhzOgWJDiDRjY4MEinHAiS6ZZDoCpDoDoBEN3sISOQbBomFtAkkugIkupUg0c2DhPJhAiQQswgSfWUO' \
			b'ggTSzYGE5gKONlEbcQgSSs0KkDja+XwDiXsBEjyhiXn9aCZBIiUgiYg6lx8xlx/N6EggkXMcg0RcnsuPxVx+NMsgURQ+IoTkq7+x9WJaBYloxiARzTqQiPPT84kP+yChMUsgMajMIZDQdDMgkXIBR5uojTgAiUTNCpAod0n/JCBxj5en3KfRXm4nB91y08Ci' \
			b'CVjbnAKLA7C40ZGBJeVYAItbBhZXAIsbA8uopBJk3OwhIJNvGGQW0iaQcdX+N4slrzZXzhhQXIMePSl1SD2EHzcPP5rhBPwgZhF+MunrhnYTgUrRBAwp08D/JmreQxhSqg7DkCvdtDcY2mBoFoY8t5Non5+GIU3AMKQTTRETTYjJR4ahlGMBQ8sTTbGYaIrF' \
			b'RNOopBKG/OwhMJRvGIYW0iYY8lMwhEmmzA0DimvQoyeHE9IMYWh+hillOAFDiFmEoUz6ShhS9ilFEzCkFQX/m6h5D2FIqVoBQ6VT9QZDGwzNwlDgRhLtC9MwpAmMnhmGMEWEmHxkGEo5FjC0PEUUiymiWEwRjUoqYSjMHgJD+YZhaCFtgqEwBUOYHsrcMKC4' \
			b'Bj16cjgh9RCG5ueGUoYTMISYRRjKpK+EIWWfUjQBQ8o08L+JmvcQhpSqFTBUukhvMLTB0CwMRW4h0b44DUOawASca9wzDMXRkWEo5VjA0LLbcyzcnmOxonZUUglDcfYQGMo3DEMLaRMMxSkYgqNz5oYBxTXo0ZPDCamHMDTv5ZwynIAhxCzCUP/8OhhS9ilF' \
			b'EzCkTNOiU95DGNKoFTAkjs22IvggMCJVJ0DqBnsCOAUmFmNgkyvhibT3U25s4o7BKXfSPQGuAVdUecM7PXBrUP17+AqAMKq44b0tSCYAZ/Q88cDwVhZn2w7lGIjzK2HOXne1B0kwMXDHu7jy3vmyHQaJPmbEdtzQHYufoGDXDJCwy2i44+aTjHSazKpptuM2' \
			b't7DPdrxWozjyohB9pFwUsmyk7e2eYgsrbVRUAY873v2RuLRztqRKHxA/pnTDfJYrlorp9LzjALhmp0w2C5MtVZUbFCabhclmYbJZmGx2bLLteHdw+coOA59Gc0tF4KeVksSToVU0rQW8jCwUytgq62aMfOGr5/rEWhLEHNpwJWWw8lOAqLFuWGCnTb5d1/Mf' \
			b'DdpELWS4okTpy3j7WEL4l6CXfhsjv5Z/GYUtQNgGwWBPYl8i8Bz2xgS5wFsA7BBal3F1cs5OUJQBs+vttRH4rZht2wO2NaA2AWiTQHYAwEjnDgLX4gycVZByBTglUOKGnQekg1CUlE4BKKNPgps9oDkKZRbn2xKkMHrsbL+z0hgP1kyZlSq/Vt+ndX1Kyw/q' \
			b't/D/oGInjZ5TZ1Zk1uKxCiflZX0ME/q4YA6dQyWTbUOsuMuKeciaqAvFPEYpD5gJ8vK/aM3sX/hGFx7cfQ1d8Z3wZqyhR2tnPOJt6c+rnaM+h6gpS/ypNJVoMkSRCSwg7rI090av00Oae1Br3cVorpAy/FctNoP545trsgAld13IsuUu2EVq9lCrLRN1lGZX' \
			b'/yQ5ekykiEXcHGcRN4d0/OB4w/JLGKrtB6OZ7f16EWd19gsvYrrnzql04ymdi2P15g6Y5zDu4vMnl7kPbofrb+g/nkL9RY9cd5z6u2Vv1xtAQFb5fpKEGX9PX+C5w5x6zBNqbvHpDbi3WqFs79uI/dCPRAu9XDHsF51703zTyHu/vX4v2SVMMKczzGGV10NQ' \
			b'aK7nqHrpXWd+8Ryy0pnd53vfz73rWcKSwgse3M47Pyl84wcKXzqJuZX+6heg9DyKu8Zy7w5a7lY3Vp97x5O8PSYpkHd8V72+2yNel/4uD9c2z7OaNv4EWnq3RrnuzOt3enJwjaXdPCb4ZR2kZy5DB4mVTKtsMX/f9LFmnbzZQNedH3bGHKWU39xn7dQ6xpsN' \
			b'cVFxF6GWxPmOlTNeiHLOzXPfVEHZ76o9QlHtvrLmDu+4o3v3FZcTt+JLsGPHh8tR4PO9Ybll+KF2pSqnjm7Zv5WObLvXkaWqXEu7/Tneu+EM6r3WpWXt+zeeQMXNJb6Hma2f5GUsZZvTa7RU6PTvZfa2OsnUU3uMWi++od31dDicQ4cH+ltfYn/2FPq76a72' \
			b'bMd6y4y9iLfxGdX2VCrrr6ey8cwqK762m8o+IJXtNpVdqbLheirbnFtlzaayD0pl2wseUr4wlY2XMXR1efp5SoerBzZ6fDrd47UrFzVgfH1lq/5JsvmYwEQmcprLUDsSKB00/pT6t7go6kSDxQ9ZH5nJO/Z9uIy3ojv/YPCNXontLevm3HrJ2dejKdY5XvBr' \
			b'cs0axYO+yWHg0HiH1RSLUMf/a1+jkna0HvASbNmD+rpuad+hFUBSefFWmpq46V+wsXlMUCjv19t2Vtp0+KHosNn7X6/D5iHrsIEOc9gqHabqv273tloRhWVtbUVPvWjoUD1FN1XjRhuN6CYjk1IPad+TXpFUywtKVQqLbTwGgieTckZFLS08nxKvLFpJQoZ7' \
			b'WOj+FZONkxul5DC4Gdh2IR5cm2dArIRVEdgkW7YMueivx0lrBtwUhTgxO42oczsYErIpv6aa2yfkOD6bgtf2BrxuZ9h9t1juetzbY3tCr7Ow3t2A9TOv6mFLmONezNdorXUv1amXaRj0V8/WslLj8f/oLTdobYk78o12LZlY+R6aEB0hse/2hfFrxh+QpZuP' \
			b'uNxwiHNWvG57nejiMMkRYjhjkakpd9PBj5sPQs6J5y0MKZagd2BI0bePyY4VMQ6bGN+qGENQzzeGdzYxxv5Z+L8QMXbd4518KtA8ZiUjcXjMikYiQWfZc4cy2MT7dsXb3VXxdvn/7oh3syjeJ5r5OYeEf8p9K1TSXSsjgzyycBOpl3GTW5icmRoZqs0NJR8b' \
			b'JJpz2ylSxIIGWBkwoqhZXSDGPmZFp1als+weQXXehP8TwLx0qD6VwLsbC7xDLucWeHctyJ8S825WzE87wX9KSb+kbYpuJvE89Xubc/AnNXB4F9zQmzm37ulylPSTrMf5sftN1m9B1uNdlnXQf3dkfXLO5Ty+WycS94txjDyF2LNYfUJfq5PJPm95XleX4tt4' \
			b'tBZMzoZtWnBrWmDuiRZoVe6oFownJs/tyrspQq8ILHGX4n97Qnvo0nzej9YIfyc14pJWj9xIK+I91Io23gfFCJtifErFaO6jYjT3QTHyVO9trYjadAO6waJ+AT7WZzSnLnIZ4dEK0lSvec8y49B23MReIlqK4K9hUjicFxHcVa9tzYlJHDiAsqPLjgNc+O6K' \
			b'zo928pVdliB8nqrhTZh5++U4+miCsQ3nzZ85Icr582xe91RusMl6+Q2EWijY2SNyJ+mc/pOcHD7DOZ0XNnsOE5k6Xocx/uv3cW77UCnDT5RRl9/KWy4S22rlhY08+c97gMoX1r7jtSn9H0ug1+2A+n+/9yd7P0tsLUsa5QtlvPwfG70L5eGGlDPsHCQ+Vmv/' \
			b'eIlKESZkxqPJnPpk4Cyl/MG7TC09sPjHS2rm/njpCp2F5mYVzbWSze+cZuRrvPSN1vThw8NfZ1Xhyp80pDD5lCGFyScMzSRHhp8N7D8HGKv8yT/53F+T9nj/jl/A03+M3uk89T/9xLH/y09N592O4otnpAXbW5S6rrrRn9DbXYzEuULqzBkljwv+tEfbDm74' \
			b'BXfTLKU1CalvT/y45c54oEImV4gt53gGKbUXLaihwsFk+irfnu6I58h0zYH2tScRWObrOpltqxMcoVmIRr1cIbfcTzoHxg6klyDl8gSYOw6Dg2hsu6oIPO3B3eKzFrB3oMWPN+gXX5rr5JkHK05xpDGF+SSoZNjEGmLdVvf9QIOfphdVvGFXynZXnfBII2Xz' \
			b'SVDhZpNwkXAe+rznBxr8iB4bNe/R/Z0ZUc8NkcWdB5rXHTwKekRqHRLej+GB3HQDXnSb8EP42+q+HxgyPaK/eB3hHzbmekXoqvMdw0mRxZTgT9n9fKgKwZNf9/xAg6/rj9Yn0onUnut0Y6pdXHXw4BmxNekO5KKzhcupMPfXz/sJT7e+sDaWr+77gQZf1xW+' \
			b'HCUK1UUeYObW5dZWaqr7fqDB13W5L0d72uoiDzBz685rK3XVfT/Q4O29b3DDfmRdPd3wPJKVGp/tsfxBdXbNYW+1e3FYYil/y3gvOExdQTCOnOk+EawmZ4rJNo0r4JWl8hYPFrT9UBazmSfgMLVuHGGsaefn7wRIzvM5VusP9oc76oFrZj1ZDjhu7j7H2+ou' \
			b'HGD3keMCF8hudkm+AwfYPeWBeX8d4dhV/MgDzuL9/zWyOJzp+gImU6ApjxwMuOtN2VT35UDzrfP2vTfN11b35UDzHTmYcNebr6vuy4Hme1gO4fwxi3tyoPna6rWr2VNbwbRL99BOarjXThjHYfIhKYSTcT9sYOIu+y7Kh9l5DRkvcyHe1fBg8HY6dayKf6R2' \
			b'e6m5xeSJpir/bQ1B9H646ofHLZRSej0M5W1JRqjt5Wle7UYp0yq3vOIs7K82s1pKHJfCC9ywT7lk2GlRKoq8bI5FTh08+DNoMlzCQyMyJCKrlAwJoWN/YgrVPhV/lCktWcJMBn/ixUqLWZ0xD7ysyUsOOl7Ln0NIIZTmu6v/D5Qw4UU='

	_PARSER_TOP             = 'expr_commas'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	_UPARTIAL = '\u2202' # \partial
	_USUM     = '\u2211' # \sum
	_UINTG    = '\u222b' # \int
	_UXSECT   = '\u2229' # &
	_UUNION   = '\u222a' # |
	_USYMDIFF = '\u2296' # ^^

	_LETTER   = fr'[a-zA-Z]'
	_LETTERU  = fr'[a-zA-Z_]'

	_VARTEX   = '(?:' + '|'.join (reversed (sorted (x.replace ('\\', '\\\\').replace ('+', '\\+').replace ('*', '\\*').replace ('^', '\\^') for x in AST.Var.TEX2PY))) + ')'
	_VARTEX1  = fr'(?:(\d)|({_LETTER})|(\\partial|\\infty))'
	_VARPY    = fr'(?:{_LETTER}(?:\w|\\_)*)'
	_VARUNI   = fr'(?:{"|".join (AST.Var.UNI2PY)})'
	_VAR      = fr'(?:{_VARPY}|{_VARTEX}(?!{_LETTERU})|{_VARUNI})'

	_STR      = r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY)))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LETTERU})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\$?(?:{_LETTER}|\\_)(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
		('LEFTDOT',      fr'\\left\s*\.'),

		('SQRT',          r'sqrt\b|\\sqrt(?!{_LETTER})'),
		('LOG',           r'log\b|\\log(?!{_LETTER})'),
		('LN',            r'ln\b|\\ln(?!{_LETTER})'),
		('LIM',          fr'\\lim(?!{_LETTER})'),
		('SUM',          fr'\\sum(?:\s*\\limits)?(?!{_LETTER})|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?(?!{_LETTER})|{_UINTG}'),
		('LEFT',         fr'\\left(?!{_LETTERU})'),
		('RIGHT',        fr'\\right(?!{_LETTERU})'),
		('CDOT',         fr'\\cdot(?!{_LETTERU})'),
		('TO',           fr'\\to(?!{_LETTERU})'),
		('CUP',          fr'\\cup(?!{_LETTERU})'),
		('OMINUS',       fr'\\ominus(?!{_LETTERU})'),
		('CAP',          fr'\\cap(?!{_LETTERU})'),
		('MAPSTO',       fr'\\mapsto(?!{_LETTERU})'),
		('EMPTYSET',     fr'\\emptyset(?!{_LETTERU})'),
		('SETMINUS',     fr'\\setminus(?!{_LETTERU})'),
		('SUBSTACK',      r'\\substack(?!{_LETTERU})'),

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
		('FRAC',          r'\\frac(?!{_LETTERU})'),
		('BINOM2',       fr'\\binom\s*{_VARTEX1}\s*{_VARTEX1}'),
		('BINOM1',       fr'\\binom\s*{_VARTEX1}'),
		('BINOM',         r'\\binom(?!{_LETTERU})'),
		('IF',            r'if(?!{_LETTERU})'),
		('ELSE',          r'else(?!{_LETTERU})'),
		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)(?!{_LETTERU})|{"|".join (AST.Eq.UNI2PY)}'),
		('EQ',            r'='),
		('NUM',           r'(?:(\d*\.\d+)|(\d+\.?))((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))('*)"),
		('ATTR',         fr'\.\s*(?:({_LETTERU}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"({_STR})|\\text\s*{{\s*({_STR})\s*}}"),
		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
		('COLON',         r'{:}|:'),
		('DBLBAR',        r'\|\|'),
		('DBLCARET',      r'\^\^'),
		('DBLAMP',        r'&&'),
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
	_VARPY_QUICK   = fr'(?:{_PYGREEK_QUICK}|{_LETTER})'
	_VAR_QUICK     = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK   = OrderedDict ([ # quick input mode different tokens
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

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
		('CUP',          fr'\\cup'),
		('OMINUS',       fr'\\ominus'),
		('CAP',          fr'\\cap'),
		('MAPSTO',       fr'\\mapsto'),
		('EMPTYSET',     fr'\\emptyset'),
		('SETMINUS',     fr'\\setminus'),
		('SUBSTACK',      r'\\substack'),

		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)|{"|".join (AST.Eq.UNI2PY)}'),
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

	def expr               (self, expr_eq):                                        return expr_eq

	def expr_eq_1          (self, expr_mapsto1, EQ, expr_mapsto2):                 return AST ('=', '=', expr_mapsto1, expr_mapsto2)
	def expr_eq_2          (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr_colon):                 return _expr_mapsto (expr_paren.strip (), expr_colon)
	def expr_mapsto_2      (self, expr_piece):                                     return expr_piece

	def expr_piece_1       (self, expr_cmp, IF, expr_eq, ELSE, expr_mapsto):       return _expr_piece (expr_cmp, expr_eq, expr_mapsto)
	def expr_piece_2       (self, expr_cmp, IF, expr_eq):                          return AST ('piece', ((expr_cmp, expr_eq),))
	def expr_piece_3       (self, expr_cmp):                                       return expr_cmp

	def expr_cmp_1         (self, expr_union1, CMP, expr_union2):                  return AST ('=', AST.Eq.ANY2PY.get (CMP.text.replace (' ', ''), CMP.text.replace (' ', '')), expr_union1, expr_union2)
	def expr_cmp_2         (self, expr_union):                                     return expr_union

	def expr_union_1       (self, expr_union, DBLBAR, expr_sdiff):                 return AST.flatcat ('||', expr_union, expr_sdiff)
	def expr_union_2       (self, expr_union, CUP, expr_sdiff):                    return AST.flatcat ('||', expr_union, expr_sdiff)
	def expr_union_3       (self, expr_sdiff):                                     return expr_sdiff

	def expr_sdiff_1       (self, expr_sdiff, DBLCARET, expr_xsect):               return AST.flatcat ('^^', expr_sdiff, expr_xsect)
	def expr_sdiff_2       (self, expr_sdiff, OMINUS, expr_xsect):                 return AST.flatcat ('^^', expr_sdiff, expr_xsect)
	def expr_sdiff_3       (self, expr_xsect):                                     return expr_xsect

	def expr_xsect_1       (self, expr_xsect, DBLAMP, expr_add):                   return AST.flatcat ('&&', expr_xsect, expr_add)
	def expr_xsect_2       (self, expr_xsect, CAP, expr_add):                      return AST.flatcat ('&&', expr_xsect, expr_add)
	def expr_xsect_3       (self, expr_add):                                       return expr_add

	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                  return AST.flatcat ('+', expr_add, _expr_neg (expr_mul_exp))
	def expr_add_3         (self, expr_add, SETMINUS, expr_mul_exp):               return AST.flatcat ('+', expr_add, _expr_neg (expr_mul_exp))
	def expr_add_4         (self, expr_mul_exp):                                   return expr_mul_exp

	def expr_mul_exp_1     (self, expr_mul_exp, CDOT, expr_neg):                   return _expr_mul_exp (expr_mul_exp, expr_neg)
	def expr_mul_exp_2     (self, expr_mul_exp, STAR, expr_neg):                   return _expr_mul_exp (expr_mul_exp, expr_neg)
	def expr_mul_exp_3     (self, expr_neg):                                       return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                return _expr_neg (expr_neg)
	def expr_neg_2         (self, expr_diff):                                      return expr_diff

	def expr_diff          (self, expr_div):                                       return _expr_diff (expr_div)

	def expr_div_1         (self, expr_div, DIVIDE, expr_mul_imp):                 return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2         (self, expr_div, DIVIDE, MINUS, expr_mul_imp):          return AST ('/', expr_div, _expr_neg (expr_mul_imp))
	def expr_div_3         (self, expr_mul_imp):                                   return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                        return _expr_mul_imp (expr_mul_imp, expr_intg, self._USER_FUNCS)
	def expr_mul_imp_2     (self, expr_intg):                                      return expr_intg

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add):           return _expr_intg (expr_add, (expr_sub, expr_super))
	def expr_intg_2        (self, INTG, expr_add):                                 return _expr_intg (expr_add)
	def expr_intg_3        (self, expr_lim):                                       return expr_lim

	def expr_lim_1         (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                          return AST ('lim', expr_neg, expr_var, expr)
	def expr_lim_2         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):  return AST ('lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg): return AST ('lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                        return expr_sum

	def expr_sum_1         (self, SUM, SUB, CURLYL, varass, CURLYR, expr_super, expr_neg):                          return AST ('sum', expr_neg, varass [0], varass [1], expr_super)
	def expr_sum_2         (self, expr_func):                                                                       return expr_func

	def expr_func_1        (self, SQRT, BRACKL, expr, BRACKR, expr_neg_func):      return _expr_func (1, 'sqrt', expr_neg_func, expr)
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

	def expr_attr_1        (self, expr_attr, ATTR):                                return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1])
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
	def expr_curly_4       (self, expr_term):                                      return expr_term

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

	def varass             (self, expr_var, EQ, expr):                             return (expr_var, expr)

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
		if not text.strip ():
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
				res = (res [0].no_curlys.flat (),) + res [1:] if isinstance (res [0], AST) else res

				print ('parse:', res, file = sys.stderr)

			if len (rated) > 32:
				print (f'... total {len (rated)}', file = sys.stderr)

			print (file = sys.stderr)

		res = next (iter (rated)) [-1]

		return (res [0].no_curlys.flat (),) + res [1:] if isinstance (res [0], AST) else res

class sparser: # for single script
	Parser = Parser

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
# 	p = Parser ()
# 	# p.set_user_funcs ({'f': 1})
# 	a = p.parse (r'x**-y[0]')
# 	# a = sym.ast2spt (a)
# 	print (a)
