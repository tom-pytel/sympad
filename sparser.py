# Builds expression tree from text, nodes are nested AST tuples.
#
# Time and interest permitting:
# sets
# assumptions/hints
# importing modules to allow custom code execution
# Proper implementation of vectors with "<b>\vec{x}</b>" and "<b>\hat{i}</b>" variables
# sympy function/variable module prefix
# systems of equations, ODEs, graphical plots (using matplotlib?)...

# TODO: multiple vector weirdness
# TODO: _xlat_func_Integral multiple integrals

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

def _ast_from_tok_digit_or_var (tok, i = 0):
	return AST ('#', tok.grp [i]) if tok.grp [i] else \
			AST ('@', AST.Var.ANY2PY.get (tok.grp [i + 2].replace (' ', ''), tok.grp [i + 1]) if tok.grp [i + 2] else tok.grp [i + 1])

def _ast_func_tuple_args (ast):
	ast = ast.strip ()

	return ast.commas if ast.is_comma else (ast,)

def _expr_lambda (lhs, expr):
	if lhs.is_var:
		if lhs.is_var_lambda:
			return AST ('lamb', expr, ())

	elif lhs.is_mul:
		if lhs.muls [-1].is_var:
			if lhs.muls [-1].is_var_lambda:
				return AST ('*', lhs.muls [:-1] + (('lamb', expr, ()),))

			if lhs.muls [-2].is_var_lambda:
				ast = AST ('lamb', expr, (lhs.muls [-1],))

				return ast if len (lhs.muls) == 2 else AST ('*', lhs.muls [:-2] + (ast,))

	elif lhs.is_comma:
		commas = lhs.commas
		ast    = None

		for imul in range (len (commas) - 1, -1, -1):
			if commas [imul].is_var:
				if commas [imul].is_var_lambda:
					ast = AST ('lamb', expr, commas [imul + 1:])

					break

				continue

			if commas [imul].is_mul:
				if commas [imul].muls [-1].is_var and commas [imul].muls [-2].is_var_lambda:
					ast = AST ('lamb', expr, (commas [imul].muls [-1],) + commas [imul + 1:])

					if len (commas [imul].muls) > 2:
						ast = AST ('*', commas [imul].muls [:-2] + (ast,))

					break

		if ast:
			return ast if imul == 0 else AST (',', commas [:imul] + (ast,))

	raise SyntaxError ('invalid lambda expression')

def _expr_mapsto (lhs, expr):
	lhs = lhs.strip ()

	if lhs.is_var:
		return AST ('lamb', expr, (lhs,))

	if lhs.is_comma:
		for var in lhs.commas:
			if not var.is_var:
				break

		else:
			return AST ('lamb', expr, lhs.commas)

	raise SyntaxError ('invalid LaTeX \\mapsto expression')

def _expr_mul_imp (lhs, rhs, user_funcs = {}):
	last      = lhs.muls [-1] if lhs.is_mul else lhs
	arg, wrap = _expr_func_reorder (rhs, strip = 0)
	ast       = None

	if last.is_attr: # {x.y} * () -> x.y(), x.{y.z} -> {x.y}.z
		if last.args is None:
			if arg.is_paren:
				ast = wrap (AST ('.', last.obj, last.attr, _ast_func_tuple_args (arg)))
			elif rhs.is_attr:
				ast = AST ('.', _expr_mul_imp (last, rhs.obj), rhs.attr)

	elif last.is_pow: # {x^y.z} * () -> x^{y.z()}
		if last.exp.is_attr and last.exp.args is None:
			if arg.is_paren:
				ast = AST ('^', last.base, wrap (AST ('.', last.exp.obj, last.exp.attr, _ast_func_tuple_args (arg))))
			elif rhs.is_attr:
				ast = AST ('^', last.base, ('.', _expr_mul_imp (last.exp, rhs.obj), rhs.attr))

	elif last.is_var:
		if last.var in user_funcs:
			if arg.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg)))

	if ast:
		return AST ('*', lhs.muls [:-1] + (ast,)) if lhs.is_mul else ast

	return AST.flatcat ('*', lhs, rhs)

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast.numer.is_diff_or_part_solo:
			p = 1
			v = ast.numer

		elif ast.numer.is_pow and ast.numer.base.is_diff_or_part_solo and ast.numer.exp.remove_curlys ().is_pos_int:
			p = int (ast.numer.exp.remove_curlys ().num)
			v = ast.numer.base

		else:
			return None

		ast_dv_check = (lambda n: n.is_differential) if v.is_diff_solo else (lambda n: n.is_partial)

		ns = ast.denom.muls if ast.denom.is_mul else (ast.denom,)
		ds = []
		cp = p

		for i in range (len (ns)):
			n = ns [i]

			if ast_dv_check (n):
				dec = 1
			elif n.is_pow and ast_dv_check (n.base) and n.exp.remove_curlys ().is_pos_int:
				dec = int (n.exp.remove_curlys ().num)
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
		end  = len (ast.muls)

		for i in range (end - 1, -1, -1):
			if ast.muls [i].is_div:
				diff = _interpret_divide (ast.muls [i])

				if diff:
					if diff.expr:
						if i < end - 1:
							tail [0 : 0] = ast.muls [i + 1 : end]

						tail.insert (0, diff)

					elif i < end - 1:
						tail.insert (0, AST ('diff', ast.muls [i + 1] if i == end - 2 else AST ('*', ast.muls [i + 1 : end]), diff.dvs))

					else:
						continue

					end = i

		if tail:
			tail = tail [0] if len (tail) == 1 else AST ('*', tuple (tail))

			return tail if end == 0 else AST.flatcat ('*', ast.muls [0], tail) if end == 1 else AST.flatcat ('*', AST ('*', ast.muls [:end]), tail)

	return ast

def _ast_strip_tail_differential (ast):
	if ast.is_differential or ast.is_null_var: # null_var is for autocomplete
		return None, ast

	if ast.is_intg:
		if ast.intg is not None:
			ast2, neg = ast.intg.strip_minus (retneg = True)
			ast2, dv  = _ast_strip_tail_differential (ast2)

			if dv:
				return \
						(AST ('intg', neg (ast2), dv, *ast [3:]), ast.dv) \
						if ast2 else \
						(AST ('intg', neg (AST.One), dv, *ast [3:]), ast.dv) \
						if neg.has_neg else \
						(AST ('intg', None, dv, *ast [3:]), ast.dv)

	elif ast.is_diff:
		ast2, neg = ast.diff.strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			return \
					(AST ('diff', neg (ast2), ast.dvs), dv) \
					if ast2 else \
					(neg (AST ('/', ('@', ast.diff_type or 'd'), ast.dvs [0])), dv) \
					if len (ast.dvs) == 1 else \
					(neg (AST ('/', ('@', ast.diff_type or 'd'), ('*', ast.dvs))), dv)
			# raise NotImplementedError ('changing differential to ordinary fraction')

	elif ast.is_div:
		ast2, neg = ast.denom.strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('/', ast.numer, neg (ast2)), dv

		ast2, neg = ast.numer.strip_minus (retneg = True)

		if dv:
			return AST ('/', neg (ast2) if ast2 else neg (AST.One), ast.denom), dv

	elif ast.is_mul:
		ast2, neg = ast.muls [-1].strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			return \
					(AST ('*', ast.muls [:-1] + (neg (ast2),)), dv) \
					if ast2 else \
					(neg (AST ('*', ast.muls [:-1])), dv) \
					if len (ast.muls) > 2 else \
					(neg (ast.muls [0]), dv)

	elif ast.is_add:
		ast2, neg = ast.adds [-1].strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('+', ast.adds [:-1] + (neg (ast2),)), dv

	return ast, None

def _expr_int (ast, from_to = ()): # find differential for integration if present in ast and return integral ast
	ast, neg = ast.strip_minus (retneg = True)
	ast, dv  = _ast_strip_tail_differential (ast)

	if dv:
		return \
				AST ('intg', neg (ast), dv, *from_to) \
				if ast else \
				AST ('intg', neg (AST.One), dv, *from_to) \
				if neg.has_neg else \
				neg (AST ('intg', None, dv, *from_to))

	raise SyntaxError ('integration expecting a differential')

_xlat_func_Limit_dirs = {'+': ('+',), '-': ('-',), '+-': ()}

def _xlat_func_Derivative (ast): # translate function 'Derivative' to native ast representation for pretty rendering
	if ast.is_null_var:
		return AST ('diff', ast, (AST.VarNull,))
	elif not ast.is_comma:
		raise lalr1.Incomplete (AST ('diff', ast, (AST.VarNull,)))
	elif len (ast.commas) == 0:
		raise lalr1.Incomplete (AST ('diff', AST.VarNull, (AST.VarNull,)))
	elif len (ast.commas) == 1:
		raise lalr1.Incomplete (AST ('diff', ast.commas [0], (AST.VarNull,)))

	commas = list (ast.commas [:0:-1])
	ds     = []

	while commas:
		d = commas.pop ().as_diff

		if commas and commas [-1].is_num:
			ds.append (AST ('^', d, commas.pop ()))
		else:
			ds.append (d)

	return AST ('diff', ast.commas [0], AST (*ds))

def _xlat_func_Integral (ast): # translate function 'Integral' to native ast representation for pretty rendering
	if not ast.is_comma:
		return AST ('intg', ast, ast.as_diff if ast.is_var else AST.VarNull)
	elif len (ast.commas) == 0:
		ast = AST ('intg', AST.VarNull, AST.VarNull)
	elif len (ast.commas) == 1:
		ast = AST ('intg', ast.commas [0], AST.VarNull)

	else:
		ast2 = ast.commas [1].strip (1)

		if not ast2.is_comma:
			return AST ('intg', ast.commas [0], ast2.as_diff)
		elif len (ast2.commas) == 3:
			return AST ('intg', ast.commas [0], ast2.commas [0].as_diff, ast2.commas [1], ast2.commas [2])
		else:
			ast = AST (*(('intg', ast.commas [0], ast2.commas [0].as_diff) + ast2.commas [1:] + (AST.VarNull, AST.VarNull)) [:5])

	raise lalr1.Incomplete (ast)

def _xlat_func_Limit (ast): # translate function 'Limit' to native ast representation for pretty rendering
	if ast.is_null_var:
		return AST ('lim', ast, AST.VarNull, AST.VarNull)
	elif not ast.is_comma:
		raise lalr1.Incomplete (AST ('lim', ast, AST.VarNull, AST.VarNull))

	commas = ast.commas
	l      = len (commas)

	if l == 0:
		ast = AST ('lim', AST.VarNull, AST.VarNull, AST.VarNull)
	elif l == 1:
		ast = AST ('lim', commas [0], AST.VarNull, AST.VarNull)
	elif l == 2:
		ast = AST ('lim', commas [0], commas [1], AST.VarNull)
	elif l == 3:
		return AST ('lim', commas [0], commas [1], commas [2], '+')
	elif commas [3].is_str:
		return AST ('lim', *(commas [:3] + _xlat_func_Limit_dirs.get (commas [3].str_, ('+',))))
	elif commas [3].is_ass and commas [3].lhs.as_identifier () == 'dir' and commas [3].rhs.is_str:
		return AST ('lim', *(commas [:3] + _xlat_func_Limit_dirs.get (commas [3].rhs.str_, ('+',))))
	else:
		ast = AST ('lim', commas [0], commas [1], commas [2])

	if l and commas [-1].is_null_var:
		return ast

	raise lalr1.Incomplete (ast)

def _xlat_func_Matrix (ast):
	if ast.is_brack and ast.bracks:
		if not ast.bracks [0].is_brack: # single layer or brackets, column matrix?
			return AST ('vec', ast.bracks)

		elif ast.bracks [0].bracks:
			rows = [ast.bracks [0].bracks]
			cols = len (rows [0])

			for row in ast.bracks [1 : -1]:
				if len (row.bracks) != cols:
					break

				rows.append (row.bracks)

			else:
				l = len (ast.bracks [-1].bracks)

				if l <= cols:
					if len (ast.bracks) > 1:
						rows.append (ast.bracks [-1].bracks + (AST.VarNull,) * (cols - l))

					if l != cols:
						raise lalr1.Incomplete (AST ('mat', tuple (rows)))

					return \
							AST ('mat', tuple (rows)) \
							if cols > 1 else \
							AST ('vec', tuple (r [0] for r in rows))

	return AST ('func', 'Matrix', (ast,))

def _xlat_func_Piecewise (ast):
	pcs = []

	if ast.is_comma and ast.commas and ast.commas [0].strip_paren ().is_comma:
		for c in ast.commas [:-1]:
			c = c.strip_paren ()

			if not c.is_comma or len (c.commas) != 2:
				raise SyntaxError ('expecting tuple of length 2')

			pcs.append (c.commas)

		ast = ast.commas [-1].strip_paren ()

	pcs = tuple (pcs)

	if not ast.is_comma:
		raise lalr1.Incomplete (AST ('piece', pcs + ((ast, AST.VarNull),)))
	if len (ast.commas) == 0:
		raise lalr1.Incomplete (AST ('piece', pcs + ()))

	if not ast.commas [0].is_comma:
		if len (ast.commas) == 1:
			raise lalr1.Incomplete (AST ('piece', pcs + ((ast.commas [0], AST.VarNull),)))
		if len (ast.commas) == 2:
			return AST ('piece', pcs + ((ast.commas [0], True if ast.commas [1] == AST.True_ else ast.commas [1]),))
			# return AST ('piece', pcs + ((ast.commas [0], True if ast.commas [1].stip_curlys ().strip_paren () == AST.True_ else ast.commas [1]),))

		raise SyntaxError ('invalid tuple length')

	raise RuntimeError ()

def _xlat_func_Pow (ast):
	if not ast.is_comma:
		raise lalr1.Incomplete (AST ('^', ast, AST.VarNull))
	elif len (ast.commas) == 0:
		raise lalr1.Incomplete (AST ('^', AST.VarNull, AST.VarNull))
	elif len (ast.commas) == 1:
		raise lalr1.Incomplete (AST ('^', ast.commas [0], AST.VarNull))

	elif len (ast.commas) == 2:
		ast = AST ('^', ast.commas [0], ast.commas [1])

		if ast.exp.is_null_var:
			raise lalr1.Incomplete (ast)
		else:
			return ast

	raise SyntaxError ('too many parameters')

def _xlat_func_Sum (ast): # translate function 'Sum' to native ast representation for pretty rendering
	if ast.is_null_var:
		return AST ('sum', ast, AST.VarNull, AST.VarNull, AST.VarNull)
	elif not ast.is_comma:
		raise lalr1.Incomplete (AST ('sum', ast, AST.VarNull, AST.VarNull, AST.VarNull))

	commas = ast.commas

	if len (commas) == 0:
		raise lalr1.Incomplete (AST ('sum', AST.VarNull, AST.VarNull, AST.VarNull, AST.VarNull))
	elif len (commas) == 1:
		ast = AST ('sum', commas [0], AST.VarNull, AST.VarNull, AST.VarNull)

	else:
		ast2 = commas [1].strip_paren (1)

		if not ast2.is_comma:
			ast = AST ('sum', commas [0], ast2, AST.VarNull, AST.VarNull)
		elif len (ast2.commas) == 3:
			return AST ('sum', commas [0], ast2.commas [0], ast2.commas [1], ast2.commas [2])

		else:
			commas = ast2.commas
			ast    = AST (*(('sum', ast.commas [0], *commas) + (AST.VarNull, AST.VarNull, AST.VarNull)) [:5])

	if commas [-1].is_null_var:
		return ast

	raise lalr1.Incomplete (ast)

# eye(2).a -> ('.', ('func', 'eye', (('.', ('(', ('#', '2')), 'a'),)), 'a')
# eye((2).a) -> ('func', 'eye', (('.', ('(', ('#', '2')), 'a'),))

def _expr_func (iparm, *args, strip = 0): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	def astarg (arg):
		return (_ast_func_tuple_args (arg) if args [0] == 'func' else arg.strip (strip)),

	if args [iparm].is_fact:
		if args [iparm].fact.is_paren:
			return AST ('!', args [:iparm] + astarg (args [iparm].fact) + args [iparm + 1:])

	elif args [iparm].is_pow:
		if args [iparm].base.is_paren:
			return AST ('^', args [:iparm] + astarg (args [iparm].base) + args [iparm + 1:], args [iparm].exp)

	elif args [iparm].is_attr:
		if args [iparm].obj.is_paren:
			if args [0] != 'func':
				return AST ('.', args [:iparm] + (args [iparm].strip (strip),) + args [iparm + 1:], *args [iparm] [2:])
			else:
				return AST ('.', args [:iparm] + (_ast_func_tuple_args (args [iparm].obj),) + args [iparm + 1:], *args [iparm] [2:])

	return AST (*(args [:iparm] + astarg (args [iparm]) + args [iparm + 1:]))

def _expr_func_reorder (ast, strip):
	ast = _expr_func (1, None, ast, strip = strip)

	return \
			(ast [1], lambda a: a) \
			if ast.op is None else \
			(ast [1] [1], lambda a: AST (ast.op, a, *ast [2:]))

def _expr_func_xlat (_xlat_func, ast): # rearrange ast tree for a given function translation like 'Derivative' or 'Limit'
	ast, wrap = _expr_func_reorder (ast, strip = None) # strip all parentheses

	return wrap (_xlat_func (ast))

_FUNC_AST_XLAT = {
	'Abs'       : lambda expr: _expr_func (1, '|', expr, strip = 1),
	'abs'       : lambda expr: _expr_func (1, '|', expr, strip = 1),
	'Derivative': lambda expr: _expr_func_xlat (_xlat_func_Derivative, expr),
	'diff'      : lambda expr: _expr_func_xlat (_xlat_func_Derivative, expr),
	'exp'       : lambda expr: _expr_func (2, '^', AST.E, expr, strip = 1),
	'factorial' : lambda expr: _expr_func (1, '!', expr, strip = 1),
	'Gamma'     : lambda expr: _expr_func (2, 'func', 'gamma', expr, strip = 1),
	'Integral'  : lambda expr: _expr_func_xlat (_xlat_func_Integral, expr),
	'integrate' : lambda expr: _expr_func_xlat (_xlat_func_Integral, expr),
	'Limit'     : lambda expr: _expr_func_xlat (_xlat_func_Limit, expr),
	'limit'     : lambda expr: _expr_func_xlat (_xlat_func_Limit, expr),
	'Matrix'    : lambda expr: _expr_func_xlat (_xlat_func_Matrix, expr),
	'ln'        : lambda expr: _expr_func (1, 'log', expr),
	'Piecewise' : lambda expr: _expr_func_xlat (_xlat_func_Piecewise, expr),
	'Pow'       : lambda expr: _expr_func_xlat (_xlat_func_Pow, expr),
	'pow'       : lambda expr: _expr_func_xlat (_xlat_func_Pow, expr),
	'Sum'       : lambda expr: _expr_func_xlat (_xlat_func_Sum, expr),
}

def _expr_func_func (FUNC, expr_func_arg):
	func = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC
	xlat = _FUNC_AST_XLAT.get (func)
	ast  = _expr_func (2, 'func', func, expr_func_arg)

	if not xlat:
		return ast

	args = ast.args if ast.is_func else ast [1].args
	arg  = args [0] if len (args) == 1 else AST (',', args)
	ast2 = xlat (AST ('(', arg))

	return ast2 if ast.is_func else AST (ast.op, ast2, *ast [2:])

def _expr_mat (expr_mat_rows):
	return \
			AST.MatEmpty \
			if not expr_mat_rows else \
			AST ('mat', expr_mat_rows) \
			if len (expr_mat_rows [0]) > 1 else  \
			AST ('vec', tuple (c [0] for c in expr_mat_rows))

def _expr_curly (ast): # convert curly expression to vector or matrix if appropriate
	if ast.op != ',':
		return AST ('{', ast)
	elif not ast.commas: # empty {}?
		return AST.VarNull

	c = sum (bool (c.is_vec) for c in ast.commas)

	if c == len (ast.commas) and len (set (len (c.vec) for c in ast.commas)) == 1:
		return \
				AST ('mat', tuple (c.vec for c in ast.commas)) \
				if len (ast.commas [0].vec) > 1 else \
				AST ('vec', tuple (c.vec [0] for c in ast.commas))

	return AST ('vec', ast.commas) # raise SyntaxError ('invalid matrix syntax')


#...............................................................................................
class Parser (lalr1.Parser):
	_USER_FUNCS = set () # set or dict of variable names to be translated into 'func' ASTs if variable followed by parentheses

	def set_user_funcs  (self, user_funcs):
		self._USER_FUNCS = user_funcs

	_PARSER_TABLES = \
			b'eJztXWuP3LaS/TMLZAZQAxJfkvzNcZxcY/3ItZ1gFwPDcBxnEWycZG3n7i4W979vnaqSSJHqh2a6Z7pnBsNpSRQfxWIdPopF6uziq0cvnr54/lX11b98+P1nujx9/O1runz/8OXj50/p5sl3z1+8fPz20Q8vn/47PX778uEjvTR6NXT9+vF3bx89fPX4ld4/' \
			b'e/ha776Otz/G2+/lllNFLs+ePP+B41J6/wqPV69f4veHr+n3+Q/P6PfHh/B58vz1d6DyyTN+zb9/f4m0nr7Ai29/eA76vubAj148e/ZwKMzLIT/cPHz2/ZAbHr/5+umrpw9f/Y1uHz//RqnH3dfx9sd4q9S/fPLd3wavofCP/46fp68ea6qvhRAiACGfPfz+' \
			b'1esXyP81l+/xvz16OrwGO7958uOTbxD10TcvXjMXtNCc7PdPmUdPvqUfToXYg1jv33368OXtH5/e/vzTb5+/vPtEXh/+589Pbz//9eeH8eGXv35///bdp/+IL38abj+++/L2/R+/pY+f/vjv7PHz8Pz+3ecPnz+/nz7+OX0cnt79FG+/fIm0vHv/Zbj/M+YE' \
			b'EiN5H4fb334db3/9fYz38a/f3v76ccz3H7HYv8eoP//6j+H2y4dPifcvvwz3P3169/4/P4zJ/v5h5ND7vz799r9pdnSTMGUs2M8/Twofaf3wX2PJKJOxwL9+eP9hfKCq+z0m+ufnL3+MxX738aef3w1PY1pjXn98/Phu8vD5qzfVxdnKNZVrziu5Mbix1crx' \
			b'tanOTGVCtWoq29LN+ejLftFj1eKmMfLjyaNx56lX41Iv3CJiLT9OXtAdpcVBWmTceM2YPAdf9Rs9Vk3Pd0RTR7FNZbtz9Vg1llMFBdZW1pzrIz3xnUO4CrlKcqOHPNkhHkVwgxdu6c7wv6H87bk8rzjNRv2Fhmpl1FOePdFvmXH94EFl4Dsi3tScUi0/jtI2' \
			b'mnj0AhujL25Rb/TvK9tXK38uz3SDEL38OPGmO2Ix7sgfOYNFUnLyCMlDKxd4IB4qAyUXovURtBNzmqm/Kx+7qZcvHl2deq1Mx6ym7E2rd2dcbGVqrTKGajODF24Rn1gBviBTFwMM3vFxZZhDnmunhrjL4ypwAPI3TUXiheoylBmKX4GBjYj8mhCAkG92DEiF' \
			b'mgZcGc490H9bOTtQRTXDLKEEBBSoR6pvm0KD3g3eowf4Ah8XfRrx8dHHiE8YfEgomeut/CToANj4JsgPA0MqhZ5wizs/vDzXR3oaXkgeTn5cN5Z99OpTL9yCMVZ+qNrOz+MtwgSRjCEKRJg5BYbzDTcjdmi+pGUgP8Hg+Oi4buyASiontymdiJZHMStIk3At' \
			b'9VYPeuZsO/kh0TvXZwIdF57eNJyuPnlpRagAJBJROCD1ImcsvSoZYYACeZ65ZoSCPibgYB8z5ENPjlnY9FUz3rR6Q1wa7wQ8REl/Tl3CRV2RNFK2BEfiNsGFRI1+fOVD5dsqmCrYqvNVF6qurbqu6vqqr6ue2NyhDMiYgeBZXqliKBSJbXBV8FUIVaBEuipQ' \
			b'S9NWbVe1PdUGit2ZqqOmxYAfVCwSvqamh5qeaqql2qPBQSNP2eOZ8q+rrgGovKs8EUispXzqKjRVH6qecGQAJUfC5YkbaENJ8HpT9VSmALGguiRYUOwqoDukJ2IGFbQBK9BA4dkEuVj2RsOGRzxRGKtPXl4Sh9ib2ARvSeksaOBOEgwSp5EwTnPrOJu7yvyz' \
			b'TjlH9NxpNnQqKj0LRy8iSSUTIbH8WspUlkYKMZKf0y4kv5GGg4W330tqtaTmG4GPiDVX51mndDcs+WjsKFFqf9HcVObutjVnTRCmSTW3wq12YFfHPBQqibhIzD6pmHA2ZegVBeICA907jGFq/VnaW1e1vmqJcFO1tmrrqm3uMlPCPVNKprT3TCmZ0t0zJe8v' \
			b'gnYUcjFy6awMJJ125zJYsNIPWyODT6YUoWoNXevws/YaTfw7jn3kfctZNxAvg/JORzJeyuD5be+q3mvVjhV5op3pmdda8p2UUGo+1DqzkLruhRu9jqGdziyYKTSx9vVRlIUIk9pzPhImlXUk5AkbXZuQR2RQ3BqIb46FTBGFnmt5QiDe9gIFO8xibauI0eZg' \
			b'QMzdHqJREc35pLgjL6TcwpH50t+C8qO0otQAGy7LiJNnA5Wbyr8PARAOnlr5qah3GgYdw+DuNoOB5R+qyDvNBne3i99xZxgV31TAO90rgJAJP3p+puLdabZYZsuVh6/p8gcNSC0zl9XHdL0ds7aLM0bQ6Rejuw3FwOoDi1ijUyGZP5lGF/SMzIga1a1kq4At' \
			b'V+WJFv0CawqnSz4WQrjmpMmYWT99I4ussuiQNNrQwXPMVgK3ErU1Q63KLLmth+cmrXUoq5FYaOXSSVqWmyho1sDS02Bgra0rc6dQFngZ/00X6/pBx8Y82ic1fVRmGVFmGVFmGTC9F6a7oc6lQmUxycaeVrpf6Wlv/eDszPXKMm6WjkKmnNMKYogdj34R+jsh' \
			b'rD0uwghSqrLrj6USqb2s633DGypS1UwaUUEa0TxKEzRpn70223S1ak7DQ2/Lj2awigHY8XpiZsN6izQWMcmmfXaQWPfrsDOj+MZMeeXSR0wF7blMAZN6wIzIqlmKlZlQ+tbqW2KILXoTSaiwcJjxxTjN6jjNyAAN8407bSjCw1Ijw9I7rKOApFiRFCtjAsW3' \
			b'1TGekcEdZit3HN/t3RaUIP1JEHkJ2jJZaZlOYo37AhMMeyITDJ5Z2Nuit8HUx+gExcoExcoEhS7DUC4kD24yXMEg3cj6tpV1ZO4sdfbYc0N+FMXE2I8HY4IKouRcRk3uXGfOb3h+7dg+Gb9Eg9MBgLu7C2YYkljVFU0GUa0MqqI6oZ6+t8LLE2l/iEBXjOOI' \
			b'WCeQcAIJp3N2p5N1d0xTLqBNZdurbPthxCCy7Vm2vQq1n5lkoHqkxF5K7O+y9p9i3eHyQ8C96B6DdhBBZCOIbIShG6ho8Kn8CknXQBFbjdierD72AgVupcAt40hU5mrLHvAu0zGiwJ1wqpOInYbtTpsN/QmTTxSdLvmQnV5NIWu1hazPZf/WRQ34USslFKB1' \
			b'AUVjkgEbUFSjwNtQCJ5xqsT5p/yQtk5KlpYAbHDMgA5NWWQYt4op26RhTMuK+WnLnGb2E3vAP7aCTCwNpeDEqJr8mKnkh3KgICgJmIjiYE0LZcLqFZausKqFFS1sV0Pbg01s2MFG5WuwtwocRvMJK2GYCMP6Fx0fej3YDKIOscsIe4Ows4c3GVI4GJNCFw09' \
			b'NHb6cAtOfrBPxTAHlqjY9YbFGZj6w7IdhtxYccFiC9ZhsAjT0juofaDzgTUzhkTY7oLmHTWMHU8wZ4Uta99RrWJjsMfeYGyFdLyBFjtL4UU+AZsnW/knMVtRV4P9tbyHEts04Y/NoX0Mlv6T1K1avKP/DltDkQG2X9bYqF7Dp8Yu0xp7Wemp4wfsyqU8PPYM' \
			b'05VIXWFHaw/SWtlcPWbiZzP2kwv2OeOW+LASCcIDSuCUCqdFwS5ZkryVw37XGnljKyo/DPE8+MSb1Skxk+TEiSoTsT21183S2LGPVxXvSR+IbPEPP0oqJP4BTMcVe7sbSQ37sR12c2ObK2+JBe2U5CRv7BnGDugevPaSKrYgUwJdUj3OKomgH4mDVMqUILUK' \
			b'9Zvq/3z3AAEJAQ9WAEN4gLAEhAcQDAIDexv1btn7n1AaoXXI2oasVZAm4YptQAeIC76nyN6E6gzNjN5NyM0QmyN1I0pzZCaoZDSuQ+EGCM5BT2F3OIjxcQIDakq8bMJKjhIBxlpQ5GDIQbAJALnYJyIPUZ8RcR5Rkay2Sd/FXabunxz7LnuF7stG6ZVZm4zK' \
			b't3dlXjts0bPqmooofUTmm0Tsw7RPm3bovImjRim7EhHclw0oaK/Yb1E47DmAfX+BDDfThw0Iadb0X2nfRf6wS2DEUDgsnmOZe4Ie1CtNc3oGCgBB1AXZ6d8PQCFx78e/JagBTlLQZLgRH3hmAOpn/pCt7WMcjSkQ4ztBGcL1nnHWM9I4fSeXoNEQKAdeH6EG' \
			b'mI0Q40JnMBNGRKhFevqy04F3AjuhiCqYgxc9Diet8OOAk9TT3sb2D9As9dTZsOw6+wCQJxmhq/knL0IyVvsEreFYcDoP0uayOL3NGEWvEMA/lLCWLk27Mz5khkEq71K3BKmcbIJU7ogiUmOaGVLLXCcU2IIuABaJBnlIe0ZFLefSy8XJJQyRc8xyGnOg1XcZ' \
			b'bAe+ROBGumaAKzmOwNWAqPZ6DrkDhwS7HHSSwQx2ZzDr8v71yBF7D9cCriLeKNoUq82I1SZ3i7Ca9arNtFeNaeZY3egYq5mXdK5NswaojQBV+tdG+leNWQC1WQdUCZ8DVZmSAHUkag6o0x5WA6LCZ7vYgT0KVOlkkwx2A6q/E0C97eNfzKECT2L8FKx+BKvP' \
			b'3SKw+gysfgrWMc0crEWuEwpsQdcAVj+CFbcDVL1A1QtUvUB1jFqg1a9Dq4TP0apcSdA6es6h1U/RKgG5xmfRqvxRtHpBa8xg2ZA43KP2NqCW9TtQOrRT1I46VXmXukWobTPUtlPUjmnmqC1ynVBgC7oG1EatKh/Ip6gVtSpf5IULSdQCte061Er4HLXKlQS1' \
			b'Y9JzqG2nqJWAqPF2FrXKH0VtK6iNGSxDbXuP2tuA2o5lvYOboLYbUdvlbhFquwy13RS1Y5o5aotcJxTYgq4BtV1EbRdR2wlqO0FtJ6gdoxao7dahVsLnqFWuJKgdk55D7VTlqwFR490sapU/itpOUBszWIba7l5VfJvga1gNhYoTHRQuRCBfxFNALCFStwTE' \
			b'JtNEmakmKqaZgbjMNSfCFqQpjk3UROFWcWxED2VED2VEDxWj5jg261RRGj7D8cCYiOOY9AyOzVQVpQGxdW5WFTWwSHBsRBWVZLAMx/09jm8VjnnKi5qSKS+fdt5Ueui5GSe+EiJ1i3CcTXzNdOIb08xxXOTa6CabMYYtaBuAHCe/Jk5+jUx+jUx+jUx+Y9QC' \
			b'yOsmvxo+B7JyJgHy6DkH5OnkVwN6K+FLICuPFMgy+U0yWAbkpr5H8q1CcmCpZ8dIDoLkIEgOI5JD7hYhOWRIDlMkj2nmSC5yzYmwBWkDkKPVBG4HIAcBchAgBwHyGLUAclgHZAmfA1kZkwB5THoOyGEKZAkIIIdZICuLFMhBgBwzWAjk5h7ItwrIrM9CHYk+' \
			b'i63NGrnUVbQUlBCpWwTkTKtlplqtmGYO5CLXnAhbkDYAOSq2TFRsqb2gEcWWEcVWjFoAeZ1iS8PnQFbGJEAek54D8lSxpQEB5FnF1sAiBbIotpIMFgL53pzqdgGZVVyoIFFxGdFyyedX+KJA7nK3CMiZostMFV0xzRzIRa45EbYgbQBy1HWZqOsyousyousy' \
			b'ouuKUQsgr9N1afgcyMqYBMhj0nNAnuq6NCCAPKvrGlikQBZdV5LBQiDbCOTm9LHcZscL311EN6LqNeAh7vEZFMOg5gu324P22uRukfbaZNprM9Vej2nm2usi15wIW5A2KLBNVGAbBnXDX3PrRJEtlsp8kQAuJEkUimyzBtwaPldkK4MSRfaY9Jwi20wV2RIQ' \
			b'UmBmFdlKviqyjSiyYwYLwT1vlDXZrXNaS1CXscm66haddSjeA4LxhSpe3ui29c+WOzPeEJouQbXio52zzd2Vtgog/sSW0oz/RQdd5Dyhwha0DUDGboKOizEx0UII3Wwg2QXJWky5ss7ZTvCLpGL/LJnl/bPyZrrlAF4zAJ50zZY3H6Bm61n4aspD34zaBJ+r' \
			b'lQA5Fn8C5N494KYsdHS1DFxfWkAfX6eMTcX7tYa+7Z0y78ACG1FrTkbaTkbaTkbabgSzy92ikbbLsOwyLNdDojmSi2wzF6RjzmmDebQMuF0ccLsIaCcDbicDbtlDFGMXmHbrBtwSPge08icZcI9Jzw243RTVEtBbCV+CWglWUMvuoiSDhX1yYcl1fMC+nznv' \
			b'DmnLq1L8GVjGs5VVKSurUnZclZIQqVuCZ5utStnpqlRMM4NzmWtOhC1I077ZxkUpGxelrCxKWVmUsrIoFaPmQLbrFqU0fAbkgTERyDHpGSDb6aKUBsTxSbOLUgOLBMhWFqWSDBYCuTDuOhCQk3MB7uF8cDjz0pRlx3CWpSkrS1N2XJqyIXeL4JwtTfUCZ+zJ' \
			b'xcEQnYA6wN+WC1Rl3jkptiBwAHVcoLJxgcrKApWVBSorC1QxagHqdQtUGj4HtbInAfWY9ByopwtUGtBbCV+CWt4PoJYFqiSDhaC+t/26VXB2bPsF5ovtlxPbLye2X260/ZKH1C2Bs8tsv9zU9iummQG5zDUnwhakKZBdtP1y0fbLie2XE9svJ7ZfMWoOZLfO' \
			b'9kvDZ0AeGBOBHJOeAbKb2n5pQC9ffy+BPLBIgOzE9ivJYCGQ742/DgVkVbXeEKB5kyJqQDYpOjkiQ9VhbtyqKH6pWwTobKuim25VjGnmgN7mGNCZlwI67lbE7QBo2avoZK+ik72KMWoB6HXbFTV8DmhlTALoMeneDXc5rKebFodAVmKVsFZGKaxl02KSzTJY' \
			b'm8IS7DA7Kvasxd7hFKpDoHVnlfVekMkqajBxqqJ2o35a3qVuESYz9bSbqqcLKBaZTTK2BTkDDm1VHHzjojp69uwbZ9fBTlLOYadlT2A3ErFB+zyEsLMwk5cDzKzAbEx2x73BprDPuofXscCL9UxQBvgpvEYNk7xL3SJ4ZRom5zfDq8hskrEtyBng5Wfg5bfA' \
			b'a50SSVPO4aVlT+A1em6Cl4aYh5e8HOAlqqOY7K7wKqym7uF1LPBiS0Zo2dopvEYbRnmXukXwymwYXbsZXkVmk4xtQc4Ar3YGXu0WeK0zU9SUc3hp2RN4jURsgpeGmIeXvBzgJcaJMdld4WXvxHbbW62v4XPdMOPppzAcD3VzhVsEwz6DYT+d2I1p5nicyziG' \
			b'tqWX4rGvZs+gcXLGm8KSL2OxC3yuO+FNw+f4VKYk+ByJmtPS9FOYSkBM5/pZpCrRitRekBoz2BGp96dFnTpSPWtWwd16glQ/6lTlXeqWINVnOlU/1anGNDOklrlOKLAFXcMZwfU8Ur2oVL2oVL2oVDVmcV7wOn2qhs+QOjAlIjUSNYNUP9WnakCI9aw+dWCP' \
			b'INWLPjXJYEek3o3jom41Ulll6vkrEROkjspSeZe6RUjNlKV+qiyNaeZI3egYqZmXInXNuW5edKVedKVedKUas0DqOkWphs+RqkxJkDoSNYfUqYpUA0KsZ1WkA3sUqaIiTTLYEamhPI07tR90p2D9u69zVPlMf3o/OQE8BXXYk3HwruCuFwC8vQzIw4bDxMmh' \
			b'MsSiIT9V3I82DRImdVeyH0b8tB0YE5052Z/J9zMUeLFmyL06lqSVPsw1BmLS4MWkwYtJg0Yuj40DpWF6yH9i4zB7grmmlTcUyrapabH6zrUU0dgBdc+tRaiGE879rMUDDjofOKlNhlg9RPbkTQZ782+HX7QeLJUtXbjtaKuLw5/jv6dD/N0WCGfQLSDbb1Et' \
			b'bVIrtdX2z2vg7PnjOdN/v+f5u6uc6b/twxZbPmex9TMWi79fQUXJxb4+iOTj21buiD9i4ds1sp/L/Zy8b/mOzA19yKLRjSdH/DELsPgKH7ToC+EtB3r7Et5wJI33ooZ7W6Pd8Pac0xBmv19hBsNu5Osssu2tH4V6GM1mwk2M2zIgGacwe/zWWDf9lFgoPyW2' \
			b'RNx3nW7sONXYKPowbgv7b78Xfv/r0B8mauxopgEWrdpcE7AYCukRHeu/3rXrl7s2wELorS/Z1lPiO43P3T4/tUU1uOw7enserGwaqONLhTu1+c1+hD4R+Gv6+lZj59p5s2Utd78DF6go1g9edmzv147WXY/xOH/vx+wm3ntv6mlOGgZp99fS4C/QLW1s8KGI' \
			b'd9fb8N9Yow+5j2c/sLrWXlPjXy7aXKbxXxkohMEnc9lOgPBiLb7SyHixO+Nlj92Buy6MXBEfGFVe96BIsdFeUWW6qH+AXPp9YaHdpu8scNC6RTiAHo2xcBUMGC8fKjW1XG03QsLtBomwV0gkn2O+Np3Osc8Prh8KKQyaZGPUteh6FsLg6hAIhej73US/PYzo' \
			b'9/eifyyif+Ve4MhFvy1EP+wm+nuaL+Qzhfpe9I9F9M0tF/2uEP1rWbKF7n+w27j6CkCDU/nonTGHW8raeQl3f0J/UIFPp9r7WgHg9T5WodVLBf8KKwENf1B6l5lu6x5QZizl5QrtYaQc2iA3UQgdrmlfY2N0Kf3P9TXth9fzQDy6VNdz0CYdn3Ob0+9cRq9z' \
			b'VX1OX10cpenNgc0OJm11fZn22sK48KYF+CrNMovDoQwM0lYY5oRztqebRNSr/QwMZtRwpuv5Y9/1vcAua3KPo6m90gAia1YbPgnyGk0H1jSjUIj0NUtlcxCpbNYLps2slK9JPLceR7yrCaNjW4xjEVex5G43iSy/zm19F4vuJVvZLacD72C/iMOe+WBvLkbR' \
			b'3JoHhFiWZHMvyactyR3/b5Tk7rQluVNJ7jZLsq0u2iruG2tYcBsW2UReRVjbbNsVS9CM5EAyUmnoHNU0z2W7WK2NqqJQl42br8Ox/rhuQtwPxBOEGeaBOSlDgoN5DtXY7oWM4DMAnOw326HQAyRyGHDhWaguWfiGv1GgAhrGYLsxxJc8cSNb/BK22JIzzVFw' \
			b'p5lCeODQgMorcyks4VLZhEvjvVPLvQsjt7XIcy3xuEupvyqzQXHdl+2mvFrQVu5SK9tawZnWb/gwR91PW7m2qMMbmAGt3bF6IFXq+tnOjAjM967oh29uVjO7A3SvM5hSdMrO0jqaXssEprsXo81ihHo5vtlx+vkRdjciR4aaIyyw9A9WEKL6wUrapv5eqLYI' \
			b'1VGqXFKh6pnGIxIqyiYVqpvT+h2rXMEi72i1ecfQ70GImmMUomtahx7HzKGafgJsk1Bdu4q4NZdprswexQqJbRiI8wCy0u9rbfusFtWRCtzNL1fcpMytkzNUy0ksR6QN2OGWH3ZrxCwfSt4EnvvyJLbt+IXjM5E9ieIF5ubhzTndna34iF05lsXU+fErm89M' \
			b'4S1YMKEfTQjUKgw2HXJkCL78ib3m2LHbYgsXTDQHJ8eiuOw/McpRP4kG/SqlhHiwIotxULqVOXQxKN3L/DFx9tDEUQsx8wczkOSJNzsH3sg2CSUbkZlQd2hCqbEq/qDBl2s383b8YwL9oQn01fwflhjWvmv5HRMYDk1gqC71x8S1U+KK05b0FPLx9KTNJyZN' \
			b'j0vC9nXekmn0OKQgC2hzBZocq+uq8RgiPoJoOGrIp8cLvUFPKX8krm2VPKSunfnLgnCo+ThzYTJ/ZmN36Druqkv9MXH9YesYivC5aq67PVY1+oXDOaiUMy+MWC6TGHO8qQ/ehbpq304oTzp/LKO2exAZfEjmhqQmVOLkWzbj4+UdBsNXT2WtkzrYOHJxdjtC' \
			b'18oQuDeVIyxJzzvm4kZnujnfEH2lOPY2iRQmY6fkpAo2juJ2kahWPyq9q1xhwnoFN0w2N4aSovlbJV19dVJOqiBsGWDsLmDC7R3FbIZ/0JAMrkvul7pBwbElVKamYGa0t0keoW46JSdV0B2PPJrqJpywob9Vkmirk3KigqqPRxJddRNO2HCrJhVQuJ+Skyow' \
			b'J1AF43c7d66Krjo21wQilOaaG0NJldg9Nw79pomf26WN6Ks9OlTtjC/RvSaGcMXtpK3aH2PslDksc+sYhMW19a7f+HZ3129JU/jkj5lPrjoCJ3zaNjm5UT6F6gic8OmkVwLwhYdtTha75X+X8Hl0rGkPSeDrU+vCUcFjhsV7Yfa2GcpRMxtmBUfthMcHXvY4' \
			b'MI9tddxOVrG3zW+Om8euOm4nPG5Omse+Om4nPMbxrjCDaZXndnjW9zi7j1kCPyzUqPzjYLOkKhqOhHMoOz52rMZZjxIyzIb0VeIkYFsERBUgcKhS1wSN0CVWPFDRaxF6/lalyMRYt22DUNAjIKSPRlpdLdYeNX+Ny/OWHdktI1uMaqn3Xo1CSCabDsxoOlgN' \
			b'nf8/lorl2w=='

	_PARSER_TOP             = 'expr_commas'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	_VAR_TEX_XLAT = {
		r'\mathbb{R}'  : 'Reals',
		r'\mathbb{C}'  : 'Complexes',
		r'\mathbb{N}'  : 'Naturals',
		r'\mathbb{N}_0': 'Naturals0',
		r'\mathbb{Z}'  : 'Integers',
	}

	_UPARTIAL = '\u2202'
	_USUM     = '\u2211'
	_UINTG    = '\u222b'
	_LETTER   = fr'[a-zA-Z]'
	_LETTERU  = fr'[a-zA-Z_]'

	_TEXGREEK = '(?:' + '|'.join (reversed (sorted (f'\\\\{g}' for g in AST.Var.GREEK))) + ')'
	_TEXXLAT  = '(?:' + '|'.join (reversed (sorted (x.replace ('\\', '\\\\') for x in _VAR_TEX_XLAT))) + ')'
	_VARPY    = fr'(?:{_LETTER}(?:\w|\\_)*)'
	_VARTEX   = fr'(?:{_TEXGREEK}|{_TEXXLAT}|\\partial|(?:(?:\\overline|\\bar|\\widetilde|\\tilde)\s*)?\\infty)'
	_VARTEX1  = fr'(?:(\d)|({_LETTER})|({_VARTEX}))'
	_VARUNI   = fr'(?:{"|".join (AST.Var.UNI2PY)})'
	_VAR      = fr'(?:{_VARPY}|{_VARTEX}|{_VARUNI})'

	_STR      = r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY - {'@', '%'})))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LETTER})'),
		('LOG',           r'log\b|\\log(?!{_LETTER})'),
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LETTERU})|\$({_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LETTER}(?:\w|\\_)*)\s*}}'),
		('LIM',          fr'\\lim(?!{_LETTER})'),
		('SUM',          fr'\\sum(?:\s*\\limits)?(?!{_LETTER})|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?(?!{_LETTER})|{_UINTG}'),
		('LEFT',         fr'\\left(?!{_LETTER})'),
		('RIGHT',        fr'\\right(?!{_LETTER})'),
		('CDOT',         fr'\\cdot(?!{_LETTER})'),
		('TO',           fr'\\to(?!{_LETTER})'),
		('MAPSTO',       fr'\\mapsto(?!{_LETTER})'),
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
		('FRAC',          r'\\frac'),
		('IF',            r'if(?!{_LETTERU})'),
		('ELSE',          r'else(?!{_LETTERU})'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
		('VAR',          fr"(?:(\\partial\s?|{_UPARTIAL})({_VAR})|({_VAR}))('*)"),
		('ATTR',         fr'\.(?:({_LETTERU}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"(?<!{_LETTERU}|')({_STR})|\\text\s*{{\s*({_STR})\s*}}"),
		# ('PRIMES',        r"'+"),
		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
		('CARET1',       fr'\^{_VARTEX1}'),
		('CARET',         r'\^'),
		('DBLSTAR',       r'\*\*'),
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('CURLYL',        r'{'),
		('CURLYR',        r'}'),
		('BRACKL',        r'\['),
		('BRACKR',        r'\]'),
		('BAR',           r'\|'),
		('PLUS',          r'\+'),
		('MINUS',         r'-'),
		('STAR',          r'\*'),
		('INEQ',         fr'==|!=|\\neq?|<=|\\le|<|\\lt|>=|\\ge|>|\\gt|{"|".join (AST.Eq.UNI2PY)}'),
		('EQ',            r'='),
		('DIVIDE',        r'/'),
		('EXCL',          r'!'),
		('AMP',           r'&'),
		('COLON',         r':'),
		('DBLSLASH',      r'\\\\'),
		('COMMA',         r','),
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('ignore',        r'\\,|\\:|\\?\s+|\\text\s*{\s*[^}]*\s*}'),
	])

	def expr_commas_1   (self, expr_comma, COMMA):                              return expr_comma if expr_comma.is_comma else AST (',', (expr_comma,))
	def expr_commas_2   (self, expr_comma):                                     return expr_comma
	def expr_commas_3   (self):                                                 return AST (',', ())
	def expr_comma_1    (self, expr_comma, COMMA, expr):                        return AST.flatcat (',', expr_comma, expr)
	def expr_comma_2    (self, expr):                                           return expr

	def expr            (self, expr_eq):                                        return expr_eq

	def expr_eq_1       (self, expr_lambda1, EQ, expr_lambda2):                 return AST ('=', '=', expr_lambda1, expr_lambda2)
	def expr_eq_2       (self, expr_lambda):                                    return expr_lambda

	def expr_lambda_1   (self, expr_commas, COLON, expr_eq):                    return _expr_lambda (expr_commas, expr_eq)
	def expr_lambda_2   (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1   (self, expr_paren, MAPSTO, expr_eq):                    return _expr_mapsto (expr_paren, expr_eq)
	def expr_mapsto_2   (self, expr_piece):                                     return expr_piece

	def expr_piece_1     (self, expr_ineq, IF, expr, ELSE, expr_lambda):
		return \
				AST ('piece', ((expr_ineq, expr),) + expr_lambda.pieces) \
				if expr_lambda.is_piece else \
				AST ('piece', ((expr_ineq, expr), (expr_lambda, True)))

	def expr_piece_2     (self, expr_ineq, IF, expr):                           return AST ('piece', ((expr_ineq, expr),))
	def expr_piece_3     (self, expr_ineq):                                     return expr_ineq

	def expr_ineq_2     (self, expr_add1, INEQ, expr_add2):                     return AST ('=', AST.Eq.ANY2PY.get (INEQ.text, INEQ.text), expr_add1, expr_add2)
	def expr_ineq_3     (self, expr_add):                                       return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2      (self, expr_add, MINUS, expr_mul_exp):                  return AST.flatcat ('+', expr_add, expr_mul_exp.neg (stack = True))
	def expr_add_3      (self, expr_mul_exp):                                   return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_neg):                   return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_2  (self, expr_mul_exp, STAR, expr_neg):                   return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_3  (self, expr_neg):                                       return expr_neg

	def expr_neg_1      (self, MINUS, expr_neg):                                return expr_neg.neg (stack = True)
	def expr_neg_2      (self, expr_diff):                                      return expr_diff

	def expr_diff       (self, expr_div):                                       return _expr_diff (expr_div)

	def expr_div_1      (self, expr_div, DIVIDE, expr_mul_imp):                 return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2      (self, expr_div, DIVIDE, MINUS, expr_mul_imp):          return AST ('/', expr_div, expr_mul_imp.neg (stack = True))
	def expr_div_3      (self, expr_mul_imp):                                   return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_int):                         return _expr_mul_imp (expr_mul_imp, expr_int, self._USER_FUNCS)
	def expr_mul_imp_2  (self, expr_int):                                       return expr_int

	def expr_int_1      (self, INTG, expr_sub, expr_super, expr_add):           return _expr_int (expr_add, (expr_sub, expr_super))
	def expr_int_2      (self, INTG, expr_add):                                 return _expr_int (expr_add)
	def expr_int_3      (self, expr_lim):                                       return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                           return AST ('lim', expr_neg, expr_var, expr)
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):   return AST ('lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg):  return AST ('lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6      (self, expr_sum):                                                                         return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQ, expr, CURLYR, expr_super, expr_neg):               return AST ('sum', expr_neg, expr_var, expr, expr_super)
	def expr_sum_2      (self, expr_func):                                                                        return expr_func

	def expr_func_1     (self, SQRT, expr_func_arg):                            return _expr_func (1, 'sqrt', expr_func_arg)
	def expr_func_2     (self, SQRT, BRACKL, expr, BRACKR, expr_func_arg):      return _expr_func (1, 'sqrt', expr_func_arg, expr)
	def expr_func_3     (self, LOG, expr_func_arg):                             return _expr_func (1, 'log', expr_func_arg)
	def expr_func_4     (self, LOG, expr_sub, expr_func_arg):                   return _expr_func (1, 'log', expr_func_arg, expr_sub)
	def expr_func_5     (self, FUNC, expr_func_arg):                            return _expr_func_func (FUNC, expr_func_arg)
	def expr_func_6     (self, FUNC, expr_super, expr_func_arg):
		func = _FUNC_name (FUNC)

		return \
				AST ('^', _expr_func_func (FUNC, expr_func_arg), expr_super) \
				if expr_super.remove_curlys () != AST.NegOne or not AST ('func', func, ()).is_trigh_func_noninv else \
				_expr_func_func (f'a{func}', expr_func_arg)

	def expr_func_8     (self, expr_pow):                                       return expr_pow

	def expr_func_arg_1 (self, expr_func):                                      return expr_func
	def expr_func_arg_2 (self, MINUS, expr_func):                               return expr_func.neg (stack = True)

	def expr_pow_1      (self, expr_pow, expr_super):                           return AST ('^', expr_pow, expr_super)
	def expr_pow_2      (self, expr_fact):                                      return expr_fact

	def expr_fact_1     (self, expr_fact, EXCL):                                return AST ('!', expr_fact)
	def expr_fact_2     (self, expr_attr):                                      return expr_attr

	def expr_attr_1     (self, expr_attr, ATTR):                                return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1])
	def expr_attr_2     (self, expr_abs):                                       return expr_abs

	def expr_abs_1      (self, LEFT, BAR1, expr_commas, RIGHT, BAR2):           return AST ('|', expr_commas)
	def expr_abs_2      (self, BAR1, expr_commas, BAR2):                        return AST ('|', expr_commas)
	def expr_abs_3      (self, expr_paren):                                     return expr_paren

	def expr_paren_1    (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):       return AST ('(', expr_commas)
	def expr_paren_2    (self, PARENL, expr_commas, PARENR):                    return AST ('(', expr_commas)
	def expr_paren_3    (self, IGNORE_CURLY, CURLYL, expr, CURLYR):             return AST ('{', expr)
	def expr_paren_4    (self, expr_frac):                                      return expr_frac

	def expr_frac_1     (self, FRAC, expr_cases1, expr_cases2):                 return AST ('/', expr_cases1.remove_curlys (), expr_cases2.remove_curlys ())
	def expr_frac_2     (self, FRAC1, expr_cases):                              return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_cases.remove_curlys ())
	def expr_frac_3     (self, FRAC2):                                          return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4     (self, expr_cases):                                     return expr_cases

	def expr_cases_1    (self, BEG_CASES, expr_casess, END_CASES):              return AST ('piece', expr_casess) # translate this on the fly?
	def expr_cases_2    (self, expr_mat):                                       return expr_mat
	def expr_casess_1   (self, expr_casessp, DBLSLASH):                         return expr_casessp
	def expr_casess_2   (self, expr_casessp):                                   return expr_casessp
	def expr_casessp_1  (self, expr_casessp, DBLSLASH, expr_casessc):           return expr_casessp + (expr_casessc,)
	def expr_casessp_2  (self, expr_casessc):                                   return (expr_casessc,)
	def expr_casessc_1  (self, expr_commas1, AMP, expr_commas2):                return (expr_commas1, expr_commas2)
	def expr_casessc_2  (self, expr_commas, AMP):                               return (expr_commas, True)

	def expr_mat_1      (self, LEFT, BRACKL, BEG_MAT, expr_mat_rows, END_MAT, RIGHT, BRACKR):  return _expr_mat (expr_mat_rows) # translate these on the fly?
	def expr_mat_2      (self, BEG_MAT, expr_mat_rows, END_MAT):                               return _expr_mat (expr_mat_rows)
	def expr_mat_3      (self, BEG_BMAT, expr_mat_rows, END_BMAT):                             return _expr_mat (expr_mat_rows)
	def expr_mat_4      (self, BEG_VMAT, expr_mat_rows, END_VMAT):                             return _expr_mat (expr_mat_rows)
	def expr_mat_5      (self, BEG_PMAT, expr_mat_rows, END_PMAT):                             return _expr_mat (expr_mat_rows)
	def expr_mat_6      (self, expr_curly):                                                    return expr_curly
	def expr_mat_rows_1 (self, expr_mat_row, DBLSLASH):                         return expr_mat_row
	def expr_mat_rows_2 (self, expr_mat_row):                                   return expr_mat_row
	def expr_mat_rows_3 (self):                                                 return ()
	def expr_mat_row_1  (self, expr_mat_row, DBLSLASH, expr_mat_col):           return expr_mat_row + (expr_mat_col,)
	def expr_mat_row_2  (self, expr_mat_col):                                   return (expr_mat_col,)
	def expr_mat_col_1  (self, expr_mat_col, AMP, expr_commas):                 return expr_mat_col + (expr_commas,)
	def expr_mat_col_2  (self, expr_commas):                                    return (expr_commas,)

	def expr_curly_1    (self, CURLYL, expr_commas, CURLYR):                    return _expr_curly (expr_commas)
	def expr_curly_2    (self, expr_bracket):                                   return expr_bracket

	def expr_bracket_1  (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):       return AST ('[', expr_commas.commas if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_2  (self, BRACKL, expr_commas, BRACKR):                    return AST ('[', expr_commas.commas if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_3  (self, expr_term):                                      return expr_term

	def expr_term_1     (self, STR):                                            return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_2     (self, SUB):                                            return AST ('@', '_') # for last expression variable
	def expr_term_3     (self, expr_num):                                       return expr_num
	def expr_term_4     (self, expr_var):                                       return expr_var

	def expr_num        (self, NUM):                                            return AST ('#', NUM.text) if NUM.grp [0] or NUM.grp [2] else AST ('#', NUM.grp [1])
	def expr_var        (self, VAR):
		var = \
				'partial' + AST.Var.ANY2PY.get (VAR.grp [1], VAR.grp [1].replace ('\\_', '_')) \
				if VAR.grp [0] else \
				self._VAR_TEX_XLAT [VAR.grp [2]] \
				if VAR.grp [2] in self._VAR_TEX_XLAT else \
				AST.Var.ANY2PY.get (VAR.grp [2].replace (' ', ''), VAR.grp [2].replace ('\\_', '_'))

		return AST ('@', var + '_prime' * len (VAR.grp [3]))

	def expr_sub_1      (self, SUB, expr_frac):                                 return expr_frac
	def expr_sub_2      (self, SUB1):                                           return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1    (self, DBLSTAR, expr_func):                             return expr_func
	def expr_super_2    (self, DBLSTAR, MINUS, expr_func):                      return expr_func.neg (stack = True)
	def expr_super_3    (self, CARET, expr_frac):                               return expr_frac
	def expr_super_4    (self, CARET1):                                         return _ast_from_tok_digit_or_var (CARET1)

	def caret_or_dblstar_1 (self, DBLSTAR):                                     return '**'
	def caret_or_dblstar_2 (self, CARET):                                       return '^'

	#...............................................................................................
	_AUTOCOMPLETE_SUBSTITUTE = { # autocomplete means autocomplete AST tree so it can be rendered, not necessarily expression
		'CARET1'             : 'CARET',
		'SUB1'               : 'SUB',
		'FRAC2'              : 'FRAC',
		'FRAC1'              : 'FRAC',
		'expr_super'         : 'CARET',
		'caret_or_doublestar': 'CARET',
	}

	_AUTOCOMPLETE_CONTINUE = {
		'RIGHT' : ' \\right',
		'COMMA' : ',',
		'PARENL': '(',
		'PARENR': ')',
		'CURLYR': '}',
		'BRACKR': ']',
		'BAR'   : '|',
	}

	def _insert_symbol (self, sym, tokinc = 0):
		tokidx       = self.tokidx
		self.tokidx += tokinc

		for sym in ((sym,) if isinstance (sym, str) else sym):
			if sym in self.TOKENS:
				self.tokens.insert (tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

				if self.autocompleting:
					if sym in self._AUTOCOMPLETE_CONTINUE:
						self.autocomplete.append (self._AUTOCOMPLETE_CONTINUE [sym])
					else:
						self.autocompleting = False

			else:
				self.tokens.insert (tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, ('', '', '', '')))
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

		if self.stack [idx].sym != 'CURLYL':
			if self.tokens [self.tokidx - 1] == 'COMMA':
				self._mark_error ()

			if self.stack [idx - 1].sym == 'LEFT':
				return self._insert_symbol ('RIGHT')

			return self._insert_symbol ('PARENR' if self.stack [idx].sym == 'PARENL' else 'BRACKR')

		# vector or matrix potentially being entered
		if self.stack [idx - 1].sym == 'CURLYL':
			if self.stack [-1].red.is_null_var:
				return self._mark_error (('CURLYR', 'CURLYR'))
			elif not self.stack [-1].red.is_comma:
				return self._insert_symbol (('COMMA', 'CURLYR', 'COMMA', 'CURLYR'), 1)
			elif len (self.stack [-1].red.commas) == 1 or self.tokens [self.tokidx - 1] != 'COMMA':
				return self._insert_symbol (('CURLYR', 'COMMA', 'CURLYR'))
			else:
				return self._mark_error (('CURLYR', 'CURLYR'))

		if self.stack [-3].sym != 'COMMA' or self.stack [-4].sym != 'expr_comma' or self.stack [-5].sym != 'CURLYL':
			if self.stack [-1].red.is_vec:
				return self._insert_symbol (('COMMA', 'CURLYR'), 1)
			elif self.stack [-1].red.is_comma:
				if len (self.stack [-1].red.commas) == 1 or self.tokens [self.tokidx - 1] != 'COMMA':
					return self._insert_symbol ('CURLYR')
				else:
					return self._mark_error ('CURLYR')

		else:
			cols = \
					len (self.stack [-4].red.vec)             if self.stack [-4].red.is_vec else \
					len (self.stack [-4].red.commas [0].vec)  if self.stack [-4].red.is_comma and self.stack [-4].red.commas [0].is_vec else \
					None

			if cols is not None:
				vec             = self.stack [-1].red.commas if self.stack [-1].red.is_comma else (self.stack [-1].red,)
				self.stack [-1] = lalr1.State (self.stack [-1].idx, self.stack [-1].sym, AST (',', vec + (AST.VarNull,) * (cols - len (vec))))

				return self._mark_error (('CURLYR', 'CURLYR')) if len (vec) != cols else self._insert_symbol (('CURLYR', 'CURLYR'))

		return self._insert_symbol ('CURLYR')

	def _parse_autocomplete_expr_int (self):
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

		if pos == 1 and rule == ('expr_func', ('FUNC', 'expr_func_arg')):
			return self._insert_symbol (('PARENL', 'PARENR'))

		if pos and rule [1] [pos - 1] == 'expr_commas':
			return self._parse_autocomplete_expr_commas (rule, pos)

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_int': # TODO: Fix this!
				return self._parse_autocomplete_expr_int ()

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

		lalr1.Parser.parse (self, text)

		if not self.parse_results:
			return (None, 0, [])

		rated = sorted ((r is None, -e if e is not None else float ('-inf'), len (a), i, (r, e, a)) \
				for i, (r, e, a) in enumerate (self.parse_results))

		if os.environ.get ('SYMPAD_DEBUG'):
			rated = list (rated)
			print (file = sys.stderr)
			for res in rated:
				res = res [-1]
				res = (res [0].remove_curlys (),) + res [1:] if isinstance (res [0], AST) else res
				print ('parse:', res, file = sys.stderr)
			print (file = sys.stderr)

		res = next (iter (rated)) [-1]

		return (res [0].remove_curlys (),) + res [1:] if isinstance (res [0], AST) else res

class sparser: # for single script
	Parser = Parser

_RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
	p = Parser ()
	a = p.parse (r"\int 2x*-dx")
	print (a)
