# Builds expression tree from text, nodes are nested AST tuples.
#
# Time and interest permitting:
# sets
# assumptions/hints
# importing modules to allow custom code execution
# Proper implementation of vectors with "<b>\vec{x}</b>" and "<b>\hat{i}</b>" variables
# sympy function/variable module prefix
# systems of equations, ODEs, graphical plots (using matplotlib?)...

# TODO: Matrix xlat convert column matrix to vector.
# TODO: multiple vector weirdness
# TODO: user_func**exp (args...)?
# TODO: _xlat_func_Integral multiple integrals

import ast as py_ast
from collections import OrderedDict
import os
import re

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
					(AST ('*', neg (ast.muls [:-1])), dv) \
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
			b'eJztXWuP3LaS/TMLZAZQAxJfkvzNdpxcY/3ItZ1gF4PAcBxnEWycZG3n7i4W979vnaqiRJHqntZM97i73RhOS6Qoslisw0exSF1cffXw+ZPnz76qvvqXd7//TJcnj755RZfv7r949OwJ3Tz+9tnzF49eP/z+xZN/J+83L+4/1EujV0PXB4++ff3w/stHL/X+' \
			b'6f1XevdgvP1hvP1ObjlV5PL08bPv+V1K718R8PLVC/x+/4B+n33/lH5/uI+Qx89efQsqHz/lx/z79xdI68lzPPjm+2eg7wFHfvj86dP7sTAvYn64uf/0u5gbvF8/ePLyyf2Xf6PbR8++Vupx92C8/WG8VepfPP72bzEoFv7R3/Hz5OUjTfWVEEIEIObT+9+9' \
			b'fPUc+b/i8j36t4dP4mOw8+vHPzz+Gq8+/Pr5K+aCFpqT/e4J8+jxN7h/8fgpZ8jJEZ/w+ts3H959ev3Hh9c///Tbx09vPlDQu//588Prj3/9+W7w/PLX729fv/nwH+PDn+Lt+zefXr/947fU++GP/868H6P/7ZuP7z5+fDv1/jn1Rt+bn8bbT59GWt68/RTv' \
			b'/xxzAokjee/j7W+/Dre//o73/jEW8f1fv73+9f2Qe/Lk9zGBn3/9R7z99O5DEvzLL/H+pw9v3v7nu4Go398NfHr714ff/jfNjm4S1gzF+/nnCQtGit/911A+ymQo9q/v3r4bPFSBv4+J/vnx0x9D4d+8/+nnN9E3pDXk9cf7928mno9f/VhdXaycqVxzWcmN' \
			b'wY2tVo6vprowlQnVqqlsSzeXQyiHjQGrFjeNkR/f0FN3mQY1Lg3CLV5s5MfJA7qjtDhKi4wbrxnb5jKGatgQsGp6vqOUOnrbVra71IBVYzlVix9XUcrqJR/fecSrbE0xLycB4nPxPXrBxyDc0p3hf0P520vxrzizRsOFhmplNFD8lH5jmXF9DKAy8B0Rb2pO' \
			b'qZYfR2kbTXwMAhvHUNyi3ujfV7avVkKmww3IreXHKfX0guWK7qsL5AwWSckpICSeVi4IQEYdVQZEQviiXtBO3G6m4a7wgqw0yJfeSRorwxXqULpO7y642FqxtcoYqs3EINzifeIw+MKZNkOEGDx6VyS6zDXUTg1xF++Kg0m6L0xTkXihugxlhoJQrVESIvJr' \
			b'YgBCvtkyIhVqGnFlmPH0xqqtnI1U0QNmBCUgoKCXbKgg6yM06FkMHgLAF4S4MaSRED+GGAkJMYSEkoWlk58EHR3ucNPKDwNDKsW2fIu7EB9eqpd88YHk4eTHdUPZh6A+DcItGGPlh6rt8nK8RZwgkhFfgQgzEWA433AzYmPzJbRSmGBw8DquGxtRSWVhEexE' \
			b'tDyKWUEeJf80WAPIz9n28kOid6l+Ah0Xnp40nK76vLQioM8kwgG5FTlj6VXJaAcoUEuCB0q6ehNwcIiJ+ZDPMQubvmqGm1ZviEvDnYCHGzVXeW1fKB3DDSWFUStLfcVVXRF2SFKJJKoGCicZpB9f+VD5tgqmCrbqfNWFqmurrqu6vurrqif+dygccZGIIoR4' \
			b'FmSqMYpF8hxcFXwVQhUoka4K1AS1VdtVbU/VBH50puqozTFgFJWXpLKpyVOTrybqao+WiASSQNHBH+ifkq6rjvhTd1QmAM8ToXRP+dVVaKo+VD0BzQBrjqTPE7vQyJJk9qbqqWwBckOVTbiht6uA/pJ8xBQqcAOWoAWD3wS5WA5GywcvfBTHqs/LQ+IUBxO7' \
			b'ECwpXQSN3EmCQd5pJI7T3DrO5kuvhItOOUh0ndlB7OhUdHoWll5ElEooQmP5sZStLJUUZihGXoaEdCL6R2lxWKj7naZaS6q+EXiJ2HM1X3RajoaRgdaSEqcGnOJQRuc26aIJwjyp/la41ka2dcxLoZaIHIliSnZExYTDKWN3JCBXGDmfsY5eg1HQuqr1VUsF' \
			b'MFVrq7au2ubMnIsQzsxZz5z2zJz1zOnOzFnXvwTtWORi5NJZGaA6HQ7IoMNK/22NDGqZYsSqNXatw9ra62sS3vHbR9IXXXRaZg7l0rRS3K5Rvw7IvJTOc/zeVb3Xyh+q+si75Quv9eg7KanIRqh1TiP86IVNvY7anc5pmDk05/f1QZWJCBQhdX4kUCrvwMgU' \
			b'tro2IZPIoTRqtBXNoZErItJz7U8IxdNeoGLjvNq2CiVtSHTW4c+DQHCHimouJ8UeeCLlF87Mc+GE+IBSi9oF7LgpQ06GHVR+4sMuBEI4eax8oCKf4SG6RHNuLq+gTDWiTD2zAz3xmQ2qTDepKp8Keu5FRKs+5UvPfirmmT2iTjc7U3xfTRZ6aKBrmdmsCKfr' \
			b'ac0Wry4YYadTnO6UioP1FRa9RqdeMl8zjS5pGlV6qBYoWwdtuWqPnAVXWDU5/mJgyYdrUpqWmRXlH2XZWZZVksYeqwv8ZiuRW3m1NbGWZZbe1tHfpFIA9TsSC61cOknLclMGnSBYe1yMrGXgWAdtlZlbhfLCy/hyulzZR1Un82wf1PWj8s2I8s2I8s2gMnqp' \
			b'DBdlQSpaltHs2HNLdy499xcz+LtwvbKOm7GDkjnntMIYioenH4XeUQhsD5NAgp6qGvtDq1ysGdT7ag6g8lUNqxFVqrRd2nRN2nmvzT9drRoq8dDfstdEeyM0Dng8MWBi/Ur6FjHNpmOBIG+dV6o3zCIaM+WZS72YmtpLmZIm9YGZmVVDHyszsvSp1afEGFv0' \
			b'RpJQYRsyE4pxoNVxoJEBIOY7Z1MbqTfpZE191qH8yJJjRXKsjC0U91bHkEYGj5glnXHP8tOeBSfITMHKTMHKTMHqTMEemzXAFSY29sgmNjyTsaemX8KUy+iEyMqEyMqEiC75EDHMBLrJ8AeTAyN2AFbW2bnT1Vltzx3BQRUfY0se5AmKiKJLGY25S53Z/8jz' \
			b'f8cW5fglWpwOKNx54RBDHas6rsngrJXB2qj2qKfPrfD0yNotItQV40Qi2gl0nEDHqS7BqRLBHeKUD2hUmfcq8z6ORETmPcu8V2H3M5MaVJeU3EvJ/Xm1g9vJMx/YWM2LDjVoBxNEVoLISojdRkWDXOVbSLoSerHVF9uj1y9foeCtFLxlfMmSgO5CCHiW6UhR' \
			b'8E441smLncbtToMd/QkUgyg7/mJApno1Ra3VFrW+lJ17VzXgSa2ZUIJWCJQNSQdsLVJNB28wIviOUzWmI+WLtIlSwrQkyg7PjOgTxnHrmbJPGtCszDRPpkaQON5xs0ZsIj7CAJV5zVq+gQdeCg7zSBQD5UBBwEuUBkt5KBIW7bBih8U8LORhnyKaJuxexNZF' \
			b'Kl6DzXRgNFpZmHHDhhvm2egn0UnCNBNVie1k2PyFLVu8/ZTiwZYXVrMwmcUWLm7oKQyWzzARxpZHmAhjkyPWobBPAxb3sCzHqArLTVhraikc2iioomBujhEV2nLsYUJFYykLeyBhRAolLwbhdU2Vi12yHrvHsY1atlgTzSvKF/unA7bXtvJP7Fz1Tdx2TlGM' \
			b'hGP7cD9GS/+JylWLZ/TfYfMwMsDG6BpHGdQIqbEPufZ8BMGqYw/ywi5e6odWHlvLyUP1t8LG5x70tbIHf8jJz+bOpRouvHmYbokhVDCIEjxMC9HvndLjtFDYUe2wKR97o2sQIPu9eQezvOzBMT4UgVI0SXacsrITG/N7bCfHC5QMylbx+QWR0hb/CKOkQhIe' \
			b'wH5ccTxDI6lh777Dzn9siebt06gHSrJN88b+cpKhVQ+ue0kV29UpgS6pKGyUZxJBPxIHqeAFxQkkGv/n+3uISFi4twI8unu8o7mhYIi1qTnYaHDLwf+ENgvNRdZYZM2EtBG3bxR6YF4AX0J9E8xzePtroJxDOIfuJtjmUE1hajbAcgMm57CoONwz5rwcEiEw' \
			b'WgOgTeDJYSNIWYuSHB05KjYhIsdBggHI/ozM81iMhLdNejfuXHXv7NC72dt1cC4R51rH91t1diEO95u4KuRY/VRHEJgJDiBSk17PKSSGbp/+SQx5lJFBhHu7CIv+dj0bNlzwISzdDFTCTC8XIWPne7hJ74ZGpVUIUTzsmUETMIETqpfmTT0jp60ZOHypqz4i' \
			b'hxLrh78lMAIWChQhMAESxobsckT1M3+tnMQyvKNvCub4LoEdIveegdcz9DgTJ5eg77Z1icR+xB5wN2COi5/hTlgyYm8kqi+7pc5McCgUUZVz9KJP4qQVjxxxknraH1n0MCTd1B2xNDt/D20ASQtdzT95XZXB2yfwDQcE3HnUmtsA95RBi94igIeozVo6Pe3w' \
			b'+OQiRq08S90S6HKyOXS5lxqhOyacQbfMekKGLYgDggODmD1F36kw5qx6uTi5hJhCDmJOaA7F+izDceTQiOSRuBkkS44DkjUiBKGeg3Jkk4CZo04ymAHzDIhd3gMfPoTP+J3Fb8OijiJOwdsM4G1ytwi8zRx4myl4h4Rz8G50DN4sSLpfvluL3EaQ2whyG0Gu' \
			b'vF4gt1mHXImfI1fZkyB3oGwOuc0UuRIRItDMIld5pMhtBLljBtsh139JyD31ITNmX4GnP36KXj+g1+duEXr9HHr9FL1Dwjl6i6wnZNiCuIheP0Uv/BG7XrDrBbtesDu8X8DXr4OvxM/hq/xJ4DsEzsHXT+ErEVkGZuGrTFL4eoHvmMGyUXQ4w/iEYMxKI+gv' \
			b'2imMB82tPEvdIhi3czBupzAeEs5hXGQ9IcMWxEUYtxmM2xHGorzlizxwIXm/gHG7DsYSP4ex8ieB8ZD0HIzbKYwlImSgnYWxMklh3AqMxwyWwbg9w/iEYNyx3OPVKYy7AcZd7hbBuJuD8VQZPCacw7jIekKGLYiLMM6WYOCPMO4Exp3AuBMYD+8XMO7WwVji' \
			b'5zBW/iQwHpKeg/FUsawRIQPdLIyVSQrjTmA8ZrAMxt1ZIX2CeDas20L9iWLLiE7aiE7aDOotiZG6Jag2c+otM1VvjQlnqC6zzimxBX0KbJOpt8yoozai3DKi3DKi3Brfz4Ft1um3NH4G7MiiEdhj0jPANlP9lkbEXsVZ/VbkkwDbiH4ryWAZsPszsE8R2Dxt' \
			b'RoXJtFkP6pfj+/miwPa5WwTsucmzmU6ex4RzYBdZowompNiCwIjsbAJtxgm0kQm0kQm0kQn0+H6B7HUTaI2fI1t5lCB7CJxD9nQCrRG9lfglspVRimyZQCcZLEN2U5+hfYrQDowAdgztINAOAu0wQDvkbhG0wxy0wxTaQ8I5tIusc0psQV9EdmbOAX9EdhBk' \
			b'B0F2EGQP7xfIDuuQLfFzZCuLEmQPSc8hO0yRLRGB7DCLbOWTIjsIsscMFiK7OSP7FJHNSjJUlSjJ2DyukUtdjUaOEiN1i5A9pyozU1XZmHCO7CLrnBJb0BeRnWnLzKgtU1NHI9oyI9qy8f0C2eu0ZRo/R7ayKEH2kPQcsqfaMo0IZM9qyyKfFNmiLUsyWIjs' \
			b's+HXSSKb9WaoJ9GbGVGd8aXmiyK7y90iZM9pz8xUezYmnCO7yDqnxBb0RWRnCjQzKtCMKNCMKNCMKNDG9wtkr1Ogafwc2cqiBNlD0nPInirQNCKQPatAi3xSZIsCLclgIbLtiOzmRMCdnFV9xngjymQDRuIeX/UxDHO+cIMeleQmd4uU5HOGns3U0HNMOFeS' \
			b'F1nnlNiCvqgnz0w+4Qc3eLm6Fn25mF03YvvZiO3nmE6hLzdr4K7xc325sirRlw9Jz+nLpwagGhFyMWsBGvml+nKxAU0yWAj3efuxyeako1z6uon52C13JK2F9Q4gDZTiu1v46NbmLtxyV8fbZdOlL5ySYof+2+bu9hshkMjEDtQN/0UfXmQ/IcUWBEZku2TW' \
			b'3WbWZPzt0F6NQJ1agTpuVMv+204AjaTGLlxyzLtw5dJ0QwWCZhA96b0tb61olaqZ7ltSjt03yQRSxOYR6cgHHkyQ3Yd7spRf09Uykn1pzn2Y/Xa9D9PuU++2ed8Zb4N3cDw6dzI6dzI6dwO6Xe4Wjc7dHLhdBm4TU86hXeSduaAAzwjsWEzQcrlskO5GhDsZ' \
			b'pDsZpAvGxyQKkLt1g3SJnyNcOZUM0oek5wbpbgpzieitxC9RrgQrymUzVZLBwl67MDo7TKSfp9+LMG55NQxVIqthVlbDrKyG2WE1TGKkbgnA7dxqmJ2uho0JZ/gus84psQV92nvbbDHMjothVhbDrCyGWVkMG9/PkW3XLYZp/AzZkUUjssekZ5Btp4thGhEH' \
			b'Wc0uhkU+CbKtLIYlGSxEdmGHtj9kxxMUzvi+K3zzkhh/B13wLUtiVpbE7LAkZkPuFuF7bkmsF8U5xBdfS4N4A+ZcP7ZcGSspyAmyBZkR5tnKmB1XxqysjFlZGbOyMja+X8B83cqYxs9hrpxKYD4kPQfz6cqYRvRW4pcwl+cR5rIylmSwEOZnO7VTBLhjOzXU' \
			b'gdipObFTc2Kn5gY7NfGkbgnA3ZydmpvaqY0JZ8gus84psQV9imyX2am50U7NiZ2aEzs1J3Zq4/s5st06OzWNnyE7smhE9pj0DLLd1E5NI+IYulk7tcgnQbYTO7Ukg4XIPhuq7RnZqsf9TAjnSSqqQNRruKBarCB80LBJjNQtQvicgs1NFWxjwjnCi6xzSmxB' \
			b'X0S4zRA+qtecqNf4Ig9cSN4vEG7XIVzi5whXFiUIH5LuXbzLcW6nONdI+laJc+WW4twKzsdsluHcFFZr+9swsmtl+VZne+0DvltrxncCVdaYgZFuogl3g6JMnqVuEUjnFGVuqigrsFnkOMndFjRFYGZasVU8Pci5auMBQm6dEkyTz3GoXEhwOFCyQckdY8zj' \
			b'Th5G3Inqa0x2y93SprAlO+PtwPDGs1vHboK3YV7rQu4W4W1uXuvCZrwVOU5ytwVNEW9hHd7CNXhbN2fV5HO8KRcSvA2UbMKbxpjHmzyMeJOZ6pjstngrLLzOeDswvLGxFvR33RRvg5mWPEvdIrzNmWm5bjPeihwnuduCpoi3bh3eumvwts4SS5PP8aZcSPA2' \
			b'ULIJbxpjHm/yMOJN7K/GZLfFm/2SNiCfshLIsxIITK4nuPSD+keepW4JLv2c+sdP1T9jwhlAy6wnZNiCuHgEbD0HUJ0betH+eNH+eNH+6OvFcbDrVD8aPwNsZM8I2JGyGdWPn6p+NCLkfFb1E3kk0PWi+kky2BK65zO4TgW6fAaX548ITKA7nMElz1K3CLpz' \
			b'Z3D56RlcY8I5dDc6hm4WpNDddAaXlzO4vJzB5eUMLn29gO66M7g0fg5dZU8C3YGyOehOz+DSiJDz2TO4Io8UunIGV5LBltD9og7hOmnoiqwbuAl0B2tmeZa6RdCds2b2U2vmMeEcukXWEzJsQVyErtkEXTFi9mLE7MWIWV8voLvOglnj59BV9iTQHSibg+7U' \
			b'glkjQs5nLZgjjxS6YueYZLAldEN5cHpq++iOxJR5lwfa8nmImOvS8+Gw9hTl3Y4snbdFu9ke8cV3GLZCfbvh3HcIVws3dwC8H7YpSpzU3d4Y2k/3KY4pz3yVgcvgZ8jwsk0xD4KpJKu2fbupdZC9il72KnrZq6gplKfzYdIaph9oSDYvzh42r2nlLYcycGon' \
			b'raFzTce4ixFSwM1HW8XD6P3sVkacSR/ZqW2IbGcceZS3IRzMv3yP5gSXAB83Jm11dSffYNjhBxjCNZjOsZxh+Nrvp2zQVQ0fY6Bna7+VAv4f2PcY9vAtBneb7zFc95WSa75NAunf+E2SxR8joaLkOKj3BQV0k/7Av0iCrzvd4qsk63qmtV8IuquvkjRH8mUS' \
			b'MPsWXyfpC2kux4Y7lOb2kJr3JU37dc26bEo6Iulu9yDdDRdt1xK+hXTLMLgZpDwOhTNpJxZeM4YZpkG7/dZcP/2UXDv/Kbkl8r/tlGXL6cpGLGAY2O2+hV/4/bc7+Q5VM27GAJ9W7axmcDE20nNO1n+9bdsvt23AiRBd37A3oMS3GuO7HX9qjapq+YcVdz2+' \
			b'2TTYb7bsFexuUJAg4C6/vgbe3PAThrsd60ADsn68027XI4R1I37fYEzPn3cy28n7PjqDgE8sq/iHO+sSFmiwNnYJsNgOd9s1fN5uAXNIM3YNWIa1d9k9lOu+N+keVgaFBsfMTbsJApD1+I4nA8huDaDddhj+LkFzW8DUdz+OUrC0y+wHd9CDIDO/U3C0YWlv' \
			b'gsMqFgCj4Rza24HCePm2rTFydfWAEbcdRsKuMRIBQnTfrebowOcYnwkbKS7Am7vXKC3Exe0xEQos+O2w0O4LC8SoMxYODQv2S8BCW2AhbIeF3c05ciw0ZywcHBbcl4CFrsDCXS0uYw0impzsaCUCJzFipdDtb41t68Xm3aFg/whIJ/E7XYmQJcmGbWv2s+Y2' \
			b'p39qmEvbTJ9bGhYFXku25Vry3sQeOic/UTvtt/FfZy91Ey3T3TX+d6RNQjpdqlHaf6OPD/7NaZFuoj26rdaor64O2YxozxYTk9bc3KRFt7CePAiJvnXDjYLcSTsNq8kZK6FQb5BZL7ZAbBOkRkBdz5+Ur88SfKNG+YAa49uPObKGFza8d2r1sKahxfC6r1lM' \
			b'm32JqdkoqT430r4jeb32aOltDTYDW5MclPyyNTv9XyfDHCc3dV4syzdsh6856XkLa00c4c2ntnMxigbZ3iMcs2ibs2ifjGjz2Vj19aLNwnq8oo2MIdpM2AbRttVVW4077RqW5IZlOBFglV4LEe1T5UOvEjUjSZCUVDq6QDWPWki2g3EVB63bxs3X6VCfXJeo' \
			b'K+4/0w1UPOmYYSaYlTIoOJgeEXWLCj2iU3DZ6oa9LZgQIVNsqAMzWN5uw4yGY6kAB+WLvrAdg3zJIzewyS9kk5vllD0cbmWQn3AsovjWXAsLuVb2AUPrv13Tvw1nr2vSZzd9xpF1sxvuN/xfNLwhNrjNksZ2m2q6rhmdaT51pEvETJvJtqjUzzfrWrtJeE8a' \
			b'3/UzrBmZmO+ve3MYM6nZTbc7nTWVslR2v9bRHF8mTd1ZrraSq/bAp+jp52t6pvZzCBYMgrjy7q1QX+ST1qs/S9lWUoaKPxIpw3b1+qCkjLJJpeyzKycPVdDa41A6HkJXCalqDliq7mjJfTh/oaumX53bJGX280kZ572427Q7lLN2o5hhB+X4SbfrvuRGtaYS' \
			b'eDDrLp9TCNcJXki60iNZV0mbuP2to2zXzNnqivUBxFD+4GDdcbDTYNa6tTwRH1VhPG3u5H3PJ2x7xMAndulturtY8THNcgqPqfPTdjafj8O74rBnIZpXRJs6IEiOhsH3a3FqALZad9hZBwvw6OT4mzD9Ty2YNExeg4hRvngPeY/voHQrs+9iULo3+WPi7L6J' \
			b'o5Zl5g8mMomPd6h3vLdwEkt2jzOhbt+Euqr8w8oEXynLuef6xwT6fRNIbe7sH5ZO1j5r+RkTGPZNIEW9yR8T106JKw7XkuPsx5OyNp+ONT0aC60+75J1euxVJ4uEcwWaHMEckuOmbHKkVJseI/Ujelj5oz6irRJP6tqZvywKx5p/Zy5OFs5s7PZdx9Q63uSP' \
			b'iev3W8f6MdGimpt6h1WNUcz+nOuKIN/eLDHmeFPvvQt11a6dUJ50/uiL2x2IDL5V9JmkJlTi5HNJg/fmDqPn26ey1kkdbBy5yFFwmxG6VobAvakcYWo475iLGx2mEWVoO4ZKcewpiRQmccfkpAo2juK2kShh9fZyhYnuLVycnW6MJUXzJyVdfXVUTqogXDPA' \
			b'2F7AhNtbitkM/6BZiY4ipN5FLmpEromV6TWYGe0pySPUVMfkpAq6w5FHU30OJ2zoT0oSbXVUTlRQ9eFIoqs+hxM2nNSkAt3CMTmpAnMEVTB8FnbrquiqQ3MN5pnElo2xpErsjhuHftPEL2zTRvTVDh2qdiY0rH1DuOJOUVCxHnN8TirEb6c+3Jmk+qm0grfr' \
			b'+WqqDa63m55u79J05tIUPl03C/qsfPLVATjh05ZLDp+HT211AE74dN0s5qCXZvCd8eucmCvI/zbx89dhlRCT8H59PCr1mGHxXJi95zWS/TIbxiEH7WTJ+7rJ0GHz2FWH7YTHzVHz2FeH7YTH5qh5HKrDdsJjnNsKQ7FWee6iX5/jnD6oaR3C0LNrPJxZllQF' \
			b'8Q2L557PmKxxolgjtlMrPtGpjBmqxEnEroiIKkDktkpdE6Tj5tNDolkVjPEkHRzJMMjEULctjLfEdk/t9qKdXSfDSmyRl+1eXI28Zsc7o4xUfK9mOiSUTQduNB3suC7/HzBzWjc='

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
		('VAR',          fr'(\\partial\s?|{_UPARTIAL})({_VAR})|{_VAR}'),
		('ATTR',         fr'\.(?:({_LETTERU}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"(?<!{_LETTERU}|')({_STR})|\\text\s*{{\s*({_STR})\s*}}"),
		('PRIMES',        r"'+"),
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

	def expr_var_1      (self, var, PRIMES):                                    return AST ('@', var + PRIMES.text.replace ("'", '_prime'))
	def expr_var_2      (self, var):                                            return AST ('@', var)
	def var             (self, VAR):
		return \
				'partial' + AST.Var.ANY2PY.get (VAR.grp [1], VAR.grp [1].replace ('\\_', '_')) \
				if VAR.grp [0] else \
				self._VAR_TEX_XLAT [VAR.text] \
				if VAR.text in self._VAR_TEX_XLAT else \
				AST.Var.ANY2PY.get (VAR.text.replace (' ', ''), VAR.text.replace ('\\_', '_'))

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
			print ()
			for res in rated:
				res = res [-1]
				res = (res [0].remove_curlys (),) + res [1:] if isinstance (res [0], AST) else res
				print ('parse:', res)
			print ()

		res = next (iter (rated)) [-1]

		return (res [0].remove_curlys (),) + res [1:] if isinstance (res [0], AST) else res

class sparser: # for single script
	Parser = Parser

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
# 	p = Parser ()
# 	a = p.parse (r"Integral(x, 1, x)")
# 	print (a)
