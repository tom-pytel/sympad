# Builds expression tree from text, nodes are nested AST tuples.
#
# Time and interest permitting:
# sets
# var assumptions
# importing modules to allow custom code execution
# Proper implementation of vectors with "<b>\vec{x}</b>" and "<b>\hat{i}</b>" variables
# sympy function/variable module prefix
# systems of equations, ODEs, graphical plots (using matplotlib?)...

# TODO: Matrix(2, 2, lambda a, b: 1 if a == b else 0)
# TODO: indexing
# TODO: change func xlat to work with python tupler args instead of AST commas tuple
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
			elif arg.is_attr and arg.obj.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg.obj)))

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

		if not d:
			raise SyntaxError ('expecting variable')
		elif commas and commas [-1].is_num:
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

	if commas and commas [-1].is_null_var:
		return ast

	raise lalr1.Incomplete (ast)

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
	'Abs'       : (1, lambda expr: _expr_func (1, '|', expr, strip = 1)),
	'abs'       : (1, lambda expr: _expr_func (1, '|', expr, strip = 1)),
	'Derivative': (0, lambda expr: _expr_func_xlat (_xlat_func_Derivative, expr)),
	'diff'      : (0, lambda expr: _expr_func_xlat (_xlat_func_Derivative, expr)),
	'exp'       : (1, lambda expr: _expr_func (2, '^', AST.E, expr, strip = 1)),
	'factorial' : (1, lambda expr: _expr_func (1, '!', expr, strip = 1)),
	# 'Gamma'     : (1, lambda expr: _expr_func (2, 'func', 'gamma', expr, strip = 1)),
	'Integral'  : (0, lambda expr: _expr_func_xlat (_xlat_func_Integral, expr)),
	'integrate' : (0, lambda expr: _expr_func_xlat (_xlat_func_Integral, expr)),
	'Limit'     : (0, lambda expr: _expr_func_xlat (_xlat_func_Limit, expr)),
	'limit'     : (0, lambda expr: _expr_func_xlat (_xlat_func_Limit, expr)),
	'Matrix'    : (0, lambda expr: _expr_func_xlat (_xlat_func_Matrix, expr)),
	'ln'        : (1, lambda expr: _expr_func (1, 'log', expr)),
	'Piecewise' : (0, lambda expr: _expr_func_xlat (_xlat_func_Piecewise, expr)),
	'Pow'       : (0, lambda expr: _expr_func_xlat (_xlat_func_Pow, expr)),
	'pow'       : (0, lambda expr: _expr_func_xlat (_xlat_func_Pow, expr)),
	'Sum'       : (0, lambda expr: _expr_func_xlat (_xlat_func_Sum, expr)),
}

def _expr_func_func (FUNC, expr_neg_func):
	func        = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC
	paren, xlat = _FUNC_AST_XLAT.get (func, (None, None))
	ast         = _expr_func (2, 'func', func, expr_neg_func)

	if not xlat:
		return ast

	args = ast.args if ast.is_func else ast [1].args
	# arg  = args [0] if len (args) == 1 else AST (',', args)
	# ast2 = xlat (AST ('(', arg))

	# return ast2 if ast.is_func else AST (ast.op, ast2, *ast [2:])

	arg  = args [0] if len (args) == 1 else AST (',', args)
	ast2 = xlat (AST ('(', arg) if paren else arg) # legacy args passed as AST commas instead of python tuple

	if ast2.is_func and len (ast2.args) == 1 and ast2.args [0].is_comma:
		ast2 = AST ('func', ast2.func, ast2.args [0].commas)

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
			b'eJztXWuP3LaS/TMLxAOoAYkvSf7mOE6usX7k2k6wC8MwHMdZBBsnWdu5u4vF/e9bp6ooUpT6oZnume6ZxnBaIlUii8U6fBQfuvf6q4fPnzx/9lX11b98+P1nujx59O0runz/4MWjZ0/o5vF3z56/ePT24Q8vnvw7eb998eChXhq9Grp+/ei7tw8fvHz0Uu+f' \
			b'Pnild1+n2x/T7fdyy7EilaePn/3A71J8/4qAl69e4PeHr+n32Q9P6ffHBwh5/OzVd+Dy8VN+zL9/f4G4njzHg29/eAb+vmbih8+fPn0QM/MipoebB0+/j6nB+83XT14+efDyb3T76Nk3yj3uvk63P6Zb5f7F4+/+FoNi5h/9HT9PXj7SWF8JI8QAKJ8++P7l' \
			b'q+dI/xXn79G/PXwSH0Oc3zz+8fE3ePXhN89fsRQ00xzt909YRo+/pR+OhcSDt96/+/Thy9s/Pr39+affPn9594mCPvzPn5/efv7rzw+D5/cP//H2l79+f58e/hRvP7778vb9H7/l3k9//Hfh/Rz97999/vD58/ux98+xN/re/ZRuv3wZePnl3fsv8f7PlNKY' \
			b'vY/x9rdfh9tffx/e+/jXb29//Tik+4+U7d/Tqz//+o94++XDpyz4l1/i/U+f3r3/zw9fMjENWfnr02//mydHN5lQhoz9/PMo84nXD/815IwSGTL864f3HwYPFd3vKdI/P3/5Y8j2u48//fwu+oa4hrT++Pjx3cjz+as31et7K9dUrrmo5MbgxlYrx9emumcq' \
			b'E6pVU9mWbi6GUA5LAasWN42RH08BjbvIgxqXB+EWL9by4+QB3VFcTNIi4cZrwhQYQzVsCFg1Pd8RTx29bSrbXWjAqrEcKziwtrLmQr3k4zsHugqpSnRDgPhsfI9ecDEIt3Rn+N9Q+vZC/CuOs9Fw4aFaGQ0Uvyf+LQuujwGUB74j5k3NMdXy4yhuo5GnIIgx' \
			b'heIW5Ub/vrJ9tfIX4qcbUPTy4ySY7kjEuKNwpAwRSc4pIGSeVi4IwHsoDORcmFYveCfhNONwN/V24yA/8bo6D1qZjgVSqyqhdKTkGrkFGeUY2UfcLhHE4ORdGRaE50KoodXiXQUmoHDTVKRFKBVDiSGXFeTUiGavoQBSfLMjIRXZmHBlOPVA/23lbOSKCkBy' \
			b'blX3UVxUrDZHAD2LwUMA5IIQl0IaCfEpxEhIiCGke6zRrfxkIACm+CbID+u/KDT5cIs7Hx9eqJd88YGk4eTHdUPeh6A+D8ItBGPlh4rt4iLdgoYYUTr1Elw4rV4eqPIAAIa5Q0kwBVcjNlZfUjNQmGBw8DouNBtRSQLgOqUTnfPIfwU1E3HmwRpAfk62kx/S' \
			b'yQv1E+iYNXrScLzq81KLUM5IV5LWIAuigKzWqjIh5osC77mEOPaaGCv5HEuy6atmuGn1hmQy3AmGKN3+ghqA13VFSkmJEPhI6IQa0jj68cRk5X0V6io0VeerLlRdW3Vd1fVVX1c9CbUDx0i4QaESVkltqXyIirQ3mCrYKrgqUCShCm3V+qqlpygKZLKrq45K' \
			b'yiD3VI6kg01N/poCagqpHaoXVOm26qiManq7q9oe0POMMB8q31aexEkchaonOBkgypGOeZIGakzSv95UPeUpQAmo5AgdlLEqoPEjHwmDMtpAFKiO4Cdh8MVyMKoxeOEjGqs+Lw+9l+AgUQUJJYlxaCcRkihwaeQSU+s4mbsq/HuUH5YR8XOnxdCpqvSsHL3o' \
			b'Ud+oklh+LHma5kYyMbBf8i4sv+FaQ5S330tstcTmhGUvLHNx3uuU74Y1H1UbRUq1LaqbytzduuZeE0RoIrNWKoY2xLqAZShcEnMDM3vlYiTZXKBXVIjX6NbeYQxT7c/5b03VUpG5qq2rtqlCV4X+LgvFnYUyFYo/C2UqlHAWStleBGlPW7kYaTa6RjqSTptz' \
			b'aXmthFojnU/mFFS1djtrq9f4mvhb7locedtyr3PKvLaYveTBSx49Z7F3Ve+1aIeCPNHG9J7XgYaXUYgXBfCdjje0mygPe+1DOx1Z8KudqTp7FHkhxqT0nE+MSWEdCXsiRtdm7BEb9G5dHwuLnZS0KHpkDk96gbGNfUjbKlK0GtA+v7/bXTPKorkYZXeQheRb' \
			b'JDKf+1uQf+RWjBkQw2UFcfJisKwG+1AAkeCp5Z+yeqdh0DEM7m41SDwaMUHeaTG4u519ypPJDd6UwTvdKoCRkTx69vf13RaLZbFcueuaT3tQh9SycNlsTNfbMVp7fY8RdPrZ6G5DNjDrwCrW6FBIxk6m0Yk8IyOiRsbQppj9a/nlE836a8wlnC77mACRykHs' \
			b'XNN50zcyuSqTDVmlDds7v9kKcavGrTqWqhiKQpyYCn1e6jBSI7Igo6QQJC4SnhGLGlBxEgJsO2HdM+sjQ4GXvt94gq6PdjUW2z456f1gwDJiwDJiwDIQeC+hzmh5S2HKBJJNraw0vdLK3oWOmTkuy929TmDknBaT1I3Hw59TpLr2uBgjYHXHVZTEUb9viMM8' \
			b'qlZJIyZII5ZHqYJG9bPXWQe6Wl1Gw11vy14TW1+rj0fLa9hukb9FMrJ5m01ZgP88/zpTpzRmLCuXezEUtBcyBMzKASMiq8tRrIyE8qdWnzp5Om5RJKLJyoaZUPTTrPbTjHTQMN640wtEuFtqpFt6h20U0BQrmmKlX6D4ttrHM9K5o8tdx3fo7rSiBKnPguhL' \
			b'0OoMqZ7K3PZrDDDsiQwweGRhb4vdBsMfo4MUK4MUK4MUusRuU8g8btRdQX/dyLy2lfljbizFmthLPS6PiH93IR0Vd6GD1Tc8pHW8FBi/lDunba67u3NU6AVYNc+M+i2t9EHSCL4bP7ciyxOBPDHoJl0nYtaJFjrRQqdDZadjZHdMIwootVel9rF1FqX2rNRe' \
			b'tdnPdOhRLpJVL1n1d9nS3oe7nH9othc7X9DKOIhuBNGNEKvciuSg8gpZNUwvtvpie7K2z9fIcCsZbhlHYp7W9eKctcyeh8x2IqVOXuqUrjttEfSnzH53wuxDd3pdaljrWsP6QvZHva4BPaqhhAPULOBoiDJgg4eO3HmbB0EzDUk4/VweUs9Jzka1l2EZBORe' \
			b'RcV1YS4wqQ5narU6dkS5hSTxQH68ylBX8qVMk6BqCmOhkjCQD2QEOYEQkR3MHSFPmCXCFBFmjzBzhO1gqHewSQw7xCh/DfYuQcKoOrEKF0twsboWjR5aPKzNQxliFw/23mDnDO8JJTos1sQOGq61UYYUhrWf6NdgVxl2lGEfGWxbWDWORdJYFIwJDcx1YKKj' \
			b'JVqYVmBXwUph9IGwlQTVOkzK2FwEQz9M8j0aHGyx9dhli02FjveoYvOmx55Yctiy3Mo/vbqiJgZbWHk3InbiIhz7L/tElv8Td6sW9/S84z3gFW/qht6tUAYrFMIKqsd7qTvs6qQiWbXYu0wBVMgrwsQKm0Z7sNbKNuUhET+bsB9dsBEUtySHlWgP2KIYvVEu' \
			b'sGmSs4jNt8SDw5ZSUpNVj02d7Inved5wjW3fFFmdpcQpqBCx0bOP+5EpC3hU8e7uyGSLTCJiiirYTGKIFrLHztpGYuvAIfZFY8MoYoZwKHiUNHblYpt95yVCbPDFu1nJOKvcIQ2Qo+Don7PVvan+z3f3QUiKf38FDIT7oCX9vw+dIAxwsNHgFlT+n7DJoFIo' \
			b'qoSiMpCa4IrQ74BsgfUY0JvAXICYQbsJsAVQS4BuBGcOyByM3QbwbUDeHOIUbYdDFu/Hj2CZwmQTREpwCB7WYqHEQKn7G/Q+1/ZM06HhM5rNfSdS0TZrqbiB1N2IQ0tlr9BY2aS00vNObfzmhsujyQqdzlHolAX3ElTVm0zbQ2rBxk23KD9lqUYuuykQuOWK' \
			b'yt9esZUiOqzgx2r5ra1VBEU901LlrRQAYhUkRIf17VjQPgIMNJ8GMj1jI/QMjSC74/uIDYJDP/wtAQoe5ziBP4MKecWVmOln/sCU7dM7+qagCncKLND1nqElCSq+OJmgr4GoxFqf0AVkDajiTBfIEkEkdCV++o3Ni4pAWR81LBylwo2JRrHmjYrt76MG6qm1' \
			b'YH119j7QTXpBV/NPnspjbPYZOsOx4HIelM1lcXkbMdmwTiNa5F5aLW2xmqHBkme5W4JMjjZDJrc1CZkpzgKZ01RHHNgJXwAoWt7AnlHjpyiNdAJTTjPEwBKjTb0GpPqsgGmUSwJq4mszUJXIN5LkCKlRMoJVJhtFPIPVGYy6sv08coSe4TnAU9QZWRpjsxmw' \
			b'2ZRuETaLVrMZt5opzhKbGx1jswiSxrNp1gBTiRSY0n5q4ASYzTpgCn0JTBVKBsyBqS3AFCKvvI2BqWJRYEojmkW8GzD9nQDmbe3PNjzYa3hmbgROP4DTl24ROH0BTj8G5xBnCc5JqiMO7ISvCE4/gBO3EZpKotD0As3h1Qk6/Tp0Cn2JTpVKhs6BdAs6hYhL' \
			b'e4JOlYui0ws6U8TLurjhjNJTRmnLuo1XxigdrJ/yLHeLUNoWKG3HKB3iLFE6SXXEgZ3wFVGa7J98CJ2iVEkUpa2gdHh1gtJ2HUqFvkSpSiVD6RD1FpQKkW8kyTFKVS6K0lZQmiJehtL2jNJTRmnHug3yMUq7AaVd6RahtCtQ2o1ROsRZonSS6ogDO+ErorRL' \
			b'KO0SSpVEUdoJSodXJyjt1qFU6EuUqlQylA5Rb0GpEPlGkhyjVOWiKO0EpSniZSjtzqbc2wBXw0qOAhObES7EGF8kUEArFLlbAlpTWI7M2HKU4ixAO021ZMJOWFPcmmQ5wq3iNpIIbo3YjdKrJW7NOtOR0he4jYJJuE1Rb8atEnmR/Bi3UTSCWyOmoyziZbjt' \
			b'z7i9FbjlIavhVWmMWy+4lYO7zTBwFYrcLcJtMXA144FrirPE7STVRreQDG/YCW8RuGnwatLgNZIocGXwml6dAHfd4FXpS+CqZDLgDqRbgCtEXkRfAFdlo8CVwWsW8TLgNvUZubcCuYG1nB0jNwhygyA3DMgNpVuE3FAgN4yRO8RZIneSasmEnbAWgZsWKuA2' \
			b'AldJFLhBgDu8OgFuWAdcTaAArgomA+4Q9RbgCpEXyRfAVdEocIMAN0W8ELjNGbi3Arhsf0LZiP2JF3M1cqmrtAZPKHK3CLiFFcqMrVApzhK4k1RLJuyEtQjcZIgyyRAVSRS4YohKr06Au84QpfQlcFUwGXCHqLcAV4i8SL4AropGgSuGqCzihcA9L1e6HcBl' \
			b'kxQKRkxSRqxS8kkQvihwu9ItAm5hmDJjw1SKswTuJNWSCTthLQI32aZMsk1FEgWu2KbSqxPgrrNNKX0JXBVMBtwh6i3AFSIvki+Aq6JR4IptKot4IXBtAm5z+thts8Nv7yaCoSRYKQzZ4R7EhkHMF66fo3XZlG6RddkU1mUzti4PcZbW5UmqJRN2wlo0MJtk' \
			b'YJZ1FA1/UawTQ7OSqqHZiKF5CJ8Yms06Q7PQl4ZmFVBmaB6i3mJoFiIvJVAYmlVEamiWlcBZxAvBPL/oabS35XZMCW1D7lU3tRwKuZhawFRG2NYOW260LFw+NdRKiDbCtnRXWmWP90drFJvhf9IQT1IecWEnvEUAYyE+yt5Wo6VQKLs6WwtV62KomPykIbYj' \
			b'7CK61BZLgmVbrPIZr9hH0JaW2PLa/TYyOG6KJdLYFKMQIetqJThOuR/huHf3uQYLLV0bxq2fLig+vjY49PteXHxb22DerwTxobScdKSddKSddKTdgGFXukUdaVdA2BUQrmOkJYAnyRYuSDtc8obVxtzBMC71p13CsVJpf1p23aS3JzB26/rTQl9iWOWT9aeH' \
			b'qLegWIi8FEABYmVUQewEuinihU3wZOHU8QH5PBDeDmHLk0b8CVLGr5VJIyuTRnaYNBKK3C3Bry0mjex40ijFWcB3mmrJhJ2wpk2wTXNGNs0ZRRIBrpU5o/RqCVy7bs5I6QvgRsEk4KaoNwNXibxIfgzcKBoBrpU5oyzihcCdrKU6EHCzTfJn+B4MvjxzZNkx' \
			b'fGXmyMrMkR1mjmwo3SL4FjNHvcAXu1RxOkInIA4It9P5o2naJSt2wmAEcZo/smn+KJIoiGX+KL06AfG6+SOlL0Gs4slAPES9BcRC5EX+BYjlWQSxzB9lES8E8Xmp1a2Ar2Mth9BlqZWTpVZOllq5YamVeHK3BL6uWGrlxkutUpwFcKeplkzYCWsKXJeWWrm0' \
			b'1CqSCHCdLLVKr5bAdeuWWil9AdwomATcFPVm4CqRF8mPgRtFI8B1stQqi3ghcM9rrQ4FXLWQXjOAeQ8fJC97+JwcCqFWLDfs5JOw3C0CcLGTz4138qU4SwBvcwzgIkgBnDbz4TYCWEkUwGK9Sq9OALxuN5/SlwBWwWQAHqLu3ZD4ehgLgVe6MYxVQApj2dOX' \
			b'Rb8Mxmay8OowGxL2bHTe4YilQ6BzZ0ReGY1sTYYAx9ZkN5iS5VnuFuGwsCS7sSV5Ar9JYqOE7YSdiD07Pd6FnwrsZk94cXYd1CTmEmqa9wxqiYn1ABOC6WlG+iCiywq6hhh33DFrJquizqg6BlSxiQjjeT9G1WAckme5W4Sqwjjk/GZUTRIbJWwn7ERU+RlU' \
			b'+S2oWmf/0ZhLVGneM1QlJtajSghmUCUPIqrE8JNi3BVVkyVLZ1QdA6p46SDsY+0YVcOiQXmWu0WoKhYNunYzqiaJjRK2E3YiqtoZVLVbULVuXaDGXKJK856hKjGxHlVCMIMqeRBRJQsCU4y7osreiS2pt9LowmeV0a/rx8gbDipzE7cIeX2BvPHBfinOEoJz' \
			b'CSdqOw1SCPbz565EIh2s9TJYk8AJJNedWqb0JSRVKBkkB6a2mFpUHo0kOUamikWR2QsyU8Q7IvN8ItKpItOzPkOq9QiZ6XhNeZa7Jcj0hSHUjw2hKc4CmdNURxzYCV/xRNt6HpmRSJDpxQ6qgZPTbdcZQZW+QGYUSkJmYmozMpXIN5LkCJlRLIJML0bQLOId' \
			b'kXk3jkS6lchkOydEOj6rzA8WTnmWu0XILCycfmzhTHGWyNzoGJlFkCJzzVllkUiRKQZODZwgc511U+lLZKpQMmQOTG1BphBF3sbIVLEoMsWumUW8IzLD9KDofJGeO4UVtvs6+5NPmafno8OpcxCHPS2+3QHMlP3dAO0vA+qw4YzrIJ9AkGUF5WHXflhYIDS5' \
			b'u9LaXLyf436IdOaceWbfz3DgZUlBGYQ1fWwg9mEN+JVOwS/rCjRwehQapOXGR85nCw1mD9bWuMqKQcU2XrKroetrBpQ71w6hiqdu+8myAxy+HSWoVYQsPUhiKasIDubfDr+oLXAJCOO6oq1eH/5I+T2dJ++2QLaA6gSi/ZZ2dp01yFfbP/BAtdsRHS+/36Pl' \
			b'3VWOl9/yaYUNH1TY+iGFxV9QoFyU2l4fROHxCSV3xJ9R4DqgVPlS3efUfMsHTG7oUwqN7t843s8pQMKX/KRCP9HZaTduXzobjqSqvvTnP4oqmkSL3S2nocN+vzoMYV33Z0Gkm9oOuhy7qoVOk8y29DqGcckeP2nVjb9YFaZfrFqi5buOIXYcP2zUeEjG77e2' \
			b'XviZqUN/CKexw4IJiGcVSjP4YgTk51Ws/0jUrh+I2rBRltntLlGzU7w79b3dPr/oRDJc9pW2PfdINnXC8f27bTU8nwi6B13P9PyaPvLU2LlaPTuC5Rp6JzA3rO2h2O21u1nXE3c9+tr8mRmzm1bvvWLnb6yqkvtrqd4XmIc2Vu8Uxh8bvKZq/saqeKi7SXCA' \
			b'lbW5pqp+Ordyiap+ZSAJRFxfpsonmFiLT/8xTOzOMNlj5e+uCxpXhAW+iHqdPR+FBIxw19YaIB27Lwi0bmnL0Jol6g+DGEPgsqpvvHz00tRytd2ABLcbEsJekZB90ffarDPH3Pe/fgTk2t9kW4yuxWqzTPuvpvlhovF+N41vD6Px/Vnjj0Hjy0nrW6Tx7UTj' \
			b'w24av6exQDkKqM8afwwab26vxncTjb+WiVXY7ONqiqtb7hscYUfPjDnczNNOE6370/WD6nk+et6X5Z6n5mAI8/1Sfb+cBR8Wtd0Gr625T+mwck/nUQ+j3LDruJFp53AV+ZoFP5ey5FxPRX54iw3i6XKrzUErcHxLbM5ScwkLzVUsM331+iiXwxx4TUBeM6O5' \
			b'XlY7Wyzuu2m9vUoljDgPNfuf17lY1Vcu+9ykmV7XtGBtiy5m6Xr+VnR91tPdK9jjqFiv1EsoKlEsI72uef01lSZMG33NytgcRBmb9fpoi3XB16SVWxfr77KI0PAiiWPRUlk33W7SVH5crrBdrLGXrFM3r6ffsoKw4WCjOZhUrtSldR0rsDkr8OkqcMf/GxV4' \
			b'Zon4iShwUAXuNiuwrV63VdqH1bC+NqypmZqKjrbFNiZWnBmFCcXuhM5QIbNAulSiKM2gxdi4+eIbis5mw1ob+/0zcuuKXlIwWDJDhbV7JhPmDHAm+7d2yHREQokAzjz06bKZb/hEf9XNMJDtJhA/lYkbxOKXiMVOJdMchXSaMXqjhCIgryylsERK05pb6uyd' \
			b'KuxdBLmtIp5UwLFv215V0OC27qfVZZDg3avIXUpkS+VXlFT8pkTdjyu3dlJ0NzC6Wbvx8xC20LUjmZmSn29L++YmRyyzmyn3NTqZasy0abSORswyOOnO2rNee1CsxzfgzT+Uwe661cdQ5YP5kP7+CrpT319JTdSfdWmDLh2l8STXpZ55PA5dotLIdenmzHbH' \
			b'qE6YNT5ac9wNN27QneYYdec6Jomj/rhq/FWqTbpkrluX2ktVTmZ/2sTrNef71jAsYJJvpqKafuWJfKpnNz+7cGOqtka9oEsnMXuQV1cHmS3YrcqyfMR2EzqIkEu4DfzA8Wm/vqZwDK4pkO7urfgEWTm3xNTl+SSbDxXhfU1YqT5M6+u6LJy9IWdr4LOT2KWN' \
			b'Ta8t9kVhbWR0cm6IK/6z9TEaJq/hoI7Ad7yOK72D3K3MobNB8V7mj5mzh2aOKoaZPyzNyHy8Xzjw7rARleznZUbdoRmlOmryB8u7XLuZp8MfM+gPzaCv5v8wNbD2WctXZjAcmsFQXeqPmWvHzE2OI9LztYfjhTYfKTQ+Twhn5gznBrl0VtBchvKzfOI5PXxG' \
			b'j57Hgw3O6QyeN2gc5Y9qyrbKPLlrZ/4KEqaaf2dCULzO8usOXbhddak/Zq4/bOGiXZ4r37rbUxmjMTicgyG4CELvZHFMLOqmPnij6ap9O+E8a+4x4dnuQVfwAZQbUJdQiZPvrwzeyzv0eK8ey7wT4W/spDi7HZNrlSeKLSkQDuWYd9zL3uhMNxcK5VWPZMfe' \
			b'Fl3CUOtknMh+Y09tF1Vq9dPFuyoUxqJXcHEcuZFKsuZvjVr11ek4kX3Y0onYXbNEzDvq14zwYPWIrsvul7potNhCVZgfWBjtbVFEmI9Oxonsu+NRRFPdhBMx9LdGBW11Ok4sSvXxqKCrbsKJGG7NiAEm85NxIntzArKPX5HcrQy66thcE/DfbyCRsrB7rg76' \
			b'TcM5t0ut0Fd7dCjTmVB8zHn+DZGK28nqtD/BzIF+nYAwKbbe9Ruf7u76LXGKnPwxy8lVR+BETtsGIDcqp1AdgRM5nawpH98v2OZkglr+d6Hf8Pr2KGYpRMjbBiFHK2QsATheJ8I98HzFAYVrqyN2MuG8bexyvMJ11RE7EW5zssL11RE7ES5ONsUalVaFbaNf' \
			b'n+MgO5YFwjC1oksscNxXVgYNv4SzGDs+jKvGeYdCGWYpfZU5IWwnhJA9iEOVuyYor122xAa2dQ3u+QuKogyTgm2ZGtYBvOGni6haaYywE132yyBq3p/CcUAPoQC9ruAg5Ww6xNl0lPybi/8Hfes7Tw=='

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

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY - {AST.Func.NOREMAP, AST.Func.NOEVAL})))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LETTER})'),
		('LOG',           r'log\b|\\log(?!{_LETTER})'),
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LETTERU})|\$({_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
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
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))('*)"),
		('ATTR',         fr'\.(?:({_LETTERU}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"({_STR})|\\text\s*{{\s*({_STR})\s*}}"),
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
	def expr_mapsto_3   (self, expr_piece):                                     return expr_piece

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

	def expr_func_1     (self, SQRT, expr_neg_func):                            return _expr_func (1, 'sqrt', expr_neg_func)
	def expr_func_2     (self, SQRT, BRACKL, expr, BRACKR, expr_neg_func):      return _expr_func (1, 'sqrt', expr_neg_func, expr)
	def expr_func_3     (self, LOG, expr_neg_func):                             return _expr_func (1, 'log', expr_neg_func)
	def expr_func_4     (self, LOG, expr_sub, expr_neg_func):                   return _expr_func (1, 'log', expr_neg_func, expr_sub)
	def expr_func_5     (self, FUNC, expr_neg_func):                            return _expr_func_func (FUNC, expr_neg_func)
	def expr_func_6     (self, FUNC, expr_super, expr_neg_func):
		func = _FUNC_name (FUNC)

		return \
				AST ('^', _expr_func_func (FUNC, expr_neg_func), expr_super) \
				if expr_super.remove_curlys () != AST.NegOne or not AST ('func', func, ()).is_trigh_func_noninv else \
				_expr_func_func (f'a{func}', expr_neg_func)

	def expr_func_8     (self, expr_pow):                                       return expr_pow

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
				'partial' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_')) \
				if VAR.grp [0] else \
				'd' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_')) \
				if VAR.grp [1] else \
				self._VAR_TEX_XLAT [VAR.grp [3]] \
				if VAR.grp [3] in self._VAR_TEX_XLAT else \
				AST.Var.ANY2PY.get (VAR.grp [3].replace (' ', ''), VAR.grp [3].replace ('\\_', '_'))

		return AST ('@', var + '_prime' * len (VAR.grp [4]))

	def expr_sub_1      (self, SUB, expr_frac):                                 return expr_frac
	def expr_sub_2      (self, SUB1):                                           return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1    (self, DBLSTAR, expr_neg_func):                         return expr_neg_func
	def expr_super_3    (self, CARET, expr_frac):                               return expr_frac
	def expr_super_4    (self, CARET1):                                         return _ast_from_tok_digit_or_var (CARET1)

	def expr_neg_func_1 (self, MINUS, expr_neg_func):                           return expr_neg_func.neg (stack = True)
	def expr_neg_func_2 (self, expr_func):                                      return expr_func

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

		if pos == 1 and rule == ('expr_func', ('FUNC', 'expr_neg_func')):
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
	a = p.parse (r'diff (1/x, 1') [0]
	# a = sym.ast2spt (a)
	print (a)
