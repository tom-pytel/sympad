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
			FUNC.grp [0] or FUNC.grp [2] or FUNC.grp [3].replace ('\\_', '_') or FUNC.text

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

		for imul in range (len (commas) - 1, -1, -1):
			if commas [imul].is_var:
				continue

			if commas [imul].is_mul:
				if commas [imul].muls [-1].is_var and commas [imul].muls [-2].is_var_lambda:
					ast = AST ('lamb', expr, (commas [imul].muls [-1],) + commas [imul + 1:])

					if len (commas [imul].muls) > 2:
						ast = AST ('*', commas [imul].muls [:-2] + (ast,))

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

		return xlat (expr_func_arg) if xlat else _expr_func (2, 'func', func, expr_func_arg)

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
			b'eJztXXuP3LZ2/zIF4gW0gMSn5P8cx8k16keu7QQtDMNwHKcIGiep7dy2uOh373lRfGp25J3ZnRkPljuSKIo8PDw/Pg4PyTsvv7r/9NHTJ191X/3Lu99/hsujB9++gMv39549ePIIbh5+9+Tpswev7//w7NG/w+O3z+7dl8sgVwXXrx989/r+vecPnsv943sv' \
			b'5O7rePtjvP2ebylWTOXxwyc/0LcQ37+ix/MXz/D3h6/h98kPj+H3x3vo8/DJi++QyoeP6TX9/v0ZxvXoKb749ocnSN/XFPj+08eP74XMPAvpPQvp4M2zh9/9Db++9/h7+P3m60fPH917/je4ffDkG8kF3n0db3+Mt5KLB3/Hn0fPH4h3YATG9oIJAQIw5ON7' \
			b'3z9/8RSTe0H5e/Bv9x+F18jObx7++PAbjOb+N09fEBck05TE94+IRw+/xftnDx9TIhQd8Ak/f/vmw7tPr//48Prnn377+OnNB/B69z9/fnj98a8/380Pv/z1+9vXbz78R3z5U7h9/+bT67d//JY+fvjjv4vHj+H57ZuP7z5+fJs//pk/hqc3P8XbT58iLW/e' \
			b'fgr3f8aUkMRI3vtw+9uv8+2vv+N3/4hZfP/Xb69/fT+nnrz5PUbw86//CLef3n1IvH/5Jdz/9OHN2/98NxP1+7uZT2//+vDb/6bJwU3Cmjl7P/+csSBS/O6/5vxBInO2f3339t38AAX4e4z0z4+f/pgz/+b9Tz+/CU9zXHNaf7x//yZ7+PjVq+7lnUujOjNc' \
			b'dHyj8EZ3l4auqrujOuW6y6HTA9xczL7kFz0uPd4Min/sAG/NReo1mNQLb/HDgX8Mv4A7iIuCeEx4sJKw7i+Cr/jNHpfDRHcQ0whf687IKyRBU6waf0yn9YU8whPdWcoqUi+vggc/mfAdvLfBC2/hTtG/8uFTigOTFX+mobtU4snPEP+giXFT8IA80B0Qr3qK' \
			b'qecfA3EriTx6IRujL95iucG/7TREwWQavEFye/4xQj18oKmgp+4OpowsGi7EwyUPni/ogQmNUBgoEsxZeUTagVd97m+qRz3lXrZ+HFKvS0UFajB3o9zdoWyPzLNeZAwCDCp44S1+DxxGvlCiwxwgeMfHSxBd4hqWDrxhQbZ4gwEchB86EC8sLgWJYUag1CAK' \
			b'DrkQAiFkhy0DQqbygJeKGA9fXPrOQCDOscMbJFQLKOAj7ToUzYgEeBe8Zw/kC/rY6DOwj4s+in188AGhJGEZ+SdBxygyrj3/EDCYRO3pFu9ceHkhj/AUXnAahn/MOOd99ppSL7xFxmj+gWK7uIi3GMaxZIRPUISJCGQ43VA1okP1xbSCH2NwfjRUNjqgEvJC' \
			b'IjiyaFlFgj4FdKXe4gHPlOzEPyB6F/IMoKPMw5uB4pUny7UI0qcS4SAedypIr0iGn6EANQm+ENLlMQEH+aiQDjwZYuEwdcN84+UGuDTfMXioUjOdlfoF4lFUUYIf1LLQVrzsO8AOSCqQBMUA/prE0HbWddZ3TnVOd6PtRteNvhvHbpy6qe+mAXMG2QYsA1GA' \
			b'EEuCDCUGoUCenemc7ZzrHEQydg6qIN/5sfMTFBPyY1TdCHWOQkZBfqHaGXp46OGpB+p6S1hQKJMjPjv4h6j7bgT+9CPkCYFngVC4h/T6zg3d5LoJgKYQawakzwK7sJIFyZxUN0HeEBjwfQe4ga87h+0lPAFTIMMDsgRrMHxWji+avLHmw0d8gjBaniy/BE6R' \
			b'N7ALvTmmO04Cjxyh428GDmMktZGS+dIL4c4oHAS6zuwAdowiOhMJy8QiCjlkodH0mvNW54ozM2ejzENCOhD9imscEuppp7H2HKsdGF4s9lTMd0bJx0DIwNoSIocKHMJAQn1R4LM0cMmzTJx2+Q+OmcfF75lrPrBtJF4ytUBkJIoo2REVGYdTxu5IQF5iz/mM' \
			b'dWw1CAXedN52HjKgOq8733d++OKBAMxxZ+YsM8efmbPMnPHMnKX2xUnDwhfFl1FzB9VId4A7HZrbb624U0sUY6heQvfSre2tfMb+I319JG3RnVHyTL6UG8/ZHQd5lg6Z5dxZCj+ZbrJS+HNRH3mzfMdKOdqRc8qy4XoZ0zA/JmbTJL12I2MaYg6M+W1/UHkC' \
			b'AllIjY0EcuEdGJnMVuMTMoEciKPHumI4NHJZRCYq/YxQfDsxVHQYV2svUJKKREYd9twJRO5AVtXFl5FVLGzWrMDlS2+KSZcEfFid/wYHmJPHygfIMvBhziBn6bQaV9IFqnN19xKVoYqVoWd2YEt6ZoMow1WqioeMnpsI1ornfJnoGbJ5Zg+rw9XOFNcvs4ka' \
			b'6KhqYjYpsuF6ag0SIex0sjOeUnZwfoREb5ChE4+31CBTkkqUFqLFYX2NMjInKVMInkr4yDnxEic/jj8bOHNDBco1TGNi+BXPHvPsSFLn4yQBfek5sOdPvZIWwfNg2/fheciEwXHD6jxfRo5LU42Gqj1k7XExsuf+Y++kciZuVToIy93MfNZxChpL4tk+qJui' \
			b'Dk2xDk2xDk1hYUxcGCbIAhc0z4bp2IBzq84N+BfTB7xjJmEd1WYHJXPGSIERFA9PzYnqQybQHyaBAD3RGE6HVrio+u/3VR2g5lYUpYo1olx3SdWV1fNw1WQIo/EaKnDSEuFzYXgENYIWEyOdDhAchz7PLG8YNQwq55lJH3Eoypz1aTngSEyLYY7mEVj6Vstb' \
			b'YIyumh2OqLLlaPhiv09Lv09xhw/HN2fTGC43bk3VefCL7aUXsWI5GnTAvZbOouJeIo6Kzrgn+fFnwXE8JNA8JNA8JNAyJNDHNnv/Ekcw+shGMDRk0aemT8KxlZKRj+aRj+aRD1zKvqBreJqs24OjAMXz9prnxanRleHrRA3BQWUfO5HUm2MUAUUX3BszFzKE' \
			b'f0UDfUMW4PgLtBjpUJjzLCB2dbTotLLur+fOWtRv9Pl7zTw9snoLCDVVPxGINgwdw9AxojQwoi0whzi2QzSKzFuReRt6IizzlmTeirDbajBDObecc8s5t+d2murJMx/IuMyystRJA+NYVhzLigvVQQejJeGbS5oS+NDLh/7oFckvMeOeM+4JX6zulVUDDt8V' \
			b'ylDM+MgcG/nDUcKOp8GO6QSyAZQdfzZQpiYxHe3FdrS/4JV2L3uEJ9RmTAnWQkjZHLXDpUCs6eAFQQDfaBdBdKR84TqRc5jmRNhhiRFTwjiqPYV3VHUWuYURcuyIc5U6iakocBnVl1nmHVVyA9KPGcAcIBMxGzhnh3nB2TmcmsNZO5yxwwWFWCfhMkNcYwj5' \
			b'GnDVG3IYq1e0t0Zja7SjxgYSW0e0ocQyxHVfuEoL11bROlEIh0a3aN6Ktq241opqePBDE2W05cW1iWjLi6sRcaYJF1SgaTyagGN3CieUcDbJgz+qoVAHhXbh2JXCShwXG2EJ42QVLlZEa0/kA/a++x5KFZezWlzmjeudeS000HwJ6eJCZ4frYD3/g7hdTkNY' \
			b'Hw5BFPvjOt8pBkv/gcpLj+/gf8RVvpgALvzucc+BHn16XDDcW9or4HKkB0wLl9v2uIIe14DDAxTfJa5QnpA+z4vlKRVbpUq5mS+09hznYOARmAGZoheQ0EiEAPHWCDFGcoTrng0unccVzD2mzquyaZ0xEoW8on0LID6VJEiJCCNx7fyEK77xA4gDc9XRFgOB' \
			b'Vo//6AdRucTfIePxiquPB44Nl9cbXJyPq5ZphTOWAEQZ8m2k+IBSkJ/LCTluOV5cU475TQoJV7OHTxxGj8QiKyCMA7H4p53uYkDAwF1abzzAM8qykmdPz/+HSiusFYo6oagNuCq4PvYnBDhDuwb1JkCXYLZXALcEbAnUTSAtgZmCUm0A4QYEtpAnqNszwizj' \
			b'h4GzgJhNaCmhwuhYREaJiBIJm1BQSn4i9SjtDSmnLhcIr08aMWpDZUnr3Ijp67VjJhHnXrrxZZuWdAliy+ZCr34Ikz9G+hICAp3hgPqLeeOetOzwD++pIzHUEKG2LcBiul47husgaG+UsQEV12jTAmR0uz3L2jKsVLxACMLhUhZcx5LBCYsXhkcTIcf3BBy6' \
			b'9N0UkANgmea/NTAaWyhCzwRI8MiuRFRIMEvd8w4p80fyKYOO7hLcYeDJEvImwh6lYvji5Fvf11CcIvgQeDPoKP8F8JgnEXyRqKlui4hfEYhMkZXgVTNEUQsgKWAWe9oEaWxigE/Q4pBIG3sXKwEQF7gqbHo0o3dK8OsOCLlt2OrrIPeUUYvNhUMeYk57bvWk' \
			b'xaMdhQi2/C51a7BL0ZbYpWYqYjdGXGC3TjojQ1fEIYIdgZgeqsZTYExJTXwxfHEhhhLEFFELxfKuwHHgUERyJK6BZE5xRrIEREHoW1AObGIwU9AsgQaYGyA2ZRN8+BA+47eJ34FEHTsXOXiHGbxD6VaBd2iBd8jBO0dcgnejI/AWXtz80t0icgdG7sDIHRi5' \
			b'/HmF3GEJuRy+RK6wJ0HuTFkLuUOOXA6IIjA0kSs8EuQOjNyYwHbItV8Sck+9z4zDL0fjH5uj187otaVbhV7bQq/N0TtHXKK3SjojQ1fEBfTaHL34HLBrGbuWsWsZu/P3FXztEnw5fAlf4U8C39mzBV+bw5cDkgw04StMEvhahm9MYF0v2p1hfEIwJq0RKjB8' \
			b'DuNZUcvvUrcKxr4FY5/DeI64hHGVdEaGrogLMPYFjH2EMatr6cIvjEu+r2Dsl2DM4UsYC38SGM9Rt2DscxhzQJQB34SxMElg7BnGMYF1MPZnGJ8QjEeSe/w0h/E4w3gs3SoYjy0Y59rgGHEJ4yrpjAxdERdgPBYwHiOMR4bxyDAeGcbz9xWMxyUYc/gSxsKf' \
			b'BMZz1C0Y55plCYgyMDZhLEwSGI8M45jAOhiPZ430CeJZkW4Ly48VW4qV0oqV0mpWb3GI1K1BtWqpt1Su3ooRF6iuky4p0RV9AmxVqLdU1FErVm4pVm4pVm7F70tgqyX9loQvgB1YFIEdo24AW+X6LQmIiw+b+q3AJwa2Yv1WksA6YE9nYJ8isGnYjAXGw2bZ' \
			b'QJ+31aeLANuWbhWwW4NnlQ+eY8QlsKuksQgyUnRFYEB2MYBWcQCteACteACteAAdv6+QvTSAlvAlsoVHCbJnzxay8wG0BLSaw9fIFkYJsnkAnSSwDtlDf4b2KULbEQLIEbQdQ9sxtN0MbVe6VdB2LWi7HNpzxCW0q6RLSnRFX0B2Yc+BzwHZjpHtGNmOkT1/' \
			b'XyHbLSGbw5fIFhYlyJ6jbiHb5cjmgIhs10S28EmQ7RjZMYGVyB7OyD5FZJOSDIuKlWRkETfwpe+iTSOHSN0qZLdUZSpXlcWIS2RXSZeU6Iq+gOxCW6aitkyMGxVryxRry+L3FbKXtGUSvkS2sChB9hx1C9m5tkwCIrKb2rLAJ0E2a8uSBFYi+2z5dZLIJr0Z' \
			b'lhPrzRSrzujS00WQPZZuFbJb2jOVa89ixCWyq6RLSnRFX0B2oUBTUYGmWIGmWIGmWIEWv6+QvaRAk/AlsoVFCbLnqFvIzhVoEhCR3VSgBT4JslmBliSwEtk6Ins4GXDTMqAzyFk5ztpkhZzEezxuRxHO6UI1etCSq9Kt0pKrlpZc5VryOeJSS14lXVKiK/qC' \
			b'olwVinJFOB9ovrpnhTkbXtOFAxiXxFMpzNUC3iV8qTAXViUK8znqlsJc5QpzDohyoZoKcyFfFOaKFeYxgZV4bxuQZauQjnLu63Psx665AmkR1juANKIUD8TC07A2t+Ga2jpaF5vOfeF2KHpuwHXprr8UQuVG3FzB8n/ViFfJZ6ToisCAbJMMu31hTkaHek5i' \
			b'BSoGKT1XqnUDrjNAY1SxDecUyzZcuJQvqVBtm+6s+da0uMILVY32m2MO7TfIBMaIy0e4JZ95kCF78nd5Lr+HqyYk29qe+zAb7n4ftt2n3mzTWjNa7246Wn830gW754a752ZGtyndqu65aYHbFOCe6SihXaVdOCcALwgcSUyw5irWFuJzQLjhXrrhXjovmopR' \
			b'VCA3S710Dl8iXDiV9NLnqFu9dJPDnANazeFrlAvBgnJeTpUksLLVrqzODhPp5/H3Koxrmg7DIuHpMM3TYZqnw/Q8HcYhUrcG4Lo1Habz6bAYcYHvOumSEl3RJ623LmbDdJwN0zwbpnk2THPrHb8vka2XZsMkfIHswKKI7Bh1A9k6nw2TgLhjVbP9DnxiZGue' \
			b'DUsSWInsyhBtf8gOWyWc8X1T+KY5MTqynPHNc2Ka58T0PCemXelW4bs1Jzaxfo3kGs8x6wXnDt/oem6sJqGkSFd0BpwXc2M6zo1pnhvTPDemeW4sfl/hfGluTMKXOBdWJTifo27hPJ8bk4BWc/ga5/w+4JznxpIEVuL8bKl2igg3ZKmGZcCWaoYt1QxbqpnZ' \
			b'Uo0fUrcG4aZlqWZyS7UYcYHsOumSEl3RJ8g2haWaiZZqhi3VDFuqGbZUi9+XyDZLlmoSvkB2YFFEdoy6gWyTW6pJQNxwrmmpFvjEyDZsqZYksBLZZ1O1PSNbFLm3hHAapWIRsH4NL1gsmhE+q9g4ROpWIbylYTO5hi1GXCK8SrqkRFf0BYQX+yWYqF8zrF8z' \
			b'vGGC4Q0T4vcVwvUSwjl8iXBhUYLwOerJhLsS5zrHuQSSr2qcC7cE55pxHpNZh3NV2a3tb8nIrrXlW23ktQ/4bq0a3wlUSWWGjDSZKtzMmjJ+l7pVIG1pykyuKauwWaWYpa4rmgIwC7XYZdhAyJhu4x5CZkkLJtGXOBQuJDicKdmg5Q4h2rjjlwF3rPuK0W65' \
			b'XlpV1mRnvB0Y3mh4a8hleJsHtsaVbhXeWgNb4zbjrUoxS11XNAW8uSW8uSvwtjRmlehLvAkXErzNlGzCm4Ro441fBrzxSDVGuy3eKhuvM94ODG9kroUKvDHH22yoxe9StwpvLUMtM27GW5VilrquaAp4G5fwNl6BtyVbLIm+xJtwIcHbTMkmvEmINt74ZcAb' \
			b'W2DFaLfFm/6SliCfshLIkhIImdxnuLSz+offpW4NLm1L/WNz9U+MuABonXRGhq6IC/u+9i2AytjQsvbHsvbHsvZHPq+2gF1S/Uj4ArCBPRGwkbKG6sfmqh8JiHLeVP0EHjF0Lat+kgS2hO55F65TgS7twmXpuIAMuvMuXPwudaug29qFy+a7cMWIS+hudATd' \
			b'wkugu2kXLsu7cFnehcvyLlzyeQXdpV24JHwJXWFPAt2ZshZ08124JCDKeXMXrsAjgS7vwpUksCV0v6htuE4auizrCl0G3dmcmd+lbhV0W+bMNjdnjhGX0K2SzsjQFXEBumoTdNmK2bIVs2UrZvm8gu6SCbOEL6Er7EmgO1PWgm5uwiwBUc6bJsyBRwJdNnRM' \
			b'EtgSuq7eOz01fjRHYsu8yy1tm4cvpCgfd2TqvC3a1faIrw5e2Ar1fsPW7yhcHl1rD3g7L1TkMKm7vjW0zVcqxpgbxzBQHmyDDMsLFUsvtJUk1bb1m2oHXq1oebWi5dWKEkO9Px8OWl1+LkOyfLG537zEVdYcwsDcUFp8W1VHXMeIUkDVh+/CfvS2uZgRt6UP' \
			b'7JQ6hBc0Rh6VdQh50y/dY3WCF4dPVJn47uWNHMPAh6zICSut41U2aKyaJzG4K5BdIrpA8pXHpsD3Wx2ZgoiFd4tHpWBpHNgBDXK4STigYflYk/WHNJjrHNRw5ZElZqvjShAbG48p2eJ8EshEiYt+X9DAZtMe+CEleK7TNQ4qWWqpFo8IuqmDSoYjOawEmX2N' \
			b'A0umSprrvuIOpdnvUpqvW9FvquSvkuayYudVSkck3X4P0j1Q1nYt4VtIN3eLh1nKQ9e4kHZg4VZ9GrPj06WA4PWnxu26/t7UrRm2lHq9vh7fIOUrN0C59oFTyJvPPKZtt3U5jviW63O/ncS7pT6MHbDPQgfaDDfUh8eqPYzsd1TB44p3eD8fjnhTFX2rF787' \
			b'kd+/uIcj+XZewXNPbyAVxs2duzYQl67syoDYe3cXEiOxV93Lmx22jp83ct1z15zk2y+MVreS8QOSbcx4XDqHOrhL35zG2Uqu935+IBPYf2a3HNhzMxLs8IhvEWK/dzlu6VPXyLIV7ctJyTTqI1SUa5zw1zcg243tj1fV0woziNxR15Fzc7Wc292Iugi524Wc' \
			b'bzN/0Jo32FbW+xuvu/06w9PPVC2GbjgmZHcm596trce92VrWB4rdX1fO7dVy7nYq57OQ9zfYL1kj46cr36lsIz9uto+yQrZ3INfuarn2+5Hr4SzXtyrX+qTl2l8t12stJbaUa3WW61uV68+f8jwGuR5vZlz5uQrAm1CIBOFVn6P002jHdChjx+vp9jAjN6LK' \
			b'Q/ulxoy86xcltfun5el3moaX6fdxIt3edJbgE1B7XFMtXVS1aE13o/ONCypotBaZejqFvL8hBZ7NdHj7k9clc8jPUd+dgPwiUy7xOL6outtvtwFP8NyVyu6zug7A5T1JtNpY97rSAPiGauAr9y3e1vzPkWXCQUk0W0r3V9bKFKY0o72pyZUrthHewtYP94fm' \
			b'A+n7VhdD3wVkU2W9t/nCs2jfvGgP9H+1aA9HLdqYMIn2sFm0dffSd3EV10CSPJAMJwIs0qtRRCdbrIHSbUlCSUmlY3RQ8lgKyVIjKmInZTuYdpnO5UlliWVFrWi6OIdawAYzkVkpg5yhpsqsy3REJ+NylMVgWzAhQKZarIXMIHm7DjMGyrcIsBO+yAfbMcjW' \
			b'PDIzm+xKNpkmp8zhcMvkkM84FlB8ba65lVyr24C59t+u6t+Gs1dV6c0FhaGvPeyG+4r+q4rXhQo3RLBVZbtNMV1VjTaqT+nfAjF5NemrQr09PcLiAtQ9mbktj7kaMtFurye9w7HVNcZTzQWdO9UD1LJUN7/a3IUODMnVeJarreQKy/qQlU6JYOE61f52BEup' \
			b'u5dUeHcvsbzgiWuv6Sxl20nZcDxSNhC1ByRlkEwqZbeubj9UQfPHoUY/hKYSpWo4YKm6oXUG89r+scuPNNskZfr2pIzSXitkNMG+KznzG8VsoO5oOC/sqmPCoNREAg9mJvE2hXBJ8FzSlB7JTGFaxe1vZnC7ag4N+lEfAAzF8S/knLyNeJPWzdNAPKrCSD5G' \
			b'/t7S7s0WQ0DC0/TqAu7uXNIWwLzDi+rLnVxocwfaeCXfdYXWHqIRc5jVC5uaIHZ4wxE8FhXXnuOC3QnXL8Lv7HBTFblLlmmxTxE0cZiNS7U/eiHGtX9Ekt4fSVBlwB8ImkbTrtlpWuqm5Y/XMY+0QhNeIhYhDWwH8LyWsNSYSDX7I9V0q/+IJLs/kqACbfzh' \
			b'LMjCG09viCx3FVnjdSiDoNUfztC0/JM/osznlFXbL/GG53Evpc37J+WbJ+EqdFpXbGVjJNkUqZWhbJNel2xIpJNNh3y60dArbCf5D2TSd8lD6rYJQ+9aH5W+8W3iT3wcty7himvbFTKMwRb+cBJu+S1V7JfTfot5GtslTQdF76q0sUuyP2fGysv6z4uMOD70' \
			b'+5YI7J7t2DHlSSuO3T+/A5HBA21uSWpcx47P1JkfP99hN/j6sSw6LoONPRPeL2wzQhdlCLmXyxGO8dqOtnPb6HA8UPv66MvZ0ackUjgaOybHRbCxt7aNRDGrt5crHLFew4Vh5sZQnDV7UtI1dUfluAjcFR2M7QWMub2lmDX4hyqS4GCwnj6uckG1cUWoQkFB' \
			b'zPCnJI+obzomx0UwHo48qu42HLNhOilJ1N1ROVYx9Ycjiaa7DcdsOKlBBTYLx+S4CNQRFMF8dujWRTF2h+YGHGcCWzaG4iLRO64cgsqtyWa3TR0xdTt0WLQNX7f4BXPFnKKg4sTK8TkuELud+nBnkmpzaUXeLvNVdRscnk27McCWLo2nFSfz6apR0K3yyXYH' \
			b'4JhPW8463A6ffHcAjvl01SjmoGdn8DDqqxzbHfD/NuHLz62KUVi7HM6bJMHqPTN7z3Mk+2U2WnkctOPJ7asGQ4fNY9MdtmMeD0fNY9sdtmMeq6PmsesO2zGPYWyk0OLLC89NeJb3Fp+RJeiHLbuEg05YWhTAN5w+d7T33IA7Gg1sBIVmXa2QvkscBxyrgFgE' \
			b'GHjsUjc4+WBK7KPQqo69cRuGWSbmsvVohcVGeGKAFwzmRu5W4lp3XrdFRUhzdiQUmgt+EnMcEMphRG4MIwwvX138P7Ub6eA=' 

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

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY - {'@', '@@'})))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LETTER})'),
		('LOG',           r'log\b|\\log(?!{_LETTER})'),
		('FUNC',         fr'(@@?|{_FUNCPY}\b)|\\({_FUNCTEX})(?!{_LETTERU})|\$({_LETTERU}\w*)|\\operatorname\s*{{\s*(@@?|{_LETTER}(?:\w|\\_)*)\s*}}'),
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
		('STR',          fr"(?<!\d|{_LETTERU}|')({_STR})|\\text\s*{{\s*({_STR})\s*}}"),
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

	def expr_lambda_1   (self, expr_commas, COLON, expr_mapsto):                return _expr_lambda (expr_commas, expr_mapsto)
	def expr_lambda_2   (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1   (self, expr_paren, MAPSTO, expr_piece):                 return _expr_mapsto (expr_paren, expr_piece)
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
	def expr_casessc_1  (self, expr1, AMP, expr2):                              return (expr1, expr2)
	def expr_casessc_2  (self, expr, AMP):                                      return (expr, True)

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
	def expr_mat_col_1  (self, expr_mat_col, AMP, expr):                        return expr_mat_col + (expr,)
	def expr_mat_col_2  (self, expr):                                           return (expr,)

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
# 	a = p.parse (r"Piecewise(((1, 2), a), ((3, 4), b))")
# 	print (a)
