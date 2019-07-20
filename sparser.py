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
			b'eJztXWuP3LaS/TMLZAZQAxJfkvzNcZxcY/3ItZ1gF4PAcBzfRbBxkrWdfWCx/33rVBUlimL3tGa6Z7rbjeG0RIoii8U6fBSL1MXVV49ePH3x/Kvqq396//svdHn6+NvXdPn+4cvHz5/SzZPvnr94+fjNox9ePv1X8n778uEjvTR6NXT9+vF3bx49fPX4ld4/' \
			b'e/ha774eb38cb7+XW04VuTx78vwHfpfS+2cEvHr9Er8/fE2/z394Rr8/PkTIk+evvwOVT57xY/79+0uk9fQFHnz7w3PQ9zVHfvTi2bOHsTAvY364efjs+5gbvN98/fTV04ev/ka3j59/o9Tj7uvx9sfxVql/+eS7v8WgWPjHf8fP01ePNdXXQggRgJjPHn7/' \
			b'6vUL5P+ay/f4Xx49jY/Bzm+e/PjkG7z66JsXr5kLWmhO9vunzKMn3+L+5ZNnnCEnR3zC6+/efnz/+c0fH9/88vNvnz6//UhB7//7z49vPv315/vB84+/fn/35u3Hfxsf/hxvP7z9/ObdH7+l3o9//Ffm/RT9795+ev/p07up98+pN/re/jzefv480vL23ed4' \
			b'/+eYE0gcyfsQb3/7dbj99Xe8959jET/89dubXz8MuSdPfh8T+OXX/4y3n99/TIL/8Y94//PHt+/+/f1A1O/vBz69++vjb/+TZkc3CWuG4v3yy4QFI8Xv/2MoH2UyFPvX9+/eDx6qwN/HRP/89PmPofBvP/z8y9voG9Ia8vrjw4e3E8+nr36qri5WzlSuuazk' \
			b'xuDGVivHV1NdmMqEatVUtqWbyyGUw8aAVYubxsiPb+ipu0yDGpcG4RYvNvLj5AHdUVocpUXGjdeMbXMZQzVsCFg1Pd9RSh29bSvbXWrAqrGcqsWPqyhl9ZKP7zziVbammJeTAPG5+B694GMQbunO8L+h/O2l+FecWaPhQkO1Mhoofkq/scy4PgZQGfiOiDc1' \
			b'p1TLj6O0jSY+BoGNYyhuUW/07yvbVysh0+EG5Nby45R6esFyRffVBXIGi6TkFBASTysXBCCjjioDIiF8US9oJ24303A384KsNMjPvZM0VoYr1KF0nd5dcLG1YmuVMVSbiUG4xfvEYfCFM22GCDF49K5IdJlrqJ06Mo7COZik+8I0FYkXqstQZigI1RolISK/' \
			b'JgYg5JstI1KhphFXhhlPb6zaytlIFT1gRlACAgp6yYYKsj5Cg57F4CEAfEGIG0MaCfFjiJGQEENIKFlYOvlJ0NHhDjet/DAwpFJsy7e4C/HhpXrJFx9IHk5+XDeUfQjq0yDcgjFWfqjaLi/HW8QJIhnxFYgwEwGG8w03IzY2X0IrhQkGB6/jurERlVQWFsFO' \
			b'RMujmJUbhCQN1gDyc7a9/JDoXaqfQMeFpycNp6s+L60I6DOJcEBuRc5YelUy2gEK1JLggZKu3gQcHGJiPuRzzMKmr5rhptUb4tJwJ+DhRs1VXtsXSsdwQ0lh1MpSX3FVV4QdklQiiaqBwkkG6cdXPlS+rYKpgq06X3Wh6tqq66qur/q66on/HQpHXCSiCCGe' \
			b'BZlqjGKRPAdXBV+FUAVKpKsCNUFt1XZV21M1gR+dqTpqcwwYReUlqWxq8tTkq4m62qMlIoEkUHTwB/qnpOuqI/7UHZUJwPNEKN1TfnUVmqoPVU9AM8CaI+nzxC40siSZval6KluA3FBlE27o7SqgvyQfMYUK3IAlaMHgN0EuloPR8sELH8Wx6vPykDjFwcQu' \
			b'BEtKF0Ejd5JgkHcaieM0t46z+dIr4aJTDhJdZ3YQOzoVnZ6FpRcRpRKK0Fh+LGWbl0oKMxQjL0NCOhH9k7Q4LNT9TlOtJVXfCLxE7LmaLzotR8PIQGtJiVMDTnEoo3ObdNEEYZ5UfytcayPbOualUEtEjkQxJTuiYsLhlLE7EpArjJzPWEevwShoXdX6qqUC' \
			b'mKq1VVtXbXNmzkUIZ+asZ057Zs565nRn5qzrX4J2LHIxcumsDFCdDgdk0GGl/7ZGBrVMMWLVGrvWYW3t9TUJ7/jtI+mLLjotM4dyaVopbteoXwdkXkrnOX7vqt5r5Q9VfeTd8oXXevSdlFRkI9Q6pxF+9MKmXkftTuc0zBya8/v6oMpEBIqQOj8SKJV3YGQK' \
			b'W12bkEnkUBo12orm0MgVEem59ieE4mkvULFxXm1bhZI2JDrr8OdBILhDRTWXWuCBG1Jy4Um5/AUOCOuOlQ8ou6hd6DKVgwVsORmxoPKfxUI0a2c+iC7RnJvLKyhTjShTz+xAT3xmgyrTTarKp4KeexHRqk/50rOfinlmj6jTzc4U31eThR4a6FpmNivC6Xpa' \
			b's8WrC0bY6RSnO6XiYH2FRa/RqZfM10yjS5pGlR6qBcrWQVuu2iNnwRVWTY6/GFjy4ZqUpqWwovyTLDvLskrS2GN1gd9sJXIrr7Ym1rLM0ts6+ptUCqB+R2KhlUsnaVluyqATBGuPi5G1DBzroK0yc2umvPAyvpwuV/ZR1ck82wd1/ah8M6J8M6J8M6iMXirD' \
			b'RVmQipZlNDv23NKdS8/9xQz+LlyvrONm7KBkzjmtMIbi4elHoXcUAtvDJJCgp6rG/tAqF2sG9b6aA6h8VcNqRJUqbZc2XZN23mvzT1fYkE4tlK6gUEOwiXZHaCQK0ailKAUTE206Ngjy9nnlesOsojFTnrnUi6mqvZQpalIvmKlZNfyxMkNLn1p9Soyxs95J' \
			b'EprZihRCMS60Oi40MiDE/OdseiP1Jp2uqc86lZ9YcqxIjpWxhuLe6pjSyGASs6Yz7ll+2rPgBJk5WJk5WJk5WJ052GOzDrjCRMce2USHZzb21PRNmIIZnSBZmSBZmSDRJR8yhkKgmwyDMFkwYhdgZd2dO12d5fbcERxU8THW5EGfoIgoupTRmLvUmf5PrA9w' \
			b'bGGOX6LF6YDCnRfQMNSxqvOaDM5aGayNapB6+twKT4+s3SJC3WycSEQ7gY4T6DjVLThVKrhDnAICjSrzXmXex5GIyLxnmfcq7L4wi0F1Scm9lNyfVz+4nTzzgY3XvOhUg3YwQWQliKyE2G1UNMhVvoWkK6EXW32xPXp98xUK3krBW8aXLBHoroSAZ5nOFAXv' \
			b'hGOdvNhp3O402NGfQDGIsuMvBmSqV9PUWm1T60vZyXdVA57UmgklaIVA2ZB0wFYj1XTwhiOC7zhVYzpSvkibKCVMS6Ls8MyIPmEct54p+6QBzcpM82RqBInjHTdrxCbiIwxSmdes9Rt44KXgMJdEMVAOFAS8RGmwtIciYREPK3hY3MPCHvYtomnCbkZsZaTi' \
			b'NdhcB0ajlYVZN2y6Ya6NfhKdJEw1UZXYXobNYNjCxdtRKR5se2FFCxNabOnihp7CYAkNk2FsgYTJMDY9Yl0K+zZggQ9Lc4yqsPyEtaeWwqGNgioK5ucYUaEtx54mVDSWtrAnEkalUPpiEF7XVLnYNeuxmxzbqmXLNdG8onyxnzpgu20r/8TOVd/EbegUxUg4' \
			b'thP3Y7T0n6hctXhG/x02EyMDbJSucbRBjZAa+5Jrz0cSrDr2IC/s6qV+aOWx1Zw8VH8rbITuQV8re/KHnHwxdy7VcOHNxHRLDKGCQZTgYVqIfu+UHqeFwg5rh0362CtdgwDZ/807muVlD47xIQmUokmy45SVndio32N7OV6gZFC2is8ziJS2+EcYJRWS8AD2' \
			b'44rjGhpJDXv5HU4CwBZp3k6NeqAk2zRv7DcnGVr14LqXVLF9nRLokorCxnkmEfQjcZAKXlCcQKLxv75/gIiEhQeQCcLDA97i3PTiN7VeNbzl8P+DPgsNRtZcZA2FtBK3bxZ6oF4gPwf7JqDnAPfXgDkHcQ7eTcDNwZoC1WwA5gZUltCoSNwz6rwcGyFAWgOh' \
			b'TfDJgSNYWYuTHB85LjZhIkdCggJIf0HqeTRGwtsm/Rt3r7qbdujf7O26OJeIc60j/K26uxAH/E1cF3KsgKojCMwEBxCpSb/nFBJDx0//JIY8zsggwv1dhEV/u74NWzD4WJauAJVQ6OciZGy5j5v0b2hUWoUQxcMuGjQBEzihemnm1DNy2pqBw5e66iNyKLF+' \
			b'+FsCI2BhhiIEJkDC6JBdjqi+8NfK2SzDO/qmYI7vEtghcu8ZeD1DjzNxcgn6blvPkdiP2APuBsxx8TPcCUtG7I1E9fOOqTMTHApFVOUcfdYrcdKKR444ST3tkSx6GJJu6pBYmp1/gDaApIWuBj2PFfD2CXzDAQG3jFpzG+CeMmjRWwTwELVZS6enHR6fZcSo' \
			b'lWepWwJdTjaHLvdSI3THhDPozrOekGFnxAHBgUHMnlnfqTDmrHq5OLmEmEIOYk6ohGJ9luE4cmhE8khcAcmS44BkjQhBqEtQjmwSMHPUSQYFMBdA7PIe+PAhfMZvEb8NizqKOAVvM4C3yd0i8DYl8DZT8A4J5+Dd6Bi8WZB0v3y3FrmNILcR5DaCXHl9htxm' \
			b'HXIlfo5cZU+C3IGyEnKbKXIlIkSgKSJXeaTIbQS5YwbbIdd/Scg99SEzZl+Bpz9+il4/oNfnbhF6fQm9foreIeEcvbOsJ2TYGXERvX6KXvgjdr1g1wt2vWB3eH8GX78OvhI/h6/yJ4HvEFiCr5/CVyKyDBThq0xS+HqB75jBslF0OMP4hGDMSiPoL9opjAfd' \
			b'rTxL3SIYtyUYt1MYDwnnMJ5lPSHDzoiLMG4zGLcjjEV9yxd54ELy/gzG7ToYS/wcxsqfBMZD0iUYt1MYS0TIQFuEsTJJYdwKjMcMlsG4PcP4hGDcsdzj1SmMuwHGXe4WwbgrwXiqDB4TzmE8y3pChp0RF2GcLcLAH2HcCYw7gXEnMB7en8G4WwdjiZ/DWPmT' \
			b'wHhIugTjqWJZI0IGuiKMlUkK405gPGawDMbdWSF9gng2rNtC/Yliy4hO2ohO2gzqLYmRuiWoNiX1lpmqt8aEM1TPs84psTP6FNgmU2+ZUUdtRLllRLllRLk1vp8D26zTb2n8DNiRRSOwx6QLwDZT/ZZGxO7Fon4r8kmAbUS/lWSwDNj9GdinCGyeNqPCZNqs' \
			b'R/fLgf58UWD73C0CdmnybKaT5zHhHNizrFEFE1LsjMCI7GwCbcYJtJEJtJEJtJEJ9Pj+DNnrJtAaP0e28ihB9hBYQvZ0Aq0RvZX4c2QroxTZMoFOMliG7KY+Q/sUoR0YAewY2kGgHQTaYYB2yN0iaIcStMMU2kPCObRnWeeU2Bl9EdmZOQf8EdlBkB0E2UGQ' \
			b'Pbw/Q3ZYh2yJnyNbWZQge0i6hOwwRbZEBLJDEdnKJ0V2EGSPGSxEdnNG9ikim5VkqCpRkrGBXCOXuhrNHCVG6hYhu6QqM1NV2ZhwjuxZ1jkldkZfRHamLTOjtkyNHY1oy4xoy8b3Z8hepy3T+DmylUUJsoekS8ieass0IpBd1JZFPimyRVuWZLAQ2WfDr5NE' \
			b'NuvNUE+iNzOiOuNLzRdFdpe7Rcguac/MVHs2Jpwje5Z1Tomd0ReRnSnQzKhAM6JAM6JAM6JAG9+fIXudAk3j58hWFiXIHpIuIXuqQNOIQHZRgRb5pMgWBVqSwUJk2xHZzYmAOzm9+ozxRpTJBozEPb7zYxjmfOEGPSrJTe4WKclLhp7N1NBzTDhXks+yzimx' \
			b'M/qinjwz+YQf3ODl6lr05WJ23YjtZyO2n2M6M325WQN3jZ/ry5VVib58SLqkL58agGpEyEXRAjTyS/XlYgOaZLAQ7mX7scn2pKNc+rqJ+dgt9ySthfUOIA2U4ktc+AzX5i7cclfHG2bTpS+ck2KH/tvm7vYbIZDIxA7UDf+zPnyW/YQUOyMwItsls+42sybj' \
			b'r4n2agTq1ArUcaM677/tBNBIauzCJce8C1cuTTdUIKiA6EnvbXlrRatUFbpvSTl23yQTSBGbR6QjH3gwQXYfHshSfk1Xy0j2c3Puw+y3632Ydp96t807z3gjvIPj0bmT0bmT0bkb0O1yt2h07krgdhm4TUw5h/Ys78wFBXhGYMdigpbLZYN0NyLcySDdySBd' \
			b'MD4mMQO5WzdIl/g5wpVTySB9SLo0SHdTmEtEbyX+HOVKsKJcNlMlGSzstWdGZ4eJ9PP0exHGLa+GoUpkNczKapiV1TA7rIZJjNQtAbgtrYbZ6WrYmHCG73nWOSV2Rp/23jZbDLPjYpiVxTAri2FWFsPG93Nk23WLYRo/Q3Zk0YjsMekCsu10MUwj4iir4mJY' \
			b'5JMg28piWJLBQmTP7ND2h+x4hsIZ33eFb14S4y+jC75lSczKkpgdlsRsyN0ifJeWxHpRnEN88f00iDdgzvVj5ytjcwpyguyMzAjzbGXMjitjVlbGrKyMWVkZG9+fwXzdypjGz2GunEpgPiRdgvl0ZUwjeivx5zCX5xHmsjKWZLAQ5mc7tVMEuGM7NdSB2Kk5' \
			b'sVNzYqfmBjs18aRuCcBdyU7NTe3UxoQzZM+zzimxM/oU2S6zU3OjnZoTOzUndmpO7NTG93Nku3V2aho/Q3Zk0YjsMekCst3UTk0j4iC6op1a5JMg24mdWpLBQmSfDdX2jGzV494TwnmSiioQ9RouqBYrCB80bBIjdYsQXlKwuamCbUw4R/gs65wSO6MvItxm' \
			b'CB/Va07Ua3yRBy4k788QbtchXOLnCFcWJQgfku5dvMtxbqc410j61hznyi3FuRWcj9ksw7mZWa3tb8PIrpXlW53utQ/4bq0Z3wlUWWMGRrqJJtwNijJ5lrpFIC0pytxUUTbD5izHSe52RlMEZqYVW8XTg5yrNh4g5NYpwTT5HIfKhQSHAyUblNwxRhl38jDi' \
			b'TlRfY7Jb7pY2M1uyM94ODG88u3XsJngb5rUu5G4R3krzWhc2422W4yR3O6Mp4i2sw1u4Bm/r5qyafI435UKCt4GSTXjTGGW8ycOIN5mpjslui7eZhdcZbweGNzbWgv6um+JtMNOSZ6lbhLeSmZbrNuNtluMkdzujKeKtW4e37hq8rbPE0uRzvCkXErwNlGzC' \
			b'm8Yo400eRryJ/dWY7LZ4s1/SBuRTVgJ5VgKByfUEl35Q/8iz1C3BpS+pf/xU/TMmnAF0nvWEDDsjLh4CW5cAqnNDL9ofL9ofL9offX12IOw61Y/GzwAb2TMCdqSsoPrxU9WPRoScF1U/kUcCXS+qnySDLaF7PoPrVKDLZ3B5/ozABLrDGVzyLHWLoFs6g8tP' \
			b'z+AaE86hu9ExdLMghe6mM7i8nMHl5QwuL2dw6esz6K47g0vj59BV9iTQHSgrQXd6BpdGhJwXz+CKPFLoyhlcSQZbQveLOoTrpKErsm7gJtAdrJnlWeoWQbdkzeyn1sxjwjl0Z1lPyLAz4iJ0zSboihGzFyNmL0bM+voMuussmDV+Dl1lTwLdgbISdKcWzBoR' \
			b'cl60YI48UuiKnWOSwZbQDfOD01PbR3ckpsy7PNCWz0PEXJeeD4e1pyjvdmTpvC3azfaIn32JYSvUtxvOfYdwtXClA+D9sE1R4qTu9sbQfrpPcUy58F0GLoMvkOFlm2IeBFNJVm37dlPrIHsVvexV9LJXUVOYn86HSWuYfqIh2bxYPGxe08pbDmXg1E5aQ0tN' \
			b'x7iLEVLAzUdbxcPofXErI86kj+zUNkS2M448ytsQDuZfvkdzgkuAjxuTtrq6k28w7PADDOEaTOdYzjB87RdUNuiqho8x0LO1X0sB/w/sewx7+BaDu833GK77Tsk1XyeB9G/8KskNPkdChcmRUO8LDOgo/YF/kwRfeLrFd0nW9U1rvxJ0V98laY7k2yRg9i2+' \
			b'T9LPpHk+OtyhNLeH1MAvadyva9hlW9IRSXe7B+luuGi7lvAtpFsGws0g5XEwnEk7sfCaUcwwEdrt9+b66efk2vLn5JbI/7aTli0nLBuxgIFgt/sWfuE34O7kS1TNuB0DfFq1Rd3gYmykJ52s/4Lbtl9v24ATIbq+YW9AiW81ync7/tgaVdXyjyvuenyzabjf' \
			b'bNkr2N2gIEHAXX5/Dby54WcMdzvWgQ5k/Xin3a5HCOvG/L7BmJ4/8GS2k/d9dAYBn1lW8Q931iUs0GFt7BJgsx3utmu4324Bs0gzdg1YiLV32T3MV35v0j2sDAoNjpmbdhMEIOvxLU8GkN0aQLvtMPxdgua2gKnvfhylYGmXWRDuoAdBZn6n4GjD0t4Ex1Us' \
			b'AEbDObS3A4Xx8n1bY+Tq6gEjbjuMhF1jJAKE6L5bzdGBzzHuCRspLsCbu9coLcTF7TERZljw22Gh3RcWiFFnLBwaFuyXgIV2hoWwHRZ2N+fIsdCcsXBwWHBfAha6GRbuankZaxDR6GRHKxE4i5GeYZVwX2tsWy837w4F+0dAOonf6UqELEk2bF2znzW3kv6p' \
			b'YS5tM31uaVgUeC3ZzteS9yb20Dn5idppv43/Ooupm2iZ7q7xvyNtEtLpUo3S/ht9fPKvpEW6ifbotlqjvro6ZEOiPVtMTFpzc5MW3cJ+8iAk+lYNd4hu/600rCYLVkKh3iCxXk2DaOQOm002DXJiGoReBiZBXc+fmK/P8nyjJvqAmubbj0CyZhg2vXdqA7Gm' \
			b'2cVgu69ZTJt9ianZKKk+N9q+I3m99qjpbQ04A9uWHJT8snU7/V8nwxwnN31eLMs3bJevOfl5C+tNHOnNp7hzMWYNtH1AOGbRNmfRPhnR5rOy6utFm4X1eEUbGUO0mbANom2rq7Yad941LMkNy3AiwCq9FiLap6qIXiWqIEmQlFQ6ukA1j1pItodxFQet28aV' \
			b'63SoT65L1BX3n+mGKp6CFJgJZqUMCg6GSETdokKP6BRctrqBbwsmRMjMNtiBGSxvt2FGw7FUgIPyRV/YjkF+ziM3sMkvZJMrcsoeDrcyyE84FlF8a66FhVyb9wFD679d078NZ69r0oubQOPIutkN9xv+nzW8ITa4zZLGdptquq4ZLTSfOtIlYqbNZDur1Pub' \
			b'da3dNLwn/e/6GVZBJsr9dW8OYyZV3IS701nTXJbm3a91NNeXSVN3lqut5Ko98Cl6+jmbnqm9D8GCeRBX3oMV6ot80nr1ZynbSspQ8UciZdi+Xh+UlFE2qZTdu3LyUAWtPQ6l4yF0lZCq5oCl6o4W4IfzGLpq+hW6TVJm70/KOO/F3abdoZy1G8UM+ynHT7xd' \
			b'92U3qjWVwINZd7lPIVwneCHpSo9kXSVt4va3jrJdM2erK9YHEEP5A4R1x8FOg1nr1vJEfFSF8bS5k/c9n7jtEQOf3KW36e5ixcc2y6k8ps5P39l8Xg7vkcMOhmhsES3sgCA5Kgbfs8UZAth43WGfHezBo5PjcML0P7Vn0jB5DSJG+eI95D2+g9KtzL6LQene' \
			b'5I+Js/smjlqWwh8MZhIf71fveKfhJJbsJWdC3b4JddWN/pg4v2/iqL2d/WHZxA8LJ6UYnpc06MpEhn0TSVFv8sfEtVPiZodtyfH248lZm0/Lmh6VhVaf98w6PQark0XCUoEmRzKH5Pgpmxwx1abHSv2EHlb+qI9oq8STurbwl0XhWOV3SnGycGZjt+86ptbx' \
			b'Jn9MXL/fOtaPi86qual3WNUYxezPuW4W5NubJcYcb+q9d6Gu2rUTypPOH31xuwORwbeL7klqQiVOPp80eG/uMHq+fSprndTBxpGLHA23GaFrZQjcm8oRpoZlx1zc6DCNmIe2Y6gUx56SSGESd0xOqmDjKG4biRJWby9XmOjewsXZ6cZYUjR/UtLVV0flpArC' \
			b'NQOM7QVMuL2lmBX4B81KdBQh9S5yUSNyTaxMr8HMaE9JHqGmOiYnVdAdjjya6j6csKE/KUm01VE5UUHVhyOJrroPJ2w4qUkFuoVjclIF5giqYPhM7NZV0VWH5hrMM4ktG2NJldgdNw79polf2KaN6KsdOlRtITSsfUO44k5RULEec3xOKsRvpz7cmaT6qbSC' \
			b't+v5aqoNrrebnm7v0nRKaQqfrpsF3SuffHUATvi05ZLD/fCprQ7ACZ+um8Uc9NIMvjt+nRNzBfnfJn7+OqwSYhLer49HpR4znD0XZu95jWS/zIZxyEE7WfK+bjJ02Dx21WE74XFz1Dz21WE74bE5ah6H6rCd8BinuMJQrFWeu+jX5zi1D2pahzD07BoPJ5gl' \
			b'VUF8w+K55xMna5wv1ojt1IrPd5rHDFXiJGI3i4gqQOS2Sl0TpOPms0SiWRWM8SQdHMkwyMRQty2Mt8R2T+32op1dJ8NKbJGX7V5cjbxmxzujjFR8r2Y6JJRNB240Hey4Lv8fBBRguw=='

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

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY - {'@', '#'})))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LETTER})'),
		('LOG',           r'log\b|\\log(?!{_LETTER})'),
		('FUNC',         fr'(@|#|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LETTERU})|\$({_LETTERU}\w*)|\\operatorname\s*{{\s*(@|#|{_LETTER}(?:\w|\\_)*)\s*}}'),
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

	def expr_lambda_1   (self, expr_commas, COLON, expr_lambda):                return _expr_lambda (expr_commas, expr_lambda)
	def expr_lambda_2   (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1   (self, expr_paren, MAPSTO, expr_lambda):                return _expr_mapsto (expr_paren, expr_lambda)
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

_RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
	p = Parser ()
	a = p.parse (r"Matrix([]).transpose")
	print (a)
