# Builds expression tree from text, nodes are nested AST tuples.
#
# Time and interest permitting:
# sets
# assumptions/hints
# importing modules to allow custom code execution
# Proper implementation of vectors with "<b>\vec{x}</b>" and "<b>\hat{i}</b>" variables
# sympy function/variable module prefix
# systems of equations, ODEs, graphical plots (using matplotlib?)...

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
	ast = ast.strip_paren ()

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
	lhs = lhs.strip_paren ()

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
	arg, wrap = _expr_func_reorder (rhs, strip_paren = 0)
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

		elif ast.numer.is_pow and ast.numer.base.is_diff_or_part_solo and ast.numer.exp.is_pos_int:
			p = int (ast.numer.exp.num)
			v = ast.numer.base

		else:
			return None

		ast_dv_check = (lambda n: n.is_diff) if v.is_diff_solo else (lambda n: n.is_part)

		ns = ast.denom.muls if ast.denom.is_mul else (ast.denom,)
		ds = []
		cp = p

		for i in range (len (ns)):
			n = ns [i]

			if ast_dv_check (n):
				dec = 1
			elif n.is_pow and ast_dv_check (n.base) and n.exp.is_pos_int:
				dec = int (n.exp.num)
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
						tail.insert (0, AST ('diff', ast.muls [i + 1] if i == end - 2 else AST ('*', ast [i + 1 : end]), diff.dvs))

					else:
						continue

					end = i

		if tail:
			tail = tail [0] if len (tail) == 1 else AST ('*', tuple (tail))

			return tail if end == 0 else AST.flatcat ('*', ast.muls [0], tail) if end == 1 else AST.flatcat ('*', AST ('*', ast.muls [:end]), tail)

	return ast

def _expr_int (ast, from_to = ()): # find differential for integration if present in ast and return integral ast
	if ast.is_diff or ast.is_null_var: # null_var is for autocomplete
		return AST ('intg', None, ast, *from_to)

	elif ast.is_div:
		if ast.denom.is_mul and ast.denom.muls [-1].is_diff:
			return AST ('intg', ('/', ast.numer, ast.denom.muls [0] if len (ast.denom.muls) == 2 else \
					AST ('*', ast.denom.muls [:-1])), ast.denom.muls [-1], *from_to)

		if ast.numer.is_diff:
			return AST ('intg', ('/', ast.One, ast.denom), ast.numer, *from_to)

	elif ast.is_mul and (ast.muls [-1].is_diff or ast.muls [-1].is_null_var): # null_var is for autocomplete
		return AST ('intg', ast.muls [0] if len (ast.muls) == 2 else AST ('*', ast.muls [:-1]), ast.muls [-1], *from_to)

	elif ast.is_add:
		if ast.adds [-1].is_diff:
			return AST ('intg', \
					AST ('+', ast.adds [:-1])
					if len (ast.adds) > 2 else \
					ast.adds [0] \
					, ast.adds [-1], *from_to)

		if ast.adds [-1].is_mul and ast.adds [-1].muls [-1].is_diff:
			return AST ('intg', \
					AST ('+', ast.adds [:-1] + (AST ('*', ast.adds [-1].muls [:-1]),))
					if len (ast.adds [-1].muls) > 2 else \
					AST ('+', ast.adds [:-1] + (ast.adds [-1].muls [0],)) \
					, ast.adds [-1].muls [-1], *from_to)

	elif ast.is_intg and ast.intg is not None:
		return AST ('intg', _expr_int (ast.intg, () if ast.from_ is None else (ast.from_, ast.to)), ast.dv, *from_to)

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
		ast2 = ast.commas [1].strip_paren (1)

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
	elif commas [3].is_eq_eq and commas [3].lhs.as_identifier () == 'dir' and commas [3].rhs.is_str:
		return AST ('lim', *(commas [:3] + _xlat_func_Limit_dirs.get (commas [3].rhs.str_, ('+',))))
	else:
		ast = AST ('lim', commas [0], commas [1], commas [2])

	if l and commas [-1].is_null_var:
		return ast

	raise lalr1.Incomplete (ast)

def _xlat_func_Matrix (ast):
	if ast.is_brack and ast.bracks:
		if not ast.bracks [0].is_brack: # single layer or brackets, column matrix?
			return AST ('mat', tuple ((e,) for e in ast.bracks))

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

					return AST ('mat', tuple (rows))

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

	if not ast.commas [0].strip_paren ().is_comma:
		if len (ast.commas) == 1:
			raise lalr1.Incomplete (AST ('piece', pcs + ((ast.commas [0], AST.VarNull),)))
		if len (ast.commas) == 2:
			return AST ('piece', pcs + ((ast.commas [0], True if ast.commas [1] == AST.True_ else ast.commas [1]),))

		raise SyntaxError ('invalid tuple length')

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

def _expr_func (iparm, *args, strip_paren = 0): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	def astarg (arg):
		return (_ast_func_tuple_args (arg) if args [0] == 'func' else arg.strip_paren (strip_paren)),

	if args [iparm].is_fact:
		if args [iparm].fact.is_paren:
			return AST ('!', args [:iparm] + astarg (args [iparm].fact) + args [iparm + 1:])

	elif args [iparm].is_pow:
		if args [iparm].base.is_paren:
			return AST ('^', args [:iparm] + astarg (args [iparm].base) + args [iparm + 1:], args [iparm].exp)

	elif args [iparm].is_attr:
		if args [iparm].obj.is_paren:
			return AST ('.', args [:iparm] + astarg (args [iparm]) + args [iparm + 1:], *args [iparm] [2:])

	return AST (*(args [:iparm] + astarg (args [iparm]) + args [iparm + 1:]))

def _expr_func_reorder (ast, strip_paren):
	ast = _expr_func (1, None, ast, strip_paren = strip_paren)

	return \
			(ast [1], lambda a: a) \
			if ast.op is None else \
			(ast [1] [1], lambda a: AST (ast.op, a, *ast [2:]))

def _expr_func_xlat (_xlat_func, ast): # rearrange ast tree for a given function translation like 'Derivative' or 'Limit'
	ast, wrap = _expr_func_reorder (ast, strip_paren = None) # strip all parentheses

	return wrap (_xlat_func (ast))

_FUNC_AST_XLAT = {
	'Abs'       : lambda expr: _expr_func (1, '|', expr, strip_paren = 1),
	'abs'       : lambda expr: _expr_func (1, '|', expr, strip_paren = 1),
	'Derivative': lambda expr: _expr_func_xlat (_xlat_func_Derivative, expr),
	'diff'      : lambda expr: _expr_func_xlat (_xlat_func_Derivative, expr),
	'exp'       : lambda expr: _expr_func (2, '^', AST.E, expr, strip_paren = 1),
	'factorial' : lambda expr: _expr_func (1, '!', expr, strip_paren = 1),
	'Gamma'     : lambda expr: _expr_func (2, 'func', 'gamma', expr, strip_paren = 1),
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
		func = _FUNC_name (FUNC)
		xlat = _FUNC_AST_XLAT.get (func)

		return xlat (expr_func_arg) if xlat else _expr_func (2, 'func', func, expr_func_arg)

def _expr_curly (ast): # convert curly expression to vector or matrix if appropriate
	if ast.op != ',':
		return ast
	elif not ast.commas: # empty {}?
		return AST.VarNull

	c = sum (bool (c.is_vec) for c in ast.commas)

	if not c:
		return AST ('vec', ast.commas)

	if c == len (ast.commas) and len (set (len (c.vec) for c in ast.commas)) == 1:
		return AST ('mat', tuple (c.vec for c in ast.commas))

	raise SyntaxError ('invalid matrix syntax')

#...............................................................................................
class Parser (lalr1.Parser):
	_USER_FUNCS = set () # set or dict of variable names to be translated into 'func' ASTs if variable followed by parentheses

	def set_user_funcs  (self, user_funcs):
		self._USER_FUNCS = user_funcs

	_PARSER_TABLES = \
			b'eJztXfuP3DaS/mcOiAdQAxKfkn9zHG/WOMfJ2k5wByMwnMS7CDavs53dOyz2f7/6qooU9epR93TPdE8aw2lRlPioYn0ki0VSD15/8vjLZ18+/6T65ItHX7189SV5/uPdLz/Q5dmTP72iy1ePXjx5/gzPnz7/+iVdnz5/9TkeP/2Cfl9+zb9/eYFXn32JB3/6' \
			b'+vljunz66AVe/vz5ly+evHn89Ytn/41nLx491kujV4N3n3z+5vGjl09eqv+LR6/U92nv/ab3fiVeThVF+5TS+U94Xr56wYX6lH6fc9G+4WI8/vKLLx4lYl6kqC9SVHhePP38z0j00Rdf0e9nnz57+ezRyz+T98nzz7RA8H3ae7/pvVqgJ3/Bz7OXTzQ40YTU' \
			b'XklBqAB48+mfmJMc4atnzNfPnn7z9DPEfPzZl6+YlkdKDFj16BWT9uS/Hj9LySD4qxdPv+AsuOa+f/v+3cc3v75/88N3P334+PY9Bb3739/ev/n57cc33//6U3n7/td/jm4/pPvv33549+HD98Pb34a36e7D77+9y9n89fdfvn/z9v3f+offkfcffTl++f3n' \
			b'5P347n32f/f+7fd/f/cx5/D7+5/+ryjcIOecF8VJ/t+I7F/Szdvv8jtvP37sy/b2+5zQbz3tKHJf3Fyiosw//ZhDf/wlJ/Hz7z+9+fHnzJQffvxH7/3rXzO97/5WRiBPLtoPP/SpvvufTOKvv/zQU/7bh4+//n14m0v19ufvfnib7nICfTo///x2cPPhk2+r' \
			b'1w82zlbOXFXisfDYauNwNa56YKvGVBRiDXmuUqiE9QEb4+Fravlxodo0zVUZ5MsQeBHRyo+XB+SjtLgANTLGfYOMrTxHqIblgI2VlCKVKdJdrJwmRnem5bciftrKuiu9pTv2dUyrpSTt1SBA7toUj553KQheJM//pk1RwQ8mTsOFUiqCBvI9Euwqh/QqV1eG' \
			b'IvnK1nPPNn4cqvcbyZ5KiuhNik4BxA7ODBxiLjZOfhxR3Eh6RZAvA+GFBNA/lahL2Tt4kLqRH68VTjkbJtcE4juqH9yOVznIl7dNUA/C4KN6RHElD7lDvRLnm0EwJGV864ZBzfQ2lEEbw/JhUaBafQ/k5op5K/IKZqQQ+BBMdATNMOTHGtrfbRqmyXM1U37h' \
			b'Sm43TDTJ5INYGc913bSV90wmECCsnH+BoRjWvedHr20alpAABFHZIwBkRHwpjEPy7SbqlfEQmYYGd8y9VkFI2W1IJIlzPRbxMIf3IZ2EhByCKkBI7EMaCcmZkOyyrBn56eHoEqhcIz+oCyeEuoa98NXp4ZXe0l16IExp5Me1PZ9SUFcGwQuflx+q3qur3guf' \
			b'YeFppHxoBBtpMInFIuRe2d4UbEcgBxX3hFIj7WqdwjaaRCM/m8RFtCJcLiL/gb6nt14klaS4LWQD+BUhY8FV8rqMAIiByRDQWz8MsH02ofJCJBHgkserh0hPvoaFqOFWk8RSqgMyYiU6URyvqMd5XXNZA91Cuqj3oMJyqUNdhaYKoQqxCm0VuirWaGOpcSNq' \
			b'KA+Seh+qWLVVV7Wuan3Vhqrtqq6GbEBACTT0mBxBhNo4+qVkTRVsFVwVfNXUNf03QBe1gSQRJAGeeidK21RdqLqI1pfEiVoFyAfxhQLpka06V3WeusoK4HRoM0gwqAWITRVNFW0VXRV9FQPDhPtNqmVqHZua2sA60n9L/1RaSp2Tx9WgD6YbYlGQS8QFocQl' \
			b'3KMFveKeD8EPiF+4xR29Q4zju04eEvs4OEgceZWKz+nyM3TdkjwxmZ9ySnGHSrn/NfIgCFtDJ+w0cms6YbbUk22UkZb5e5HpoUx7kV4vkiiy1irHhI+tiGfrNbTl4DMm+kErxHa1glOhKpywIcmLMoMvZ0RcK1R5Kb7n247Etrt30vvAK/CDNJ3BysVJK8tR' \
			b'0ZTWIsjB622tV22FnbbCUtHoE0+KytcYhVxarglXnLT2ruurTcT8tIrpRdp80xezqSl6TfFr+P2pFVjA1DEqRkXlXkFQ5dL4x+mApVbUKaoYbEMhzRI8GKawNP8hZPaB9js63vPa/DC/D5WFS6nag6bqJNWGUyf1lRQG0nhIkyGFhZTHSz0P2NUEYVfkqm2b' \
			b'qjVVS+kRkXUVYxXbC8dGrU60F1atZZW7sGotq/yFVeuarCh9k5UhdOO0Tw96lbFWp307R0V406RO3+hInJh1tW00mhktfFQWMzdtz0+pGuGqVNAZ8/Y15oqIK/dfingyzMgsmLmM/sbMIW4AHDtywyo/hJf3jyvEACPTn+YywTlRci84mmlOG5aYhiXmMi0y' \
			b'glNk5oQ8ictNsZgr1HjxrcyVG5krNzJXfpGzaXtthJUjg4/nPu7+kcuCc58Iau8dQdwd3AdC/L0gBLYww7Nt2yy43WX6fq5xFU3B8ujvzEoPo6BRI5uZnST30r2O7KmtatMcfIxydb1BzIhBzIhBzIhBjLt5GLxEamWoIOYl20uoSKbI6R9UPh94XbnhGdqn' \
			b'VDS2B07HJbCHSa1ym3R6dkxYwgQ0zWkWkBhbG0WoPcFar92xmg0YIdXmZ8S0Z8SiJ/UlmoJLC5JGw+HuoqPOKe7cAh9S5S3GFLDucQ15qaFGFzro+iedlDU6J9vI8gcj9ab1CNsUx20l5VbHLl1a5aO1HPU+tsPYqlU6uYiINElixsomebC4MGjBIt++xiyh' \
			b'LSULEoQhwWCxHE8Q2YFGa/h+nIkbJkYc47cuJrjVDYzwddStEC+srD+0usbOyryBlXmDgulQmPkl4pCdjH4knclqsplQ3Fq55eS6y0TPTHV1c6MAHlfb81u29hqKgD07RYA1AHv/JoOgqhhVJKwoElYUCbpMxiX1TKiLg5bBu6RqWFmzZWVNlOVxhnZFGHaZ' \
			b'0xp28agLJU9N0aCXQS9vpR+22g8b6YDR919Wxsx1MjLhbC4TzjM2eO0+W7FvRGbVZawyOx6OF/mZyo+0rlHaqCgDAWKGk7lJx1tN3JUMjt2V6gDfslrhdHDnZHDnLnbqyXhrbnjM4xZ3juMtKqqbjNGDSAkV3Ul379K8odMJQ3eKMzc8crCytNZJB2xV8x3q' \
			b'hHLfK7XDQQqJuBeoeIaKV6j4K22bBSpeoYJg2VR0gcpoFVAnzBkr8sJYKrwX6fKXJnxuNH1hyxjf2AgvlrWg4Avz8hVEvoLIV0jgroiHibuhQDxKhtsWF04g3gOz5GuwIAoLIjdaMnen04FU4jhjtAL1rbCvlbhter29L0zp7gch7l4QwqLVicTxYQ7YuFdf' \
			b'yU7r1zUwW1ktCtozKVqffNCNKKJoG4PmUFvKlptDO+AOtRYg0SgRs5yQoY00oj0fmwErB1ONnvWzLk0wB60DqhiiFsyLuiktVUAPu6DcIEpABGbpMUWP2XvM3GMjOZopbC/H3nJq/RtscMbuZmxtxr5mjD7AcexgxfZV7F3FtlU0jGgVsUcLuxuxtRHb5bBX' \
			b'DvvRsBkNBk4YN7EBGLt/sV8Um0WxpxJjXEzWY18lKgcVAyGCFQIT6tisgV0IMArAYgAbQkthmMbFHC422GJAjL2o2C6MnbaofSyQwGoIbH3C/jJsJYNRvEMNUs1R9Rqs6mssCQFOK/E4DgEnkvCBKzj5ZRMaOceEKmATcISC3hMNOBWkxSWdQELBVISN59NC' \
			b'cOZGjQT4FJEUy9DrseKDKpqUMgXROzhtxOmhKU1Ih6f0/xHHjvApLkiPTxvBuS+cEP8YfddP44ZWSBMKW/FuWhSo1bI6zRIiifM6QAdOECE+bYh3fIJGUzNrNKkNHwfh5B+yhXCqyk3Ea2Bf2+fscu4kzJtOY1qcdeNx+AjOsKHq3LQ+v8ins+CsGSSPU01w' \
			b'AA0orXGgRY0n8gKOrWgKqqMp/BQx4niTIl2ixnPt0LPO9TQE1ATFdZJEZmjXJ4dDc2zXR4moQ5DJRcJBL5RmcN9W/wrNww1jqH4IGSKMPdwwvuxDpEB4eoiTikhWcf9vzOpdGqFLI4RBd31vGyEmTSi8rhHCO9saIU1q0gghfKYRCnVuhPiNNY1QqI/TCIX6' \
			b'dBshg0aob4JyA7Sm9SmbnrLdCYsNDZUJrUnZlLTzjUiQBmPSWKxoGLhB2NYYaEPADUAJ/DHgS6C3CnB7DZjnkFyieHcEj9E7Qi5QuwqlXjA4wZ+3W4AHtAFlU4gpoPh8qVlAAUlbUZQQBLEvETOBSgERpqQTSCzBACo7pLrlbtSpOjEQ5GYsy/3UmVnoUpuB' \
			b'irJDx1pP+tYWsypj9YbNMD0ybN/PtqzalMqSKFQlXJKenWATFSZmvt9kiBAkcDYAdvLPwsVMIbOq70wwigWU5vrLsq+kGsDiUUCqhp+qCYt9BvAiDlWQOqiCJYD4tuXLPIQiZqzwEyZoyj0hS75LV2wZBbKi/q1BWNR8+r8wcEBfFI9AUMDWMQqlD8RDp5TU' \
			b'Go3fGuMyajkVnQmLZoTBogybrp2HYwwTRArFRq89MqX0PmocReew81J+KT7xYjBFKYbdVdM9ROvXUi/FirxDt8QtMV3Dv3mS/HXN042HhPIeo+OVIA474ngK4vsM4BbsIz4whuMQw9IH4rKAYQgBmDsdz7bjPrFl7Lb6twa7raTf/0lO2QG74LuUcNCFKoBb' \
			b'AXAUAEcBsMQdg7ftgdsuALcowDJw4wS4Qq7Raw9cLVEqzixwlVkJuFGAG3siZoA7A1jf97yzQ8iTgusyVvcD6oKWymDdBtTbBilVAtZEYTnUVsA2MhfrwbWFUSsGcPOIRe4evxh1jiCLWEPMyumqVc6RB4bXA7d8f4vbSGHQZAK9LPIFeJkIGQZzYWspvJli' \
			b'tyl6XfgVvXEM4EYGwPzKAn7H4E1Em+zrAdzIsBjQ7hYR3KehIMbyba6WCgdTh/KNIZxbUgshdNHRNQLGYdcB9CGnovZDbwndiTq5b9d6aLQesjtFJbDbdPxboJNv+QitBXCaqWJpJrolQqjicz64X4HJ8v0tDphMvpFOyqXbopby4dGKQqZ/rg8d5LUGgIlC' \
			b'k309AFMyy/1nn5eij/lZhq/tQuMFe6ePPT4SHZMhcmh9iT0r2LOL2LNT7NkJ9qxgz/ZuFfbsKsfYU98Ye/Ya7NkCe3YJe2Veq7CnFJrsK7CnyWzBXs4rYc8K9nL4Wuy1F+ydPvZiJQ7YG6qRRgalZlGNnDGHTK0hagzJ+aw0hJTvb3GMPfWNsRevwV4ssLc0' \
			b'6TPIaxX2lEKTfQX2NJkt2Mt5JeyJ6tiHr8Ved/hJ27tQHf/w0zw484fdRn5LfHaCz24Rn13vJkDtJkDtBKhlpDVA7VY5Bqr6ZmZ8uISWL05JqtP7E+B2BXC7JeCWeS9pjZL6EL9KuMm+Ar/KyagR5yGcc00Q7gTCXU/POgg39QXD9wLDqBB2hGE71C2t6JZ2' \
			b'Ube0hRtj2E6UTCtK5iDSCgzbZpUDhpNvBsNWFE1cnJJUp/fHGLaF0mmXlM5B3ksYltQHGE6Em+zrMZw4GTXiLIb7XBXDVtTPPnw1hpsLhu8Hhk0lDhg2QwwbwbBZxLDp3QTDZoJhIxguI63B8DrHGFbfHIaNYNgIho1gWN6fYNgUGDZLGC7zXsTwdBydCO9Z' \
			b'UGBYORk14jyGc8yEYZm27cNXY5iX9ciSnji7rvDEYX0zQ2ozQndaRGR1heHK1YXHQj1OGllE/trVhWkR0rWtQCzXImGHfRysSMKtLEqyQ106WXjsojINQUhu0khMtGorWvUg0ppGIq5yaCSEOLtgobWiXFsx0Vox0er7UzOPlHey/MlKzGtXPzHXfUp+sRGZ' \
			b'mnATY0z2FVagVqjQBVK2VMqnywjx2HQpmWLBlBUFvWfdpFXRRgUXalMsW4SaI6ypugwL7mJY0FXiNvJbDgtEPbeL6nmOa6fquZ2o51bU80GkNYjvVjkeFqhvDu6inltRz62o5/r+ZFhQqOd2ST0f5L2I6Kl6ngg32VcMC5STUSPODwtyrmlYIOp5H756WODu' \
			b'LYZnV0TeZxhjQSo7fBl6qKE70dDdoobuCjeGsZto6E409EGkFTB2zSoHGCefwJhpEhA70c+d6OdO9PM+6hjHrlDR3ZKKPsh8CcduqqInyk329ThOrIwacRbHfa6KYycqeknPbqsjG3/B873Bs63EAc9Di7ITi7JbtCjnuG5qWnYT07IT0/Ig0ho821WO8aw+' \
			b'xbPt8SzGZSc2Lr6ri6gTPBe2Zrdkax5kvohnO8WzUm6yr8CzsjJqxHk851wTnsXqXNKzI553XnZ1wfPJ4tlV4oBnN8SzEzy7RTy73k3w7CZ4ll1Ag0hr8OxWOcaz+hTPrsezEzw7wbMTPOeoEzy7As9uCc9l5ot4dlM8K+Um+wo8KyujRpzHc8414dkJngt6' \
			b'dsTzzku5LvuQzgDZvhIHZPshsr0ge3FRdI7Lr4yQnRdFOwF3wrcsjR5EXYNvv8oxvtWn+O63JTlZGM0FUbLqIuoE31rmBHG/BPEy/0WI+ynElXiTfQXEladRI85DPL+XIO4F4gVJO0J85xVjF4ifAcRjJQ4QH06LO5kVd4uz4jmum86KuzwrDp/TiyTahGHU' \
			b'NRCPY4fqmIYyxtWnGO8nypzMizuZF3cyL95HnWBcgjPGl5ahDfJfxPh0AjxRb7KvwLgyNZVsHuM514Rxme8uSdoR40dYmXbB+J1jvK3EAePtEOOtYHxxU36Oy6+MMJ73I8Ln9CKJAuNl1DUYb1c5hrj6FOJtD3HZncgF0TLXRdQJxCU4Q3xpl+Ig/0WIt1OI' \
			b'K/Em+wqIa/miRpyHeM41QVyOAShJ2g3i5ggL1y4Qv3OId5W4jfyWEBdTl1s0deW4bmrqctnUBZ/TiyQKiJdR10C8W+UY4upTiHc9xMXc5cTc5cTc1UedQFyCM8SXjF6D/BchPjV6JeJN9hUQV55GjTgP8ZxrgrgYvUqSdoT4Eda1XSB+1xAHn9ltmOclxPm2' \
			b'5cs8xHNcfmUIcQQJxOFzepFESXAGUVdAvHx/iwPEk08gzpQJxLmUVgqiZJVRxxDX4ARxTmgO4oNEliAuGQwgnog32ddDPPE0asRZiPe5KsSZ52ZA0o4QN4eFuO3uCOX5ZOUL1guso1rZbTr+LbDeyILWZnFBa47bTBe0NrygVaTU853TiyQMKSqjrzmXYJ3j' \
			b'cwnUJ3hn6nCqIWXN81RBSmylQEpiXSQxWbsmwfmUgqVlroNyLOG+mS5zTUzo2VGuUJOagagsr3Pts00HFcg615KmHYFvj3FO0LFxv+si10XQ+3sOfCKI8kBtcT9vh/28lX7eLvbzlLfEtdN+3uZ+3ko/b6Wft9LP53h2XT9fvr/F8WrVTJFC3/ZdvZWu3kpX' \
			b'b6Wr72NP1q+xC8XUu13q7QelWFzFNu3tEwtM9hWr2JSzUSPOr2LLuaZVbNLbl1TtCPojrGa7DOjvGuvgLTsM6Id2cy92c79oN89x/dRu7rPdHD6nF3kVA/oy6poBvVvleECvPh3Q99ZzL9ZzL9ZzL9bzPupkQC/BeUC/ZEAf5L84oJ8a0BPxJvuKAb3yNGrE' \
			b'+QF9zjUN6MWAXpK0I8TXLXCzBcrjBejnAXRUGTtsEx8C3QjQWxnNt26E9TZtFuc3W27jJ5vFM9yNwN0I3I3APWdu1sG9fH+L4y3j6hO4mx7uRuBuBO5G4N5HnewZl+C8bXwJ7oP8F7eNT+GeiDfZ18NdQ7BtfBnufa5p27jAvSRpR7gfYf3bBeh3DXRwlR16' \
			b'9DDs0YP06GGxRw+9m/ToIffoQXr0ID16kB69jLqmRw+rHPfo6tMePfQ9epAePUiPHqRHz1EnPboE5x49LPXoZf6LPXqY9uhKvMm+okfX0kaNON+j51xTjx6kRy9I2hHilyVxO0JcJoLOBOptJQ5QH9rUvdjU/aJNPcf1U5u6zzZ1LzZ1LzZ1Lzb1QdQ1UG9X' \
			b'OYa6+hTqvU3di03di03di029jzqBugRnqC/Z1Af5dz0/5gA/tawnFpjsKwCvKUWNOA/4nGMCvFjWS8J2BHxLQ71b+75EWPt9iWb6cZrZD9OEHb45ERZQmhDqq/XfnqB4Sx+byd+hoPBrPzDDX5Jxp/c5iiDw2vFzFGlAXH4AZu7rL/JlFV2atvzNl50/9nLt' \
			b'pyq2fdVFbdnrvuSyyydcuhJh7S18w0W+DjXzXajDf8wlf+FpG7AWQEXFbEKcAVcJqhJQSyBa83mmu/ywS+Lk8keWjvSRF8503w+9pHq48Qdfqn+FQGBpAQYq0Fx3Y46Jhu4UPmq0S+cykv98vsiWToXKjrPEr8fFzT9ZdkBc6OlBp/PRI/B//w8fxYyF/uyX' \
			b'YS+ShuWTYZpPvQXVy77jsfpAn/za+vXAm2LkukHYEkbqHfoJt2NfcbN+Yu4TfvtjYh4PevJso0uEj4GLhr9Bslc/0a7uI1Av20ZVLmA0xTgwt6mXNDzH4G/aUWAc6FUraXc8yGofUJhrQDHWSG4PFAcERPrM4uE6ijzy5JO+6jUAQQH2Hkgh+S0AQYO1ciBF' \
			b'IoaRFKr2IWXDQLHV61sByQ7YQDHsjOZ+qMHU2oGUmdHSV+Hh1HCwl+zLPCNksR3h4Ja/ECmFiDsrDpBud3LSrZ+z52WEtyHlebZ4m6TXOif1R5d4zC0ZnlnftPXxJd/UayadEBt7LLq9UeAPjALK7wDNfHMNCOIRmvtmNIfUnWuz39pjAoE/6W22gADZH7gL' \
			b'IJkZ6gVzw54bgCAcGgTtIUBQAsDfwninuQ9jnqMKfyn44NXRxz4jwT+o0MdDC313aKEfK8MXob97oR/b3s5M6NtDD/qX15nsKfTxIvQnJ/T+vIW+uyVNd/0ijLmW3d3SFE5YOaXptws6GH0yOu1+iyrGs5hBUzr+BA4Wl83O6OuaCZSEKplndxanLL2si8jr' \
			b'JbBOopX1EYYtXkTnqU3x3Omk5Uk358drypeabqyIPPYE5e4rGnSdD8tvc3Lyi6V+eZrymFOT5WLWNdOTf0zZbljWZGryqEOUJu44Jbn7MIWy2kfazQ0Evh6u7D5Cs22P0HSPByqhEHN3TFHHKnd/SGFH1Czvurx6//b8Gjlf2j5xozZ9tMbT1P2IBcRNm3dL' \
			b'oxTP5lW3n3n1Iu+3J+8B7pDyHu6dvNte3sM18u6q16cwhEGmeR/OMYfbY/m1updmslK/Pbdhh4hk2sZyzOHzSOzSEGJu+OBJvE5Ktu5artBcnKtMnYA8hVOTp7toqxoe0qCZn5Gv5m7lKzb7ihdiHk7CpBxbBcwwJdRNznWRLSn80Hejoyt/cpFivT4hwbvr' \
			b'hqyQMqw4uDRi6xqx6l9N+5BgyRLVXiSqbLrsefaL2Jpu71akqJGCMkgXrDH3Dze8+4pyv8hXIV/uTOXLVVz0k5Mvj919TWUbYi5mLyyGaL6Rw4T8bjIF8/ac1EA6tkrDnAS06J9ylTItN6hBTWimL0EVbGH4DI9jwzwymUc7Qo/YtISvA3CKZz9uJu4i4kud' \
			b'794Ms5lhe021YZJt5QxbZue+s2bXNUtuyPIId4CGpovVPlNYqWb2npi6pjXp4mC+ibJ4zVWCA4QbXqlquIK9hkslRM9M6qUKc7EdiQIFP9j0R8db/ma8fLmnP2OmmztIJmKnI5//YnQfVjZn6bksOIulP2cFBcS++tBhcySfvjv333S9H5vB+NrK1Q6jxvkk' \
			b'Qk4BjNiYWyKOesV9/7ic9pbKSWDnPz4kJB8Q0v9b3pDHb9CAxvJ0uJWdp9iFLW80apFEnFbTk33VTIu7JVqojdr3j8vpb6mc1HLO/sHssPTMqzGA/VzacEulDdX0D4aSufDJH5c03lJJO6zG6mb/sNRq/kn+46K21xd19hytfZq/urrGwRJ17UvzjonpbpGY' \
			b'pjqaY1qa/ptFptmRnnqOJBw5dj1ZthLXNlX2r3PTIGhV8+8Khc2NKJRj3Pal01X7u6R5ro0h1JoDUCuH1u1Ds54nkY92Aw9CdVOXdO/VMcZaNHOm7/pxcOmJMCdW4rAVKd6+E864U+RMW92pE874w3KGtKwJc5p9GYSHh3OY1yrvMV+1KqowKpSMwozdUXhV' \
			b'b+cXyryVZ5hHTC52VXl7ELeU5kK4sC6eB+tMdUpOWNdOWTc46TXyua72Zpw0fNhQxye0puNZ84msc/xNp636LbzGqanb+e2r03ENd09hp0hSQ915CHeoTsnJjEp9vXDfjIelTC/z80ZC3FYj16bfdvJoD4epTkkLk5wzz+NcrIWshevN+XMdM83n4YTl5h6w' \
			b'3FVn4oTl9h6wXEx1Z+CE5e4esDxUZ+KE5f4esLytzsQJy2f0wEOyfHEsfnDGwz57NAcz7TjIT4J2dFIBM9rkCahEN6sKU2136dsY1764h4PF/AbxpVJOU0+9WaWE6jyd1MiMXnruNYJVJGfpxDC/Qt09uxox1Xk6qZEVqvDZ1YitztNJjazQlM+uRnx1nk5q' \
			b'ZIUifa4z0FjYdsZO6scVa31rYqCEkmKIWuIqEqYSO/BK0EWWee1kp8gjvUbWcLa1LoZETYhxk9gmL+EYPM9LUDT3NgfoGzg+CfXCCwmxyLeVYTsfL1PIB9Uqr/5o9LzGIKd5BbG28WEeM2+bavQvb5vJ25AGjmGryX+rsSxMjIGNZljBePX/iqIbLg==' 

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
		('FUNC',         fr'(@@?|{_FUNCPY}\b)|\\({_FUNCTEX})(?!{_LETTERU})|\$({_LETTERU}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}}'),
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

	def expr_mapsto_1   (self, LEFT, PARENL, expr_mapstok, RIGHT, PARENR):      return expr_mapstok
	def expr_mapsto_2   (self, PARENL, expr_mapstok, PARENR):                   return expr_mapstok
	def expr_mapsto_3   (self, expr_mapstok):                                   return expr_mapstok
	def expr_mapsto_4   (self, expr_cond):                                      return expr_cond
	def expr_mapstok    (self, expr_commas, MAPSTO, expr_cond):                 return _expr_mapsto (expr_commas, expr_cond)

	def expr_cond_1     (self, expr_ineq, IF, expr, ELSE, CURLYL, expr_lambda, CURLYR):  return AST ('piece', ((expr_ineq, expr), (expr_lambda, True)))
	def expr_cond_2     (self, expr_ineq, IF, expr, ELSE, expr_lambda):
		return \
				AST ('piece', ((expr_ineq, expr),) + expr_lambda.pieces) \
				if expr_lambda.is_piece else \
				AST ('piece', ((expr_ineq, expr), (expr_lambda, True)))

	def expr_cond_3     (self, expr_ineq, IF, expr):                            return AST ('piece', ((expr_ineq, expr),))
	def expr_cond_4     (self, expr_ineq):                                      return expr_ineq

	def expr_ineq_2     (self, expr_add1, INEQ, expr_add2):                     return AST ('=', AST.Eq.ANY2PY.get (INEQ.text, INEQ.text), expr_add1, expr_add2)
	def expr_ineq_3     (self, expr_add):                                       return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2      (self, expr_add, MINUS, expr_mul_exp):                  return AST.flatcat ('+', expr_add, expr_mul_exp.neg (stack = True))
	def expr_add_3      (self, expr_mul_exp):                                   return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_neg):                   return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_2  (self, expr_mul_exp, STAR, expr_neg):                   return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_3  (self, expr_neg):                                       return expr_neg

	def expr_neg_1      (self, MINUS, expr_diff):                               return expr_diff.neg (stack = True)
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
		ast = _expr_func_func (FUNC, expr_func_arg)

		return \
				AST ('^', ast, expr_super) \
				if expr_super != AST.NegOne or not ast.is_trigh_func_noninv else \
				AST ('func', f'a{ast.func}', ast.args)

	# def expr_func_7     (self, FUNC):                                           return AST ('@', _FUNC_name (FUNC))
	def expr_func_8     (self, expr_pow):                                       return expr_pow

	def expr_func_arg_1 (self, expr_func):                                      return expr_func
	def expr_func_arg_2 (self, MINUS, expr_func):                               return expr_func.neg (stack = True)

	def expr_pow_1      (self, expr_pow, expr_super):                           return AST ('^', expr_pow, expr_super)
	def expr_pow_2      (self, expr_fact):                                      return expr_fact

	def expr_fact_1     (self, expr_fact, EXCL):                                return AST ('!', expr_fact)
	def expr_fact_2     (self, expr_attr):                                      return expr_attr

	def expr_attr_1     (self, expr_attr, ATTR):                                return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1])
	def expr_attr_2     (self, expr_abs):                                       return expr_abs

	def expr_abs_1      (self, LEFT, BAR1, expr, RIGHT, BAR2):                  return AST ('|', expr)
	def expr_abs_2      (self, BAR1, expr, BAR2):                               return AST ('|', expr)
	def expr_abs_3      (self, expr_paren):                                     return expr_paren

	def expr_paren_1    (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):       return AST ('(', expr_commas)
	def expr_paren_2    (self, PARENL, expr_commas, PARENR):                    return AST ('(', expr_commas)
	def expr_paren_3    (self, IGNORE_CURLY, CURLYL, expr, CURLYR):             return expr
	def expr_paren_4    (self, expr_frac):                                      return expr_frac

	def expr_frac_1     (self, FRAC, expr_cases1, expr_cases2):                 return AST ('/', expr_cases1, expr_cases2)
	def expr_frac_2     (self, FRAC1, expr_cases):                              return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_cases)
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

	def expr_mat_1      (self, LEFT, BRACKL, BEG_MAT, expr_mat_rows, END_MAT, RIGHT, BRACKR):  return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty # translate these on the fly?
	def expr_mat_2      (self, BEG_MAT, expr_mat_rows, END_MAT):                               return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_3      (self, BEG_BMAT, expr_mat_rows, END_BMAT):                             return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_4      (self, BEG_VMAT, expr_mat_rows, END_VMAT):                             return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_5      (self, BEG_PMAT, expr_mat_rows, END_PMAT):                             return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
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
					if not (ast.is_diff or ast.is_part_any):
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

		assert rule [1] [pos - 1] != 'expr_comma'

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_int':
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
				print ('parse:', res [-1])
			print ()

		return next (iter (rated)) [-1]

class sparser: # for single script
	Parser = Parser

_RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
	p = Parser ()
	a = p.parse (r'\left(\left(x, y \right) \mapsto y + x\right)')
	print (a)
