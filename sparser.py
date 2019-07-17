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
			b'eJztXXmP3LaS/zILxAOoAYmHSPk/x3HyjPWRZzvBLozAcBxnEWzsZG3n7S4W77tvXbzVhzzdM93txnBaEkmRxWL9eBSL1J2XX91/+ujpk6+6r/7l7ftf4PLowbcv4PL9vWcPnjyCm4ffPXn67MGr+z88e/Tv8Pjts3v35TLIVcH16wffvbp/7/mD53L/+N4L' \
			b'ufs63f6Ybr/nW0oVc3n88MkP9C6k96/o8fzFM/z94Wv4ffLDY/j98R76PHzy4juk8uFjCqbfvz/DtB49xYBvf3iC9H1Nke8/ffz4XijMs5Dfs5AP3jx7+N3f8O17j7+H32++fvT80b3nf4PbB0++kVLg3dfp9sd0K6V48Hf8efT8gXgHRmBqL5gQIABjPr73' \
			b'/fMXTzG7F1S+B/92/1EIRnZ+8/DHh99gMve/efqCuCCFpiy+f0Q8evgt3j97+JgyoeSAT/j6m9cf3n569ceHV7/8/PvHT68/gNfb//nzw6uPf/35Nj78+tf7N69ef/iPFPhzuH33+tOrN3/8nj9++OO/q8eP4fnN649vP358Uz7+WT6Gp9c/p9tPnxItr998' \
			b'Cvd/ppyQxETeu3D7+2/x9rf3+N4/UhHf/fX7q9/exdyzkPcpgV9++0e4/fT2Q+b966/h/ucPr9/859tI1Pu3kU9v/vrw+//m2cFNxppYvF9+KViQKH77X7F8kEmM9Mf7+MKfUH/vU5p/fvz0Ryz763c///I6PMWkUirv3r0uHj5+9VP38s7KqM4MVx3fKLzR' \
			b'3crQVXV3VKfGDnz0ADdX0Zf8ksfK4c2g+McO3WowV7nXYHIvvMUXB/4xHAB3kBZFcZjxYCEiZqz7q+ArftFjNUx0Byl5eFt3RoKQBE2pavwxndZX8ghPdGepqEi9BAUPfjLhPQi3wQtv4U7Rv3LhVUoDsxV/pqFbKfGkZ4/3fWcV8XPqBkjZdmqaDVzZxls8' \
			b'4JlSBWoxhSGkQKzheoBIiiKpnn8MUKqE1OSFlZJ88RalAP5tp32gwOANFr7nHyO8gBc0ic3U3cGckeHDlXiM2YPjC3pgRlAihQLG9SSPSDsUuy/9TfOIjMm9bPs45F4rReJhsHRe7u5QsT3zrBeJhQiDCl54i+8Dh5EvlOkQIwTv9LgCIBDXsK4hhGFh8QYj' \
			b'jBB/6EBYsboUZGYIPMgSjrkmBgLSDjtGhEKVEVeKGA9vrFxnIBKXeMQbJFQLxOAlPXYo6AlXEBa8owfyBX1s8hnYZ0w+in1c8AGhJGHx/JNhzQtitOMfghmTqB3d4t0YAq/kEZ5CAOdh+Mf4WPboNeVeeIuM0fwD1XZ1lW4xzsiSMYhkjHSLUYDhdEONkpY2' \
			b'SQQI/BiD8dFQ3eiASigLiSBUDv2AJF3JM2CIygIhA0WTJ8tNDGansromlnUqCKNUtIuSDc0MBggl8pjJOvmokA88GeLIAA1RvHFyA4WOd4wFavFMZ6W5gHQUtaLgB00wdCQv+w6gAIIHJAFXwV8jyVCese/GoRvHbnSdn7qp76ahm6CZ9FgaAD12AQpl1ECt' \
			b'WSh/Z0cUTagDeAMkdPTdCA1J37mhc6pzuvND51XnqfkG0fFj54FRCnkFRQZpHnq46/EK6fQotx1JZuc9PEPc3nfedB5DgeWus76zkJPqRt2NphsBGa6bPHAJm0qQL5AnaCYAkNAYT7qbgFZoDYHFfQdIANZ0I/an8AR8GfGCj8ATfAa+0EWTN7Zl+IhPEAfY' \
			b'RE8TBwKzyHvkd0bxdezrJ/bld7DIVyR0lNtEuV/qAdovYaJWF44IRxRzRLHkKJYjzfKqB5EgQ7G4iG3huEyxNHVRshIA7ZCnsZyn0XtN1XCqlrFlGSeEjzteyjFQGLaeUJfQPkPiUwfddln1US5YBlg6zl4ShpH5xxLgB74o4ZynUBwQRHKIhj3lX7A3Z+me' \
			b'pOMljoovkOfOaKQqdr5zU+eBYiiD65zpnL0AAfnj+gt/NvJnuPBnI3/UhT8bOhqnuWvhi5Yn7qgH6cS1DIW5L9cy2iWKMVZv5GrlKn2Xlu6egk+ka7rjPRNPvlQaHq7c8aF0k4xsONxS/AnKEio/VjVX8sn20neslHTkCczI1T0amewwPyZmwyRsMzzQM+Rr' \
			b'NWo/jqlMQCAPrc2UCOTKOy4yLY/57ZCRCST34N0jKerY6GUZmUhGSkpp0stNhAlTbjMImKQpkZkgidSlVUbM9Z26+mLGwFjJrHpRl/onjgALsP6Xs0DPMIH5eaqsgFIDK/IycqnOq7clraG6zIm5ykn6UXN64QhzxFxaRuHERD1j0t5DWS+skU5DlaxRDCNF' \
			b'DQuqkS+MEjQRo/bWcucLPaj7pmEM6b7hem7dlMNCnU9x/DkVB5dUSPQGUV7IOtIgS5qyvDTwqoLiOaYKE/peVi+pQT1xTrzExZLTLwau9FCF8vx5ZmH5J1595jWVrPXHdQV603Fkx6+6UfoGxxLiwrK0s4UwOO5l3cAXxWlpnqdpIurEGGl4SNk7aZzp2moq' \
			b'LPeZ5UrlFHR/VA2HIG8ao65Nsa5Nsa5NYW1MRCwq11gY+JEX0XTqxLln5078Sxoe37FipWG5fo5J7oyXOiM4Hp9GFDWNDIjhOAkE9E2Cvv7YaheXCYZDNQmo5BWdqmLdKTdgUl08tE99tybDEY3X4E1qJHyurZdGjg3c0fl8YeTYlxXpzbMHIKJgm8l5jvNT' \
			b'Yi5wIPfWSmqIeayY9bovIhmJBPzRTSfkyK8xBZnxxWGglmGg4vEfTncuxjWxBnlGrC4zYulAPQurZ8kedGgHtIwgFQ8dcTp7aQeiZcFFKReMCLgZcyxFTloxza3YSa3/v8TJjT6xyQ3NZvS5qZpw1qVkTqR5TqR5TgSXeojoZjyNKzpXyzNAwz2vZVmdZJaM' \
			b'g0t1XINLGlsixQKjqTNXPEgzVzK9/4mUAIasy/EXaDEyyDA8yDCXRURsoNQgA6KpHB+7kVus+GzKcCDOnF4TBoSaZvg4sqAA4YZRZESzYESlYI5x9kfAFPG3Iv42jE1Y/C2JvxW5xyfeUHCRe+TIxBwpJoAkDJaFwbIw2MtAZpSO5MIKajKNY9kAigVa47wg' \
			b'jSxIIwvSGJrPDhgnHB2zXhjSwx1sii70vjt5Lf1LLL/j8jtqlViXLls4HIbVmmYsuWfOeX7TS2R/HvyYzqEY5gyKgTI1if1uLwa8/RXvg3zZI0yx3yNKsJFCymLSI+7NYsUR79ACGCd7nLznJJpyHnELyqWVUlliyiTDDG4dkYnc0GZM5IYWm4oh6CGVMB2Z' \
			b'xSa7xGhSkkYGjFxqpB8LgCVAJmIxcEUUy4Jrn7jwiWuiuB6K2z2xbcJNoLgDVGHrC/Fw7x1uvMNddzieQI5ja4xG8GgBj8bt2BhiS4hmrbSRF/d4I+MgHtUf+KFhLC5P4NIEboZDs3G0GcfawJrAHaS4nodKV9zqgkNRXIvDhTpco8PlO1y78xCGWj5U8aGx' \
			b'Prb3uA0MewuscVwaxAkTzhmAJ6rXUMO499jiFnvca8770HGnPPRpuMl8xI3J8j/htm/cl4/78/E8gZH9cY/1lKLl/w43rGs60WHlMSpmgLuze9xu3dMdnjrQ05ZwiEPnIsCPJ188PwFpgYcJTzLAbc9GNk4PkottcqXSxMsKN83jlmdMFUvEAZCMp+whhvVC' \
			b'jJESWdyMjxni+QA95kpHHXR0qgC+OtI5Cx3tfx/HIkcInSSWVnzF7dpQr7iJHHPKKIbaWnk8SAPSGjMeQi2vQK5XDlluORU8JAA3w+OxHBNuiodqxNMJpsAJI7lCISzyGrqSlZ84YdzSbyRelg8eKIG1Hd4dsQRYJiwzhI1Il/mp+z873cUXAB53aa/4AM8o' \
			b'1gqeEQK+x+d/omIQG4yquagaCm4lrt8sTIh9Rn2L901Yr3Fut2C6xnKN4U34rTEreCWs6i243ADKOTAKEA8MOsuQYiytAdFGAFXgIbjQkRL9HFRqiNTQ2ASLBgoBBhOL/hpxp3EZSLHLOjrqZ2Ufcuzo9PX6OpPJdRgA1P2eD13fkPV+sccP3T1IFwiUj2jQ' \
			b'BSBoXKmaQUA2AgAs4GBjaLFC/V/Ax3S9vg43/tB5NX4GM+NMvxewozf0eXl/h81LT1gasB1AxR3q7ApcoWjDLGsiCKEwAWV0Md0UIASJTfFvCZ4wWgMn9MwQhVpXzZ4ltEKGRe5Emk4vyauMPrrLAIiRp5EgOBEIPeOQMuvlXTeDySmhEBEY0UflrxDIPEko' \
			b'TERNLRy9LhApzHDi33RQkrpgEyONRQZ5l6SxC0L5vkuVABJ2FxsEkBq4jtgVaQbxlMF4PCIAz6NXXwfA5w5e6j6Qj1janntB6QHpwCdCL4flbgmEMXoDYfTMIJwSriDcZl2QgfysvDwVZyX5Np2poJmy0pyG56eYQo1l4sscmEOOJZwDhxKgE3EzgOYcI6AD' \
			b'G5wENIjOCs+gpiosMpkB9QyYTd0jHz+ULzhei2MayNJ4owTxEEE81G4RiIc5EA8liGPCNYg3OgJx5cW9Md2tRfDACB4YwQMjmF9vEDysQ7BkVyFY2JMhOFI2h+ChRLDwwElAi+BUckHwwAhOmeyGYPslIfhLGErj9IzXLmyJYhtRbGu3CMV2DsW2RHFMuEZx' \
			b'k3VBhtGNl6DYliimsgmGLWPYMoYtYzi+38DYroOx5FfBWPiTwThGnYOxLWEsTHAS0MI4FV1gbBnGKZNlo+vxAuczg7Mj+cckSjhHHS+H5W4RnOd0TeiZwzkmXMO5ybogA5lZeQmcXQVnl+DMml56nQMQzvH9Bs5uHZwlvwrOwp8MzjHpOTi7Es7ChEBKC+dU' \
			b'dIGzYzinTJbB2V3gfGZw9iT/qF8u4ewjnH3tFsHZz8HZl3COCddwbrIuyEBmVl4CZ1/B2Sc4e4azZziz9jm938DZr4Oz5FfBWfiTwTkmPQdnX8JZCHIS0MI5FV3gzGrpLJNlcPYXBfaZ4lqRDgzrkBVginXYinXYKqrBOEbulqBbzanBVKkGSwlX6G6zrinB' \
			b'/e+VFwNcVWowlVTaipVgipVgipVg6f0a4GqdHizkVwI8sCgBPCU9A3BV6sECH5wENADPis4AV6wHyzJZBvDpAvBzBThNq7HSeFpNK678ZKgyA8Bt7RYBfG5yrcrJdUq4BniTNVZDQYrRDXWC8GqCrdIEW/EEW/EEW/EEO73fIHzdBDvkVyFceJQhPEadQ3g5' \
			b'wQ6McBLQIjwVXRDOE+wsk2UIH/oLxM8V4owEcgTxkSE+MsSjLYcaa7cI4uMcxMcS4jHhGuJN1jUliPDKy4dylQgfE8LZOIRe5wBEeHy/Qfi4DuGSS4VwYVGG8MTlGYSPJcKFPCcBLcJT0QXhIyM8ZbIQ4cMF4eeKcFKmYXWxMo2s7SxfTJfMJjlG7hYhfE6l' \
			b'pkqVWkq4RniTdU0JIrzyEoRXWjWVtGpiP6lYq6ZYq5bebxC+TqsW8qsQLizKEB6TnkN4qVULfAiktAhPRReEs1Yty2Qhwi+GZGeLcNKvYV2xfg0viHDPCI9aNo6Ru0UIn9OyqVLLlhKuEd5kXVOCCK+8BOGVok0lRZtiRZtiRZtiRVt6v0H4OkVbyK9CuLAo' \
			b'Q3hMeg7hpaIt8MFJQIvwVHRBOCvaskwWIlwnhA9nA/K4C+kCdlams42WQm7iPX6FiVXqdDF0Ea26qt0irbqa06qrUqseE6616k3WNSXI2MpLFOuqUqwrwvuAh+CjFbfhKFZzMhzB9lk6jYJdrVOwS76Vgl1YlSnYY9JzCnZVrZcJl5yEtBr2xAPRsCvWsKdc' \
			b'FgJ/3iJtbzuhbmfF7HOs0a65BWotuPcFbPBDvOKHBzb36Jp6Po0uXzHDQ1x07M514a6/20KV5uHczvJ/05/rTY4688pLwG2yGbkzXWGZRvlrMSwVm5ae29a2L9cFpjGp1J1LjlV3Llwqd22oeWvxoifXtH/Dcc8z25WngktXjhWMVdCtGNspRoHtyd1lU4Ae' \
			b'ro6wbFtT8ePsw/tDmI1/CT04bW9DdmIFGh6xGx6xGx6xmwhxU7tFI3YzB3JTgTzSUUO8ybtyowC9ItBT2VaSfT5wz5BueOBueOBueOAek2jAbtYN3CXLCunCqWzgHpOeG7ibEu7CDScBLdpjYgHthjGeMlnYfzcGbMeJ+MvUfDHWNa2gYbXwCprmFTTN3bmO' \
			b'K2gcI3dLgK7nVtB0uYKWEq5w3mZdUwJcrb24N9fVAppOC2iaF9A0L6Bp7s3T+zXC9boFtJBfifDAooTwlPQMwnW5gBb44CSgQXhWdEa45gW0LJOFCG9s2g6H8LnDHC44PzTOGQ/kCOe8jKZ5GU3HZTQ91m4RzueW0SZWwZEY42fuUM4R72PHvw3eGxJqihDv' \
			b'lZcP5SvxnpbTNC+naV5O07yclt5v8L5uOS3kV+FdWJXhPXF7Bu/lcppERLzPL6dlRRe883JalslCvF+M3s4V6YaM3rAe2OjNsNGbYaM3E43eOEbuliDdzBm9mdLoLSVcIbzNuqYEpafyYoSbyujNJKM3w0Zvho3eDBu9pfdrhJt1Rm8hvxLhgUUJ4SnpGYSb' \
			b'0ugt8MFJQIPwrOiMcMNGb1kmCxF+sXo7MMJF33uLSKdZLFYDK+HwgtWhGelRD8cxcrcI6XoO6aUmLiVcI73JuqZkxkuQriuk64R01sMZVsXRU5+93yBdr0O65FchXViUIT0mPcWXarzrEu8SyUlAi/fEAMG7ZrynrJbhXTUmcIfblbJv1fpOx44dAsY769H3' \
			b'BllSrSEzTaE3N1Gjxg+5WwTWOY2aKTVqDUabHIvcpfJzLwFopT5bhTONjOk2Hmtk1mnLQvIVHoULGR4jJRu04iHGvPlKVj7BH+vIkv+OW7VVY5h2wd0R4o4lllyBuzjxNWPtFuFubuJrxs24a3IscsfKr7x8KMUa3G05Tsysm9OG5CvcCRcy3EVKNuFOYqzB' \
			b'XSqf4I5nssl/V9w15mIX3B0h7sjyCwdp5c5KE22+OCx3i3A3Z/Nl/GbcNTkWuWPlV16CO78Od34L7taZdYXkK9wJFzLcRUo24U5irMFdKp/gjo25kv+uuNNf0u7nc1cWWVIWIaP7Ap82qok4LHdL8Gnn1ES2VBOlhCugtlkXZAAzay85tbafA6rMHS1riSxr' \
			b'iSxrieT1Grh2nYooZFcCN7AnATclPaMisqWKKPDASUAD4azkDGHLKqIskx0hfDkg7JwgTAeEIZfLA8JsPCCMw3K3CMJzB4TZ8oCwlHAN4Y2OIFx5CYQ3HRBm+YAwyweEWT4gTF5vILzugLCQXQVhYU8G4UjZHITLA8ICD5wEtBBOJRcI8wFhWSY7QviLOiHs' \
			b'7CFMJtPIYlVCOFpKc1juFkF4zlLalpbSKeEawk3WBRkI4cpLIKw2QZgNpC0bSFs2kJbXGwivs44O2VUQFvZkEI6UzUG4tI4OPHAS0EI4lVwgzAaUWSY7QpiMqtLR77lBpZmzkD5CSO/zBN74WQk0T+8rlPs92U/vina1EPF9i3o6qn4r8t3MifX4ASmHbu7o' \
			b'ehv3Q3Kc3F3fwtqWGyJTynWj0ORd0IGNQuWFVpek/LZuU7vAWyItb4m0vCVSUmgPDcQpbJ8+LZHtj5w9ID9QUrUXwrrS7DpUwEyDkTZKYv1To+HiAfprpt/orWJe2YH6lndNJj7VrYflxgMvIz5R0+G6lzfy3Qj+YIx8LWbuUzEb9Fezn4kx3W6fhqnxXOF4' \
			b'66dg4P1tn4GJn5UA/62ffrHT0X1dAtcIVVyM2fCZlqWfaNnxwyzbvjax9UMsZoePsMgJ9zt9eGWHL67AezVw+kNhB3tSe+SfXUGzvGt+emXc9C2k2/z0ynAin19Bhl/3EyxTI9btOHKPYu32KdbX7Qo2dQNrxDoO2dY3/wPu6JzcKYm7O4C4Ixtv+otDLop8' \
			b'GkOX7X4YS1ftv7ehnQdqdxogmT1/Wwsqa/nn9Pbd1m8aGw07tvfm89r8DQBYeFzLtT+3hfz53O/W7bXdx4nj+rbf7dT2Y2VsGPjYAQc+JPjDDc0M4nc699QT4I58nU0QbqpHmJsQ7FfwDy/08ROF+2z9eWw4kC7kBr87NxDlOw18QPDdeBdy/Cd/pPzlzU6H' \
			b'/fIZsTv8iJ6E3K2Z/e4s6Eck4FjotKEPtXorZz9bwA/+IUUmcG5au/NoHvh4M6IMvy5Iszu4QM+paZcItRW1ztkJNwqFSgKOsuZuQMhnDnZe1HIrLAO+M15b4M12gbf7kXmR9nEfAr/L+sTcusSuQt/fSmvulxn4fKbiMozRUX6mvQm87xe37H5nocexIgn+' \
			b'HgTebhf4ca8CH6W9v8EhyxJhP29Bz4UceXLDw5fdhXxfAj5uF3B3GAEfLgJ+6wKuz1/A3XYBX2qgsaOAq4uA37qAf95a60kJuL+ZSejn6g5vQo0SpFjtYECwQaKx2o9ksnk99SAV5JDKkyCvg5+3vRvZ9p3oWKcTtLz2TzYAntf+FWsIp4tEn4nO5Jpa7qoN' \
			b'Riu/m1rb3KrRZpsV+op7f0NqQFtoAg8nuOtsNT9HCXgmgoyMWeEnC5MC8LADC/za6b4Uf58/uAAOHEi01cbWeKxNlG+oTd56ZPMuq5JjJtbmuESb7bn7re00xalNfm9q0WbLIcq72CHi2dhBrKks7ehD3wWcU/N9sAXJi4zfjowP9L9dxocTl3GdyfiwWcZ1' \
			b'99J1affZQCI9kDBnkixiTLYik632bul5kUKRycXEe6h+rPZsexTVs5MKHtZUbKxUqlA+jcl1xYYi6hhnOIocy5k0euq8zLJCJ5gyQL1sYtuBCQE7DV6QGSh012LGQOUWKR6FL/LCbgyyLY9MZJNdyCYzyylzPNyqcF9wLED52lwbF3Kt7QxiN7BbH7ALZ7e1' \
			b'7bNtugzDJ7Mf7iv6b1rfMbS6akmLuxP6t7Slc21o+F7KoMp20jW1envKhrU7Zw9lVhcEoenMZ4Rivtee9B7nXNeYZ83uQt2voqAVprYD1uYujGNIsPxFsHYSrBtdKrieZOHu2v6WJEupuyuqvbsrrDB48iRm00XMdhOz4XTEbCBqj0nMgORczG5dLX+skob1' \
			b'cgKq9qPoLVGshiMWq5va2xBEq/zA22Yx07cnZk5/hpThS3sTNKZg/RAf5xlD+Hrato+mQYlFBI9mzfFWpXCN5CF+T2w9MW/kDrh+uFtDhxsHUC0AHJ246ORtxJuUb25AfieNGM2e/UARLR1QbTEGUDTB23B3Z0UnHPPhNKqvD6HBYyv4zJjywBja94g20mHd' \
			b'L5zJgmeqpFOS8IOxuE8e9xRPuH8SflsX9odFj9mInIajQq/UYYmGVJf/EWH6sIRBEwJ/gDaN1mLR8XEcvuNg3mc3srYfBBAiID4hL4w6cjTZFk1Em8MSbbrP+CPC7GEJgwZ25g8XTdaE0FIG3RN54zby/HUphOjNHy7szPkXf0SfK+lrjpjSdPx6Oi9q8xlR' \
			b'5QFROMagzc9WDn+aeKFwrljFIcVjdvCS7ooj1WgzuA8bwH/CXpX/oOl2XfaQu13iUNjcS7VvHpqFEDf9zrXd8G73Cvfduj9cx1sfCn9E5HTYKpdPdja1Tt/c3mfN42DmcM74xsu6z06PGD/0NyEeOL7bv+MCZAMBHEK6PQgQfgLoFmVo7Njxl4ji4+c7HE5f' \
			b'P5VNjqti4/DGmO2wXStRyMRWqnBFft5Nbm2QOJxetL6u8OVS6XMTMJzjnZjjmtg44NtFvpjjy6QMp8PXcGEOuy0il9CenaxN3ak5romNg+TdZY05vkDiZniIqphru6A/2R6xUoQQN9y5ySXqtk7McU34LSPlGxZN1UXns/vDO+bGdHZyqbtTc6zZ6o9LLk13' \
			b'S465cXaTEuw5TsxxTagTqIn40dZFNeK7Y3MDTlfxM+NbInLN6D23GEG1N8vtcdeGY+r26LCWZ3zHTS8xc8y5ii0u+pyk43qxuykq9ya3tpRdYvFG9qpug5vMptDdXZ7OmjSZXeOxs8t2x+GYXTuufNweu1x3HI7ZtW0udPQLRdCCbnVsMMH/u8SvX7cqJWHt' \
			b'+njOZBnORWGeH3il5vA8RyuVY3e8Jr9tSnX8rDbd0Ttm9XDyrLbd0TtmtTp5Vo/d0TtmNcywFNkjCOtNeJZwi8/IGfTDMYDEg1FbXiPAPlziH+mgvgEPexrGnmO62ZiuyxxH9E1ErAmM7LvcDaO8MGVmX2gtKCY/PX0elkUjVrFD4zI2LhTDwmAI6Lkpxb39' \
			b'vCuNvqBgKPrEtoe0vZSnpLg9evAjLS3CeP+nq/8H+26uEQ==' 

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

	def expr_mapsto_1   (self, expr_paren, MAPSTO, expr_cond):                  return _expr_mapsto (expr_paren, expr_cond)
	def expr_mapsto_2   (self, expr_cond):                                      return expr_cond

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
