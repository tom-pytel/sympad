# Builds expression tree from text, nodes are nested AST tuples.
#
# Time and interest permitting:
# sets
# assumptions/hints
# importing modules to allow custom code execution
# Proper implementation of vectors with "<b>\vec{x}</b>" and "<b>\hat{i}</b>" variables
# sympy function/variable module prefix
# systems of equations, ODEs, graphical plots (using matplotlib?)...

# TODO: eye(2).is_diagonal
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
					(neg (AST ('/', ('@', ast.diff_or_part_type or 'd'), ast.dvs [0])), dv) \
					if len (ast.dvs) == 1 else \
					(neg (AST ('/', ('@', ast.diff_or_part_type or 'd'), ('*', ast.dvs))), dv)
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

	return AST ('vec', ast.commas)

	raise SyntaxError ('invalid matrix syntax')

#...............................................................................................
class Parser (lalr1.Parser):
	_USER_FUNCS = set () # set or dict of variable names to be translated into 'func' ASTs if variable followed by parentheses

	def set_user_funcs  (self, user_funcs):
		self._USER_FUNCS = user_funcs

	_PARSER_TABLES = \
			b'eJztXXmPHLdy/zIBrAV6gW6e3fpPkmU/ITr8JNlIsBAEWZIDI5btSPJLgod899TF5jlHa2d2Z0aD5U53s9lksVg/HsUieefqmwfPHj97+k33zb+8//0dXB4//O4lXH649/zh08dw8+j7p8+eP3z94Mfnj/8dHr97fu+BXAa5Krjef/j96wf3Xjx8IfdP7r2U' \
			b'u/vx9qd4+wPfUqyYypNHT3+kbyG+f0WPFy+f4++P9+H36Y9P4Pene+jz6OnL75HKR0/oNf3+/TnG9fgZvvjux6dI330K/ODZkyf3Qmaeh/Seh3Tw5vmj7/+GX9978gP8fnv/8YvH9178DW4fPv1WcoF39+PtT/FWcvHw7/jz+MVD8Q6MwNheMiFAAIZ8cu+H' \
			b'Fy+fYXIvKX8P/+3B4/Aa2fnto58efYvRPPj22UvigmSakvjhMfHo0Xd4//zRE0qEogM+4edv33x8//n1Hx9fv/v5t0+f33wEr/f/8+fH15/++vP9/PDLX7+/ff3m43/Elz+H2w9vPr9++8dv6ePHP/67ePwUnt+++fT+06e3+eOf+WN4evNzvP38OdLy5u3n' \
			b'cP9nTAlJjOR9CLe//Trf/vo7fvePmMUPf/32+tcPc+rJm99jBO9+/Ue4/fz+Y+L9yy/h/uePb97+5/uZqN/fz3x6+9fH3/43TQ5uEtbM2Xv3LmNBpPj9f835g0TmbP/6/u37+QEK8PcY6Z+fPv8xZ/7Nh5/fvQlPc1xzWn98+PAme/j0zavu6s6lUZ0ZLjq+' \
			b'UXiju0tDV9XdUZ1yHfjoAW4uZl/yix6XHm8GxT926C4Hc5F6DSb1wlv8cOAfwy/gDuKiIB4THiwExIR1fxF8xW/2uBwmuoOYRvhad0ZeIQmaYtX4YzqtL+QRnujOUlaRenkVPPjJhO/gvQ1eeAt3iv6VD59SHJis+DMN3aUST36G+AeN9KspeEAe6A6IVz3F' \
			b'1POPgbiVRB69kI3RF2+x3ODfdhqiYDIN3iC5Pf8YoR4+0FTQU3cHU0YWDRfi4ZIHzxf0wIRGKAwUCeasPCLtwKs+9zfVo55yL1s/DqnXpaICNZi7Ue7uULZH5lkvMgYBBhW88Ba/Bw4jXyjRYQ4QvOPjJYgucQ1LB96wIFu8wQAOwg8diBcWl4LEDIk7soRD' \
			b'rgiBELLDlgEhU3nAS0WMhy8ufWcgEOfY4Q0SqgUU8JF2HYpmRAK8C96zB/IFfWz0GdjHRR/FPj74gFCSsIz8k6BjFBnXnn8IGEyi9nSLdy68vJBHeAovOA3DP2ac8z57TakX3iJjNP9AsV1cxFsM41gywicowkQEMpxuqBrRUouIAIEfY3B+NFQ2OqAS8kIi' \
			b'OLJoWUWCPgV0pd7iAc+U7MQ/IHoX8gygo8zDm4HilSfLtQjSpxLhIB53KkivSIafoQA1Cb4Q0uUxAQf5qJAOPBli4TB1w3zj5Qa4NN8xeKhSM52V+gXiUVRRgh/UstBWXPUdYAckFUiCYgB/TWJoO+s66zunOqe70Xaj60bfjWM3Tt3Ud9OAOYNsA5aBKECI' \
			b'JUGGEoNQIM/OdM52znUOIhk7B1WQ7/zY+QmKCfkxqm6EOkchoyC/UO0MPTz08NQDdb0lLCiUyRGfHfxD1H03An/6EfKEwLNAKNxDen3nhm5y3QRAU4g1A9JngV1YyYJkTqqbIG8IDPi+A9zA153D9hKegCmQ4QFZgjUYPivHF03eWPPhIz5BGC1Pll8Cp8gb' \
			b'2IXeHNMdJ4FHjtDxNwOHMZLaSMl87YVwZxQOAl1ndgA7RhGdiYRlYhGFHLLQaHrNeatzxZmZs1HmISEdiH7FNQ4J9bTTWHuO1Q4MLxZ7KuY7o+RjIGRgbQmRQwUOYSChvijwWRq45FkmTrv8B8fM4+L3zDUf2DYSL5laIDISRZTsiIqMwyljdyQgV9hzPmMd' \
			b'Ww1CgTedt52HDKjO6873nR++eiAAc9yZOauZ48/MWc2c8cycVe2Lk4aFL4ovo+YOqpHuAHc6NLffWnGnlijGUL2E7qVb21v5jP1H+vpI2qI7o+SZfCk3nrM7DvIsHTLLubMUfjLdZKXw56I+8mb5jpVytCPnlGXD9TKmYX5MzKZJeu1GxjTEHBjz2/6g8gQE' \
			b'spAaGwnkwjswMpmtxidkAjkQR491xXBo5LKITFT6GaH4dmKo6DCu1l6gJBWJjDqoSL72CvkK1Q/q4uvo72LxsmZFnUuedEnAh8X5b3CAOXmsfIAsAx/mDHKWTqtxJV2gOo95r1AZqlgZemYHtqTnqlCU4SpVxUNGz3xhrXjOl4meIZtn9rA6XO1McX2VTdRA' \
			b'R1UTs0mRDddTa5AIYaeTnfGUsoPzIyR6gwydeLylBpmSVKK0EC0O62uUkTlJmULwVMJHzokrnPw4/mzgzA0VKNcwjYnhVzx7zLMjSZ2PkwT0pefAnj/1SloEz4Nt34fnIRMGxw2r83wZOS5NNRqq9pC1x8XInvuPvZPKmbhV6SAsdzPzWccpaCyJZ/ugboo6' \
			b'NMU6NMU6NIWFMXFhmCALXNA8G6ZjA86tOjfgX01X+I6ZhHVUmx2UzBkjBUZQPDw1J6oPmUB/mAQC9ERjOB1a4aLqv99XdYCaW1GUKtaIct0lVRdrw2KzrckQRuM1eJOWCJ8LwyOoEbSYGOl0gOA49Hlmec2oYVA5z0zKcByKMmd95g250GKYo3kElr7V8hYY' \
			b'o6tmhyOqbDkavtjv09LvU9zhw/HN2TSGy41bU3Ue/GJ76UWsWI4GHXCvpbOouJeIo6Iz7kl+/FlwHA8JNA8JNA8JtAwJ9LHN3l/hCEYf2QiGhiz61PRJOLZSMvLRPPLRPPKBS9kXdA1Pk3V7cBSgeN5e87w4NboyfJ2oITio7GMnkkZ8jCKg6IJ7Y+ZChvCv' \
			b'aKBvyAIcf4EWIx0Kc54FxK6OFp1W1v313FmL+o0+f6+Zp0dWbwGhpuonAtGGoWMYOkaUBka0BeYQx3aIRpF5KzJvQ0+EZd6SzFsRdlsNZijnlnNuOef23E5TPXnmAxmXWVaWOmlgHMuKY1lxoTroYLQkfHNJUwIfevnQH70i+Qoz7jnjnvDF6l5ZNeDwXaEM' \
			b'xYyPzLGRPxwl7Hga7JhOIBtA2fFnA2VqEtPRXmxH+wteaXfVIzyhNmNKsBZCyuaoHS4FYk0HLwgC+EbzEKIj5QvXiZzDNCfCDkuMmBLGUe0pvKOqs8gtjJBjR5yr1ElMRYHLqL7MMu+okhuQfswA5gCZiNnAOTvMC87O4dQcztrhjB0uKMQ6CZcZ4hpDyNeA' \
			b'q96Qw1i9or01GlujHTU2kNg6og0lliGu+8JVWri2itaJQjg0ukXzVrRtxbVWVMODH5oooy0vrk1EW15cjYgzTbigAk3j0QQcu1M4oYSzSR78UQ2FOii0C8euFFbiuNgISxgnq3CxIlp7Ih+w9933UKq4nNXiMm9c78xroYHmS0gXFzo7XAfr+R/E7XIawvpw' \
			b'CKLYH9f5TjFY+g9UXnp8B/8jrvLFBHDhd497DvTo0+OC4d7SXgGXIz1gWrjctscV9LgGHB6g+C5xhfKE9HleLE+p2CpVys18obXnOAcDj8AMyBS9gIRGIgSIt0aIMZIjXPdscOk8rmDuMXVelU0r2/FTi8yijQsgQpWliBELK3H1/IRrvjEfEAvmq6NNBgK1' \
			b'Hv/RD+Jyib9D1uMV1x8PkiYu7cfl+bhumdY4YxlAlCHnRgoQaAUJupyQ55bjxVXlSFhSTLiePXziMHokFpkBYRwIxj/tdBcDAgru0orjAZ5RmpU8e3r+P1RbYb1Q1ApFfcCVwfXRPyHEGdw1rNdBuoSz3QDdErIlVNfBtIRmCku1BoZrMNjCnuBuzxizjCCG' \
			b'zgrMrMVLgRVGx0pklIgokbAOBaXkJ1KP0t6Qcup0gfD6pBmjVlQWtc7NmL5eS2YSce6lI1+2akmnILZtLvTrhzD9Y6Q3ISDQGQ6ox5g370nbDv/wnroSQw0Rat0CLKbrtWS4EoJ2RxkbUHGNVi1ARrdbtKw1w0rFC4QgHC5mwZUsGZyweGGANBFyfE/AoUvf' \
			b'TQE5AJZp/lsCo7GFIvRMgASP7EpEhQSz1D3vkTJ/JJ8y6OguwR0GniwhbyLsUSqGL06+9X0NxSmCD4E3g47yXwCPeRLBF4ma6raI+BWByBRZCV41QxS1AJICZrGnTZDGJgb4BC0OibSxd7ESAHGBq8KmRzN6pwS/7oCQ24atvg5yTxm12Fw45CHmtOdWT1o8' \
			b'2lOIYMvvUrcEuxRtiV1qpiJ2Y8QFduukMzJ0RRwi2BGI6aFqPAXGlNTEF8MXF2IoQUwRtVAs7wocBw5FJEfiGkjmFGckS0AUhL4F5cAmBjMFzRJogLkBYlM2wYcP4TN+m/gdSNSxc5GDd5jBO5RuEXiHFniHHLxzxCV41zoCb+HFzS/drUTuwMgdGLkDI5c/' \
			b'r5A7rEIuhy+RK+xJkDtT1kLukCOXA6IIDE3kCo8EuQMjNyawHXLt14TcU+8z4/DL0fjH5ui1M3pt6Rah17bQa3P0zhGX6K2SzsjQFXEBvTZHLz4H7FrGrmXsWsbu/H0FX7sKvhy+hK/wJ4Hv7NmCr83hywFJBprwFSYJfC3DNyawrBftzjA+IRiT1ggVGD6H' \
			b'8ayq5XepWwRj34Kxz2E8R1zCuEo6I0NXxAUY+wLGPsKYFbZ04RfGJd9XMParYMzhSxgLfxIYz1G3YOxzGHNAlAHfhLEwSWDsGcYxgWUw9mcYnxCMR5J7/DSH8TjDeCzdIhiPLRjn2uAYcQnjKumMDF0RF2A8FjAeI4xHhvHIMB4ZxvP3FYzHVTDm8CWMhT8J' \
			b'jOeoWzDONcsSEGVgbMJYmCQwHhnGMYFlMB7PGukTxLMi3RaWHyu2FCulFSul1aze4hCpW4Jq1VJvqVy9FSMuUF0nXVKiK/oE2KpQb6moo1as3FKs3FKs3Irfl8BWq/RbEr4AdmBRBHaMugFsleu3JCAuP2zqtwKfGNiK9VtJAsuAPZ2BfYrApmEzFhgPm2UL' \
			b'fd5Yny4CbFu6RcBuDZ5VPniOEZfArpLGIshI0RWBAdnFAFrFAbTiAbTiAbTiAXT8vkL2qgG0hC+RLTxKkD17tpCdD6AloNUcvka2MEqQzQPoJIFlyB76M7RPEdqOEECOoO0Y2o6h7WZou9ItgrZrQdvl0J4jLqFdJV1Soiv6ArILew58Dsh2jGzHyHaM7Pn7' \
			b'CtluFbI5fIlsYVGC7DnqFrJdjmwOiMh2TWQLnwTZjpEdE1iI7OGM7FNENinJsKhYSUYWcQNf+i5aNXKI1C1CdktVpnJVWYy4RHaVdEmJrugLyC60ZSpqy8S8UbG2TLG2LH5fIXuVtkzCl8gWFiXInqNuITvXlklARHZTWxb4JMhmbVmSwEJkny2/ThLZpDfD' \
			b'cmK9mWLVGV16ugiyx9ItQnZLe6Zy7VmMuER2lXRJia7oC8guFGgqKtAUK9AUK9AUK9Di9xWyVynQJHyJbGFRguw56haycwWaBERkNxVogU+CbFagJQksRLaOyB5OBty0EOgMclaOszZZISfxHg/cUYRzulCNHrTkqnSLtOSqpSVXuZZ8jrjUkldJl5Toir6g' \
			b'KFeFolwRzgear+5ZYc6G13ThAMYl8VQKc7UC7xK+VJgLqxKF+Rx1S2GucoU5B0S5UE2FuZAvCnPFCvOYwEK8tw3IsnVIRzn39SX2Y9dcg7QS1juANKIUj8TC87DWt+Ga2jpaGZvOfeGGKHpuwHXprr8UQuVG3FzB8n/ViFfJZ6ToisCAbJMMu31hTkbHek5i' \
			b'BSoGKT1XqnUDrjNAY1SxDecUyzZcuJQvqVBtm+6s+da0uMILVY32m2MO7TfIBMaIy0e4JZ95kCF78nd5Lr+HqyYk29qe+zAb7n4ftt2n3mzTWjNa8W46Wig30gW754a752ZGtyndou65aYHbFOCe6SihXaVdOCcALwgcSUyw5ipWF+JzQLjhXrrhXjovmopR' \
			b'VCA3q3rpHL5EuHAq6aXPUbd66SaHOQe0msPXKBeCBeW8nCpJYGGrXVmdHSbSz+PvRRjXNB2GRcLTYZqnwzRPh+l5OoxDpG4JwHVrOkzn02Ex4gLfddIlJbqiT1pvXcyG6Tgbpnk2TPNsmObWO35fIluvmg2T8AWyA4sismPUDWTrfDZMAuKeVc32O/CJka15' \
			b'NixJYCGyK0O0/SE7bJZwxvdN4ZvmxOjQcsY3z4lpnhPT85yYdqVbhO/WnNjE+jWSazzJrBecO3yj67mxmoSSIl3RGXBezI3pODemeW5M89yY5rmx+H2F81VzYxK+xLmwKsH5HHUL5/ncmAS0msPXOOf3Aec8N5YksBDnZ0u1U0S4IUs1LAO2VDNsqWbYUs3M' \
			b'lmr8kLolCDctSzWTW6rFiAtk10mXlOiKPkG2KSzVTLRUM2ypZthSzbClWvy+RLZZZakm4QtkBxZFZMeoG8g2uaWaBMQt55qWaoFPjGzDlmpJAguRfTZV2zOyRZF7SwinUSoWAevX8ILFohnhs4qNQ6RuEcJbGjaTa9hixCXCq6RLSnRFX0B4sV+Cifo1w/o1' \
			b'wxsmGN4wIX5fIVyvQjiHLxEuLEoQPkc9mXBX4lznOJdA8lWNc+GW4FwzzmMyy3CuKru1/S0Z2bW2fKutvPYB361V4zuBKqnMkJEmU4WbWVPG71K3CKQtTZnJNWUVNqsUs9R1RVMAZqEWuwwbCBnTrd1DyKzSgkn0JQ6FCwkOZ0rWaLlDiDbu+GXAHeu+YrRb' \
			b'rpdWlTXZGW8Hhjca3hpyGd7mga1xpVuEt9bA1rj1eKtSzFLXFU0Bb24V3twGvK0as0r0Jd6ECwneZkrW4U1CtPHGLwPeeKQao90Wb5WN1xlvB4Y3MtdCBd6Y42021OJ3qVuEt5ahlhnX461KMUtdVzQFvI2r8DZuwNsqWyyJvsSbcCHB20zJOrxJiDbe+GXA' \
			b'G1tgxWi3xZv+mpYgn7ISyJISCJncZ7i0s/qH36VuCS5tS/1jc/VPjLgAaJ10RoauiAs7v/YtgMrY0LL2x7L2x7L2Rz4vAWtXqX4kfAHYwJ4I2EhZQ/Vjc9WPBEQ5b6p+Ao8YupZVP0kCW0L3vAvXqUCXduGydGBABt15Fy5+l7pF0G3twmXzXbhixCV01zqC' \
			b'buEl0F23C5flXbgs78JleRcu+byC7qpduCR8CV1hTwLdmbIWdPNduCQgynlzF67AI4Eu78KVJLAldL+qbbhOGros6wpdBt3ZnJnfpW4RdFvmzDY3Z44Rl9Ctks7I0BVxAbpqHXTZitmyFbNlK2b5vILuKhNmCV9CV9iTQHemrAXd3IRZAqKcN02YA48Eumzo' \
			b'mCSwJXTJCCrum54aPpojsWPe5Xa289ELaNjeF+ged2TivC3K1fZIr45c2ArtuIavK7Z6R2Hy6Fp7vtt5YSKHSd31rZ9tvjIxxlxWBFXaGR26oo4sI0mRbf26uoDXJlpem2h5baLEUO/Gh0NU1H5hvPzt2p3lJZ6yjhDW5SbR4tuqJOKKRSx3qih8F3aet81l' \
			b'i7gBfWCk1Ba8dDHyp6wtUAShssCLwyeqKnx3dSOHLPAhKnKCSuv4lDX6qObRKabb7riUEr8FbjcejwLfb3U0CuIT3q08EgVL4sCOYZBDTMIxDKuPL1l6dMmWB5ZsOpZh4wElZqvDSRAfaw8l2eI0EshEiZN+X1DBhtIe+JEkeI7TNY4lceuOBbrNY0mGIzma' \
			b'BJl9jeNJpkqa697hDqXZ71Kar1vhr6vsN0lzWcHzmqQjkm6/B+keKGu7lvAtpJs7w8Ms5aFDXEg7sHCrPo7Z8VlSQPDyU+J2XX+v694MW0q9Xl6Pr5HyhdudXPt4KeTNlx7LttO6HMd5q+tzv53Eu1V9GDtgn4WOrxluqE+PVTuN5XdUu+Pidp107W+qlm91' \
			b'5Xcn7/uX9XD63k5rdu7iDaSxuLnj1Qbi0MY+DMi7d3chMZJ31V3d7Ph1XD6E9fvvk5Ns+xXD1a3k+4DkGjMeV8ihyu3SN2drtpLrvR8TyAT2X9gfB/bcjAQ7PMtbhNjvXY5b6tMlsmxF/XJSMo2KCBXlGuf19Q3IdmOX40X1tMIMInfUdeTcbJZzuxtRFyF3' \
			b'u5DzbaYLWtME28p6f+N1t19mX/qFusXQ/8aE7M7k3Lul9bg3W8v6QLH768q53SznbqdyPgt5f4P9kiUyfrrynco28uNm+ygLZHsHcu02y7Xfj1wPZ7m+VbnWJy3XfrNcLzWK2FKu1Vmub1Wuv2zO81jkeryZceWXKv9uQiEShFd9icJPo8nSoYwdr6fbw4zc' \
			b'iCoPzZUaU/GuXymp3T8tz7vT/LvMu48T6famswSfgNrjmmrpoqpF47kbnWhcoYJGM5Gpp8PG+xtS4NlMh7c/eV1l/fgl6rsTkF9kyiWeuhdVd/vtNuBBnbtS2X1R1wG4vCeJVmvrXlfa+t5QDbxxe+Jt7f8cmSQclESzUXS/sVamMKX97E1NrmzYLXgLIz/c' \
			b'BprPne9bXQx9F5BNlfXe5gvPon3zoj3Q/2bRHo5atDFhEu1hvWjr7sp3cbHWQJI8kAwnAizSS4Ybky2WOum2JKGkpNIxOih5LIVkRREVsZOyHUy7TOfypLLEsqJWNF2DQy1gg5nIrJRBzlBTZZZlOqKTcTnKmq8tmBAgU63JQmaQvF2HGQPlWwTYCV/kg+0Y' \
			b'ZGsemZlNdiGbTJNT5nC4ZXLIZxwLKL4219xCrtVtwFz7b1f1b8PZTVV6c91g6GsPu+G+ov+q4nWhwg0RbFXZblNMm6rRRvUp/VsgJq8mfVWot6dHWLnOdE8mbqvHXA2ZaLfXk97h2Ooa46nmus2d6gFqWaqbX23uQgeG5Go8y9VWcoVlfchKp0SwcElqfzuC' \
			b'pdTdSyq8u5dYXvDEtdd0lrLtpGw4HikbiNoDkjJIJpWyW1e3H6qg+eNQox9CU4lSNRywVN3QGoN5Kf/Y5SeXrZMyfXtSRmkvFTKaYN+VnPm1YjZQdzQcC7bpNDAoNZHAg5lJvE0hXCV4LmlKj2SmMK3i9jczuF01hwb9qA8AhuL4F3JO3ka8SevmaSAeVWEk' \
			b'HyN/b2mTZoshIOFpenUBd3cuaadf3sxF9eWmLbjtA++xkm+wQosO0Yg5zOqFPUwQO7y/CJ5+iovOcaXuhAsX4bd2YYXW7LEqoJ8wE5dqf9RCjEv/iCS9P5KgwoA/EDONhl2z490rxo5f8+I2x8p8EFIIgGiEdDAoHswSVhkTuWZ/5Jpu8R+RZPdHElShjT+c' \
			b'B1nxxtMbIsttImu8DmUQtPrDOZqWf/JHlPmcsmqvJd7ZPG6ctH6zpHynJFyATkuKreyCJDsgtTKU7cbrkh2IdLLLkE93FnqFLSX/gUz6LnlI3TZh6F3ro9I3vk38iY/j1iVccW27QoZR2Io/nIZb/Zaq9stpv8U8je2SphOhd1Xa2CnZnzNj5WX9l0VGHB/6' \
			b'fUsEdtB27JjypB3HDqDfgcjgyTW3JDWuY8eH58yPX+6wI3z9WFY6LoO1vRPeKmw9QlfKEHIvlyMc5bUd7d+21uGIoPb10Zezo09JpHA8dkyOi2Btb20biWJWby9XOGa9hgsDzbWhOGv2pKRr6o7KcRG4DR2M7QWMub2lmDX4h0qS4GC4nj4uckG5sSFUoaIg' \
			b'ZvhTkkfUOB2T4yIYD0ceVXcbjtkwnZQk6u6oHKuZ+sORRNPdhmM2nNSgApuFY3JcBOoIimA+JHTrohi7Q3MDjjOBLWtDcZHoHVcOQeXWZLPbpo6Yuh06LNqGr1v5BXPFnKKg4tTK8TkuELud+nBnkmpzaUXeruar6tY4PIR2bYAtXRpPK07m06ZR0K3yyXYH' \
			b'4JhPW8463A6ffHcAjvm0aRRz0LMzeOr0JseWB/y/Tfjyc6tiFNauDudNkmD1npm95zmS/TIb7TwO2vEE96bB0GHz2HSH7ZjHw1Hz2HaH7ZjH6qh57LrDdsxjGBsptPnywnMTnuW9xWdkCfphyy7hoBOWFgXwDafPHe0+N+CeRgObQaFhVyuk7xLHAccqIBYB' \
			b'Bh671A1OPpgSCym0q2Nv3Ihhlom5bD3aYbEZnpjgBZO5kbuVuNqdV25REdKcHQmF5oKfxBwHhHIYkRvDCMPLVxf/D9aa5bw='

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

	def expr_abs_1      (self, LEFT, BAR1, expr, RIGHT, BAR2):                  return AST ('|', expr)
	def expr_abs_2      (self, BAR1, expr, BAR2):                               return AST ('|', expr)
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
