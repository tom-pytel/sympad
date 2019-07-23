# Builds expression tree from text, nodes are nested AST tuples.
#
# Time and interest permitting:
# sets
# var assumptions
# importing modules to allow custom code execution
# Proper implementation of vectors with "<b>\vec{x}</b>" and "<b>\hat{i}</b>" variables
# sympy function/variable module prefix
# systems of equations, ODEs, graphical plots (using matplotlib?)...

# TODO: indexing - slices
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

	elif last.is_var: # user_func * () -> user_func ()
		if last.var in user_funcs:
			if arg.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg)))
			elif arg.is_attr and arg.obj.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg.obj)))

	if arg.is_brack: # x * [y] -> x [y]
		if not arg.brack:
			raise SyntaxError ('missing index')

		ast = wrap (AST ('idx', last, arg.brack))

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
	if ast.is_brack and ast.brack:
		if not ast.brack [0].is_brack: # single layer or brackets, column matrix?
			return AST ('vec', ast.brack)

		elif ast.brack [0].brack:
			rows = [ast.brack [0].brack]
			cols = len (rows [0])

			for row in ast.brack [1 : -1]:
				if len (row.brack) != cols:
					break

				rows.append (row.brack)

			else:
				l = len (ast.brack [-1].brack)

				if l <= cols:
					if len (ast.brack) > 1:
						rows.append (ast.brack [-1].brack + (AST.VarNull,) * (cols - l))

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
	def __init__ (self):
		self.TOKENS_LONG.update ([(v, self.TOKENS [v]) for v in self.TOKENS_QUICK])

		lalr1.Parser.__init__ (self)

	def set_quick (self, yes = True):
		self.TOKENS.update (self.TOKENS_QUICK if yes else self.TOKENS_LONG)

		self.set_tokens (self.TOKENS)

	_USER_FUNCS = set () # set or dict of variable names to be translated into 'func' ASTs if variable followed by parentheses

	def set_user_funcs  (self, user_funcs):
		self._USER_FUNCS = user_funcs

	_PARSER_TABLES = \
			b'eJztXWuP3LaS/TMLxAOoAYkvSf7mOE6usbaTazvBLgzDcBxnEWxeazt3d7G4/33rVBVFiuyXZrrH3TOD4bREqkQWi3X4KD5079UXD7998u2zL5ov/uX97z/R5cmjr1/S5bsHzx89e0I3j7959u3zR28efv/8yb+T9+vnDx7qpdOroeuXj7558/DBi0cv9P7p' \
			b'g5d692W6/SHdfie3HCtSefr42ff8LsX3rwh48fI5fr//kn6fff+Ufn94gJDHz15+Ay4fP+XH/Pv354jrybd48PX3z8Dfl0z88NunTx/EzDyP6eHmwdPvYmrwfvXlkxdPHrz4G90+evaVco+7L9PtD+lWuX/++Ju/xaCY+Ud/x8+TF4801pfCCDEAyqcPvnvx' \
			b'8luk/5Lz9+jfHj6JjyHOrx7/8PgrvPrwq29fshQ00xztd09YRo+/ph+OhcSDt969/fD+05s/Prz56cdfP356+4GC3v/Pnx/efPzrz/eT5/f3//Hm579+f5ce/hhvf3v76c27P37NvR/++O/C+zH63739+P7jx3dz759zb/S9/THdfvo08fLz23ef4v2fKaU5' \
			b'e7/F219/mW5/+X1677e/fn3zy29Tuv9I2f49vfrTL/+It5/ef8iCf/453v/44e27/3z/KRPTlJW/Pvz6v3lydJMJZcrYTz/NMp94ff9fU84okSnDv7x/937yUNH9niL98+OnP6Zsv/3tx5/eRt8U15TWH7/99nbm+fjF6+bVvZXrGtddNHJjcGObleNr19wz' \
			b'jQnNqmtsTzcXUyiHpYBVj5vOyI+ngM5d5EGdy4Nwixdb+XHygO4oLibpkXDnNWEKjKEaNgWsupHviKeB3jaNHS40YNVZjhUcWNtYc6Fe8vGdA12DVCW6KUB8Nr5HL7gYhFu6M/xvKH17If4Vx9lpuPDQrIwGit8T/5YFN8YAygPfEfOm5Zha+XEUt9HIUxDE' \
			b'mEJxi3Kjf9/YsVn5C/HTDShG+XESTHckYtxROFKGiCTnFBAyTy8XBOA9FAZyLkyrF7yTcLp5uKu9wzzIV17X5kErM7BAWlUllI6UXCe3IKMcI/uI2yWCGJy8K8OC8FwILbRavKvABBRuuoa0CKViKDHksoGcOtHsDRRAiu/2JKQimxOuDKce6L9vnI1cUQFI' \
			b'zq3qPoqLitXmCKBnMXgKgFwQ4lJIJyE+hRgJCTGEdI81upefDATAFN8E+WH9F4UmH25x5+PDC/WSLz6QNJz8uGHK+xQ05kG4hWCs/FCxXVykW9AQI0qnXoILpzXKA1UeAMAwdygJpuBqxMbqS2oGChMMTl7HhWYjKkkAXKcMonMe+W+gZiLOPFgDyM/JDvJD' \
			b'OnmhfgIds0ZPOo5XfV5qEcoZ6UrSGmRBFJDVWlUmxHxR4D2XEMdeE2Mln2NJdpBDN90ZveviQ6lxkO54QQ3Aq7YhpaRECHwkdEINaRz9eGKy8b4JbRO6ZvDNEJqhb4ahGcZmbJuRhDqAYyTcoVAJq6S2VD5ERdobTBNsE1wTKJLQhL7pfdPTUxQFMjm0zUAl' \
			b'ZZB7KkfSwa4lf0sBLYW0DtULqnTbDFRGLb09NP0I6HlGmA+N7xtP4iSOQjMSnAwQ5UjHPEkDNSbp32iakfIUoARUcoQOylgT0PiRj4RBGe0gClRH8JMw+GI5GNUYvPARjVWfl4feS3CQqIKEksQ4dJAISRS4dHKJqQ2czG0V/j3KD8uI+LnVYhhUVUZWjlH0' \
			b'aOxUSSw/ljzVuZFMTOyXvAvLr7nWEOUdDxJbK7E5YdkLy1yc9wblu2PNR9VGkVJti+qmMbe3rrnXBRGayKyXiqEPsS5gGQqXxNzEzEG5mEk2F+gVFeIVurW3GMNU+3P+e9P0VGSu6dum75owNGG8zUJxd0KpheLvhFILJdwJpWwvgrSnvVyMNBtDJx1Jp825' \
			b'tLxWQq2RzidzCqpWu52t1Wt8Tfw9dy1OvG25NzhlXlvMUfLgJY+eszi6ZvRatFNBnmljes/rQMPLKMSLAvhBxxvaTZSHo/ahnY4s+NXBNIM9ibwQY1J6zifGpLBOhD0Ro+sz9ogNerdtT4XFQUpaFD0yhyejwNjGPqTtFSlaDWif39/urhll0VzMsjvJQvIt' \
			b'Elmf+xuQf+RWjBkQw2UFcfZisKwGh1AAkeC55Z+yeqthMDAMbm81SDwaMUHeajG42519ypPJDd6UwVvdKoCRmTxG9o/t7RaLZbFcueuaT3tQh9SycNlsTNebMVp7dY8RdP7ZGG5CNjDrwCrW6VBIxk6m04k8IyOiTsbQppj96/nlM836K8wlnC/7mACRykHs' \
			b'XPW86WuZXJXJhqzShu2d3+yFuFfjVhtLVQxFIU5MhTEvdRipEVmQUVIIEhcJz4hFDag4CwH2g7DumfWZocBL328+QTdGuxpfD8nJ6CcDlhEDlhEDloHARwl1RstbClMmkGxqZaXplVb2NnTMzGlZ7u4NAiPntJikbjwd/pwi1fWnxRgBazitoiSOxkNDHOZR' \
			b'tUoaMUEasTxKFTSrn73OOtDV6jIa7npb9prY+lp9PFtew3aL/C2Skc3bbMoC/Hfzr2vqlM7MZeVyL4aC9kKGgFk5YERkdTmKlZFQ/tTqUydP5y2KRFStbFgTin6a1X6akQ4axhu3eoEId0uNdEtvsY0CmmJFU6z0CxTfVvt4Rjp3dLnt+A7DrVaUIPVZEH0J' \
			b'Wp0h1XOZ236FAYY9kwEGjyzsTbHbYPhjdJBiZZBiZZBCl9htCpnHzbor6K8bmde2Mn/MjaVYE0epx+UR8e8upKPiLnSw+pqHtI6XAuOXcue0zXW3d44KvQCr5plZv6WXPkgawQ/z51ZkeSaQJwZd1XUiZp1ooRMtdDpUdjpGdqc0ooBSe1VqH1tnUWrPSu1V' \
			b'm/2aDj3KRbLqJav+Nlvax3Cb8w/N9mLnC1oZB9GNILoRYpXbkBxUXiGrhunFXl/sz9b2+QoZ7iXDPeNIzNO6XpyzltnzkNlBpDTIS4PSDectgvGc2R/OmH3ozqhLDVtda9heyP6oVy2gRzWUcICaBRxNUQZs8NCRO2/zIGimIQmnn8tD6jnJ2az2MiyDgNyr' \
			b'qLguzAUm1eGaWq2NHVFuIUk8kB+vMtSVfCnTJKiWwlioJAzkAxlBTiBEZAdzR8gTZokwRYTZI8wcYTsY6h1sEsMOMcpfh71LkDCqTqzCxRJcrK5Fo4cWD2vzUIbYxYO9N9g5w3tCiQ6LNbGDhmttlCGFYe0n+jXYVYYdZdhHBtsWVo1jkTQWBWNCA3MdmOjo' \
			b'iRamFdhVsFIYfSBsJUG1DpMyNhfB0A+T/IgGB1tsPXbZYlOh4z2q2LzpsSeWHLYs9/JPr66oicEWVt6NiJ24CMf+yzGR5f/E3arHPT0feA94w5u6oXcrlMEKhbCC6vFe6gG7OqlIVj32LlMAFfKKMLHCptERrPWyTXlKxK9N2M8u2AiKW5LDSrQHbFGM3mja' \
			b'2DTJWcTmW/ixpZTUZDViUyd74nueN1xj2zdF1mYpcQoqRGz0HON+ZMoCHjW8uzsy2SOTiJiiCjaTGKKF7LGztpPYqNxWDvuisWEUMUM4FDxLGrtysc1+8BIhNvji3axknFXukAbIUXD0z9kaXjf/54f7ICTFv78CBsJ90JL+34dOEAY42GhwDyr/T9hkUCkU' \
			b'VUJRGUhNcEXoD0C2wHoO6G1gLkDMoN0G2AKoJUC3gjMHZA7GYQv4tiBvHeIUbcdDFu/Hj2CpYbINIiU4BA8bsVBioNT9LXqfa3um6dDwNZrNfSdS0T5rqbiB1N2IU0tlr9BY2aS00vNObfz2hsujyQqDzlHolAX3ElTVu0zbQ2rB5k23KD9lqUUuhxoI3HJF' \
			b'5e+v2EoRHVbwY7X8ztYqgqJd01LlrRQAYhUkRIf17VjQPgMMNJ8GMiNjI4wMjSC748eIDYLDOP0tAQoe5ziBP4MKecWVmBnX/IEpO6Z39E1BFe4UWKAbPUNLElR8cTJBXwNRibUxoQvImlDFmS6QJYJI6Er8jFubFxWBsj5rWDhKhRsTzWLNGxU73kcNNFJr' \
			b'wXrq7H2gm/SCruafPJXH2BwzdIZTweV6UHaXxeVNxGTHOo1okXtptbTF6qYGS57lbgkyOdoMmdzWJGSmOAtk1qnOOLAVXwAoWt7AnlnjpyiNdAJTTjPEwBKjXbsBpPqsgGmUSwJq4ms7UJXId5LkDKlRMoJVJptFvAarazDqyvbzxBF6B88JnqLOyNIcm92E' \
			b'za50i7BZtJrdvNVMcZbY3OoYm0WQNJ5dtwGYSqTAlPZTAytgdpuAKfQlMFUoGTAnpnYAU4i88jYHpopFgSmNaBbxfsD0twKYN7U/2/Fgr+OZuRk4/QROX7pF4PQFOP0cnFOcJTirVGcc2IqvCE4/gRO3EZpKotD0As3p1QqdfhM6hb5Ep0olQ+dEugOdQsSl' \
			b'XaFT5aLo9ILOFPGyLm64Q+k5o7Rn3cYrc5RO1k95lrtFKO0LlPZzlE5xliitUp1xYCu+IkqT/ZMPoVOUKomitBeUTq9WKO03oVToS5SqVDKUTlHvQKkQ+U6SnKNU5aIo7QWlKeJlKO3vUHrOKB1Yt0E+R+kwoXQo3SKUDgVKhzlKpzhLlFapzjiwFV8RpUNC' \
			b'6ZBQqiSK0kFQOr1aoXTYhFKhL1GqUslQOkW9A6VC5DtJco5SlYuidBCUpoiXoXS4M+XeBLgaVnIUmNiMcCHG+CKBAlqhyN0S0JrCcmTmlqMUZwHaOtWSCVuxprg1yXKEW8VtJBHcGrEbpVdL3JpNpiOlL3AbBZNwm6Lejlsl8iL5OW6jaAS3RkxHWcTLcDve' \
			b'4fZG4JaHrIZXpTFuveBWDu4208BVKHK3CLfFwNXMB64pzhK3VaqdbiGZ3rAVbxG4afBq0uA1kihwZfCaXq2Au2nwqvQlcFUyGXAn0h3AFSIvoi+Aq7JR4MrgNYt4GXC79g65NwK5gbWcHSM3CHKDIDdMyA2lW4TcUCA3zJE7xVkit0q1ZMJWrEXgpoUKuI3A' \
			b'VRIFbhDgTq9WwA2bgKsJFMBVwWTAnaLeAVwh8iL5ArgqGgVuEOCmiBcCt7sD7o0ALtufUDZif+LFXJ1c2iatwROK3C0CbmGFMnMrVIqzBG6VasmErViLwE2GKJMMUZFEgSuGqPRqBdxNhiilL4GrgsmAO0W9A7hC5EXyBXBVNApcMURlES8E7t1ypZsBXDZJ' \
			b'oWDEJGXEKiWfBOGLAnco3SLgFoYpMzdMpThL4FaplkzYirUI3GSbMsk2FUkUuGKbSq9WwN1km1L6ErgqmAy4U9Q7gCtEXiRfAFdFo8AV21QW8ULg2gTc7vyx22eH395OBENJsFIYssM9iA2DmC9cP0frsindIuuyKazLZm5dnuIsrctVqiUTtmItGphNMjAb' \
			b'BnHHXxQbxNCspGpoNmJonsIrQ7PZZGgW+tLQrALKDM1T1DsMzULkpQQKQ7OKSA3NshI4i3ghmNcveprtbbkZU0K7kHvVTS3HQi6mFjCVEXa1w5YbLQuXTw31EqKNsC3dlVbZ4/3ZGsVu+q8a4irlGRe24i0CGAvxUfaRh9gOW0lmWqSoi6Fi8lVDbGfYRXSp' \
			b'LZYEy7ZY5TNfsY+gHS2x5bX7fWRw3hRLpLEpRiFC1s1KcJxyP8Px6O5zDRZ6unaMW18vKD69NjiMh15cfFPbYN6vBPGhtJx0pJ10pJ10pN2EYVe6RR1pV0DYFRBuY6QlgKtkCxekHS55w2pj7mAYl/rTGY6VSvvTsusmvV3B2G3qTwt9iWGVT9afnqLegWIh' \
			b'8lIABYiVUQWxE+imiBc2wdXCqdMD8t1AeDeELVuwIH2xYFmxYFmxYNnJgiUUuVuCX1tYsOzcgpXiLOBbp1oyYSvWtAm2yYJlkwUrkghwrViw0qslcO0mC5bSF8CNgknATVFvB64SeZH8HLhRNAJcKxasLOKFwK3WUh0JuNkm+Tv4Hg2+bMeyfMbASo4aYPiK' \
			b'HctOdiyhyN0i+BZ2rFHmfLFLFacjDALiAeG2tmbVaZes2IrBCOJkzbLJmhVJFMRizUqvViDeZM1S+hLEKp4MxFPUO0AsRF7kX4BYy0ZBLNasLOKFIL5banUj4OtYyyF0WWrlZKmVk6VWblpqJZ7cLYGvK5ZauflSqxRnAdw61ZIJW7GmwHVpqZVLS60iiQDX' \
			b'yVKr9GoJXLdpqZXSF8CNgknATVFvB64SeZH8HLhRNAJcJ0utsogXAvdurdWxgKsW0msGMO/hg+RlD5+TQyHUiuWmnXwSlrtFAC528rn5Tr4UZwngXY4BXAQpgNNmPtxGACuJAlisV+nVCsCbdvMpfQlgFUwG4Cnq0U2Jb4axEHilm8NYBaQwlj19WfTLYGyq' \
			b'hVfH2ZBwYKPzHkcsHQOdeyPyymhkazIEOLcmu8mULM9ytwiHhSXZzS3JFfyqxGYJ24qdiD1bH+/CTwV2a094cXYT1CTmEmqa9wxqiYnNABOC+jQjfRDRZQVdU4x77pg11aqoO1SdAqp4XTHG836OqmlFsTzL3SJUFSuKnd+OqiqxWcK2Yieiyq9Bld+Bqk1r' \
			b'hjXmElWa9wxViYnNqBKCNaiSBxFVslg4xbgvqqolS3eoOgVUseEV9rF+jqrJ5CrPcrcIVYXJ1fXbUVUlNkvYVuxEVPVrUNXvQNUmq6rGXKJK856hKjGxGVVCsAZV8iCiSsypKcZ9UWVvxZbUG2l04bPK6NeNc+RNB5W5yi1C3lggb36wX4qzhOC6hBO1rYMU' \
			b'guP6c1cikQ7WRhmsSWAFyU2nlil9CUkVSgbJiakdphaVRydJzpGpYlFkjoLMFPGeyLw7EelckelZnyHVdobMdLymPMvdEmT6whDq54bQFGeBzDrVGQe24iueaNuuR2YkEmR6sYNqYHW67SYjqNIXyIxCSchMTG1HphL5TpKcITOKRZDpxQiaRbwnMm/HkUg3' \
			b'Epls54RI52eV+cnCKc9ytwiZhYXTzy2cKc4SmVsdI7MIUmRuOKssEikyxcCpgRUyN1k3lb5EpgolQ+bE1A5kClHkbY5MFYsiU+yaWcR7IjPUB0Xni/TcOaywPdTZn3zKPD2fHU6dgzgcaPHtHmCm7O8HaH8ZUIctZ1wH+QSCbEgtD7v205ZUocndldbm+vme' \
			b'1BTpmnPmmX2/hgMvW1LLIKzpYwOxDxvAr3QKftmXqoH1UWiQlpsfOZ9tVF17sLbGVVYMKrb5kl0N3VwzoNy5dghNPHXbV9tWcfh2lKBWEbJ1NYmlrCI4mH8H/KK2wCUgjOuKvnl1/CPlD3SevNsB2QKqFUTHHe3sJmuQb3Z/4IFqtxM6Xv6wR8u7qxwvv+PT' \
			b'Cls+qLDzQwqLv6BAuSi1vT2KwuMTSu6EP6PAdUCp8qW6r1PzHR8w+UyfUuh0/8bpfk4BEr7kJxXGSmfrbtyhdDacSFV96c9/FFU0iRa7W85Dh/1hdRjCuu7Pgkg3tZ90OXZVC50mme3odUzjkgN+0mqYf7Eq1F+sWqLl+44h9hw/bNV4SMYftrZe+JmpY38I' \
			b'p7PTggmIZxVKM/hiBOTnVWz+SNS+H4jaslGW2R0uUbNTvHv1vd0hv+hEMlz2lbYD90i2dcLx/btdNTyfCHoAXc/0/Jo+8gSRLP8e2mF7JzA3bOyh2N21u9nUE3cj+tr8mRmzn1YfvGLnb6yqkvtrqd4XmIe2Vu8Uxh8bvKZq/rNV8VD3dCwCW1m7a6rq67mV' \
			b'S1T1KwNJIOL2MlU+wcRafPqPYWL3hskBK393XdC4IizwRdTr7PkoJGCEu7bWAOnYQ0GAzYeLWobeLFF/GMQYApdVfePlo5emlasdJiS4/ZAQDoqE7Iu+12adOeW+//UjINf+LttidC1Wm2XafzXND5XG+/00vj+Oxo93Gn8KGl9OWt8gje8rjQ/7afyBxgLl' \
			b'KKC90/hT0HhzczV+qDT+WiZWYbOPqymubrnvcIQdPTPmeDNPe020Hk7Xj6rn+ej5UJZ7npqDIcyPS/X9chZ8WNT2G7z25j6lw8pdz6MeR7lh13Ez087xKvINC34uZcm5nor8+BYbxDPkVpujVuD4ltg6S80lLDRXscyMzauTXA5z5DUBec2M5npZ7WyxuO9z' \
			b'6+1VKmHEeazZ/7zOxaq+ctnnNs30uqYFa1t0Mcsw8rei2zs93b+CPY2K9Uq9hKISxTLS65rX31BpwrQxtqyM3VGUsdusj7ZYF3xNWrlzsf4+iwgNL5I4FS2VddP9Nk3lx+UK28Uae8k6dft6+h0rCDsONpqDqnKlLq0bWIHNnQKfrwIP/L9VgdcsET8TBQ6q' \
			b'wMN2BbbNq75J+7A61teONTVTU9HRvtjGxIqzRmFCsTthMFTILJAhlShKM2gxdm598U1FZ7NhrY39/jVyG4peUjBYMkOFtX8mE+YMcCb7t/bIdERCiQDOPPTpspnv+ER/1c2gD7t2P4H4WiZuEotfIhZbS6Y7Cel0c/RGCUVAXllKYYmU6ppb6uy9Kux9BLmr' \
			b'Iq4q4Ni37a8qaHDbjnV1GSR4/ypynxLZUfkVJRW/KdGO88qtr4ruM4xuNm78PIYtdONIZk3Jr29Lx+5zjljWbqY81Oik1pi6abSORswyOBnutGez9qBYT2/Am38og911q4+hygfzIeP9FXSnvb+Smmi806UtunSSxpNcl0bm8TR0iUoj16XPZ7Y7RXXCrPHJ' \
			b'muM+c+MG3elOUXeuY5I46o9r5l+l2qZL5rp1qb9U5WQOp028XnN93xqGBUzyramo6q88kU/17PPPLnw2VdugXtCls5g9yKuro8wW7FdlWT5iuwsDRMgl3Ad+4Pi0X99SOAbXFEh391Z8gqycW2La8nyS7YeK8L4mrFSfpvV1XRbO3pCzNfDZSezSxqbXHvui' \
			b'sDYyOjk3xBX/2foYDZPXcFBH4Dtex5XeQe5W5tjZoHgv88fM2WMzRxXDmj8szch8vF848O6wGZXs52VG3bEZpTqq+oPlXa7DmqfTHzPoj82gb9b/YWpg47Oer8xgODaDobnUHzPXz5mrjiPS87Wn44W2Hyk0P08IZ+ZM5wa5dFbQugzlZ/nEc3r4jB49jwcb' \
			b'nNMZPK/ROMof1ZR9k3ly16/5K0iYav07FUHxOstvOHbhDs2l/pi58biFi3Z5Xfm2w4HKGI3B8RwMwUUQeieLY2JRd+3RG03XHNoJ51lzjwnP/gC6gg+gfAZ1CY04+f7K5L28Q4/36rGsdyL8rZ0UZ3djcqPyRLElBcKhHOsd97K3OjOsC4XyqkeyY2+KLmGo' \
			b'dTZOZL+1p7aPKvX66eJ9FQpj0Su4OI7cSiVZ8zdGrcbmfJzIPuzoROyvWSLmPfVrjfBg9YhuyO6Xumi02EFVmB9YGP1NUUSYj87GieyH01FE03wOJ2IYb4wK2uZ8nFiU2tNRQdd8DidiuDEjBjQCZ+NE9uYMZB+/IrlfGYTm1FwXwPy4hUTKwh64Ohi3Defc' \
			b'PrXC2BzQoUzXhOJjzuvfEKm4vaxOhxPMOtBvEhAmxTa7cevT/d24I06Rkz9lObnmBJzIadcA5LPKKTQn4EROZ2vKx/cLdjmZoJb/fei3vL47irUUIuRdg5CTFTKWAJyuE+Eeeb7iiMK1zQk7mXDeNXY5XeG65oSdCLc7W+H65oSdCBcnm2KNSq/CttGvz3GQ' \
			b'HcsCYei96xILHPeVlUHHL+EsxoEP42px3qFQhrWUvsmcEPYVIWQP4tDkrgvK65AtsYFtXYNH/oKiKENVsD1TwzqAN3y9iKqXxgg70WW/DKLm/SkcB/QQCjDqCg5Szm5AnN1Ayb+++H/zETu1'

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
	_VAR      = fr'(?:{_VARPY}|{_VARTEX}(?!{_LETTERU})|{_VARUNI})'

	_STR      = r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY - {AST.Func.NOREMAP, AST.Func.NOEVAL})))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LETTER})'),
		('LOG',           r'log\b|\\log(?!{_LETTER})'),
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LETTERU})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
		('LIM',          fr'\\lim(?!{_LETTER})'),
		('SUM',          fr'\\sum(?:\s*\\limits)?(?!{_LETTER})|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?(?!{_LETTER})|{_UINTG}'),
		('LEFT',         fr'\\left(?!{_LETTERU})'),
		('RIGHT',        fr'\\right(?!{_LETTERU})'),
		('CDOT',         fr'\\cdot(?!{_LETTERU})'),
		('TO',           fr'\\to(?!{_LETTERU})'),
		('MAPSTO',       fr'\\mapsto(?!{_LETTERU})'),
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

	_VARPY_QUICK = fr'(?:{_LETTER})'
	_VAR_QUICK   = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK = OrderedDict ([
		('SQRT',          r'sqrt\b|\\sqrt'),
		('LOG',           r'log\b|\\log'),
		('FUNC',         fr'(@|\%|{_FUNCPY})|\\({_FUNCTEX})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
		('LIM',          fr'\\lim'),
		('SUM',          fr'\\sum(?:\s*\\limits)?|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?|{_UINTG}'),
		('LEFT',         fr'\\left'),
		('RIGHT',        fr'\\right'),
		('CDOT',         fr'\\cdot'),
		('TO',           fr'\\to'),
		('MAPSTO',       fr'\\mapsto'),
		('IF',            r'if'),
		('ELSE',          r'else'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR_QUICK})|({_VAR_QUICK}))('*)"),
	])

	TOKENS_LONG  = OrderedDict () # initialized in __init__()

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

	def expr_term_1     (self, expr_num):                                       return expr_num
	def expr_term_2     (self, expr_var):                                       return expr_var
	def expr_term_3     (self, STR):                                            return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_4     (self, SUB):                                            return AST ('@', '_') # for last expression variable

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
