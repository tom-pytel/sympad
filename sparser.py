# Builds expression tree from text, nodes are nested AST tuples.
#
# Time and interest permitting:
# sets
# var assumptions
# importing modules to allow custom code execution
# Proper implementation of vectors with "<b>\vec{x}</b>" and "<b>\hat{i}</b>" variables
# systems of equations, ODEs, graphical plots (using matplotlib?)...

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

def _expr_intg (ast, from_to = ()): # find differential for integration if present in ast and return integral ast
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
			b'eJztXfmP3LaS/mcWiAdQAxIvSf7NcZw8Y20nz3aCXRiG4TjOQ7C51nb2wOL971tfVVGkyL400z3unhkMpyVSJbJYrI9H8dC9V188/PbJt8++aL74l/e//0SXJ4++fkmX7x48f/TsCd08/ubZt88fvXn4/fMn/07er58/eKiXTq+Grl8++ubNwwcvHr3Q+6cP' \
			b'Xurdl+n2h3T7ndxyrEjl6eNn3/O7FN+/IuDFy+f4/f5L+n32/VP6/eEBQh4/e/kNuHz8lB/z79+fI64n3+LB198/A39fMvHDb58+fRAz8zymh5sHT7+LqcH71ZdPXjx58OJvdPvo2VfKPe6+TLc/pFvl/vnjb/4Wg2LmH/0dP09ePNJYXwojxAAonz747sXL' \
			b'b5H+S87fo397+CQ+hji/evzD46/w6sOvvn3JUtBMc7TfPWEZPf6afjgWEg/eevf2w/tPb/748OanH3/9+OntBwp6/z9/fnjz8a8/30+e39//483Pf/3+Lj38Md7+9vbTm3d//Jp7P/zx34X3Y/S/e/vx/ceP7+beP+fe6Hv7Y7r99Gni5ee37z7F+z9TSnP2' \
			b'fou3v/4y3f7y+6d/THz99eubX36bEv6vlO/f07s//fJf8fbT+w9Z8M8/x/sfP7x99x/vP2VymvLy14df/zdPjm4yqUw5++mnWe4Ts+//c8oaJTLl+Jf3795PHiq731Okf3789MeU77e//fjT2+ib4prS+uO3397OPB+/eN28urdyXeO6i0ZuDG5ss3J87Zp7' \
			b'pjGhWXWN7enmYgrlsBSw6nHTGfnxFNC5izyoc3kQbvFiKz9OHtAdxcUkPRLuvCZMgTFUw6aAVTfyHfE00NumscOFBqw6y7GCA2sbay7USz6+c6BrkKpENwWIz8b36AUXg3BLd4b/DaVvL8S/4jg7DRcempXRQPF74t+y4MYYQHngO2LetBxTKz+O4jYaeQqC' \
			b'GFMoblFu9O8bOzYrfyF+ugHFKD9OgumORIw7CkfKEJHknAJC5unlggC8h8JAzoVp9YJ3Ek43D3e1d5gH+crr2jxoZQYWSKuqhNKRkuvkFmSUY2QfcbtEEIOTd2VYEJ4LoYVWi3cVmIDCTdeQFqFUDCWGXDaQUyeavYECSPHdnoRUZHPCleHUA/33jbORKyoA' \
			b'yblV3UdxUbHaHAH0LAZPAZALQlwK6STEpxAjISGGkO6xRvfyk4EAmOKbID+s/6LQ5MMt7nx8eKFe8sUHkoaTHzdMeZ+CxjwItxCMlR8qtouLdAsaYkTp1Etw4bRGeaDKAwAY5g4lwRRcjdhYfUnNQGGCwcnruNBsRCUJgOuUQXTOI/8N1EzEmQdrAPk52UF+' \
			b'SCcv1E+gY9boScfxqs9LLUI5I11JWoMsiAKyWqvKhJgvCrznEuLYa2Ks5HMsyQ5y6KY7o3ddfCg1DtIdL6gBeNU2pJSUCIGPhE6oIY2jH09MNt43oW1C1wy+GUIz9M0wNMPYjG0zklAHcIyEOxQqYZXUlsqHqEh7g2mCbYJrAkUSmtA3vW96eoqiQCaHthmo' \
			b'pAxyT+VIOti15G8poKWQ1qF6QZVum4HKqKW3h6YfAT3PCPOh8X3jSZzEUWhGgpMBohzpmCdpoMYk/RtNM1KeApSASo7QQRlrAho/8pEwKKMdRIHqCH4SBl8sB6Magxc+orHq8/LQewkOElWQUJIYhw4SIYkCl04uMbWBk7mtwr9H+WEZET+3WgyDqsrIyjGK' \
			b'Ho2dKonlx5KnOjeSiYn9kndh+TXXGqK840FiayU2Jyx7YZmL896gfHes+ajaKFKqbVHdNOb21jX3uiBCE5n1UjH0IdYFLEPhkpibmDkoFzPJ5gK9okK8Qrf2FmOYan/Of2+anorMNX3b9F0ThiaMt1ko7k4otVD8nVBqoYQ7oZTtRZD2tJeLkWZj6KQj6bQ5' \
			b'l5bXSqg10vlkTkHVareztXqNr4m/567Fibct9wanzGuLOUoevOTRcxZH14xei3YqyDNtTO95HWh4GYV4UQA/6HhDu4nycNQ+tNORBb86mGawJ5EXYkxKz/nEmBTWibAnYnR9xh6xQe+27amwOEhJi6JH5vBkFBjb2Ie0vSJFqwHt8/vb3TWjLJqLWXYnWUi+' \
			b'RSLrc38D8o/cijEDYrisIM5eDJbV4BAKIBI8t/xTVm81DAaGwe2tBolHIybIWy0Gd7uzT3kyucGbMnirWwUwMpPHyP6xvd1isSyWK3dd82kP6pBaFi6bjel6M0Zrr+4xgs4/G8NNyAZmHVjFOh0KydjJdDqRZ2RE1MkY2hSzfz2/fKZZf4W5hPNlHxMgUjmI' \
			b'naueN30tk6sy2ZBV2rC985u9EPdq3GpjqYqhKMSJqTDmpQ4jNSILMkoKQeIi4RmxqAEVZyHAfhDWPbM+MxR46fvNJ+jGaFfj6yE5Gf1kwDJiwDJiwDIQ+Cihzmh5S2HKBJJNraw0vdLK3oaOmTkty929QWDknBaT1I2nw59TpLr+tBgjYA2nVZTE0XhoiMM8' \
			b'qlZJIyZII5ZHqYJm9bPXWQe6Wl1Gw11vy14TW1+rj2fLa9hukb9FMrJ5m01ZgP9u/nVNndKZuaxc7sVQ0F7IEDArB4yIrC5HsTISyp9aferk6bxFkYiqlQ1rQtFPs9pPM9JBw3jjVi8Q4W6pkW7pLbZRQFOsaIqVfoHi22ofz0jnji63Hd9huNWKEqQ+C6Iv' \
			b'QaszpHouc9uvMMCwZzLA4JGFvSl2Gwx/jA5SrAxSrAxS6BK7TSHzuFl3Bf11I/PaVuaPubEUa+Io9bg8Iv7dhXRU3IUOVl/zkNbxUmD8Uu6ctrnu9s5RoRdg1Twz67f00gdJI/hh/tyKLM8E8sSgq7pOxKwTLXSihU6Hyk7HyO6URhRQaq9K7WPrLErtWam9' \
			b'arNf06FHuUhWvWTV32ZL+xhuc/6h2V7sfEEr4yC6EUQ3QqxyG5KDyitk1TC92OuL/dnaPl8hw71kuGcciXla14tz1jJ7HjI7iJQGeWlQuuG8RTCeM/vDGbMP3Rl1qWGraw3bC9kf9aoF9KiGEg5Qs4CjKcqADR46cudtHgTNNCTh9HN5SD0nOZvVXoZlEJB7' \
			b'FRXXhbnApDpcU6u1sSPKLSSJB/LjVYa6ki9lmgTVUhgLlYSBfCAjyAmEiOxg7gh5wiwRpogwe4SZI2wHQ72DTWLYIUb567B3CRJG1YlVuFiCi9W1aPTQ4mFtHsoQu3iw9wY7Z3hPKNFhsSZ20HCtjTKkMKz9RL8Gu8qwowz7yGDbwqpxLJLGomBMaGCuAxMd' \
			b'PdHCtAK7ClYKow+ErSSo1mFSxuYiGPphkh/R4GCLrccuW2wqdLxHFZs3PfbEksOW5V7+6dUVNTHYwsq7EbETF+HYfzkmsvyfuFv1uKfnA+8Bb3hTN/RuhTJYoRBWUD3eSz1gVycVyarH3mUKoEJeESZW2DQ6grVetilPifi1CfvZBRtBcUtyWIn2gC2K0RtN' \
			b'G5smOYvYfAs/tpSSmqxGbOpkT3zP84ZrbPumyNosJU5BhYiNnmPcj0xZwKOGd3dHJntkEhFTVMFmEkO0kD121nYSG5XbymFfNDaMImYIh4JnSWNXLrbZD14ixAZfvJuVjLPKHdIAOQqO/jlbw+vm//xwH4Sk+PdXwEC4D1rS//vQCcIABxsN7kHl/wmbDCqF' \
			b'okooKgOpCa4I/QHIFljPAb0NzAWIGbTbAFsAtQToVnDmgMzBOGwB3xbkrUOcou14yOL9+BEsNUy2QaQEh+BhIxZKDJS6v0Xvc23PNB0avkazue9EKtpnLRU3kLobcWqp7BUaK5uUVnreqY3f3nB5NFlh0DkKnbLgXoKqepdpe0gt2LzpFuWnLLXI5VADgVuu' \
			b'qPz9FVsposMKfqyW39laRVC0a1qqvJUCQKyChOiwvh0L2meAgebTQGZkbISRoRFkd/wYsUFwGKe/JUDB4xwn8GdQIa+4EjPjmj8wZcf0jr4pqMKdAgt0o2doSYKKL04m6GsgKrE2JnQBWROqONMFskQQCV2Jn3Fr86IiUNZnDQtHqXBjolmseaNix/uogUZq' \
			b'LVhPnb0PdJNe0NX8k6fyGJtjhs5wKrhcD8rusri8iZjsWKcRLXIvrZa2WN3UYMmz3C1BJkebIZPbmoTMFGeBzDrVGQe24gsARcsb2DNr/BSlkU5gymmGGFhitGs3gFSfFTCNcklATXxtB6oS+U6SnCE1SkawymSziNdgdQ1GXdl+njhC7+A5wVPUGVmaY7Ob' \
			b'sNmVbhE2i1azm7eaKc4Sm1sdY7MIksaz6zYAU4kUmNJ+amAFzG4TMIW+BKYKJQPmxNQOYAqRV97mwFSxKDClEc0i3g+Y/lYA86b2Zzse7HU8MzcDp5/A6Uu3CJy+AKefg3OKswRnleqMA1vxFcHpJ3DiNkJTSRSaXqA5vVqh029Cp9CX6FSpZOicSHegU4i4' \
			b'tCt0qlwUnV7QmSJe1sUNdyg9Z5T2rNt4ZY7Syfopz3K3CKV9gdJ+jtIpzhKlVaozDmzFV0Rpsn/yIXSKUiVRlPaC0unVCqX9JpQKfYlSlUqG0inqHSgVIt9JknOUqlwUpb2gNEW8DKX9HUrPGaUD6zbI5ygdJpQOpVuE0qFA6TBH6RRnidIq1RkHtuIronRI' \
			b'KB0SSpVEUToISqdXK5QOm1Aq9CVKVSoZSqeod6BUiHwnSc5RqnJRlA6C0hTxMpQOd6bcmwBXw0qOAhObES7EGF8kUEArFLlbAlpTWI7M3HKU4ixAW6daMmEr1hS3JlmOcKu4jSSCWyN2o/RqiVuzyXSk9AVuo2ASblPU23GrRF4kP8dtFI3g1ojpKIt4GW7H' \
			b'O9zeCNzykNXwqjTGrRfcysHdZhq4CkXuFuG2GLia+cA1xVnitkq10y0k0xu24i0CNw1eTRq8RhIFrgxe06sVcDcNXpW+BK5KJgPuRLoDuELkRfQFcFU2ClwZvGYRLwNu194h90YgN7CWs2PkBkFuEOSGCbmhdIuQGwrkhjlypzhL5FaplkzYirUI3LRQAbcR' \
			b'uEqiwA0C3OnVCrhhE3A1gQK4KpgMuFPUO4ArRF4kXwBXRaPADQLcFPFC4HZ3wL0RwGX7E8pG7E+8mKuTS9ukNXhCkbtFwC2sUGZuhUpxlsCtUi2ZsBVrEbjJEGWSISqSKHDFEJVerYC7yRCl9CVwVTAZcKeodwBXiLxIvgCuikaBK4aoLOKFwL1brnQzgMsm' \
			b'KRSMmKSMWKXkkyB8UeAOpVsE3MIwZeaGqRRnCdwq1ZIJW7EWgZtsUybZpiKJAldsU+nVCribbFNKXwJXBZMBd4p6B3CFyIvkC+CqaBS4YpvKIl4IXJuA250/dvvs8NvbiWAoCVYKQ3a4B7FhEPOF6+doXTalW2RdNoV12cyty1OcpXW5SrVkwlasRQOzSQZm' \
			b'wyDu+ItigxialVQNzUYMzVN4ZWg2mwzNQl8amlVAmaF5inqHoVmIvJRAYWhWEamhWVYCZxEvBPP6RU+zvS03Y0poF3KvuqnlWMjF1AKmMsKudthyo2Xh8qmhXkK0Ebalu9Iqe7w/W6PYTf9VQ1ylPOPCVrxFAGMhPso+8hDbYSvJTIsUdTFUTL5qiO0Mu4gu' \
			b'tcWSYNkWq3zmK/YRtKMltrx2v48MzptiiTQ2xShEyLpZCY5T7mc4Ht19rsFCT9eOcevrBcWn1waH8dCLi29qG8z7lSA+lJaTjrSTjrSTjrSbMOxKt6gj7QoIuwLCbYy0BHCVbOGCtMMlb1htzB0M41J/OsOxUml/WnbdpLcrGLtN/WmhLzGs8sn601PUO1As' \
			b'RF4KoACxMqogdgLdFPHCJrhaOHV6QL4bCO+GsGULFqQvFiwrFiwrFiw7WbCEIndL8GsLC5adW7BSnAV861RLJmzFmjbBNlmwbLJgRRIBrhULVnq1BK7dZMFS+gK4UTAJuCnq7cBVIi+SnwM3ikaAa8WClUW8ELjVWqojATfbJH8H36PBl+1Yls8YWMlRAwxf' \
			b'sWPZyY4lFLlbBN/CjjXKnC92qeJ0hEFAPCDc1tasOu2SFVsxGEGcrFk2WbMiiYJYrFnp1QrEm6xZSl+CWMWTgXiKegeIhciL/AsQa9koiMWalUW8EMR3S61uBHwdazmELkutnCy1crLUyk1LrcSTuyXwdcVSKzdfapXiLIBbp1oyYSvWFLguLbVyaalVJBHg' \
			b'OllqlV4tges2LbVS+gK4UTAJuCnq7cBVIi+SnwM3ikaA62SpVRbxQuDerbU6FnDVQnrNAOY9fJC87OFzciiEWrHctJNPwnK3CMDFTj4338mX4iwBvMsxgIsgBXDazIfbCGAlUQCL9Sq9WgF4024+pS8BrILJADxFPbop8c0wFgKvdHMYq4AUxrKnL4t+GYxN' \
			b'tfDqOBsSDmx03uOIpWOgc29EXhmNbE2GAOfWZDeZkuVZ7hbhsLAku7kluYJfldgsYVuxE7Fn6+Nd+KnAbu0JL85ugprEXEJN855BLTGxGWBCUJ9mpA8iuqyga4pxzx2zploVdYeqU0AVryvGeN7PUTWtKJZnuVuEqmJFsfPbUVUlNkvYVuxEVPk1qPI7ULVp' \
			b'zbDGXKJK856hKjGxGVVCsAZV8iCiShYLpxj3RVW1ZOkOVaeAKja8wj7Wz1E1mVzlWe4Woaowubp+O6qqxGYJ24qdiKp+Dar6HajaZFXVmEtUad4zVCUmNqNKCNagSh5EVIk5NcW4L6rsrdiSeiONLnxWGf26cY686aAyV7lFyBsL5M0P9ktxlhBcl3CitnWQ' \
			b'QnBcf+5KJNLB2iiDNQmsILnp1DKlLyGpQskgOTG1w9Si8ugkyTkyVSyKzFGQmSLeE5l3JyKdKzI96zOk2s6QmY7XlGe5W4JMXxhC/dwQmuIskFmnOuPAVnzFE23b9ciMRIJML3ZQDaxOt91kBFX6AplRKAmZiantyFQi30mSM2RGsQgyvRhBs4j3RObtOBLp' \
			b'RiKT7ZwQ6fysMj9ZOOVZ7hYhs7Bw+rmFM8VZInOrY2QWQYrMDWeVRSJFphg4NbBC5ibrptKXyFShZMicmNqBTCGKvM2RqWJRZIpdM4t4T2SG+qDofJGeO4cVtoc6+5NPmafns8OpcxCHAy2+3QPMlP39AO0vA+qw5YzrIJ9AkA2p5WHXftqSKjS5u9LaXD/f' \
			b'k5oiXXPOPLPv13DgZUtqGYQ1fWwg9mED+JVOwS/7UjWwPgoN0nLzI+ezjaprD9bWuMqKQcU2X7KroZtrBpQ71w6hiadu+2rbKg7fjhLUKkK2riaxlFUEB/PvgF/UFrgEhHFd0Tevjn+k/IHOk3c7IFtAtYLouKOd3WQN8s3uDzxQ7XZCx8sf9mh5d5Xj5Xd8' \
			b'WmHLBxV2fkhh8RcUKBeltrdHUXh8Qsmd8GcUuA4oVb5U93VqvuMDJp/pUwqd7t843c8pQMKX/KTCWOls3Y07lM6GE6mqL/35j6KKJtFid8t56LA/rA5DWNf9WRDppvaTLseuaqHTJLMdvY5pXHLAT1oN8y9WhfqLVUu0fN8xxJ7jh60aD8n4w9bWCz8zdewP' \
			b'4XR2WjAB8axCaQZfjID8vIrNH4na9wNRWzbKMrvDJWp2inevvrc75BedSIbLvtJ24B7Jtk44vn+3q4bnE0EPoOuZnl/TR54gkuXfQzts7wTmho09FLu7djebeuJuRF+bPzNj9tPqg1fs/I1VVXJ/LdX7AvPQ1uqdwvhjg9dUzX+2Kh7qno5FYCtrd01VfT23' \
			b'comqfmUgCUTcXqbKJ5hYi0//MUzs3jA5YOXvrgsaV4QFvoh6nT0fhQSMcNfWGiAdeygIsPlwUcvQmyXqD4MYQ+Cyqm+8fPTStHK1w4QEtx8SwkGRkH3R99qsM6fc979+BOTa32VbjK7FarNM+6+m+aHSeL+fxvfH0fjxTuNPQePLSesbpPF9pfFhP40/0Fig' \
			b'HAW0dxp/Chpvbq7GD5XGX8vEKmz2cTXF1S33HY6wo2fGHG/maa+J1sPp+lH1PB89H8pyz1NzMIT5cam+X86CD4vafoPX3tyndFi563nU4yg37DpuZto5XkW+YcHPpSw511ORH99ig3iG3Gpz1Aoc3xJbZ6m5hIXmKpaZsXl1ksthjrwmIK+Z0Vwvq50tFvd9' \
			b'br29SiWMOI81+5/XuVjVVy773KaZXte0YG2LLmYZRv5WdHunp/tXsKdRsV6pl1BUolhGel3z+hsqTZg2xpaVsTuKMnab9dEW64KvSSt3LtbfZxGh4UUSp6Klsm6636ap/LhcYbtYYy9Zp25fT79jBWHHwUZzUFWu1KV1AyuwuVPg81Xggf+3KvCaJeJnosBB' \
			b'FXjYrsC2edU3aR9Wx/rasaZmaio62hfbmFhx1ihMKHYnDIYKmQUypBJFaQYtxs6tL76p6Gw2rLWx379GbkPRSwoGS2aosPbPZMKcAc5k/9YemY5IKBHAmYc+XTbzHZ/or7oZ9GHX7icQX8vETWLxS8Ria8l0JyGdbo7eKKEIyCtLKSyRUl1zS529V4W9jyB3' \
			b'VcRVBRz7tv1VBQ1u27GuLoME719F7lMiOyq/oqTiNyXacV659VXRfYbRzcaNn8ewhW4cyawp+fVt6dh9zhHL2s2Uhxqd1BpTN43W0YhZBifDnfZs1h4U6+kNePMPZbC7bvUxVPlgPmS8v4LutPdXUhONd7q0RZdO0niS69LIPJ6GLlFp5Lr0+cx2p6hOmDU+' \
			b'WXPcZ27coDvdKerOdUwSR/1xzfyrVNt0yVy3LvWXqpzM4bSJ12uu71vDsIBJvjUVVf2VJ/Kpnn3+2YXPpmob1Au6dBazB3l1dZTZgv2qLMtHbHdhgAi5hPvADxyf9utbCsfgmgLp7t6KT5CVc0tMW55Psv1QEd7XhJXq07S+rsvC2RtytgY+O4ld2tj02mNf' \
			b'FNZGRifnhrjiP1sfo2HyGg7qCHzH67jSO8jdyhw7GxTvZf6YOXts5qhiWPOHpRmZj/cLB94dNqOS/bzMqDs2o1RHVX+wvMt1WPN0+mMG/bEZ9M36P0wNbHzW85UZDMdmMDSX+mPm+jlz1XFEer72dLzQ9iOF5ucJ4cyc6dwgl84KWpeh/CyfeE4Pn9Gj5/Fg' \
			b'g3M6g+c1Gkf5o5qybzJP7vo1fwUJU61/pyIoXmf5Dccu3KG51B8zNx63cNEuryvfdjhQGaMxOJ6DIbgIQu9kcUws6q49eqPpmkM74Txr7jHh2R9AV/ABlM+gLqERJ99fmbyXd+jxXj2W9U6Ev7WT4uxuTG5Unii2pEA4lGO94172VmeGdaFQXvVIduxN0SUM' \
			b'tc7Giey39tT2UaVeP128r0JhLHoFF8eRW6kka/7GqNXYnI8T2YcdnYj9NUvEvKd+rREerB7RDdn9UheNFjuoCvMDC6O/KYoI89HZOJH9cDqKaJrP4UQM441RQducjxOLUns6Kuiaz+FEDDdmxIBG4GycyN6cgezjVyT3K4PQnJrrApgft5BIWdgDVwfjtuGc' \
			b'26dWGJsDOpTpmlB8zHn9GyIVt5fV6XCCWQf6TQLCpNhmN259ur8bd8QpcvKnLCfXnIATOe0agHxWOYXmBJzI6WxN+fh+wS4nE9Tyvw/9ltd3R7GWQoS8axByskLGEoDTdSLcI89XHFG4tjlhJxPOu8Yupytc15ywE+F2Zytc35ywE+HiZFOsUelV2Db69TkO' \
			b'smNZIAy9d11igeO+sjLo+CWcxTjwYVwtzjsUyrCW0jeZE8K+IoTsQRya3HVBeR2yJTawrWvwyF9QFGWoCrZnalgH8IavF1H10hhhJ7rsl0HUvD+F44AeQgFGXcFBytkNiLMbKPnXF/8PaWU8HA==' 

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
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LETTERU})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\$?{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
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

	def expr_commas_1      (self, expr_comma, COMMA):                              return expr_comma if expr_comma.is_comma else AST (',', (expr_comma,))
	def expr_commas_2      (self, expr_comma):                                     return expr_comma
	def expr_commas_3      (self):                                                 return AST (',', ())
	def expr_comma_1       (self, expr_comma, COMMA, expr):                        return AST.flatcat (',', expr_comma, expr)
	def expr_comma_2       (self, expr):                                           return expr

	def expr               (self, expr_eq):                                        return expr_eq

	def expr_eq_1          (self, expr_lambda1, EQ, expr_lambda2):                 return AST ('=', '=', expr_lambda1, expr_lambda2)
	def expr_eq_2          (self, expr_lambda):                                    return expr_lambda

	def expr_lambda_1      (self, expr_commas, COLON, expr_eq):                    return _expr_lambda (expr_commas, expr_eq)
	def expr_lambda_2      (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr_eq):                    return _expr_mapsto (expr_paren, expr_eq)
	def expr_mapsto_3      (self, expr_piece):                                     return expr_piece

	def expr_piece_1       (self, expr_ineq, IF, expr, ELSE, expr_lambda):
		return \
				AST ('piece', ((expr_ineq, expr),) + expr_lambda.pieces) \
				if expr_lambda.is_piece else \
				AST ('piece', ((expr_ineq, expr), (expr_lambda, True)))

	def expr_piece_2       (self, expr_ineq, IF, expr):                            return AST ('piece', ((expr_ineq, expr),))
	def expr_piece_3       (self, expr_ineq):                                      return expr_ineq

	def expr_ineq_2        (self, expr_add1, INEQ, expr_add2):                     return AST ('=', AST.Eq.ANY2PY.get (INEQ.text, INEQ.text), expr_add1, expr_add2)
	def expr_ineq_3        (self, expr_add):                                       return expr_add

	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                  return AST.flatcat ('+', expr_add, expr_mul_exp.neg (stack = True))
	def expr_add_3         (self, expr_mul_exp):                                   return expr_mul_exp

	def expr_mul_exp_1     (self, expr_mul_exp, CDOT, expr_neg):                   return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_2     (self, expr_mul_exp, STAR, expr_neg):                   return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_3     (self, expr_neg):                                       return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                return expr_neg.neg (stack = True)
	def expr_neg_2         (self, expr_diff):                                      return expr_diff

	def expr_diff          (self, expr_div):                                       return _expr_diff (expr_div)

	def expr_div_1         (self, expr_div, DIVIDE, expr_mul_imp):                 return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2         (self, expr_div, DIVIDE, MINUS, expr_mul_imp):          return AST ('/', expr_div, expr_mul_imp.neg (stack = True))
	def expr_div_3         (self, expr_mul_imp):                                   return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                        return _expr_mul_imp (expr_mul_imp, expr_intg, self._USER_FUNCS)
	def expr_mul_imp_2     (self, expr_intg):                                      return expr_intg

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add):           return _expr_intg (expr_add, (expr_sub, expr_super))
	def expr_intg_2        (self, INTG, expr_add):                                 return _expr_intg (expr_add)
	def expr_intg_3        (self, expr_lim):                                       return expr_lim

	def expr_lim_1         (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                           return AST ('lim', expr_neg, expr_var, expr)
	def expr_lim_2         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):   return AST ('lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg):  return AST ('lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                         return expr_sum

	def expr_sum_1         (self, SUM, SUB, CURLYL, expr_var, EQ, expr, CURLYR, expr_super, expr_neg):               return AST ('sum', expr_neg, expr_var, expr, expr_super)
	def expr_sum_2         (self, expr_func):                                                                        return expr_func

	def expr_func_1        (self, SQRT, expr_neg_func):                            return _expr_func (1, 'sqrt', expr_neg_func)
	def expr_func_2        (self, SQRT, BRACKL, expr, BRACKR, expr_neg_func):      return _expr_func (1, 'sqrt', expr_neg_func, expr)
	def expr_func_3        (self, LOG, expr_neg_func):                             return _expr_func (1, 'log', expr_neg_func)
	def expr_func_4        (self, LOG, expr_sub, expr_neg_func):                   return _expr_func (1, 'log', expr_neg_func, expr_sub)
	def expr_func_5        (self, FUNC, expr_neg_func):                            return _expr_func_func (FUNC, expr_neg_func)
	def expr_func_6        (self, FUNC, expr_super, expr_neg_func):
		func = _FUNC_name (FUNC)

		return \
				AST ('^', _expr_func_func (FUNC, expr_neg_func), expr_super) \
				if expr_super.remove_curlys () != AST.NegOne or not AST ('func', func, ()).is_trigh_func_noninv else \
				_expr_func_func (f'a{func}', expr_neg_func)

	def expr_func_8        (self, expr_pow):                                       return expr_pow

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
	def expr_paren_3       (self, IGNORE_CURLY, CURLYL, expr, CURLYR):             return AST ('{', expr)
	def expr_paren_4       (self, expr_frac):                                      return expr_frac

	def expr_frac_1        (self, FRAC, expr_cases1, expr_cases2):                 return AST ('/', expr_cases1.remove_curlys (), expr_cases2.remove_curlys ())
	def expr_frac_2        (self, FRAC1, expr_cases):                              return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_cases.remove_curlys ())
	def expr_frac_3        (self, FRAC2):                                          return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4        (self, expr_cases):                                     return expr_cases

	def expr_cases_1       (self, BEG_CASES, expr_casess, END_CASES):              return AST ('piece', expr_casess) # translate this on the fly?
	def expr_cases_2       (self, expr_mat):                                       return expr_mat
	def expr_casess_1      (self, expr_casessp, DBLSLASH):                         return expr_casessp
	def expr_casess_2      (self, expr_casessp):                                   return expr_casessp
	def expr_casessp_1     (self, expr_casessp, DBLSLASH, expr_casessc):           return expr_casessp + (expr_casessc,)
	def expr_casessp_2     (self, expr_casessc):                                   return (expr_casessc,)
	def expr_casessc_1     (self, expr_commas1, AMP, expr_commas2):                return (expr_commas1, expr_commas2)
	def expr_casessc_2     (self, expr_commas, AMP):                               return (expr_commas, True)

	def expr_mat_1         (self, LEFT, BRACKL, BEG_MAT, expr_mat_rows, END_MAT, RIGHT, BRACKR):  return _expr_mat (expr_mat_rows) # translate these on the fly?
	def expr_mat_2         (self, BEG_MAT, expr_mat_rows, END_MAT):                               return _expr_mat (expr_mat_rows)
	def expr_mat_3         (self, BEG_BMAT, expr_mat_rows, END_BMAT):                             return _expr_mat (expr_mat_rows)
	def expr_mat_4         (self, BEG_VMAT, expr_mat_rows, END_VMAT):                             return _expr_mat (expr_mat_rows)
	def expr_mat_5         (self, BEG_PMAT, expr_mat_rows, END_PMAT):                             return _expr_mat (expr_mat_rows)
	def expr_mat_6         (self, expr_curly):                                                    return expr_curly
	def expr_mat_rows_1    (self, expr_mat_row, DBLSLASH):                         return expr_mat_row
	def expr_mat_rows_2    (self, expr_mat_row):                                   return expr_mat_row
	def expr_mat_rows_3    (self):                                                 return ()
	def expr_mat_row_1     (self, expr_mat_row, DBLSLASH, expr_mat_col):           return expr_mat_row + (expr_mat_col,)
	def expr_mat_row_2     (self, expr_mat_col):                                   return (expr_mat_col,)
	def expr_mat_col_1     (self, expr_mat_col, AMP, expr_commas):                 return expr_mat_col + (expr_commas,)
	def expr_mat_col_2     (self, expr_commas):                                    return (expr_commas,)

	def expr_curly_1       (self, CURLYL, expr_commas, CURLYR):                    return _expr_curly (expr_commas)
	def expr_curly_2       (self, expr_bracket):                                   return expr_bracket

	def expr_bracket_1     (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):       return AST ('[', expr_commas.commas if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_2     (self, BRACKL, expr_commas, BRACKR):                    return AST ('[', expr_commas.commas if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_3     (self, expr_term):                                      return expr_term

	def expr_term_1        (self, expr_num):                                       return expr_num
	def expr_term_2        (self, expr_var):                                       return expr_var
	def expr_term_3        (self, STR):                                            return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_4        (self, SUB):                                            return AST ('@', '_') # for last expression variable

	def expr_num           (self, NUM):                                            return AST ('#', NUM.text) if NUM.grp [0] or NUM.grp [2] else AST ('#', NUM.grp [1])
	def expr_var           (self, VAR):
		var = \
				'partial' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_')) \
				if VAR.grp [0] else \
				'd' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_')) \
				if VAR.grp [1] else \
				self._VAR_TEX_XLAT [VAR.grp [3]] \
				if VAR.grp [3] in self._VAR_TEX_XLAT else \
				AST.Var.ANY2PY.get (VAR.grp [3].replace (' ', ''), VAR.grp [3].replace ('\\_', '_'))

		return AST ('@', var + '_prime' * len (VAR.grp [4]))

	def expr_sub_1         (self, SUB, expr_frac):                                 return expr_frac
	def expr_sub_2         (self, SUB1):                                           return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1       (self, DBLSTAR, expr_neg_func):                         return expr_neg_func
	def expr_super_3       (self, CARET, expr_frac):                               return expr_frac
	def expr_super_4       (self, CARET1):                                         return _ast_from_tok_digit_or_var (CARET1)

	def expr_neg_func_1    (self, MINUS, expr_neg_func):                           return expr_neg_func.neg (stack = True)
	def expr_neg_func_2    (self, expr_func):                                      return expr_func

	def caret_or_dblstar_1 (self, DBLSTAR):                                        return '**'
	def caret_or_dblstar_2 (self, CARET):                                          return '^'

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

		if pos == 1 and rule == ('expr_func', ('FUNC', 'expr_neg_func')):
			return self._insert_symbol (('PARENL', 'PARENR'))

		if pos and rule [1] [pos - 1] == 'expr_commas':
			return self._parse_autocomplete_expr_commas (rule, pos)

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_intg': # TODO: Fix this!
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
	a = p.parse (r'a, lambda: (b = 1) = 0') [0]
	# a = sym.ast2spt (a)
	print (a)
