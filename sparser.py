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

	if lhs.is_mul:
		if lhs.muls [-1].is_var and lhs.muls [-2].is_var_lambda:
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
			b'eJztXWuP3LaS/TMLxAOoAYlPyd8cx8k11o9c2wl2MQgMx/G9CDZOsrZzdxdB/vvWqSqJ1IP9mOn2dM80htOiKBZVLNbhsyjeu/zi4fMnz599UX3xb+9+/YkuTx8/++4lXR8/e/UNXZ48fkq/L7/j37+/eIWg53jw9XfPHuLm0dcI+/LBC/r99sGLR8+egPib' \
			b'Z89fPHr98LsXT/4TcV88eKiXRq8GRI++ef3wwctHL9X/9MEr9X2ZvN8n77fi5VTxli8pnX+H5+WrF8zkl/T7jFn9nvl5+Pzp0wc9xYueYuAUnhePv/kbEn3w9Fv6/erLJy+fPHj5N/I+evaVMgTfl8n7ffIqQ4/+jp8nLx9pcJ8npPZKGKHXIebjr1myTPDt' \
			b'E5bzV4+/f/wVKB9+9fwV5+WBZgaievCKs/boPx4+6ZNB8LcvHj/lV7x6Tj9v33x49+n1bx9e//TjLx8/vflAQe/+9/cPr9+/+fT67W+/5Lcffvufye3H/v7tm4/vPn58O779fXzb33384/d3w2v+8cevb1+/+fDP9PBH8v4r8fHrH+9776d3Hwb/jx/evP2v' \
			b'd5+GN/zx4Zf/y5gbvXl4F9H0/t8p27/2N29+HOK8+fQp8fbm7ZDQ7ynvYDmxO3CU8fzLz0Poz78OSbz/45fXP78fhPLTz/9K3n/8Y8jvu3/mBOQZWPvpp5Tqu/8esvjbr0P4L2/e//jTm/5uiJOivn//ZnTz8Ysfqst7K9dUrrmoxGPgsdXK4WpMda+rmrqi' \
			b'ENuQ56IPlbAUsDIWvpb/na9W3UW6N+mWPCBo5McrfUP0/GLT4oVIr8ELjZAhVMJSwMpISp54CcSLr5wmRi83gXPh8RMqay/0lu7YFzmPlpLUR32A3IWejp7HPgheJM//JvaknAZdGw2/kJuV0UC+R4KxcpblSPmj574y7dKzlZ+G6v1KXk+cgrzpycEJefEy' \
			b'BMtrjfw4omqEPgsyeSC8KHn695Vt+9c7eJB6LT++udBbKiz2EUVD3LG0hYaDXH7bePUgDO+jcoQg9e18h3K1VK6j4Di7M6OQdnbn8pBVw7qB8mta9d0zfHPBcmUlJZL+fiUCpAxYfdfwUAOHm5VkynPpkjjChdyuWLMaCncV5ZjLKFTece7AkmjncgRGnt8u' \
			b'nplEWzWiGEGR00BcbUU5yABED4fwFNJKiE8hnYSEIQQljpDYh5DCsYLU8pMw5GpFAikx/0D8iknoNXnha/uHF3pLd/0DDur438UhjxrQZgHwIfdWfqhcLi6SF75aClzUFpVVw2pr60pU0Viu2RqtaKzWHRSqYVmA4UKwA+Kg9vKWTn5WKlR4jWST4MZ6Lw/o' \
			b'1nEuqRDu+axYOf9coNC4vlDjoLekfK4ZFFdvzTjApNe4yks1Sppge49TD2W+9zWirFzPUS2swAE0RUr0jnBBbcMlxEV+1HeUbeLbgmUqv1BXAXUQkEtCRSq+8qGKVVt1Veyqtq7apmpd1XrWRfql7NJjU7W28rHybeUpHVMFWwVXBV915AJqKCp8Km7XUftA' \
			b'NQ/lqeqaqiMZ1tRQoTmiMqKsVqFqKcG2aruqo0cG9SXBmpBEuKDsBHKxCm0ViKW6ig3UldSSSpRUhcDc1EiO7mq0ZcRroAuR1rhGNI70LpJIwAW3JA3ck0T4YjkYJY1b3FEcEhDfdfKQxMTBRoJNJ08lYTSqnDAxRvd3XNhepOtFupF/WxWQiC3Kpe3Lo2XJ' \
			b'n2yW77WN5Mer6qgiiRxs6JVDRcE6cjJZUzh4Yd6z+ne26twt09t7vpOcBiOVhZWLE/wz6QWuUrhBCrfTSxBaJzrvWFjeor0/pjxeorN3rqCc1OGuS6UkGn1cbHppXHyTsRmrjsoCg7n62LgVfHTMbc4nV/vy0PUVvmsUTAoubVwFWq1UNUGwBBaYhpE2UdVB' \
			b'jzOdFZ2+jZp7T2uZtr3zIL7XSheiq1VzWMH2lbjThtzZvabqJNWGU6fhAY3caACBwR717+s7rtuNKndg9EfKX6xiW0XqZ/gqmirauy0gkkx7lkxBMt1ZMsuSifVZMovVTZQeiJVefuO0P9L3SyS41TqJSTk89KOBqLVVXZmLW9/a8oyJkakSc8c7YTwzRELY' \
			b'MvNWsy8Suz1CMK0oRMcXW5/1ApN/Jp9l9IyZ25bLyJm6Ndlpb1d2IuPx5LPR1rcgG5jWNjwfLI0nZQGZOq0sGMmCZ9hPp3W8NAKTKX7tUsmE6SGY6twwU2tkptbITK1B36wTabsgnDvmXCc+bWqVpKmS9uiOzJn4fi6f5XdMrPHEdNZ4YopWSo/rs+ObScfk' \
			b'rACjOU4GCYcCy649vsLuukNVDZgX12loIxPORuaZRZvOvVTMrps7Pnl8ibUFI2sLZ1noyF7XOUM9rDGMBjNtd8YOVhnM3tYDLicrXFhtYKX0Ulk1Un83anDSqJGK0SkpWf8wUt0NpReFNqrthSQRnRZilGms2C+pRTum1jKXMX3s607fa4JlAxiLa0/DsyG4' \
			b'H5vL8PyAlfkBK/MDGRFGypwWaYmd9R+jhE1NRBZCcWvl1mo/256agcUlhgX2xIYFPB6wt21uAyMXo+MKK+MKK+MKukx7MH4h0MWRlnvXjzysWBtYWc3HpVOgdgy545JC13eWRjhvJXNDgxCC3J+X60ojGpML7J7WTa1UVW03UhUncRsvTxsZsxruxJ4Xh6W5' \
			b'M9Lc3fVeCBBntY030rhjBvOMuEv0a87aIR2lIPVL7DttxJz0xtydX7kipt3p9RKJUTfrKhPTTjoqTjoqTidAnc58umOcmkKnh3tEUg5RuA1SLDyC+YEHRfy0E8VttGHsxp2SKJ2UNKAx4+ek29gnImb5d1zvKbN+YaBGbHvRIS865O94Fcqd+7suBFQenjHq' \
			b'BaNeMeovtAciGPXauoRlzQqiWUE0K/TQrEh0Kuhwkc0/BLmlYYQOw+LJLwJeIv9R8h9ZaDLlIrM4xG+cLqtBDExA2RTxtULeKkV7O4TS3YZsuFuQDehUpzteat3yUl/ItrnLGlilulA4kUoOvA2JMw+wZK7VmBnbIkOqI8HMIJmWc5dlYVEO0mWRalUFyHUw' \
			b'stkhgxjt9DMOWt3akZREkrKpQwSO1TCsDWH7Tk0VFTKAHCALyAMygRlXTLdibhUTq5hzxXwrNghiwx92+2GrH7oTEDD2eWF3FzZ2ofJDzYctDig+GKTDfBxG3ygq7AzCtiDsPcHGE2zuwM4ObJvAuizWZLFxDrvmMGWA/UWYW4FpK4w4Ya+Ibg6mbDGfi6lc' \
			b'zPJiipek0GBmFNOi2IqGPVuwj4dxPHYmIe9dSwWKbeYeO82xAVi2ImNPb8C+WGx2p0f0fuzMpWRWrdcd2dhZTVE979jFtlUS4irg6wBBifBpAMP7mnn/OsL0EfGwwocEsE8b942G5/8R7+dNv0gbadTYq41t7zX/RN2hLvGRgxY7u+mNvlWeXM8Kw26FfcYe' \
			b'+4WpzFekDbyvGRuIR+92DFG9c1aEYpgLbAVHdMsbp0VaeB+F4/X0CynV/MkCfoqt3di57LD5n17YIfNd/5Keb4rcanLY8dukXK1CxhmheUUlv4rKMT5cAHJqJlZtl/jk+F2iw35rSEaTw5cBbB4dyVJSAeWFHBK/wf1Q/enb+6AnNNznHf+Nvw9CQsV9bLYm' \
			b'7cP9X5iiQpWQVwjbVAd5XeCzWsCtg/0U7e0CzhnSu0K5BOMBtj1k2wlEJ/BkSOZQbDdAr4S7nTE3xVsY4wwY2xZTi0Dydg2CgJMZPmy9Dh8lbCgaeiSEiebPtL4baTi0u6DR3MMiRS20VnGmoUu9++u2XDFrvLIOwKi9bnTmLjVnjXYepFOx3KjFTPHXtVmU' \
			b'W+xxL7Zb3YLS79BOYcfsAIZ6ffuELd7YH43OBzb4DSCh+LDnwkbaEWCwJ7CByArQgN4voiPyByEij8WmSBGw4DfDSyMfcZDHGmkL+OTxJw6oaowgKzjlsXMMLuZb8MUM1swwUDJF2ijFAXVWkpyBjDNli1jj147g1osjDr4EPdyShmDM0g34y5iZNTN40PG3' \
			b'ffApHUVkIhg1NmhMsI/cU+PiIxoVK1jVPG8E6x57l9tjNAdoqbM5xeUSJp3g8lCY3AmPGzEY+Ts0Hf9mGGwUgrEAwWbeJ2y4S9iMe4SNdAjlNfqybZBXdoy8OG/Smri+VRulkWNtDLQUpwSzOIOZxA8DZQ4zTSu1cRkTc4zFhKwh2ghZ3G2LULT7XCV43Ie/' \
			b'eB7njLCjRBgiMMLGrRzfWr4sI2yhbesYYd0YYZ0grEtuK4R1RccI6xYQ1m1AWJ7GGoQNcUoIm/UbNX6Igy9DmBJkCEtMzBHWJYQN0bZEmD8j7CgRhjl6C4ThN0MY38qzRYTxgzHCECQPMoThtuHQwW2DsDz+xAFhfJkgjDlag7BRGmWEpTgFhPGjEcI0foiD' \
			b'LyGsTyshLGNihjAmFoSlaFsiLOyGsKMZ0mFN6CqjujXIK47q/A2N7Dai0KNAgEI/RqEXFPoSCn1yMzh6hqMfw9ELHHO6beDoi47h6Cdw1MEccyXsY8eKZ2Aq2QyeeZpr4DnEKYzm+JEIcoJSIQtx8GUoVQkquQI1sTMHqk9ATRxtB9R4BurpAjXyV3E7/s2B' \
			b'KkM+UxryCZ1ST4HKY7/JaoAuBozotgFq2TFQp2O/Hqgy/jOyNMB3dU82A2qe5hqgDnFKQNXmdDYkVLIwJJADVSWo5ArUxM4cqGlUmHG0HVDbM1BPF6gtf3C2498cqK0AtS0BtU1uBtSWgdqOgdoKUHO6bYDaFh0DtS0AtRWgtgJU6eoq2QyoeZprgDrEKQG1' \
			b'FaC2M6AKWYiDLwOqcqfkCtTEzhyoaaki42g7oHZ7Byrpsxga3AxcQxGx2K96a0FLDFoejNrxYNTKYNSWBqNCp9QT0FoelVoZlWJVjXLJF0m2mVBvAd08/sQBujaNTfEeBa6V0amVASrf1UrUdXPs5ol2a2eE0rsL8OVHItIxfJUsxMGX4NvLUskFvulVc/ja' \
			b'NHLNOFqAbzT3uQAXYNywQc3UlOY6iLZH3Pq6cQNstzS0+dzYbjJ8bzCy4dX9rXA+W+RHiKzz86EE8/VMjrCIfZfcFPudJMyR8jbbihXAiHQb4LuiY+BPbQV66DuBvhPoO4G+cjHFfZ8gCo8pcnOCjaYEmmqpJnBSE7hZTSBkIQ6+rCZwg6UB07dc7lwdOLY5' \
			b'UJIF2xojue2rhUFW02oB2aXawLL60YXrgmY/bfox1wC3uf8NeQuew7gpDwLnUIJz5mZwNhyqKWdwDgLnnHQbOIeiYziHApzFAggXwDkInCV8Buc8zTVt+BCnhNwgyA0z5ApZiIMvQ67yquTahid25m14SGBNHG3XBW/MebB8umCNsMoGWMezWn3bW5rVEjql' \
			b'nva7eVbLjme1rMxqjei2QWrZMVILs1pWZrWszGpZmdVSshlS8zTXIHWIU0KqzGrZ2ayWkoUhgRypKkElV6QmduZITbNaGUdbInVHc6JjRmp5nHyLwdrxCWrym4NVbCJsySZC6JR6ClY2jrBj4wgrxhEjum3A2hUdgzUZR9hseCzmEXyEljwAVAe6GVrzRNeg' \
			b'dYhTQmsnaJ0ZTShZiIMvQ6sSKLmiNbEzR2uym8g42nFsvKOJ0hm1x4VaPn4SqMVvhlq+tXxZRK3QKfUEtY7Ndd3YXNeJue6IbgvU5vEnDqjli6CW3yeodWKsi4uTB77O6KaoHSVaRm2KU0AtPxJJjlGrZCEOvoTaXoRKLqjN2JmhlukFtRlHO6J2R7OnM2qP' \
			b'DLUGwgZqzRi1RlBrSqg1yc1Qaxi1ZoxaI6jN6bZBrSk6Rq1JqE3dYuZJmHfywNcZ3Qy1eaJrUDvEKaHWCGrNDLVCFuLgy1CrIlRyRW1iZ47aZF+fcbQjavdvSnVeT7oR+Fo+XLjj3xy+sp7kSutJQqfUU/jyepKT9SRcUJBWQCzrSSPqbUBsi45BnNaT+K0K' \
			b'YllPcrKe5GQ9KdHNQDxJdw2OhzglHMt6kputJylZiIMvw7HKUskVx4mdOY7TelLG0Y443r+l1RnHN4JjL6et82+OYzGPdCXzSKFT6imO2TzSiXkkt8ISTYqUcZxTb4NjX3SM42QkyW9VHIuJpBMTSScmkoluhmMORgn17JaBPCRSArJYSrqZpaSShTj4MiCr' \
			b'MJVcgTzQLAA5WUpmHO0I5P1bYp2BfCNA5k97AMjjVSEnq0KutCrkMjcDMi8JOVkSwkUKkoEsC0Mj6m2AHIqOgZwWhvitCmRZFnKyLORkWSjRzYA8SXcNjoc4JRzL4pCbLQ4pWYiDL8OxcqzkiuPEzhzHaXEo42hHHJ8NtW4JjiMEDByPF4ycLBi50oKR0Cn1' \
			b'FMe8YORkwYj1z8tFkm0m1NvguOwYx2nZiN+qOJZFIyeLRk4WjRLdDMeTdNfgeIhTwrEsHbnZ0pGShSGBHMcqSyVXHCd25jhOS0cZR7vh2NRnHN8OHLeQLnA8tpJ2YiXtSlbSQqfUUxyzlbQTK2lcUJCt4FhspUfU2+C4LTrGcbKV5rcqjsVS2omltG4KTHQz' \
			b'HE/SXYPjIU4Jx2Iv7Wb20koW4uDLcKw8KrniOLEzx3Gyl8442hHHezKyyj7t9pmgLN9RPwN6CmjKMOA8RrOAuYTlVv+mOGYYt1UnDbLgWGAsKB7otkBwO/sDcBNuBbYNvrHFuwNCJegV8Ap2lW4K3CzJMmY1QgGwgtcZXJkkRL0mqKKkBKoJqT0HM5gmlPY8' \
			b'7AjRPdlV2ZNpbeVDn7cUnygcHgCb8QDYyADYlAbA9BIhNQtmkUKnKdd8cV4uknITErXZbgxsQtHx/qQ0BjZpDGxkDGxkDGxkDJzoZhuUxul2a+elUzKlbUoyDDazYbCShTj4sm1KyrSS6zal4VUL25TSMDjjaEdM798C65gBfXvRDHHy8rAfLw97WR72peVh' \
			b'oVPqCZo9Lw97WR7GhXLJF0m2mVBvAeU8/sQByj4tEvu0SOxlkdjLIrGXReJEN4XyNN0yjlOcAo69rBP72TqxkoU4+BKOe1kqueA4Y2eGY5/WiTOOdsTxZpssOZ1GoWzPaD5mNKOgam6b63HbXDOao6A5ugmgo24cZmqcsVLPMI2gIInLO9A819I819I818lt' \
			b'1TzXRcfNc52a5zo1z7U0z7U0z7U0zwPdrHmepLumbR7ilNrmWtrmetY2C1mIgy9rmyXEK7m2zYmdedtcp7Y5cbQjpvdvsXVG8420zQ6yRNs83lDItyznQtvskpu1zbyZ0MtmQlzQNjtpm2VL4Yh6m7bZFR23zWlLIb9V22bZUOhlQ6GXDYWJbtY2T9Jd0zYP' \
			b'cUpts+wg9LMdhEoW4uDL2maVpZJr25zYmbfNadNgxtGOOD7bcBVxrNMsJ4bnUMkGYT8eOXsZOfvSyNlnboZnHjZ7GTZ7GTZ7GTZ7GTaPqLfBcyg6xnMaNvs0bPYybPYybPYybE50MzxP0l2D5yFOZwcRLKBaRs5+NnJWkhAHX4ZqTU7JFdWJqTmq08g542tH' \
			b'VEfqph386/rbfFofOnrIAzMWD8nY8MX94UCMZhlnWx2CgU10R/QR/t0/wG+0iTvMYRVLR1Rs/DC/cjL5QP9OR1BscfYE0Y7Asd1ZNFc7fGJ+2sznO39iB0QMX63I0bAOCfhOsKmmZ1OE/Z0HsydYoClvrgSPvZ9PAUFvD4W4dE5F+nJIO4JA3xOYQCF2g8p3' \
			b'u7cHYU8HrpSPV7qS2q9rEHY6esWtOX7FrKn493b8ytKRR1dX87VnGUFa+1R1dFv3cBwLhF04kqXh4GItbzrU8nzoQ33trk7Y51lC0JUbO07IXOlIoT3p84IuT4/uOuiRQs1o49XnPFYIQt79aCES8mfopG+rtjxI3qvm9ufZjc6y27ZDUuia34gWf75DsYYD' \
			b'2PamxfJhMsPt3fUOykKruE6j0eGI9ynRv+So5MubH3ymkWecjD4/V4WMzLaF0eZadT4SNb5Sv5knv/Aw5mr8uc53kzebXStjezwKa/SM1XBgxY1bKG/Q6ZI7qMRoUAzP4K6wdnkYZdZVvfX1MLKFZ+4qiu32pth+D7rt96/Xi1Pw/dR7SbftsVfO2xmMXlW3' \
			b'kXrcq17HmV0o63UMRd1Gp471+2p67fem12EPep3pdN0drqOxVqfvrD7nugzxHKjTsUaXr6HHYW96HPerx0191uOb1GNzWnoc96bHZSOBq+lxc9bjm9Tjgw0CD6PH7dEMBD/nbAVOUt40+cargWuU1p/qWG/QT7B2yDkKmPYMNiCLq9x+3bJHv6SNaytL2obX' \
			b'9yj0LiptUWFvvHY9uKayAvi1Fhr7mU7bofaE9QVbW/BR0fXRqCQVwDCpdhD1zOz9tplMuzvq2vC3mVqeSDtAJwCWHbtMoO3UESB57aTA7TV0uB6btu6lci1aou+jgu2X42rV3PZA2guDXr9P/UVq0+/f71brblDdgkX4Hmre/nRx5Iu0DTlZrIRhG+EN18E7' \
			b'rsKdVfgQKsxunyocTl+Fo6hw2KzCtrq88Q7EsGHg0P3YJf1c0kmU40l1BFaD4f1B+6oLVsOFxt1Vl8eiVEehUOYklekIFMkfjyLdRO3kuT/SsH3QomLZG1WsYK+iV6Dap2oFu06zYE2/IresY9WfmObB9JynsbVn6yrKzOVxqNwx1F2ZfkHu53prY71V/Yld' \
			b'MnKAJFGcdSlVV/7kGkHskfU3q0z1/RWmpanTjh2zdNeyZrVnzco0K5yeZgW4Y9SsjjQrViaSXDHfYNET87V8mqTZTZtIiab6Ar3YpAdc9rNyR2s0FCYK7Bplp+lMWg4If4OwWcBT4bKEmkFCO0KOhLSAqz3Jifm9np6Lbi+1tNeSl+nldbWZsVhvPSEWrzfZ' \
			b'tbY2WpB4hNtDBdP2st9tGgoFc41JpnItwt4wmkAiji65OEgCkDX45sJ1Gi4l4KNIKGkUxGh+uKDgeyv9/quRs9Dl6JrsmxbDhytI5qMDv9g0tV8d6r8EgTKqK/3SA7jCNmGqYKnmo6ofv0tOIvQbahajUDLsQfZW5pAsU9O9+x+zZQ/Jlq3wR7po0wcH8v+G' \
			b'n6ATwrtII0fnjdIcw8nyXC02O/xMNj8z5+6QnFMlsvsfs+UPyRbhY+EPc/eFJzzL3sHPzIUNzMVr8kcdlNkfVheWwkd/zF08MHexutIf89af5BK3Yo86TlMOsfN9Ky6pJUJnuiv8YVopu6P6chaHGe52ZVi+8HNltjGy2Mn1o4AdHGesqa+WM/l20dXyJ7v8' \
			b'0zd+kF9TXcn1Y55d3GTwwlLoP4He3Lgg0C/CIFA8n8uJFMzRSMFVN+FECvaaUqDO3EwQ7jrC8NW1HCYEpqE7JCBCcUkofo9ysZtlA17XyydU4mCKHPbj1iRVeCRi8kcsprY6AidiClMxZR/eE3lZOZZ5J6lxNwHfzDPpa3nTL+SNvoLXfwFvg1jxFbu1osUY' \
			b'+kZdA+tbfOZ1NzopjHi8OotZ1Jt3IqZ2o87uKq9cVcuyu7Zyuip3sdVf8VzBYR5H6DGDsxyFsrz4oPBSkXB3qhLuquN2MmVSn6h4MTF51E7E25yqeGVJ4XidiNecqnhNddxOxGtPVby+Om4n4p0Nn64p3k1d3T0Lua326LAWNA2ys6ArORH2bBB2I6OLa0sd' \
			b'K3BrnX7xe2O8nRxW4a5KLOI/jsHd9cXvqpNyIvzZYO5Ehd9VJ+VE+JuHiCchfCz3n5IT4W8ePZ6G8JvqpJyse28eW56G8G11Uk6Ev3nkeVKzqbBbOT0nRWEy0z0qE7UKocEVyoQLRMRJUkCUoGZTg0lUlGYcn7UTqyxIquUzfR0sq1jSnZY7vhEmi8WKwjAE' \
			b'6Ivx1RrYgLB5EDaIi+nXij8DkqkCFRjH8Pp9r1q+KxP0Rd1y7FBN/sWSpJ7FhhIwRaxm/0E67diP3LQ1r1OQLH+4+H/g5Mmh'

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

	def expr_lambda_1   (self, expr_commas, COLON, expr_cond):                  return _expr_lambda (expr_commas, expr_cond)
	def expr_lambda_2   (self, expr_cond):                                      return expr_cond

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

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
# 	p = Parser ()
# 	a = p.parse ('lambda x, y:')
# 	print (a)
