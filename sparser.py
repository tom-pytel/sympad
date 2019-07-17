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
			b'eJztXfuP3DaS/mcOyAygBiQ+Jf/mOE7WOD+ythPcYRAYjuNdBBcnOcfZvcNh//err6okUg/29Gs83TON4bQoikUVi/XxWRQvrr549OLpi+dfVF/82/tff6LLsyfPv3tF1yfPX39Dl6dPntHvq+/4968vXyPoBR58/d3zR7h5/DXCvnz4kn6/ffjy8fOnIP7m' \
			b'+YuXj988+u7l0/9E3JcPH+ml0asB0eNv3jx6+OrxK/U/e/hafV8m7/fJ+614OVW85UtK59/hefX6JTP5Jf0+Z1a/Z3445ss+5sAhPC+ffPMXJPb4r4j34tmzh3R9+Oxb+v3qy6evnj589Rc8ff6VcgXfl8n7ffIqV4+fvnqsIX2ekNBrYYRei0hPvmbJ8ku/' \
			b'fcpy/urJ90++AuWjr1685rw81MxAVA9fc9Ye/8ejp30yCP725ZNn/IrXL+jn3duP7z+9+e3jm59+/OWPT28/UtD7//n945sPbz+9effbL/ntx9/+Obn9o79/9/aP93/88W58+/v4tr/748/f3w+v+dufv7578/bj39PDH8n7j8THr39+6L2f3n8c/D9+fPvu' \
			b'v95/Gt7w58df/jdjbvTm4V1E0/t/p2z/2t+8/XGI8/bTp8Tb23dDQr+nvIPlxO7AUcbzLz8PoT//OiTx4c9f3vz8YRDKTz//I3n/9rchv+//nhOQZ2Dtp59Squ//e8jib78O4Xnohw9v9WYUNuT0l7cffvzp7Rc/VFcXK9dUrrmsxGPgsdXK42pMddFVTV1R' \
			b'iK3Jc9mHSlgKWBkLX8v/zler7jLdm3RLHhA08uOVviF6frFp8UKk1+CFpr3sQyUsBayMpOSJl0C8+MppYvRyEzgXHj+hsu5Sb+mOfZHzaCmb9nIUIHehp6PnsQ+CFzLif2t6UsTh12q48FCtnAbyPRKMlbMsR8pfw3mJS89WzTRU71f8ekOcjsgpgMQBX4Ng' \
			b'lmJj5McRVSP0WZDJA+Eln+dXWEohXMr9iiVlavnxwhX5qLDYR3JoiDuWtr8cglx+23j1IAzvo3KEIPXtfIdytRUKNAuOszszCmlndy4PWTWsGyjfplXfheGbS5YrKymR9PcrESBlwOq7hocaONysJFOswFXdFw8UmK8kSFdRjrmMQuUd547eoFBZjsDI85vF' \
			b'M5Noq0YUIyhyGoirrUjbMwDRwyE8hbQSElJIJyFxCEGJI2RIhxSO1b6Wn4QhVysSSIn5BzJUTEKvyQtf2z+81Fu66x9wUMf/LuVRA9osAD7k3soPlcvlZfLCV0uBi9qismpYbSESUUrLNVvTVzRSPyFUwvIAw4VgB8RB7eUtnfysNDfwGskmwY31XrNJwONc' \
			b'UiFc+KxYbdPrB6TVF2oc9JaUzzWD4uqtGQeY9BpXealGSRNs73Hqocz3vobB3XA9R7Ww6jCgKVKid4RLahuu6iqQo1tiOoBPyjxxTzVVyxUZ1e0d5IdUfOVDFau26qrYVW1dtU3Vuqr10ASoI2WXHpuqtZWPlW8r31XBVMFWwVXBVx25gBqKCp+K23XUPlDN' \
			b'Q3mquqbqSIY1NVRojqiMKKtVqFpKsK3arurokUF9SbAmJBEuKDuBXKxCWwViqa5ig3qbNJZKlFSFwNzUSI7uarRlxGugC5HWuMYfqgt61SU1kYGvFySIhsSCkuVgkgqCSTJ8sfLUykOSEEJJSgilyHJvOgmWFG2jT4kxur/Xwr668CJPL/KM/NuqgERsUS5t' \
			b'raEtl8TJZvmibSQ/XnXGiVaIHGzolUNFwTpyMllTHHhh3rP6d7bq3B3T2wvfaS1hpJawcnFSHTDpJa5SuEEKt9NLEFonOu9YWN6ivT+mPF6hs3euoJzU4a5LpSQafVxsemlcfJOxGauOygKDufrYuBV8dMxtzidX+/LQ9RW+axRMCq5G4SMVpFQ1QbAEFpiG' \
			b'kXZflPRCK5S2vfd4vWilt9BpL86xLh0qcadttrMHTVW7lg2nTiMBGqTRWAHjOiqw+v6UXaN6HBjTkfIXq9hWkXoPvoqmivbeyIKE0J6FcBG6sxAuYn3vhXARpQ9gpZ/dOO0R9D0DCW61/mBSDg99fzwOg3pzf/oFPFthZJriXmWb8kn5vfv5NK0Ub8cXe6+U' \
			b'G9Nn5lJmkOh6tzJHlT5n6s5kp71b2YmMuJPPRlvfgWxgQpgrAiuNHWUBmTqtLPR1GcN+OiHipZqfTI5rV0imGm+Cqc4Nc5xG5jiNzHEa9Kk6kbYLwrljznXK0OokhLZEw1RE1iTJtMSdbJh8PwvO8jsq1hopQ9dqoXE1dnxTz5jNFDw0x8kgwU/Q2LXHVsbE' \
			b'WndTNQImknXe1sgMrZGJWdGm+9T9vMLMs7nns61XmHc3Mu9+32VxIe1hq1Vr290vNDjWgEPqVbaegwl3VjMvwm2k8m3UvKI30TA6/SNLAEbXi0IUoqgmBkIbnfajoswVRX1T1JVc6XIFGVnHvqKTMiY9tzKrggtK+FIG41YG41YG4/ZSRqlWR6l21oeLEjY1' \
			b'cFgIxa2VW6t9XXtq5gFX6JrbE+uac5/c3rX5BYwejPbtrfTtrfTt6TLtTviFQCeqa9Tgwbu+929lrdzKWjQuneKvY0gdlxQE3k6wFAVaIYgszotQqH65IEU+Ui+1UrhOHjVehNbI8M9wx/B+LVtyg2OkwblHTT4AYrVdNdKgYorvXgHkCt2Ge1XmUgcEqQNi' \
			b'PfR8nPR83D0fBHAXx51ex4wYdbPeKTHtpG/gpG/gdN7P6YSfO8apGfQzuIGScojCbZBi4bGANGxO2jInrRa3ZZ1WaNIfGEYEZtBybCM4W20z0r32Hr1oiBcN8fenLuSO8T3KLwDvGVdecOUVV/5S+wKCK69YCZe6RKtVSRBFCaIodCH4SHUSxH4zKGG81FGz' \
			b'EsaTX6G6QsajZDyymGSCQqYriN84XfOBPJiAsilya4W8VYr2bgiluwvZcHcgG9CpTjcy1LqToWYE1tUVjWuomhM+pFIDZ0PSzAFsVms1W8Vet5BqQ7AiQmk5Y4ZZz/IsnQipNElYyEmHPGAw0Y+/UYHakRRITDDEx44+yhvYAT9gCByBJUwTYo4QE4KYDcRE' \
			b'ISYJsS0Le7KwIQu7sdCkQ1jYgwOrc4geJr4wzMXuDNjWw7AeVutY3MPCHvYtYRMIBAUrRRjpYe4Q84qYUsRsI6Ya0RGEXTbskrH/A5s/OugNdvF6bOTFlsHAOz2xZRK7A7E3kESBTY+U7VXrdbMrNq1imzZvhsSOQCrIVcDG66BE2HVteMsobw3WYBLWCvuz' \
			b'sf0VO/4idiDyvkmkgbg1trti53DNP1E2+bbYEUvJ+VZf6Pr3YFsqBXpssqzph7SWN4Ni1yXvTqZ/bGSGjq0CAm0lGz9r2WxL4uM9uPSLXNa8m5tlgV2v2NRJCrIioa86ZAB+ikbRsfURO2BJSVak7yuS/SrqW7FjGyKlinTVdsoJtqGCGwqKQoYt0Nh8TKBZ' \
			b'BUgMydEbg/uh+j/zYIUtfy1drfkXeoVT/d9E+yeqv5veLyr9Lup+QFWfqfl1Kg5pLun41vq9oNsH1eu1Or2DLh9Sj8c6vFZ/M8010NxCbR1nKrtkpAH1dbPKu296FtuvkU4PbV89av5GrVWjc0ajmp6bTmlSR9rf9LV+SEhYp/mUX2zYLSEA+3VnKAAygqAB' \
			b'e7+w8auIinbSCFAcDBuLDQGFY/sq9n6iBR5Qg60e9AwWNyMEcQYhtQJWAIRFuETe6B55+DGFjqAHvxmAGtmcLo810gZ4yuNPHGDWACuU8+CUx84x2phvARwzWDPDsh9+DL1RigMMrSQ5Qx1nyhbBx68d4a8XRxx8CYu4JcVHp70bwJgxM29VoFv0sOPPCeCL' \
			b'IArRRDTCamwerFiFPF0jIGsFsprvazEbbgOqa3pkJXguQdMqPG8KmtvC8looRv7MRse/GRQbRWIsILGZ98sQJA9yAEYBYExuIwCWHQMwzpu65poe3CiNHHJjvKU4JbTFGdokfhgoc7RpWqndy5hYhlpMABuijhtDAhY20hu0iVAKR9fwL57FOAPtWIGGhwy0' \
			b'cZvHt5Yvy0BbaOk6Blo3BlonQOuS2whoXdEx0LoFoHXXAC1PYw3QhjgloM26lRo/xMGXAU0JMqAlJpaB1iWgDVE3BJo/A+1YgYZFCwugcSctAY1v5dki0PjBGGgIkgcZ0HDbcOjgNgFaHn/iADTtUY6AxhytAdoojTLQUpwC0PjRCGgaP8TBl4DWp5WAljGx' \
			b'CDROQICWom4ItLAd0I5muIf1kR1GfOsAWBrxuVsc9V0LRo8yWfFuiREYvYDRl8Dok5uh0jMq/RiVXlCZ022CSl90jEo/QaUO9JgrYR+bDjzjU8lmKM3TXIPSIU5hpMePRJATsApZiIMvA6tKUMkVr4mdZbz6hNfE1WZ4jWe8njReI3/Cr+PfHK8yHDSl4aDQ' \
			b'KfUUrzwunMzYGxkXjug2wWvZMV6n48IerzI25Pn7Vu7qnmyG1zzNNXgd4pTwqo3rbLioZGFIIMerSlDJFa+JnWW8phFjxtVmeG3PeD1pvLb8wVm20xjhtRW8tiW8tsnN8NoyXtsxXlvBa063CV7bomO8tgW8toLXVvAq/V8lm+E1T3MNXoc4Jby2gtd2hlch' \
			b'C3HwZXhV7pRc8ZrYWcZrWuXIuNoMr93B8Wo7XZe/HdSGMnDj3caule92d/ybYdfKQNWWBqpCp9QT7FoesVoZsUIdKZd8kWSbCfUGCM7jTxwQbNO4Fe9R/FoZuVoZvPJdrUTdAoTzRLu1KE7vLqCYH4lIxyhWshAHX0JxL0slFxSnVy2j2KZRbcbVAoojgZiN' \
			b'VOZobopmKPuA2x5xe+xGTfI2y/2fG+r1xArmIJB3JcsBPBHjAf5g+3xNlCMsVgcuuWl10EnCcgBA1ppbMS0YkW5SF/D370dkib7Vy0JzzpxJFlAdOKkOlI1pXdAniFJkiq2NFDTlUg3hpIZwsxpCyEIcfMsGDJxAy1rA9YRjUwalKdQVLtUVg8CmdQW+ed7i' \
			b'FxUFLt7KxfEFFhCm5VqjOUwn4JjriTveb4fIBe1h3PYHAXsogT1zM7AbDtWUM7AHAXtOugnYQ9Ex1kMB62J0hAuwHgTrEj7Dep7mmkZ/iFOCdBBIhxmkhSzEwZc1+sqrkmujn9hZBnJIQE5cbdZ1b8x5rH3SmI2wfwZmx3NjfQNdmhsTOqWe9td5bsyO58as' \
			b'zI2N6DYBbNkxYAtzY1bmxqzMjVmZG1OyGWDzNNcAdohTAqzMjdnZ3JiShSGBHLAqQSVXwCZ2lgGb5sYyrjYE7JZ2S8cM2DXD7DuN2Y5PopLfHLNidWFLVhdCp9RTzLL5hR2bX1gxvxjRbYLZrugYs8n8gt+niBUDDD6KSB4AsQPdDLR5omtAO8QpgbYT0M7M' \
			b'MpQsxMGXgVYJlFxBm9hZBm2yzMi42nJovaUt1Bm8RwdePs0P4MVvBl6+tXxZBK/QKfUEvI6thN3YStiJlfCIbgPw5vEnDuDli4CX3yfgdWIjjIuTB77O6KbgHSVaBm+KUwAvPxJJjsGrZCEOvgTeXoRKLuDN2FkEL6ch4M242hK8W9pXncF7fOA1kDfAa8bg' \
			b'NQJeUwKvSW4GXsPgNWPwGgFvTrcJeE3RMXhNAm/qKzNPwryTB77O6GbgzRNdA94hTgm8RsBrZuAVshAHXwZeFaGSK3gTO8vgTdb9GVdbgvfwNlvnNarbQrHlk1s7/s1RLGtUrrRGJXRKPUUxr1E5WaPCBWVpBcuyRjWi3gTLtugYy2mNit+qWJY1KidrVE7W' \
			b'qBLdDMuTdNfAeYhTgrOsUbnZGpWShTj4MjirLJVc4ZzYWYZzWqPKuNoSzoc36TrD+bbg7OVEa/7N4SzmmK5kjil0Sj2FM5tjOjHH5DZZokmpMpxz6k3g7IuO4ZyMMvmtCmcxyXRikunEJDPRzeDMwSilnt0ynodESngWy0w3s8xUshAHX4ZnFaaSK54HmgKe' \
			b'k2VmxtWWeD68ydcZz7eFZ/7cBvA8XkZysozkSstILnMzPPMakpM1JFykLBnPspI0ot4Ez6HoGM9pJYnfqniWdSQn60hO1pES3QzPk3TXwHmIU4KzrCa52WqSkoU4+DI4K8dKrnBO7CzDOa0mZVxtCeezRdjdgXPk0+LlzPgczrLC5EorTEKn1FM48wqTkxUm' \
			b'VkMvF0m2mVBvAueyYzindSZ+q8JZVpmcrDI5WWVKdDM4T9JdA+chTgnOstbkZmtNShaGBHI4qyyVXOGc2FmGc1pryrjaDs6mPsP5zsC5hYAB57FxthPjbFcyzhY6pZ7CmY2znRhnOzHwdGLg6cREe0S9CZzbomM4JxNtlww8nRhoOzHQ1g2KiW4G50m6a+A8' \
			b'xCnBWcy03cxMW8lCHHwZnJVHJVc4J3aW4ZzMtDOutoTzgUy1sg+wfSZEy4fBz7hewDXlGageg1owXYJ0q39TODOaWwgNeBY4C5oFzAPdBkBuZ3/Ab4KvoLchBWt4L1GoBMSCYYGw0k3xmyVZhq5GKOBWYDtDLZOEqNeEWJSWIDYBtudgEa0JrD0fWyL1QNZZ' \
			b'9nTa3vZuwxTlw4NjMx4cGxkcm9LgmF4ipGbBxlLoNOWaL87LRVJuQqI2m42PTSg63iSVxscmjY+NjI+NjI+NjI8T3WyX1Djdbu0MdkqmtFdKhshmNkRWshAHX7ZXSplWct0rNbyqsFcqDZEzrraE9uHtuI4a13cZ1JAoLyv78bKyl2VlX1pWFjqlnoDa87Ky' \
			b'l2VlXCiXfJFkmwn1BojO408cEO3T4rJPi8teFpe9LC57WVxOdFNET9MtwznFKcDZy/qyn60vK1mIgy/BuZelkgucM3YW4ezT+nLG1ZZwvt6yS45qUUTbM6iPHNQoq5pb6nrcUtcM6iigjm6C66h7mZkaR5bUM2gjKEji8g401rU01rU01nVyGzXWddFxY12n' \
			b'xrpOjXUtjXUtjXUtjfVAN2usJ+muaamHOKWWupaWup611EIW4uDLWmoJ8UquLXViZ7mlrlNLnbjaEtqHt/s6g/q2WmoHcaKlHm9o5FsWdaGldsnNWmrezOhlMyMuaKmdtNSypXFEvUlL7YqOW+q0o5Hfqi217Gf0sp/Ry37GRDdrqSfprmmphzilllo2L/rZ' \
			b'5kUlC3HwZS21ylLJtaVO7Cy31GnLYsbVlnA+W4IV4SyzMCcI61DJPmU/HlV7GVX70qjaZ24Gax5SexlSexlSexlSexlSj6g3gXUoOoZ1GlL7NKT2MqT2MqT2MqROdDNYT9JdA+shTmcHESyAW0bVfjaqVpIQB18Gbk1OyRXciallcKdRdcbbluCO1HHb+gCN' \
			b'3Y4QaG7vFAFT7X9oBr7hiw3j9AwfPh2dLIAvlzYTjJVOF9jpBI0J1vY4YQCCPIZTBiDofU/MgI4MdV4cnTzQ13vlEwjaseZvovfzg2P2OTWmPpT2txsgYFPtt2vO0miqNedpHOosjcJZMTdxTgwkdkiNR1t9oLM1IPDC+RqQ/5ozNkz7AOWQa3q3vaYf6nyk' \
			b'xRre3+5RMc0ux8Xc4FExBz8Gae13vUdb0D73kTEQ9D7HxhCP+6ryAfV490O+CqpMkmqwi5206zAnIIVbVOvPdwLSHqd6FdRaPhzVcHu4/6lIaDmvUfEYHvAX8TNVb45J1W+rvo6HU25/krp9K1U1JhhKJ3xde0odaTLqr0yTzalr8iE72PtoMtTmZGvpHTT5' \
			b'0GcubqnJ7gGqjlyT7ZFpMp+YGio57ey2+tOYMKE4oT2iPvVnVWuZy4Xi3Va/mk/KYQ7M7n1rd2zK3eixwP4zKHnYUNEhhnBWeFTOhhcvVhjS3Zzi6/L29XU7sojnbj8Q+IOCwB8EB+5mMLC4MqUrUmtxYE6l0t/M5HofHBA1ZuoOjIE4s7BmDMSwFgfoRzIW' \
			b'9sVAOCgGwkEwkOl/3d5sZ+da/T/rPn/SI+l9I5FuquNzjd4fROfjQXU+Hlznb3gC5qzz2+t8c+o6v8MK6BqdX2O4s5vOs8HRWeePSufNqev8/muhd2BWvTQPeTRK/VknISGbzzJDs53SsvFWnU8/uqNa/cTb6zRLc2OKnNlKbjo7cz8Vu+G3tDwzc0O1NE6x' \
			b'33ZGZsea2u2w/tnup+/12Hz4YFV2yfD/wMtHbJlo2BLuZjUdNtT+0LqOFKenGhx8QalgkH/YBaUGWSFdxGVRy033AJVFruw7LJGelf3zKDu7Qyt7uDvKHkTZw+bKbqurm+q8bNXtvolu9lR9t1nmR9HeVq9jj670wbvOU81b3v6wpG7QLlddHYluHY1emZPU' \
			b'qSPRJ380+nRbdZXjLg1q+oJ+2VvVr2B3US9QHVLDWAhrFQzbhFbolBRaytg8WPFuPxr4+8gtZaiujkLzjqUmy9QM4j/XYhvVYjSuxoY/xyoVzyo1rrz8ybWM2PPsb1+n6gcrFGj7YIWGibr5fK4t5eCsYCMFC6enYAHuWBWsIwWLlYFsMXlh0UvztXyAptlO' \
			b'qUiXJmoD9bhOHVgFFosfTdRQptzc716Ems6kOUEZXCNzlvOSjFlQzSCoLQFIspqj7IDiYrb303rR9KVWeG+xmV5su827xXrTubaw5xzadVVUnAs+wh2g1mn7IthuRgtS3mOuan3VwrdhmIdCBUJcXXGpkBQgc/DOZew0XEqCn4+UC6Jsfrik4IuVfhLY8OHR' \
			b'JFzZDMhTmKFDwvjeQcubXfG1gH5XH09ntnjbylyTAjWU4z+msomKj+92dvTtFPlGSqg5wezDJmLs2S+l9Z8csfknRXDQaoU/Kj2rWwvi+H+YCPayKQb7ghEX31fgOFbW32qxmuBn8r0E5t1dk2OCz/iPqfxN5piKe/s/ZitswpZ8rGYnzqgJXvzDLHzpGf8x' \
			b'd/GGuYvVTn/MW390TdyIPeoWTDnE9vaNuKSaFT3GrvCHGZXsjrA/i8MMd9syLJ8m2pltdJ+3cn1fdwsizlhT75Yz+ejSbvmTr3WkLxMhv6bayfU9+23cpHvOUug/797cuiDQyGOkI57P5UQK5mik4KrbcCIFu6cUqNmbCcLuIwxf7eUw7J2Gus0TEKG4JBR/' \
			b'QLmY62UDXtfLJ1TiECscxq1JqvBIxOSPWEyYmbh1J2IKUzFlXwwUeVk5oHorqXE3AR/7M+kzf5NP+42/3wfRoqa9RqyYkV8rWowJb9U1GLHgM6/b0UlhxOPVWUwV3r4TMbXX6uy28spVtSy7vZXTVbmLrf6KZweHiQmhx5TEchTK9eKDwktFwt2pSrirjtvJ' \
			b'ZEN9ouLFRNtROxFvc6rilQnz43UiXnOq4jXVcTsRrz1V8frquJ2IdzZ82lO813V1Dyzktjqgw+LGNMjOgnZyIuzZIOxWRhd7Sx0rSmudfKr82mhbOawq7Uos0j+Osd3+0nfVSTkR/mwsd6LC76qTciL860eIJyF8rF6fkhPhXz94PA3hN9VJOVmRvn5oeRrC' \
			b't9VJORH+9QPPk5pMhf3F6TkpCpPZpVGZqL0GPhnptUBEnCQFRAlqBTSY+EQtUnyHj42MYCzS8lnFDoZCLOlOk6VurrO8VixVID7apAEKy4gAFAUHwg5L+aSWKlcFKjCO4eTLSvylmRpf+ZLY3XJsX03+xcKjnsWGEjBFqGb/QRZgsdW3iWw101JX5ofL/wcR' \
			b'g3ug'

	_PARSER_TOP             = 'expr_lambda'
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

	def expr_lambda_1   (self, expr_commas, COLON, expr):                       return _expr_lambda (expr_commas, expr)
	def expr_lambda_2   (self, expr_commas):                                    return expr_commas

	def expr_commas_1   (self, expr_comma, COMMA):                              return expr_comma if expr_comma.is_comma else AST (',', (expr_comma,))
	def expr_commas_2   (self, expr_comma):                                     return expr_comma
	def expr_commas_3   (self):                                                 return AST (',', ())
	def expr_comma_1    (self, expr_comma, COMMA, expr):                        return AST.flatcat (',', expr_comma, expr)
	def expr_comma_2    (self, expr):                                           return expr

	def expr            (self, expr_eq):                                        return expr_eq

	def expr_eq_1       (self, expr_cond1, EQ, expr_cond2):                     return AST ('=', '=', expr_cond1, expr_cond2)
	def expr_eq_2       (self, expr_cond):                                      return expr_cond

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

	def expr_paren_1    (self, LEFT, PARENL, expr_lambda, RIGHT, PARENR):       return AST ('(', expr_lambda)
	def expr_paren_2    (self, PARENL, expr_lambda, PARENR):                    return AST ('(', expr_lambda)
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

	def expr_curly_1    (self, CURLYL, expr_lambda, CURLYR):                    return _expr_curly (expr_lambda)
	def expr_curly_2    (self, expr_bracket):                                   return expr_bracket

	def expr_bracket_1  (self, LEFT, BRACKL, expr_lambda, RIGHT, BRACKR):       return AST ('[', expr_lambda.commas if expr_lambda.is_comma else (expr_lambda,))
	def expr_bracket_2  (self, BRACKL, expr_lambda, BRACKR):                    return AST ('[', expr_lambda.commas if expr_lambda.is_comma else (expr_lambda,))
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
