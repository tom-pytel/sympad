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

def _expr_mul_imp (expr_mul_imp, expr_int, var_funcs = {}):
	last      = expr_mul_imp.muls [-1] if expr_mul_imp.is_mul else expr_mul_imp
	arg, wrap = _expr_func_reorder (expr_int, strip_paren = 0)
	ast       = None

	if last.is_attr: # {x.y} * () -> x.y(), x.{y.z} -> {x.y}.z
		if last.args is None:
			if arg.is_paren:
				ast = wrap (AST ('.', last.obj, last.attr, _ast_func_tuple_args (arg)))
			elif expr_int.is_attr:
				ast = AST ('.', _expr_mul_imp (last, expr_int.obj), expr_int.attr)

	elif last.is_pow: # {x^y.z} * () -> x^{y.z()}
		if last.exp.is_attr and last.exp.args is None:
			if arg.is_paren:
				ast = AST ('^', last.base, wrap (AST ('.', last.exp.obj, last.exp.attr, _ast_func_tuple_args (arg))))
			elif expr_int.is_attr:
				ast = AST ('^', last.base, ('.', _expr_mul_imp (last.exp, expr_int.obj), expr_int.attr))

	elif last.is_var:
		if last.var in var_funcs:
			if arg.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg)))

	if ast:
		return AST ('*', expr_mul_imp.muls [:-1] + (ast,)) if expr_mul_imp.is_mul else ast

	return AST.flatcat ('*', expr_mul_imp, expr_int)

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
			b'eJztXWuP3LaS/TMLZAZQA03xJfmb4zi5xtpOru0EuxgEhuP4XgSb19rO3V0E+e9bpw4lUq+e7pmecfdMYzgtimJRxWIdPovU2cVn//bu1x8/qz579uT5ty/l+uT5q6/k8vTJM/l9+a3+/v3FKwR9jQdffvv8EW4ef4mwzx++kN9vHr54/PwpiL96/vWLx68f' \
			b'ffvi6X8i7ouHj9LFpGsNosdfvX708OXjl8n/7OGr5Ps8e7/L3m/o1VTxls8lnX+H5+WrF8rk5/L7XFn9Tvl59PWzZw87ihcdRc8pPC+efPU3JPrw2Tfy+8XnT18+ffjyb+J9/PyLxBB8n2fvd9mbGHr89OVjXP6egrs8IbVXZEReh5hPvlTJasxvnqqcv3jy' \
			b'3ZMvQP7oi69faV4epsxAVA9fadYe/8ejp10yCP7mxZNn+opXX8vP2zfv3318/dv71z/+8POHj2/eS9C7//39/etf3nx8/fa3n8vb97/9z+j2Q3f/9s2Hdx8+vB3e/j687e4+/PH7u/41//jj17ev37z/Z374g3j/lfn49Y9fOu/Hd+97/w/v37z9r3cf+zf8' \
			b'8f7n/yuYG7y5f5fQdP7fJdu/djdvfujjvPn4MfP25m2f0O8572A5s9tzVPD880996E+/9kn88sfPr3/6pRfKjz/9K3v/8Y8+v+/+WRKIp2ftxx9zqu/+u8/ib7/24X1ofvjLL28GNx8++766OFu5deXW5xU9Bh5brRyutanOmqqtJMCuq/a8C9OQ/nZV1/BF' \
			b'/XeuWjXn+d7kW/GAYM0fl+jXQq8vrSNehvQM3laTDKEMywGrmim56sx4YcVVNiUmL6+95sDhx1e2Pk+3cqe+oPmzkqQ9HwTwznd08jx0QfAief2vQ0eKOLiaFH7Om1WdAvUeCYbK1SrEWCG/vqrj3LOVH4em+xVfL5yC3HTk4ES8eBmCVYrG8McJlWHmiyBT' \
			b'BsKLUtdX2KZ7vYMHMVr++PV5upXC0tdakbtwp9J2532QLW+NSx6EgVzKEYJMb9c7lKuVch0Eh8mdGYTEyZ0tQ1ZGdQPlZ2LynRm9OVe5qpIKSXe/ogAlA3V6V/8wBfY3K2bKiMSEbatlKQrorWZD3k0tnH+u6HJbRTPDWCvD4vcJHwZCiZW1JUzkYR+eQyJD' \
			b'XA5pGOJzSMuQ0IWIWqncWv4USGmTvouu6I+ChGxCfcQLX+wenqdbueseaFCj/y50WUz3Md+vNCVT80dEf36eveJrWaRUzFZ94L2tqGt1DUkpJlREqXKAIhA+RYBR8dseUtBrgrrhzyrJE17DHAqeVLGTWARZmkGR/5krClRlokUJlUrFGXq9FOVy614x060Z' \
			b'Bpj8Flt5VpOiA3Xnsckjee98huDVemxd+QQMQE+FBHn4c6n3L+BBZSYMgmepRMGxFDISbiE4yZkXvQxVrNAKxFjFpopt1dRVI5GFQjIZUHM166qRyLHyTeXbKqyrYKpQV0GaCXEOpS0F7KSYUaFIVoSzqmmrFm2PtDooLVRRla9C1fiqkV9JtkE1KGgV4KD2' \
			b'8tD94KogscQTq9BUoYUeinhEPQzqnaptJTVJbo1U5S1OLvJgjav/vjqTR+fS7knuIVCRgF4khojlTOSAW8s4IhC9a/Wh0PC+bhm85sWkp8KH3N9PqV6cecrTU55Rf5skGcorMjB2oY3K61hzfBaZq6bTlaQ5FIMNnVIkSaiuHEnOGsMsefLuVetbU7X13VLa' \
			b'M98yo4FIDoaXmnWBkp7jWjNcS/qsTRdHWkeFdyoracT9QWXxAv2ye1wrOdbYrs2lQ0U+KC49Fc2bgktftaFqY9U2B8YrwdCoRAsutZ5nPtCR0crPmQSgBKhUr7CmbFhTBt6ZOtFo6D3Rz7NAgTTh/mL0rEktZJOUQ/VrT2k7nxK1+0w01fxGE5dBltFxmYwd' \
			b'ZDAlnf/7UnAmaW9QOURXRV9FyaT0EmwV11U090UUIoNwkkGIJxmE5r7L4Cyk0TG7yYbNe9umngB7BE1Xha5TLFCzz+374XnNcXl9b7oDOuEg2b3z2awbFm6rF8xJ3ZsyxixRfc75ErneqbxdnEXN013JTXOnchO1cI4+F83x5wIzn1oHWDZykgPk6ahysE61' \
			b'mCrVaBrAs3ofzQF3cwE6R3ADLLV1P5lXczKv5mRejY5Fqx0JzNYp3075TpNjNg+9UxukA/C73hL5NHPttTN2SJyZVFhNKiztJxzc3Cqm7QgCc5D8CeY4xdaGAytg4SzeVC3QdNOTNWcia05AUpHuUUfzAhOs9X2dVbzAvHLNeeV7K4Qzdi+a1OY18V6pv9OS' \
			b'36M6FcsUmFBW7fIUrWFfxyT7AJOMCVKPxHDyo07LICERRSYZWUnHbgEkckokptgxLUoGdmfYbwlNqtdsN0sCUxAU7DmH15bDa8vhtT3nwNOmgaed9M4iw8Yr9DOhuLW8takPa49sgfsCPW57XD1u7WrbOzZhgEFBnfrsln12yz67XMY9BjsT6KiLdZo99K7r' \
			b'1Vsu+lququLSJtS1CqSDEgIx7YgjT1gF3p7WVlDlajFSPIEXlrvjI5NkZijIWpXqXq3FaRtTs425P2080GFTS1qzCcWE3X1CxwX6CfepxIn/QPyH3OFx7PC4e7B6Ijy7o+txCZ9u0usUnh2bfcdm36WpOpfm6NwBTqugB6GND0vBk9nAW+3bs9FybKccWyRt' \
			b'p9pUXbHZ6nv4616LYbydzIgLLe5Hr1RnjmGp1DarNSuA41ZuQNinDqGnZnhqhr83dZx2de9PdgFzr3DyhJNPcPLnqYEnnHyCSOBAd2CXjwxSWwK1RS4CG9YlgUaGuAh5TNoVj30R6QLZjcxuVBlxkoFTDsJuHK3LQAgaXzJJYTWkbhJBcydE0t6BXNTHnwso' \
			b'VJts6tfJqH6tYF1X2Hsk1VtiQ6oyGAZ36eL1MY3eMJKzgwoQ4oioFSUz4HiYVfYVWEmC+wi+MR5wOnhuIb4y21iFWOP1EIvwACbABdgAH7BwBDOY18MkHjYLSTNssA8Im4CwAwjNNTZ5oE6C4TOkDAtRbAiA9TlMz2HYDbtpbI6BQGAph9Yfc3uY98NMILaT' \
			b'wCQatsBYysQ2g9aJwLjlNXDDJTYJttyo6LGDrloJ3aqxFfe4YpctHummOOwuk5JZBWw/w7ZO8YsmrLCtDPs/hV5ksMJWUafbDCWo5W41bDtsNRFs4MXDtf5ge6D8i2quGuxkbdJ7sJsPGxgdtpHKfStX0buV7nDDc6S51k1zFTcLYtedpCJlpVuD5VcuEU8k' \
			b'xONlSE6SENmtpB5btdggKzHlTdgbiy1tAf/gWh4FkIIL7CNEziA0cCBX7EnW/bCVbpET1V4FMClvCJBD/T06Z1DLOKuOYaKRrlhRKLWzx2uvowWwZtFZqiyRXcJ6gMI2DW3zbFCbqgRWFaVmE/TY6uCylm/SbGS53qDhfkbLJRyG1art8hw7YQZavy403xfa' \
			b'j6vEgaHgAAWWSMDABluQsD8Mu6s6VGDLAXYYwJJggBDAdw2JLeABGjgLCcxsr7UjFSfwAFHQ3wIkuoFUQ3u3BWbK6ANS5BC7RRtyr/xJzgAn5ZmIUuaUTQPcj7A1SLDHmZQZUpxAC5Fas4gwfesAZF0msy8DDreCOXRAMuoKZjL0AuGHB5Am9rX2OMwEBSCr' \
			b'P0P7APWLaI9c41/atVGEtqkVuwSi/taRWcLSbIfGOSSuExpvCom7oPBS5AXdjt7qb4E83AJ4YQF4+mCEt6B4GzZKul9aQ3u3Dd7CvFO8hWnTZTa3XoMkSoQN4ZXjLIErTMCVcpR9BbhSWgWyMhNTZIWMpz7aAE/GPUB9KDr2QCsCb+QagCt7wtXB4arBpiLg' \
			b'qhniqiGumiVcNVNcNYqrZoirhrhqstsGV828U1w1M7hqNuOqTGIDrvo4S7hqJrhKOcq+AlcprQJXmYkprnJ/MUfbElfuhKtDw5V0cWvtJuK3wBVuG93CN48rfTDEFYICCTOucGs0tHdb4KqMPiBt0mWEK+VmGVeDJJZxleMs4EofDXDV5Sj7Mq66tDKuCiYm' \
			b'uKpz/y9H2xJXfidcHchQLV5ptLYJb0ujNfOJRmyXYs+hMIA9N8SeI/bcEvYKNwGhUxC6IQg5mTGg2wKEbt4pCN0IhGmQphypjgGLerfuyMagLJPcAMo+zsIoTR9FvmuIzZTR7CuwmYRHug6emZ0pPF2GZ+ZoO3iGEzyPEp5Bj7Zr9beEJ4dy9dJQjnSJegxP' \
			b'HdPVwzFdzTHdgG4LeIZ5p/Acj+k6eHJchwvgGQjPlM8RPMskN8Czj7MEz0B4ToZ6XUazr4BnYpV0HTwzO1N45tFewdF28IwneB4lPCNPBdTfEp6c4sRlHp4xuwk8o8IzDuEZCc+Sbgt4xnmn8IwL8IyEZyQ8OcvZ5XMEzzLJDfDs4yzBMxKek7WELqPZV8Az' \
			b'EaSUEzwzO1N4xgzPzNF28Gz2Dk81IuDy322D1C3j1N9dqGKhVAeZdjjItBxk2qVBJukS9QiqVkeblqNNqKDzvDBZE4bUlwO2jD4gbdKFgMU7ElwtR524OB7+KVIkUTttUMs0241tan71Amj1UeQbB6DtMpt9GbSdGEmXQJtfNQWtzSPSgqMZ0Mb1Ay27GfC2' \
			b'AC+XtdNK4nVAXB9qM1sPWtpt1s1vGco4uLCHc9wMaV133wrWtlx+xx1X4PXA4Omio0aYhbnNbgzzhskF/S0aZcVyGJJugXE77xTjdr5RVqYYCyi3RDkDxhDv0jM8jrjA+GUr/F2CC4C3BLydAD7lPPsKwNveAEDpgxa1ot6qKUAimSIfRgGaWEJ/L6Yx+pFV' \
			b'AT0ugnlr/+LW0n002AeL9TvcpYasvSLYD9tpTwD7JQD77MYAFi9CAxMpAOwJ4JJ0CwAvOAWwXwCwJ4A9AewJ4JTVEYDLJDc00H2cJbxyvljfNcRrymj2FXhN8iNd10BndqYNtM8QzRxt16s25jTqPUqIBpg+AqLDSSnLSSm7NClFukQ97krrpJQdTkpZTkoN' \
			b'6LbAZ5h3is+FSSnLSSnLSSnLSakunyN8lkluwGcfZwmfnJSyk0mpLqPZV+AzsUq6Dp+ZnSk+86RUwdGW+NzNtudg8blhwHtnIdrolw50/8kAojRVsEumCqRL1GOIqs2CHdosWNosDOi2gGgz7xSi2WZBs5AASqsFXFzibl3QjTFaprkBo5l+AaMNMTqxZehy' \
			b'mn0FRhN/pOswmtmZYjSbMxQc7TbINbvZC52wejhY1U89Aav4LbCKWxGMW7KTJV2iHmHVqZ2sG9rJOtrJDugux2oZfUAqJebWPVZdbkwdrWRxcXzgS7oRVgdpLmO1oJ/Hqj6KfN0Aq11Osy9jtZMe6RJWC3YmWFV6YrXgaEes7maDdMLqAWHVQNArFfcAq4ZY' \
			b'XdrmQbpEPcaq7vrQFAqsGmK1pNsCq2beKVZNxqrJWDXEqiFWDbHa042xWqa5AauZfgGrhlg1E6ymnGZfgdUkPdJ1WM3sTLFqMlYzRztidf92Taeln9sGba0f7mv1twQtl37c0tIP6RL1GLS69OO49IMLSrAmdLn0M6DeArr1vFPo5qUfzUiCLpd+HJd+HJd+' \
			b'Mt0YuqNkN6A3J7GAXi79uMnST5fZ7CvQm8RIug69mZ0pevPST8HRjujdv9nTCb23jV6n3y9t9bdELy0U3ZKFoivcBL1qoehooYgLStARvbRTHFBvgV437xS92U5RM5LQSytFRytFRyvFTDdGr4aicNLzDfDNaSzAl8aKbmKs2OU2+wr4JjmSroNv/6oZ+GZj' \
			b'xYKjHeG7f7OoE3xvG75eP3vb6m8JX67nuKX1HNIl6jF8dTHHcTFHO8yMxrJU+JbUW8B3wSl885KOZiTBlws6jgs6jgs6mW4M31GyG9Cbk1hAL5d13GRZp8ts9hXoTWIkXYfezM4UvXlZp+BoR/SerKaOH72B3wTW3xK9XOpxS0s9pEvUY/TqUo/jUo+j1ZSj' \
			b'1ZTjgs+Aegv0hnmn6M0LPi5bTaWTERyXexyXezLdGL2jZDegNyexgF4u+rjJok+X2ewr0JsYJl2H3szOFL150afgaEf0tif0Hj16I7/grb8lemkM5ZbMk0mXqMfoVfNkR/NkVT3PC5M1YUi9BXrjvFP0ZiNlzUhCL02UHU2UHU2UM90YvaNkN6A3J7GAXhoq' \
			b'u4mhcpfZ7CvQmwhSygm9mZ0perOhcsHRbuit92MANTzp6MYBzHN0TzAewVjkABAPMUwILyE4pr8xehW8EQIDfIlegpfY7ekux20c/QGvGa5Eq8EX3HUzW6gIWmKWkE10I7wWKS5DtSOdxylhOkEpM9ZdM0JRSkRoBmjHwQSdGZwdDzsicz9GT/WRNK3h7sIS' \
			b'BaMj23o4sq05sq2XRrZR6RL12FKRdIGJNHpxjOmYsgmZut5qcFsvON0FlAe3dR7c1hzc1hzc1hzcZrrxNqBhsu3GpaEilYXNQBzf1pPxbZff7Cs2AyVhkq7bDNTHnNkMlMe3BUc7Inn/5lEHC+O7imGIUtdz/XA913M91y+t55IuUY8w7HU913M9FxfJlV6Y' \
			b'rAlD6ssBXEYfkErR+byq6/OqrueqrueqrueqbqYbAXic7DJ6iyTm0eu5sOsnC7tdZrMvo7cTI+kSegt2Juj1eWG34GhH9F5uMNUUAK5PGD5UDIP5FhjGb3ksU8suMu2nYj2CcSSSSY2XtxMkIygwHdUFIFkvTNyERJ042OKspnbe6VlNbY9kzQ6RrFxZvpUP' \
			b'/LqgGx/eNEp2w/lNOYl5JOujyDcOkNxlNvuKnjRDPOm6k5wyOxMkKz2RXHC0I5L3b051wvBtt8MWckQ7bIftsGU7bJfaYZvdpB222g5btsOW7bBlO2zZDpfUW7TDdt5pO2xzO2xzO2zZDlu2w5btcE83bodHyW5oh3MSC+2wZTtsJ+1wymz2Fe1wEiPpunY4' \
			b'szNth21uhzNHO6L3ZGA1i15OnBwZij0kCRQPR8SeI2K/NCImXaIeo1iHw57DYc/hsOdw2HM4PKDeAsULTlGch8M+D4c9h8Oew2HP4XCmG6N4lOwGFOckTJ/7GSxzROwnI+Iuy9lXYDklR7oOy5mpKZbziLjga0csh+rihs+Qv5ED5P0CzuoZfO16iHy3od1X' \
			b'y4fJY8v6YZwjf9NnyOuBZ1MV38M58t22cQhw+Tx5KeJCQ+cPlr+2jqIpaT/Jpw7w7ZWtNTXMaGunqWh441Bj9UzWphp/BmGqunosz6dRXyDZ2JtX480qDPFur8ZTVYYW9AdguIE6d+3uqGaOXqrg9i9+TGe3Ktjv6Use7BE1h1QdrxeqZCh5s6E63st3PWZO' \
			b'9tr3tz3SUV0mndW1B8U2C12QHetniHjhWx+Q+FL9LIpciyLX7i9+NvBafQm/10/S2E/yVRpMBV3hyzQ305sYnUh3k1+mMYNtu7f1dRqIdvcv1AhXN93n3VZJOdTcl57iBCGYnIc9doJvW2dv60tKdWrI96OzelKWYn+yl3XHXjHauU36i66DfSCJ6hcnTHVx' \
			b'CCM3032vbIejzPY1esPHTfyuFe6nV9qr9Hc5TQSzXtNNUNxCJasLAvrW9a4VbX0I6tl/YM/eoJbaLTRV/KJD90xjoSC1TmyusHy3f82t11tUsXgrRFZfRYvtfrTYXb+erfesxXOz0d0s9FIHtz3gejfepCYLddyfFsfJfgLVYgzDFju7ltp8NS12+9Fif30t' \
			b'LjU43FCPYYMG30ftLTXXqNH/3nsPGzT3Glrr96O1Yb9aG09ae/ta2xyP1ob9aO3y0veVtLY5ae3ta217PFobD2G0dvsTCIeklje63gup+FuYLNhB7ao/pZwfCDB0Nqu5XwrormmDIMoIqR+rLt7oxBWsoi6xO4DsFtWyX50VtToApRQ59tNY+1bP0vxsm+mr' \
			b'e1BfGn1lo1NXe9ZXE3ebstqpCZcsbK+s8Rr62gxtK69dlS4ZP+/TnCskPXU3oKswJLV71FYkNj7wfF8V64L98f4MukxDJUUmZivXunkg4NZPO++ygHVS2D0qrLo9Kqw7aoW1VFh3ucLW1cUh9E9vYWA0a1M+awvbHFXjvupNu290EDRj6LrQaNvq4jAU6hCU' \
			b'SeVzbIp0AErkDkWJPkWtZLTPgWp8QanMp1SqYK6gUyDap1qpCBa1CqbiK4kxr1/Vn6F9oLtcfS3XqA2hry4OQd0Ooc4qdAtSP9VXl9RX1Z/GPhAUqh6Fkx711ZQ9soYP+y3tJ1UkqZdQgv7BCgUXHqwaVap4UqpeqdyxKZWrlOeDU6qmusBRTgHnu5kqGu13' \
			b'tXqahWjVTpokpTfSFejEZTqg5T4pczRAfUGisK5ebimZUWsByV8i6WZOspCPZD3JZ1ewQUQTRO1LSvG6Gk6t3ru0TC+tq012NdvOcdlrzmFtqoVm5O3hrl+xNJ3kd5thqq81h7Rce6jXDeaHpDQutCxwys1aM+G1ZG0Kp/y9pXyyOmFlpfn+XILPVum8wVo/' \
			b'zRp92iZiAmoeg42qUfc3YUdc2u/hW7xkVW8grKvBn8a3Ob5+6dbVg4MXsCu2QTrlqQhqNdovGqXzCvJZBPiSYYW/FltsuDXAD/91n0vNXYOWkXUbrD43XGWCH5/qS9OgUdl1N8KupLDbn/LiL+clbssOTngYsOSruT/MTC880Tlk9Stz4SaZk7Hk7n/KVvo2' \
			b'BM9D3MwZDuscMYdzNrZisKl0tr+Z/cMERXEneJ3EUV6bnXjl8SNX5liINvx1/ciNsZTp9gpM88yUq7GeNjy33SZn1E+m2t11/eNd3Kiji+x335BHBfMpRYC6DYMFem7FMf/mMPJvq1t3zH99nfzjSOGxCNbXEYOrru4wVBwFYQS4bQIUh83icHuSSHno0ZJU' \
			b'vLlMMr6iQ7Pl9+A2pLPwiAJyhyqgWH1qRwH5sYCKw7woKcsvsm4vL23YZXCPReP+BK7hqVvDo7UwVEHf5BKBomu9UagYVX06Z3Dsg4wAdqRjMYQD1VPMpH1iRwHFS/V0J0kN1HNRatdWSFuVTgY6/KVnV4exPIkxip+P4hdSXngjZdscpWyb6oAdBdsepWDb' \
			b'6oAdZ0HWxyhYyynkA3UUrDlKwZrqgB0FWx+lYF11wI6CnQyBriPYy7quexZvrPblMNc/DrKToCs5inkykLr9ccL15d1Wmx3PA7402vYOyytXJabcD2B8dm25Yz3raBzFPhmPHaPYm+p4HMV++SjvCMTeVsfjKPbLB4CHL3aslR+No9gvHx4egdjr6ngcl8Qv' \
			b'Hzwez5QnLA6OzLEQTDa1ksw1RASOk0NpaFFQlkYNLWDtoqYuvR1LTBTS/aclDUTUwBwOBRAo5ob1m56MVGMVls2Mnjmj9+k5TvNACdRq04Fln6QqODChUAEpK41Rp3ONIs/cSLYZurt9JratRv+M3U5io/yVwlWTf5oPwfTlwkQ1E2lkZPn9+f8DZVc3jw=='

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

	def expr_eq_1       (self, expr_cond1, EQ, expr_cond2):                     return AST ('=', '=', expr_cond1, expr_cond2)
	def expr_eq_2       (self, expr_cond):                                      return expr_cond

	def expr_cond_1     (self, expr_ineq, IF, expr, ELSE, CURLYL, expr_cond, CURLYR):  return AST ('piece', ((expr_ineq, expr), (expr_cond, True)))
	def expr_cond_2     (self, expr_ineq, IF, expr, ELSE, expr_cond):
		return \
				AST ('piece', ((expr_ineq, expr),) + expr_cond.pieces) \
				if expr_cond.is_piece else \
				AST ('piece', ((expr_ineq, expr), (expr_cond, True)))

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
# 	a = p.parse ('x**2.z')
# 	print (a)
