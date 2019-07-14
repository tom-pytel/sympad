# Time and interest permitting:
# sets
# assumptions/hints
# importing modules to allow custom code execution
# Proper implementation of vectors with "<b>\vec{x}</b>" and "<b>\hat{i}</b>" variables
# sympy function/variable module prefix
# systems of equations, ODEs, graphical plots (using matplotlib?)...

# Builds expression tree from text, nodes are nested AST tuples.

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

def _ast2tuple_func_args (ast):
	ast = ast.strip_paren ()

	return ast.commas if ast.is_comma else (ast,)

def _expr_mul_imp (expr_mul_imp, expr_int):
	if expr_mul_imp.is_attr: # x.y * () -> x.y()
		if expr_mul_imp.args is None:
			if expr_int.is_paren:
				return AST ('.', expr_mul_imp.obj, expr_mul_imp.attr, _ast2tuple_func_args (expr_int))
			elif expr_int.is_attr:
				return AST ('.', _expr_mul_imp (expr_mul_imp, expr_int.obj), expr_int.attr)

	elif expr_mul_imp.is_pow: # x^y.z * () -> x.{y.z()}
		if expr_mul_imp.exp.is_attr and expr_mul_imp.exp.args is None:
			if expr_int.is_paren:
				return AST ('^', expr_mul_imp.base, ('.', expr_mul_imp.exp.obj, expr_mul_imp.exp.attr, _ast2tuple_func_args (expr_int)))
			elif expr_int.is_attr:
				return AST ('^', expr_mul_imp.base, ('.', _expr_mul_imp (expr_mul_imp.exp, expr_int.obj), expr_int.attr))

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

def _expr_func (iparm, *args, strip_paren = 0): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	def astarg (arg):
		return (_ast2tuple_func_args (arg) if args [0] == 'func' else arg.strip_paren (strip_paren)),

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

def _expr_func_xlat (_xlat_func, ast): # rearrange ast tree for a given function translation like 'Derivative' or 'Limit'
	expr = _expr_func (1, None, ast, strip_paren = None) # strip all parentheses

	if expr.op is None:
		return _xlat_func (expr [1])
	else:
		return AST (expr.op, _xlat_func (expr [1] [1]), *expr [2:])

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
	_PARSER_TABLES = \
			b'eJztXWuP3LaS/TMLZAZQA82XKPmb4zi5xtpOru0EuxgEhuP4XgSb19rO3V0E+e9bpw4lUq+e7pmecfdMYzgtimJRxWIdPovU2cVn//bu1x8/qz579uT5ty/l+uT5q6/k8vTJM/l9+a3+/v3FKwR9jQdffvv8EW4ef4mwzx++kN9vHr54/PwpiL96/vWLx68f' \
			b'ffvi6X8i7ouHj9LFpKsF0eOvXj96+PLxy+R/9vBV8n2evd9l7zf0aqp4y+eSzr/D8/LVC2Xyc/l9rqx+p/w8+vrZs4cdxYuOoucUnhdPvvobEn347Bv5/eLzpy+fPnz5N/E+fv5FYgi+z7P3u+xNDD1++vIxLn9PwV2ekNorMiKvQ8wnX6pkNeY3T1XOXzz5' \
			b'7skXIH/0xdevNC8PU2Ygqsf/8ehpR4/7h680q9+8ePJMX/Hqa/l5++b9u4+vf3v/+scffv7w8c17CXr3v7+/f/3Lm4+v3/72c3n7/rf/Gd1+6O7fvvnw7sOHt8Pb34e33d2HP35/17/mH3/8+vb1m/f/zA9/EO+/Mh+//vFL5/347n3v/+H9m7f/9e5j/4Y/' \
			b'3v/8fwVzgzf37xKazv+7ZPvX7ubNDznOm7c98e85v28+fhywnNntOSp4/vmnPvSnX/vkfvnj59c//dIL5cef/pW9//hHn993/ywJxNPz8OOPOdV3/91n8bdf+/A+ND/85Zc3g5sPn31fXZyt/Lry6/OKHgOPq1YeV2uqs6ZqKwlw66o978I0pL9dWQtf1H/v' \
			b'q1Vznu9NvhWPXE3Dn2DO0+3KtJpSxMuQnsHbLMkQyrAcsLKakvXVmQnCiq9cYkZeboPmwOMnVM6ep1u5U1+t+XOSpDsfBPAudHTyvO6C4EXy+m/rjhRxNA8pnBkSFlKg3iPBuvJWhRgru64kyMa5Z6swDk33K75eOAW56cjBiXjxMgRr0RnDHy9UhpkvgkwZ' \
			b'CC9KXV/hmu71Hh6kvuaPT7KVV1h9hXUid+FOpe3P+yBX3hqfPAjD+6QcIcj0dr1DuTop10FwPbkzg5A4uXNliCiUFprwZ2LynRm9OVe5qpIKSXe/ogAlAza9q3+YAvubFTNlRGLCttOyFAUMTrMh76ak5p8ruvxW0cww1sqw+EPCh4FQYuVcCRN52IfnkMgQ' \
			b'n0MahoQc0jKk7kJErVRuLX8KpLRJ313DHwUJ2YT6OIWxi93D83Qrd90DDWr039ddFtN9zPcrTclY/ojoz8+zV3wti3R9zhv4wHtbUdeshaQUEyqipMBQBMKnCDAqftdDCnpNULf8WSV5wmv1PSKRM1XsJBZBFms2US5fFKjKRIsSKpWKs+71UpTLr3vFTLdm' \
			b'GGDyW1wVmEvRAdt5XPJI3jufUfAarcfWVUjAAPTIvMgjnEu9fwEPKjNhEDxLJQqOpZCRcAvBSc6C6GVdxQqtQIxVbKrYVo2tGoksFJLJGjVXs64aiRyrIBV7W9XrqjZVbatamglxHqUtBeylmFvJh1T+whlKSOTftFWLFkjanspXoaqrJlSN/EqyDapBQasA' \
			b'B7VXgO7XvqollnhiVTdV3UIPRTyiHgb1TtW2krIkvRaorIVVLxd5sMY1fF+dyaNzafck96jORAJ6kRgiljORA24d44hA9K7Vh0LDe9syeM2LSU+FD7m/n1K9OAuUZ6A8o/42STKUV2Rg7EIbldex5vgsMldNpytJcygGV3dKkSShunIkOWsMsxTIe1Ctb03V' \
			b'2rultGehZUZrIrk2vFjWBUp6jqtluJb0WZsunrSeCu9VVtKIh4PK4gX6Zfe4VvKssX2bS4eKfFBcBipaMAWXoWrrqo1V2xwYrzaBIlVwhqBpVMIF11rvM1+ecdGfIWRIwZqy5p2xKT0NvSf6eVZTIE19fzF61qQWsknKofq1p7R9SIm6fSaaan6jicsgy+i4' \
			b'TMYOMkiQzv99KTiTtLdWOURfxVBFyaT0ElwV11U090UUIoP6JIM6nmRQN/ddBmd1Gh2zm2zYvLdt6jWk3kJXha5TLFCzzx364bnluNzem+6ATjhIdu98Nm3Dwm31gjmpe1PGmCWy55wvkeudytvFWdQ83ZXcNHcqN1EL5+hz0Rx/LjDzqXWAYyMnOUCejioH' \
			b'61SLqVKNhv2B1ftoDtikll7nBG6Apdb2k3mWk3mWk3kWHYtWOxKYrVO+vfKdJsdcHnqnNkgH4He9JQpp5jpoZ+yQODOpsJpUWNpPOLi5VUzbEQTmIPkTzHGKra0PrICFs3hTtUDTTU9azkpaTkBSke5RR/MCE6z2vs4qXmBe2XJe+d4K4Yzdiya1eU28V+rv' \
			b'teT3qE7FMgUmlFW7AkVr2NcxyT7AJGOC1CMxnPywaRmkTkSRSUZW0rFbAImcEokpdkyLkjW7M+y31Oxhgcc0SwJTEBTsOYfXjsNrx+G1O+fA06WBp5v0ziLDxiv0M6G4dbx1qQ/rjmyB+wI9bndcPW7tars7NmGAQYFNfXbHPrtjn10u4x6Dmwn01EWbZg+D' \
			b'73r1jou+jququLQJda0C6aCEQEx74igQVjVvT2srqHK1GCmemheWu+cjk2RmKEirSnWv1uK0jbFsY+5PGw90uNSSWjahmLC7T+i4QD/hPpU48V8T/3Xu8Hh2ePw9WD0Rnv3R9biETz/pdQrPns2+Z7Pv01SdT3N0/gCnVdCD0MaHpRDIbM1b7duz0fJspzxb' \
			b'JG2n2lRdsdnqe/jrXothvJ3MiAst7kevVGeOYanULqs1K4DjVm5AOKQOYaBmBGpGuDd1nHZ17092AfOgcAqEU0hwCuepgSecQoJIzYHuwC4fGaS21NQWuQhsWJfUNDLERchj0q547ItIF8huZHajyoiTDJxyEHbjaF0GQtD4kkkKqyF1kwiaOyGS9g7kwh5/' \
			b'LqBQbbKpXyej+rWCdV1h75FUb4kNqcpgQ9yli9fHNHrDSM4NKkCII6JWRDbcOKvsK7CSBPcRfGM84HXw3EJ8ZbaxCrHG6yEi4QFMgAuwAT5g4QhmMK+HSTxsFpJm2GAfEDYBYQcQmmts8kCdBENnGDnDQhQbAmB9DtNzGHajJLA5BgKBpRxaf8ztYd4PM4HY' \
			b'TgKTaNgCYykT2wxaLwLjlteaGy6xSbDlRsWAHXTVSuhWjau4xxW7bPFIN8Vhd5mUzKrG9jNs68QGOnkqerDC1jKhFxmssFXU6zZDCWq5Ww3bDltNBBt48XCtP9geKP+imqsGO1mb9B7s5sMGRo9tpHLf6gOJ1OqOxhV2XEI9dEeobozDrjtJRcpKtwbLr1wi' \
			b'nkhIwMuQnJAHcCxhLTbISkx5E/bGYktbjX9wLY9qkIIL7CNEziA0vF2u2JOs+2Er3SInqr2qwaS8oYYc7PfonEEt46w61hON9MWKQqmdPV57HS2ANYvOUmWJ7BLWAxS2aWibZ4PaVCWwqig1m3DHVgeftXyTZiPLdoOGhxktl3AYVqu2y3PshBlo/brQ/FBo' \
			b'P64SB4aCAxQ4IgEDG2xBwv4w7K7qUIEtBthRAEuCAUIA3zUktoAHaOIsJDCzvdaOVJzAA0S1/hYg0Q2kGtq7LTBTRh+QIofYLdqQe+VPcgY4Kc9ElDKnbBrgfoStQYI9zqTMkOIEWojUmkWE6VsHIOsymX0ZcLgVzKEDklFXMJOhVxN+eABpYl9rj8NMUACy' \
			b'+rNuH6B+Ee2Ra/xLuzaK0Da1aJdANNw6MktYmu3QOIfEdULjTSFxFxReirxat6O3+lsgD7cNt6rPAk8fjPBWK96GjZLul9bQ3m2Dt3reKd7qadNlNrdegyRKhA3hleMsgauegCvlKPsKcKW0CmRlJqbIqjOe+mgDPBn/APWh6NgDrQiCkWsNXLkTrg4OVw02' \
			b'FQFXzRBXDXHVLOGqmeKqUVw1Q1w1xFWT3Ta4auad4qqZwVWzGVdlEhtw1cdZwlUzwVXKUfYVuEppFbjKTExxlfuLOdqWuPInXB0arqSLa7WbiN8CV7htdAvfPK70wRBXCKpJmHGFW6OhvdsCV2X0AWmTLiNcKTfLuBoksYyrHGcBV/pogKsuR9mXcdWllXFV' \
			b'MDHBlc39vxxtS1yFnXB1IEO1eKXR2ia8LY3WzCcasV2KPY/CAPb8EHue2PNL2CvcBIReQeiHIORkxoBuCxD6eacg9CMQpkGacqQ6Bizq3bojG4OyTHIDKPs4C6M0fRT5riE2U0azr8BmEh7pOnhmdqbw9BmemaPt4Fmf4HmU8Kz1aLtWf0t4cihnl4ZypEvU' \
			b'Y3jqmM4Ox3SWY7oB3RbwrOedwnM8puvgyXEdLoBnTXimfI7gWSa5AZ59nCV41oTnZKjXZTT7CngmVknXwTOzM4VnHu0VHG0Hz3iC51HCM/JUQP0t4ckpTlzm4Rmzm8AzKjzjEJ6R8CzptoBnnHcKz7gAz0h4RsKTs5xdPkfwLJPcAM8+zhI8I+E5WUvoMpp9' \
			b'BTwTQUo5wTOzM4VnzPDMHG0Hz2bv8FQjgrTwd8sg9cs4DXcXqlgo1UGmGw4yHQeZbmmQSbpEPYKq09Gm42gTKugDL0zW1EPqywFbRh+QNulCwOIdCa6Oo05cPA//FCmSqJ02qGWa7cY2Nb96AbT6KPKNA9B2mc2+DNpOjKRLoM2vmoLW5RFpwdEMaOP6gZbd' \
			b'DHhbgJfL2mkl8TogtofazNpBS7vNuvktQxkHF/ZwjpshrevuW8HalcvvuOMKvB4YPF101AizMHfZjWHeMLlaf4tGWbFcD0m3wLibd4pxN98oK1OMBZQ7opwBY4h36RkeR1xg/LIV/i7BBcA7At5NAJ9ynn0F4F1vAKD0tRa1ot6pKUAimSIfRgGaWEJ/L6Yx' \
			b'+pFVAT0ugnnn/uJG03002AeL9TvcpYasgyI4DNvpQACHJQCH7MYAlgtCayZSADgQwCXpFgBecArgsADgQAAHAjgQwCmrIwCXSW5ooPs4S3jlfLG+a4jXlNHsK/Ca5Ee6roHO7Ewb6JAhmjnarldtzGnUe5QQrWH6CIgOJ6UcJ6Xc0qQU6RL1uCutk1JuOCnl' \
			b'OCk1oNsCn/W8U3wuTEo5Tko5Tko5Tkp1+Rzhs0xyAz77OEv45KSUm0xKdRnNvgKfiVXSdfjM7EzxmSelCo62xOdutj0Hi88NA947C9FGv3Sg+08GEKWpglsyVSBdoh5DVG0W3NBmwdFmYUC3BUSbeacQzTYLmoUEUFot4OITd+uCbozRMs0NGM30CxhtiNGJ' \
			b'LUOX0+wrMJr4I12H0czOFKPZnKHgaLdBrtnNXuiE1cPBqn7qCVjFb4FV3Ipg/JKdLOkS9QirXu1k/dBO1tNOdkB3OVbL6ANSKTG/7rHqc2PqaSWrJuZ8EEq6EVYHaS5jtaCfx6o+inzdAKtdTrMvY7WTHukSVgt2JlhVemK14GhHrO5mg3TC6gFh1UDQKxX3' \
			b'AKuGWF3a5kG6RD3Gqu760BQKrBpitaTbAqtm3ilWTcaqyVg1xKohVg2x2tONsVqmuQGrmX4Bq4ZYNROsppxmX4HVJD3SdVjN7EyxajJWM0c7YnX/dk2npZ/bBq3VD/e1+luClks/fmnph3SJegxaXfrxXPrBBSVoCV0u/Qyot4CunXcK3bz0oxlJ0OXSj+fS' \
			b'j+fST6YbQ3eU7Ab05iQW0MulHz9Z+ukym30FepMYSdehN7MzRW9e+ik42hG9+zd7OqH3ttHr9fulrf6W6KWFol+yUPSFm6BXLRQ9LRRxQQl6opd2igPqLdDr552iN9spakYSemml6Gml6GmlmOnG6NVQFE56vgG+OY0F+NJY0U+MFbvcZl8B3yRH0nXw7V81' \
			b'A99srFhwtCN8928WdYLvbcM36GdvW/0t4cv1HL+0nkO6RD2Gry7meC7maIeZ0ViWCt+Segv4LjiFb17S0Ywk+HJBx3NBx3NBJ9ON4TtKdgN6cxIL6OWyjp8s63SZzb4CvUmMpOvQm9mZojcv6xQc7Yjek9XU8aO35jeB9bdEL5d6/NJSD+kS9Ri9utTjudTj' \
			b'aTXlaTXlueAzoN4CvfW8U/TmBR+frabSyQieyz2eyz2ZbozeUbIb0JuTWEAvF338ZNGny2z2FehNDJOuQ29mZ4revOhTcLQjetsTeo8evZFf8NbfEr00hvJL5smkS9Rj9Kp5sqd5sqpe4IXJmnpIvQV647xT9GYjZc1IQi9NlD1NlD1NlDPdGL2jZDegNyex' \
			b'gF4aKvuJoXKX2ewr0JsIUsoJvZmdKXqzoXLB0W7otfsxgBqedHTjAOY5uicYj2AscgCIhxgmhJcQHNPfGL0K3giBAb5EL8FL7PZ0l+M2jv6A1wxXotXgC+66ma2uCFpilpBNdCO8FikuQ7UjnccpYTpBKTPWXTNCUUpEaAZox8EEnRmcHQ87InM/Rk/2SJrW' \
			b'+u7CEgWjI1s7HNlajmzt0sg2Kl2iHlsqkq5mIo1ePGN6pmzqTG23GtzaBae7gPLg1ubBreXg1nJwazm4zXTjbUDDZNuNS0NFKgubgTi+tZPxbZff7Cs2AyVhkq7bDNTHnNkMlMe3BUc7Inn/5lEHC+O7imGIUtdzw3A9N3A9Nyyt55IuUY8wHHQ9N3A9FxfJ' \
			b'lV6YrKmH1JcDuIw+IJWiC3lVN+RV3cBV3cBV3cBV3Uw3AvA42WX0FknMozdwYTdMFna7zGZfRm8nRtIl9BbsTNAb8sJuwdGO6L3cYKopAGxPGD5UDIP5FhjGb3ksU8suMu2noh3BOBLJpMbL2wmSEVQzHdUFIFkvTNzUiTpxsMVZTe2807Oa2h7Jmh0iWbly' \
			b'fCsfhHVBNz68aZTshvObchLzSNZHkW8cILnLbPYVPWmGBNJ1JzlldiZIVnoiueBoRyTv35zqhOHbbocd5Ih22A3bYcd22C21wy67STvstB12bIcd22HHdtixHS6pt2iH3bzTdtjldtjldtixHXZshx3b4Z5u3A6Pkt3QDuckFtphx3bYTdrhlNnsK9rhJEbS' \
			b'de1wZmfaDrvcDmeOdkTvycBqFr2cODkyFAdIEigejogDR8RhaURMukQ9RrEOhwOHw4HD4cDhcOBweEC9BYoXnKI4D4dDHg4HDocDh8OBw+FMN0bxKNkNKM5JmD73M1jmiDhMRsRdlrOvwHJKjnQdljNTUyznEXHB145YrquLGz5D/kYOkA8LOLMz+Nr1EPlu' \
			b'Q3uolg+Tx5b1wzhH/qbPkNcDz6Yqvodz5Ltt4xDg8nnyUsSFhs4fLH9tHUVT0n6STx3g2ytba2o9o62dpqLhjUON1TNZm2r8GYSp6uqxPJ9GfYFk425ejTerMMS7vRpPVRla0B+A4Qfq3LW7o5o5BqmC27/4MZ3dquCwpy95sEfUHFJ1vF6okqHkzYbqeC/f' \
			b'9Zg52Wvf3/ZIR3WZdFbXHhTbLHRBdqyfIeKFb31A4kv1syiyFUW2/i9+NvBafYmw10/SuE/yVRpMBV3hyzQ305sYnUh3k1+mMYNtu7f1dRqIdvcv1AhXN93n3VZJOdTcl57iBCGYnNd77ATfts7e1peUbGrI96OzelKWYn+yl3XHXjHauU36i66DeyCJ6hcn' \
			b'THVxCCM3032vbIejzPY1esPHTcKuFe6nV9qr9Hc5TQSzXtNNUNxCJasLAvrW9a4VrT0E9ew/sOduUEvdFpoqftGhe6axUBCrE5srLN/tX3PteosqFm+FyOxVtNjtR4v99etZu2ctnpuN7mahlzq47QHXu/EmNVmo4/60OE72E6gWYxi22Nl11OarabHfjxaH' \
			b'62txqcH1DfUYNmjwfdTeUnONGv3vvfewQXOvobVhP1pb71dr40lrb19rm+PR2no/Wru89H0lrW1OWnv7Wtsej9bGQxit3f4EwiGp5Y2u90Iq4RYmC3ZQu+pPKecHAgydzWrulwL6a9ogiDJC6seqizc6cQWrqEvsDiC7RbXsV2dFrQ5AKUWO/TTWvtWzND/b' \
			b'ZvrqHtSXRs/ya3Tqas/6auJuU1Y7NeHC/vbKGq+hr83QtvLaVemS8fM+zbnqpKf+BnQVkYLak+5HWzW9TmGTTeO+KtYF++P9GXSZhkqKTMxWrrZ9IMDWTzvvsoB1Utg9KizrV1z2o7D+qBXWUWH95Qprq4tD6J/ewsBo1qZ81ha2OarGfdWbdt/oIGjG0HWh' \
			b'0XbVxWEo1CEok8rn2BTpAJTIH4oSfYpayWifA9X4glKZT6lUtbmCToFon2qlIljUKpiKryTGvH5Vf9bSAMK8KVi5Rm0IQ3VxCOp2CHVWoVuQ+qm+uqS+qv407oGgUPWoPulRX025I2v4sN/SfVJFknoJJRgerFBw9YNVo0oVT0rVK5U/NqXylfJ8cErVVBc4' \
			b'yqnG+W6mikb7Xa2eZiFatZMmSemNdAU6cZkOaLlPyhwNUF+QWlhXLjeW1bi1gOQvkXQzJ1nIR7Ke5HPF6Ztm21kbd81ZmU24mpFz4PxJuCZUmk7qu82Z2GvNiizjQb1+MOMh6XYluHvxbVlR3kihjQqs3kfFdoU5hn0XUSqfRjriVsvHVhcqbJyrs1a2gyLP' \
			b'pXCKOTiKI+cEaznN9+cSfLZKJxxa/RhsDGljiqlR1xlsjY26owp78NIOk9DiJSu7gdBWgz+N73J8/baut4OjHrAPt0E65TkMaqfaL1OlExLy6Qf4dmKFvxabergZIQz/dWeN5T5Fx8i68VafG65rwY+PA6aJ16js+hthV1LY7U95CZfzErdlB2dKDFgK1dwf' \
			b'5sIXnuistfqVufommZPR6+5/ylb6GgVPYNzMGY4HHTGHkz22YrCpdH2hmf3DlEhxh1Zj/Ke8NjvxygNPrsyxEG3463quG2Mp0+0VmOYpLVdjPW2xbrtt1aifTLW763rku7hR1xrZ775ajwrmU4oAdRuGJ/TcimP+zWHk31W37ph/e5384xDjsQjW1xGDr67u' \
			b'MDgdBWHMuW0CFIfL4vB7kkh5zNKSVIK5TDKhokOzFfbgNqSz8IgC8ocqoFh9akcBhbGAiuPDKCnHb8BuLy9t2GPUY7/6M7+G53wND/PCiAR9k0sEiq71RqFizPTpnMFBEzIC2JGOxVAfqJ5i7u4TOwooXqqnO0lqoJ6LUru2QrqqdDLQ4S89uzoM20mMAft8' \
			b'lLCQ8sIbKdvmKGXbVAfsKNj2KAXbVgfsOAuyPkbBOk5aH6ijYM1RCtZUB+woWHuUgvXVATsKdjIEuo5gL+u67lm8sdqXw1rMOMhNgq7kKObJQOr2xwnXl3dbbXY8gfjSaNs7rKRclZhyP4Dx2bXljgWro3EU+2Q8doxib6rjcRT75aO8IxB7Wx2Po9gvHwAe' \
			b'vtixGH40jmK/fHh4BGK31fE4LolfPng8nilPWBwcmWMhmGzcJZlriAgcYIfS0KKgLI0aWsCoRS1aepOVmCik+w9LpxaWS6aBAR4KIFLMDes3PYvJYhWWzYyecqP36TnOD0EJWLXpwLJPUhUc0VCogJSVxrDpJKXIUz6SbYbup5+J7arRP2O3k9gof6Xw1eSf' \
			b'5l2wd7kwUc1EGhlZfn/+/1UmTkE=' 

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

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY - {'@'})))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LETTER})'),
		('LOG',           r'log\b|\\log(?!{_LETTER})'),
		('FUNC',         fr'(@|{_FUNCPY}\b)|\\({_FUNCTEX})\b|\$({_LETTERU}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}}'),
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

	_FUNC_AST_XLAT = {
		'Abs'       : lambda expr: _expr_func (1, '|', expr, strip_paren = 1),
		'abs'       : lambda expr: _expr_func (1, '|', expr, strip_paren = 1),
		'Derivative': lambda expr: _expr_func_xlat (_xlat_func_Derivative, expr),
		'diff'      : lambda expr: _expr_func_xlat (_xlat_func_Derivative, expr),
		'exp'       : lambda expr: _expr_func (2, '^', AST.E, expr, strip_paren = 1),
		'factorial' : lambda expr: _expr_func (1, '!', expr, strip_paren = 1),
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

	def expr_mul_imp_1  (self, expr_mul_imp, expr_int):                         return _expr_mul_imp (expr_mul_imp, expr_int)
	def expr_mul_imp_2  (self, expr_int):                                       return expr_int

	def expr_int_1      (self, INTG, expr_sub, expr_super, expr_add):            return _expr_int (expr_add, (expr_sub, expr_super))
	def expr_int_2      (self, INTG, expr_add):                                  return _expr_int (expr_add)
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
	def expr_func_5     (self, FUNC, expr_func_arg):
		func  = _FUNC_name (FUNC)
		xlat = self._FUNC_AST_XLAT.get (func)

		return xlat (expr_func_arg) if xlat else _expr_func (2, 'func', func, expr_func_arg)

	def expr_func_6     (self, FUNC, expr_super, expr_func_arg):
		ast = self.expr_func_5 (FUNC, expr_func_arg)

		return \
				AST ('^', ast, expr_super) \
				if expr_super != AST.NegOne or not ast.is_trigh_func_noninv else \
				AST ('func', f'a{ast.func}', ast.args)

	def expr_func_7     (self, expr_attr):                                      return expr_attr

	def expr_func_arg_1 (self, expr_func):                                      return expr_func
	def expr_func_arg_2 (self, MINUS, expr_func):                               return expr_func.neg (stack = True)

	def expr_attr_1     (self, expr_attr, ATTR):                                return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1])
	def expr_attr_2     (self, expr_pow):                                       return expr_pow

	def expr_pow_1      (self, expr_pow, expr_super):                           return AST ('^', expr_pow, expr_super)
	def expr_pow_2      (self, expr_fact):                                      return expr_fact

	def expr_fact_1     (self, expr_fact, EXCL):                                return AST ('!', expr_fact)
	def expr_fact_2     (self, expr_abs):                                       return expr_abs

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
		expr_diffs      = set ()
		expr_parts      = set ()

		if self.autocompleting:
			stack = [s [2]]

			while stack:
				ast = stack.pop ()

				if ast.is_var:
					(expr_diffs if ast.is_diff else expr_vars if not ast.is_part_any else expr_parts).add (ast.var)
				else:
					stack.extend (filter (lambda a: isinstance (a, tuple), ast))

		expr_vars = expr_vars - {'_', AST.E.var, AST.I.var, AST.Pi.var, AST.Infty.var, AST.CInfty.var} - set (var [1:] for var in expr_diffs)

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
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT:
# 	p = Parser ()
# 	a = p.parse ('sin**-1 x')
# 	print (a)
