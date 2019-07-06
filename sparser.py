# TODO: Concretize empty matrix stuff.
# TODO: Concretize empty variable stuff.
# TODO: Change '$' to be more generic function OR variable name escape or do another escape character for variable escapes?
# TODO: remap \begin{matrix} \end{matrix}?

# Builds expression tree from text, nodes are nested AST tuples.

import ast as py_ast
from collections import OrderedDict
import os
import re

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT

def _FUNC_name (FUNC):
	return f'a{FUNC.grp [2] [3:]}' if FUNC.grp [2] else \
			FUNC.grp [0] or FUNC.grp [1] or FUNC.grp [3] or FUNC.grp [4].replace ('\\_', '_') or FUNC.text

def _ast_from_tok_digit_or_var (tok, i = 0):
	return AST ('#', tok.grp [i]) if tok.grp [i] else \
			AST ('@', AST.Var.SHORT2LONG.get (tok.grp [i + 1] or tok.grp [i + 3], tok.grp [i + 2]))

def _expr_mul_imp (expr_mul_imp, expr_int): # convert x.y * (...) -> x.y (...)
	if expr_mul_imp.is_attr and expr_mul_imp.arg is None:
		if expr_int.is_paren:
			return AST ('.', expr_mul_imp.obj, expr_mul_imp.attr, expr_int.strip_paren (1))
		elif expr_int.is_attr:
			return AST ('.', _expr_mul_imp (expr_mul_imp, expr_int.obj), expr_int.attr)

	return AST.flatcat ('*', expr_mul_imp, expr_int)

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast.numer.is_diff_or_part_solo:
			p = 1
			v = ast.numer.var

		elif ast.numer.is_pow and ast.numer.base.is_diff_or_part_solo and ast.numer.exp.is_pos_int:
			p = int (ast.numer.exp.num)
			v = ast.numer.base.var

		else:
			return None

		ast_dv_check = (lambda n: n.is_differential) if v [0] == 'd' else (lambda n: n.is_partial)

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
	if ast.is_differential or ast.is_null_var: # null_var is for autocomplete
		return AST ('intg', None, ast, *from_to)

	elif ast.is_div:
		if ast.denom.is_mul and ast.denom.muls [-1].is_differential:
			return AST ('intg', ('/', ast.numer, ast.denom.muls [0] if len (ast.denom.muls) == 2 else \
					AST ('*', ast.denom.muls [:-1])), ast.denom.muls [-1], *from_to)

		if ast.numer.is_differential:
			return AST ('intg', ('/', ast.One, ast.denom), ast.numer, *from_to)

	elif ast.is_mul and (ast.muls [-1].is_differential or ast.muls [-1].is_null_var): # null_var is for autocomplete
		return AST ('intg', ast.muls [0] if len (ast.muls) == 2 else AST ('*', ast.muls [:-1]), ast.muls [-1], *from_to)

	elif ast.is_add:
		if ast.adds [-1].is_differential:
			return AST ('intg', \
					AST ('+', ast.adds [:-1])
					if len (ast.adds) > 2 else \
					ast.adds [0] \
					, ast.adds [-1], *from_to)

		if ast.adds [-1].is_mul and ast.adds [-1].muls [-1].is_differential:
			return AST ('intg', \
					AST ('+', ast.adds [:-1] + (AST ('*', ast.adds [-1].muls [:-1]),))
					if len (ast.adds [-1].muls) > 2 else \
					AST ('+', ast.adds [:-1] + (ast.adds [-1].muls [0],)) \
					, ast.adds [-1].muls [-1], *from_to)

	elif ast.is_intg and ast.intg is not None:
		return AST ('intg', _expr_int (ast.intg, () if ast.from_ is None else (ast.from_, ast.to)), ast.dv, *from_to)

	raise SyntaxError ('integration expecting a differential')

def _expr_func (iparm, *args, strip_paren = 0): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	if args [iparm].is_fact:
		if args [iparm].fact.is_paren:
			return AST ('!', args [:iparm] + (args [iparm].fact.strip_paren (strip_paren),) + args [iparm + 1:])

	elif args [iparm].is_pow:
		if args [iparm].base.is_paren:
			return AST ('^', args [:iparm] + (args [iparm].base.strip_paren (strip_paren),) + args [iparm + 1:], args [iparm].exp)

	return AST (*(args [:iparm] + (args [iparm].strip_paren (strip_paren),) + args [iparm + 1:]))

def _expr_func_remap (_remap_func, ast): # rearrange ast tree for a given function remapping like 'Derivative' or 'Limit'
	expr = _expr_func (1, None, ast, strip_paren = None) # strip all parentheses

	if expr.op is None:
		return _remap_func (expr [1])
	else:
		return AST (expr.op, _remap_func (expr [1] [1]), *expr [2:])

_remap_func_Limit_dirs = {'+': ('+',), '-': ('-',), '+-': ()}

def _remap_func_Limit (ast): # remap function 'Limit' to native ast representation for pretty rendering
	if ast.is_null_var:
		return AST ('lim', ast, AST.VarNull, AST.VarNull)
	elif not ast.is_comma:
		raise lalr1.Incomplete (AST ('lim', ast, AST.VarNull, AST.VarNull))

	commas = ast.commas
	l      = len (commas)

	if l == 1:
		ast = AST ('lim', commas [0], AST.VarNull, AST.VarNull)
	elif l == 2:
		ast = AST ('lim', commas [0], commas [1], AST.VarNull)
	elif l == 3:
		return AST ('lim', commas [0], commas [1], commas [2], '+')
	elif commas [3].is_str:
		return AST ('lim', *(commas [:3] + _remap_func_Limit_dirs.get (commas [3].str_, ('+',))))
	elif commas [3].is_eq_eq and commas [3].lhs.as_identifier () == 'dir' and commas [3].rhs.is_str:
		return AST ('lim', *(commas [:3] + _remap_func_Limit_dirs.get (commas [3].rhs.str_, ('+',))))
	else:
		ast = AST ('lim', commas [0], commas [1], commas [2])

	if commas [-1].is_null_var:
		return ast

	raise lalr1.Incomplete (ast)

def _remap_func_Sum (ast): # remap function 'Sum' to native ast representation for pretty rendering
	if ast.is_null_var:
		return AST ('sum', ast, AST.VarNull, AST.VarNull, AST.VarNull)
	elif not ast.is_comma:
		ast = AST ('sum', ast, AST.VarNull, AST.VarNull, AST.VarNull)

	else:
		commas = ast.commas

		if len (commas) == 1:
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

def _remap_func_Derivative (ast): # remap function 'Derivative' to native ast representation for pretty rendering
	if ast.is_null_var:
		return AST ('diff', ast, (AST.VarNull,))
	elif not ast.is_comma:
		raise lalr1.Incomplete (AST ('diff', ast, (AST.VarNull,)))
	elif len (ast.commas) == 1:
		raise lalr1.Incomplete (AST ('diff', ast.commas [0], (AST.VarNull,)))

	commas = list (ast.commas [:0:-1])
	ds     = []

	while commas:
		d = commas.pop ().as_differential ()

		if commas and commas [-1].is_num:
			ds.append (AST ('^', d, commas.pop ()))
		else:
			ds.append (d)

	return AST ('diff', ast.commas [0], AST (*ds))

def _remap_func_Integral (ast): # remap function 'Integral' to native ast representation for pretty rendering
	if not ast.is_comma:
		return AST ('intg', ast, ast.as_differential () if ast.is_var else AST.VarNull)
	elif len (ast.commas) == 1:
		ast = AST ('intg', ast.commas [0], AST.VarNull)

	else:
		ast2 = ast.commas [1].strip_paren (1)

		if not ast2.is_comma:
			return AST ('intg', ast.commas [0], ast2.as_differential ())
		elif len (ast2.commas) == 3:
			return AST ('intg', ast.commas [0], ast2.commas [0].as_differential (), ast2.commas [1], ast2.commas [2])
		else:
			ast = AST (*(('intg', ast.commas [0], ast2.commas [0].as_differential ()) + ast2.commas [1:] + (AST.VarNull, AST.VarNull)) [:5])

	raise lalr1.Incomplete (ast)

def _remap_func_Pow (ast):
	if not ast.is_comma:
		raise lalr1.Incomplete (AST ('^', ast, AST.VarNull))

	if len (ast.commas) == 1:
		raise lalr1.Incomplete (AST ('^', ast.commas [0], AST.VarNull))

	if len (ast.commas) == 2:
		ast = AST ('^', ast.commas [0], ast.commas [1])

		if ast.exp.is_null_var:
			raise lalr1.Incomplete (ast)
		else:
			return ast

	raise SyntaxError ('too many parameters')

def _remap_func_Matrix (ast):
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

	return AST ('func', 'Matrix', ast)

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
			b'eJztXftv3EaS/mcOiARwAPaLZOs3O/FmjbOdrOMEexACw3GcRXBxknPs3TsE+79fffU12XzNcEYzkkYjQa3hY7qLVdX19auqOWeXnz1/+uLbbz4rPnv64pV8Pnv6XD6/+VY///ZSb331pXz+5dsXn+PiyV9w7/Gjl/L59aOXT148Q9kvX3z18snrz799+ey/' \
			b'kPflo8/TwaSjRaEnX75+/ujVy6d/TxePB1ffDa6+7q6UKp7yWOj855NXOP3m1Utl87F8vlBmv1OO/uPdrz+iyFfPnz9qi77MRTumcfLo+dfy+cXjZ988e/TNX+X0yYsvMn+4eDy4+m5wlfl7+fTLv75KlF4pF5/LI3Dnyd9Ur3r4+plq+Yun3z394gnyfPHV' \
			b'KxXkUZIEmnr06lVXHtdP/v45pP365dPnT1D61Vfy8fbNh3cfX//24fWPP/zyx8c3H+TWH59++KeevPvf3z+8fv/m4+u3v/3Sv/zw279Gl3+01398+v1dV/SnT7++ff3mwz/a67e/vX//ZnDRK/eDnPYe++un9+3px3cfuvMfPrx5+9/vPnZEPn345f96vHRP' \
			b'lmzt+e8i4a/txZsfuke++fixe9rvWaKf3rz92Bcgc9gx0WPzl5+7uz//2pV7/+mX1z+//729/PHnf+bTn37qRHz3j34BOelY+/HHTPXd/7Tn3dln3xeXZytXFa46L3hS48QUK6vHpjiri6aQGy4UzXl7T+90lysTceb135fFKpzn696lnKBAzQ/P23ImNHBm' \
			b'HR5mojy7weNsfd7eTjfznZX1ehb5YYMQOU935AwnTfvVebqUq/YL3rL6vKZ7XtXdTjfzHXkmzoRXZbXRfy9qiueD6zLfWfFpUGvh5NKRFk4gduCHp0gGAmgd2FIeD/3r/3l3y/YvjUsnuIfiomvRryvP8xV0ZkRlg9thfDX6vppcmf4d4VPtRB5sfDo744Ve' \
			b'aTU7eXB7vdJcBgKkZ5n2y3Szu1gZimKKM1uI9GpYtvAUQ1hhZcx/D9MVy9sm2yjXKunSJOODlM4WzvRNUL7s7uc7gXdsvlPxjst3at7x7R0xJtWM5wfNNd2h4TrHDyg5lZMrnOLMtl+ep0u5ar/QW0H/vW1FTNcuX6/UzqL+i+LPz7szOam0Pil2hROwLYpg' \
			b'cxChpAzQ1ALI3YTPfEMqVDXfYkgRrE8QJenHKqkSp4bPkZZBVUSe5NLTfEQjrleXrmlNAtaU6LvOJEXtrso2yctyeKPuniKXnsCT2ijbE5NO5HHtmWXrhQqQR3sgOrVg6ZZcy+3zYa5xjvZaLvXpQUVOgiVd5Zt2/t4qt1Z4JpvCqpA2Strzy7JwgL3Uh5fm' \
			b'OBRowGNRVUVVF1VT1Kaohazk8Wg3pVwVi7oULUhjBLkEKqEsgimCLRpJDnWtXQM0L+gWoElTJ6YrJloLQQGN1LbosQhFVdS+qOWhclIrioAHAUARXBHkMxShKkJdBJGkRKWKPCK61J8grGmKJhaxLKIpoi2iK6IvYiiiUJMMpfke5onKcfi8PBM5cSWyGsh+' \
			b'JhLjWqTGgV+230W9Ej3ooU53RR1yfXfVUTUU1SaFOCqEerAhSWmT1KqDuyJaXVImT+a9VmdTFo05NZv2TZKUNhpo48Fo7Z01MdWtmqrRMQt6Kqnc6rSxHpMiLIGcDgn7jiB3ah3S4fnjYv7yzLh7Vl+X6Fi1TppcJwTskbFJnPmyx6YUlSlOVTT1kTHrDdvy' \
			b'mNpyR1DUquMe29qbUTDwh5bDmNSusAQPIXURJANelKyi6ZSt86yiMupwz2B5VrMDrevUcKpVHIq484mqPSjV1MgHpV65ovJFJboyRWWLIHVz2qNcETzcV8Gr+yp4fS8FPwucwViO7gw7qYY3Y+rAIr+M7Loi80QOAKMaTKyLKGoB6yWaPJc6QtNNFGUmf4r6' \
			b'00mvyHZqUmmFnY44zWmJI5LA5u68GPUJiIE1LKuNnDYEWPWBrd0pEYRbm9Z67GRW47WWRst5DecvXBy5DpaadvKkrGFRxnJRxmJqZZPODbky7K9MSBOvql2xQBkXmNepcGldwOUpCDt3TkROsYs682l10lPyY2JNcmoV1amKtJ0+vtUkLFkQIOVxMiiATCO3' \
			b'cGx1LKxV19ZI1O3ijOWajOXyC+sKh1Meu19iTcneq8WUS6yfWS6c3TfJbXnPRD4LhHXqv+vq9AHtdFxzSLBMF5uxVqhjKU+9VsxUsQOpTBrhVZz0By58n1XJGcQ6CRxLhdRvR1KMSnG4FnCJZQPL9QJLTzAb7ZjWGBJ9yUxeRbPnnFa7yahTv5s4kZuZu7h0' \
			b'vHRpcO7umgv2EnMJd8fmEjqJcKe2IIL5jk3TEcfpiON0RA6jMixgDQ3PcPZkwuk3XsLTGm3o5AsK05kZpiSunYs5OiwdHYI4NKldaqiyIxIRI1mwnZomzxoOFOKe+krQqzj2MaoFqiYdWOnOtApyqb+x7GjQ1Z28gi7RhZ449jEscBwWOA4LcIi0jOhY75Et' \
			b'YeQsLapS5hsL0YC/e501GJ2MWIRpz/7Cs7/wOtihukQKn1am/DGuKqAJ1oaZgnlyK8R9O3wk/j3x7wl5zVQlzKfRXWC3GdNoLLLBj3p3PF5EPVNlgSoLpw0e7ThPXEaYeFBLCrSkkCwptB0DLSnQkgJtxbO58DQVn8ZfFY2jonHIQbj5XsFUMb6mYv6Q8td3' \
			b'3sVwCXlrylurpjhV4rKu8FuPFu2hBeQXsRpqq2HpJhVoTkMn8RTEMCcgBmwqptjZMgXPltoBlsVlqTywQSNPibSuYHFBq3tqXwVsD0WexLFXgXvSsstkgzmrqal4GHDq0BwjdVUxVN/TjuiOQZPUcj8yESpQgeVfJChlxF9i0CISlNLhlyKeyiffQzwEU0BA' \
			b'SIglGEQQq17lO4SIIywccYWI3ULEFUJqEU+LME7EcCJOEkGSCEGEDwf+G8TWIyIbioaSEbaClRos4mAFp4JO5XssgyA4HWMoRHIj0B6BaIhCQ+wizAM+PET1IqQXa/RYTUfkB5x6iP2NsM8KCsQOFaG2qnUvVqG7KYSqfGInhuSXs4i9ZvK9UJNsFT6Q3esW' \
			b'JsmOTS4GGSt81Niag009UgvpbxWw78sWutWpwRYu7PBCXuwuKU2XkQSgZOyzicqg8LBqjO7NAFfYpVHr80WJiM7HHrUG+04kX439HmWfGHbyRIiJjWBlqRSx20zIg2GU88jX6J4vfQJ4wsYgyYNNdw14oBRSNHBzTPBJMLkOOAqhiEdBhQFPAYcNSrSMgLRc' \
			b'ei3MrSrY1YaC0Ag0bVAAG3UkD/Z4xVaKBndQC1Jvf1bmYoWYfV/Jsfo3JttAorYFi0i0NwLAPvqqnUA3BzibQHddgLsi2BYBhjqOhZpyRhguQcl2CNNsGWJmCi0lwZIZXMbmtAiwfuZUpE50sauwJsygNdthDAAbI2tMZAyvIbZyPsuHrcGWSjAAVyvWFF5K' \
			b'puqw1fKxiC6TQZXZGuDKlBdo/sTmLtAoiH3IMfxbh2MP+DpGfGn3hc8+vjzx5TO+/BBffoovr/jyQ3z5nJbx5cdJ8eWn+PKb8TUisoCvLp/lw9bhy0/wlcSawZcf4ivxsYwvn/HV0d8SX+4BX0eJr6j4Go4QcQlKMeMrDvEVp/iKiq84xFfMaRlfcZwUX3GK' \
			b'r7gZXyMiC/jq8lk+bB2+4gRfSawZfMUhvhIfy/iKGV8dW1viy2+Pr1ucqdl9JmubcLc0WQu3N2FbxCD27UdUSx+DuKy1sloMaraMQVRjm8ZgVFokkcE4KLAERjtJAKPS7YExzdmUA31jBDCph9iWGoFzTHQzOHO+NHfTJ00Bqjko8BCjrbRTjColFkkwbTla' \
			b'hKlSJEx7DG4H0/AA0zsLU6cwdUOYOsLUZZi6IUx7aQJTpzB1Q5j2CyzC1I2TwtTNw9QRpo4wdYQpS41hOiK6ANMuXwtTNw9TR5i6CUyTtDMwdYSpyzBNHC3D1GWYZga3g2n1ANM7C1OdMdrhjNFyxmjzjNEOZ4yovTZNYKpTRzucOg4KLMLUj5PC1M/DlNNH' \
			b'HABTT5iy1BimI6ILMO3ytTCdn05ajnjtZEbZSjsDU84otWSCaeJoGaZ5UtljcDuY1oeF6ZxL5vrAKta1Ca/mHkFWJ6F2OAm1nITaPAm1w0mojTlNIKuzUcvZKGxUqlcPo2KLwI3jpMDNc1IQbXHLaSkOwG0kbjVprhF0h2Tj4kJr5qBF7/xkVXNQ9hF6k8gz' \
			b'6OV8VUsm9DLvFujNU9YegzPoreyFLiRMQdwAxALA1td5VSjTeXo8na7Y01y/Gza4HW8azPaaAK3v39PX2q3kmSutmDkXJG4ncOO0B25X5jQGtyhZ6elnr0selFlCdj9zKlIb0p12ycqE5WsFax5iW2qE6z5FVI5mHgMbb3P0c17KliYRro+dIlxzUPohwlvR' \
			b'5x2WgLgWDVrLgHkqsAxzJUuYZ32NYe7UjPUg6HYlwB337qGPDdb3aSythgvF98Hr6N102bvpht5NfbFnShPsBpIjlR52+2UWsWvHSbFr57FLb6fjgrFjUEEqNcbuiOjmDjnna+E67/3UHBR4BNck7RSujg5Ql+MLWo6WkZp9oD0GtxtOm/Jh2ntnoaqrU264' \
			b'OuW4OuXy6pQbrk65XhpDVWmRRA+n/QKLOHXjpDidX51yXJ1yXJ1yXJ1KpcY4HRFdwGmXr8Xp/OqU4+qUm6xOtdLO4JSrUy6vTrUcLeM0r071GNwSpzsEAx0TThdmvPcGqhwShyFUA6EaMlTDEKohpwlUg0I1DKHaL7AI1TBOCtXQQRWnLVIDkRqI1ECkduXG' \
			b'YB2RXQBrJpPAGubBGgjWMAFrkncGrGkIHDJYE0fLYA0ZrJnBnWa5ZocAowfMHh9ma8VsPcRsTczWGbP1ELN1ThPM1orZeojZfoFFzNbjpJitM2brjNmamK2JWUZO5HJjzI7ILmA2k0mYrecxWxOz9QSzSd4ZzNbEbJ0xmzhaxmydMZsZ3A2zOwQtPWD2+DDb' \
			b'KGabIWYbYrbJmG2GmG1ymmC2Ucw2Q8z2CyxithknxWyTMdtkzDbEbEPMNsRsV26M2RHZBcxmMgmzzTxmG2K2mWA2yTuD2YaYbTJmE0fLmG0yZjODu2H2wIFQDz6hWwKv+oTc0Cfk6BNy2Sfkhj4hF3OagFd9Qo4+IRwcf2/HjYotQjiOk0I4+4Rcb1JLn5Cj' \
			b'T8jRJ5TLjSGsd1EfOcsCjDOpBON5p5CjU8hNnEKtzDMwplPIZadQy9EyjLNTqMfgbjA+cKDUA4xvB8awP9V3H8a4xO7I7P3xQ++PL3Maw1hpkUStB8cfTnOjYksw7mdORepEnTBW6BDGnv4fT/+Pp/8nlxvBeIbyZhT3KBHFft7x4+n48RPHTyvyFMVKiUUS' \
			b'iluOFlHss8+nx+BuKD5wHNUDim8JxRqh7IcRyp4Ryj5HKPthhDIqp00TFGuEsmeEsn7neRgVW0TxJCmKc5wyTlsUM0zZM0zZM0w5lxujeEp5AcWZUkLxfLCyZ7CynwQrtyLPoJjByj4HK7ccLaM4Byv3GNwNxQ9hVqeBYvXm+qE319Ob67M31w+9uaiZNk1Q' \
			b'rK5cT1euZ5iVZ5jVoNgiiu04KYqzQ9fnMCtPf27aAOTpz83lxiieUl5AcaaUUDzv1fX06vqJV7cVeQbF9Or67NVtOVpGcfbq9hjcDcXNYUMx3LVh2eOVOXsh2g5B7U4c2PgZ0IgaHGziY4iVya95MMP3PEDcNk3CNGqSw2fkUFt/dtTzMCq8uLOvGifd2Vd1' \
			b'8MYpXhkPO8TvebpApiwflx4ee+XHe/4mT2iGy9YG4VYzu/8yQaLdzL8dQnMkYQdobzUwswmwUrSb3j5AXm2xD7Dq0N5jcDe0Hz7w6ti6bXt/em6rPbcd9tyWPbfNPbcd9tz8kmkC8IrkSKXmL+N6HlwuZrfovPuZU5HakDrRbXPnbdl5W3belp13LjeOkZ5Q' \
			b'bmZe9zIKk87EiGg7339b9t920n+3Us+ESbP/trn/Tnm3CJPO/XePwZ0QbQ8cnHVscL4vWPbaWfthZ+3ZWfvcWfthZ43aaNNkFK49tZKo9YBROLvpQbHFUXg1TjoKz920r/IonN2zZ/fs2T3ncuNR+JTywig8U0qj8Pl+2bNf9pN+uRV5ZhTOfrm3P7/laHkU' \
			b'nvvlHoO7oXhT6JYfABk/bvOA5YNi2VzH4Fujucwwmsswmqti31x5jr9zQBeyNmy3A3KZaUyXUiShWg/O89AWY5pDNWY8efAdxkkH3zmyy+TILsPILsPILsPIrlxuPOieUnacbq1710amlEbb88FdhsFdZhLc1Yo8M9pmcJfJwV067UtcLY+4c4BXj8kZZPvm' \
			b'Am1mC/BSAI5fVJwB+oHjvR4gPoW4v6kuW33RfuiL9vRF++yL9kNftI85Tbps9UV7+qI9fdGevuhBscUuO46TdtnZF+2zL9rTF+3pi/b0Redy4y57Snmhy86UUpc974r2dEX7iSu6FXluKp2osVjbbSeulrvt7I7uMblbt33gSLC7juaQEY2Ryp1EdVDXdBi6' \
			b'pgNd0yG7psPQNR3KnMaoVlokUesBr+ila3pQbAnV/cypSJ2oE9Uhu6YDXdOBrulA13QuN0L1DOXNqO5R4sG27M1hO9BBHSYO6lbwKbZbYiyVoN2ytgjtkH3UPU53g7YvLtvdxwNwE9kdrPtQNjmccy1k6+G75uZeNLfT3uBqDcyqGXhtGg+3cOrDaAZCHXz6' \
			b'kBlu6p3b0duipg+ZMUxW1SB+chEOMP7xO+A2vQBuh/22qzUvlIIVj0x407ba1m77Fjtjra2p9i2Uvzl77RbIXyI4kB3izXSHsEXfrLHHNc36EdskusKVru4f1jbX+CN2tc/evGiLVnWdnVYb7bQ6kKmGQ1vrumlH31r9jhZbJast06rCptZUaOBN+yLJ0Irl' \
			b'Gnvxr2rN5rotGnbTXI9Vz28Q6Vk1tLuLZUPjOutPWt/QEucRohlYeztKHFt9vV3rbA/UQHMM7w5k+AdvqsMWw4dw+OZ65o2zew8j+sad3ilr0jssD2TkZs04+YrNt1FtbRxmQOnrmnAZDJt4ISLrsLe50qDDHnLcgd8luY7GfBd7dkcxHB69N3k/W970buTZ' \
			b'7fL7Nta72XC1z1A53uZkTWoAP397W1O2AJuNt26r1z11M7obrrylKZw+PcQr2qeo6jbtMzyY6A2ZqNyDc+/WzHRVmX3M1Oxlpliy3tNS/YGNde0q85LR+qM13GreuXsA44X5+IMacDVx1a4qt2jIWOg5gDHb/drc8mDNLsbf19LybmPI98uI+wZsdBPwwVvh' \
			b'LQz4AMbr9jNeczjjjQ/GexvG669lCHEzxrun62yDw3vnAW/5YL23Yr3m7lrvbbvdchDGARfBLL5DaAX6RXNv/XFbey5MzP+HWxjjq7VdWi8/hK8Oq+rbGnfxp1TZhTxIf3hvs9euM3N/VUsvhzFIe7vs/DUHO8wZs0sGbQ5q1LAxYQuHPc1aKSXLToE/h/LH' \
			b'pWi9a4qCmPEw49erYbngddZ4bXWx4tvD3Za+twfbPbzt0uGGw762G0/IdvHESJmWbLcpLo8jquya1341Zn7fUUMwtz5i2Nkur3OdF6Gu+0fsiBiXx2CBNx3PuJPl2btlddfuWbiytclzj8LabiOCdl0gOoc76DbWWJ+7DevDU69ifCh3HfYXdmrsEDm3EoJ2' \
			b'TR9cmQvd1+alL/Ya7CJqu7x9uzwSm5wfJGYjVCN6aAF3bgGLP+OFAFjtzT7Y20KvG+5Ol4sdV+EoDS5cYOtxWV+stK4vVo1an3uwvgXrq+6Q9VWFsntnrM8Xl0Y3QIo2Q3LLVNA6FlmcWgc3pquZeB05Bt1HLwa6vVFWs2anJrblsrea0KL5oHNMNqGByFcw' \
			b'AV2Pnl3ZMKzELSqt3qaSVJdVp8vdl8WqcsfVsEOseO0EZzOuk1Ih2lwdoSh65bWpA6xAbQ9DPEwqub/KJJXX1vauVb19W36jFTyo3D3b3qttFryp6kx1Kc2oN1qXjcyfU5uZNJ81gzeNQCStGGWvHFBT6MdMoFd9XfdZjwiqspTqQAHdrns7fICUOFvp+2uM' \
			b'vvrK8RcTe/vXhfpoczl9lbHotnxzGzekUdeo/kyufMZe4qaVOn0PQ8H2LBEsfQ0/OzdUQeiVPRRH0mlt96ePdZseKxa/y5NdMf6Dm2F6V//06forF9iSv56BMC+928CHxyDPT/6wpDK49oNrZShsxRBfYbArWzL+nv1rB5nrvg/KWbUDZ3y5wk78pb1kVbt/' \
			b'TPiti/V/7YB4Q47RcBUy6BuYq5uVosG4v9nvT5lvboH5WOz9p7zHK/Au3dIc+3ZHETBr2jVhljW9i3nTQlEV1pRJ2h3xskZgs15ocLRecBTEjJMn+6RZInM3Kb85DvldceOJ8tux/L132SRF6E/JLaqj0r4Hb6IJvXfQTN47M9RRKPILZcJIX+mlMBjarNdb' \
			b'XdxO8ukQh7cRHzdfhNp2x2Ft8GrfcKL8ftnatlBE38gWlTI2qyWTwmJZL+G9ttyfbYrRVxuS6cpg1rQpYzAzjxsmqi7cAdWF4pgS9VbdAb1VxTEl6q2+A3rj4uGxJOqtuQN6a4pjStRbPH69YY3tiBKXQiYD+N31ts3Q7QDa88WeCUvP41vSYu1HlVqcTANu' \
			b'dBh8JXVWxebElzwuZtsmmfT2yh0S1Xq7s4urqBVr58ebqNXJLOL4teqLI07U6hZzk2PTaiiOOFGrW0xbjk2rdXHEiVrdYlJzxKs2cEjegURV1ym2AdEMoqlk1o3+BBeWb+hySepCpoBXuTURn71teSwW1xerikmi0wnvlzGpbllLol2UiMmP2zloK7Zk+qoP' \
			b'j7kclqMaxGFIoSbVXpPIWv3B7c46pBaxhu7xRgPdF461iUTPzWYNRS8xo59khGUgc1X0kwlULvZj+qYXL6IOTJSsk8cNkQ21+g5rKfL9+f8DEcplnA==' 

	_PARSER_TOP             = 'expr'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	_GREEK       = '|'.join (reversed (sorted (f'\\\\{g}' for g in AST.Var.GREEK)))
	_SPECIAL     =  r'\\partial|\\pi|\\infty'
	_CHAR        = fr'[a-zA-Z]'
	_PYVAR       = '|'.join (reversed (sorted (AST.Var.PY | {f'_{g}' for g in AST.Var.GREEK})))
	_TEXTVAR     = fr'\\text\s*\{{\s*({_PYVAR})\s*\}}'
	_ONEVAR      = fr'{_CHAR}|{_GREEK}'
	_DSONEVARSP  = fr'(?:(\d)|({_PYVAR})|({_CHAR}|{_GREEK}|{_SPECIAL})|{_TEXTVAR})'
	_STR         =  r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPYONLY  = '|'.join (reversed (sorted (AST.Func.PY_ONLY)))
	_FUNCPYTEX   = '|'.join (reversed (sorted (AST.Func.PY_AND_TEX)))
	_FUNCTEXONLY = '|'.join (reversed (sorted (AST.Func.TEX_ONLY)))

	TOKENS       = OrderedDict ([ # order matters
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('SQRT',          r'\\?sqrt'),
		('LOG',           r'\\?log'),
		('FUNC',         fr'({_FUNCPYONLY})|\\?({_FUNCPYTEX})|\\({_FUNCTEXONLY})|\$({_CHAR}\w*)|\\operatorname\s*\{{\s*({_CHAR}(?:\w|\\_)*)\s*\}}'),
		('LIM',           r'\\lim'),
		('SUM',           r'\\sum'),
		('INT',           r'\\int(?:\s*\\limits)?'),
		('LEFT',          r'\\left'),
		('RIGHT',         r'\\right'),
		('CDOT',          r'\\cdot'),
		('TO',            r'\\to'),
		('BEG_MATRIX',    r'\\begin\s*\{\s*matrix\s*\}'),
		('END_MATRIX',    r'\\end\s*\{\s*matrix\s*\}'),
		('BEG_BMATRIX',   r'\\begin\s*\{\s*bmatrix\s*\}'),
		('END_BMATRIX',   r'\\end\s*\{\s*bmatrix\s*\}'),
		('BEG_VMATRIX',   r'\\begin\s*\{\s*vmatrix\s*\}'),
		('END_VMATRIX',   r'\\end\s*\{\s*vmatrix\s*\}'),
		('BEG_PMATRIX',   r'\\begin\s*\{\s*pmatrix\s*\}'),
		('END_PMATRIX',   r'\\end\s*\{\s*pmatrix\s*\}'),
		('FRAC2',        fr'\\frac\s*{_DSONEVARSP}\s*{_DSONEVARSP}'),
		('FRAC1',        fr'\\frac\s*{_DSONEVARSP}'),
		('FRAC',          r'\\frac'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
		('VAR',          fr"({_PYVAR})|(d|\\partial\s?)?({_ONEVAR})|{_SPECIAL}|{_TEXTVAR}"),
		# ('METHOD_LEFT',  fr'\.(?:({_CHAR}\w*)|\\text\s*{{\s*({_CHAR}\w*)\s*}})\s*\\left\('),
		# ('METHOD',       fr'\.(?:({_CHAR}\w*)|\\text\s*{{\s*({_CHAR}\w*)\s*}})\s*\('),
		# ('MEMBER',       fr'\.(?:({_CHAR}\w*)|\\text\s*{{\s*({_CHAR}\w*)\s*}})'),
		('ATTR',         fr'\.(?:({_CHAR}\w*)|\\text\s*{{\s*({_CHAR}\w*)\s*}})'),
		('STR',          fr"(?<!\d|{_CHAR}|['}}])({_STR})|\\text\s*\{{\s*({_STR})\s*\}}"),
		('PRIMES',        r"'+|(?:_prime)+"),
		('SUB1',         fr'_{_DSONEVARSP}'),
		('SUB',           r'_'),
		('CARET1',       fr'\^{_DSONEVARSP}'),
		('CARET',         r'\^'),
		('DBLSTAR',       r'\*\*'),
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('CURLYL',        r'{'),
		('CURLYR',        r'}'),
		('BRACKETL',      r'\['),
		('BRACKETR',      r'\]'),
		('BAR',           r'\|'),
		('PLUS',          r'\+'),
		('MINUS',         r'-'),
		('STAR',          r'\*'),
		('INEQ',          r'==|!=|\\neq?|<=|\\le|<|\\lt|>=|\\ge|>|\\gt'),
		('EQ',            r'='),
		('DIVIDE',        r'/'),
		('EXCL',          r'!'),
		('AMP',           r'&'),
		('DBLSLASH',      r'\\\\'),
		('COMMA',         r','),
		('ignore',        r'\\,|\\:|\\?\s+'),
	])

	_FUNC_AST_REMAP = {
		'Abs'       : lambda expr: _expr_func (1, '|', expr, strip_paren = 1),
		'abs'       : lambda expr: _expr_func (1, '|', expr, strip_paren = 1),
		'Derivative': lambda expr: _expr_func_remap (_remap_func_Derivative, expr),
		'diff'      : lambda expr: _expr_func_remap (_remap_func_Derivative, expr),
		'exp'       : lambda expr: _expr_func (2, '^', AST.E, expr, strip_paren = 1),
		'factorial' : lambda expr: _expr_func (1, '!', expr, strip_paren = 1),
		'Integral'  : lambda expr: _expr_func_remap (_remap_func_Integral, expr),
		'integrate' : lambda expr: _expr_func_remap (_remap_func_Integral, expr),
		'Limit'     : lambda expr: _expr_func_remap (_remap_func_Limit, expr),
		'limit'     : lambda expr: _expr_func_remap (_remap_func_Limit, expr),
		'Matrix'    : lambda expr: _expr_func_remap (_remap_func_Matrix, expr),
		'ln'        : lambda expr: _expr_func (1, 'log', expr),
		'Pow'       : lambda expr: _expr_func_remap (_remap_func_Pow, expr),
		'pow'       : lambda expr: _expr_func_remap (_remap_func_Pow, expr),
		'Sum'       : lambda expr: _expr_func_remap (_remap_func_Sum, expr),
	}

	def expr_commas_1   (self, expr_comma, COMMA):                              return expr_comma if expr_comma.is_comma else AST (',', (expr_comma,))
	def expr_commas_2   (self, expr_comma):                                     return expr_comma
	def expr_commas_3   (self):                                                 return AST (',', ())
	def expr_comma_1    (self, expr_comma, COMMA, expr):                        return AST.flatcat (',', expr_comma, expr)
	def expr_comma_2    (self, expr):                                           return expr

	def expr            (self, expr_eq):                      	                return expr_eq

	def expr_eq_1       (self, expr_ineq1, EQ, expr_ineq2):                     return AST ('=', '=', expr_ineq1, expr_ineq2)
	def expr_eq_2       (self, expr_ineq):                                      return expr_ineq
	def expr_ineq_2     (self, expr_add1, INEQ, expr_add2):                     return AST ('=', AST.Eq.LONG2SHORT.get (INEQ.text, INEQ.text), expr_add1, expr_add2)
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

	def expr_int_1      (self, INT, expr_sub, expr_super, expr_add):            return _expr_int (expr_add, (expr_sub, expr_super))
	def expr_int_2      (self, INT, expr_add):                                  return _expr_int (expr_add)
	def expr_int_3      (self, expr_lim):                                       return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                           return AST ('lim', expr_neg, expr_var, expr)
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):   return AST ('lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg):  return AST ('lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6      (self, expr_sum):                                                                         return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQ, expr, CURLYR, expr_super, expr_neg):               return AST ('sum', expr_neg, expr_var, expr, expr_super)
	def expr_sum_2      (self, expr_func):                                                                        return expr_func

	def expr_func_1     (self, SQRT, expr_func_arg):                            return _expr_func (1, 'sqrt', expr_func_arg)
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_func_arg):  return _expr_func (1, 'sqrt', expr_func_arg, expr)
	def expr_func_3     (self, LOG, expr_func_arg):                             return _expr_func (1, 'log', expr_func_arg)
	def expr_func_4     (self, LOG, expr_sub, expr_func_arg):                   return _expr_func (1, 'log', expr_func_arg, expr_sub)
	def expr_func_5     (self, FUNC, expr_func_arg):
		func  = _FUNC_name (FUNC)
		remap = self._FUNC_AST_REMAP.get (func)

		return remap (expr_func_arg) if remap else _expr_func (2, 'func', func, expr_func_arg)

	def expr_func_6     (self, FUNC, expr_super, expr_func_arg):
		ast = self.expr_func_5 (FUNC, expr_func_arg)

		return \
				AST ('^', ast, expr_super) \
				if expr_super != AST.NegOne or not ast.is_trigh_func_noninv else \
				AST ('func', f'a{ast.func}', ast.arg)

	def expr_func_7     (self, expr_fact):                                      return expr_fact

	def expr_func_arg_1 (self, expr_func):                                      return expr_func
	def expr_func_arg_2 (self, MINUS, expr_func):                               return expr_func.neg (stack = True)

	def expr_fact_1     (self, expr_fact, EXCL):                                return AST ('!', expr_fact)
	def expr_fact_2     (self, expr_pow):                                       return expr_pow

	def expr_pow_1      (self, expr_pow, expr_super):                           return AST ('^', expr_pow, expr_super)
	def expr_pow_2      (self, expr_attr):                                      return expr_attr

	def expr_attr_1     (self, expr_attr, ATTR):                                return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1])
	def expr_attr_2     (self, expr_abs):                                       return expr_abs

	def expr_abs_1      (self, LEFT, BAR1, expr, RIGHT, BAR2):                  return AST ('|', expr)
	def expr_abs_2      (self, BAR1, expr, BAR2):                               return AST ('|', expr)
	def expr_abs_3      (self, expr_paren):                                     return expr_paren

	def expr_paren_1    (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):       return AST ('(', expr_commas)
	def expr_paren_2    (self, PARENL, expr_commas, PARENR):                    return AST ('(', expr_commas)
	def expr_paren_3    (self, IGNORE_CURLY, CURLYL, expr, CURLYR):             return expr
	def expr_paren_4    (self, expr_frac):                                      return expr_frac

	def expr_frac_1     (self, FRAC, expr_mat1, expr_mat2):                     return AST ('/', expr_mat1, expr_mat2)
	def expr_frac_2     (self, FRAC1, expr_mat):                                return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_mat)
	def expr_frac_3     (self, FRAC2):                                          return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 4))
	def expr_frac_4     (self, expr_mat):                                       return expr_mat

	def expr_mat_1      (self, LEFT, BRACKETL, BEG_MATRIX, expr_mat_rows, END_MATRIX, RIGHT, BRACKETR):  return AST ('mat', expr_mat_rows) if expr_mat_rows else AST ('func', 'Matrix', ('[', ()))
	def expr_mat_2      (self, BEG_MATRIX, expr_mat_rows, END_MATRIX):                                   return AST ('mat', expr_mat_rows) if expr_mat_rows else AST ('func', 'Matrix', ('[', ()))
	def expr_mat_3      (self, BEG_BMATRIX, expr_mat_rows, END_BMATRIX):                                 return AST ('mat', expr_mat_rows) if expr_mat_rows else AST ('func', 'Matrix', ('[', ()))
	def expr_mat_4      (self, BEG_VMATRIX, expr_mat_rows, END_VMATRIX):                                 return AST ('mat', expr_mat_rows) if expr_mat_rows else AST ('func', 'Matrix', ('[', ()))
	def expr_mat_5      (self, BEG_PMATRIX, expr_mat_rows, END_PMATRIX):                                 return AST ('mat', expr_mat_rows) if expr_mat_rows else AST ('func', 'Matrix', ('[', ()))
	def expr_mat_6      (self, expr_curly):                                                              return expr_curly
	def expr_mat_rows_1 (self, expr_mat_row, DBLSLASH):                         return expr_mat_row
	def expr_mat_rows_2 (self, expr_mat_row):                                   return expr_mat_row
	def expr_mat_rows_3 (self):                                                 return ()
	def expr_mat_row_1  (self, expr_mat_row, DBLSLASH, expr_mat_col):           return expr_mat_row + (expr_mat_col,)
	def expr_mat_row_2  (self, expr_mat_col):                                   return (expr_mat_col,)
	def expr_mat_col_1  (self, expr_mat_col, AMP, expr):                        return expr_mat_col + (expr,)
	def expr_mat_col_2  (self, expr):                                           return (expr,)

	def expr_curly_1    (self, LEFT, CURLYL, expr_commas, RIGHT, CURLYR):       return _expr_curly (expr_commas)
	def expr_curly_2    (self, CURLYL, expr_commas, CURLYR):                    return _expr_curly (expr_commas)
	def expr_curly_3    (self, expr_bracket):                                   return expr_bracket

	def expr_bracket_1  (self, LEFT, BRACKETL, expr_commas, RIGHT, BRACKETR):   return AST ('[', expr_commas.commas if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_2  (self, BRACKETL, expr_commas, BRACKETR):                return AST ('[', expr_commas.commas if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_3  (self, expr_term):                                      return expr_term

	def expr_term_1     (self, STR):                                            return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_2     (self, SUB):                                            return AST ('@', '_') # for last expression variable
	def expr_term_3     (self, expr_var):                                       return expr_var
	def expr_term_4     (self, expr_num):                                       return expr_num

	def expr_num        (self, NUM):                                            return AST ('#', NUM.text) if NUM.grp [0] or NUM.grp [2] else AST ('#', NUM.grp [1])

	def expr_var_1      (self, var, PRIMES, subvar):                            return AST ('@', f'''{var}{subvar}{PRIMES.text.replace ("_prime", "'")}''')
	def expr_var_2      (self, var, subvar, PRIMES):                            return AST ('@', f'''{var}{subvar}{PRIMES.text.replace ("_prime", "'")}''')
	def expr_var_3      (self, var, PRIMES):                                    return AST ('@', f'''{var}{PRIMES.text.replace ("_prime", "'")}''')
	def expr_var_4      (self, var, subvar):                                    return AST ('@', f'{var}{subvar}')
	def expr_var_5      (self, var):                                            return AST ('@', var)

	def var_2           (self, VAR):
		return \
				f'\\partial {VAR.grp [2]}' \
				if VAR.grp [1] and VAR.grp [1] != 'd' else \
				AST.Var.SHORT2LONG.get (VAR.grp [0] or VAR.grp [3], VAR.text)

	def subvar_1        (self, SUB, CURLYL, expr_var, CURLYR):                  return f'_{expr_var.var}' if expr_var.var and expr_var.is_single_var else f'_{{{expr_var.var}}}'
	def subvar_2        (self, SUB, CURLYL, NUM, CURLYR):                       return f'_{{{NUM.text}}}'
	def subvar_3        (self, SUB, CURLYL, NUM, subvar, CURLYR):               return f'_{{{NUM.text}{subvar}}}'
	def subvar_4        (self, SUB1):                                           return f'_{AST.Var.SHORT2LONG.get (SUB1.grp [1] or SUB1.grp [3], SUB1.text [1:])}'

	def expr_sub_1      (self, SUB, expr_frac):                                 return expr_frac
	def expr_sub_2      (self, SUB1):                                           return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1    (self, DBLSTAR, expr_func):                             return expr_func
	def expr_super_2    (self, DBLSTAR, MINUS, expr_func):                      return expr_func.neg (stack = True)
	def expr_super_3    (self, CARET, expr_frac):                               return expr_frac
	def expr_super_4    (self, CARET1):                                         return _ast_from_tok_digit_or_var (CARET1)

	def caret_or_dblstar_1 (self, DBLSTAR):                                     return '**'
	def caret_or_dblstar_2 (self, CARET):                                       return '^'

	#...............................................................................................
	_AUTOCOMPLETE_SUBSTITUTE = { # autocomplete means autocomplete AST tree so it can be rendered, not expression
		'CARET1'             : 'CARET',
		'SUB1'               : 'SUB',
		'FRAC2'              : 'FRAC',
		'FRAC1'              : 'FRAC',
		# 'expr_sub'           : 'SUB',
		'expr_super'         : 'CARET',
		'caret_or_doublestar': 'CARET',
	}

	_AUTOCOMPLETE_CONTINUE = {
		'RIGHT'      : ' \\right',
		'COMMA'      : ',',
		'PARENL'     : '(',
		'PARENR'     : ')',
		'CURLYR'     : '}',
		'BRACKETR'   : ']',
		'BAR'        : '|',
	}

	def _mark_error (self):
		self.autocompleting = False

		if self.erridx is None:
			self.erridx = self.tokens [self.tokidx].pos

	def _insert_symbol (self, sym):
		tokidx = self.tokidx

		for sym in ((sym,) if isinstance (sym, str) else sym):
			if sym in self.TOKENS:
				self.tokens.insert (tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

				if self.autocompleting and sym in self._AUTOCOMPLETE_CONTINUE:
					self.autocomplete.append (self._AUTOCOMPLETE_CONTINUE [sym])
				else:
					self.autocompleting = False

			else:
				self.tokens.insert (tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, ('', '', '', '')))
				self._mark_error ()

			tokidx += 1

		return True # for convenience

	def _parse_autocomplete_expr_comma (self, rule):
		idx = -1 - len (rule [1])

		if self.stack [idx].sym == 'CURLYL': # vector or matrix potentially being entered
			if idx == -2: # { something
				if self.stack [-1].red.is_vec or self.stack [-3].sym == 'CURLYL' or \
						(self.stack [-1].sym == 'expr' and self.stack [-2].sym == 'CURLYL' and self.stack [-3].sym == 'COMMA' and \
						self.stack [-4].red.is_vec and self.stack [-5].sym == 'CURLYL'):
					return self._insert_symbol (('COMMA', 'CURLYR'))
				else:
					return self._insert_symbol ('CURLYR')

			elif idx == -3: # { something ,
				if self.stack [-2].red.is_comma:
					self._mark_error ()

					return False

			elif idx == -4: # { expr_comma(s) , something
				if (self.stack [-1].red.is_vec or self.stack [-1].sym == 'expr') and self.stack [-2].sym == 'COMMA':
					vlen = len (self.stack [-1].red.vec) if self.stack [-1].red.is_vec else 1
					cols = None

					if self.stack [-3].red.is_vec and self.tokens [self.tokidx - 1] == 'CURLYR' and vlen < len (self.stack [-3].red.vec):
						cols = len (self.stack [-3].red.vec)

					elif self.stack [-3].red.is_comma and not sum (not c.is_vec for c in self.stack [-3].red.commas) and \
							not sum (len (c.vec) != len (self.stack [-3].red.commas [0].vec) for c in self.stack [-3].red.commas) and \
							vlen < len (self.stack [-3].red.commas [0].vec):

						cols = len (self.stack [-3].red.commas [0].vec)

					if cols is not None:
						vec               = self.stack [-1].red.vec if self.stack [-1].red.is_vec else (self.stack [-1].sym,)
						self.stack [-1]   = lalr1.State (self.stack [-1].idx, self.stack [-1].sym, AST ('vec', vec + (AST.VarNull,) * (cols - vlen)))
						self.autocomplete = []

						self._mark_error ()

						return True

			return self._insert_symbol ('CURLYR')

		elif self.stack [idx - 1].sym == 'LEFT':
			return self._insert_symbol ('RIGHT')
		elif self.stack [idx].sym == 'PARENL':
			return self._insert_symbol ('PARENR')
		elif self.stack [idx].sym == 'BRACKETL':
			return self._insert_symbol ('BRACKETR')

		return False

	def _parse_autocomplete_expr_int (self):
		s               = self.stack [-1]
		self.stack [-1] = lalr1.State (s.idx, s.sym, AST ('*', (s.red, AST.VarNull)))
		expr_vars       = set ()
		expr_diffs      = set ()

		if self.autocompleting:
			stack = [s [2]]

			while stack:
				ast = stack.pop ()

				if ast.is_var:
					(expr_diffs if ast.is_differential else expr_vars).add (ast.var)
				else:
					stack.extend (filter (lambda a: isinstance (a, tuple), ast))

		expr_vars = expr_vars - {'_', AST.E.var, AST.I.var} - set (AST.Var.LONG2SHORT) - set (var [1:] for var in expr_diffs)

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

		if pos == 1 and rule == ('expr_func', ('FUNC', 'expr_func_arg')) and \
				_FUNC_name (self.stack [-1].sym) not in AST.Func.PY_ALL:
			return self._insert_symbol (('PARENL', 'PARENR'))

		if pos >= len (rule [1]):
			if rule [0] in {'expr_comma', 'expr_commas'}: # end of comma expression?
				return self._parse_autocomplete_expr_comma (rule)
			elif rule [0] == 'expr_int': # exception raised by rule reduction function?
				return self._parse_autocomplete_expr_int ()

			return False

		return self._insert_symbol (rule [1] [pos])

	def parse_success (self, red):
		self.parse_results.append ((red, self.erridx, self.autocomplete))

		return True # continue parsing if conflict branches remain to find best resolution

	def parse (self, text):
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

		return next (iter (rated)) [-1]

class sparser: # for single script
	Parser = Parser

if __name__ == '__main__':
	p = Parser ()
	a = p.parse ('x.y ().z.w')
	print (a)
