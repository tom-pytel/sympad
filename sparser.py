# Time and interest permitting:
# Proper implementation of vectors with "<b>\vec{x}</b>" and "<b>\hat{i}</b>" variables
# sympy function/variable module prefix
# importing modules to allow custom code execution
# assumptions/hints, systems of equations, ODEs, piecewise expressions, long Python variable names, graphical plots (using matplotlib?)...

# Builds expression tree from text, nodes are nested AST tuples.

import ast as py_ast
from collections import OrderedDict
import os
import re

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT

def _FUNC_name (FUNC):
	return AST.Func.TEX2PY_TRIGHINV.get (FUNC.grp [1], FUNC.grp [1]) if FUNC.grp [1] else \
			FUNC.grp [0] or FUNC.grp [2] or FUNC.grp [3].replace ('\\_', '_') or FUNC.text

def _ast_from_tok_digit_or_var (tok, i = 0):
	return AST ('#', tok.grp [i]) if tok.grp [i] else \
			AST ('@', AST.Var.TEX2PY.get (tok.grp [i + 2].replace (' ', ''), tok.grp [i + 1]) if tok.grp [i + 2] else tok.grp [i + 1])

def _expr_mul_imp (expr_mul_imp, expr_int):
	if expr_mul_imp.is_attr: # x.y * () -> x.y()
		if expr_mul_imp.arg is None:
			if expr_int.is_paren:
				return AST ('.', expr_mul_imp.obj, expr_mul_imp.attr, expr_int.strip_paren (1))
			elif expr_int.is_attr:
				return AST ('.', _expr_mul_imp (expr_mul_imp, expr_int.obj), expr_int.attr)

	elif expr_mul_imp.is_pow: # x^y.z * () -> x.{y.z()}
		if expr_mul_imp.exp.is_attr and expr_mul_imp.exp.arg is None:
			if expr_int.is_paren:
				return AST ('^', expr_mul_imp.base, ('.', expr_mul_imp.exp.obj, expr_mul_imp.exp.attr, expr_int.strip_paren (1)))
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
	if args [iparm].is_fact:
		if args [iparm].fact.is_paren:
			return AST ('!', args [:iparm] + (args [iparm].fact.strip_paren (strip_paren),) + args [iparm + 1:])

	elif args [iparm].is_pow:
		if args [iparm].base.is_paren:
			return AST ('^', args [:iparm] + (args [iparm].base.strip_paren (strip_paren),) + args [iparm + 1:], args [iparm].exp)

	elif args [iparm].is_attr:
		if args [iparm].obj.is_paren:
			return AST ('.', args [:iparm] + (args [iparm].obj.strip_paren (strip_paren),) + args [iparm + 1:], *args [iparm] [2:])

	return AST (*(args [:iparm] + (args [iparm].strip_paren (strip_paren),) + args [iparm + 1:]))

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

	if l == 1:
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

	if commas [-1].is_null_var:
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

	return AST ('func', 'Matrix', ast)

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

	if len (ast.commas) == 1:
		raise lalr1.Incomplete (AST ('^', ast.commas [0], AST.VarNull))

	if len (ast.commas) == 2:
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
			b'eJztXWuP3LaS/TMLZAZQA82XKPmb4zi5xtpOru0EuxgEhuP4XgSb19rO3V0E+e9bpw4lUq+e7pmecfdMYzgtimJRxWIdPovU2cVn//bu1x8/qz579uT5ty/l+uT5K/l9+uSZ/L78Vn///kKDvv5Kfr/89vkj3Dz+EmGfP3whv988fPH4+VPQfvX86xePXz/6' \
			b'9sXT/0TcFw8fpYtJVwuix1+9fvTw5eOXyf/s4avk+zx7v8veb+jVVPGWzyWdf4fn5asXyuTn8vtcWf1O+Xn09bNnDzuKFx1Fzyk8L5589Tck+vDZN/L7xedPXz59+PJv4n38/IvEEHyfZ+932ZsYevz05WNc/p6CuzwhtVdkRF6HmE++VMFqzG+eqpi/ePLd' \
			b'ky9A/uiLr19pXh6mzEBUj//j0dOOHvcPX2lWv3nx5Jm+4tXX8vP2zft3H1//9v71jz/8/OHjm/cS9O5/f3//+pc3H1+//e3n8vb9b/8zuv3Q3b998+Hdhw9vh7e/D2+7uw9//P6uf80//vj17es37/+ZH/4g3n9lPn7945fO+/Hd+97/w/s3b//r3cf+DX+8' \
			b'//n/CuYGb+7fJTSd/3fJ9q/dzZsfcpw3b3vi33N+33z8OGA5s9tzVPD880996E+/9sn98sfPr3/6pRfKjz/9K3v/8Y8+v+/+WRKIp+fhxx9zqu/+u8/ib7/24X1ofvjLL28GNx8++766OFv5deXX5xU9Bh5XrTyu1lRnTdVWEuDWVXvehWlIf7uyFr6o/95X' \
			b'q+Y835t8Kx65moY/wZyn25VpNaWIlyE9g7dZkiGUYTlgZTUl66szE4QVX7nEjLzcBs2Bx0+onD1Pt3Knvlrz5yRJdz4I4F3o6OR53QXBi+T139YdKeJoHlI4MyQspEC9R4J15a0KMVZ2XUmQjXPPVmEcmu5XfL1wCnLTkYMT8eJlCNaiM4Y/XqgMM18EmTIQ' \
			b'XpS6vsI13es9PEh9zR+fZCuvsPoK60Tuwp1K25/3Qa68NT55EIb3STlCkOnteodydVKug+B6cmcGIXFy58oQUSgtNOHPxOQ7M3pzrnJVJRWS7n5FAUoGbHpX/zAF9jcrZsqIxIRtp2UpChicZkPeTUnNP1d0+a2imWGslWHxh4QPA6HEyrkSJvKwD88hkSE+' \
			b'hzQMCTmkZUjdhYhaqdxa/hRIaZO+u4Y/ChKyCfVxCmMXu4fn6Vbuugca1Oi/r7sspvuY71eakrH8EdGfn2ev+FoW6fqcN/CB97airlkLSSkmVERJgaEIhE8RYFT8rocU9JqgbvmzSvKE1+p7RCJnqthJLIIs1myiXL4oUJWJFiVUKhVn3eulKJdf94qZbs0w' \
			b'wOS3uCowl6IDtvO45JG8dz6j4DVaj62rkIAB6JF5kUc4l3r/Ah5UZsIgeJZKFBxLISPhFoKTnAXRy7qKFVqBGKvYVLGtGls1ElkoJJM1aq5mXTUSOVZBKva2qtdVbaraVrU0E+I8SlsK2Esxt5IPqfyFM5SQyL9pqxYtkLQ9la9CVVdNqBr5lWQbVIOCVgEO' \
			b'aq8A3a99VUss8cSqbqq6hR6KeEQ9DOqdqm0lZUl6LVBZC6teLvJgjWv4vjqTR+fS7knuUZ2JBPQiMUQsZyIH3DrGEYHoXasPhYb3tmXwmheTngofcn8/pXpxFijPQHlG/W2SZCivyMDYhTYqr2PN8VlkrppOV5LmUAyu7pQiSUJ15Uhy1hhmKZD3oFrfmqq1' \
			b'd0tpz0LLjNZEcm14sawLlPQcV8twLemzNl08aT0V3quspBEPB5XFC/TL7nGt5Flj+zaXDhX5oLgMVLRgCi5D1dZVG6u2OTBebQJFquAMQdOohAuutd5nvjzjoj9DyJCCNWXNO2NTehp6T/TzrKZAmvr+YvSsSS1kk5RD9WtPafuQEnX7TDTV/EYTl0GW0XGZ' \
			b'jB1kkCCd//tScCZpb61yiL6KoYqSSekluCquq2juiyhEBvVJBnU8yaBu7rsMzuo0OmY32bB5b9vUa0i9ha4KXadYoGafO/TDc8txub033QGdcJDs3vls2oaF2+oFc1L3powxS2TPOV8i1zuVt4uzqHm6K7lp7lRuohbO0eeiOf5cYOZT6wDHRk5ygDwdVQ7W' \
			b'qRZTpRoN+wOr99EcsEktvc4J3ABLre0n8ywn8ywn8yw6Fq12JDBbp3x75TtNjrk89E5tkA7A73pLFNLMddDO2CFxZlJhNamwtJ9wcHOrmLYjCMxB8ieY4xRbWx9YAQtn8aZqgaabnrSclbScgKQi3aOO5gUmWO19nVW8wLyy5bzyvRXCGbsXTWrzmniv1N9r' \
			b'ye9RnYplCkwoq3YFitawr2OSfYBJxgSpR2I4+WHTMkidiCKTjKykY7cAEjklElPsmBYla3Zn2G+p2cMCj2mWBKYgKNhzDq8dh9eOw2t3zoGnSwNPN+mdRYaNV+hnQnHreOtSH9Yd2QL3BXrc7rh63NrVdndswgCDApv67I59dsc+u1zGPQY3E+ipizbNHgbf' \
			b'9eodF30dV1VxaRPqWgXSQQmBmPbEUSCsat6e1lZQ5WoxUjw1Lyx3z0cmycxQkFaV6l6txWkbY9nG3J82HuhwqSW1bEIxYXef0HGBfsJ9KnHivyb+69zh8ezw+HuweiI8+6PrcQmfftLrFJ49m33PZt+nqTqf5uj8AU6roAehjQ9LIZDZmrfat2ej5dlOebZI' \
			b'2k61qbpis9X38Ne9FsN4O5kRF1rcj16pzhzDUqldVmtWAMet3IBwSB3CQM0I1Ixwb+o47eren+wC5kHhFAinkOAUzlMDTziFBJGaA92BXT4ySG2pqS1yEdiwLqlpZIiLkMekXfHYF5EukN3I7EaVEScZOOUg7MbRugyEoPElkxRWQ+omETR3QiTtHciFPf5c' \
			b'QKHaZFO/Tkb1awXrusLeI6neEhtSlcGGuEsXr49p9IaRnBtUgBBHRK2IbLhxVtlXYCUJ7iP4xnjA6+C5hfjKbGMVYo3XQ0TCA5gAF2ADfMDCEcxgXg+TeNgsJM2wwT4gbALCDiA019jkgToJhs4wcoaFKDYEwPocpucw7EZJYHMMBAJLObT+mNvDvB9mArGd' \
			b'BCbRsAXGUia2GbReBMYtrzU3XGKTYMuNigE76KqV0K0aV3GPK3bZ4pFuisPuMimZVY3tZ9jWiQ108lT0YIWtZUIvMlhhq6jXbYYS1HK3GrYdtpoINvDi4Vp/sD1Q/kU1Vw12sjbpPdjNhw2MHttI5b7VBxKp1R2NK+y4hHrojlDdGIddd5KKlJVuDZZfuUQ8' \
			b'kZCAlyE5IQ/gWMJabJCVmPIm7I3FlrYa/+BaHtUgBRfYR4icQWh4u1yxJ1n3w1a6RU5Ue1WDSXlDDTnY79E5g1rGWXWsJxrpixWFUjt7vPY6WgBrFp2lyhLZJawHKGzT0DbPBrWpSmBVUWo24Y6tDj5r+SbNRpbtBg0PM1ou4TCsVm2X59gJM9D6daH5odB+' \
			b'XCUODAUHKHBEAgY22IKE/WHYXdWhAlsMsKMAlgQDhAC+a0hsAQ/QxFlIYGZ7rR2pOIEHiGr9LUCiG0g1tHdbYKaMPiBFDrFbtCH3yp/kDHBSnokoZU7ZNMD9CFuDBHucSZkhxQm0EKk1iwjTtw5A1mUy+zLgcCuYQwcko65gJkOvJvzwANLEvtYeh5mgAGT1' \
			b'Z90+QP0i2iPX+Jd2bRShbWrRLoFouHVklrA026FxDonrhMabQuIuKLwUebVuR2/1t0AebhtuVZ8Fnj4Y4a1WvA0bJd0vraG92wZv9bxTvNXTpstsbr0GSZQIG8Irx1kCVz0BV8pR9hXgSmkVyMpMTJFVZzz10QZ4Mv4B6kPRsQdaEQQj1xq4cidcHRyuGmwq' \
			b'Aq6aIa4a4qpZwlUzxVWjuGqGuGqIqya7bXDVzDvFVTODq2YzrsokNuCqj7OEq2aCq5Sj7CtwldIqcJWZmOIq9xdztC1x5U+4OjRcSRfXajcRvwWucNvoFr55XOmDIa4QVJMw4wq3RkN7twWuyugD0iZdRrhSbpZxNUhiGVc5zgKu9NEAV12Osi/jqksr46pg' \
			b'YoIrm/t/OdqWuAo74epAhmrxSqO1TXhbGq2ZTzRiuxR7HoUB7Pkh9jyx55ewV7gJCL2C0A9ByMmMAd0WIPTzTkHoRyBMgzTlSHUMWNS7dUc2BmWZ5AZQ9nEWRmn6KPJdQ2ymjGZfgc0kPNJ18MzsTOHpMzwzR9vBsz7B8yjhWevRdq3+lvDkUM4uDeVIl6jH' \
			b'8NQxnR2O6SzHdAO6LeBZzzuF53hM18GT4zpcAM+a8Ez5HMGzTHIDPPs4S/CsCc/JUK/LaPYV8Eyskq6DZ2ZnCs882is42g6e8QTPo4Rn5KmA+lvCk1OcuMzDM2Y3gWdUeMYhPCPhWdJtAc847xSecQGekfCMhCdnObt8juBZJrkBnn2cJXhGwnOyltBlNPsK' \
			b'eCaClHKCZ2ZnCs+Y4Zk52g6ezd7hqUYEaeHvlkHql3Ea7i5UsVCqg0w3HGQ6DjLd0iCTdIl6BFWno03H0SZU0AdemKyph9SXA7aMPiBt0oWAxTsSXB1Hnbh4Hv4pUiRRO21QyzTbjW1qfvUCaPVR5BsHoO0ym30ZtJ0YSZdAm181Ba3LI9KCoxnQxvUDLbsZ' \
			b'8LYAL5e100ridUBsD7WZtYOWdpt181uGMg4u7OEcN0Na1923grUrl99xxxV4PTB4uuioEWZh7rIbw7xhcrX+Fo2yYrkekm6BcTfvFONuvlFWphgLKHdEOQPGEO/SMzyOuMD4ZSv8XYILgHcEvJsAPuU8+wrAu94AQOlrLWpFvVNTgEQyRT6MAjSxhP5eTGP0' \
			b'I6sCelwE8879xY2m+2iwDxbrd7hLDVkHRXAYttOBAA5LAA7ZjQEsF4TWTKQAcCCAS9ItALzgFMBhAcCBAA4EcCCAU1ZHAC6T3NBA93GW8Mr5Yn3XEK8po9lX4DXJj3RdA53ZmTbQIUM0c7Rdr9qY06j3KCFaw/QREB1OSjlOSrmlSSnSJepxV1onpdxwUspx' \
			b'UmpAtwU+63mn+FyYlHKclHKclHKclOryOcJnmeQGfPZxlvDJSSk3mZTqMpp9BT4Tq6Tr8JnZmeIzT0oVHG2Jz91sew4WnxsGvHcWoo1+6UD3nwwgSlMFt2SqQLpEPYao2iy4oc2Co83CgG4LiDbzTiGabRY0CwmgtFrAxSfu1gXdGKNlmhswmukXMNoQoxNb' \
			b'hi6n2VdgNPFHug6jmZ0pRrM5Q8HRboNcs5u90Amrh4NV/dQTsIrfAqu4FcH4JTtZ0iXqEVa92sn6oZ2sp53sgO5yrJbRB6RSYn7dY9XnxtTTSlZNzPkglHQjrA7SXMZqQT+PVX0U+boBVrucZl/Gaic90iWsFuxMsKr0xGrB0Y5Y3c0G6YTVA8KqgaBXKu4B' \
			b'Vg2xurTNg3SJeoxV3fWhKRRYNcRqSbcFVs28U6yajFWTsWqIVUOsGmK1pxtjtUxzA1Yz/QJWDbFqJlhNOc2+AqtJeqTrsJrZmWLVZKxmjnbE6v7tmk5LP7cNWqsf7mv1twQtl3780tIP6RL1GLS69OO59IMLStASulz6GVBvAV077xS6eelHM5Kgy6Ufz6Uf' \
			b'z6WfTDeG7ijZDejNSSygl0s/frL002U2+wr0JjGSrkNvZmeK3rz0U3C0I3r3b/Z0Qu9to9fr90tb/S3RSwtFv2Sh6As3Qa9aKHpaKOKCEvREL+0UB9RboNfPO0VvtlPUjCT00krR00rR00ox043Rq6EonPR8A3xzGgvwpbGinxgrdrnNvgK+SY6k6+Dbv2oG' \
			b'vtlYseBoR/ju3yzqBN/bhm/Qz962+lvCl+s5fmk9h3SJegxfXczxXMzRDjOjsSwVviX1FvBdcArfvKSjGUnw5YKO54KO54JOphvDd5TsBvTmJBbQy2UdP1nW6TKbfQV6kxhJ16E3szNFb17WKTjaEb0nq6njR2/NbwLrb4leLvX4paUe0iXqMXp1qcdzqcfT' \
			b'asrTaspzwWdAvQV663mn6M0LPj5bTaWTETyXezyXezLdGL2jZDegNyexgF4u+vjJok+X2ewr0JsYJl2H3szOFL150afgaEf0tif0Hj16I7/grb8lemkM5ZfMk0mXqMfoVfNkT/NkVb3AC5M19ZB6C/TGeafozUbKmpGEXpooe5ooe5ooZ7oxekfJbkBvTmIB' \
			b'vTRU9hND5S6z2VegNxGklBN6MztT9GZD5YKj3dBr92MANTzp6MYBzHN0TzAewVjkABAPMUwILyE4pr8xehW8EQIDfIlegpfY7ekux20c/QGvGa5Eq8EX3HUzW10RtMQsIZvoRngtUlyGakc6j1PCdIJSZqy7ZoSilIjQDNCOgwk6Mzg7HnZE5n6MnuyRNK31' \
			b'3YUlCkZHtnY4srUc2dqlkW1UukQ9tlQkXc1EGr14xvRM2dSZ2m41uLULTncB5cGtzYNby8Gt5eDWcnCb6cbbgIbJthuXhopUFjYDcXxrJ+PbLr/ZV2wGSsIkXbcZqI85sxkoj28LjnZE8v7Now4WxncVwxClrueG4Xpu4HpuWFrPJV2iHmE46Hpu4HouLpIr' \
			b'vTBZUw+pLwdwGX1AKkUX8qpuyKu6gau6gau6gau6mW4E4HGyy+gtkphHb+DCbpgs7HaZzb6M3k6MpEvoLdiZoDfkhd2Cox3Re7nBVFMA2J4wfKgYBvMtMIzf8limll1k2k9FO4JxJJJJjZe3EyQjqGY6qgtAsl6YuKkTdeJgi7Oa2nmnZzW1PZI1O0SycuX4' \
			b'Vj4I64JufHjTKNkN5zflJOaRrI8i3zhAcpfZ7Ct60gwJpOtOcsrsTJCs9ERywdGOSN6/OdUJw7fdDjvIEe2wG7bDju2wW2qHXXaTdthpO+zYDju2w47tsGM7XFJv0Q67eaftsMvtsMvtsGM77NgOO7bDPd24HR4lu6EdzkkstMOO7bCbtMMps9lXtMNJjKTr' \
			b'2uHMzrQddrkdzhztiN6TgdUsejlxcmQoDpAkUDwcEQeOiMPSiJh0iXqMYh0OBw6HA4fDgcPhwOHwgHoLFC84RXEeDoc8HA4cDgcOhwOHw5lujOJRshtQnJMwfe5nsMwRcZiMiLssZ1+B5ZQc6TosZ6amWM4j4oKvHbFcVxc3fIb8jRwgHxZwZmfwtesh8t2G' \
			b'9lAtHyaPLeuHcY78TZ8hrweeTVV8D+fId9vGIcDl8+SliAsNnT9Y/to6iqak/SSfOsC3V7bW1HpGWztNRcMbhxqrZ7I21fgzCFPV1WN5Po36AsnG3bwab1ZhiHd7NZ6qMrSgPwDDD9S5a3dHNXMMUgW3f/FjOrtVwWFPX/Jgj6g5pOp4vVAlQ8mbDdXxXr7r' \
			b'MXOy176/7ZGO6jLprK49KLZZ6ILsWD9DxAvf+oDEl+pnUWQrimz9X/xs4LX6EmGvn6Rxn+SrNJgKusKXaW6mNzE6ke4mv0xjBtt2b+vrNBDt7l+oEa5uus+7rZJyqLkvPcUJQjA5r/fYCb5tnb2tLynZ1JDvR2f1pCzF/mQv6469YrRzm/QXXQf3QBLVL06Y' \
			b'6uIQRm6m+17ZDkeZ7Wv0ho+bhF0r3E+vtFfp73KaCGa9ppuguIVKVhcE9K3rXStaewjq2X9gz92glrotNFX8okP3TGOhIFYnNldYvtu/5tr1FlUs3gqR2atosduPFvvr17N2z1o8NxvdzUIvdXDbA653401qslDH/WlxnOwnUC3GMGyxs+uozVfTYr8fLQ7X' \
			b'1+JSg+sb6jFs0OD7qL2l5ho1+t9772GD5l5Da8N+tLber9bGk9bevtY2x6O19X60dnnp+0pa25y09va1tj0erY2HMFq7/QmEQ1LLG13vhVTCLUwW7KB21Z9Szg8EGDqb1dwvBfTXtEEQZYTUj1UXb3TiClZRl9gdQHaLatmvzopaHYBSihz7aax9q2dpfrbN' \
			b'9NU9qC+NnuXX6NTVnvXVxN2mrHZqwoX97ZU1XkNfm6Ft5bWr0iXj532ac9VJT/0N6CoiBbUn3Y+2anqdwiabxn1VrAv2x/sz6DINlRSZmK1cbftAgK2fdt5lAeuksHtUWNavuOxHYf1RK6yjwvrLFdZWF4fQP72FgdGsTfmsLWxzVI37qjftvtFB0Iyh60Kj' \
			b'7aqLw1CoQ1Amlc+xKdIBKJE/FCX6FLWS0T4HqvEFpTKfUqlqcwWdAtE+1UpFsKhVMBVfSYx5/ar+rKUBhHlTsHKN2hCG6uIQ1O0Q6qxCtyD1U311SX1V/WncA0Gh6lF90qO+mnJH1vBhv6X7pIok9RJKMDxYoeDqB6tGlSqelKpXKn9sSuUr5fnglKqpLnCU' \
			b'U43z3UwVjfa7Wj3NQrRqJ02S0hvpCnTiMh3Qcp+UORqgviC1sK5cbiyrcWsByV8i6WZOspCPZD3J54rTN822szbumrMym3A1I+fA+ZNwTag0ndR3mzOx15oVWcaDev1gxkPS7Upw9+LbsqK8kUIbFVi9j4rtCnMM+y6iVD6NdMStlo+tLlTYOFdnrWwHRZ5L' \
			b'4RRzcBRHzgnWcprvzyX4bJVOOLT6MdgY0sYUU6OuM9gaG3VHFfbgpR0mocVLVnYDoa0Gfxrf5fj6bV1vB0c9YB9ug3TKcxjUTrVfpkonJOTTD/DtxAp/LTb1cDNCGP7rzhrLfYqOkXXjrT43XNeCHx8HTBOvUdn1N8KupLDbn/ISLuclbssOzpQYsBSquT/M' \
			b'hS880Vlr9Stz9U0yJ6PX3f+UrfQ1Cp7AuJkzHA86Yg4ne2zFYFPp+kIz+4cpkeIOrcb4T3ltduKVB55cmWMh2vDX9Vw3xlKm2yswzVNarsZ62mLddtuqUT+ZanfX9ch3caOuNbLffbUeFcynFAHqNgxP6LkVx/ybw8i/q27dMf/2OvnHIcZjEayvIwZfXd1h' \
			b'cDoKwphz2wQoDpfF4fckkfKYpSWpBHOZZEJFh2Yr7MFtSGfhEQXkD1VAsfrUjgIKYwEVx4dRUo7fgN1eXtqwx6jHfvVnfg3P+Roe5oURCfomlwgUXeuNQsWY6dM5g4MmZASwIx2LoT5QPcXc3Sd2FFC8VE93ktRAPReldm2FdFXpZKDDX3p2dRi2kxgD9vko' \
			b'YSHlhTdSts1RyrapDthRsO1RCratDthxFmR9jIJ1nLQ+UEfBmqMUrKkO2FGw9igF66sDdhTsZAh0HcFe1nXds3hjtS+HtZhxkJsEXclRzJOB1O2PE64v77ba7HgC8aXRtndYSbkqMeV+AOOza8sdC1ZH4yj2yXjsGMXeVMfjKPbLR3lHIPa2Oh5HsV8+ADx8' \
			b'sWMx/GgcxX758PAIxG6r43FcEr988Hg8U56wODgyx0Iw2bhLMtcQETjADqWhRUFZGjW0gFGLWrT0JisxUUj3H5ZOLSyXTAMDPBRApJgb1m96FpPFKiybGT3lRu/Tc5wfghKwatOBZZ+kKjiioVABKSuNYdNJSpGnfCTbDN1PPxPbVaN/xm4nsVH+SuGryT/N' \
			b'u2DvcmGimok0MrL8/vz/ATnYTfo='

	_PARSER_TOP             = 'expr_commas'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	_TEXGREEK = '(?:' + '|'.join (reversed (sorted (f'\\\\{g}' for g in AST.Var.GREEK))) + ')'
	_LETTER   = fr'[a-zA-Z]'
	_VARPY    = fr'(?:{_LETTER}(?:\w|\\_)*)'
	_VARTEX   = fr'(?:{_TEXGREEK}|\\partial|(?:(?:\\overline|\\bar|\\widetilde|\\tilde)\s*)?\\infty)'
	_VARTEX1  = fr'(?:(\d)|({_LETTER})|({_VARTEX}))'
	_VAR      = fr'(?:{_VARPY}|{_VARTEX})'

	_STR      = r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY - {'@'})))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LETTER})'),
		('LOG',           r'log\b|\\log(?!{_LETTER})'),
		('FUNC',         fr'(@|{_FUNCPY}\b)|\\({_FUNCTEX})\b|\$({_LETTER}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}}'),
		('LIM',          fr'\\lim(?!{_LETTER})'),
		('SUM',          fr'\\sum(?!{_LETTER})'),
		('INT',          fr'\\int(?:\s*\\limits)?(?!{_LETTER})'),
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
		('IF',            r'if(?!{_LETTER})'),
		('ELSE',          r'else(?!{_LETTER})'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
		('VAR',          fr'(\\partial)\s?({_VAR})|{_VAR}'),
		('ATTR',         fr'\.(?:({_LETTER}\w*)|\\text\s*{{\s*({_LETTER}\w*)\s*}})'),
		('STR',          fr"(?<!\d|{_LETTER}|')({_STR})|\\text\s*{{\s*({_STR})\s*}}"),
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
		('INEQ',          r'==|!=|\\neq?|<=|\\le|<|\\lt|>=|\\ge|>|\\gt'),
		('EQ',            r'='),
		('DIVIDE',        r'/'),
		('EXCL',          r'!'),
		('AMP',           r'&'),
		('DBLSLASH',      r'\\\\'),
		('COMMA',         r','),
		('ignore',        r'\\,|\\:|\\?\s+|\\text\s*{\s*[^}]*\s*}'),
	])

	_FUNC_AST_REMAP = {
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
	def expr_func_2     (self, SQRT, BRACKL, expr, BRACKR, expr_func_arg):      return _expr_func (1, 'sqrt', expr_func_arg, expr)
	def expr_func_3     (self, LOG, expr_func_arg):                             return _expr_func (1, 'log', expr_func_arg)
	def expr_func_4     (self, LOG, expr_sub, expr_func_arg):                   return _expr_func (1, 'log', expr_func_arg, expr_sub)
	def expr_func_5     (self, FUNC, expr_func_arg):
		func  = _FUNC_name (FUNC)
		xlat = self._FUNC_AST_REMAP.get (func)

		return xlat (expr_func_arg) if xlat else _expr_func (2, 'func', func, expr_func_arg)

	def expr_func_6     (self, FUNC, expr_super, expr_func_arg):
		ast = self.expr_func_5 (FUNC, expr_func_arg)

		return \
				AST ('^', ast, expr_super) \
				if expr_super != AST.NegOne or not ast.is_trigh_func_noninv else \
				AST ('func', f'a{ast.func}', ast.arg)

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
				'partial' + AST.Var.TEX2PY.get (VAR.grp [1], VAR.grp [1].replace ('\\_', '_')) \
				if VAR.grp [0] else \
				AST.Var.TEX2PY.get (VAR.text.replace (' ', ''), VAR.text.replace ('\\_', '_'))

	# def expr_var_1      (self, var, PRIMES, subvar):                            return AST ('@', f'''{var}{subvar}{PRIMES.text.replace ("_prime", "'")}''')
	# def expr_var_2      (self, var, subvar, PRIMES):                            return AST ('@', f'''{var}{subvar}{PRIMES.text.replace ("_prime", "'")}''')
	# def expr_var_3      (self, var, PRIMES):                                    return AST ('@', f'''{var}{PRIMES.text.replace ("_prime", "'")}''')
	# def expr_var_4      (self, var, subvar):                                    return AST ('@', f'{var}{subvar}')
	# def expr_var_5      (self, var):                                            return AST ('@', var)

	# def var_2           (self, VAR):
	# 	return \
	# 			f'\\partial {VAR.grp [2]}' \
	# 			if VAR.grp [1] and VAR.grp [1] != 'd' else \
	# 			AST.Var.SHORT2LONG.get (VAR.grp [0] or VAR.grp [3], VAR.text)

	# def subvar_1        (self, SUB, CURLYL, expr_var, CURLYR):                  return f'_{expr_var.var}' if expr_var.var and expr_var.is_single_var else f'_{{{expr_var.var}}}'
	# def subvar_2        (self, SUB, CURLYL, NUM, CURLYR):                       return f'_{{{NUM.text}}}'
	# def subvar_3        (self, SUB, CURLYL, NUM, subvar, CURLYR):               return f'_{{{NUM.text}{subvar}}}'
	# def subvar_4        (self, SUB1):                                           return f'_{AST.Var.SHORT2LONG.get (SUB1.grp [1] or SUB1.grp [3], SUB1.text [1:])}'

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
# 	a = p.parse ('Piecewise ((1,x<0),')
# 	print (a)
