# TODO: Concretize empty matrix stuff.
# TODO: Concretize empty variable stuff.
# TODO: remap \begin{matrix} \end{matrix}?

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
		d = commas.pop ().as_diff

		if commas and commas [-1].is_num:
			ds.append (AST ('^', d, commas.pop ()))
		else:
			ds.append (d)

	return AST ('diff', ast.commas [0], AST (*ds))

def _remap_func_Integral (ast): # remap function 'Integral' to native ast representation for pretty rendering
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
			b'eJztXWuP3LaS/TMLZAZQA8235G924ptrrO3kOk6wi4FhOI5zEWycZB1nH1j4v29VHVIkJXWre0Yzo2kPhqMHxUcVWYevKrLPLr74l3e//fRF88WzJ8+//47uT56/pOvTJ8/o+t33cv3HC/H65mu6/u3751/yy+O/sd+jhy/o+u3DF4+fP+W4Xz//5sXj119+' \
			b'/+Lpv3PYFw+/jDcV75ojPf769bOHL+PTo/z4Q378Fo+SEqf8iOL+Kz989/KFEPaIrs+FvB+Ehi+/efbsYYrxIsXoqeOHF0++/jsn+vDZt3T96tHT754+/O7v9Pj4+VeRIH56lB9/yI+RII71EhlSsvLxH1Jocvv2qRThV09+ePLVYw7z1TcvheaHkWguhocv' \
			b'X/bx+f3xv33JjH374smzxxz75Td0efvmw7uPr3//8PqnH3/98+ObD+T17n/++PD6/ZuPr9/+/mv5+uH3/x68/pne//zrj3d91J//+u3t6zcf/pk//kiP/5XT/u2v9+nx47sP/fOPH968/Y93H9Pr278+/Pq/RYZ98hQsPf9B1P+WXt782NPz5uPHPrc/Mtk/' \
			b'v3n7saQyU9gTUZD56y+97y+/9fHe//Xr61/e/5Fef/rlv/Ljzz/3LL77ZxmBHnrSfvopp/ruP9Nz/9Sz//v792+qlz+/eNVcnG2Ma4w/b/AQ5KHZWL7rbXPWNl1DHrpruvPkJz7960YrfvLyb+k9nOd3lV83krbqcLHuPL5SGpKS48w4PcW5aURj3+jXe2y0' \
			b'kKvln98NvvADJxn9kT6Fjp4IZJszzpPS88mD0uQn9hVK1BYXS5GVOh94VZ78SE+U6IYKr202yNXyA4cIuFjQTk8b1UquRLwigrXh//Peq3pVNj6wH0enImVut+f5jcuGaidU3n74prvKJ4zeVOlDdIoUMHs+Pp0peTkXRrk2DSWZ3jcSivg50zEvlT5Gz/5l' \
			b'o8CKac6IbOKRS902FkJGebfnu7+zhJKAHRJM1aE2SuqDihsyprgcdUOuEDX62PtnHw8fk30CfGz2aeHjkg9JlZSbxYVLEvHpBUJqDC5S8kjJGHnkJ50+nsdXeksfxCvIv9WJxfhu8vtG5EwpXKjoz8/zIz21UqUAccsPTHloIGlacTmpHotIlH2jX+GhpPBN' \
			b'jydGHCDX4rKJbPCjQj7UBohYx2Km1kD4ptI/s0V1MqAgFVxMsTJdL5WUu/G9WMZXVXuEPhd6tWg3fIMWix90fCDe0xNgp7judNvYmC03E4AuCZA9p5bzgsQoNMQVUUtUkaAIrVrqwdomNNx2etd43/jQhG0TFDNH8kGNDrVbvm08N4REF7UQlBPLr9s2TjUt' \
			b'ORaxRhpnapa5LAhyLP0tV0mgBKWGqPxtQ2k1wTSBMnVN8CxwxK6IbeN04+hKgVzjfOMCyz/VEoGRgEF8tURo27TUwBOFuulU09HVvGrOKPVz6iGYy3ORcrkRq8Q+A4NfDcJovOkgHy/OrPifUTHwDQm08Vsnb97h5qNvkNzuVPl48EXVijLQKAOwrm1kTEdG' \
			b'pfjWzE0HNizotVKjoWva7QmIsg2ROQixhQy6LWS5bWMNigyeOKq7LXhXAGW8aZSAAWCNyACNduyt03vBo6KTr5UL6bvOpcfqSx7gu33KgBnTZcpa07QUxzWtv336LARap/5FA9xBSrKgVHqZ2IlF4KvYdMduCi23QzvOWUt6goUTk7czD8aDPX1snQX0aCHy' \
			b'bERerpCeiYMeo66aUGx1nSTodeNN423jt41XjWsb151aXRCv9jPi1X1GvPrPhdczh3G/xtBJofNo4yQndj4R2R3CdOhLzjrTT6k05lL65LoWmQwSWyfDDjFC7JwAIyJ0d5qD9s5z4AXyd5Jyfzcp55UlLbN7wTEvzLAQrZ1q34JqKwIzmMZYqYvBulpA14PF' \
			b'jIWoaLf9uonGuonGuonm7kxLyfIaAt+MBcXGoXMzmDf1kwv0cphinEjncGbTBFL6+9umRkHCjY8VIQ3+KlZxeBEBNHWroYm6E0z4W7uCyiNq3JLA9WlRRGMtRGPZA23KSQ47g0j/aa9lXPDqlMbq1Mkze4aOJMR+JZzmbMkIKK8oEsWCJS9LSSdtUGweXz3a' \
			b'Or+NowWPmanD6OHMRY2IRVyUvMMwo1NptsraYSp+c45pkRmPQcRvqNtrJ3z51eDVxNGZuQNqsgseP5r1jx9l4GhOYNrKw1odh6AGQ1CDISjdimB6CzkioqsPMh7lGCrKndVpeGqgbzFQbvCtjZhp0UPeMuctUGiBMwP+KD0DdH8uy20qcoxiiKWBN7NNhWFi' \
			b'U6fRxnGLeoqFccEN9un1gtzvGPQ7Bv0O+gTb2DvRJzBto76Q6USDZdFgWbE1UPwqrZJdyUSImztpWsGEAYGUnk3DCKDQAnjy1UfkpeFDGwcFBDrw7MCzOzlZlS7m9NhigZSqkyul76IQuNTAQghcrGaPavaoZroRuxBvDx26jwHDXVw0vGDeAngLwjmm01jt' \
			b'IRLDYE2OOebwxEmLkmkRu40R2jtbDN3dpJyIuZOUs7B00UZtG43UttKhbJsLSoManph100VSYqJO1gM6yUlz0wSimSwj/LTMySTnIJdHkVqGk04KTgtjIZYL5J1VmFvKckt5bvnZ0j/lvKXh9Zay33L5EGGsFmVyeH2CFyjYtk74pzhsqsNWOmxAwTYQbG7G' \
			b'9k9s/MTWRmxqxBakbK3HA122GWBdOiteefrIhpdsrMPWK8FR0cg+AjEw9mIBzgbx1CizTT+F3QQxSm5k8wDV/cayfTRbPW+bjWPTYvrGOxfYdj1wKmy/To+cmBHb7o1jS2IlZsmblqNzUPLv+J8NzDkbSoKka2M9kmdrb95EwFbKbMvcsp0x3QPvA9jCqrnj' \
			b'NGVPA4WldDhpSoUJ9XF/AIW0YjlPMdj2nHJu2dKbwpALbFLOfJCX440H7M1ROXN6pirbBCdG8bwvITCtzA+zzDRR/mw277aveFLEEjYhWTYJV1vIVwIUusEsayL/DKJe4mSQg35yj/SVYMHgHbOaXiSpRADnKJg+4pHt5AoJhVkaVRJVby+tu6SUvjGPe6XV' \
			b'T0gs+bOt5KTk6kJ6KTwvz1RS7KMk0zdenOGVGWIwSzYbltM3tiGopLzlktkh020v1bVcUwKtNFJmJOIsZ3wpxLyNf3Pi3lZ/LPhKQfhdhFa7FflvewQwAUZIUUz2AAt9UhETnMwIChy82wuIdggJMFPDgtJmYiIwkGsGhwNAqO687BPaZLBEEgvINP/n7QPG' \
			b'O1U83d0nGSNcJIvpeQzZG4JOhZswD5cpqGwjXJaEyqEwmYOGksaerwU25BW+ERsSLINDvtSgkDhyLWDBLCc3B40ybI7EhNtR76D2dxBVCqmzqFCRP+8BhRBdoSJxknGh6t4i5TmChUQDGnLeFSCUfsBtEonMA8YsVTXd7SfZKnIPjJsHhhdg+BoYHsDwGRi+' \
			b'BoYfA8MLMOphkfLZzQLDTzgBhh8Dw+8HRpnCNDD6z/uA4UfAiJwUwPA1MGKeY2D4DIw+7wOBYe+BcfPAYEnteEZWAkNe4RuBIcEyMORLDQyJI9cCGFplNweMMmyOFLZIuQaG5L8bGFUKk8DIn/cAQ4iugJE4ycAQSjIwUp4jYEg0ACPnfSAw3DHAuN3piDl6' \
			b'RrIPMPtmJPoGZiWz4DECHlODxwA8JoPH1OAx2Y1QZARFpkZRGWEORVNOUGRqFMWZidCAfA0yNm2KNURVmeI0qnKGuycoOoLLjMAVGSzAZQRcOk9TUu5jfJmMrz6pA/Hl7/G1Unw5wZer8YWZPt8SvlyNL5fdCF9O8OVqfJUR5vDlJpzgy03jywFfDvhywBdi' \
			b'DfFVpjiNr5zhHnw54Gu0LpYYLPDlgK+i/4q5j/HlMr76YAfiK9zja6X4klmRrmdFGrMinWdFup4Vcc0kN8KXTI90PT2qIszhy084wZefxhemSHI6BsKaNsUa4qtMcRpfOcM9+PLA12jWlBgs8IVZk8SI+Iq5j/GVJ06ZigPx1S6Nr0Lhc0Mo2+4GmjoNrInA' \
			b'yUE3BdYMJlomT7RMPdFiRVpyQ6xJZLlSUXZyOg5ug2gziCvD5khhi/SBOA4aAWcw9TKYfcmtjZG68YJ2mabQNgW7ItfdsJOzbxwYqmCXuMywM5iTSQzALoYZw87kaVmmYgp23j2QBaIx+jpGX1JFXg2Dal3dHPFb9nT7tJw3gUK7FBL1QDnKHhO6JPZOqNQ1' \
			b'Kgs3Uic5pCfXohOs4sxBUk84gaSe7ASFDBEewaQGJhFrCMiUHNeBKRC5U/Oact8DTQ1o6hE0I7djfaxEsVKBgk8EnMBnVjvlghjik7khXIogtXT7hD0eC3SKKwPkqYw7DWBXq6kM1FQmq6lMrabiSkhuhDqP+HItUVfGmUOdnXCCOjuNOqit5DA7ZGzaFGuI' \
			b'ujLF6T4wZ7gHaBZAG2myEoNFHxhxZnMfGHMfYywrszIVBw49lbqf260UY7J2Yuq1ExN7trx2Yuq1E7b4Sm403pS1E1OvnVQR5gDmJpwAbHrtxGDtxGDtxGDtJMYaAqxMcRpgOcM9AMPaiRmtnSQGC4Bh7cTktZOU+xhgee0kU3EowI6yo1gbwPZM604CY2KH' \
			b'xNcSYwEYCxljocZYyG6EsSAYCzXGyghzGAsTTjAWeozxY4JYAMQCIBYAsT7eEGVlmtMoy1nuQVkAysIIZZHFAmUBKAsZZTH3McpCRllm4KipnDrKNuMebDcLtk7AVtv9ySt8E9i6GmxddiOwdU08wrkEWxlhDmzdhBOwdRlsXQZbB7B1AFsHsPXxhmAr05wG' \
			b'W85yD9g6gK0bgS2yWICtA9i6DLaY+xhsXQZbZuA4sB1l73EPthsFGyNF1n9LsMkrfCPYJFgGGxd/ckOwSWQcjJ/BVkWYAVsZNkcKuEWw8WMEm5CAbA0+RPlAhAHYqjQnwVZkuRtskrIDNxXYEosZbEIfgkawpdxHYJOYAFvBwHFgW9yG5F5HcA2oEx2BrXUE' \
			b'FjoCm3UEttYRcPEnN0Kd6AgsdARiMWVwG0Sbw56acIK9rCPgx4Q96AiihZaFjiDHG2JPfLnkU5xJ/OVs9+APSgI7UhIkNgv8QUlgs5Ig5T7GX1YSFEwch7/FbUzu8XcN+NOCv1odIK/wTfirtQG2cCP8iSrAQhVgoaOz0NFV0ebwpyec4C8rBGzW0VnoAyz0' \
			b'ARb6gBxviL9BstPwy7nugR8UAXakCEhcFvDTgJ/O8Iu5j+GXdQAFD8fBb3ETlHv4XQP8xJzS1uaUFuaUNptT2tqckgs+uRH8xJzSwpySbwbBzCDaHPymnMAvG1XKr85E+MGm0sKm0sKmMscbwm+Q7DT8cq574AfLSjuyrExcFvCDZaXNlpUp9zH8smVlwcNx' \
			b'8Lu3ULkL8BOtnK21chZaOZu1crbWynGpJzeCn6jkLFRyfDMGt0G0OfjZCSfwy4o5fkzwg17OQi9noZfL8YbwGyQ7Db+c6x74QTtnR9q5xGUBP2jnbNbOpdzH8MvauYKH4+DXLQq/0aEACyKQJI+k7fPGIW/g77hOqr1qLfaq5Q3Oqt7hrNrsRpvWZI+zEnMe' \
			b'hqL8HJlp4g+2VTHndq+1E052r7U9FBU0eIolTH5JzoIm0GFi9mX84b62QfLTW9ty7rshKYk7MFZBMnGbISkkImja5BZzH29ya3tIFjwcBUl9HeYpa+sU9WngUUu/qOt+UaNf1Llf1HW/yMet2OhG1ioB8eUacDMGN52j6fmusQybI7G5dO4ade4aNbpGja5R' \
			b'o2vM8YYG03Wy7S6lX5HxHrNp9I561DsmRjMUo42Yzr1jDDNhNp17x4KN46C4uAnL2nB4CiC00inaulO06BRt7hRt3SnaNrvR4FQ6Rb4G3Hhwih6xijY3OG0nnAxOc49os02LRU9o0RNa9IQ53nBwOkh2enCac90zOEVPaEc9YeKyGJyiJ7S5J0y5jwenuScs' \
			b'eDgOfvsNXHyNQHUPwtscmYq9i6rtXRTsXTxsynwcnGaTFz4/ppVg5Ly0qKPxqVi9KFi9yA8Lmyb+vjCiwc0OTsOEk8Fptn1R2fZFwfZFwfZFwfYlxxsOSgfJTg9Kc657BqUwf1Ej85fEZTEohfmLyuYvKffxoDSbvxQ8HAfFxc1f7kG4PAidqOZdrZp3UM27' \
			b'rJp3tWqeyzi5IfwkslwDbnxw31bgV0WbgV8ZNkcKuEX4uaygd1DQOyjoHRT0Od4AfsNkJ+FX5Lobfg46ejfS0ScuM/wcdPQu6+hT7iP4uayjL3g4Dn6LG8TcVfiZCEG3ZhiKrtDVukIHXaHLukJX6wpd4UYwFF2hg67QQVfooCusos3BUE84gWHWFbqsK3TQ' \
			b'FTroCh10hTneEIaDZKdhmHNFWWhkPgVGaAzdSGOYeC3ACI2hyxrDRMMYjFljWHByHBgdTfyv64zRxQ8Y9TuAYiYAcughowkMCQiV8HM539YZo9d3vqiccjUW0iucMRoFcsc5o0TNvJC1i51lS4V2I8fZbi8hbfSdD1Hn319JEsfn3fOS9+CI2/ZY0VPdouI3' \
			b'ccStklMCFxPD/SKoZCp+nBjKyWzcq+WdKKlXG4pkOKbds0scr4yxhF1DGximJZN/LWjHgctHS2MpiWpsk77UgcsKtuYqqlyuJpHKTvfeRzSMSo6ynZBKP9k4Ug+t/AMq2k/49bbL98V2sSO/+ZDyJZvJOWF0O4TxGgRxQghVt4wg7ju/UnfLNYvzAuimBHBX' \
			b'z9xd4/DvUHnD1GkJkaNvvL2Qf3f0WsaDd+/QeTkpfwnxw7kUTjqPyw0SuXvZJYrUDjpqB535hJ95urjN+Ujnmy4084eBLNH40TP/8gP/6sNhDeBdmYoo2W7fzRy6sdDPHSCz9sBGj6i7Xfly9yK2jIixWaq6OTHbcAt2uJjpq4qZurKk2aWEbdcS5C6h86sR' \
			b'PD9vXXI54eO0FxFAP7IV2Xi9UxB5hHIJYTRXFUa9WLPXtQu3fPsE8aSFsBRAJUecLNUK7hHASwifvarwmeWEr7sXvusQPr9a4XNXFb7dmsTjB3zbe+m7DukLq5U+f6j0+ctON0ytst6r9tgndvsMQhZQsLHag82iFhS9gHXlcOVZhyRUH8p1kI5jt7zN/HLZ' \
			b'1dRs/BtynMHkQopm3W73CT92fi971yV7LeyL+HY12ZOE7pLsWSF5Tvba5uK2LQqua1FFXcaSwN6BBRWRq+tYQFGFNcvhZgOUx8XtStA1LskdLjnuLkjNtS25HSwtxPgtS8s1L+JOSgwGA/UPylbS429BetxxwiMLWgvKj2S/pwNj3prNtCBN/cQrsXDxubdC' \
			b'hRDxpOu+BZqy5KDBjxzKTpl+9gLDM+R191ls9327EhMe8DajrXuw4ZryDzatSI+5lx63+hEPUShErk56rPw8tuZS5IMmvIyNnGxqY/k5XGZcKRUiAe3+2pYaHtUudx6xypjDS9SQGLeWM98tynhPmYapMpSS8H1JXGLRwxy41nGV9Yy9WHHDElVYhVCXFX+O' \
			b'eezKwxXWF3bLOBNCVVSuIVAFpLo6tqLmm7lrqZ6qavSVmqVjhj6LV0asCWph7FZqgldzuGR5c+yWczUCpi56o0jtVgaKkYGOdx6pV+fkd7aRsweUHF5ATAUFoz9OTaz1xeg09NZ7nPZG74pC3V/+k6CmCCq/81HuAiOWgqq2aIk1Q9pAhQ1SfO52w398srao' \
			b'CZMTg0Q2uubEG460TV9EsSLG/EKFXYIKinXIn2ToZjJ09rA8XTP+4+XaCX/JV874VHYma5KyYe4ynJmiwMvYZOKPJ9XFGwl2/yakhENJwVa/gwmioDv+0vho8qvQ1B5HE7YfHkYZdjfkvXpEadfs+0ujuB1fB+Mupl7O0Gpvjn5qx3jbwTU6YQu/k3WTfKnm' \
			b'mh34Upfji+gdsXYUe7q5jOPJxMCL5wj7IoFNHdnUS3BabsQtuTXtPo45EE+j8HAVN05kKlkwbm6fcdfcrAPjdsh4sRM8/uJZkE3fB5SDl76I93H7Ygd3vWu73p5NBcO0yBbsQUHx9urdhdU1t+PsFpqp+bAoXnfrcsVLGTfqwLiflasDS6ASp52lcawA8epO' \
			b'4UK6htp/1vHkBtFUPE1oHIRYHOdVO5RZWHmZhWY1DgXWrrzA2mY1DgXWrbzAZOVsHQ6z4+26C4wXatbiUGBq5QVmmtU4FNhoyH2pApsdel2x2HxzdcfrtUMvbS6dHopvNHC/yfHr8eXYNvsdzjWaDXaI43XVYyKgPG91PnB0efLK9EodinM0/l93cfpmrQ7F' \
			b'OT+rWFVxhmatDsU5P+FYVXF2zVodinN+OrLGtRRWLa3aoXC7QuHOpQKVFI3PuZSliFFSxCxrFrZRKdlrHR3GW7wrnXXSbSMGfZwcReJzVOXkWIxiZU9xUUlUoKwDsLynUna28SpQpMBMBnVN4RDQjgJyJXFg35RORXHiHVXKtbza5fWr81fn/w8mAqWS'

	_PARSER_TOP             = 'expr_commas'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	_TEXGREEK = '(?:' + '|'.join (reversed (sorted (f'\\\\{g}' for g in AST.Var.GREEK))) + ')'
	_LETTER   = fr'[a-zA-Z]'
	_VARPY    = fr'{_LETTER}(?:\w|\\_)*'
	_VARTEX   = fr'(?:{_TEXGREEK}|\\partial|(?:(?:\\overline|\\bar|\\widetilde|\\tilde)\s*)?\\infty)'
	_VARTEX1  = fr'(?:(\d)|({_LETTER})|({_VARTEX}))'
	_VAR      = fr'(?:{_VARPY}|{_VARTEX})'

	_STR      = r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY   = '|'.join (reversed (sorted (AST.Func.PY)))
	_FUNCTEX  = '|'.join (reversed (sorted (AST.Func.TEX)))

	TOKENS    = OrderedDict ([ # order matters
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LETTER})'),
		('LOG',           r'log\b|\\log(?!{_LETTER})'),
		('FUNC',         fr'({_FUNCPY})\b|\\({_FUNCTEX})\b|\$({_LETTER}\w*)|\\operatorname\s*\{{\s*({_LETTER}(?:\w|\\_)*)\s*\}}'),
		('LIM',          fr'\\lim(?!{_LETTER})'),
		('SUM',          fr'\\sum(?!{_LETTER})'),
		('INT',          fr'\\int(?:\s*\\limits)?(?!{_LETTER})'),
		('LEFT',         fr'\\left(?!{_LETTER})'),
		('RIGHT',        fr'\\right(?!{_LETTER})'),
		('CDOT',         fr'\\cdot(?!{_LETTER})'),
		('TO',           fr'\\to(?!{_LETTER})'),
		('BEG_MAT',       r'\\begin\s*\{\s*matrix\s*\}'),
		('END_MAT',       r'\\end\s*\{\s*matrix\s*\}'),
		('BEG_BMAT',      r'\\begin\s*\{\s*bmatrix\s*\}'),
		('END_BMAT',      r'\\end\s*\{\s*bmatrix\s*\}'),
		('BEG_VMAT',      r'\\begin\s*\{\s*vmatrix\s*\}'),
		('END_VMAT',      r'\\end\s*\{\s*vmatrix\s*\}'),
		('BEG_PMAT',      r'\\begin\s*\{\s*pmatrix\s*\}'),
		('END_PMAT',      r'\\end\s*\{\s*pmatrix\s*\}'),
		('FRAC2',        fr'\\frac\s*{_VARTEX1}\s*{_VARTEX1}'),
		('FRAC1',        fr'\\frac\s*{_VARTEX1}'),
		('FRAC',          r'\\frac'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
		('VAR',          fr'(\\partial)\s?({_VAR})|{_VAR}'),
		('ATTR',         fr'\.(?:({_LETTER}\w*)|\\text\s*{{\s*({_LETTER}\w*)\s*}})'),
		('STR',          fr"(?<!\d|{_LETTER}|')({_STR})|\\text\s*\{{\s*({_STR})\s*\}}"),
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
	def expr_func_2     (self, SQRT, BRACKL, expr, BRACKR, expr_func_arg):      return _expr_func (1, 'sqrt', expr_func_arg, expr)
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
	def expr_frac_3     (self, FRAC2):                                          return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4     (self, expr_mat):                                       return expr_mat

	def expr_mat_1      (self, LEFT, BRACKL, BEG_MAT, expr_mat_rows, END_MAT, RIGHT, BRACKR):  return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
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

		if pos == 1 and rule == ('expr_func', ('FUNC', 'expr_func_arg')): # and _FUNC_name (self.stack [-1].sym) in AST.Func.NO_PARMS:
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

		return next (iter (rated)) [-1]

class sparser: # for single script
	Parser = Parser

if __name__ == '__main__':
	p = Parser ()
	a = p.parse ('\\frac1x')
	print (a)
