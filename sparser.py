# TODO: Fix! func (x).something. !!!
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
			b'eJztXW2P3DaS/jMHZAZQA81XUf5mJ96scbaTdZxgD4PAcBxnEVyc5Bxn9w4L//erqocUSVGt6Z7ume4ZD4YjiRRfqkr18KVYUp9dfPYfb3/98bPus2dPnn/7DZ2fPH9Jx6dPntHxm2/l+LcXkvTVl3T8y7fPP+fI479w2qOHL+j49cMXj58/5bJfPv/qxeNX' \
			b'n3/74ul/cd4XDz+PJxXPmgs9/vLVs4cvXzz5e4w8qmLfVbGvx5jUyq08onr+8/FLvvzm5Qsh8xEdnwux3wlFn3/17NnDVOZFLjNSyxcvnnz5V2bi4bOv6fjFo6ffPH34zV/p8vHzLzKBHHlUxb6rYplAruElmqcmuObHfxOByunrpyLeL5589+SLx5zni69e' \
			b'CgcPIwssoocvX47lOf74758zmy+/osOb1+/ffnj12/tXP/7wyx8fXr+npLf/+/v7V+9ef3j15rdfyuj73/41if6R4n/8+fvbsehPf/765tXr9//IN39Il7/++S5dfnj7frz+4f3rN//99kOKvvnz/S//VzQ1VkzZ0vXvRPevKfL6h5GS1x8+jIT8ngn+6fWb' \
			b'DyV9mbaRiH9m5n/5eUz9+dex3Ls/f3n187vfU/THn/+ZL3/6aWTx7T/KAnQxkvbjj7nWt/+Trserkf3f3r17XUX++Oz77uJsZWxn/HmHi14uupXls153Z6EbOkrQQzecpzRJGaMrrfjKy7+leH+e4ypHV1K3GnCw7jxGqQ6pyXFjXJ/i1jSKcWpMGxNWWsjV' \
			b'8s9xgzt8wVXGdNRPuWMiMtnujNuk+nxKoDr5ilOFErXGwVJhpc4nSVUiX9IVVbpynQndCq1avuAcPQ4WtNPVSgVplYhXRLA2/H8+JlVRZeMFp3FxEilzD8kjxrKhp9NXyb6JhSqln8bMukwhOqVhFoiPV2dKIufCKD9NQ3dTfCW5iJ8zjba4PtyMiWNkpcCK' \
			b'6c6IbOKRG7GdDcIGtR3ON99nDSUF2yabqnOtlDwPEjd0TLHWqM7oUtXo5pieUzxSTE7pkWJzSkCKSymkVYIjgwOLA+WNiUpqNA5UbBXrNlou+Uqlm+cxSrF0Q5J6+bc6sRjjJsdXomdK4UCiPz/Pl3QV5JHimQe+YMr7DpqmFctJjVhEpZwa04oEJcI3I54Y' \
			b'cYBcwIG04TzGCe6Sh+6IWkcxh86KvEj6Z7Z4nGbUCpZgfJguaSWlnRk/qmWMqjqhH1uhqIU2+w49Fl/oeEG8pyvAjpqnh0gd5AVpS98R8UQUNU76ICRpEbe1Xd9xF+ld533n+65fd71iHkgNqG+h7smHznN/R81TR8A6aofOrTunukCBHjNxSr0HVdwzy4Qs' \
			b'VvLAku+pQnkQJGbbUV1db7qeGnVd71mvoMSkVk53jo6UyXXOd65nNaeHQZgj/SduAhEaukD9OFGou0F9351Rvec0BDB/56LGciImiXHWfI4a5NGI6V5uXpxZST8jAfAJFYR4b5CYdzj5mNpLa7dEMh4c0aME9xrcg2ltI0s6siiCO00+BjBgQamVp9gPXVjf' \
			b'asW1fWQLKmuhcW4NzQ0hPjXRuDuL3mENrhXAF08avBsA08hzp2mLPSKlFzyxucNP4kIGnnMZbkZpA2THpAnYMEOmKZguUG7XBX9MyiwUV6fxQgO+vUivoFFGjTgoRWir2CHHYQf9sUPvzI1KfaLzd0a7zjxY7u1dxtBZjxGqj9wa0ZEr1WTilMWoq1cRe1En' \
			b'VXndedN52/l151XnQueGuyN54tJ+Ely6T4JLf/e5PHOYnWtMeRQGgxAXIXEwwZgwqHGJo7G20XdoaJBlGTF0BxghFoiRW82CqNgtpT3cYtq9gPqW0exvG81sv9GyqhakshGEVeZ06fUB9FpRj8mywor8J3arHkMHzAd7tx/Wo41Cw0ahYaPQvJDRIk1etfPJ' \
			b'WNBqHIYpgxXMONnHeIUp/63v7M9sWsTJGH08OhQ02fgofOnAj2wr4WU7qBlOgBoaGLDEDvaoj4rocIcBpU+mBw2Lg4ZxAT3FHZsc9qLfd9VicMF2Hw27zx1m8wxDQh9HiP6urWCMgO/KClAY/tjgI0Osgag87nr0YH4dR3mPVaPDqH/m4t6BRVlI2/m0XOT9' \
			b'UJK1OccaxbSTBkmbbnaFmVSOGkRNnEiZk949uuBJnjnlSZ7M7sytXjfyrFPHeaLBPNFgnkgnyaDX0BciNCbJRJFzqahZVqd5o8E2hIHln08hwiFgeDsanwHQssCQAU9UkwFk777VSkVeIYAoB8TMOonBxJ5Lo8virvFuieGCe967NITx0GEwdBgMHejdbWdP' \
			b'vHdnqprxjClEN2TRDVnZUlcclX7HHn1Vwl2ZdJUg34A0qsmm0R9oswCY3PURYWnUD3FIJ3CBWwdu3R3STBky7hJDrH7yuORINbv44F3qPPHgXXy0Ho/W49HSiRiFMntsG/uYsb9dtrgL5qoHV73wjFUtzCpEXD8xeDGvnJ94CJBJQOkQC4RbKIDhttFMZNwy' \
			b'mlk1huhgtY4eVmsZJtbdBZWmriU22g2RiFidkwX5IG1o7nxALhNkhJPAPMzyzIQOPAGMk8GB5cUsefaogURIuwdqaM30UJtrvqZW15b+qek1zYvX1D4Tw6TwPJnpYQsBmwiEbUpjoyp7n7C3AbsNsNcUu0yxPw8787Clkn3m2MeKF5s8T+V9ZCJL8eKO/QN5' \
			b'p7E3JBNxZhcvVy9uyOyVTf0tO5ZTP7vqxTO2Ew924mll2UmXXW/X3YrqXxFXKyuO2JSXa6E09prnythtmG47dmdV4hu7Clycs1L6wGncBPtdU1HrUTWxs2IvdnaTZWfaEH3Be3ZEX4vTsjjUstsrOw9zlVQDE+ijczrlsuK2TbnZ8ZlaDOxmTHko0FMR31yS' \
			b'y8qx1zsnc1FumK6pB1r17FNN/3zJntjMB7PK9FD79NhXbv09r15YpWZUySZtCoVCJexgZMvKJaourzQkFZO5Coa+jepW4wIzbixCog46UcN10kQBF6BXquToXMUg0pvVck0cCotL6mlnVJTS2TVlVlXXWV0ZrgzVSm0tVJftHWwLYTMIW0iSKvNElb1F2U23' \
			b'UuvAUtmgxGFU41qRqXDgQ9/qNCsYHwq9DvFvSb9D9ceartZBtN1FZQ9rUfgwqjyXNEKGYjWeKP9YFQmVq2h0n7MOiwgIUwyAiRoHDoREJKDFjAYHRLDsmaxuldERySsw0v3bmwcMbnrgdHYfZcy/SK68l4PG3ghWSqD4ZXzMYSNEfBwSG9vi4jIsKOnO+ViA' \
			b'QaJIjWCQbBkNcqdGgZSRY4EDfmgpLGGhzJcLMLG26f/V8hBQ1cDDQQWDfGsBBUJsBYPEQQaCqseD1F6DAykG9c9tVwhQ+gF3PqQqDxik9IjpbD/Kiwr3SLhBJMiYwMcSCR5I8BkJvkaCb5HgBQn1TEf5HBaR4GeCIMG3SPDLSChraJEw3lpCgm+QEDkokOBr' \
			b'JMT2WiT4jISx7S2RYO+RcINIYNUceCFVIkGiSI1IkGwZCXKnRoKUkWOBBK1yWEKCnguMBKm1RoK0vRkJVQ0NEvKtBSQIsRUSEgcZCUJFRkJqr0GCFAMScttbIsHtgoQjLin0TquKJYQsrSrWN7CyuBQtRtBiarQYoMVktJgaLSaHBjZGYGNq2JQFlmBjZoLA' \
			b'xtSwiasLaR9tGjRqQio1hVFZYwuj3NjmRYaOaDINmiJjBZqMoElKREDFlltAmQyosaotAeXvAXVqgHICKFcDCstzPiVAuRpQLocGUE4A5WpAlQWWAOVmggDKzQPKAVAOgHIAFEpNAVXW2AIqN7YAKAdANdarxFgBKAdAFSNUbLkFlMuAGrNtCaj+HlCnBihZ' \
			b'2eh6ZaOxstF5ZaPrlQ0/khQaQMkSR9dLnKrAEqD8TBBA+XlAYZkjX01AXhNSqSmgyhpbQOXGFgDlAahm5ZMYKwCFlY+UiICKLbeAyoufTMWWgAqHBlSx5XIDsMJrw/PIWt9+cBlZLJl6sWSwWDJ5sWTqxRLvYaUwBZcUliPJcJDPqeA0KbYAMTMXGGImr524' \
			b'yogwg+WTwQpKTiEWklw1yMo6h7kFVdHiZpzxbVIE06yrEncZZwbrKikBnMU8Lc5MXlplKuZw5u0Dsea0cBsYbmkPcD/QqVMayPpxLFvYXrwR2OlDQU9PdiU5YWZPh5MTDHUNwyI02zoW9cmxGOaqMksY1DNBMKhnhzkhQYoJCLHVE0tNEZiqY/lLTrWw5Zla' \
			b'XsCiBhZ1g8XIZbsRarADxA9OAImMM4DM2z9ZCFNAMicERFEcT6ePeIXhAMPeSSHwDkwlDXBWbxcZbBeZvF1k6u0iln4KDcwcysuxhFlZZglmdiYIzOw8zLB9xCeDRk1IpaYwK2tsR7nc2AKyLJDV7CglxopRLgLL5lEuttyCKm8qZSq2nE0qdb8+OzVQicHD' \
			b'1AYPE8eubPAwtcGD/adSaKaQYvAwtcGjKrCEKDcTBFHzBg8Dg4eBwcPA4BFLTRFV1tgiKje2gCgYPExj8EiMFYiCwcNkg0dquUVUNnhkKrZF1E4eC6eEqKWl2a0HVS+g6mtQ9QBVn0HV16Dqc2hA1Quo+hpUZYElUPUzQUDVj6Diy4SpHpjqgakemBrLTWFV' \
			b'1tnCKje3AKsesOobWEXWClj1gFWfYRVbbmHVZ1hl4ndajqmdvCDu0XVD6BoEXbUPnUSRmtA11OgacmjQNXTxI7wlusoCS+gaZoKga8joGjK6BqBrALoGoGssN0VXWWeLrtzcAroGoGto0BVZK9A1AF1DRldsuUXXkNGVid8NXTt5Vtyj62bQxdAQ82yJLoki' \
			b'NaJLsmV0sdxTmKJLCuNb5hldVYEFdJX5coEep4guvozokubRpMGNqBQoMEFXVWeDrqK5zeiSWh24qNCVWMvoEtqQNaIrtdygS0oCXQXxu6Hr4N4a96b7Q8JMTPe2Nt1bmO5tNt3b2nTPck+hgZmY7i1M9xamewvTfVVsCWxzQcCWTfc2m+4tTPfR+cnCdJ/L' \
			b'TcEmqSz1VKYBXG5yAXCw3dvGdp/YKwAH273NtvvUcgu4bLsvGNgNcAf35rgH3CEBpwVwtZVeokhNgKuN9LYIDeDEQm9hobcagNMAXFlsCXB6Jgjgsp1efpcgAg5megszvYWZPpebAm5SbYu33OIC3mCft419PnFX4E0Db/kFjdRyi7dsmi/o3w1vB3f2uMfb' \
			b'IfEmrom2dk20cE202TXR1q6JLPEUGryJa6KFayKfDLKZSbElvJmZIHjLDoryux8Rb/BPtPBPtPBPzOWmeJtU2+Itt7iAN3gp2sZLMXFX4A1eijZ7KaaWW7xlL8WC/t3wdu8LctJ4k90xW++OWeyO2bw7ZuvdMRZ3Cg3eZGvMYmuMT8bgNCm2hDc7EwRveYOM' \
			b'LxPesD9msT9msT+Wy03xNqm2xVtucQFv2CWzzS5Z4q7AG3bJbN4lSy23eMu7ZAX9u+FtOCjemjfeDwY5H1+5/0SBx++oD/wwqne3At7dyq/0qvqdXhVyaF7ikrd6lXw9gLEnP/tkcJqUXHqbK8wEeZsrjNhT2ElT3KjgwoIe0GBi02X56Xtek+rbV71yy5sx' \
			b'KBU7MFRhMHGZMSjkIWt66Su23L70FUYMFvTvhEF9HY4gJzXsqdsPQC0jn65HPo2RT+eRT9cjH/v82hgavxCP8nLscTIGJ52L6eXBr8yXC6DdBECdBz+NwU9j8NMY/HK5qbdxXW2Y9TnOjS74HGP80834lxjM2IvuVzqPfzHPjM9xHv8KFnbD3sGdRU4KeLcd' \
			b'dVaGPVsPexbDns3Dnq2HPRtyaOabMuzxsceJ55sY86piS/PNMBNkvpnHPJu9RyzGOouxzmKsy+Wm881Jte18M7e4MN/EWGebsS5xV8w3MdbZPNalltv5Zh7rCvp3w9uyK4mvIafuUXeUyaZ4lqjas0TBs8RjrPPwkFLZuYQVP0g2CtxE618iVcixx4k56THf' \
			b'7HNYnG/2M0Hmm9nLRGUvEwUvEwUvEwUvk1xuOs+cVNvOM3OLC/NMOJqoxtEkcVfMM+FoorKjSWq5nWdmR5OC/t2wd3BHk3vUHRB1TvbEXb0n7rAn7vKeuKv3xFm4KUzxJoXl2OPEn5RbC96qYgt4K/PlAj1OEW8u74w77Iw77Iw77IznchO8Tatt8Fa0uBlv' \
			b'DpvjrtkcT9xlvDlsjru8OZ5abvDm8uZ4Qf9ueDu468mtw5uKmDOnjDvZJHf1JrnDJrnLm+Su3iRnCafQ4E42yR02yR02yR02yatiS7ibC4K7vEnu8ia5wya5wya5wyZ5LjfF3aTaFne5RchAo+E59GGn3DU75YnHAn3YKXd5pzy136Iv75QXXOyGPkeL9uv5' \
			b'2OUhv3RpNyBDzSBi4ZM4c9o/+8VLlupRPnZ5PR+6lG8zzX/Q5oofu4wauOGDl0TN5VoVDvQV1f76P6QarqBe3LFyWl90rhTn31+ffFw17KprajiYvs18XJVFciMfWGWZXeEjqxiv8iZqGq+mOtjv0rPZvb/ki+mBOXYv5zaoYtjQ0+35XV/VenAf4tu+Cp7Z' \
			b'Svk9VVDZS9XwMhVk+c2pobez3R8NuoqGW+U/4ue4rj682sN8TppkemNflDbz2ncdmjejdWrYX/OWPqSo+8N0fJdrnJnTuE2D7XBtU7gtFUzWO3vrGN3juSm/XHctc7rb9QVz+eT6sKe+4RsLRoaFq030eODYpHvU0znq6Zz5iB/6uTjaImJw3eBvoHvjhTRf' \
			b'h227uNuwflBS53C9XZpYbaWhsGW3RpQdUaHsvU7tp1PchLoZvVr59S56pffVK7WfaplDaNcmU+AmLbMno2l+2VPjatrGZcy+Gucbv4uV1xs1jycbV9A+s6/26cN0bEN/wL5tSfPurNaVGsfsH6afW9C4K2ib3VfbzIG0Ldxr2yG1zZ6ktrl9tW3TJt2u2jbc' \
			b'a9shte1Q5o7DapvfVtv8lZYIut793bi/sKRnS84UB9i6kl/dMAfVNVYxEgyfrr5S6Atli1uvlyrcZgW75Leq9tvA4l8L68OsjnX/1uEB4e4jfnj6XtkOr2zYPOj3WpZKJbdF2cDzZcoWuouj7cZfk6mDZHiFXXhz4maOazFrqMLxavstd2rj4kgqc42Wse1V' \
			b'5aTV5NosX1urBzF8LPU4hoqsu+ZnQGt1cTesLtzgltoi280HVBh3yZjEG6fdal5z5n6Yk8i/+GT7mUJreLVy38eUbg80gZFvdlOjn66G8HM9zWGInZv7o6oI9SGsFdSlsPWZnVJFXcynrC7hZNUldO64PcoGdbHyc8XakfR4vexkfuPkhSxWmO2UhB5GVAN5' \
			b'5H758cojbR4njwfxGbEUdnwk4smZFqRrCHVBiP2c0IR1P7K+o/GBzQ6X2hz2sSssosFMRbgWDefT7grOpXaxAOyxzt+sxdw4PZNyLU8STw9npyez3HNdy/OonoW6ck+z7Xzl4NKPoud56lpEH+StFWWCzNuY9eH7c7o+W8nr7ErehydSqW8UFzZ+p5PdyXvx' \
			b'mWTnJ/ijMchWelMRGpzyn2Q1RVb5kYbyLSQnnzso3xKSzfz0Hg/e0+EvK3f8R8I1sqORgrjYsaMwf2e5M+KbHu/ILoR4nAsV9hBUUKlt/qRBd0mD9Ji2atN17R9bPmfSpV351qOylzTtbNP6ehMFXiYPM3+8mC1ipLZjTEjptyUFb5ttTRDp5Ia/NImZvSs0' \
			b'hd1owhtw21EWXfFHF3yidOiW/tJUa8PdyeSIqZcPL4Wbo5/f+8JM9LqCsIVfNbpJvlR3zQF8qavxRWvphrWwC3u6u0rgGf8kiSfyS4XApo5s6oNw2s9za/wSxzys8zoHF/uEtpK5asG4OT7jrrvZAMbtlPHiTeT4M1W9vHS8hRy8jEX8KrErXiKuXxyu3xJm' \
			b'gPFgv54R1HpJWEN3nMAfkDBb5YV43dH1ig0NNxrAuL9Ur7aUQKlOm6WxqwKx7aUIvYpHXGwfeLmCYrxQmc9i1UxbdYDM+hOXWd+dTIDAwokLLHQnEyCw4cQFJmau0whYHa9PW2BsczmVAIGpExeY6U4mQGDNlPtKArt06rWn2Hy3f2CT6zSJ9OWq9UF8zcT9' \
			b'Juevu8sxdMsBn9a5NNs2gS2luxSAPI+6HthZnmxkPtEAcTbz/9MWp+9ONUCcl68qTkqcfXeqAeK8fMFxUuIculMNEGcoNnBZDkjlzxiYKFTIhtjkLEPcBRu3uhyMjfzKOW95hk78vHg3nQrx1zXXIhJkUvIDX+NjIVGymdrwC3BDkFdFLPYv5MXQNqftioCM' \
			b'psnIT4czu64MKuoPv4alnOwveZr+fX/+/wuNjAU='

	_PARSER_TOP             = 'expr_commas'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	_TEXGREEK    = '(?:' + '|'.join (reversed (sorted (f'\\\\{g}' for g in AST.Var.GREEK))) + ')'
	_LETTER      = fr'[a-zA-Z]'
	_VARPY       = fr'{_LETTER}(?:\w|\\_)*'
	_VARTEX      = fr'(?:{_TEXGREEK}|\\partial|(?:(?:\\overline|\\bar|\\widetilde|\\tilde)\s*)?\\infty)'
	_VARTEX1     = fr'(?:(\d)|({_LETTER})|({_VARTEX}))'
	_VAR         = fr'(?:{_VARPY}|{_VARTEX})'

	_STR         =  r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY      = '|'.join (reversed (sorted (AST.Func.PY)))
	_FUNCTEX     = '|'.join (reversed (sorted (AST.Func.TEX)))

	TOKENS       = OrderedDict ([ # order matters
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
		('BEG_MATRIX',    r'\\begin\s*\{\s*matrix\s*\}'),
		('END_MATRIX',    r'\\end\s*\{\s*matrix\s*\}'),
		('BEG_BMATRIX',   r'\\begin\s*\{\s*bmatrix\s*\}'),
		('END_BMATRIX',   r'\\end\s*\{\s*bmatrix\s*\}'),
		('BEG_VMATRIX',   r'\\begin\s*\{\s*vmatrix\s*\}'),
		('END_VMATRIX',   r'\\end\s*\{\s*vmatrix\s*\}'),
		('BEG_PMATRIX',   r'\\begin\s*\{\s*pmatrix\s*\}'),
		('END_PMATRIX',   r'\\end\s*\{\s*pmatrix\s*\}'),
		('FRAC2',        fr'\\frac\s*{_VARTEX1}\s*{_VARTEX1}'),
		('FRAC1',        fr'\\frac\s*{_VARTEX1}'),
		('FRAC',          r'\\frac'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
		('VAR',          fr'(\\partial)\s?({_VAR})|{_VAR}'),
		('ATTR',         fr'\.(?:({_LETTER}\w*)|\\text\s*{{\s*({_LETTER}\w*)\s*}})'),
		('STR',          fr"(?<!\d|{_LETTER}|['}}])({_STR})|\\text\s*\{{\s*({_STR})\s*\}}"),
		# ('PRIMES',        r"'+|(?:_prime)+"),
		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
		('CARET1',       fr'\^{_VARTEX1}'),
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
	def expr_frac_3     (self, FRAC2):                                          return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4     (self, expr_mat):                                       return expr_mat

	def expr_mat_1      (self, LEFT, BRACKETL, BEG_MATRIX, expr_mat_rows, END_MATRIX, RIGHT, BRACKETR):  return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_2      (self, BEG_MATRIX, expr_mat_rows, END_MATRIX):                                   return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_3      (self, BEG_BMATRIX, expr_mat_rows, END_BMATRIX):                                 return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_4      (self, BEG_VMATRIX, expr_mat_rows, END_VMATRIX):                                 return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_5      (self, BEG_PMATRIX, expr_mat_rows, END_PMATRIX):                                 return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_6      (self, expr_curly):                                                              return expr_curly
	def expr_mat_rows_1 (self, expr_mat_row, DBLSLASH):                         return expr_mat_row
	def expr_mat_rows_2 (self, expr_mat_row):                                   return expr_mat_row
	def expr_mat_rows_3 (self):                                                 return ()
	def expr_mat_row_1  (self, expr_mat_row, DBLSLASH, expr_mat_col):           return expr_mat_row + (expr_mat_col,)
	def expr_mat_row_2  (self, expr_mat_col):                                   return (expr_mat_col,)
	def expr_mat_col_1  (self, expr_mat_col, AMP, expr):                        return expr_mat_col + (expr,)
	def expr_mat_col_2  (self, expr):                                           return (expr,)

	def expr_curly_1    (self, CURLYL, expr_commas, CURLYR):                    return _expr_curly (expr_commas)
	def expr_curly_2    (self, expr_bracket):                                   return expr_bracket

	def expr_bracket_1  (self, LEFT, BRACKETL, expr_commas, RIGHT, BRACKETR):   return AST ('[', expr_commas.commas if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_2  (self, BRACKETL, expr_commas, BRACKETR):                return AST ('[', expr_commas.commas if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_3  (self, expr_term):                                      return expr_term

	def expr_term_1     (self, STR):                                            return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_2     (self, SUB):                                            return AST ('@', '_') # for last expression variable
	def expr_term_3     (self, expr_num):                                       return expr_num
	def expr_term_4     (self, expr_var):                                       return expr_var

	def expr_num        (self, NUM):                                            return AST ('#', NUM.text) if NUM.grp [0] or NUM.grp [2] else AST ('#', NUM.grp [1])

	def expr_var        (self, VAR):
		return AST ('@', \
				'partial' + AST.Var.TEX2PY.get (VAR.grp [1], VAR.grp [1].replace ('\\_', '_')) \
				if VAR.grp [0] else \
				AST.Var.TEX2PY.get (VAR.text.replace (' ', ''), VAR.text.replace ('\\_', '_')))

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
		'RIGHT'   : ' \\right',
		'COMMA'   : ',',
		'PARENL'  : '(',
		'PARENR'  : ')',
		'CURLYR'  : '}',
		'BRACKETR': ']',
		'BAR'     : '|',
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

			return self._insert_symbol ('PARENR' if self.stack [idx].sym == 'PARENL' else 'BRACKETR')

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
