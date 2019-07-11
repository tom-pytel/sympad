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
			b'eJztXfuP3DaS/mcOyAygBiS+5d9sx5s1zna8thPcYRAYjuMsgouTnO3s3uGw//tV1UeKpKR+TvdMd89gNHpQfFQV6yNFVpF9cfXVv3347aevmq8ePfnm7eOHr5+8pvvnT198x9enL97Q+dnT53R+/Z2c//ZKgr79hs5/+e7FY3548hcOe/TwFZ1fPnz15MUz' \
			b'TvvNi29fPXn7+LtXz/6T4756+DheunhVsdTnD9/Eu0f59vt8+xK3khPn/IjS/jvfvH7zSgh7ROcXQt73QsPjb58/f5hSvEopBur45tXTb/7KmT58/pLOXz969vrZw9d/pdsnL76OBPHdo3z7fb59mW+TxDiHNyicipC3fxMByuXlMxHn10+/f/r1E47z9bdv' \
			b'hP6HkQEWycM3b4b0/PzkPx4zky9fPX0uRbz5lk7v33368OXt75/e/vTjr5+/vPtEQR/+549Pbz+++/L2/e+/lo+ffv/n6PFzev785x8fhqQ///nb+7fvPv09v/wx3f7xz18+f/j8vn78o36kp39kOn7782O6/fLh03D/46d37//rw5f0+P7PT7/+b0HcQApF' \
			b'G3InTn9LD+9+HGh/9+XLUNofmcWf373/UnKUuRmIKMj89Zch9JffhnQf//z17S8fB/5++uUf+fbnnwcWP/y9TEA3A2k//ZRz/fDf6T7ficTiwyCL3z9+fFc9fP7qh+bqYqH7RofLBje93DQLw1fVNRd907UNheiWbi5TKMJywEIpvvPyb1SzCJf5uXhcSEGq' \
			b'xcn4y/hIecid4wI5v44LVEjGoQjLAQvl5U7++VnjDd/QtYvhl3hYqBiISJbyayU/nwIoT4nCwUJK1+FkSBiduhwFqTKQb+mOcl24xlAOKNbyDccIOJn+Mj4uOhGz0iRIyl4Z/r8cgqrHzsYbDuPkJFNmFxHwxMIhmkIV7CdPugoJkydbhhCdogpETOfj3YWS' \
			b'h0thVGqaCk7PC4lF/FzoWJZNL2Pg8LDowArlaBpiTSrDNhZsUNlRUrPvWU1JwzaJNoq16KQ+SNxQso7l6BqtS12jl0N4DvEIMTkkIMTmkB4hLoWQWoncAk66S0qqQ9RS7XHSrLYoX3u55TuXXl7GR3pKLyQoyL8xicX4bPPzQvSsUziR6C8v8y3d9ahSwLiX' \
			b'O6Y9NNA1pQT/AxyRLYcirAxQIn49QIryVYBij9MiyopvlZTDQqPgttFIQ4xAYtw8kLgS55yvYFIraZwKSaYAPHUpHb1XKYhv+Y50UFAUU+rGAJ0kTVtoj2mTEupBkKwQEQQEcq6+iIL4qOqAPpdC+aHFo1ZQpRsdb0jQ6Q4o77gJUX1jUSEdN0toKUhf7SW1' \
			b'1lfUCvuGlI+kSK+JMN34vgktt4GUETVNpA++CU3fONs41zjf+LbxVFlKuCSkUHhoXM+aYqjBolTcOFGpDJ3QNz3ViCHVblidSQFJd3uWC+tF33jKMHCnwC1hQ3k1nmigQm3jHasJaoAEbFVj6UyRCJSusZ5lzLhTDTUCBMjeNr1ret/0ofGq6bmv4W6m+6G5' \
			b'oOsl9U7M7aXATS7EMomBEcqPGnFIAHQNRLtqgm2Ca4Jugjlb0YQoGwUpKC9CubowIo8L4pIvEFyI70REF87i4mKol5xOjH0HzqjeIAUFKYB5ZSJrKrIqinPc/PRgxIBiI7UaSFHDWWir8ZE9QNhAE20LJPcu1qJo4h1p23qIwnaAKCTSR1RrwFeLNtAHFn3r' \
			b'3DrFV/ydemfqh+og9i8+1wEAeQy0QXl0n2nru6ans256cwwUmhZNcep7FBTcizQLWqUHih17bA662KjHLgxtukULz4VLfoKMM9W9i9geenN38Hbh0fP5yLsW/blWjjp+Guru+lkpZGUlS6capxtnGtc2rmtsaGx/rvVCPJs7yLO9gzy7u8bzhcUoQuEbrEOH' \
			b'06Mh6uMIIyK/72MflTqpthsGpwqjUnW+HRJxpZjZEL9W0RmHOBIPsc0O6KrDMPxynOpspCCDa2LoLFgRrT1xHsIZ8OCk3ThR2t2p0s6TXtKgKUE0zxixKh0/3S6AbiNqMxpHGamP0aRfwCPmWPY3/RiGCR2FCR2FCR3FHYIS6fKkBl+0Ac3aoqfUGLoN4xp0' \
			b'mRjdnFvHadJYVnrM26eng75rF6tEuoEjmWASK4pQ1R8RVfTph4+e/jiqkOjRe4Vyb9JMjcIEjcJcDNqZM/6qveK5JXVXJliueApNYQrtzjB9gS7Hxx7In/MgTebM1PUmuq5G86w8dyYdu4YAHd46DPRcG78xHFpIi2+OCxvNOwZpUQcWHyd9n4bLbAGnitBx' \
			b'XKkwoKTLWRtuZZSsMEo+X13kob9ULHGkJ5+kXsLGdugwE8qPGo86fq7rkzDoXvGQQp/CkELGEvosZjV4rKPiqERjVKIxKqFLrZ5tbHf68SsZpnCqLmqgUWnUomEN1DC88aXvUF4vcW6f/x5NiwHmNHikHDWa8Ls2vdtFziGOKBU86TYJRcd+TaFD4w70nIVy' \
			b'xb30GXc8FtVsUc1W+g3+rpBLrG1ixpxIL8LUTfpPphTNm0HzZmQWXh6l/TJHM3rmplGaYrChQSLlaNJXJXBqAE156yI209dkiJ8SBEtwbcG1PVstlo7pfNljFZWqlDOVYKNS2NQkQylsrHaHaneodroQw1B4B88QFyP605yNvmLuPLjzwjtmZKJVTd5VU73M' \
			b'M8cnXgJkE5A6xAThhAXRnyrtRM6J0s4q00e/zDY6ZrbS1bTNFeVCDZHhoqXp6Yo8efLI8yySAsuGac5UWWaHeKGeaMR4SS03ZCHKjZgiftmNW0dvO4hIqKWSWhYG00AUMAlMAxPBX+tMCc9psRcwu0WzTzT7n7HrGbsTsRMPe/Ox8xy7p/HcPPtJs88tO9wy' \
			b'98w5O7zwFAZ9JXc8HOWxKH8rsO8aVwbbt9n0HRxJSJYyyHIeJytOAq9j8s1CVmQ0C2qhF16WRjWywogUYWF4PQrFpnpY8DoVYm/BKw6IzoXnnCiMl9K4uISGklpeKMDLLThXXpLA2cqqDV6w0PIbDuFlR5SBcSiA1+3w6hxZNsILQXg9Cl09LzaQBRUU1suK' \
			b'h4XnBQsUj5c68RItyonJ5UVWvGCCSZQVIw1Wp1DsnlPTMyc2soRjYfmRV3BQmHVY1CRLUSipt1hNQUFellNRFPonpVgEFgr92/YHHmmxylnRXifQcLHnA4Iob6I/N4dc8QwPqkx2l2VDC/vA80yV01RBhIbN/36QZlfKn1N1l7S9LRTexu4ZgM3KP4B6gEDB' \
			b'xSo4yMgsD9RST58xogQmPiFFxRkzXvZQQqYQUYJPktRS6NB7aTNWQcjOwChKfRZOuoCU1MoIWj7Ci96xsyd7PbIz4AA3yp8dTti7pIIeM9OylJYAjVU8Yo1vC7h5eenF9DiGHkdFggKAKArHejCWsXMyXmfBjQV3BxoADbL+DoQCp0wQCZYJFHTWiK3yi+jN' \
			b'UpjAlmMFvxK9wk8F4MRkDWMnn6IJyImCDGcLSPOLIKsqFxnfmeQC6M3/+fYBt1SkI3S1/5KlPIK8PvZ366HnbgpxJdz05iibQRhbXARl+0TYpuhaiygn6yF7OReIkkeEJkDV/Ze8GeHICY7qjgwFxGLW48jNHIIjN+nohILlfV2VQ0JOzK+ETY60CjRuAprI' \
			b'UQaN0JO7vlTyFDEu42Qou8JJZx5wi0ba80BAbXq6mn/J+OkeL7eLF34peAk1XgLwEjJeQo2XMMVLELyEGi8hHxvgJcwcgpcwxUtYjZcyh4SXmF+FlyHSKryECV4iRwVeQo2XWPIULyHjZSh7Q7zYe7zcLl54SCyfa3wu8CKPCI14kWgZL/KmxoukkXOBFxQQ' \
			b'i1mLlzJ2TuZR3AgvQsFyvFQ5RLyk/Eq85Egr8KImo6rEUcaL0JPxkkqe4EWSAS+57A3x4rbFy60OhXiqdMfR0CocrRoNdTcwIlqLKctyZ0zZGlMYBPElYcrWmLL5mIDLCrhsDa4ywXpw2ZlDwGVrcMVBkFCBkjWKZnfAyNwIbGWOCWwx/wpsQ6QVoyDJX4On' \
			b'GnOR0QJzVjCnCthFGqawsxl2mYrNYOfvYXcCsPPYV0bOJew8YOcz7HwNO5+PCey8wM7XsCsTrIednzkEdn4edh6ww+Y2cgkp1Rh2ZY4JdjH/CnZDpFWw84Cdn8AuMlrAzgN2PsPOD5uzjGDnM+wyFZvBLtzD7gRgF2SLq17OJeww4lJ5xKXqERcSxuRj2MnQ' \
			b'S9VDryrBetiFmUNgF+Zhh+GXwg5SchlSjWFX5phgF/OvYDdEWgW7ANhNRmSJ0QJ2GJFJigi7SMMUdnlQVlCxGez6A8AOFjS4QNwQ+Nxy/PnzgiBvlSaDOF0P4jQGcToP4nQ9iEPCmHwEQUksZxIyp6Fbuag62VoglrFzMt+iBACRM4441BjWCeZRPquPJOqn' \
			b'UCzz7DMaUyElGnPZK9AoAoqMVWhM3GY0aoz3JAXQGONM0ajzkK+gYgaNvnsgc1NTUHZi940GZ5jCrolOfWT9oim7RrEoJ2yusCzfCEbtvnDK6sRSH9mkOWTGWibG4ohbU+PW5GOMW1ZiI9A1Ve9ZpVkPWjNzCGjNbO8ZDdvCIYrWIaUaQzZlx5UhMaPR2/cp' \
			b'xVKzd3y/CsAGADYTAEfOp8ZwSaKkTgXFiDiDYpNRPIhkjGLmi9DLFwKvBna7ffWox4bZM/uWlY1CBZG1tU3D2qaztU3X1jYkjMnHgIzp5VwCskyzHpBu5hBAunlAwvqm46apmCNN/I0AWeaYOtCYf9WBDpFW4c8BfxODXGK06EBhkJMUsQONNEyhl21yBRWb' \
			b'fc526n4YeQLQ8+xrx9CrZ280Zm90nr3R9ewNEsbk429Ymb3R9exNlWA97vzMIbibn73RmL3RmL3BvsEp1Rh3ZY4JdzH/CndDpFW4w+yNnszeJEYL3GH2RufZm0TDFHd59qagYkPcbe08cmy4WzGCPCvo8QbzAr3aa0seEZqg19fQ6/MxgV4v0Otr6JUJ1kOv' \
			b'nzkEev0APb5NyOuBvLjhN9y2crox+Mo8E/hiCRX4huBV4OsBvn4CvshqAb4e4MuuW4mGKfj6DL5MxXajxq0dUu4xeCsY5JkxVkI5FxiUR4RGDEq0jEEkjMlHGJTE+DWAjMEqwVoMmrmDMSh5A4N8GzEoRCCOxgvWlyHdCINVnhGDqYQSgznSCgwaWOqFqwqD' \
			b'idWMQaHSIgUwmGiYYFBSAoMFFdthcGsnl3sM3g4GlfxGivyORYVBBQyqjEFVY1DlY4JBJRhUNQbLBOsxqGYOwaDKGFQZgwoYVMCgAgaHdGMMlnkmDMYSKgwOkVZhUAGDaoLByGqBQQUMqozBSMMUg9lxuaBiOwwewnHm3qZxSDBq+Y2fXs4lGGHTMNmmYWqb' \
			b'BhLG5GMwik3DwKZh8IM4JkKyTLYeknrmEEhmmwbfJkjCpmFg0zCwaeR0Y0hKKIs/vk+wjKVUsBwyWQVLGDXMxKiR2C1gCaOGyUaNRMMUltmoUVCxHSwP4VhzD8tDwtLgl43kXMLSAJbZZGFqkwUSxuRjWIq9wsBewRetcVF1svWwNDOHwDJbLfg2wRJGCwOj' \
			b'hYHRIqcbw3KUbUJlLKRC5RBpFSphqTATS0XitkAlDBXGZFRGGqaozEaKgortUHkIv5t7VB4SlRa/LybnEpUwJJrscWpqj1MkjMnHqBSPUwOPU74wKi1QWSZbj0o7cwgqs98p3yZUwu3UwO3UwO00pxujcpRtQmUspELlEGkVKuF8aibOp4nbApVwPi18vhMN' \
			b'U1Rm59OCiu1Qee+Wc2qodI0YB+RcohLWRJOtiaa2JiJhTD5GpZgSDUyJBkNKuag62XpUuplDUJkNiibbNQzsiQb2RAN7Yk43RuUo24TKWEiFyiHSKlTCqmgmVsXEbYFKWBVNtiomGqaozFbFgoqtUKnavaPSHxKYOu5TcQ/PK64VXoQu59JxtYXjal6rruq1' \
			b'6qo4Jo6rsladzj0Qys8av2KpVZ1yvQdrO3OIB2veVYJveedvXuLI7izsyIq161JkJCAU6ce+rKPskztrLKxyZx0irXJnbQWparKKPXFduLO2cGdtB6QmGqburG12Z81UbIfUAznhHF0XGs4MprIFPcO07kUVelGVe1FV96K8b7aLx8QnRyO9nD0uGmFa5WRq' \
			b'k460jJ2T+RYlRJgWfuboSBU6UoWONKcbw7POti/WMsZyKoQO2axCKPpSNelLE8MFQtGXqtyXxjgzCM19aUHFdgg9hKPO0cHznLDJspMu1NZdqEUXanMXausu1BbHGJuSWM4eF95KC/1nlWwtMG07czAwbe4/bTsA06LftOg3LfrNnG4EzHG2EZWpkBKVOdIK' \
			b'VFr0m3bSbyZuMyot+k2b+81EwwSVNvebBRXboXK9G0+oganvsXkE2GRCxaunq716Onj1eHgUsK5wvWfHHt4VjPfDkIT8a84zGzKJb08H3x75DXmNi4rJYtnrt8foZw7ZHiN7+HTZw6eDh08HD58OHj453XjDjFG2ac+MWEi1Z8YQvAKhHZx8uomTT+I2I7SD' \
			b'k0+XnXwSDROEdtnJp6BiO4QewsnnHpuH7DcVC477zdrTwMLTwGZPA1t7GiBhTD7uN8XTwMLTgC/YglL6zTLZ+n5TzRzSb2Z/A5v9DSz8DSz8DSz8DXK6cb85yjb1m7GQqt8cIq3qN+FyYCcuB4nbot+Ey4HNLgeJhmm/mV0OCiq2Q+Uh3H5OHpUqItMcMzoN' \
			b'i47RWds4LWycNts4bW3jRMKYfIxOsXFa2DgtbJwWNs4q2Xp0mplD0JltnDbbOC1snBY2TgsbZ043Ruco24TOWEiFziES6QdfFEiYwygsnXZi6Uw8FxiFpdNmS2eiZIrRbOksaNkOo665OuRWugfZR9cugY6agcwcVBJM5uCRoFHBgSR/y1vpHnYbXdkYcKq1' \
			b'19hKN2roku10SYIbaV27vz2czY1t40zC22krZ96cjz/8kwryfqv8G5SjrZ3DLrpYjG4OtrVzJ5t97VUvV+skS3GHLZ7RBebJutQFjnU0bNkyun3sM44d99pjaSXDvKryoHjJzuM7qWepmjOj7f3tPJ7Gz3FroeurKH93XbPpZInOqqmfbT6pU1f2AQlZuu/+' \
			b'et23299m+Pbm98N3S7TzQJo5o5VxBuiwe+KzMG50X3yW5OZ741NmB/2E3FQBMSjblw6y+zFv0OAO9E15qr/PID8t0e9JH7GxiJOOZrcPTe6KlukmtZTOP6DMZB/3rrk6mIb2m49zqNRWFzu8HLqNZJ2ke/411M3aydvTR54/2WWg04kfft+kLVQO/pshKDBs' \
			b'2j6qA2qe518G3Fj5uhkFXLO90M5KSO/44/p0lZHthG5HheRp4q5WymAOoJiBnWj1tIF07TYKqvegoPr6U0DtEg3dVTuXzaAuayr9UWmo22QqdDft5ML0VEN30043mdNcOLW0+exEOltrqNmDhprra2ipneYAnfgq7bwDmllqZSc077NDX6GVO2ik3YNG2v1q' \
			b'pL3XyMNqpD1qjXR70MjldtSdNNLda+RhNdIdtUb6Aw583LZjn6SHyU5/k2OeYx/rtDw+UTuPd/IYp7vhcc5mehi20MOwo4mbHQpLZ5K1erhK/1Z5b+3ByC2WRrd3PeRKMrhc184tWUUFjG4cGyvhcuVb87uT1zN182+EMtmzE5G6fUAIlXnI/l4Zb0QZHZTR' \
			b'7UEZ3Qkqo/itrVNGEtDVbXv9HGz2W+1gleHvm1Nx7TnEDHcnvwK8rTsPUXt1y0p0SPPJxsrTnYbiHMossoXCqFtXmEPb3OaURjfTHxKvFEjdigJJsZvrD0ffpwo5tUqD2A2u/unudb/YTe3i1Z1viwo94st9OzTrHqDpQ0iJzph7nbniOatj77x4/Ya5VaXp' \
			b'H/CKQnas53qyDxZBFMjeK9CV1MqxK5BthMyjUyDXXHW8+InkyKN2Jd9JXlaxkiA21xoSfqEXogN+dX1LHU/qVzoRVJq45e5SR+J6XrT4stZgtVT9nBRFFiHJYpdpkX7D2ZDrzHasxIsbyZSH/zw/4XeHQPDbz0lcY9ZhuZ5zplRJ1cxCP9TWllW1QWN3kAqq' \
			b'Kidcs3Ha5jNo79WBulDUzpiW64IEfCWy5TXxrZTeMaJI6giHVG0nbqmZB5YUQY9CLxaydZCS3Vi0LFMQd1vOkJfWBPH/5sUq8Jnl3BdqWRLqDPOfRI0bLMTI8tNN5dpOYpmTFwsvBzMOO/mkZZFY9sg/58EembqRX9TT0RRZ/gesjuBtjPg9CVyMaSFHEQui' \
			b'rMcR+sx+6aN0m/8JAXa/BNCHxeZ/QoBbS4Brt6PBN3N/PBU9/8YLHXG75M6tIYUqcBk1vGpjliLCPX9thZk/ni8YhdgippAWNicNa5G3JpAawaV/6QtwaQyhsd+WRqyX3o5SrLDKi4u5leiaLY/0HbvZMfoUZVa7uC8h03rj7PIib/5+x80hD/Da3SKvurmp' \
			b'A7yqnXmlvn4Zu2mJ/mYsm2bHg4dl8+/61UnBus6sm71yH+YlYPpVUrANDv58svs5plnNZQ5hmKMShm9u6YAw7Iwwit00IBWNHxfaRDbSffJeGCrvgjHa+WJWYHEXTmxjMRKeXYUpHinc6kHfv2I03CAuRO6OSf94hul2DgjDb6J/G0qlVLv1Etpa0UwzOujj' \
			b'AWfcbH7wIBTJePi5KqKdK7E+IMdwOnLsm+M7IMT+ZITIMyNHd2D03p6OEDE9elwHhNidjhBVc3wHhKhOR4i2Ob4DQpwbOuwmxHWfhnsSZWj2cvCM/jiIdetauUKkcwOQ2/jm3lq2PAG/7sDWdpvEXHt0OyWDjI9lXLO9jH1z9AdEPDeOOQ0Rh+boD4h4o9HR' \
			b'UYq4b47+gIg3Gjgdo4jZ9nnsB0S80bDqmOeY2Nh5Ggesomy3ZbJh0OAdbOQR7TZvK8IOPy0H8bRyDNbZj8SxbBFK3ypcV1JRkDeJiq1wLtrZB0O6w0wEL3DmSm0bLNBg+5hhO7xUQYBKyJrToqqpOsTG3Mb18RZrQBPFfj5214z+ETtMYnNVSwrVTP4dPhh4' \
			b'eU3nepmRJSn+cPn/J7V8ng=='

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
		('FUNC',         fr'({_FUNCPY})\b|\\({_FUNCTEX})\b|\$({_LETTER}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}}'),
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

	def expr            (self, expr_pwise):                      	              return expr_pwise

	def expr_pwise_1    (self, BEG_CASES, expr_pwises, END_CASES):              return AST ('pwise', expr_pwises)
	def expr_pwise_2    (self, expr_eq):                                        return expr_eq
	def expr_pwises_1   (self, expr_pwisesp, DBLSLASH):                         return expr_pwisesp
	def expr_pwises_2   (self, expr_pwisesp):                                   return expr_pwisesp
	def expr_pwisesp_1  (self, expr_pwisesp, DBLSLASH, expr_pwisesc):           return expr_pwisesp + (expr_pwisesc,)
	def expr_pwisesp_2  (self, expr_pwisesc):                                   return (expr_pwisesc,)
	def expr_pwisesc_1  (self, expr1, AMP, expr2):                              return (expr1, expr2)
	def expr_pwisesc_2  (self, expr, AMP):                                      return (expr, True)

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

# if __name__ == '__main__':
# 	p = Parser ()
# 	a = p.parse ('\\frac1x')
# 	print (a)
