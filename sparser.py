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
			b'eJztXW2P3DaS/jMHZAZQA+KbSPmbHc9mjfNL1nGCPQwCw3GcRXBxknPs3TsE+9+vqh5KJCV1Sz3d49FMD4bTEtkkVSzWwyJZRfXZ5RfPnjz/9psvqi+ePH9Fn0+fPKPPb76Vz7+9lKQXX9HnX759/iVHLv7CaY8evqTPrx++vHj+lMt+9fzFy4vXX3778ul/' \
			b'cd6XD7+MFxWvmgtdfPX62cNXL5/8PUYeFbHvitjXfUxq5ac8onr+8+IV337z6qWQ+Yg+nwux3wlF//Hu1x+5yItnzx52RV+moj3RfPPw2df0+fjR02+ePvzmr3R78fxxoo8jj4rYd0Us0ffyyVd/fRVreiVUfEmP4JSLvwlf5fL1U+Hy4yffPXl8wXkev3gl' \
			b'DXkYW8Kcenbx6q8vHr+OTEZMbp49uugr5owXf/+S2fD1yyfPLrjaVy/o4+2bD+8+vv7tw+sff/jlj49vPlDSH59++KfcvPvf3z+8fv/m4+u3v/2SRz/89q9B9I8u/sen39/1RX/69Ovb128+/KOLv/3t/fs3RSQr9wPdZo/99dP77vbjuw/9/Q8f3rz973cf' \
			b'+0o+ffjl/zJa+idTtu7+d2rhr13kzQ/9I3/8rc/+e2rQT2/efszpTwT2NGRU/vJzn/rzr325959+ef3z+9/7B/38z3T70099C9/9Iy9ANz2RP/6Yan33P919f/fF99Xl2cY0lWnOK9x4vlHVRss1VGe+ChUlGFeF8y5NUvroRrV8Z+Xf1tXGnad4FqUbumrD' \
			b'daqWHhG4Vu3Pu+SYmFI22spdiw/t6FnnMYXu+CZ0X53HKMW6L5Ck5Xmhf17TJ8fElELP5DtfbQJfg/xb4kZ7XsTrlLKRpykPVljXPyayp/uiwaMGqb6LUkxo4F6oDFVrQBPfcA6HD4vHKmaEdJmuqRncXfJ/3ifpPKpMvOE0Lk5dQ91h6vMUY94rYn2R7Iax' \
			b'wffNKKbyFKJTxIoerGy8O0NEYiIVhh7cxTeSS3ED4rNU92VM7CMbhaao6kxX1HqRQ105Jc0gUtCp09+zpJOgLsk2yLWJvFRRiLmVRldG5aJMX/bpKcUhRaeUBikmpXik2C6FhFI4Y/EBsY8pAIAx+GAmx3IU41u+092X5zFKse4LSXLyb3XXxBg3Kb4ROWvl' \
			b'nxh/ft7f0U0j/YlmN3zDZBMjMHq0zKR2iAhKbQswUAJ1qHC+w6KMBPIEYpJ8bCIr+VbhOQQiYRFooqiF+BBHTNaXJnQiwdIU6ze9SBLbTZNkEtG6TPD9UyhqgVTqjbq7UfGGHtfdaRF9xR1Aj3bcOxiiuiSKU/J5mWuYo4tTVJ7upMmxYZFXKVFPp23SqEd3' \
			b'YBJVT2MdDf+XdWVYrkh+aIyyvuLxvq2aUDVt5evKm8pzC6VyymkrryqviQs0GHG7CCqOAGMqZ6tAwZEOYZ4TrgliNFiScJE8MUJ0FeoqKB7H+fmeJKCylauaylOgR4fKEyWU2bLAUD844hF9+sqFyhFVIiYkHDyoUaAW6qqtq1ZVLd2YqrVV66q2qVoSPKrN' \
			b'UTbzPQspd5Hhz8szaq3EOJEVILWb49R2vuAzxO+QtQm4tDHVS023nSkeXKHuBVuURKlJcjGxrdoil3x7yxqo0TKL7rPSmYHoMXdTyl2N9jr0pENPOvTkWavwrRI2kDqioZQUDg2FpKxOYAxoIzsgzyFeHJhiAHsjkmItT+TW14RLnuqdYt9R/2AgtnXqHwB5' \
			b'jcRa4M/qjNimCtQzoQrtOkk2kH8VR30DsAThd0Y84SjEcUQ7KApoTw0A6U5xRq2BLx2yKozDqlO8knr3pfesAcO8P0nwnnl0u2/jUCuidqzKTWSusUetNaoFJ7U3xKWmanzVmKqxVaOqRp9Ax1Hz/Wk3P5x289sTbv5Zg9WRxkVBH7aItXEl2ULLtVBvLZRd' \
			b'C03YivC0xMOan0zPrTUPhlEV1mkxqs/vMB9leU0tvJtt89y0u9aocBcb1Uir7kpj2jvTGN5L0zIQar7yvhM37TY2RKEhViStWDNd8t6THm0uhqhUZEF1HSQF028IaWwIaWwIad4QUi0IVlElQX2puF2k+n0SLmM88hppXNyHMGkxg+kAljR3V5md2bhXarF0' \
			b'XR+BCj1tYteykWu9+1m8UQIy9ZrJJKACGsGvs9eJwHBtQ0jbbQxp7AfpuPejT3Ar45J3u06x4by9B6Ty5e6395J3Lk+xoy95r1Zjk/Y026/CSTb8DN3uI859OBWgG1lwHBM+Y1MH707LzLsBdxtkajCtaDpTe4MpdwMjzFkTDZYeZTHzdnFm16LGVmoc7jJd' \
			b'8paUxl6Uhh9DG+mJ21l1fAZlxzYXcfccmzVmtE7xkjZ0gggTqRw1iJq4qDO303ngklei5lauRGUJau7mlhuvmXVc0hosaQ2WtHQZlIkroiiKKuo1cyoDG1G2hSeyjGe2yRqf12GuW9UbGNkNzNd8CXHMCjIMra+hvPaRjSMn5GoMYBbjToO+d/jupK15rIsM' \
			b'NJPwAgzC0O6RZkzHJhO1lIZ64v3gE2HTJavfkxgheGJhMLEwmFjwpQVyWgcZaNu4GqjjVZgzPagQJ+xtVfZM7mjeQ6Rb6BgLHWNlygSUUFts3BG169274mHbYHS0GB2tjI4Wo6ONo6PtJqcYJyzGCYuhQTI1aHU/N4WqaDvlWsfBpZb08XyUpQCsdGClOwWI' \
			b'iRI+iZYyDBzkzImAOQiYiwLmOr0CAXMQMAcRsnGEsVGCbJzgNZCYBhJDF2rY94K8Bk5lTSzgYgF/R4xil9xsj2Z7YRkWaTA+ENV+6JRHD5b8fCxLmBZQOsQC4S5xpr07jTF3pjEsZW30Oq+j23ktarSuLmuhAQNfX6nK7Ie861YXLMgbQEMn2sZENxMth/rF' \
			b'8DrJtWEjZTbLCwAMwYo7gFrS8whMhIsxOJ578DIjpNn0T0uomppQ8zSIGieto+Zx+7iB3EJuIvOUPe/5eAWfreBjFexBy+6z7DTLXpHsy8iO6OzszJ7O7EfMTsTsnMuWR7Y68mEVPqnChxnY35/d2XnPiV31eCOJ92N4M4YPd/BMjM9A8HEVPuXBXcUeueyI' \
			b'yk6ZbB5mP3h2gmcTF9u32N7DXk7s4sTuTdxOdmxir6Y2UHc2zE4+Aeb55JeNRw/pSk9qqg2fdCJRoTti0oazUu3yFX1Q2PDZMj6IFpQcAuPDdfxBQsnH7fiEUhP/Ng2fWKzlrNOm5XqpKEncxvPxR2J+k/1tuJF86o4aLQRS9YEf5flLy8fxWjxfoKX4dGFo' \
			b'cSaMOluq0D6vkI/YtdwOPp1Za6mVCxFd/M8n1KTFJCR8Xo2fwnTxIUWilY/UBf5WmkhfeD7bRwS5WD112IaEcUPSuGn5UXy8UmSVqQx85IxbFSIxfFSVcjANjVSCQ5B8AFVO43GkZr4r5jvzlnJRAVajqCLwCVxOJbD+2agHG4gQXcO/WY8ySmWcmEWp/izg' \
			b'zJHZXAGQU2C0EZDXBcZDgTgHPkEC90qOPolquUT0SbYEPzWGHSc1KJmAp3QKs+DLM8ci3uDCEGgBQeag7vHH4MtRF8tpP6pqCL4SeSmfAje2IE9YUkAvFpsAn1QTCuR1tCzEnkqQSwQWqFOENpY1ZR7w4EFyQ1fzb5na3aNv/egTxSdKJkMfVB9fOvTZEn12' \
			b'jD4r6LMl+mwK8+izwyDos2P02e3oQzntR1XNoK/PFw/Ab0OfHaEPxabQZ8foi7QsRZ9N6OsJXIg+c4++W4C+VtBXzjwlquXSoa8t0deO0dcK+toSfW0K8+hrh0HQ147R125HH8ppP6pqBn19vnjZhr52hD7kn0JfO0ZfpGUp+tqEvp7Aheizy9F3g+tDffgS' \
			b'cRcq55aIfgXLxDmE8kqw5U7KESpRebdKh1DJlhCKPDHnAKqc1KCKBNWiwBxU88wdNQaXDKpxpSgUyE4MI1ZifakMujFF+1HVu6Gb8sU1ozxhDF/JgcaXCI6lJxAsNaFIBuKOqoUglroB4ozUZSB29yC+IyA2AmJTgtgAxCaB2JQgNimMQGwExKYEcV5gFsSj' \
			b'ICA20yA2ALEBiA1AjOw5iJGi/ajqGRD3+ToQm2kQG4DYjECM0lMgNgCxKUEcqVoKYpNAnEhdBuLmHsR3BMSyUtXlSjVu0uq0UtXlSpX7sgsjEMuSVZdL1qLALIjtMAiI7TSIsWzVmDtLTHWlchAjRftR1TMg7vN1IJ5exkoONH4AYpSeAjFWslIyA3GkaimI' \
			b'02I2I3UZiP1xQSw2oklz03VAmYRrHs3mBAEti19dLn41Fr86LX51ufjVbQojQMsqWGMVzLJLbZfLoNgsrNthEFintTBX2qEay2G+mEiUioXaAbDxtfbDytt5bPd0dNieXiRLDvBhgG0UmcI21slSMsM28i/GdloqZ6ROYLvRD2RDYwzxwBBnbzx7GNDhlbI6' \
			b'hV1P6my/w8h6A1Dnl4NcG9zlbZ6VvDmVnr+RbpoyuHJyhD7fZtDnfu3CEPrEbE7FZ6bOizJzuM8zxyIeryGdUOdChMVLStEYq7pSGepjivZFvdxVeL3pAPYCx2bCKtvVDPzL48b4lxwBLCzwH0tvMdDyACBFMQBwf/MgEAstHQTkARgEEv+GgwC3ncDPF8K+' \
			b'qRn67cHafaWgP8FZuhFrrimtuQbWXJOsuaa05spLhGMYIdtLaoNaMmTnZWaRrYdBkK2nkQ3rrrxaGG2xqiuVIxsp2o+q3q3MU74OzNPWXskRwLUSzJGVYzAbGHxN6W3RUbUUx8nmm5G6bKKu6vvl9h0BsuyZmXLPzGDPzKQ9M1PumbETXheGQDayZ2bKPbOi' \
			b'wCyKR0FQPL1nZrBnZrBnZrBnFkvlKEaK9qOqZ1Dc5+tQPL1nZrBnZkZ7ZrH0FIqjRi73zDqqlqI47ZllpC5E8R6OU2tC8aKV9skB2QmQXQlkByC7BGRXAjkLIyA7AbIrgZwXmAWyGwYBsuuBzLcdjh1w7IBjBxz35XIoI0X7UeUzUE6VRSi7aSg7QNmNoIzS' \
			b'U1B2gLIroRypWgpll6CcSN1rda32cMa6R/TaEY3lsy8R7YFonxDtS0T7FEaI9oJoXyI6LzCLaD8MgmifEO0Toj0Q7YFoD0T35XJEI0WPK59BdKosItpPI9oD0X6EaJSeQrQHon2J6EjVUkT7hOhE6n6I3sPB6x7Ra0d0EESHEtEBiA4J0aFEdEhhhOggiA4l' \
			b'ovMCs4gOwyCIDgnRISE6ANEBiA5AdF8uRzRStB9VPoPoVFlEdJhGdACiwwjRMXEC0QGILp3FOqqWIjokRCdS90P0kZ3G7q1cq4C2WLlMaeUysHKZZOUypZXLtCmMoC1WLgMrlwG65TIoNgvwdhgE4MnKxbcdwGHlMrByRdfPVC4HOFK0j3fcOynjDMhThRHk' \
			b'02YuAzOXGZm5YukpkMPMZUozV0fVUpAnM1dG6n4gP7JT2T3I1wBylk3hfg5yiWr8eiRAbkt7FvdWF4Ygt2LMsjBm8QU/7ye/dpYXmwN5njkW8QYXgJxvI8gtLFoWFi0Li1Yql4E8pmg/Vf9ujGf1AeN22pRlYcqyI1NWLD2BcSmNIhnGO6oWYtwmK1ZG6n4Y' \
			b'P7LP2T3GV4Fx8QS3pSe4hSe4TZ7gtvQEtyqFEcbFE9zCE9zGn/BUwHhebBbjahgE48kf3KZdcQt3cAt3cAt38FQuxzhStJ+qfwbjqb6I8WmncAuncDtyCo+lpzAOp3BbOoV3VC3FeHIKz0jdD+P3Lml3EeNivbal9drCem2T9dqW1murUxhhXEzXFqZrvhjE' \
			b'zKDYLMb1MAjGkwFbIBUxDvu1hf3awn6dyuUYR4r2U/XPYDzVFzE+bcW2sGLbkRU7lp7COKzYtrRid1QtxXiyYmek7ofxcFzHFHNtSLfZq5cOwbstIe9OBPb8A8wt92dxDLMR2Kv0AhBVvgGEm96FkdMKqpPvWoBffvAZmc2g8OzZzGYY5Gxm04Ofb7m1LI9c' \
			b'EXMZrwiRxyGDVVn5/NQmUrSfeE4o1+yKT1ROnN9M1WIsUNNvDlHxGOfo7SGx9NQxzkbGAimZneSMfFx6krPpx4KM1P3GguM7qa1T5dvT0/patL4utb6G1tdJ6+tS63ucnEeWIfzxI+UNakHdpul/uFxnJWd90fUwiC96Uvw6KX4Nxa+h+DUUfyqX+6IjRfuJ' \
			b'+sPsZnxWJfCup3W/hu7XI90fS0+5o0P361L3x/yL3dGT7s9I3Qvv+siObOsE+6kh3Yqit6Wit1D0Nil6Wyp67psujOb3ouWlClRsEDODYrPz+2YYZH6fVLxt0vweqt1CtVuo9lQun98jRfup+mfm96m+OL+f1ukWOt2OdHosPTW/h063pU7vqFo6v086PSN1' \
			b'P4zvcnOzBczx7sB7pF8L0v11TevF802Vnm8Knm8N9HpjMbNPzm8s/jy5l8A/VzH2f1Pi/6bg/8YXg5jpiiFMYZ7XVGla74ZBpvXJC04lLzgFLzgFLzgFL7hULp/OI0X7qfoNlnXb3sOS6ovz+GlHOAVHODVyhIulp+bxcIRTpSOcLDEjZUvn8skZLiN3Avc2' \
			b'POARtoN/TfBn6ZgYBo7sG3c/AGwbAMLnVvdie7el7d3C9m6T7d2WtnfbpjBS92J7t7C9W9jeLWzvRbFZdd8Og6j7ZHu3yfZuYXu3sL1b2N5TuVzdI0X7qfpn1H2qL6r7adO7hendjkzvsfTkEj62AcVylR8pW6ryk/k9I3c/lX9kr7m7gXWf4b2+5ZgXTDOv' \
			b'c8w7mOJdMsW70hTPfdOFIeadmOIdTPEOpngHU3xRbA7zeeZYxBtcgHmXTPEOpngHU7yDKT6VyzAfU7Sfqn835rP6wBvVpU0h38Eg70YG+VhkAvldZSiVAb8jbyHwXbLJZzTvB3xbXXanywvoA/c96HOgq+QYuxXQvnzD4fj1hm6/U99hC/zCBOx2zbEzmI3g' \
			b'NQWtDlY5lMrj2lNntTs05VAawmfTFD6oszBhUAzfObjthYMs9nucod7seLfgQKh3HZXOJXkow5Py2wlvLrP4YYlrl0n8KtSxJFMdSTr1jIRuUwDrlVIlb6+0R5fWHe+i3UdildkptVtH3m2S2+yU3OZIwuuOLL873xHbyW+4ggzrOKFpsJsxN+LytgGv1Kkh' \
			b'pVzzm0b11eVb+WuWcZak5nrkfHqnIZNz5vC+ss5cl32GyPm50TpNM0Mp/91cc4gDv2wE10caxLEuMMeCwnUM52rhpEMff0hX44NtB08+cnFXEHkVX8N4JLHnZdGRh3jm9pLJCXN/6zBPk2qtHlDjZfocrjRV0cebrchal3+w55hjfn1FQW8g7K5dzQxb+SMK' \
			b'+rZxXeEsppo8gHnl8V250fHLJYLOHIewm8Nn4u1Nrg6pX+TXBW9wjcg/082/4L0CSb7utaISd0t9g2tGUDD2V95HYonXNymx/l5oP7PQ8jkAe8OCu+Ep+KGCqw4SXN5lP1B2m2OL77Yt8SViXK9blP11iTPvlzdHFelmPItopm3RQ9Hm/aajibc+bFyujzg0' \
			b'19c0PC+V7dOT61ymmUfXMFQvlOmjybM5TJ7VEeVZ3cvzjcrztdhZPrc8H2gH3GHb31ue9b0836g8u7sgzzdrQzTigdK7nxxxb446QxluB/vm0HfsXHniNsZ99ujk2v0fc6+Otz5D3PpUYvo6nh1Sie/ZUumv/qROfECPlJ+73G2R7HFgrwqFuvTQOtgc2Xwm' \
			b'Z48pMe8MXeGo4s79SWTy5UCBl5qizEeHqGPZGsNn8QKZsqfzz9GLLHP+SXHWzQMaLkSaF9oV76X5+qS5hTS3h0tzeyel2UdpbuelOVSX6/C8u+7NaXPEOQczdP0b06WkXudGNLsKH9OHiRp1uQaZvCkv0L1kUd8uOfwsxpAD5Y+oWIX83aQn8jYZdDJbYh2z' \
			b'RR7NTcijPPUK4sjlrkMi3RWdOpWsJSnvFs3dqAc4fVjTNcjPmSvi+Y1L6tqkdHKymcSSe+x+lDxklKz+5PMbSiRQ30vgQl3tbo+i5jNwbuUi6B7wIfKaJNFz7z/YYEQ09/K4UB6bWySPTSV7+LdQHm11qeS4Kk7b4bVhnvjPWzxG5AUvHRDBaWQG6uQdCWqx' \
			b'jDbjn2YQcZtygJkQLRGlWRESJQq54N2SfUVAun2o6WRXWy3qMNl7nO8Y4V+zdv7ZdfPPr51/bt38Cz3/9t8Ibuo993+Pscd7JaUShr1Si6LgyxX1RKgP2I09wp7rVZQB00Pdnu+rUkd2/b9v5y+fY9xIlxfdrQ6bE1xpaXQDHRx7l9S7lRPrjveHoi6PfZF4' \
			b'xG834sZJV9mO6rw+HiBo7nCZTQe6avquUYMqhXFgWs6M/j0eYfgIKnO2kbdoKXmpn8Gv4mZvwqAuj2+qKF9TIbZ/9pztXh6Bl0Fwu8TbwPNPpvNnmwIfWMN37BmAO4kEMffHTOzOgsOVzIKNPi51NMVa/icEmF0EUBfsT4Ophn9snBun9n9Ch/y6kNK7SHG7' \
			b'OOJ2UGR54WJHf7y5OEojacziQppbRBpem3I1AmmdOfnXLaG2fS9/QmOzB414tcsVKMXh0/RuE6LcV9v/uoXfrjx+tCTj1sjb65ubaE/glW44/E+aEW6sGVTkGH/SivYKrSCNs70hds/G8B7CvoH3GrZ9Z9vZCqThqo4t3xNZOxtvtjOA6drOBMYS78Hg5vAw' \
			b'WdVUInih1sQLU91QAC/0kBfZu7giU/D7pHOsaUSj8Zu0XPYOrSlmcfsLfvkqvRDLD3jXvdTK7uKhr24yyOQOLgl5Mr+iYroIOG/WJIWhuqEAXth5KVzAlFz4ljFoJG5zosbbzVmgJRY+cbMw8CoPZXh9N5+d2jh+aBnARndr2Oiq9QXwsLk1PGyq9QXw0N8a' \
			b'HvpqfQE8DLeGh6FaXwAP29vCQ95JXF3Aps5o4bA/D5dPDY/ASVsdGHj7fZjEm70HV2ywBaNHy48bmHJfibVNtTvghbiz2ZYH3u7eswxYvIZVzVVYzFaEtQdweLR6uS0cttXqAzi8YE20Tg67avUBHF6wXFonh321+gAOL1hMrX53iU25tyaA7T56KLFPEnEt' \
			b'inuQn1/kbabc+BRZx1kdv/Cyldde4lBwnR8KRiXtXCVNtSXARMcv01JRAtCXxH0u10YLeW/69tjUkLcYWV5d8ht8Avu5UaEQrQgt1BG/CyaXIeplthyw5PEWOL/OguUv1mgmM/sqC8hoRxlZdjhzqPKgGozZfEScZar3CBNDMBuBPewPfHZWhVp23Iih35//' \
			b'P4fNvME=' 

	_PARSER_TOP  = 'expr'

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
		('METHOD_LEFT',  fr'\.(?:({_CHAR}\w*)|\\text\s*{{\s*({_CHAR}\w*)\s*}})\s*\\left\('),
		('METHOD',       fr'\.(?:({_CHAR}\w*)|\\text\s*{{\s*({_CHAR}\w*)\s*}})\s*\('),
		('MEMBER',       fr'\.(?:({_CHAR}\w*)|\\text\s*{{\s*({_CHAR}\w*)\s*}})'),
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

	def expr_mul_imp_1  (self, expr_mul_imp, expr_int):                         return AST.flatcat ('*', expr_mul_imp, expr_int)
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
	def expr_pow_2      (self, expr_dot):                                       return expr_dot

	def expr_dot_1      (self, expr_abs, METHOD_LEFT, expr_commas, RIGHT, PARENR):  return AST ('.', expr_abs, METHOD_LEFT.grp [0] or METHOD_LEFT.grp [1], expr_commas)
	def expr_dot_2      (self, expr_abs, METHOD, expr_commas, PARENR):              return AST ('.', expr_abs, METHOD.grp [0] or METHOD.grp [1], expr_commas)
	def expr_dot_3      (self, expr_abs, MEMBER):                                   return AST ('.', expr_abs, MEMBER.grp [0] or MEMBER.grp [1])
	def expr_dot_4      (self, expr_abs):                                           return expr_abs

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
		# 'END_MATRIX' : '\\end{matrix}',
		# 'END_BMATRIX': '\\end{bmatrix}',
		# 'END_VMATRIX': '\\end{vmatrix}',
		# 'END_PMATRIX': '\\end{pmatrix}',
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
	a = p.parse ('|a|b|c|')
	print (a)
