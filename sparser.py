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
			b'eJztXW2P3DaS/jMHZAZQA+K7NN/sxJs11nayjhPsYRAYjuMsgo2TnGPv3mGx//3qqSJFUVJL3dM9M5qewXBaEkVSVcV6+FZF6ezys/969+uPn1WfPX/64ttv6Pj0xSv6ffb0Of1+8y3//vUlR331Jf3+6dsXn+PiyZ8Q9/jRS/r9+tHLJy+eIe+XL756+eT1' \
			b'59++fPbfSPvy0efxoOJRI9OTL18/f/Tq5dO/xYvHxdV3xdXX3RWXiqc8pnL+8uQVTr959ZLJfEy/L5jY75iiz796/vxRyvMy5+moxcnLp1/+GUw8ev41/X7x+Nk3zx5982c6ffLii0wgLh4XV98VV5lAlPBKHk+PQMlP/soC5cPXz1i8Xzz97ukXT5Dmi69e' \
			b'MQePIgsQ0aNXr7r8uH7yt8/B5tcvnz5/gtyvvqKft28+vPv4+rcPr3/84Zc/Pr75QFF/fPrhn3zy7n9///D6/ZuPr9/+9kv/8sNv/xpc/pGu//j0+7su60+ffn37+s2Hv+ebP9Bpr+xfP71Ppx/ffejOf/jw5u0/3n1Ml28/ffjl/3oP7IqnZOn8d2Lj13Tx' \
			b'5oeOnjcfP3ZP+z2T/dObtx/7VGYKOyJ6ZP7ycxf7869dvveffnn98/vf0+WPP/8zn/70U8fiu7/3M9BJR9qPP+ZS3/1POu/OOvZ/e//+TXHxx2ffV5dnG+Mr488rOQl8Um0sjrquzpqqrShCt1V7nuI4prvcaIUzz/+WrsN5vlb5csNlq1Z+rDuPl1QGl+Tw' \
			b'MJSn8DQt2RAb47qIjWZyNf/j2sgdnKDIGC/lU+oYKYksnoKnylN8Fxvjugh6Es4Qy/SpWn4sFanU+SCqiMQpnVGhG1eZptoILRYnSBHkxwpHdLZRDT+VWFLEhjb4P++iiktl4wnikJ0EDRnU5/kKEqM6C0W0H17ptogJoyvVjyE6WTfAno9nZ4ovzplR1LGh' \
			b'ItP1hlMRP2c6PkulmzGyu9goYcVUZ0S2lvqxlRXVo2c359vvQ29J7XZJpspUG8X1QeIWzVOQo64o9BSQbnbxOcZLjMkxQWJsjmkkxqUY0iqWm5UfSFLy04WorjHyw5KXkozhU5zpdPM8XtJVusFRgf+tTizGa5OvN6xnSskPif78PJ/SWcNVKtBucALKQyWa' \
			b'phVjp0OoFIrYGNeLUCx80+EJOBQgNvKziWzgVMlzqGVgtY5ipjaC+Sbpn9ledQJQohUQU6xM12klPd34Ti3jpSojQvcUurTSmvhK2jGc6HiyiWADWKT1Qt3pprKgIbYwMYquKfq8TDVMka7pkp/umOXIWJRVjtRmMg5XOV6ERMWTdlF7fklqHCrFbRxJhRSV' \
			b'GwJQQ0hwVajQontf+VD5pgqqCpofZNGUEqe+rQI1aYSpADYJPK6unKqcrhoKpH/UpqGnQEUQ3i23f1RbpM+BCmyhIVT/tnKVr4KtAj2UTgK0mjFDIKmcqRz9usr5yoXKMf5IS8AkBUPNXNU0VUPdTl21qmp11VKfY6vWVS2VRglq9X11Ro86p04MLJ8z5PhA' \
			b'fJMsgFJcGkmjJY1u+OblGckD19bxQW6mey1fecnvQ4wlYdH13RWWF/FQhYtAjAhE5KBd5FJHrlkGd4W1EBXBCvGWq7Opq0admsbbJnIqOupqOShR+aaNdcuqep9agjYKQguQ4yFi3wjIDWsHdZB2XcRfYox3v+rrEr0w10mT60QAuzIyBWe27pFJWV3V+KoJ' \
			b'KyPWKmnL29iWGwFFYBn3yObeTBgDfdxZqtiuSA45uNhFSDGghYtlNJ2ydp55EUZw9wyWZ0E60BBiw8lacazCjY2l6qOWGht5x6V7U3lbeZKVqryuHNVNfdJVRoy7+8q4v6+Mh3vJ+JmTGYyW0Z2STqqRyDZ2YK3cbKXraiVNKwPAlhWmDVVLYgHpNZo8EztC' \
			b'1U0mtcwi9Wn3cjwnJh5Pkzfiing7Na64wk6Hnea02CFOoHN3no1wAmxguU7zWgg3BFjggq7dKRaIWh2XtfRoAmelnypXLhuZqsk60HWQ1KR5IpOG9Sct608as0jNMsfyCw7GCfnGS49qZN7Yzaeka5VZ1Sl2Qmc2LrVa4XxNpFFKrqIQq4hb4vUtjWH9RSBQ' \
			b'r5NAglwchrq11TGR5q+tGQhppUnLApOWtSSpq9MfOQfm8R6tDF1iMVDLKuB941zX94zlMyewjv138KcPaMMjl2OCZbxyjoVPHi1ZkauXRF46EK/iGM7LCoaTVfwzHy1bUidOxlIu9tutlNhyieXCxiXWQLQsfmgxa0uj3cYFk1g+JU5mc/h5UCWbc5k/m9Hw' \
			b'ku+NDOPNRCwujVyaOAo3d82sfIlJg7ljkwaeLZhTW/nAxEbHeYeReYeReQcdBnkkg1aieMTLliQ8MUEp7CiC4bpJ8xQjlkkjlj8cmojZRpYFVyUaaRIiXq2w7YSJe2oUQYtrpP1lKYho4kEq3agkIBPbYi2NMLqBkxfQJbqXE+/U0WUa6TKNdJk4tKIZrZF6' \
			b'b2UVpZUZTMtCmW4sSAL27vVgIHTUjRPRVhpRK42oZechjUtuFe0ap9poe7lFFo6sUEuF2zSmEuBbAb4VrHMiH8EehzxOOpE2jk1aaelbjh0OolDBIisnsnKnjRruMU+cR6i4Y01yokkuapJLPYJokhNNcqIrVtoJK6pi42jEi3J4UQ46EDUCJi8eNF7Su5g+' \
			b'3PmV9UvwG4TfwJKSuY6sdRK9YbBWDSkgPbHViLQayd3EDM1pyKQ9BTbUCbABnWqjd2wd3WNr7vnq6pIKpMYt0lElumLxjpd5Wn6sji2gMAECPZgDZ25aEkB7jRG2jLZJYCRFMBrg2ChyImTAKaGm59Ugl55YY4xBj62xvYIIYoqIJNAEorDsBI9elgJdw2Ub' \
			b'/tpwaYf3E/yq4NsKl0o4KsINEKYHmB3g5g6vaLhEQwxwHcGCg8ciFsXDKRxDGnhQw8EdDmDwnoXrLKxI8KttoRm8V4u3a3jeT4MdDSQH7JCiMjYhbVzCTq+ablEc5d9Q/o3DlhTsKuMdRXQfJWE3EJ1i3wz2v9Btqm3e2IQNEg22n2AvCtJgq06NPRyUOCAf' \
			b'5bdByie122DLCzZ1YPtRE2S3UQClNW/B2ZC8Ny22iNTYqIIdZJSIBMM7Yqg4eoZHNmzMoOKxYwbbg7DTBBvaGtBDaShjcLLtxGEzF507RFPWFk8B96AGe4yQ1vOmI+z7InXnfU7YmNUiObgjIh2EAqLpnoOg1PeYf0JHJ3TTJvVsehrag2ihrQlRWWdVHNJJ' \
			b'h75Nfwfwk5mQTBvjFNKzXquk2oxhQXhfxzsPWapJAHWo8ttUne5hOj6r8vVY7eFGDFfdWfWvexCg+1h+K6AQpuEAZ0i40KINg321gweggupoBlBpKtaJSWA0HTSaAhyk5A1+whgnUFH89LDSxL9FzDTFH9CjkJRYdBFAjWIQNR2MkJVEibaUt8uVgOoVNoQW' \
			b'ShwhCrzWs7hqhsgSxqbR5YS+iC8hI2PMTeMM9QMaK2wSjZiLPPSQV/3b2wu0K6QsdPT/4TENQVHGvstQtDeEwAJ+YS/UTSHORtRdB+KuiLZFhEGH8ewCYrhESbaDGCfLGOM7Jba4CMmZ0QWRpLCIsH7inCvEosueignY3lkNCxn1XQW6croZcDEHBboSW2N8' \
			b'MXW580pELMKLixNUZZoKYCl9gfaP9O0CbQLpBx0dAGYeALZOgHkGmC8BJl0YDglgvgSYHwPMM8DKoZ7yOSwDzE8EBpgfA8zPA2xQyALAunRzABsNDBNbEwDzJcAiEcsA8xlgXbYdAWYfALZKgEGlWkxt+wDDZeAJbwIYJ8sA4zslwLgIyZkBplUOiwDTUwEA' \
			b'0+O5FhOwHWDDQuYBltPNAIw5KACW2BoDjIvJAEtELAKMixOAZZp2BJjbB2C3O1szh0zY5oA3N2HztzdpWwahYRCaEoRGQGgyCE0Jwl4YodEwGk2Jxn6GRTSaicBoNCUa48SNidDyYogghzblGqJzUOgCOrt0MxM4vi0MD0AauZ0AqWGQ6jyNS+Qs49RknGbq' \
			b'dsOpf8Dp3cUprzPit49TJzh1GaeuxKnLYYRTxzh1JU77GRZx6iYC49RN41QWKvmFVUEObco1xOmg0AWcdunmcOoEp26E08jtBE5lLZNzRpxGcpZx6jJOM3W74TQ84PTu4pRnjbqcNcaFT51njbqcNaLyUhjhlKePupw+FhkWceonAuPUT+NUppD8gqkghzbl' \
			b'GuJ0UOgCTrt0czj1gtPRrDJxO4FTmVXq3rg3krOM0zyx7FG3G06bY+O0tBzeBFrrWcDq+4FZwxNRU05EjUxETZ6ImnIiCqNtCkPMcllSRIB5FrDlwyDbEnLNVAByTZ6XotwIXCNTU355XpBDGzO147HwoNh2cTicKZiBL98W3kv4JpbH8DUyZ+WcAt+Ydhm+' \
			b'Jk9be9RNwNe7C16tG6O4BYqTLfwwLKvVdbtwE5joeecs7TeJZn1diNYDAz0iJkyRiE7o1iW6dQ4ja6ST8vi31ykXeRahrScCQ1tPdspMhyQCtrVgWyKGwO6VqISuMbK3OgCkMmcgrgXiegTxyPp2twDO6riWGeeRoWWcZ7NlFtYQ54ZVmA8Eb6P/IxvyjtBJ' \
			b'rw/Y92U8bdjMaUozpxEzp8lmTlOaOVFPKYzQ66U4KaWH3n6eRfTaicDotdPoFbMnPyrIoU25hugdFLrQJ3fp5gAr68hmZAlN3E70yWIJ5ZwRq5GcZaxmY2iPut2G1Eo9zH3vLlalqy3XqIysUZm8RmXKNSqgI4XROJrXqEy5RlVkWASqmwgM1Ok1quhMZ2SN' \
			b'ysgaVYwfAnVQ6AJQu3RzQJU1KjNao0rcTgA1dqx5jSqRswzUvEbVo25HoO7lF7Q2oM5Pe+8FVtk9D799rAbBashYDSVWQw4jrAbGaiix2s+wiNUwERirocMqThNUg0A1CFTFHJvzDdE6KHYBrbmYGbQGQWsYoTXyO4HWIGgNGa2RnGW0hozWTN1eU121l6/R' \
			b'A2hXB9qWQVu61eISoG0zaEunc9PmMAJtW8WPVvRB28+wCNp2IjBo2wzaXv/aCmhbAW0roO3yDUE7KHYBtLmYGdC2Atp2BNrI7wRoWwFtm0EbyVkGbXZx71G3H2j38l96AO3aQAu94yX9Pmj5K0E1HyJoOVkGra1zGIKWy5IiMmiLDEug7SfOuUIsWkDLeBHQ' \
			b'Mg2aD0ZuRCOF5BuAdljsPGh7xWwHLR+E5RK0id8xaJlmyRJBm8hZBC2XKKDtUbcfaI/uE/VgG7od9LJtyJa2ISu2IZttQ7a0DaGGUhihl21DVmxDfM/KYZBtEcNTgTGcbUM4TRgW25AV25AV21DON8Qwx6JKcpIFHOeiZnAsxiE7Mg4lnidwLMYhm41DiZxl' \
			b'HGfjUI+6/XB8dJ+pBxzfDo4147g0A+ESOM5WIFtagVA9KYxwzCYgKyYgdgi2chhkW8SxngiM42wI4i+aRRyLHSh6IFuxA+V8QxyPS16AcS5pBsZiALIjA1BieQLGWmCsM4wjOcswzrafHnX7wfjoLlUPML4dGLO7si3dla24K9vsrmxLd2XbCyMYs7uyFXdl' \
			b'K64aVlw1imyLMDYTgWGcnZZtdtWw4rNsxWfZis9yzjeE8bjkBRjnkmZgLJ7LduS5nFiegLF4LtvsuZzIWYZx9lzuUbcfjB88rk4ExmzVtaVV14pV12arri2tuqiYFEYwZpOuFZMuDkaSmUG2RRjbicAwzoZdnCYYi13Xil3Xil035xvCeFzyAoxzSTMwFuuu' \
			b'HVl3E8sTMBbrrs3W3UTOMoyzdbdH3X4wbo/tkzH14pVjgRmve2oPg7QpUW1PGNl4PQpeElHumm0Y2TikXbNNgWywmsLIX0Ni8UDIc8NkML75MMi8uJW2mQi8lbbp8I1TvOQfmqjirtqGcc5PjM9ve/mHm2xHTwApPagrOwn3XoHb4c63vTBbwD1JYAx3pl6y' \
			b'pI23knaHjbdNB/cedXvBXV+HC9YKO25zP/puzX23LvtuLX23zn23Lvtu7DawMYwQHqQ4KUUujKQ0JmfTO3Tf/cQ5lzw8wVvn7ltL962l+9bSfed8w80Oo5KbRUNyr7CZLQ/Sg+tRD564ntjyID24zj14TLvDlofcg/eo2w/SR3fTWiGe7wOYLXfXtuyurXTX' \
			b'NnfXtuyubZPDaCDOfTUXEeQr8VYOg2yLA/FmIvBAPHfUtskDcemgrXTQVjronG84EB+XvDAQzyXNDMSlZ7ajnjmxPDEQl57Z5p45kbM8EM89c4+6/WA878TlSySrBzAfF8zqOsbf7NelSr8uJX5dXnwwvXg8quzaBTg1nIyC5wZ89BIb9u5S4t2lxOzMh5RN' \
			b'whSsMeHJ4+8wEXj8nX28VPbxUuLjpcTHS4mPV843HHePS8ZmgHorrHslzQy4xc1Ljdy8EssTA25x81LZzYtnfZGk5UF3dvXqUTgBbVdfoNFMCK8pFpo+gfSje349YHyEcXdDnbZjm7QrbdJObNIu26RdaZNGPaQwRDeXJUUEPuBFtGKTLrItddpuKgDdLtuk' \
			b'XbZJO7FJO7FJO7FJ53wDdE+UPN9p90rajm4nJmk3MkknlifQ7aMQJVtEeCJpEd0um6V7FO7XcR/dJ+wE4BwE0vg81d2ENZuoXWmidmKidtlE7UoTNSojhRGs2UTtxETtxETtxERdZFuEtZ4IDOtsonbZRO3ERO3ERO3ERJ3zDWE9LnkB1rkkEYwWQqbALYZq' \
			b'NzJUJ8bH4E6SlFwJ25GuZWxnW3WPzP2w7arLa3s997W9m7veArowBtve7+feAqrJd3RD+Lf3eu4beDU3v0FxrOlHeD33FpXe8opuEuOymjZX19TBi+TxxY2bfJe820NffdTZOs7p+ro71FvMZTA/sAMdxvK9q4bvm2/2VWZ1ZIWeeN+8YsPB8RV7Xqkh4V0V' \
			b'GxLnOVeU+sw76HPvrAplTz30UOnDPm2zPcbXE2T4ZNfYTrsdvqXgZtrqA7+loMbbWY72PQUl21QgpyPqOMaPR2q8FUvJz+o2dHdLA45xSH1BwucRR3PAiMMe75sg9e1+FsQc9GmQg1R5Qo1VeyRVnnsZ9OT7BW7q8yCQ8NU/EUJsXN8weUeNzTPWI+qtxj3K' \
			b'Y+B/r294+HwHP2+j2vx/PF2WdxOZ2MsdOrZGP7irblPT7MMFPYQ/DlBXl7c5EZRPAe7+8qhjtsc4Unn4YuHV2uQ7MwdUvFe2rnZ8Q9ORP9HET3ftFdthetDtaqh/UNIbUlJoob5FRd14dYii6kMVVR2sq+7Y6rplLXtRbe1qVRdG6utRXxiY7VFVmGkt1dhP' \
			b'75sox73hGOpsDlVnfbSmlz8VfA2t706qfL/UuK/Cyl5LS7yDCh9Bfe2h6muOOHKoH/T3VvRX3V39dYfq73bj+v76qx7091b0d7jccIf01++qv/6qMzdT+oHsZLqbU9w5l63rMjObqLjqqMobxHKBw4ETuNDT3uh9sZ9dbrvGLnyz9vjGZnxdGBobtq2L6eaC' \
			b'IM/LYuFBe29Ne6EYRFpz+PIDl3Qq2osntsLTkvY21eVafHuueY0MpvTDfXrsXVgfKzXzOtfD4HZ4uAMPsXG5Dh28gTXaq+veHdO7a1+DvbK+0XNXom83ZBfYyTFYhj3oPLbon78N/cNTr6J+yHcdGuj2UkB4022oQL2lJ/b2grcZ2UBH9oAhsV2uQTNXopXT' \
			b'g8Wshph5PrSC+7eC1b+VuiAMs8rpB5Vb7Hybu9PzYgvMOnWOWjmoWXuxwQ6Z+mLTsP6ZB/1b1L87NPIjWpncO6N/trpUvC3N8S4e1goPqeOdS561Q3YMs5o4HkI63uAMBd1dKd2U2rGK7ehcxyq0qD7oIaNO8PDjCirADvyTyxxKKnGHSgu7VBLL0neyvMIa' \
			b'mdlzaewYy197wVkN60TJopW6MkIbdcBC1RGWo3aHISikSu4vOVEVptret6p3b8tvtIKLytWHtb1XGmPeWHXGusRkRXFdYvkwtplR8lkyeAVErWPLiUUopjWXxtBvcwG9QrrusxkUyMJiQRUC6HZD6/IBlONswy8IIoXQ/Pm3oDpfaRDIu7nY4R++sdnZGcRt' \
			b'9ExOGpP0/zi96aXnL+z19y87fvPUYHOxuE3FLb+yjRcfV6nwh8+nsEtLCuzLzdtmmkqSYHNYvAejp2znYlLskUihjLv98VPdwlOd3fnB1BmP/mDWmIrnHnnD70fHNuzZ5xMAJkjAcHOSDM+DyIk/rN0U19RedVdMT9iVHtm4vg9VlHrLXxrFbrnPhDX7ESY7' \
			b'6ncmL25i67aWE7ltNfeXBtxb7w8Gw2CBX9vZ3CgTJFQY2q83MHOqvgXuVHX9QbhTV+POq0kG7T5M6uoqARPBcSymdnP5hFkdmdXH4tdM88y2mK18o6fAhFhODgzjcqZKFvbNKth31Y0HYd8O2e+9/0TkIF8e20UanjsuvL3E995bMnpXSfkyEkxz8RISPxCX' \
			b'E5HhJSLbxYYm95YCBn52EIfWdzq9CNutQdewXHXTQdj3i7q2oxwKFZuRyUiplhQK63i9ENJvKOMXA2Z2kg1zuq2pnJp4XBlEcmH9kgvVmoKIrVm/2JpqTUHE1q5fbLyouZogU/F69WLDKtaKgohNrV9splpTELGNhu1XEtsuQ7YDheerwwOWxIdR1M4fUKQI' \
			b'cTT4v+HR7/7SbKr5IO8CXEy2Y1Cy4r1zEKne9pxib6liOX+9QYQ6mjusXqi+WnEQoS7PSNYm1FCtOIhQlycraxNqW604iFCXpzIrXqeB/ewOBJF0G10tYFqBiMRuRoN7iJzlLWIjlmHnqKOttzPiejE04VUfcBZoYP9XDXw1KBMMBRBnE4vV/NHkrsZItDBG' \
			b'ONkkXstmRRcLNJNpfdULktCOEqK+kDhU/aCcdNjYnon665xK2MoJC2eIVkN2fzD8xnzK8v35/wPyDYZB'

	_PARSER_TOP             = 'expr_commas'
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

		if pos == 1 and rule == ('expr_func', ('FUNC', 'expr_func_arg')):# and _FUNC_name (self.stack [-1].sym) not in AST.Func.PY_ALL:
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

# if __name__ == '__main__':
# 	p = Parser ()
# 	a = p.parse ('x.y ().z.w')
# 	print (a)
