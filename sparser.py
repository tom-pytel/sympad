# TODO: remap \begin{matrix} \end{matrix}

# TODO: Concretize empty matrix stuff.
# TODO: Concretize empty variable stuff.
# TODO: Change '$' to be more generic function OR variable name escape.

# TODO: 1+1j complex number parsing?
# TODO: SymPy E and I optional instead of e and i?

# Builds expression tree from text, nodes are nested AST tuples.

import ast as py_ast
from collections import OrderedDict
import os
import re

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT

def _ast_from_tok_digit_or_var (tok, i = 0):
	return AST ('#', tok.grp [i]) if tok.grp [i] else AST ('@', AST.Var.SHORT2LONG.get (tok.grp [i + 1] or tok.grp [i + 3], tok.grp [i + 2]))

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
	if ast.is_bracket and ast.brackets:
		if not ast.brackets [0].is_bracket: # single layer or brackets, column matrix?
			return AST ('mat', tuple ((e,) for e in ast.brackets))

		elif ast.brackets [0].brackets:
			rows = [ast.brackets [0].brackets]
			cols = len (rows [0])

			for row in ast.brackets [1 : -1]:
				if len (row.brackets) != cols:
					break

				rows.append (row.brackets)

			else:
				l = len (ast.brackets [-1].brackets)

				if l <= cols:
					if len (ast.brackets) > 1:
						rows.append (ast.brackets [-1].brackets + (AST.VarNull,) * (cols - l))

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
			b'eJztXW2P3DaS/jMHZAZQA803kfI3O/FmjbWd7MQJ9jAIDMdxFsHGSc6xd++w2P9+VfWQIimpW90zmpnumcZw9EKRVFWxHr5Ukeqzy89ePHv57TefNZ89e/mKjs+fvaDjN9/K8a8XEvXVl3T807cvP+ebp3/iuCePL+j49eOLpy+fc94vX3518fT1599ePP9v' \
			b'Tnvx+PN4UvGsOdPTL1+/ePzq4tnf4s2T6u676u7r/k5K5bc8oXL+8vQVX37z6kLIfELHl0Lsd0LRf7379UfO8tWLF49T1ouctSeaLx6/+JqOXzx5/s3zx9/8mS6fvvwi08c3T6q776q7TN/Fsy///CqW9Eqo+JxewTFP/ypyldPXz0XKXzz77tkXTznNF1+9' \
			b'EkYeR05UysgXT//2ObP59cWzF08526uv6PD2zYd3H1//9uH1jz/88sfHNx8o6o9PP/xTLt797+8fXr9/8/H1299+KW8//Pavwe0f6f6PT7+/67P+9OnXt6/ffPh7un/72/v3b6qbIt8PdFm89tdP79Plx3cf+usfPrx5+493H/tCPn345f8KWvo3U7J0/Ttx' \
			b'+Gu6efND/8rfMxc/vXn7sSQ6U9W/uCDtl5/72J9/7fO9//TL65/f/55uf/z5n/nyp596tt79vcxAFz1lP/6YS333P+m6v/rs++bybGVcY9rzBheeL1Sz0nL2zZlvQkMR9CycpziJ6W9XKvCVlX+7blbuPN8Xt3RBZ625TNXRKzyXqv15io6ROWaljVwFHLSj' \
			b'd53HGLriC58encdbuksPEKXkfaF/X9tHx8gcQ+/kKypEygjybym+O6/u1zmGLjgvS68xdGtQFl+wdBwOFq9QzICImlg9U/zCNf+f91G6vFUmXnAcX5FISYwa78YdP1WN8J2j3eiurWJGd2ZdxhCdwgQXbePV2VpuRE2kNg09TfcrSaXWxADexeXhYYzsb1ZK' \
			b'6o14P9MNiZzrgLi2olKcNUpq8jlrKCnYLskGqVaQJYkbysdcGtJqVaogk5ric4xDjM4xLWJMjvGIsSmGlEkkY3AQSZ7HGCiu0TiwpGJJRsslX6n08Dze0l16IFFO/q1OLMZ7k+9Xomed/JPgz8/7K7popT7BdssXTLZtoP4ky7OIxIjxwFLLiM2xVKEq1lyK' \
			b'I32VqxaHVeSBLxXeQ08Yawr6RrcW6kPCMkVdml4lWEaxfJNUkuLOTJt1ErfrOsL3b6FbC6WmV6zThYoX9Lp0pUEL1w41N5YrNupujKJ7ij6vUw1TpHu6lbdbYTkyFmWVI/V0HN/leAiJiqc2kZrty3VjuEFk8WmueG6nu6a1Teuatm3arvFrliYXTikp3jct' \
			b'tV5UErdHzBqhxXaNWzeBAis0aXAjvQH1Ayx/wrhoQePbxlP6hopuvG48vc423rFik2QFHo1TjaOjaRylc41rmQ2CGsGB1YS40k1om0CEhiZ0TbduOtV0uulM01FpdN19z3rJtWL4eHlGDPIdMamY6TNile+tPGYkn3NnhGed3JEA5ORibCvRRyiHtgWP6ygJ' \
			b'BUlAANpE9nRkV0Rx+DwFMGNBtZXa9URCd2/U17aRRSinDTh1Ul9nweOpEq2kroWaReo8qFmjjud+4jlAAg64DvGkIAcDIBvRB+rZ7YFQfcmDswdSQ1QLaGVNm2sBoDwU+oAlEzJ9gXKaJtgmuIOhEh2Q9qlphuJ7kWpBL2HCx2YAzaAHCBxaeIVs/GopRurm' \
			b'XireWWwqvX4oUDvzscZd7NRFZRYq2+jYpq6XLDQ21E4Kb1XT6qalQqky1o3zjQv3s6aIY/PgOLYPjmP3sDg+c5hUaIzCFCYTAZGhA9Q7POzQHXVI06GP6kRFOtd0bdP5pgvcpsWEXT9lo8n0vRKbzDuJqXvDjmdu7gEf4Z7wQSwwI8dLvztm+tlGpKXpEpSz' \
			b'cYW5ORLaPWi3okLVNOOSDSx6ZCfzmGDAFHETY9yut4BoWEA0LCCaLSAqylphzqnQ9yjYs9j8Hq0EnMcYpDXCW5ySmzxTQA+N+cK96nDObLT6WbB8EDRRQqkUFyullX7+cGw2bCYAZeHAKKOOKo60zMFUJ9Fkb6gBCC4ZQjTsH2ig+HQvR9WXbMHRD8OCcclm' \
			b'Kg371INhWYWHwutZHDBoYNbfZ9BqGYksCIux9ZZtcSxPF+XZIlGL3sB1yUeJGbeD5fjMRY+JQV4MflzsdjuU2EmJ1UT8kqfsGnN1DY8oGuIOY6wuFt+heKpTc46prRmPESVu6EsNE7F8a3Br4hjaHI1D8pLH+uZYxvoyyDf3xgzBExEdJwoGEwWDiQKdBlkw' \
			b'AO2gYgqNlDL3uHEiYqalILMhlpNMlXiqoNLkyMCHZ+Aq41OI7U6AqA6BNR52ynwQrY5BlTpQ/9C8DNxPGPQawj5kEhtkSEh3STIm9iAaXQf3XfdXMpfcG95XeHPXbtC1G3TtfOqgC51CTXdo5boWJ5HGZHtAnNsj6nGZwtF4g6lFF2DRBVixBkFMRL6NZiB7' \
			b'UPN6blelywJHBmRS2TaN+QBxC4hboBqJIqzTkA9dYBcHUR1a8U5iB4M8EpWDqBxE5e4pSqQTvK/MsTJL/cmRXuSi6rjU2EN1HFTHQTksGgQL3bBx8NRCHVqoA51IGt8LbFosK2mR3sX0/nhN9ZfMqAejXkSEuQyspUSoHy61ofdKeioXYgrIHWKGcOTC6I6a' \
			b'/u6Y6Wf16eIaz3Vc5LmW7mzdXK6FBLRWfZmqcF6wUanmGs0cc9GTaoTHxCC6PrSDk8IZ84UhIo2i46A6RGn3YoG4fBcFW66rI96Za6af5ULkr2nOsSYG1sTBmlhYM+f0nLlj9nhOwgyyNHmJK8uTFy7zqmVeqcxr43h5Eq8q4qWfvO6TFx/yykNe5Mcr/HgZ' \
			b'Hbs/2PXB67x5rTBLmKXL6zXYWMJ2FDai0BxBsTmCbRG8XprHQLzGmBd981IrXmfF6+94vR27vXj1KS89ZdM3W6l55QP7wXiNamCNbFl4vE2i5V0Rso+DtwTQPQmuWZG4V5Sej6FZkcBXVBppQ8sHz7s0eJMEPfKSqOWD5w0BWvaHtPFv5Vrs/OEdAoFLo2yk' \
			b'VysuguTdFn8r5oX3zRBvTBu9fkW1xRtJmKC1bHaRV3s+Kd7DEJxs1Vj5qiDeRUEqvOqYwyCF8UYnKpn54yxa6JUtHFI4b9LgkjkzxQam1gr9lIw3NxAdTkeWqDjHe7zoWcdvYsEZfgsTF/hlNtJBqZhXI5mxJ4j3UXFGetyx6BRn4BIoDe8e8omJwBuLKLWl' \
			b'2vp3u3604jXk1tLZ/oe7SgaeIH8WePrm8VaCze2MsSl8rSPGbgpfV8TWLJ5YwZnOClByG+QUASU4yIji2wJJkl6OBZa4UlOYw1OZNuZoI1WEAKpWQRULTPeQYjyVQBoWMEBTDaWcTOE9G6AktFdYSgyN0STF2B5KiYxZMKmMoUxWBSNFMGLtWXePuA0graCz' \
			b'+Y+Mq05wOig4WYGTreGE7olPCU62hpOt4WQFTraGk81hFk52GAROdgwnuxlOgwK2w6lPFnduboKTHcEpRk7AydZwimTMw8lmOPXZdoSTOcHpsODUCZzq4Z7cymygh1NXw6mr4dQJnLoaTl0Os3AaBYFTN4ZTtxlOgwK2w6lPFk+b4NSN4BQZmoBTV8MpkjEP' \
			b'py7DqSdrRzjZ3eF0V7MsddWJ1jaYzU20zN1NtmYhx/OpjuujhJzcBjlFyPFlATldhBJ7klGOBfaqxDPY02oYGHtyKrAX51tC3xo0OJx8ylVgcVjgVizmZHHeJS8Z41HeYcFSBcnE5xiSUhKyRFQmgmZRKSUClZnAHVHpTqg8PlSK0YOPJSoNUGkyKk2NSpND' \
			b'hUojqDQ1KsvEc6g0wyCoNNOoNEClASoNUIn4EpWDArejsk+WUGmmUWmASjNCZeRzApUGqDQZlZGgeVSajMqewB1R2Z5QeXyolNmermd70Rip82xP17M9rrYUKlTKtE/X074q8Rwq7TAIKu00KjH1ExocTj7lKlE5KHA7KvtkCZXTU0F5R2SpRmWMnEAlZoM6' \
			b'j2ATQfOozBPCTOCOqPQLonLkDrlZbIaN8GR/yUNBaBCEhhqhAQgNGaGhRmjIoUJoEIQGQSgrJoFUToMsczgNwyA4DT1OucwE0wCYBsA0AKaSiVOVSK2LFLq2grV/eQJrmAZrAFjDCKyR2QmwBoA1ZLBGWc6DNWSw9gROgbVVj2TqP8ZsYMzqxiQX49WQGw6p' \
			b'S22nelWzxd1329hd3xR+GQX4Yp3FELi2BWnYgnS2BenaFqS7HEoos2KLXUjXdqEq/RyOR0Fw3E33t7ANCRkOJ59ylSguSuMq0RO2Iv6CGX9YroZzT0OC87TdSN5nwV4N58jzBJxhOpKcRipWIB1lOg/pbEHKRO7Y/3bX7H8PCsUPZ2BsxIhkaiOSgRHJZCOS' \
			b'qY1IpggVVg3yyrHAapV+BquD5AZ2JDNtRzKwIxnYkQzsSDFXgdVhgVu725ws4tNM25EM7EhmZEdKfI7xaWBHMtmOlAiaxabJdqRM4I7YVOvTlPX4kCn+flP7+w38/Sb7+03t7+cvnaZQIlMyyrGEZZl4DpZ6GASWehqWcP7LaxxOPuUqYTkocDss+2QJltOL' \
			b'AQw8Lma0HiDxOQFLrAeQnBGWkaB5WOYlAZnAXWG5xxKbw4Hl5tnqg0GmGJNMbUwyMCaZbEwytTGJrQopVMgUY5KpjUlV4jlk2mEQZGZjkpQdgQlbkoEtycCWlPOV2BwUuR2bfbKEzWlzkoE5yYzMSYnTCWzCnGSyOSkRNI/NbE4qWNxrhqr2WLZzgugBQbQV' \
			b'iLY1RFtANK8+NfXyUzb5pVBBVBagmnoFapV4DqLtMAhE2wzRNkMUa1GFBDwwvshXQnRQ5HaI9skSRKeXpco7LJiqIRo5nYBoC4i2GaKRoHmIthmimcX9ILrHUqATRA8Iol4g6muIekDUZ4j6GqI+hwqiXiDqa4iWiecg6odBIOozRIvhrQdEPSDqAdE+XwnR' \
			b'QZHbIdonSxD10xD1gKgfQTRyOgFRD4j6DNFI0DxEfYZoZnE/iC65vOjknLkDrIpzxtTOGQPnjMnOGVM7Z0zIocKqOGcMnDPyDL9QYQZZ5hAbhkEQm50z8oaIWDhnDJwzBs6ZnK9ErMRwNRS0b0Vtnyyhdto7Y+CdMSPvTOJ2ArXwzpjsnUkEzaM2e2cKNvdD' \
			b'7ZLLj06ovQPUyppcU/thDPwwJvthTO2HMV0OFWrFCWPghJFnGqdBljnUjoKgNrti5A0RtfDEGHhiDDwxOV+J2nGp20HbJ0ugnfbBGPhgzMgHk5idAC18MKbLoI0EzYM2+18KLvcD7ZKrk06gvX3Q8qp0EXQJWrkNcoqg5csCtFwxKZSglYxy9A7PNE6DLDOg' \
			b'LdPGHG0kEqC1eR2EEBkJie/0Rb4CtBOlbgVtThZBK68ag1ZeE38+rwJtYnYMWikJWSJoE0GzoJUSAdqCy/1Ae1q8dOSgFS+qrb2oFl5Um72otvai2iJUoBUXqoULVZ5pnAZZ5kCrhkFAmx2p8oYIWvhRLfyoFn7UnK8E7bjU7aDtkyXQTntTLbypduRNTcxO' \
			b'gBbeVJu9qYmgedBmb2rB5X6gDQuueNA3Bl0TvwBxRQCvKwyre45jJWZjVZuNFczGKpuNVW025qpOoVoN4ZCXjwGzXUmhm/izl1XGua1t7TDI1rZsQlYwIStWPynfgOQ13hbf7Yv85aa3UeCHBbAVL2Mab3/ry4rgVtNGZQWjshoZlRPvE7vgYFRW2aicBDy/' \
			b'ES4blQtm9wP3wsuZDqpTXj+YflnLGgpdr6HQWEOh8xoKXa+haCULQoVni7xy5M/gaAGzjusRdZFrbj2iHoZVG+kEmOUNcTki1lJorKXQWEuR85UrEkelhtl9AH05aS3i9KIKjUUVerSoIvE7sRYRiyp0XlSRJDq/DjEvqigY3QvAesklTweF3gcCXV5R1LFk' \
			b'qyG1w5Da5SG1q4fULodqSO1kSO0wpIaHyOLXqKssc0NqNwwypHZ5SO3ykNphSO0wpMZG85yvHFKPS90+pO6TpSG1mx5SOwyp3WhIHZmdGFI7DKldHlJHguaH1C4PqTOX+4F224IoW+EWXxg7QXcB6PK305cfSQt8VQ1fBfi2mBG3+ASXyghmEAVJRqFF+vLz' \
			b'EAJiBRArgDj+pDyyIEyBmKcu/UjaDYOMpDOIVQaxAogVQKwA4pyvHEGPSzWYMm34ckSfLA2dp0GsAGI1AnFidmLoDBCrDGKZuUWi5ofPGcgFpxNAtv4RN44Rzx3BmX/hbgLWSy6iOgG6BrS+rf5YXMC2dgFbuIBtdgHb2gVsQw5VfywuYItJsYUL2MIFXGWZ' \
			b'64/DMEh/nF3ANruALVzAFi5gCxdwzlf2x+NSt/fHfbLUH097gC08wHbkAU7MTkE5loZsqU+ORM33ydkLXHC6X5+85PKqYwavKQDcHiuIxSNsa4+whUfYZo+wrT3CtsuhArF4hC08whYeYQuPcJVlDsSjICDOHmGbPcIWHmELj7CFRzjnK0E8LnU7iPtkHrJQ' \
			b'fcQUlOEXtiO/cGJ5YmgdC0OuhORI2TySs2u4YHc/JNvmMm22rbAMIPcoTshl2KYlkRsR2lZfQRt/Am2frbB2A6rsBJq2jW0TekrUTCCmR0uJkHoP69S3axNISoSUqFjVy4TntJ91ffh1sk2fJtttfylX+2rLt8gGGrvpc7PlN8hKBZ1QzqSZpULiZ5FuVuHw' \
			b'2fol1M4vpHrtBvXb0GgfpgpyH7eSTzgupopbvjS5jzoqM6mSG9rMTWrZblXLdgnNtEsq56YpQ6mcek8FtXHuH+L8f1tbSWXw57CpkmqlpXveZX5V5VU3qMCsK+3iSjw9Qy+UmGW6jyKznOHagqy3tLP5I+xdpdxpoDdUcr9b26sXaH7j+FsvoedLN8Rmh7GA' \
			b'Wb4xVn7RMUGpywqbD5TqFtJptWG6esXGWYmMto4ZWNSbGmgayCr/iLiVIWvYfwShFhtEsFHrBprqfdRX3flQVvnlVHfTF3enPslw3aZ4P5W11xnmdnc0r7Lye1Z3NLviH3rhn9y6n7MsJRsTw93MtvByf0V1JOrvRh3NSSNvVCPZQbW+O61cue46WqmurpVE' \
			b'97UUUy+rmxutu3M6qg9ST9kNu7iuMil6SX0VKmudbadXBZd6y4aXBXRXX0N3u4Ua1fZm2tVd9PZB6Gypr0r2pi/dxu6grwvoqrlG779eSFf9SVdvUVdvYjxwO7p6HYfUFq/xXroaTrp6i7raHa2u3p0vq1+3sKAxiuhURKjS/KmD7iE6uXbyDyif/xczUOEb' \
			b'zCoap5dwgKk9dLn5N1XUI3qR/IradldYr9X2KopNeCtX6VzPD6aXtxfM6q6KTpduUR32cA3w6epa7AtFjktjFnByxeVrN7RwYMJLy78mzIrqN+mqbh8R3kVVd3RonVR1QVUNUNVrNbic+16oaoCqhnlVDc3lHS+zummTq19gCMBKdrDm1koNb9K8ygs8r7+m' \
			b'hQRzeacKd9vr+fZSNHUMSnbj9vsrKxdxcLfKdRcLRjcts8aghXuDDcqmb1nZ+IV76pq7ofZMSNlZ23gB2YozbuhQ2/Uj2Y1lLZ1lOQhRd3lq46YHeFnn2MZxat92nw/zQnkl6qVP6rWpVbOH3n/y/iB7kPrlHvFO2DWduGZpliCTBKqak7JtUDZ38MrmGiHy' \
			b'aJTNNpdKtuZh/5DsgmZRs71Di0rIzmhRDS1jPid7uJXf36LS7WFIWcRYss/wTQwk3F9GRRKLRCen/VWIc13FrLGA8WJ3PWHinKoMFFRdqXL3qdkd25bbrM+qLhkIV2wL9h3M3FrtxaojPJtOqs7TXEww3Ms7y4NkwcxwZcgXCauiBNUh5S4rrBe8GxQmIuoG' \
			b'Prv++1zrunRKf7aSD3gofIoIP+VWbPOlcgfbcMVHJeup4u5Y7Hjl70eIO6zlH9SkIztqU5A9AtrF56wUvPnFpkTiTsV2FeZ4pZeiiPLv9ievNdtey5+62OPNhMvBHxugN/zJ2+V7+0pvI8BNc6+20GF5gGFHfzw/r+5tdS8EuZ0Iwk7vfcmivnjyLw1yNj13' \
			b'Qlm7B2XYg74XfXFjtk37dIheapI3/qUB2ZYUg+ES8yCfj21vl4vAY85wvT8hPtwB8dT+XfdPaO+uQDu1T1Pkr/dkgTPsHbqpWB63z+QTZvErkq3EXJ/h6vsKA6aZos2Mcwae7eDiOmGykKlI8K8Og3/T3HoA/3rIf/m9DwgCP/00Kw7pe/iDHTZ/qmP8hY5a' \
			b'Rqbpv70h39ko5ZW+nxG2yc03dxMsJvV2EM16Np0F0jaHoW3cy9xyAP92Xtt2EESpZLNCGarVnEqxlaYIPh19Hb898FwJeXiWtC2h7SZeVweIzh2B6FxzSAFya49Abm1zSAFy80cgN98cUoDcwuHLje1CBxQgt24Bue0wBFlAeqa5ZmAL6TCKuLxeqTCMjIbz' \
			b'tzqcu5I4XbM94LNus8l2CSqaQ/cIEOtolnDwYmV77+EGSPVu5x5XkqppDjhAqqM5xuFL1TYHHCDVHWYuhybVtjngAKnuMKk5YOsDe12OIEDUbfQWs3GdJBXV2svv45DMDVwHUVzsRbb89afg+VhsK0K2sDmba0YBefiLKirWLWqJpMs5QvQ99o7FNrpb+KMX' \
			b'luck/DUzz65tysSmcq69AA74GwSldlAtsi1Yy+Zqz1sBlYvF6cmUpikCEppRQlYMTmybMigHNeY9j9ZnB7w44dgB5zG25X1myosHzFOO78//H7otCHQ='

	_PARSER_TOP  = 'expr'

	_GREEK       = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'

	_SPECIAL     =  r'\\partial|\\pi|\\infty'
	_CHAR        = fr'[a-zA-Z]'
	_PYVAR       = '|'.join (reversed (sorted (AST.Var.PY)))
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
		('STR',          fr"(?<!\d|{_CHAR}|['}}])({_STR})|\\text\s*\{{\s*({_STR})\s*\}}"),
		('SUB1',         fr'_{_DSONEVARSP}'),
		('SUB',           r'_'),
		('CARET1',       fr'\^{_DSONEVARSP}'),
		('CARET',         r'\^'),
		('DBLSTAR',       r'\*\*'),
		('PRIMES',        r"'+"),
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
		'exp'       : lambda expr: _expr_func (2, '^', ('@', 'e'), expr, strip_paren = 1),
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
		func  = f'a{FUNC.grp [2] [3:]}' if FUNC.grp [2] else \
				FUNC.grp [0] or FUNC.grp [1] or FUNC.grp [3] or FUNC.grp [4].replace ('\\_', '_') or FUNC.text
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
	def expr_pow_2      (self, expr_abs):                                       return expr_abs

	def expr_abs_1      (self, LEFT, BAR1, expr, RIGHT, BAR2):                  return AST ('|', expr)
	def expr_abs_2      (self, BAR1, expr, BAR2):                               return AST ('|', expr)
	def expr_abs_3      (self, expr_paren):                                     return expr_paren

	def expr_paren_1    (self, PARENL, expr_commas, PARENR):                    return AST ('(', expr_commas)
	def expr_paren_2    (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):       return AST ('(', expr_commas)
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

	def expr_var_1      (self, var, PRIMES, subvar):                            return AST ('@', f'{var}{subvar}{PRIMES.text}')
	def expr_var_2      (self, var, subvar, PRIMES):                            return AST ('@', f'{var}{subvar}{PRIMES.text}')
	def expr_var_3      (self, var, PRIMES):                                    return AST ('@', f'{var}{PRIMES.text}')
	def expr_var_4      (self, var, subvar):                                    return AST ('@', f'{var}{subvar}')
	def expr_var_5      (self, var):                                            return AST ('@', var)

	def var             (self, VAR):
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
			self.erridx = self.tokens [self.tokidx].pos ## DEBUG!
			# self.erridx = self.tokens [self.tokidx - 1].pos

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

		expr_vars = expr_vars - {'_', 'e', 'i'} - set (AST.Var.LONG2SHORT) - set (var [1:] for var in expr_diffs)

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

		if pos >= len (rule [1]): # exception raised by rule reduction function or end of comma expression
			if rule [0] in {'expr_comma', 'expr_commas'}:
				return self._parse_autocomplete_expr_comma (rule)
			elif rule [0] == 'expr_int':
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
# 	a = p.parse ('pow (x,')
# 	print (a)
