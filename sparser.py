# TODO: Merge trigh into func.
# TODO: Terminal empty ',' allowed in all sequence types.
# TODO: Add 'max', 'min'.
# TODO: 1+1j complex number parsing?

# Builds expression tree from text, nodes are nested AST tuples.

# FUTURE: verify vars in expr func remaps
# FUTURE: vectors and matrices, Python long variable names, Python '.' members, assumptions / hints, stateful variables, piecewise expressions, plots

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

def _expr_func (iparm, *args): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	if args [iparm].is_fact:
		if args [iparm].fact.is_paren:
			return AST ('!', AST (*(args [:iparm] + (args [iparm].fact.paren,) + args [iparm + 1:])))

	elif args [iparm].is_pow:
		if args [iparm].base.is_paren:
			return AST ('^', AST (*(args [:iparm] + (args [iparm].base.paren,) + args [iparm + 1:])), args [iparm].exp)

	return AST (*args)

def _expr_func_remap (remap_func, ast): # rearrange ast tree for a given function remapping like 'Derivative' or 'Limit'
	expr = _expr_func (1, '(', ast)
	ast  = remap_func (expr.paren if expr.is_paren else expr [1].paren)

	return AST (expr.op, ast, *expr [2:]) if not expr.is_paren else ast

_remap_func_lim_dirs = {'+': '+', '-': '-', '+-': None}

def remap_func_lim (ast): # remap function 'Limit' to native ast representation for pretty rendering
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
		return AST ('lim', commas [0], commas [1], commas [2], _remap_func_lim_dirs.get (commas [3].str_, '+'))
	elif commas [3].is_eq_eq and commas [3].lhs.as_identifier () == 'dir' and commas [3].rhs.is_str:
		return AST ('lim', commas [0], commas [1], commas [2], _remap_func_lim_dirs.get (commas [3].rhs.str_, '+'))
	else:
		ast = AST ('lim', commas [0], commas [1], commas [2])

	if commas [-1].is_null_var:
		return ast

	raise lalr1.Incomplete (ast)

def remap_func_sum (ast): # remap function 'Sum' to native ast representation for pretty rendering
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

def remap_func_diff (ast): # remap function 'Derivative' to native ast representation for pretty rendering
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

def remap_func_intg (ast): # remap function 'Integral' to native ast representation for pretty rendering
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

def _expr_curly (ast):
	if ast.op != ',':
		return ast

	c = sum (bool (c.is_vec) for c in ast.commas)

	if not c:
		return AST ('vec', ast.commas)

	if c != len (ast.commas) or len (set (len (c.vec) for c in ast.commas)) != 1:
		raise SyntaxError ('invalid matrix syntax')

	return AST ('mat', tuple (c.vec for c in ast.commas))

#...............................................................................................
class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJztXW2P3DaS/jMHZAZQA+KrKH9zEm/WONvJOk6wh0FgOIlzCC725hx77w6L/PerqocUSUnd6p7pme6eaQynJbH5UlWsh29VVF9cffb86Yvvvv2s+ezpi1f0+ezpc/r89jv5/NtLifr6K/p89fLpV3+l61++e/EFRz75C3/3+eOX9PnN45dPXjzjMr568fXL' \
			b'J6+/+O7ls//gtC8ffxEvKl41Z3ry1evnj6nAv8eHz6un76unb4YnKZVr+ZzK+fcnr/j221cvhdzP6fOFEP29UPRvb9//zFm+fv78ccr6MmcdiOabx8+/oc8nL77MRH35+bNvnz3+9q8xPtPHT99XT5k+FtCrmPmVUPEFVcExT/4m8pXLN89E2l8+/f7pl084' \
			b'zZdfvxJGHkdOVMrIN0/+/gWz+c3Lp8+fcLZXX9PHT28+vP34+h8fXv/8429/fHzzgaL++PTjP+Xm7f/+/uH1uzcfX3/4x/+MHv9Iz398+v3tkPaXT+9/ev3+7X+m55/+8e7dm5zyR7otSn7/6V26/fj2w3D/44c3P/3X249DGZ8+/PZ/Re1DXZQs3f9OTLxP' \
			b'D29+HIj7PdP9y5ufPpZkZqqGigvSfvt1iP31/ZDv3affXv/67vf0+POv/8y3v/wysJX55wx0M1D288+51Lf/ne6Hu89+aK4uVsY0prtscBP4RjUrLdeuuQhN31CE8U1/meIkZnhcKclk5d9SXneZn9v8SDd01ZrL1BSvOy5Vh8sUHSNzzEobuevwoT3VdTnE' \
			b'KIpITxTPN4rLVv1QdneZomNkjqHy+Y6yCvVB/i3VCb6G5zbH0A3nZUk1hsozKItvmByHD4sq6G6lvNz1VD0zw+y1l0OUKR+VjTccx3ckPhJZlAWeuABiOlTRbvLkq5jpU1/FdOUTUS0sURUgiO4uWnkQBUETU0R6XoHsltiJNffpyxg5PKyUtJGixtANNS7z' \
			b'SmKxokzchGjM+e9ZN+12ydo61UpBh9qodtwupm2MKpWPSU3xOcYjxuSYDjE2xwTEuBRDqiWSUfgwbVJZo6KSUpR8GFac+F0rt3Tn5N+axEB8tvl5JTrVyz+J9fJyuKMbL60FBfR8w0SR4kBBqS1VhFgEbxC8ZCzmaJKcii2T4kg75c7jY5VSMypRE33DqFX4' \
			b'gh6tqBNp+oUp2soMTc7aElvKDCpHvJlu0Ln42NYRIdfSN1ZEoqkKlW50vKHq0p2GqjJ8NYmUG05fllH0TNGXdapxivRMj9JyWliOjEVZ5UgmZSaOn3I8hETFE4XUIV+RakhG6UypB+oa7oN923jVeN1413gvBZGmKxarN423rDSkJ5aIJrl3zCBhovNN14my' \
			b'k9ip17KkqtzSJFGSIddJCagKyttQuY0PjadcbdNJAxH8Sb6kno6CapxunGkcJXUNNTvBQYn6sLLoJlAwTbBNcE3wTSC6QxP6pifKu6Z3P7BycgsZ/ry60HK9ID4V831B3PIzccyXTj5D/K6XJ4/8XsVYEgU9n6YoPNjkpmRhKHCowaFOHOqYSkR1EmxZ8GPR' \
			b'uFYeO9t07j7psXWRSw8uoawW2noRooIriaaejUZWGl7uLaqDBftQ4Q4y6ToIwQDVRhSZen7bHg3hVzLKPYAWolYAHI3NrQBQHhGJDiT6gsTQdH0T2iaoYyK0O0ZVNgEjh0sjR4Sh4K4QJOG1i/0TYOsBW4eRRyEbVy3FSKPcV1xcxMHXhwfRDVx0aONOxQmY' \
			b'KPKeyjZtLDTssVDdo1AnFLvQuL5xvnHdvW0j4lU/IF7NA+LVPhReLxyGcoUhSWENE+IlTp0DBpoQ13lIGjAW9dKX9KrpddObprfcVSNh74bFI63s75vkZBFMfN0njjpm6H6wEu4PK8QF83LSLKgTZ4H3r7R0ZtIYvOvDDJ0O+QbkW7lWa4wr3vnRk228DksO' \
			b'bJDcxgQ378to7Mto7MtoqV7hmSf6eAY5Cmsm3rngr40CW7xJe9nEPQKTlwf3dNA2ca5tZfA9FrJkj6ZoNN7JQOuIfh3XKpz3MECcPz7iCH2YZHX9cTVwaG+pNwhx6xGo1w4dko6dlrTQPQXzFe/q6AewpXHF+1YaG1YPg1/lHwSjF7En9aEesrv2fuNWS2e1' \
			b'R3BMN3V5i07HXTWWrUuzMxd3gj2SuWjBcXqUzIyebf0cMI0KUku1iL/i5b7GOh8zsh5ddI+9gT6O8T3mZdTG5hJrYjOdSkrc2CIcZmL50eDRxNm2OSWb6hUvDMwJLQxkRWDu0y4GL1x0XFgYLCwMFhZ0GWWR9KqDrilzn7srXkCJWDq/RhCyimJRjZZatk1r' \
			b'KwOzpIHpT3Aeu6dOpjBHw2sAyRYNSzWZclxy6FQekqFCtbUIlC+faQCXXhY9coe0uktSEiE6aen7Lifn73Uf4ABwZ3ABlAN0IcRusMdMo8dMopdOcba3IObtaY3NTORkcsIEY5iwGCbYs4+RYeAgY+P+kj22TQLudGVkQzP0oJTKtoBtMdFj/FtMLi0QbiOm' \
			b'TTmJhCL0EfE9lKUXSYzmhiQ0B6E5CM3dX9TIkHmP+WPlllaUT6rIRT1yqfuHAjkokIOKWPQRFhpi44TLQyk8lIIuRDB2az38VjzSu5i+O2mjwBXz2oHXTqSEtRDWYp2wV7vzUL2SnoqDpAJyh5ghnL48+lNnIZw4C6xHffR0baOraytDXdtctUICOq+hTJ4G' \
			b'FnUNLKO/A/2g0wzDnxUGQxwT0SfOCmfKFCaRmHjH3tMUMjHJB1mkOjgVjhnvZUBiLoiNlphoadnSEhst8dEy78w3fc88MpO8rGE22X2bfbfZcZt9ttm3nV3x2BuKPWDZ/ZWdL9nJkT0c2YeQPfbY6MIGF/Z9Z8d39pdm52L2peXNGx5GeRuDvcV5UsTu1ez1' \
			b'znrEHhHsucYOfOzZxcYvdr5lz1ve6ud9ft4CZ8cL9rpgjwt2t2BfC3a06FtqP8/y4wMkVMPK81EOPh7E95aUakW0rEhCdEdCWvEhGxYfyZc/EFZ8GIOP/nSSzvOHRLdyvsPHv5XjA1FBzkmsAv/TMynYithY9W5IJ2mZRT6W4qV5mYJVx8cvuOKVHL0yqNrx' \
			b'RWlOw498pITSES6Kwvg0U+B/ytdbKZBPfVHpXIOSg1lMMx9/6oRpOaxExVGM4W84s6Th4zdBTsusnIpsESukhSuhk+XENCiuhQnsWGItUvKBHz7I00tmHImiaBr3Vj2fO2PxKRYzk0Rp+JjVwETHdFHRNvzQ/MurRytoCl3NnzyGMgpZiMso1LePvBJ2bhe0' \
			b'zSGtjWi7JaRdF2WLyGI9Z1oraCkgiy8RWgKHjC1+LAAl6eWzgBS3awpLsCrTxhze4cKn9yK4jELFQBbDaoyncSEjUNWIyskUOFqDKKG/glRiagoqKcYMiIoJlzGlMpQyWRWaVPuIezzStkfcFZBm0FX9KZOuM6qODVUyWvFniSoLVNmMKlujytaosoIqW6PK' \
			b'5rCIKjsOgio7RZXdjKpRIZtRNSRT4GgdquwEVZGpGVTZGlVIuAWqbEbVQNaWqDJnVB0dqnpBVT0NlEcrl4SqvkZVX6OqF1T1NaqKsIiqfhwEVf0UVf1mVI0K2YyqIZkCR+tQ1U9QFZmaQVVfowoJt0BVn1E1kLUlquz2qDrgOkzdYCm2CXBLSzF7uOXYIvj4' \
			b'ZRQ9t0oJPnm0cong49sCfNyKRSiBKHnlswBilXgBiKOypTyHSwHEuCKTykGwQd0mlTAG5rjQjcDMyeLKTGQxBafU04KtCp+J1yk+pSTQGiGahLgIUSkREC0I3A6i7gzRU4WoEYiaGqIGEDUZoqaGqKlCBVEjEDU1RMvESxA1k+K9w2UGogYQNYAoRs2YawzR' \
			b'UaGbITokSxA18xA1gKiZQDTyOgNRA4jmUTQJcRmiJkM0E7gdRP0ZoqcKUVkY6nphqLEw1HlhqOuFobZVqCAqi0RdLxKrxEsQtZPivcNlBqJYKMoFdZtUwgSio0I3Q3RIliA6v3CUelqwVUM08joDUawdpewI0SjEZYjm5WNB4HYQ7c4QPVWIOoGoqyHqAFGX' \
			b'IepqiLoqVBB1AlFXQ7RMvATRSRCIunmIOkDUAaIOEEXyMURHhW6G6JAsQdTNQ9QBom4C0cjrDEQdIOoyRKMQlyHqMkQzgdtBNOwXooXd8y6AGjZitX04cJVNIV1vCmlsCum8KaTrTSHdV6GCq2wQaWwQ9UAsX8ZZlkDbTyrxDheAlstMmMVOkcZmkVxSAf3M' \
			b'+rQutl9cog4EJOTO7x+JiFrwViM3MjyDXGwhSdkRuZGNZeTmXaSCwBnkev1IdvWmAO4ZwAS+6FtwbRjDBeGIBttubrw1G+z8dw1kdUtglldM8ksQSQXEMMkRBa7l0col4ppvC1xzOxahxHVM7OWzGImr9AugHhUv5TlcpiOx1A+aDeo2qYQxpMsSVcw6xrSs' \
			b'NdUI25mOiG0RzRTbUmdkscJ24nuKbSkJdLOPhreC7yTXRXxLqcB3QeR2I7Nqbzw0Hx2mH84E2gC5tUuBgUuByS4FpnYp4HYqQoVc5PPyWSK3TL+EXD2pwTtcZpALLwO5gFCTSpggd1ToxpE4J0tonfc6kHrw7t0RWiOvM2iF44GUjZE4yXEZqdn3oCBwS6Tu' \
			b'4NJzXuceF0xlt9jUu8UGu8Um7xaberfYmCqUMJW88llitEy8hFEzKd47XGYwit1ig93iaGONd2OMjgrdjNEhWcLo/G6xwW6xmewWJ15nMIrdYpN3ixPlyxjNu8UFgVtidAcHoaPC6OYl7kOBqWxHmXo7ymA7yuTtKFNvRzEWilDBVLajTL0dVSVegukkCEzz' \
			b'dpSUHVGK3SiD3SiD3aicbwzUUbGbgTokS0Cd35Ay2JAykw2pxO0MULEhZfKGVBLjMlDzhlRB4E7LWrWD69EZr0eH107w2tV47YDXLuO1q/FahwqvneC1q/FaJl7C67R473CJeO0yXjvgtQNeO+B1yDfG66jYzXgdkiW8dvN47YDXboLXyO0MXjvgtct4jWJc' \
			b'xmuX8ZoJ3A2vp+rUdMYr4zUIXkON1wC8hozXUOM1VKHCaxC8hhqvZeIlvIZJ8d7hEvEaMl4D8BqA1wC8DvnGeB0VuxmvQ7KE1zCPV3geCmM1XiO3M3gNwGvIeI1iXMZryHjNBO6G1z17OJ0NP4cBrhh+TG34MTD8mGz4MbXhx/RVqIArhh8Dw49818pFj7Is' \
			b'wbefVOIdLhG+fYYvDD/RS9jA8JPzjeErsdwaOclmCA/JEoTnLT8Glh8zsfwkjmcgDMuPyZafxMcyhLPlpyBwNwjv2QPqDOGDQJhVUcRdQtjCxmOzjcfWNh5uniKUEJa88klSl++QRPd1lgUIj2qwMPPYbOaRGgBhCyuPhZXHwsqT840gPFPyRgTnZBHBdt6+' \
			b'Y2HfsRP7TmJ4imAL+45tBwQneS4i2GbbTkHgbgjes4PUGcGHQbCcCrD1qQCLUwE2nwqw9akAbpsiVAiWUwEWpwIsJtAW3hdVliUEq0kl3uESEZy9LyyOBlgcDbA4GpDzjRE8LXkzgodkCcHzBwQsDgjYyQGBxPAMgnFAwOYDAkmeywjOBwQKAndD8Nl/6l4g' \
			b'WKy1trbWWlhrbbbW2tpayw1ThArBYqq1MNXKd61cdF9nWUKwnlTiHS4RwTojGPZaC3uthb025xsjeFryZgQPyRKC5622FlZbO7HaJoZnEAyrrc1W2yTPZQRnq21B4G4I7vfrZjF5/8vecGz5DS83QrOqAK3uOahFV7gBq5OyXkDNl3RS1leg5gYvQuWCgRj5' \
			b'DFghxx8exm/s1hmXTtD6SVXC8QBtvmVeWQ/l14xjbeDBgHBTFDQ5WzupgQFXoFzxwdfpKduhvIh0kdUU6VIjWK+RnvifIl1KAuHpvG0U8iLSpUQgvSBwJ6Tr/TtUHdtwrR7MiK1lxNb1iB1fhqTziK3rEdtLmiFU4HbILp+dwtfyXgNxei5zLTk963EQp+c8' \
			b'aOs8aGsM2hqDtsagnfONnZ4nISyeWBjKSn7P8+O2xritJ+N24nmKZo1xW+dxO0l1Ec06j9sFgbuhec9OV8cG5QeCYyuDtK0HaYtB2uZB2taDNDdGEaqZt4zQ/MkzbwzPFsNzlWVp5u0nlXiHS5x5+zzzxrBsMSxbDMs533jmPS1588x7SJZm3vPjscV4bCfj' \
			b'cWJ4ZuaN8djm8TjJc3nmncfjgsDdELzJJctWIC5fxHjG8T5w3N7GhFu8tFTtpaXgpeUxJnv4L6rsqMV442m348DkyE31shrx1VLw1ZLvWrnoPiaOWWYQzYucYcI9CTLhzh5bKntsKXhsKXhsKXhs5Xzjifa0ZG4jrnv+PTZDsjTDnnfaUnDaUhOnrcTwzAwb' \
			b'TlsqO23JOi/KdHmWnR23CiJnUG3DI+4tI7h7wnYIsxjfsxvXGd0TdJu7GqnF1GxrU7OFqdlmU7OtTc22r0I1Uoup2WIhbWFqtjA1V1mWRup+Uol3uMSROpuaLUzNFqZmC1Nzzjceqaclbx6ph2RppJ63NFtYmu3E0pwYnls5I70F1Wm0jqwsj9bZ2lwQudto' \
			b'vWcHrxNHsinQ3J0oop1Ynl1teXawPLtseXa15dm1VSgRLXnlk1rAwfLsYHmusiwgelSDg+XZZcuzy5ZnB8uzg+XZwfKc840QPVPyRkTnZB1qVYn/OVw72J/dxP6c2J7iOhUG0iOsk2AXYe2yCbqgdDdYu+YqnR6ugA1UD5AeMKyye+ZarHbVSxtn39i4y8Fe' \
			b'uwZfbgZX27ySscTPDHYG3JRYqU/kzr2CO8GlxEoJjpWvnCGXQMAqP36Z4qY3KW53VJZbn5V43asTR4q77pXZ5SsTSz2d0dGkoKVest75W9Y7eYF/1D4998rQsLMOUhyvRde+KpTS85okHl/eWi/5Rf2zurmmbz9O/cRQ6Ac9VXHxNPvWTzWzbblZX2MDrH3l' \
			b'p9SO/110WM3r8Zr+dk6Xm395/2glVQe+/onfzro75b5x1+q36F7NjqrsoM78M5Wy1bCpy6UyWCd4pV+pNz2Tqh6dmvPU3u27O97wjuiozizPXVSaZQwLG+S8oZvOM8a2UvM0axx33eGWtXtjv73nTvtaHbXdYiJhj7mzLjWYxbI/LVZr1ry7Ti4GLe6WJhks' \
			b'4vWdc9kr93elt/uabOxTZ/VJT3636HHV3Jsnbtrr7qar7gYTYpLMwRZitiGZH2o5xr9dzb9TeKKaucU8QMn5yu4wyzNU7q+rlepwWmkOqZjm4Sgnr5j6wygor3Gly3ThJkqqj0BJfdN3TR/O2nrL2uoHbcUmOv7vXnPNXjTXHHrQ9+dx//a2YwdFPdTW7M2U' \
			b'0x5aObuzct6BcvYnqZwHtFtBOQ801D8s5ZQjvaennLdt3LqTzX8i74HbtO52ox9vlNZxf3kfdiwlfkjb2rEUG7IcfvdxSwOWvZYOt5XLzo3VWO+/h11U2Wg04Vbbo+pG7eXL9ZWXc49eE7on/Y1ebbfkOzBjc+XfRmd9ZZZmVVZ3jwjqorFbGqXOGrtfjQ3Q' \
			b'2HAjjQ33SGN7aGxY1ti+uTq839UtT1lt2MM8gOV83NPVUhtvc3rK/p839Ffh359tm6tD691d+/ntpG8no2t36du3o46pw+vYIfxJ1/ljdzKZ4eFhjc6ZO9Y5rvAaKsfZbkPr3E5Kp2RxRhnXjLJePVqhmehq5De3Ncn43OOtm/xl1eONj3Nvt5sHaP+IACta' \
			b'Zs5atmFcdacwqPLpIneUakadGTc1Xbh1/aNVEJ2zZ53boHP+JHTON0Loyeica66UHPGzcuyJ1cGzuHmDxIhayJFrUQ8t80Ev58Pxq8Y7aSRvvuyy87KP3ZWd1E52VHgQjfrEIjdy3vAamsS5rrsPsofdju3VhVO6ttrRoFZLbbxTA2/d09xps5ZNypK/Zs9w' \
			b'nYnOnTVibEGCtQGuA63aBNGDzLNMSB59D1zLbowtixKM9yl32WhDl+5HhYmYREQF68N5Z1WXTukvVvLKHyXvDDL4bbfi5DCVPTrWKweCotOQnLbFCVp+U4WY0ORHRumTrbkpyGEB7eP3rBx89oXUNX7NdlecVmGOV3pfFFFnut2fVGs2VUttvUvNphn/8eb1' \
			b'mj+pXU6Ccze7ngA3z73aQIflWYed/PEyvnrmDiT/CUFuK4JweHxXsmg2OPuXpj3rvndCmd+BMhxr34m+eGzHpaM6RG/XrP9LU7QNKUYTKOZBXlLt75aLwBPRcLM/IT4cgPi+ufGf0N5fg3YXZslvd2SBM+wc+rlYnskv5BNm8XO3XmJuznC7gWl5t+ZaxjkD' \
			b'L4Fwc5MwW8hcJPhXx8G/ae48gH895r9+i0iUBX6Ia1EiMvzwa0BsfgHI9KUftZjSGWZ2ebEjkZm4JO03ia5rDhYsXr/C5rYymrVtPgtkbo5D53i8ueMA/u1WOreFLEpVW5TLWLmWFIv3cIrQpc8u3W8ZeO2EPLxq2pTQzdVYBwjQnYYAfXNkAdLzpyG9rjmy' \
			b'AOl1pyG90BxZgPTCSUiP94+OK0B6/X6kt8U0ZQ8ytM3NA2+rjqOY0RuVii2UycT/rid+1xKqbxYDXiu3TcrFoOIu6g4Bwp2sKk5BuLxTfNQBsj34iuVasrXNcQfIdrIyOQnZuua4A2S73arn2GTbNccdINvtFkRHvIvBZrnTCBC4j5ZoNj7TSjV2H538/A9v' \
			b'Z8AQESXGiRy/VyoE/iyONyEbHyJQubUgd5IX5wvRPhkK46OPIwG/Wcjy2oRfdhbYEE75eCudmyQAdvyCl7LJqWl4r9jkVwcoh+L4pRujlNyInNo2ZVAOWscvQLAhW+HF9sZ2tw7TVT5mrjoxfHWU44fL/we5Ax+S'

	_PARSER_TOP = 'expr'

	_GREEK      = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'

	_SPECIAL    =  r'\\partial|\\pi|\\infty'
	_CHAR       = fr'[a-zA-Z]'
	_PYVAR      = '|'.join (reversed (sorted (AST.Var.PY)))
	_TEXTVAR    =  r'\\text\s*\{\s*(' + _PYVAR + r')\s*\}'
	_ONEVAR     = fr'{_CHAR}|{_GREEK}'
	_DSONEVARSP = fr'(?:(\d)|({_PYVAR})|({_CHAR}|{_GREEK}|{_SPECIAL})|{_TEXTVAR})'
	_STR        =  r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPYONLY = '|'.join (reversed (sorted (AST.Func.PY_ONLY)))
	_FUNCPYTEX  = '|'.join (reversed (sorted (AST.Func.PY_AND_TEX)))

	TOKENS      = OrderedDict ([ # order matters
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('TRIGH',         r'\\?(?:(a)(?:rc)?)?((?:sin|cos|tan|csc|sec|cot)h?)|\\operatorname\s*\{(sech|csch)\s*\}'),
		('FUNC',         fr'({_FUNCPYONLY})|\\?({_FUNCPYTEX})|\$({_CHAR}\w*)|\\operatorname\s*\{{\s*({_CHAR}(?:\w|\\_)*)\s*\}}'),
		('SQRT',          r'\\?sqrt'),
		('LOG',           r'\\?log'),
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
		('INEQ',          r'==|!=|\\neq?|<=|\\le|<|>=|\\ge|>'),
		('EQ',            r'='),
		('DIVIDE',        r'/'),
		('EXCL',          r'!'),
		('AMP',           r'&'),
		('DBLSLASH',      r'\\\\'),
		('COMMA',         r','),
		('ignore',        r'\\,|\\:|\\?\s+'),
	])

	_FUNC_AST_REMAP = {
		'Abs'       : lambda expr: _expr_func (1, '|', expr),
		'Derivative': lambda expr: _expr_func_remap (remap_func_diff, expr),
		'Integral'  : lambda expr: _expr_func_remap (remap_func_intg, expr),
		'Limit'     : lambda expr: _expr_func_remap (remap_func_lim, expr),
		'Sum'       : lambda expr: _expr_func_remap (remap_func_sum, expr),
		'abs'       : lambda expr: _expr_func (1, '|', expr),
		'exp'       : lambda expr: _expr_func (2, '^', ('@', 'e'), expr),
		'factorial' : lambda expr: _expr_func (1, '!', expr),
		'ln'        : lambda expr: _expr_func (1, 'log', expr),
	}

	def expr_comma_1    (self, expr_comma, COMMA, expr):                     return AST.flatcat (',', expr_comma, expr)
	def expr_comma_2    (self, expr, COMMA):                                 return AST (',', (expr,))
	def expr_comma_3    (self, expr):                                        return expr

	def expr            (self, expr_eq):                      	             return expr_eq

	def expr_eq_1       (self, expr_ineq1, EQ, expr_ineq2):                  return AST ('=', '=', expr_ineq1, expr_ineq2)
	def expr_eq_2       (self, expr_ineq):                                   return expr_ineq
	def expr_ineq_2     (self, expr_add1, INEQ, expr_add2):                  return AST ('=', AST.Eq.LONG2SHORT.get (INEQ.text, INEQ.text), expr_add1, expr_add2)
	def expr_ineq_3     (self, expr_add):                                    return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_mul_exp):                return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2      (self, expr_add, MINUS, expr_mul_exp):               return AST.flatcat ('+', expr_add, expr_mul_exp.neg (stack = True))
	def expr_add_3      (self, expr_mul_exp):                                return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_neg):                return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_2  (self, expr_mul_exp, STAR, expr_neg):                return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_3  (self, expr_neg):                                    return expr_neg

	def expr_neg_1      (self, MINUS, expr_diff):                            return expr_diff.neg (stack = True)
	def expr_neg_2      (self, expr_diff):                                   return expr_diff

	def expr_diff       (self, expr_div):                                    return _expr_diff (expr_div)

	def expr_div_1      (self, expr_div, DIVIDE, expr_mul_imp):              return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2      (self, expr_div, DIVIDE, MINUS, expr_mul_imp):       return AST ('/', expr_div, expr_mul_imp.neg (stack = True))
	def expr_div_3      (self, expr_mul_imp):                                return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_int):                      return AST.flatcat ('*', expr_mul_imp, expr_int)
	def expr_mul_imp_2  (self, expr_int):                                    return expr_int

	def expr_int_1      (self, INT, expr_sub, expr_super, expr_add):         return _expr_int (expr_add, (expr_sub, expr_super))
	def expr_int_2      (self, INT, expr_add):                               return _expr_int (expr_add)
	def expr_int_3      (self, expr_lim):                                    return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                           return AST ('lim', expr_neg, expr_var, expr)
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):   return AST ('lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg):  return AST ('lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6      (self, expr_sum):                                                                         return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQ, expr, CURLYR, expr_super, expr_neg):               return AST ('sum', expr_neg, expr_var, expr, expr_super)
	def expr_sum_2      (self, expr_func):                                                                        return expr_func

	def expr_func_1     (self, SQRT, expr_func_neg):                            return _expr_func (1, 'sqrt', expr_func_neg)
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_func_neg):  return _expr_func (1, 'sqrt', expr_func_neg, expr)
	def expr_func_3     (self, LOG, expr_func_neg):                             return _expr_func (1, 'log', expr_func_neg)
	def expr_func_4     (self, LOG, expr_sub, expr_func_neg):                   return _expr_func (1, 'log', expr_func_neg, expr_sub)
	def expr_func_5     (self, TRIGH, expr_func_neg):                           return _expr_func (2, 'func', f'{"a" if TRIGH.grp [0] else ""}{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func_neg)
	def expr_func_6     (self, TRIGH, expr_super, expr_func_neg):
		return \
				AST ('^', _expr_func (2, 'func', f'{TRIGH.grp [0] or ""}{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func_neg), expr_super) \
				if expr_super != AST.NegOne else \
				_expr_func (2, 'func', TRIGH.grp [1] or TRIGH.grp [2], expr_func_neg) \
				if TRIGH.grp [0] else \
				_expr_func (2, 'func', f'a{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func_neg)

	def expr_func_7     (self, FUNC, expr_func_neg):
		func  = FUNC.grp [0] or FUNC.grp [1] or FUNC.grp [2] or FUNC.grp [3].replace ('\\_', '_') or FUNC.text
		args  = expr_func_neg.strip_paren ()
		remap = self._FUNC_AST_REMAP.get (func)

		return remap (args) if remap else _expr_func (2, 'func', func, args)

	def expr_func_8     (self, expr_fact):                                   return expr_fact

	def expr_func_neg_1 (self, expr_func):                                   return expr_func
	def expr_func_neg_2 (self, MINUS, expr_func):                            return expr_func.neg (stack = True)

	def expr_fact_1     (self, expr_fact, EXCL):                             return AST ('!', expr_fact)
	def expr_fact_2     (self, expr_pow):                                    return expr_pow

	def expr_pow_1      (self, expr_pow, expr_super):                        return AST ('^', expr_pow, expr_super)
	def expr_pow_2      (self, expr_abs):                                    return expr_abs

	def expr_abs_1      (self, LEFT, BAR1, expr, RIGHT, BAR2):               return AST ('|', expr)
	def expr_abs_2      (self, BAR1, expr, BAR2):                            return AST ('|', expr)
	def expr_abs_3      (self, expr_paren):                                  return expr_paren

	def expr_paren_1    (self, PARENL, expr_comma, PARENR):                  return AST ('(', expr_comma)
	def expr_paren_2    (self, LEFT, PARENL, expr_comma, RIGHT, PARENR):     return AST ('(', expr_comma)
	def expr_paren_3    (self, IGNORE_CURLY, CURLYL, expr, CURLYR):          return expr
	def expr_paren_4    (self, expr_frac):                                   return expr_frac

	def expr_frac_1     (self, FRAC, expr_mat1, expr_mat2):                  return AST ('/', expr_mat1, expr_mat2)
	def expr_frac_2     (self, FRAC1, expr_mat):                             return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_mat)
	def expr_frac_3     (self, FRAC2):                                       return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 4))
	def expr_frac_4     (self, expr_mat):                                    return expr_mat

	def expr_mat_1      (self, LEFT, BRACKETL, BEG_MATRIX, expr_mat_rows, END_MATRIX, RIGHT, BRACKETR):  return AST ('mat', expr_mat_rows)
	def expr_mat_2      (self, BEG_MATRIX, expr_mat_rows, END_MATRIX):                                   return AST ('mat', expr_mat_rows)
	def expr_mat_3      (self, BEG_BMATRIX, expr_mat_rows, END_BMATRIX):                                 return AST ('mat', expr_mat_rows)
	def expr_mat_4      (self, BEG_VMATRIX, expr_mat_rows, END_VMATRIX):                                 return AST ('mat', expr_mat_rows)
	def expr_mat_5      (self, BEG_PMATRIX, expr_mat_rows, END_PMATRIX):                                 return AST ('mat', expr_mat_rows)
	def expr_mat_6      (self, expr_curly):                                                              return expr_curly

	def expr_mat_rows_1 (self, expr_mat_rows, DBLSLASH, expr_mat_row):       return expr_mat_rows + (expr_mat_row,)
	def expr_mat_rows_2 (self, expr_mat_row):                                return (expr_mat_row,)
	def expr_mat_row_1  (self, expr_mat_row, AMP, expr):                     return expr_mat_row + (expr,)
	def expr_mat_row_2  (self, expr):                                        return (expr,)

	def expr_curly_1    (self, LEFT, CURLYL, expr_comma, RIGHT, CURLYR):     return _expr_curly (expr_comma)
	def expr_curly_2    (self, CURLYL, expr_comma, CURLYR):                  return _expr_curly (expr_comma)
	def expr_curly_3    (self, expr_bracket):                                return expr_bracket

	def expr_bracket_1  (self, LEFT, BRACKETL, expr_comma, RIGHT, BRACKETR): return AST ('[', expr_comma.commas if expr_comma.is_comma else (expr_comma,))
	def expr_bracket_2  (self, BRACKETL, expr_comma, BRACKETR):              return AST ('[', expr_comma.commas if expr_comma.is_comma else (expr_comma,))
	def expr_bracket_3  (self, expr_term):                                   return expr_term

	def expr_term_1     (self, STR):                                         return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_2     (self, SUB):                                         return AST ('@', '_')
	def expr_term_3     (self, expr_var):                                    return expr_var
	def expr_term_4     (self, expr_num):                                    return expr_num

	def expr_num        (self, NUM):                                         return AST ('#', NUM.text) if NUM.grp [0] or NUM.grp [2] else AST ('#', NUM.grp [1])

	def expr_var_1      (self, var, PRIMES, subvar):                         return AST ('@', f'{var}{subvar}{PRIMES.text}')
	def expr_var_2      (self, var, subvar, PRIMES):                         return AST ('@', f'{var}{subvar}{PRIMES.text}')
	def expr_var_3      (self, var, PRIMES):                                 return AST ('@', f'{var}{PRIMES.text}')
	def expr_var_4      (self, var, subvar):                                 return AST ('@', f'{var}{subvar}')
	def expr_var_5      (self, var):                                         return AST ('@', var)

	def var             (self, VAR):
		return \
				f'\\partial {VAR.grp [2]}' \
				if VAR.grp [1] and VAR.grp [1] != 'd' else \
				AST.Var.SHORT2LONG.get (VAR.grp [0] or VAR.grp [3], VAR.text)

	def subvar_1        (self, SUB, CURLYL, expr_var, CURLYR):               return f'_{expr_var.var}' if expr_var.var and expr_var.is_single_var else f'_{{{expr_var.var}}}'
	def subvar_2        (self, SUB, CURLYL, NUM, CURLYR):                    return f'_{{{NUM.text}}}'
	def subvar_3        (self, SUB, CURLYL, NUM, subvar, CURLYR):            return f'_{{{NUM.text}{subvar}}}'
	def subvar_4        (self, SUB1):                                        return f'_{AST.Var.SHORT2LONG.get (SUB1.grp [1] or SUB1.grp [3], SUB1.text [1:])}'

	def expr_sub_1      (self, SUB, expr_frac):                              return expr_frac
	def expr_sub_2      (self, SUB1):                                        return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1    (self, DBLSTAR, expr_func):                          return expr_func
	def expr_super_2    (self, DBLSTAR, MINUS, expr_func):                   return expr_func.neg (stack = True)
	def expr_super_3    (self, CARET, expr_frac):                            return expr_frac
	def expr_super_4    (self, CARET1):                                      return _ast_from_tok_digit_or_var (CARET1)

	def caret_or_dblstar_1 (self, DBLSTAR):                                  return '**'
	def caret_or_dblstar_2 (self, CARET):                                    return '^'

	#...............................................................................................
	_AUTOCOMPLETE_SUBSTITUTE = { # autocomplete means autocomplete AST tree so it can be rendered, not expression
		'CARET1'             : 'CARET',
		'SUB1'               : 'SUB',
		'FRAC2'              : 'FRAC',
		'FRAC1'              : 'FRAC',
		'expr_sub'           : 'SUB',
		'expr_super'         : 'CARET',
		'caret_or_doublestar': 'CARET',
	}

	_AUTOCOMPLETE_CLOSE = {
		'RIGHT'   : '\\right',
		'PARENR'  : ')',
		'CURLYR'  : '}',
		'BRACKETR': ']',
		'BAR'     : '|',
	}

	def _mark_error (self):
		self.autocompleting = False

		if self.erridx is None:
			self.erridx = self.tokens [self.tokidx - 1].pos

	def _insert_symbol (self, sym):
		if sym in self.TOKENS:
			self.tokens.insert (self.tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

			if self.autocompleting and sym in self._AUTOCOMPLETE_CLOSE:
				self.autocomplete.append (self._AUTOCOMPLETE_CLOSE [sym])
			else:
				self.autocompleting = False

		else:
			self.tokens.insert (self.tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, ('', '', '', '')))
			self._mark_error ()

		return True

	def _parse_autocomplete_expr_comma (self, rule):
		idx = -1 -len (rule [1])

		if self.stack [idx] [1] == 'CURLYL':
			return self._insert_symbol ('CURLYR')

		if self.stack [idx] [1] != 'PARENL':
			return False

		if self.stack [idx - 1] [1] == 'LEFT':
			return self._insert_symbol ('RIGHT')

		return self._insert_symbol ('PARENR')

	def _parse_autocomplete_expr_int (self):
		s               = self.stack [-1]
		self.stack [-1] = (s [0], s [1], AST ('*', (s [2], AST.VarNull)))
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

		expr_vars  = expr_vars - {'_', 'e', 'i'} - set (AST.Var.LONG2SHORT)
		expr_vars -= set (var [1:] for var in expr_diffs)

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

		if rule [0] == 'expr_comma' and pos == 1: # force (expr . COMMA) to (expr .)
			rule = self.rules [self.strules [self.stidx] [1] [0]]

		if pos >= len (rule [1]): # special error raised by rule reduction function or end of comma expression
			if rule [0] == 'expr_comma':
				return self._parse_autocomplete_expr_comma (rule)

			if rule [0] == 'expr_int':
				return self._parse_autocomplete_expr_int ()

			return False

		return self._insert_symbol (rule [1] [pos])

	def parse_success (self, reduct):
		self.parse_results.append ((reduct, self.erridx, self.autocomplete))

		return True # continue parsing if conflict branches remain to find best resolution

	def parse (self, text):
		self.parse_results  = [] # [(reduct, erridx, autocomplete), ...]
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
