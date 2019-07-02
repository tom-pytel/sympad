# TODO: autocomplete vectors, matrices show input
# TODO: Change vars to internal short representation?
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
			return AST ('^', AST (*(args [:iparm] + (args [iparm].base,) + args [iparm + 1:])), args [iparm].exp)

	return AST (*args)

def _expr_func_remap (remap_func, ast): # rearrange ast tree for a given function remapping like 'Derivative' or 'Limit'
	expr = _expr_func (1, '(', ast)
	ast  = remap_func (expr.paren if expr.is_paren else expr [1].paren)

	return AST (expr.op, ast, *expr [2:]) if not expr.is_paren else ast

_remap_func_lim_dirs = {'+': ('+',), '-': ('-',), '+-': ()}

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
		return AST ('lim', *(commas [:3] + _remap_func_lim_dirs.get (commas [3].str_, ('+',))))
	elif commas [3].is_eq_eq and commas [3].lhs.as_identifier () == 'dir' and commas [3].rhs.is_str:
		return AST ('lim', *(commas [:3] + _remap_func_lim_dirs.get (commas [3].rhs.str_, ('+',))))
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
			b'eJztXW2P3DaS/jMHZAZQA803kfI3O/FmjbWd7MQJ9jAIDMdxFsHGSc6xd++w2P9+VfWQIimpW90zmunumcFwWiKbpKqK9fClilSfXX724tnLb7/5rPns2ctX9Pn82Qv6/OZb+fzrhSR99SV9/unbl59z5OmfOO3J4wv6/PrxxdOXz7nsly+/unj6+vNvL57/' \
			b'N+e9ePx5vKh41Vzo6ZevXzx+dfHsbzHypIp9V8W+7mNSKz/lCdXzl6ev+PabVxdC5hP6fCnEficU/de7X3/kIl+9ePE4Fb3IRXui+ebxi6/p84snz795/vibP9Pt05dfZPo48qSKfVfFMn0Xz77886tY0yuh4nN6BKc8/avIVS5fPxcpf/Hsu2dfPOU8X3z1' \
			b'Shh5HDlRqSDfPP3b58zm1xfPXjzlYq++oo+3bz68+/j6tw+vf/zhlz8+vvlASX98+uGfcvPuf3//8Pr9m4+v3/72Sxn98Nu/BtE/UvyPT7+/64v+9OnXt6/ffPh7ir/97f37N1WkKPcD3RaP/fXT+3T78d2H/v6HD2/e/uPdx76STx9++b+Clv7JlC3d/04c' \
			b'/poib37oH/l75uKnN28/lkRnqvoHF6T98nOf+vOvfbn3n355/fP731P0x5//mW9/+qln693fywJ001P244+51nf/k+77u8++by7PVsY1pj1vcOP5RjUrLVffnPkmNJRA34XzlCYpfXSlAt9Z+bfrZuXOc7yI0g1dteY6VUeP8Fyr9ucpOSbmlJU2chfwoR09' \
			b'6zym0B3f+PTVeYxSLH2BJCXPC/3z2j45JuYUeibfUSVSR5B/S+ndeRVf5xS64bIsvcZQ1KAuvmHpOHxYPEIxAyJqYvVM8QPX/H/eJ+kyqky84TS+I5GSGDWejRh/qxrhOye7UaytUkYxsy5TiE5hgqu28e5sLRFRE2lNQ9+m+EpyqTUxgGdxffgyJvaRlZJ2' \
			b'I97PdEMi5zYgrq2oFBeNkpr8njWUFGyXbINcK8iSxA3lYy4NabUqVZBJTek5xSFF55QWKSaneKTYlELKJJIx+BBJnscUKK7R+GBJxZqMllu+U+nL8xilGN85+bc6cRbjJsdXol6d/JO8z8/7O7pppRnBbcs3TK1toPUkwrMIwAjtwMLKQM2p1I4qNlhKIzWV' \
			b'uxYfq0g63yo8h75hiCmoGUUttIZkZIomNL0msGhi/SZpIqWdmTarIqLrOsH3T6GohS7TI9bpRsUbely606CFG4V6GcvtGVU2JlGcks/rXMMcKU5ReboVliNjUVY5UU+ncSynQ0hUPXWF1FtfrhvD/SCLT3PDc/fcNa1pWtu0rmlD03YsTa6cclJi27SeqiFB' \
			b'UDfErBFIbNe4deO7JlB91HHZRgYB6v5Z/gRt0YLGu8ZTkYbqbbxqvG48PdGyPpNkBRWNU42jT9M4yuca1zIbhDBCAasJcaWbQINH2wSiNTSha7p106mm001HtdF9+J71klvF8OflGTHIMWJSMdNnxCrHrXzNAD7nMQjfdRJr8RUJAaktf32KcmjBettFSShI' \
			b'AgLQJrKnLXKxgE6AJw9mLKi2wqL3jQ93Rn1tG1mEctqASyftdRbit0palUYU6hZpzKBujcabu4nnAEE44NoDpWENORig1Yg+0IBu1XFQfclzsnvSQtQK6GpMm1sBoDwW+qBCJmT6AgUqbJpgj4ZKqLb2qWsG9L0It6CXMOFTJ4Ec6NMdeniFYvxoqUaK30nF' \
			b'O4tS8PcGamc+TlxsHNRFZRaq2+jYp66XrFShUieVt6ppqVJqiXXjfOPC3WwmYtfcL3bt/WLX3SN2z1yLcQkTMIXBJmDIDwHwDhi7OuTpMBJ1yNoJFjrbdK7p2qbz3I/FjKFfptEC+k6JTdaaxNSdYcczN3eAj3BH+CAWmJHTpd+eMv1sF9LSdQnK2aDC3JwI' \
			b'7S1ot9IE1dLiko0qemQb8zEqQ8FNzGtDb/XQsHpoWD00Wz24PrF6YNBRGJAUbFhsaY+WAS5jDPIa4S0uw01eHWCExhrhTg04ZzbaRCxYPgqaKKM0iouNIop3RHYaNg2AsnBklNFAhVlU0EfTnESTuaEOINhk/NCweaCD4sudnFVfstVG3w+rxSWbpjRsUveG' \
			b'ZRXuC69nccKggFlv7jBotUwyFoTF2GLL9jeWp9OQZ4tMbTTydskviRW0g7X4zKEOZ1AWkx8Xu9GAqVEnLVQtxC95ya6xVtfwgqIj7jDV6uA4Pesw/6M2NedY2prxHFHShv7TMJHKUYOoiXNoczJOyEue65tTmevLJN/cGTMEL0R0XCgYLBQMFgp0GRTBBLSD' \
			b'iil0Uuoud05+kxRkNcRyUhF/VqXFkYHfzsA9xpcQ+/Eg/c9RsMbTTlkPotfRaFIH6u+VZ4EHCYMhQ3iHQCAIj05Vd0ksJg4fGuMGD1x3VzKXPBTeVWzzuG4wrhuM64JUtHS3Rkt3GPQ79HSdLLUnOwPi3J7QcMsUjiYbTC36f4v+34opCGLyHEWvZ49qUc+d' \
			b'qoxX4EiDTKrbpgkfIG4BcQtUI1OEdZrvYfzr4gyqg0Z00pMPZngkKgdROYjK3VGUyAh4V5ljZZb2k096kIuq41JnD9VxUB0H5bDoECx0w8aZUwt1aKEOdCFpfC+wabGPpEV+F/P707XTXzKjHox6EREWMnHnCCcO9tbQcyU/VQoxBZQOsUA4cWF0J01/d8r0' \
			b's/p0cVPnOu7qXMtwtm4u10ICequ+TlV4LtiitK64RjfHXPSkGuExMYihD/3gpHDGfGGKSLNozKghaqIfMoGseHOfSLXcRcfsB2GZ6We5EPlrWnCsiYE1cbAmFtbMOX3P3DF7vCBhBlmavKeV5ck7lXmbMm9N5s1wvB+JtxHxXk/e6Mm7DXmrIe/q4y19vG+O' \
			b'fR/s9+CN3bw5mCXM0uWdGmwpYSMKW1DYDsFGCN4czfMf3lDMO7x5lzRvquLNdry5jv1d7JPifaZsh2fzNG95YAcYb0jlfQ+ho5ZrWXh8LqLlExN8xIEPrli6p262WZG4V1SGP32zIoGvqEZSMmgan8bgIqFZeckkH55Pjmg5B9LGv5VrccKHjwQQHavA54Xo' \
			b'wZ4PEIU+HyphWfKJB9AWuEo+T2SEoLUcapFHe74oPrQQrJzNWHlXVsTHJjo+s0QP7bxUxgeaqGY+JsJFtNArpySkcj6VwTVzYcpHklsFeSyRzI/k4ytOR5aoEsdnuZgdSu/4sIvhp3BOUquVN5EOykWBgMmFcfaH+ac0GttWHWdSwciBHc7Dp4R8YsLz6SLK' \
			b'bam1/t2uH61407i1dLX/4aGSgSfInwWevnm8lWBzO2NsCl/riLGbwtcVsTWLJ1ZwprMClES9XCKgBAcZURwtkCT55bPAEjdqCnN4KvPGEm3AhdXcAVUsMN1DivFUAmlYwQBNNZRyNgXuN0BJaK+wlBgao0mqsT2UEhmzYFIZQ5msCkaKYMTas+4ecR9AWkFX' \
			b'8x+ZVz3A6ajgZAVOtoYThie+JDjZGk62hpMVONkaTjaHWTjZYRA42TGc7GY4DSrYDqc+WzyhuQlOdgSnyNAEnGwNp0jGPJxshlNP1o5wMg9wOi44dQKneronURxET3Dqajh1NZw6gVNXw6nLYRZO3TAInLoxnLrNcBpUsB1OfbZ42QSnbgSnyNAEnLoaTpGM' \
			b'eTh1GU49WTvCye4Op0OtstRVF1rbYDa30DKHW2zNQo7XU7LWLyEnUS+XCDm+LSCHPDFngT0pKJ8F9qrMM9jTahgYe3IpsBfXW0LfGjQ4XHwqVWBxWOFWLOZscd0lDxnjUQOSwlIFycTnGJJSk0VJoDIRNItKqRGoLAjcDZXuAZWnh0oxevBniUoDVJqMSlOj' \
			b'0uRQodIIKk2NyjLzHCrNMAgqzTQqDVBpgEoDVCK9ROWgwu2o7LMlVJppVBqg0oxQGRMnUGmASpNRGQmaR6XJqMwE7obK9gGVp4dKWe3perUXjZE6r/Z0vdrjZkuhQqUs+3S97Ksyz6HSDoOg0k6jEks/ocHh4lOpEpWDCrejss+WUDm9FJRngIQBKiOfE6jE' \
			b'alDnGWwiaB6VeUFYELgbKv2CqBy5Q24Wm2EjPNlZcl8QGgShoUZoAEJDRmioERpyqBAaBKFBEMr2cwKpXFRdZA6noyA4DT1Ouc4E0wCYBsA0AKaSm3OVSK2rFLq2grV/eAJrmAZrAFjDCKyR2QmwBoA1ZLBGWc6DNWSwZgInwNqqR7L0H2M2MGZ1Y5KL8WrI' \
			b'Dcc0pLZTo6rZ4u67beyubwq/bKPAm+kspsC1LUjDFqSzLUjXtiDd5VBCmXdbil1I13ahKv8cjrthEBx30+MtbENChsPFp1IliovauEn0hK2IX1nGb5Kr4dzTkOA8bTeS54GcAZwjzxNwhulISqJhBdJRpvOQzhakgsjdxt/umuPvUaH4/kyMjRiRTG1EMjAi' \
			b'mWxEMrURKb7WETlLrBqUlc8Cq1X+GawOshvYkcy0HcnAjmRgRzKwI8VSBVaHFW4dbnO2iE8zbUcysCOZkR0p8TnGp4EdyWQ7UiJoFpsm25EKAnfDplo/LFlPD5ni7ze1v9/A32+yv9/U/n5+o2kKJTKloHyWsCwzz8FSD4PAUk/DEs5/eYzDxadSJSwHFW6H' \
			b'ZZ8twXJ6M4A8AyQMYBn5nIAl9gNIyQjLSNA8LPOWgILAHWG5xxab44Hl5tXqvUGmGJNMbUwyMCaZbEwytTGJrQopVMgUY5KpjUlV5jlk2mEQZGZjktQdgQlbkoEtycCWlMuV2BxUuR2bfbaEzWlzkoE5yYzMSYnTCWzCnGSyOSkRNI/NbE4qCNxrhar22Lbz' \
			b'ANEjgmgrEG1riLaAaN59aurtp6bNoYKobEA19Q7UKvMcRNthEIi2GaLF2Im9qEICvjC+KFdCdFDldoj22RJEp7elyjNAxQCikdMJiLaAaJshGgmah2ibIZoJ3A+ie2wFeoDoEUHUC0R9DVEPiPoMUV9D1OdQQdQLRH0N0TLzHET9MAhEfYaozxD1gKgHRD0g' \
			b'2pcrITqocjtE+2wJon4aoh4Q9SOIRk4nIOoBUZ8hGgmah6jPEM0E7gfRJbcXPThnDoBVcc6Y2jlj4Jwx2TljaucMN08KFVbFOWPgnJHv8JMURtVF5hA7CoLY7JyRJ0TEwjlj4JwxcM7kciViJYWboaB9K2r7bAm1094ZA++MGXlnErcTqIV3xmTvTCJoHrXZ' \
			b'O1MQuB9ql9x+9IDaA6BW9uSa2g9j4Icx2Q9jaj+M6XKoUCtOGAMnjHyncVF1kTnUdsMgqM2uGHlCRC08MQaeGANPTC5XonZc63bQ9tkSaKd9MAY+GDPywSRmJ0ALH4zpMmgjQfOgzf6XgsD9QLvk7qQH0N4+aHlXugi6BK1EvVwiaPm2AK0tQglaKSifHr8b' \
			b'R6C12AdRFZkBrV0PA4PWrnvQ2rwPQoiMhOAL44tyBWgnat0K2pwtglYeNQatPAaE1KBNzI5BKzVBQhG0iaBZ0EqNAG1B4H6gfdi8dOKgFS+qrb2oFl5Um72otvaiWpVDBVpxoVq4UOU7jYuqi8yBVg2DgDY7UuUJEbTwo1r4US38qLlcCdpxrdtB22dLoJ32' \
			b'plp4U+3Im5qYnQAtvKk2e1MTQfOgzd7UgsD9QBsW3PGgbwy6hl//cHUArysMqzuOYyVmY1WbjRXMxiqbjVVtNlZtDtVuCIey/Bmw2pUcuok/b1kVnDva1g6DHG3LJmQFE7Ji9VPxlBtMyQqmZAVTci5fHnob1c4kFMBWdvL4W19XBLeaNiorGJXVyKiceJ84' \
			b'BQejsspG5STgWXCrbFQuCNwP3AtvZzqqQXl9b8ZlLXsodL2HQmMPhc57KHS9h6KVIggVni3KyqdHxMRcKhfR85spyryxRIsfJo1glifE7YjYS6Gxl0JjL0UuV+5IHNUaZs8B9PWkvYjTmyo0NlXo0aaKxO/EXkRsqtB5U0WS6Pw+xLypoiBwLwDrJbc8HRV6' \
			b'7wl0eUdRx5KtptQOU2qXp9SunlK7HKoptZMptcOU2mFKjV+drorMTandMMiU2uUptctTaocptcOUGgfNc7lySj2udfuUus+WptRuekrtMKV2oyl1ZHZiSu0wpXZ5Sh0Jmp9SuzylzgTuB9ptG6JshVu8YewBugtAl1+cvvxMWuCravgqwLfFirjFK7hURnDr' \
			b'MZ9mojiXqkEsxeXTW3ynm/jT8SiCMAViXrr0M2k3DDKTziBWGcQKIFYAsQKIc7lyBj2u1WDJtOHNEX22NHWeBrECiNUIxInZiakzQKwyiGXlFomanz5nIBdETgDZ+kfcOUY8dwRn/nm7CVgvuYnqAdA1oPVtjcfiAra1C9jCBWyzC9jWLmBuhBSq8VhcwBaL' \
			b'YgsXsIULuCoyNx6PgozH2QVsswvYwgVs4QK2cAHncuV4PK51+3jcZ0vj8bQH2MIDbEce4MTsFJRjbZBSGpMjUfNjcvYCF0TuNyYvub3qlMFrCgC3pwpi8Qjb2iNs4RG22SNsa4+w7XKoQCweYQuPsIVH2MIjXBWZA3E3DALi7BG22SNs4RG28AhbeIRzuRLE' \
			b'41q3g7jP5iEL1SdMQRl+YTvyCyeWJ6bWsTKIKiE5UjaP5OwaLijdD8m2uUyHbSssA8g9ihNyzTpvidyI0LZ6C9r4FWj7HIW1G1BlJ9C0bW6b0FOiZgIxPVpKhNRnWKfeXZtAUiKkRMWq3iY8p/2s68O3k216Ndlu50u52Vdb3kU20NhNr5st30FWKuiEcibN' \
			b'LBUSv4l0swrn5O3WS6idX0j12g3qt6HTPk4V5DFuJa9wXEwVt7xpch91VGZSJTf0mZvUst2qlu0SmmmXVM5NS4ZSOfWeCmrj2j/E9f+2vpLq4Ndhk6RrpaU4r0yvqrzK35wCs660iyvx9Aq9UGKW6T6KzHKGawuy3tLP5pewd5Vyp4neUMn9bn2vXqD7jfNv' \
			b'vYSeL90Rmx3mAmb5zlj5RecEpS4rHD5QqltIp9WG5eoVO2eW78ycgUW9qYOmiazyj4hbmbKG/WcQarFJBDXoTXTV+6ivOvhUVvnlVHfTG3enXslw3a54P5W115nmdgdaV+HHrA60uuIfeuGf3LqbqywlBxPDYVZbeLi/ojoS9YdRR/OgkTeqkUzS+nBauXLd' \
			b'dbRSHUgr9Q0rpttBOfX9UFAmQ9+gkrbT24BLRWVLywLKqg/dhbaHU9Y7r6ilkio5hX4ARV1ASc2hldQ/KOktKemBetMFlPRQPqdeScODkt6SknYnq6SH81P1exIWNDQRnYoIVZpfY9DdRwfWTrZ/Nmyl/8WMT3i/soqGZ7uAc4vN07vqcvNvaqhH9CD5hbTt' \
			b'bq5eq+1VFJvwVu7AuZ6PSy9vC5jVXRUdKt2iOuxh9ufL1bWYSw/ep7mAAytuTbuhTQETHlj+pWBWVL5M6qpuHxHeRVV3dFY9qOqCqhqgqtfqcLn0nVDVAFUN86oamssDb6G6aXOqX2AKwEp2vNPWUg1v0nTKmzevv1+FBHN5UIW77b16eymaOgUlu839efsp' \
			b'F3FwWOU6xGbQTVuoW5m08GiwQdn0LSsbP3BPXXM31J8JKTtrG28OW3GlGwbUdv1ITlpZS1fZ6kHUXT70cdMTvKxzbON46N92Xw/zJngl6qUf1GtTr2aPffzksz/2KPXLPeJTrmu6cMvSKkEWCdQ0D8q2Qdnc0Suba4TIk1E221wqOXaHs0GsCo5FzfYOLSoh' \
			b'p55FNbTM+Zycz1Z+f4tKt4chZRFjyT7TNzGQ8HgZFYmFxyaO7ioqxKWuYtZYwHixu54wkU5VBgpqrtS4+7Tsjn3LbbZn1ZbcH1yxL9h3MnNrrRebjvBsOmk6T2sxwXAv7ywPkkXXAcnytkFfViWoDql02WC94N2gMhFRN3As9+/eWte1U/6zlbycQ8nbebT8' \
			b'KFp5hJfqHRyxFR+VnISNJ19xmpXfDSHusJZ/LJM+2Umbguz/1y5+z0rBB1tsyiSuVBxFYY5XeimKqPxuf/JYs+2xbr3XkwmXgz82QG/4k6fLu/SV3kaAm+ZebaHD8gTDjv54fV7FbRUXgtxOBOEU975k0Vg8+ZcmOZu+d0JZuwdlOF++F33x0LVNZ3CIXhp0' \
			b'Nv6lCdmWHIPpEvMgr4Ztb5eLwHPOcL0/IT4cgHjq/677J7R3V6Cd+qcp8td7ssAF9g7dVCrP22fKCbP4hchWUq7PcPXuhAHTTNFmxrkAr3Zwc50wWclUIvhXx8G/aW49gH895L98lwcEgd+QmhWHjD38Mg6bX8MxfvtGLSPT9O/VkHdolPJK78YI2+Tmm8ME' \
			b'i0W9HSSznk0XgbTNcWgbjzK3HMC/nde2HQRRKtmsUIZqNadSbKUpgk+fvk7fHnithDK8StqW0XYTj6sDROdOQHSuOaYAubUnILe2OaYAufkTkJtvjilAbuH45cZ2oSMKkFu3gNx2mIIsID3TXDOwhXSYRFxer1YYRkbT+Vudzl1JnK7ZHvDKttlsuwQVzaF7' \
			b'BIh1tEo4erGyvfd4A6R62LXHlaRqmiMOkOpojXH8UrXNEQdIdYeVy7FJtW2OOECqOyxqjtj6wF6XEwgQdRu9xWxcJ0lFtfby2zckcwPXQRQXe5Etv9mJvam6PFaEYmFzMdeMAsrw21JUbFu0EkmXS4Toe+wdi210t/ALLSyvSfhNZZ5d2/xjHAqtF8ABv1+g' \
			b'1A5qRbYFazlK7Rt57XesTk/mNE0RkNGMMrJicGbblEE5qDEfdrQ+O+DFCccOOI+5LZ8zU148YJ6dauf/D2QS+zM='

	_PARSER_TOP  = 'expr'

	_GREEK       = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'

	_SPECIAL     =  r'\\partial|\\pi|\\infty'
	_CHAR        = fr'[a-zA-Z]'
	_PYVAR       = '|'.join (reversed (sorted (AST.Var.PY)))
	_TEXTVAR     =  r'\\text\s*\{\s*(' + _PYVAR + r')\s*\}'
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
		'abs'       : lambda expr: _expr_func (1, '|', expr),
		'Derivative': lambda expr: _expr_func_remap (remap_func_diff, expr),
		'exp'       : lambda expr: _expr_func (2, '^', ('@', 'e'), expr),
		'factorial' : lambda expr: _expr_func (1, '!', expr),
		'Integral'  : lambda expr: _expr_func_remap (remap_func_intg, expr),
		'Limit'     : lambda expr: _expr_func_remap (remap_func_lim, expr),
		'ln'        : lambda expr: _expr_func (1, 'log', expr),
		'Sum'       : lambda expr: _expr_func_remap (remap_func_sum, expr),
	}

	def expr_commas_1   (self, expr_comma, COMMA):                              return expr_comma if expr_comma.is_comma else AST (',', (expr_comma,))
	def expr_commas_2   (self, expr_comma):                                     return expr_comma
	def expr_commas_3   (self):                                                 return AST (',', ()) # empty production
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
		args  = expr_func_arg.strip_paren ()
		remap = self._FUNC_AST_REMAP.get (func)

		return remap (args) if remap else _expr_func (2, 'func', func, args)

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

	def expr_mat_1      (self, LEFT, BRACKETL, BEG_MATRIX, expr_mat_rows, END_MATRIX, RIGHT, BRACKETR):  return AST ('mat', expr_mat_rows)
	def expr_mat_2      (self, BEG_MATRIX, expr_mat_rows, END_MATRIX):                                   return AST ('mat', expr_mat_rows)
	def expr_mat_3      (self, BEG_BMATRIX, expr_mat_rows, END_BMATRIX):                                 return AST ('mat', expr_mat_rows)
	def expr_mat_4      (self, BEG_VMATRIX, expr_mat_rows, END_VMATRIX):                                 return AST ('mat', expr_mat_rows)
	def expr_mat_5      (self, BEG_PMATRIX, expr_mat_rows, END_PMATRIX):                                 return AST ('mat', expr_mat_rows)
	def expr_mat_6      (self, expr_curly):                                                              return expr_curly
	def expr_mat_rows_1 (self, expr_mat_row, DBLSLASH):                         return expr_mat_row
	def expr_mat_rows_2 (self, expr_mat_row):                                   return expr_mat_row
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
	def expr_term_2     (self, SUB):                                            return AST ('@', '_')
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
		'expr_sub'           : 'SUB',
		'expr_super'         : 'CARET',
		'caret_or_doublestar': 'CARET',
	}

	_AUTOCOMPLETE_CONTINUE = {
		'RIGHT'      : '\\right',
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
			self.erridx = self.tokens [self.tokidx - 1].pos

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

		return True

	def _parse_autocomplete_expr_comma (self, rule): # also deals with curly vectors and matrices
		idx = -1 -len (rule [1])

		if self.stack [idx] [1] == 'CURLYL':
			if idx == -2:
				if self.stack [-1] [-1].is_vec or \
						(self.stack [-1] [1] == 'expr' and self.stack [-2] [-1] == 'CURLYL' and self.stack [-3] [-1] == 'COMMA' and \
						self.stack [-4] [-1].is_vec and self.stack [-5] [-1] == 'CURLYL'):
					return self._insert_symbol (('COMMA', 'CURLYR'))

				else:
					return self._insert_symbol ('CURLYR')

			elif idx == -4: # examine stack for two vectors started with curly or vector and comma list of vectors
				if (self.stack [-1] [-1].is_vec or self.stack [-1] [1] == 'expr') and self.stack [-2] [-1] == 'COMMA':
					vlen = len (self.stack [-1] [-1].vec) if self.stack [-1] [-1].is_vec else 1
					cols = None

					if self.stack [-3] [-1].is_vec and self.tokens [self.tokidx - 1] == 'CURLYR' and vlen < len (self.stack [-3] [-1].vec):
						cols = len (self.stack [-3] [-1].vec)

					elif self.stack [-3] [-1].is_comma and not sum (not c.is_vec for c in self.stack [-3] [-1].commas) and \
							not sum (len (c.vec) != len (self.stack [-3] [-1].commas [0].vec) for c in self.stack [-3] [-1].commas) and \
							vlen < len (self.stack [-3] [-1].commas [0].vec):

						cols = len (self.stack [-3] [-1].commas [0].vec)

					if cols is not None:
						vec               = self.stack [-1] [-1].vec if self.stack [-1] [-1].is_vec else (self.stack [-1] [-1],)
						self.stack [-1]   = self.stack [-1] [:-1] + (AST ('vec', vec + (AST.VarNull,) * (cols - vlen)),)
						self.autocomplete = []

						self._mark_error ()

						return True

			return self._insert_symbol ('CURLYR')

		elif self.stack [idx - 1] [1] == 'LEFT':
			return self._insert_symbol ('RIGHT')
		elif self.stack [idx] [1] == 'PARENL':
			return self._insert_symbol ('PARENR')
		elif self.stack [idx] [1] == 'BRACKETL':
			return self._insert_symbol ('BRACKETR')
		else:
			return False

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

if __name__ == '__main__':
	p = Parser ()
	a = p.parse ('{{1,2,3},{4,5,6},{7')
	print (a)
