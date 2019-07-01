# TODO: 1+1j complex number parsing?
# TODO: \operatorname{n_}

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
			b'eJztXfuP3DaS/mcOyAzABsQ3Nb85jjdnnB/Zib3AYmAYfkwWwcVOzrH39rDI/35V9VEPSmq1umfa3T0ZDKclsSmyWPw+Pool9dnVN08fP3v54zfqm8fPXtDnk8dP6fPHl/L510uJev49fb64fPz9f9LxLy+fPeTIR3/h7759cEmfPzy4fPTsCefx/bPnl49e' \
			b'P3x5+eTvnPbywcN80Plo6Chfc/JvKeK/Hr3g0x9fXEq539LnMyn9b5L1f1x/fM+3PH/69EFz62V3a1s6n7CELNR3z19+++TRjy8kg4f0LUc++qvUUQ4/PJEaf/f4b4+/e8Rpvnv+QmR4kIXQzY0i9oOHL55fPn7AYv5w+fjpI773xXP6ePfm0/Xn179+ev3+' \
			b'1y9vf7n+/fObTxT7+5e3/5ST63/99un1719+u24vfvry8d3rj9f/aK7f/frhw5su5Vs67d368cuH5vTz9af2/O2nN+/++/pzm8eXT7/8X1sAfdec/0bSfWwu3rz9vY3/9X/b5G/efe7L1onSltaT55ef29ifP7b3ffjyy+ufP/zWXL7/+Z/d6U8/tXXpKs03' \
			b'0Ekr2fv3Xa7X/9Oct2ffvFJXZytbKRPPFU4Sn2i1MnKM6iypWlGECao+b+Ikpr1cabnJyb+le/15d111l3RCR6M5Tx2oiMC5GnfeRDeRbczKiBgUJx/GUFnnbQwJZZoriueTSvL2bd72vIluItsYyp/PSHyRPsm/pRJQr/a66mLohO9lTSlDOsh58QmL4/Fh' \
			b'43m+XOkgZzUVT6mk0Oq8jbL9S+3yCcfxGamPVGZyZnLF+qFKl9F+dFXGhNFVKmJi/4qklipxo7p8dlbJhQAETUwRzfUKYrOCc8mp+TJHthcrLQrX1NBGaTQTqcUCXpRVOF//PWPTLktWlalWWlrHy79tv8nXrrteSWPV8k/ynp+3Z3QSRA3QU+AT1o1VWhBB' \
			b'UpxxBRlfADvHkGhVC8QumkQSkRsoUtwqZxPwQTo8z9dELymJpM3p8qWVdiIIndmeEkyrS26GrALbtiWVnlu2d1mVEb1SCP6iEqJdFoMVnk+ouObMAP7MC8KmZXjlviFH0TVFn5ephimaa7qUjGupclOxTLU2kogyFcdXXTyURNkTpainuyIIsXIowmnljIqK' \
			b'OzdfKa+VN8p75YPkTBDizkV5qzwltsrRp1cuKBeVS8rVKgQVIkOSughCFQHJUqsEYj9rgFqIWj0YFehe5VVQPilPd1UqUM6R+lluLEIrNTJ1oVrAwtAgqShYFZ2KXsWgYlQxqVirRHKSxP4VQ5GpZPnz6szI8YxqpbmWZ1Q3vqb68SHKZ8rf1XLlcb/XOZYq' \
			b'TtenUHGPSnEzcdU16mNQH9PUx+RUopgjrISD9A4N5+QyOBX86SLS+VyngDoBdg64O4sZqlqiqUeioYZHyrvBxuhQWYAxQAMhosoWbLQCSRqkXHUgMa9k5Llz2icNg0bWdRoGmQ4mkIdAoSdQUqFWsVJRH06seHgI2oSe2jc9dSaLsKOnJGJVyH0GyOVBLo30' \
			b'XCZGLqnSnQDyWR7TfLqDLD0LGKKDznMWDAS75GSrnEXaOQuTwQQw6jxRyoc8kEUgLWIgi0gacWMSEZJWyahkVXI8qOeJlm8nZTQ/Pu1Gk6kk1eJ05Y8s/ikKnk5VcJKZJT8hgfVJCcxrNSMdjCia1zws/rEKayGsk2Mxvl/xuseMFqgBwz0WDDcfdbpVicGq' \
			b'xGBVYqQwjWsea3GNwjVmJzyT56+tRiVIgZJaY87RjtB3Yny2ddaUDG0HXKH0GoRn9tC8IOWQM1ee00OUcGhRiCOYjIT6kE0Vq1thaMzLYzDRiJZ5OYBuQ3R9Jwh2xSsYc+fm9Ve8IruT1aruYLXOcifmUznuheouEc1IX7Izmnv2BV5jmrwYNFgFmsG674pX' \
			b'iAZLQ0wqEnq0hOVkykNZwtSCNGzPsbCyo7lPlLihcT5NxPKlxaXNk0F7vAbvK56l2qOdpcr01J7uMpfnzCbPci1muRazXK5UeYuk1xGo0fbu0J7n7qKEENZUWybwrJjBLN9VzbTewopsYbvlQ8j8DzJ2H2p7AQI6NBrla4s1SxhcV/1r6vGlY0AnEvCdAUAi' \
			b'7owZDQlz74RVThJsTKqRcOCOubNhkUZ9K4sHbjhww7F2tIVe5EsBiDvwOiOgeR1UXMtBQ3bKxqER+ZBy158A6iQ1GQxNVGmPSntU2t8VugvP70xtGHjSQvJJ2Xq0ukerezS3AzsdWtvlHj+ggQMamA4kDmwXAQl9ThhPyMp1xVWKqFIUomL2BBtFkMqUu0Uk' \
			b'eYImEm5LOWU6tWrXpyVwOimBGRF19k+osoOC+AadVeqqkgLRibR58kDqu7LaCqLfgbSQyraDhpPqpDySoG+aVEXXVYm6SIckJ9WX6o4t7P6+Mdduqmrc6TuVSG5Cfa1qrWqraqdqr2qqLSGKK0n1qahCFVWnoglQxXFUTaknxXNNeWLEHjXsTsMuNOxYxF5F' \
			b'vEnLG3bsysB+DLyRzHZCdjRiLyP2Y2EnFvYBYf8PVi4rlp11eJbA/i7sYsQQ4d1N3gTkHV/e4WV7L1tpQ6BGCKwT9rmjO1eevd/Yo4vPSRlqRfmvqH3Z/c7RFX1HOGI0yYeElXif0TFIuiAfcAtciXNcEneyVeR/yi6xeyq7gDLQur8ViVuzHFYkiuw1SKlJ' \
			b'AVwEe35alOb5oNnFLnIpET6QjN4uL3api/xP91FDSYaKvUk9F67FL5TFZO/LKPUUX0nKjmIsf8M3c1oK4rtJl6wELk1nRq0Cq6NCiezFyu62XGHWIt1LIFnR4LFKrBcdKnGW5GStmJwJtdzKpVfq3z5crLhJTaSj/YPHIeYHa2kzP8ztc6JPCGbDQh6UJKjr' \
			b'zIObcGAX/M9hntHI5RWg18A8HzLoBbQd6vmyB3W+DPhcBnauahkY8nJgn14HzFuNggB4RvsQ5sNMBlgvgd4l06jBcqBLatuiPGczj3MNeHelFgjX1QV3LXW6WElbE+CN/kMmGfdA3wvQnQDdlUB3ALrrgO5KoLsS6E6A7pYD3Q2DAN2Nge7mgT7IZB7obTKN' \
			b'GmwBdFcCHdlsALoD0NtSlwHd3gN9P0CXOYwupzFy6eTQAL0ugV6XQK8F6PVyoNfDIECvx0Cv54E+yGQe6G0yjRpsAfS6BDqy2QD0GkBvS10GdLcc6F9zah92nd2v4cCm2b3d4wx/jg/8HFfNqu3zQS6dHDIf+LTHB26KXuhzgy8DPpdxY5CXlO1x6HEjz/Cl' \
			b'MAhoUZZtchhyZZjpLFe6ZHmmL3Uf80XKmaSM3JCrD9Y0uplljdwW+uUvYo2/Z81BWWOFNbZkjQVrbMcaW7LGFqFgjRXW2OWssaPsvMdhgjUWrLFgDcaWfNeQNYNM51nTJmtYY6dZY9eyxoI13VjT6GaeNRas6cpfxJpwz5qDskYWGaZcZBgsMky3yDDlIsO4' \
			b'IhSskQWHWb7gGORlsOAwbpo1WHTIAWXZJocRawaZzrOmTdawZnoRIuVMswbrEMkisybrZp41WIr0yl/EmnjPmoOyxgtrfMkaD9b4jjW+ZI0vQsEaL6zxy1kzCsIaP80aD9Z4sMaDNUg+ZM0g03nWtMka1vhp1vi1rPFgje9Yk3UzzxoP1nTlL2JNul3W9DZh' \
			b'9sKdNTszmT7+tBkka35TrvkN1vymW/Obcs1v6iIUDJL1v8H6PwUhER828ageZeo9DuAR59HQCIYAA1uAHJoMONWQSWW2abyxMSBTK0BDpmnzgKhkmkywEEgWmUxZ2nkywUjQK3+CTD5ecHuMOVUzp4gPee9xZ2Zhi/KQQ5IZjUpmYmNwL8yyt8wuHkB4ocDM' \
			b'ke0SjugRTS7ze0lAND7tEY2bohf6RIvSCxLX5HPZaDXITor3OIxHKykPMloIZpschhzr56hzvYYkk3WJHpCtkyOTTVQxJpuUOUk2uQHi8XMFYpnr1DVLOLk19GVYNHrp6sbD1+FJdtrzPgsylXuPFnuPttt7tOXeIyu7Fwoy4faAz4VkMqMcvcdhgkzYjpQD' \
			b'BLNNDiMyDTKdHa26ZA2BprcnpZxpAmGHUrLAaNWoZ5482KTslb+MPFtsx9+vmPbAHLHO2dI6Z2Gds511zpbWOWuL0GeOvJgKnwtpY0fZebzfaoo2sM5ZWOfyzk8+G9JmkOk8bdpkDW2mrXN2rXXOwjpnO+tcI+A8bWCd65W/jDZbbO4fljbzi6VTZo7YGmxp' \
			b'a7CwNdjO1mBLWwPDtRcK5oitwS63NdhREOZ0tgbJKxMHpgYLU4OFqaG7b8idQbbz3GmTNdyZtjbYtdYGC2uD7awNjXbmuQNrQ6/8bRZIegu3gXsK7YdCUSgUSwpFUCh2FIolhcpQUCgKheJyCo2z8x6HTKHYUSiCQhEUiqBQe9+QQoNs5ynUJmsoFKcpFNdS' \
			b'KIJCsaNQ1s48hSIo1JW/FYVOxiHh7lIoCYVSSaEECqWOQqmkUCpCQaEkFErLKZRG2XmPQ6ZQ6iiUQKEECiVQqL1vSKFBtvMUapM1FErTFFrryCM3ZAVkCmXtzFMogUJd+VtR6ObeCYXxYPQYws504kcVzM3s4KFHreoU2cXNXXMjFB5wQdilO0d+XXryc6P1' \
			b'Qp9dSZ72WEl8wl6shk1cb7aJD/LVcO+XA5imYRPXFdWlCnCSg5+/HCCo7WU08pkblZBKy53mhGPvuTa/zD097fwvJU470QXhnu78/xvdzfvRBfjRdeVvxb2b+zgMDXcH33oKJz2aGbHjmdKOl5+bMZ0dz5R2vCBftqHgm7TbCm9cD7iw4ge8cQPKDINsQHXW' \
			b'PMkxb0DBmGdgzDMw5nX3DTegRiFtdLlr82r2oKatematVc/Aqmc6q16jrPk9KFj1euVvRbBbdoc4OLtOmFpOnFdd6bzq4LzqOudVVzqvsoJ7oU8tJ86rDs6rDnNFPmzg1SBHBxdW17mwSo7glYMHq4MHq4MHa3ffgFcTOc+SqkuWSeWm/VjdWj9WBz9W1/mx' \
			b'NmqaJZWDH2uv/K1INect4Qpe9Z9jvafWkFo8Lbq9maJYA3VpDdSwBnqYMhgNUTq+hmHBYL7Ij5RyKpwUT0+ITVDDJijfVfhVkDHJ6t5EcRRkotgZBnVnGNQwDGoYBjUMg919wwniOGdCEhc9/VhFm6qZGE6bBvVa06CGaVB3psG6avU0PzeEdbAnwgTLnL1Y' \
			b'yUPVQrZEZCNoTnCuvh/ItmGb3/dgJt6xrvSOdfCOdZ13rCu9Y50rQjGYiXesw4pMvqvksGkwc6NMvcchD2auG8zgIuvgIuvgItvdNxzMxjnPD2ZtsmYwm3aUdWsdZXUWzmVt5AEtq2p+QIOzbE+GbQY0c3P/iZMkl+kRLBwjyWRIc+WQ5jCkuW6Dy5UbXKzg' \
			b'XihIJoOZw2DmMJi56cGsINkoCMm60cx1o5nDaOYwmjmMZt19Q5KNc54nWZssoFTd1HeSamsHteaerJLMtKyveaZhUOsJshXTNC2xs0tgwTUQrWVZSyu9wSzPxOk/Bzv1EOxGzz2w4CYPvG5Cehogu/TBm3pJRwPuPrL7UOafzlpoH2ewDh9dnXtudZmjnPwG' \
			b'm57eJZp5x0b/SdUNUGOc9eHF+DH7xI+8FyejKE4ByS7FEptA4wym+E0n9D2vkObwxb+ucJoYw6DiW6zx9drnpKuJucU85nTOfQ32UDr+53Cod8ai+nfQF/zDhNTOfPwDbyT9SuDctYvzC7o5vQGKPq9dU16/zsCSf8aJ37Yq67AMUf71GTGuHxFUGQn+trvF' \
			b'zS+r0JL5elhqGV6rVp8zEO3mU7GFazOnGnahbp8one8/b6fzXNJhhlPsNPso5KrfHhJ5fr7LQN0iMezWSfZ7R/9VcHfDQfsmmHOnjrn1r6Za+vTEFr3fPN7crhPEcCCU3Rxi/s8wL/y6Ay2en3J51hL2NBfEe6AXwc5tjzxf2oR2BF9jS93XIrfKYIu3BriI' \
			b'fXQ+7AY5/mrgvH9LqMsGzv2sfPn9noyyaCbGU36JpAkynKZ7xN024vAcieBlN8SNHxc5DcQFIG5qBtdDXK2uDmm5u0WzXXWD4ZM1dBpmu9s02emei8H2wyPV9upwwDm0sZf1cPxoObxxlyQ+IEoOsCvgVPky7wI06SuChgvbATNy2y3AxqWlqNESr1ZTc6Px' \
			b'i7Ypr6s/a6fTAw/3Cvcdzhgw9QXRSnBi/7w4Ef0f9cjEHhLVQYHiL4hNtbsgyNZ0nv7Ar1v9eTGjjx4zWomQR4YZLz9SQO0Ax4ske2is0MSL7VpL3bmF9Sv8ctoVELXdKt5vsXjfaZ2+GDiRB6KMiAh/Nz5sh4V4gxX1DuvmZQ0eXbE2JhmaplreTsvYvqfW' \
			b'6bdM2Imiu4z5+2gLbgia+llQLNHUGeSC9ooak1Lxkx0O4vQyOZcf7r5qiZlvb/vMNFQeq0LU0J/SQG72gCvy5l9FWsl7ZrQ8ymLllTYEzoHvnvgswH2OPbplw0HeP8YucrwnShgLTTS26tstdq7BymxbBvVG6/4kQzvMkH/lZkOeVjV/tVF2+CfZymPb2gxz' \
			b'dnEy82pQgAyWrv2rbe9CFgA4k5L82pLyT2gtKI+4WvxhAJ74kxLDhhLh8bmxXOznd76RJEdU4z9MA6b+huM2yyaPQ4X9SJd4IpO2/ROx0h7FIh5v/ydS1Qul8nZCsNbRdk427s4XBJnkjQJP46ZvEOnxUjik2a0GqagEF7e+Ijwm8SwWJ9uG/o1TmaBC+mtW' \
			b'yKp9BlTIDCtUOpejcnjFx2QVvXSX7CBe91zDR+7g/Xob1bp7syCNC7f8as9aXUT1VQOPtdlKnx3NplNCifZroiKpfQZUyC1BxbrKFWCYrag0/6am53VsL9BIgk+EwbeDwJNWpOPp6lxCa7rMywCN+GPSSFCHC1BHOCZ1RHW4AHXEY1JHUocLUEc6InXwGvhg' \
			b'Aeqod1bHktF1J6U4tVtgW80wSu+YGVaLoyni/icgi7UU1MaAR92WpJwMbDVZlhTaGs0/j0hbtTqaAGUdYG67VFlsijuWAGWN5rBHpCyjjiZAWYvmx4dfNTlY+Y8rQIPNNgSbtmiCnhkb5G1jxjRmw6wO/jHxip/n4N+7jn0fZdwW5WcJW/VDqaQavs82tm3f' \
			b'ma6bZkzyE1N0u7hA8E4BN0aExkM2Z8Ii2+6TpBoWWQeR2a1I+0pefkEj2qvz/wfTxS80'

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
		('FUNC',         fr'({_FUNCPYONLY})|\\?({_FUNCPYTEX})|\\operatorname\s*\{{\s*({_CHAR}\w*)\s*\}}|\$({_CHAR}\w*)'),
		('SQRT',          r'\\?sqrt'),
		('LOG',           r'\\?log'),
		('LIM',           r'\\lim'),
		('SUM',           r'\\sum'),
		('INT',           r'\\int(?:\s*\\limits)?'),
		('LEFT',          r'\\left'),
		('RIGHT',         r'\\right'),
		('CDOT',          r'\\cdot'),
		('TO',            r'\\to'),
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
		('DOUBLESTAR',    r'\*\*'),
		('PRIMES',        r"'+"),
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('CURLYL',        r'\{'),
		('CURLYR',        r'\}'),
		('BRACKETL',      r'\['),
		('BRACKETR',      r'\]'),
		('BAR',           r'\|'),
		('PLUS',          r'\+'),
		('MINUS',         r'\-'),
		('STAR',          r'\*'),
		('INEQ',          r'==|!=|\\neq?|<=|\\le|<|>=|\\ge|>'),
		('EQ',            r'='),
		('DIVIDE',        r'/'),
		('FACTORIAL',     r'!'),
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

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                              return AST ('lim', expr_neg, expr_var, expr)
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_doublestar, PLUS, CURLYR, expr_neg):   return AST ('lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_doublestar, MINUS, CURLYR, expr_neg):  return AST ('lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6      (self, expr_sum):                                                                            return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQ, expr, CURLYR, expr_super, expr_neg):                  return AST ('sum', expr_neg, expr_var, expr, expr_super)
	def expr_sum_2      (self, expr_func):                                                                           return expr_func

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
		func  = FUNC.grp [0] or FUNC.grp [1] or FUNC.grp [2] or FUNC.grp [3] or FUNC.text
		args  = expr_func_neg.strip_paren ()
		remap = self._FUNC_AST_REMAP.get (func)

		return remap (args) if remap else _expr_func (2, 'func', func, args)

	def expr_func_8     (self, expr_fact):                                   return expr_fact

	def expr_func_neg_1 (self, expr_func):                                   return expr_func
	def expr_func_neg_2 (self, MINUS, expr_func):                            return expr_func.neg (stack = True)

	def expr_fact_1     (self, expr_fact, FACTORIAL):                        return AST ('!', expr_fact)
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

	def expr_frac_1     (self, FRAC, expr_curly1, expr_curly2):              return AST ('/', expr_curly1, expr_curly2)
	def expr_frac_2     (self, FRAC1, expr_curly):                           return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_curly)
	def expr_frac_3     (self, FRAC2):                                       return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 4))
	def expr_frac_4     (self, expr_curly):                                  return expr_curly

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

	def expr_super_1    (self, DOUBLESTAR, expr_func):                       return expr_func
	def expr_super_2    (self, DOUBLESTAR, MINUS, expr_func):                return expr_func.neg (stack = True)
	def expr_super_3    (self, CARET, expr_frac):                            return expr_frac
	def expr_super_4    (self, CARET1):                                      return _ast_from_tok_digit_or_var (CARET1)

	def caret_or_doublestar_1 (self, DOUBLESTAR):                            return '**'
	def caret_or_doublestar_2 (self, CARET):                                 return '^'

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

# DEBUG!
if __name__ == '__main__':
	p = Parser ()
	a = p.parse ('{1,')
	print (a)

# 	print (p.parse ('1') [0])
# 	print (p.parse ('x') [0])
# 	print (p.parse ('x!') [0])
# 	print (p.parse ('|x|') [0])
# 	print (p.parse ('x/y') [0])
# 	print (p.parse ('x/(y/z)') [0])
# 	print (p.parse ('sin x') [0])
# 	print (p.parse ('sin x**2') [0])
# 	print (p.parse ('sin (x**2)') [0])
# 	print (p.parse ('sin (x)**2') [0])
# 	print (p.parse ('x') [0])
# 	print (p.parse ('-x') [0])
# 	print (p.parse ('-{-x}') [0])
# 	print (p.parse ('\\int dx') [0])
# 	print (p.parse ('\\int dx/2') [0])
# 	print (p.parse ('\\int 2 dx') [0])
# 	print (p.parse ('\\int 3 / 2 dx') [0])
# 	print (p.parse ('\\int x + y dx') [0])
# 	print (p.parse ('\\int_0^1 dx') [0])
# 	print (p.parse ('\\int_0^1 dx/2') [0])
# 	print (p.parse ('\\int_0^1 2 dx') [0])
# 	print (p.parse ('\\int_0^1 3 / 2 dx') [0])
# 	print (p.parse ('\\int_0^1 x + y dx') [0])
# 	print (p.parse ('dx') [0])
# 	print (p.parse ('d / dx x') [0])
# 	print (p.parse ('d**2 / dx**2 x') [0])
# 	print (p.parse ('d**2 / dx dy x') [0])
# 	print (p.parse ('\\frac{d}{dx} x') [0])
# 	print (p.parse ('\\frac{d**2}{dx**2} x') [0])
# 	print (p.parse ('\\frac{d**2}{dxdy} x') [0])
