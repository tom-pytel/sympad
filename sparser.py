# TODO: 1+1j complex number parsing?

# Builds expression tree from text, nodes are nested AST tuples.

# FUTURE: verify vars in expr func remaps
# FUTURE: vectors and matrices, assumptions, stateful variables, piecewise expressions, long Python variable names, plots

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
	expr = _expr_func (1, '(', ast.strip_paren ())
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

#...............................................................................................
class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJztXXmP27gV/zIFMgZowOTjpfyXTWa3g+bYnSQLFMYiyDEpAmyO5mgLLPLd+w5KJGVZPmJ77GQwtCRSFN/B3+PjJc3Z/NaDi4dPH99Sty4ePsHj/YsHeHz8lI+/XXLSo1/w+OTy4pe/4/nnpw/vUuL5z3TvpzuXePz1zuX5w/tUxi8PH12eP7v79PL+Pynv' \
			b'5Z276aTT2eCZb1P2x08umdhPeHzIJH/n8v529e5Vm68rny7uPnrw4A6RxZL+cc5PE1vEyb1HT3+6f/74CRdwFx+gxPPfWDA+/Xqfxbx38fvFvXPKc+/RE+bhTmJCtw8yr3fuPnl0eXHnfqZGl79eXjw4p2KePMLDy+cfrz4/e//x2av3X178efXp8/OPmPrp' \
			b'y4v/8MXV/z58fPby/du3z9vIpy8frro7r7+8e/ns3dW/8s0XeFk8+u7L2/by89XH7vr1x+cv2+sPyMG7NvL8xacu/f1/u+zPX34uSWZyXYkFzT/fdKlv3nXPvf3y57M3bz+00Vdv/pMvX7/u+M2y0AN40XH26lUu9erf7XV3desPNT+bmqiMnyi5CHSh1dTw' \
			b'OaizqBqFCcapZtKmcUoXnepIV5Z/MFNTN8nxIooXRMTLwQA+OEkpeIUXWBSXFPkHyIXQ6OKznIIX9Cj+QCHfU5Ci6IK4cnIAP0nRqWYRdaPONOYyM/pNuiQoo9qmC0qjKxQF2Td2kmMQWCt1sluIQZXiF2L1E6GMIdcsEl3ZdHU248iExSadGmSyjU+F7RmK' \
			b'kyi79mZK7CJTzQrXWp0ZhVXICjIKpKoxZ9Lb4H3CCVbzOtl6uaaaa8fxD0x7J8Uhx6dcWQ3/kN/JpLvCC89qCBO5njJikYygUCNYSEBCmJm0KVG1aa5MRpaYZeSyTcNq5ysvB9ThJMUR6kwJFc+gFyRiFETvmA6FEgiUokvjOhVAV5coM+NeqiRFZ3VCQQXV' \
			b'I2igiixZxgRBNl2EdIH02ysjFU2GYrBmkCkjmmuTMI7JkzpXP0cbxygXHFgHraSJky4R1TiURrGcLlrD4lFEbIbmM4Xa86RAQOtyKihqeSwoa5V1ykZl0TIxO2azVKL1ymJmT6aIciHo7ExZraxRrlF+RsZJ1Y2VHqg20FQQtUBAQZrKOeWwBOWUV04rh0+B' \
			b'cvgIYxb5wpr1eNMrH5SPyjcqzFTQKhgVQAV8EqPNHwRG0jHQcX5GIkxEaBLrDIXhu45PgY8x3Ws4ZkFONqVaun2cklqRwjZJViOyigC6FUCnXKyJY+A6CLsgVQMcdUG5eEIgg5iESKAR0CEnpPMzn0T0rPpTNSQfRSiBlRNJ/UxEM2JIRiQ05C4OxNecmmam' \
			b'HTJtwc/hOBDVmCZz4LXyRnm8sIfjA2bXoH4qkxqYtt3UggzHUCjUgBByXtAiYHEmPXHaZiEiOdYC9mOw13KqojhxFc4mm2Y0rfeoSQ7W6A2ekZbEi/n65LaCtJ1BUBUkTxDOAnMWUKdehaBCJKZT/tbroZYmp6Z57ogg2yfEcCB+T4LTeDKcIpPE6jFzaI+b' \
			b'Q+qeG24GWJXU6yV+j4Y7L9wBnyvfOKeer1kYhDiJSg9yixY990uN9EuN9EsN90sdR53cNFaYM5x6qj4MTJKYPcahqJpUsYbr8KAdMOp8Cu3m4LRxSCNu2psDahupwnbm4NNwX8xAR4G/E/3ZE4b9nDrT5uT7n1IRTkv1zGT0rHXqYcNJV5Bh0K1p0lo0EQSo' \
			b'geu26vbOqYNspGds2FOENIclvekgM1xnQUamqDOYSDcTFnxM4LT+RFccSKUoSBSSl4Ujmkuak7+H4/H37OjhhLr11N0wqb8A0l8A6S+QFPUj0qA6AYJrluUwnIPcsZE5GpCJEjr5BHPP+D7YgF1YSRDGgqBobIRbpxO+Zyfc5FCDycqWSgzplEQL0vcLXk5c' \
			b'7wP1xyZlj8rGkQe70IYRPwJYK4C1XJucyl1ae+humRdgifawHCsoY3iBSJCMJ3ipGbaNXiuPcjmRy4lc7mTxyK3E6bJPIOI64COVI1VoxYqs1KBNraeXSvNSaXhCWgJILxldyhiOeTg9JxmCyBC4Lybz3KlDxtzXM7zIahTRozwWU8549HI2R86hPm4OqZKb' \
			b'tPY1S4tfM26bZ2o+Ywpi6zJGSSK41BjQWKygWPHcMoyNNzYYi2LmxoNVISpCrkgcloVkZFUQVnlFJku0IA72mCOiF5FrVLQqehWRb0xE8RAkWAugGqsarxqShaQlSVGcGdbHDEWZ0X4GvEdSkpgkJwlKktLiCM2r03oZLVjRyhEtG9HKDdUJTV/Q1AUtg9Ki' \
			b'Ii0okkZJm9QXJzdMK6a0DE1AoNlvp1HLnqSnXRiWtpU0vPTPO2swN96grQWer7AOp5Y2d8zYbtswpQ09tKkG0UC56OBs2qlC2SkRbwfaKUQbPFChxd8UGWowmxU+kNTU0Z4Cy8QN7+4gKigvzRXMaDcJlkT7kWjvgXNtObQlA+tiipUxxaqgwmjjEZZMW2ho' \
			b'tw0wa5iIlTilbSm0E4N22njazIJxTMaq97KNKNCPRLNUFrFAPweJGikIo0QQLwNRIy1p62STDFJoBZ060i4WZ1Hffzm4PaVK0h7P/is5d4I5ybEa5juEdolrtwace1g2DOftsLwJjkexS1DlRq0EL0cDnxJ46bJAb4lYvsXHFZiVgstAyNWCXKpQhi5L1eGW' \
			b'QNtHa368B9garTnbOFjbTW8JrUzcd1BtKQ2CVQtGM6UKpnp2m1qBRt+eStXh2X5lH36D1i3RahmttkarFbTajFa7HK2W0WpXo9X2A6PVLqLVjqO1e3wcrV22FWi1NVptjdZEaRitVtDaUVoPrXCD1m3R2jBa644BRwOfWrQ2y9HaMFqb1WhdCIzWZhGtzTha' \
			b'u8fH0dplW4HWpkZrU6M1URpGayNo7Sith1a7PloP0OE1m/d5B4E83OeF/fR7RzFNsGh4826BaY4GPiVM8+bmjGmjcyjxzdn4uALfZQGpGFpu1jW+U7eXiQhXRko3sX2qh/dc3Cjec7YlnV9TwZ7Ly7BnfpKwgvyW5iDyOXtT0lwL+e4G+ftFPveUTd1TNtJT' \
			b'NrmnbOqesjE5VMjnXrNZ3WsuC0jFEPLNMPKl52xM2uYvyJeEPvK74saR32VbhnxTIb/uTBvpTJs89GtpDiNf+tMFzbWQ72+Qv1/kAyMfauSDIB8y8qFGPuRQIR8Y+bAa+dAPjHwYRj4I8kG1r1CZ2D7VR35X3Djyu2zLkA8V8qFGPgjyISM/0RxGPgjyM821' \
			b'kB9ukL9f5PN409TjTSPjTZPHm6YebxqbQ4V8Hnua1WPPsoBUjI1yGkC+jD/5hTsp3cT2qT7yu+LGkd9lW4Z8WyG/HpIaGZJynoT8RHMY+TIqLWiuhfx4g/z9Ij8y8mON/CjIjxn5sUZ+zKFCfmTkx9XIj/3AyI/DyI+C/CjIj4J8yd5HfndjHPldtmXIjxXy' \
			b'Y438KMiPGfmJ5jDyoyA/01wL+Q0h3yhIC0db4j9ehwm4BStwQ4s8u7QFvSt7oOkIxS91o7LINOppHSPTOiZP65h6Wsc0OZSmQZvIeJbHrJ7lMQuBraMZtg6Z6aGTkdKl0plazzo4lZRqBmZ+6A1fsH1L6ThYZilNZSn1RJCRiSDOY7hG2FqkwCXWIvNBBd21' \
			b'rEXPvtFRXIuhnJav4O8R8FcJCoMAmROCPCcE9ZwQKbQNlUFYycnHFQZRlpFKsvJ9hAGDAJkWApkWgvS6vjzVM4hc3Ki7yNmWGAFU00JQTwuBTAtBnhZqaQ4aAMi0UEFzPQPYYG30pqe0Dfp5XgjqeSGQeSHI80JQzwuByaFEP2fj4yrom35g6A/PC4HMC6WJ' \
			b'f5B5oZTQh35X3Dj0u2zLoF/NC0E9LwQyLwR5XqilOQx9mRcqaK4H/Q0WWq8F+kNbek4N/TxChnqEDDJChjxChnqETPsP21Chn0fIsHqEXBaQiiH05xEyl5HALwNkkAEyyAA5P9fHf3djHP9dtmX4r8bIUI+RQcbIkMfILc1h/MsYuaA5gH9nb5OmB8xggxXc' \
			b'GzPY0gx4AxgdSzPwYgZ5DxjUm8AIAm2ozIB3gcHqbWBlAakYMgOfzcBnM5DdYHQyktXE4rm+GXQ3xs2gy7bMDHxlBvXOMGYpkU9mkGgOm4EXM8g0NzKDY18a/h7MILAZhNoMgphByGYQajMIOVRmENgMwmozCP3AZhCyGRRdoSBmEMQMgphB91zfDLob42bQ' \
			b'ZVtmBqEyg1CbQRAzCNkMEs1hMwhiBpnmRmaws3VifqVD3iQY3AK9lj14+ljMFlaBtZ4NA07BNjS7CF27CC0uQmcXoWsXQWy0odoZxC4Cj0EmVfmLbCCnJVuEfD/wFqHsK7T4iga70mmvkHgMLR5Di8fIT/e3DpUlF9aiaavZ4g6iLusSi9GV49C149DiOHSx' \
			b'lyjRHd5LJI6joLmRxexyffkbzeUbDeX4rQR43QHqdQeQdQfI6w5QrzuQKttQeRBedwAxEf7EH8hpiR+J/cB+JK8+cEnJj8jiA8jiA8jiQ36u70fKe+OupMu2zJVUSxBQL0GALEFAXoJoaQ67ElmCKGhuZBhjy8+2sg2sjxvzwJ/fhSPh9Qd+v6RwJPK6iZMh' \
			b't5P3QCgxWQmhltwJVSfXjKvdiWN34sSXyPdZ+ZQNJUJ2Ja4f2JW47EpcZydMSPgzQsHE4rm+EynLRLgQ0eEdqF2uZf7DVf7D1f7Dif9wnZlE6KgOuxAnLiSTHbAUiyd6K0sMJqLBINQG7GaXi9ffk8XYPTkVywsUtl6gsLJAYfMCha0XKEiLbShthbPxEXVo' \
			b'5YvCfBp2KmUxqTCqirxGwSWJsVhZorCyRGFliSI/1zOWqsxRp5KzLbEWWy1U2HqhQideIMkuFtPSHTQXK4sVBd2NHEvzIxiIYxsJR2QmvJJh65UMKysZNq9k2Holw5ocKjPhlQwrKxl0IjMxy83E9AObSV7P4JKSmchyhpXlDCvLGfm5vpmUZY6bSZfNJTGd' \
			b'0OoZS7W0YeuljVYRSQHJVhLxYVuR1Y2C+Ca2gqTn7W6QylrEVBbezSHDWDaB1dQv4Ay9fbN698b4SzejL9wsAS6DtgRqvRNj6LXbFqvLXqyZrp5bJfj1354Ze3VmvX0T/KXz8Zdm+u/Olq/MLIEQ4aeEzYS/Y7QXXIT9QWO2Ah4udaCHYIL36Uvi1KnrIENv' \
			b'ubljgE7jD4ce3duO2UdQq7IBJGUvYTpUtZ6ijy5z0FZHPsuyt7aHXt6F76ENIjH530nsuy3SLMds0zYJTgk1fg3kfCeoaXaEGi5phRfbHDX2+Ho48aaTswZENL/Eu++Ojjtso/INLYr7kVqVHbUovIPb7KFV8evBBjZBjqknDrZrXlZ+4Gjj5sUl3JidYcfL' \
			b'Sj1vMdwIPfxgvTlxR+3N6s8Sbdje0Mef+JNEi/hRfxmPA/Dmq3xX8wZI2wNJFuzotCGQ4gkBSQuQ4jiQoppfTy9nFwMpWuTbuI9Daj8up9WHya4GTbp4K2wDJ9Wgjq4BEIef0rP2mFFwPVN4yNG11P4h5nQXPq5YgeEQTQKVvgUW6LFvhYN1q9CguWCVPoK4' \
			b'6vOHqID5j9BIFKCgyvyxGwj1V4M9B8P1b36M+qfKPk4PQSuk4eAAcLfRImK4PaWquD2NX+Vr/z8GFuLRYoHDUWDB8gdeUU7L6/SR93Kg8mhY6ajiSF6qP8v9Dceby3RYd7BKw9S1x6ibDUdX4sGQP0gVTRVIg8i1q5ii2w4cNxwejtejb6ohIFZ8WwPrqH89' \
			b'49yZ1guNh80sahuXuisdk4LROEB/lX9xPDf8ze4ZIx6H3Mk0WFW1sFEz96QZcfK5zAl/bn/emVV6vGvVQl9vQWyt7jS026tCXTZ9uH3Kr21r/kYCQXuW9xfxhiDZ7EO7QWlJnr6sEWhVguaYqfuo0zSyrIkTu1OzZoHYXiz+cQlQlYDt2/JCELH8F52C8o/L' \
			b'4Rex5OWHrihsKcvSGugVaMkb2fQXfXdJzoOvuGQ3XLJs8RotH9uw4k/8WZ3mmIIfoyCbyJbTSavr3f4rpIt11/sTL9pP7TtA4oW3X/tdcsM74OL6f8xG3DkbqIFN/piLZh0uUHkVI2Y1L2RJq0Kj6xRqwoezMqvyTRLPKRuxq0uOichyrqlRpz6c3iS4Jddt' \
			b'EO71/rkHtYcg3Js+9+UGUvm8Br/WOiiP41aKtoLavAm03PiZN3jyW1Syl5PEbfdsjkItqEME/sU2ZtyynKIv2H9tR7WHINzblbW9TJKykoekKiQbrVQacRWBemtt6N3qhaZJ2ajHtnhbl0Uu3Bbp3fVL79TBg8jur192rw4eRPZw/bIHdfAgssdrl51GbIcO' \
			b'InuznezjXm0bDYDaIjS2n0Lj1A1LkaHOQgdrP05+A404NR7kpZGV2RYDjd/XyyqqWei9XbtqGnXdQTRzxD1Dmmc4liDKgjSzSENnElpSLf+DiE5rogsUjXI1aZoqzPJclEmqd/yRcfRgzqSpPXwuCJBsmr7w/KHBYGnQTLWUkgNrp5vZjEZmYSBxFGk04XhM' \
			b'gbT+mPwf6zDtTA==' 

	_PARSER_TOP = 'expr'

	_GREEK      = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'

	_SPECIAL    =  r'\\partial|\\pi|\\infty'
	_CHAR       = fr'[a-zA-Z]'
	_SHORT      =  r'pi|oo|True|False|undefined'
	_TEXTVAR    =  r'\\text\s*\{\s*(True|False|undefined)\s*\}'
	_ONEVAR     = fr'{_CHAR}|{_GREEK}'
	_DSONEVARSP = fr'(?:(\d)|({_SHORT})|({_CHAR}|{_GREEK}|{_SPECIAL})|{_TEXTVAR})'
	_STR        =  r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPYONLY = '|'.join (reversed (sorted ('\\?' if s == '?' else s for s in AST.Func.PY_ONLY))) # special cased function name '?' for regex
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
		# ('VAR',          fr"(?<!\d|{_CHAR}|['])_|({_SHORT})|(d|\\partial\s?)?({_ONEVAR})|{_SPECIAL}|{_TEXTVAR}"),
		('VAR',          fr"({_SHORT})|(d|\\partial\s?)?({_ONEVAR})|{_SPECIAL}|{_TEXTVAR}"),
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
		'Abs'       : lambda expr: _expr_func (1, '|', expr.strip_paren ()),
		'Derivative': lambda expr: _expr_func_remap (remap_func_diff, expr),
		'Integral'  : lambda expr: _expr_func_remap (remap_func_intg, expr),
		'Limit'     : lambda expr: _expr_func_remap (remap_func_lim, expr),
		'Sum'       : lambda expr: _expr_func_remap (remap_func_sum, expr),
		'abs'       : lambda expr: _expr_func (1, '|', expr.strip_paren ()),
		'exp'       : lambda expr: _expr_func (2, '^', ('@', 'e'), expr.strip_paren ()),
		'factorial' : lambda expr: _expr_func (1, '!', expr.strip_paren ()),
		'ln'        : lambda expr: _expr_func (1, 'log', expr.strip_paren ()),
	}

	def expr_comma_1    (self, expr_comma, COMMA, expr):                     return AST.flatcat (',', expr_comma, expr)
	def expr_comma_2    (self, expr):                                        return expr

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
		remap = self._FUNC_AST_REMAP.get (func)

		return remap (expr_func_neg) if remap else _expr_func (2, 'func', func, expr_func_neg)

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

	def expr_frac_1     (self, FRAC, expr_term1, expr_term2):                return AST ('/', expr_term1, expr_term2)
	def expr_frac_2     (self, FRAC1, expr_term):                            return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_term)
	def expr_frac_3     (self, FRAC2):                                       return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 4))
	def expr_frac_4     (self, expr_term):                                   return expr_term

	def expr_term_1     (self, CURLYL, expr, CURLYR):                        return expr
	def expr_term_2     (self, STR):                                         return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_3     (self, SUB):                                         return AST ('@', '_')
	def expr_term_4     (self, expr_var):                                    return expr_var
	def expr_term_5     (self, expr_num):                                    return expr_num

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
			self.tokens.insert (self.tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, (None, None, '', None)))
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
# if __name__ == '__main__':
# 	p = Parser ()
# 	a = p.parse ('\\left(1,2')
# 	print (a)

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
