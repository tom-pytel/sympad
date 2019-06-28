# TODO: Fix variable naming for subscripted stuff and stuff with primes.
# TODO: 1+1j complex number parsing?
# TODO: Redo _expr_diff d or \partial handling???

# Builds expression tree from text, nodes are nested AST tuples.
#
# ) When parsing, explicit and implicit multiplication have different precedence, as well as latex
#   \frac and regular '/' division operators.
#
# ) Explicit multiplication and addition have higher precedence than integration, so they are included in the expression to be integrated,
#   but lower precedence than limits or sums, so they end those expressions.
#
# ) Differentiation and partially integration are dynamically extracted from the tree being built so they have
#   no specific complete grammar rules.
#
# ) Future: vectors and matrices, assumptions, stateful variables, piecewise expressions

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
		return AST ('intg', _expr_int (ast.intg, () if ast.from_ is None else (ast.from_, ast.to)), ast.var, *from_to)

	raise SyntaxError ('integration expecting a differential')

_rec_var_d_or_partial = re.compile (r'^(?:d|\\partial)$')

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast.numer.is_var and _rec_var_d_or_partial.match (ast.numer.var):
			p = 1
			v = ast.numer.var

		elif ast.numer.is_pow and ast.numer.base.is_var and _rec_var_d_or_partial.match (ast.numer.base.var) and ast.numer.exp.is_pos_int:
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
						tail.insert (0, AST ('diff', ast.muls [i + 1] if i == end - 2 else AST ('*', ast [i + 1 : end]), diff.vars))

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

#...............................................................................................
class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJztXfuPG7cR/mcK5ARQgPjezW+O46ZG/UjPdoFCMAzHdooAsZM6cVsgyP/emfnI5XJ3Ja0ukk5yD8fbB5fkDIff8DGcXV2tv3j88MmLZ1+oLx4+eU7HRw8f0/HZCzn+7Vqinn5Dx+fXD7/5C53//OLJfY588Gd+9tW9azp+e+/6wZNHXMY3T55eP3h1/8X1' \
			b'o39w2ut799NJp7Ohszzm5M+ec+4nQuzvUtKf3n14m1Pw/f2njx/fyxQ44isq468PJB8zxDx8/fTFV48ePHsuBdynhBz54G9SJTl9+0gq+PXDvz/8+gGn+frpc6EuOZ69+ApHnbMLr/fuP396/fDeo0KTL7+9fvj4ARf2/Ckd3rz++O7XVz99fPX2p0/f/fju' \
			b'l19ff6TYXz5992+5ePffnz+++uXTz++6m+8/fXjz6sO7f+b7Nz+9f/+6pPyOLntZP3x6ny9/ffexu/7+4+s3+fpn4uBDvnn93S9d/E//6ZK/fvNrn34h15XYo/njD13sDx+6fO8//fjqh/c/59u3P/y7XH7/fcdvqRhnoIuOs7dvS6nv/pWvu6svXqr11dI0' \
			b'yviFwkXgC62WRs5RXTWqVRRhnGoXOU5iutulbvjKyb+hZ35R7lfldgkiDgdDRPQixdAVXVBRUlIj/5aygkZ334uhC85K/1YZymhRFF8wVx4HGxbpdqlRs1ZdaUplVvy/6KJs/1a7dMFxfEUsE48GFcGdjSIVW0X70V39PIzu6pjYvyOupUrMu0tXVyu5WUi1' \
			b'RdwkiXy/BNsrqk6iHPLDFNndLLUIXGt1ZZS1SgREV2hqep7kNvlccNLOSraqUy21tI6Xf6vzk3Rvyv1SGquVf+J3seiu6CKIGOIC13TBstFKy4UmsHAFGWFmkWMaleOqaGJJWFa57UmaWoClAw4kw0W6X4IACfaKqsrp0q2F3Dm+JwQTsyy5GVIptmtLKj+1' \
			b'bO92VUeEQiUoCzRwQ3pUBTxTDKDNpLTJVwYNzApiqEWoYgYSy1F0T9GLOtUwRb6nWyk4St1zDRMDXST1BVNxfFfiIS0qnnoN6n7WK0XpAqezpFVeRcU9jrPKOeW8co1ypJGUnJI5LtEF5ShxYBWkehHY3Eo5rZxRvlVhJW3sqSfjJgBUqesgtFHrkk57rzyV' \
			b'oLwKymvlKZdVnsXJXRLxRS0a6GFQIarQqNCquFJRq2hUpJR03bxkBLKALR/XV8w/3VEdNNfpimoiT72cohyb9KyVO2dxcinW8eMzrKZDFVybKmpQUXCvM/c6pRIx3DrLEbxaNIqVWx+Vby4FW7ZJNUhYAdaIDUg7iLSpQ6Pu6yJ1J0AjHMDkUcuwQqUNdMdI' \
			b'Ja0MK6dgas3drRCOhTBQcyLyDci3hXzQKhgV6MKdiAm7OrXUuUDuSnL3qIEGL83fEwDBxgcgBADxJuUAUC5SD1Afry9cnz2GA++SBguIZuQzafg0em4G9BgBmhpSNxkAmYhuMgJQEUmjkIhORZJmUDEyuylh0w3eNLm5JIHLBIN4vhRuIzN7/mw2l8Emcch8' \
			b'ni177ozZ43m2EaUXIfIMlpk9D9YCWLNyroa+Nc9izWgp4eV23866TC4NJpcGk0uTJ5cimJXQkBUy5mgcaxxYNJLoIscqa1L1ZWA4CUmTGtZIG55ucsVTShBuT0uYUATYBHMqIRNJewNlCGmhDiXQIi+eexrMMy8U5GueHJvLnlKiCbzu90ZrnmlebJsYAdkc' \
			b'tdWofECnG+W2msKuebJrMMtFtx0B5JgsTgG9d8R4QdKyC8wa7WgQiRI3tEc1E7F8a3Fr0xhqz8Xqs+ah3J7JUC5juL2U+TlPI0yaEVjMCCxmBHQaZEGn6VP7ry5XGX27qXZGasfzAwNrkIVVhk8ha6Z0r6exEYCPpHJUiu3NzsCq1zhBHQ2aL4DjuELG6NBf' \
			b'YHYXMcUc117UyJ2PUhMDbtRjMTPAqQNOncxUUW8vD2WK6k462QpoGoiPCnFoEmE/tV5Ee0V0DnWHTpXyqJRHpfwFq9aF8s6gEenLkQtB4zlojkPbudRXBjRXQHPRiQi9FAAGJPQpYTzb5fCaKxBRgShKBBt0sksK67UNlvhsUO8G2ZqUsjnvSrbnzJ4+Y/a4' \
			b'bdu0CbVKu1Ar6YZXar2S4qHcWGwk/n3Sft1W5ArDHbdGeoipOpbeQuQA+RBXXBGXJMDglO2RUpHBoEa9bFSR8EmIJbRa1XjVBNUQ041qqG6EDaNaq1qv2qBarghXlatJdVlRS6yoHisSqdSQ4rmO3EJcS96uYHs3m7J5A4l3j3gnh7dxeDOFW4NNDrwZyTuR' \
			b'vLXH23osTt7/4v1VHmt505L3gBkCfkXiDVxz9nngk2tlw138WChlUEsqh70KIt2z28RKdDSHJbtWsPsKtT+n4oN3ySeEk3Nko5Ykn6VnVwourPwtiZGWvUXAg2/E3YCJGnFmYApUR17cr6gEkv6SfXXYecL7XAa790T+p8TUAlwQu/dQqeyowt4tVtiiSG47' \
			b'KsKKo8CSHYgCu4YwcxQ0nHWoXZdR/CO4LGaB/71N1FgwdMvE6ByZGj/QQkmJX1CbWfMsVSrK6ZfqN2++XHLDaE/n8DtPrhjXzNIOXB8Ky30g+xn4HYBXC35vBN59gLsVrIxN6bv6aJXbKCdGvang2oeoPJLjDpCi0H5gqMqJARQFp0LPJNeqZgTPknWA0Bqe' \
			b'JVnwKHIWPCVl6LCZKU2iUwOUhVKFS736ktW95ZPlJqOz+10G5zt47gtPJ/B0NTwd4OkAT7cZnk7g6XbD0w2DwNPV8HTb4dll3Q7PLlnwKHIePF0Nz0RpGp4O8OwozYOnvYPn3vBsBJ5NDc8G8GwAz2YzPBuBZ7MbnqMg8GxqeDbb4dll3Q7PLlnwKHIePJsa' \
			b'nonSNDwbwLOjNA+ebiY8jz1pNfvPWyeRu3Heag8/d90KYm5G+AT3QCy3UU4kJ2npAmLTC31ASzI57gC0WQ0DA1pOCdBp6ioETPbFlVPOPQR4KWorwEuyNIEVEjXIpfRJnEviVFFAPdOchLokb/s0Z0Hd30H9SFDXAnVdQ10D6hpQ1zXUdQkV1LVAXe+Guh4G' \
			b'gboeQ10D6hpQT876yDGEelfUdqh3yTLU9RjqG7t0SZwqmqCeaE5DXQPqheYsqIc7qB8J6rKwM/XCzmBhZ7CwM/XCzpgSKqjLIs/sXuT1C0jFOFAZQh0LPYPZioFRIuUYQr0rajvUu2QZ6uOFn5Q+DXWs/UwxTWSa01DH8q9HcxbU4x3UjwR1K1C3NdQtoG4B' \
			b'dVtD3ZZQQd0K1O1uqNthEKjbMdQtoI53uuSUc4+g3hW1Hepdsgx1O4a63Qh1C6jbAvVEcxrqFlAvNGdBvbmD+pGgHgXqsYZ6BNQjoB5rqMcSKqhHgXrcDfU4DAL1OIZ6BNQjoB4BdeQYQr0rajvUu2QZ6nEM9bgR6hFQjwXqieY01COgXmjOgnrLUCekpu2a' \
			b'mwA+nhzzfgR7N7W7ckDw60MpABsPlLy7bGWXxdTGFwPji4HxxdTGF9OU0NcFkoqklOMudRgFUYdmrA6wx/AJvdqy5Biqg8SyIM2EfYZfYLVuqBpdWVk1xrYaoTStGjDXSAIjLSHqgQI3qAesNj26s9RDr/7IUHB6zbio0UDes5e37XsaYGG5sbDc2NpyY3uh' \
			b'0gCHlHLcoQF2NQysAXZsvLEw3lgYbyyMNynHQANKUVsHhJIsod6OjTd2o/HGwnhji/Em05xEvIXxpkdzHuLn7kLeTX72hbtYb2xtvbGw3lhYb2xtvaHbLvThLsnkuAvrehgE62PrjYX1xsJ6Y2G9STmGWO+K2o71LlnG+th6YzdabyysN7ZYbzLNaazDetOj' \
			b'OQ/rc7c0j4F1uwvuI8eYy0O8rGxtvbK1WNlarGxtvbK1toQK8bKytbtXtv0CUjEOVBLipYwEeixuLRa3Fovbkm+I++7Bdtx3yTLux+tbu3F9a7G+tWV9m2lO4x7r2x7Nebifu1d6h/ub4V6m9nzs4x4uVHxiafka976ECvdecO93494Pg+DeF9wXhyqhAYYM' \
			b'Cje9Aka47x5sx32XLOPej3HvN+LeA/e+4D7RnMa9B+4LzXm4v81N2P8H3AfBfahxH4B7+A7a2nmQpZhDhXvxHrS73Qf7BaRiHKhk3IeCe3gSWnz+ysLRoOQb4r57sB33XbKM+7FLoZQ+jfsA3Bffg0xzGvcBuC805+H+MDuyOr3VAM/6GyqA5w+b3EQNmp4m' \
			b'mAtQBi2DgK4HgeRHqzEI6HoQYBZyqBxtZBDQYvVifdD4vpucNnjc+GEQj5syGmiMBq1TbXK/wZigMSZojAkl99Abp19yTz00f2ds7JTTJU0qosdDg944NGgMDboMDZnutHsOhoYezXkqcrCd3D+oH39QM85eLaxsAdh6C8BiC8BiC8DWWwA2llCNEbIFYKET' \
			b'4kVmcdowUsRhkJGibAT0l8PYC7DYC7DYCyj5hiNFv8ztg0WXLA8W4x0Bu3FHwGJHwJYdgUxzerDAjkCP5jxNONhG72ekCfZI2uDEBOpqE6iDCdTBBOpqE6jrhb42SDI5kuz4RPzJaVob3GoYWBtcsYJKSdAGB0OogyHUwRBa8g20oSpzqzaUZEkb3Ngc6jaa' \
			b'Q7VJGVLdoRGZ7qRGOJhEe3TnacTB9oPPViNcVop4JnohtlJX20odbKUOtlJX20pZhjlUeiG2UgdbKZ9YL/RmvdDDIHpRLKZSUtILGE0djKYORtOSb6gX/TK360WXzINe8F3FBtqx0YCa0ycBJOVIxKeVAzbUHvF5ytGqdd4/rtTDTvnct5tXz03PsX7Sq37n' \
			b'fq+/uSf9BpwKRvu4rDdvp16RY2hu8phf7l7PMtr6bvHbfOLnbbXKt3/DeMa95T23vi/8BrQwVPoIwfv/B0ZCkO9gHgkPq3bDbDf2cOFkmJnGBz3nz+3yt3Y7rPCrLe42MUOVlu9dnwo6WviagI8uY3IW2QSUymigO1jlEWEIL31aeIWbIyzsWE/Fc+952jAL' \
			b'Re2EcWxvIHEhW7qhHo726IrMobFyHKDMAYk5Z6DMQQlX8bhDVcKIFi+HvXBiz2ny0tzNX7aAghcYx5/DuBN2HDftNfznMMScZpYCz01zhBHGzwCK2QcruucBdTO42IMvgVxCij4IWgLst3zaDy+SsVhnDwSZZHQ6XJ/C31eRr3/EEWLUb8bTirmV7yiEO+js' \
			b'DR14PPNpT+g0lwEdxklM7G6BTlTrU89WDjKZbW4wHHHTn+c85VATV917uWOPoach2ZwUAqe3szl7ju1+S3a19tTtfQrT6uh7ZFXzuyM3PxPYs/XdAZSec21vfzYhlu+G7fpiGLG7/rw7gh4MBAn/l52A+q2lGYCRFtefe4u7cEzFv0mTc38RTt7kpOTUEOFL' \
			b'AlwTv1w20vrms2/9eHatL+EsWt/KBw+1fOaKuMRubSOuECQ6dhKAd6VlD0muNztKGp5DEBbW+FbMMJPjhWNjkZwyWknuKXmYuwrl9ee8xed+68yd4NE8QODNMFkdzsaDpLzBinDPdd/2Rg9ttbajGonM5wh8jqgPJeck47ifwu0r2UNJlUXqaHqkf8cvcK6N' \
			b'fNN2JaimhVOCv4iormQDzlkiGOdLmQv5/PS6U52UvevswlBeEfpU1zC7LYW6bPklbHnpUstr0CQl6uA6D542ZHca9ilmezJlpGPbiCWYf4lJdrJj3o1mbpdmXnmk3+M/KcBWBVCvu7EMq/DXOGX7f1KMvHABv+euJOpJq8JMXZ7j0cmlP1qK5EseT+RKCvbT' \
			b'BcOBalvxJLLeH0a4Og4SDNsIwENrI5m0pd05NxFZarbBH4bVYexwRFzIr5MTK+GAzDQ8DdjjT7hoDs0FzSn2+RMm2jlMuLbmQ+9khXvDXaEdxPAwPJ1UOMWXA4LE7MXtqscw09jMNHc/PJvDxczQTz+VF8zrozNv1RECmDdD5vt+mXiFX94vm6yOl96JPSxd' \
			b'8a3s+1OWOrrkMSkukp0rZLut1kGdIuRTIyd2YppOCXHZo7d1VEcIYN7tbOtNFek38XSlVrOatFX9wPOyHAaPBqHNiWVuNpmIJ2btZEmovL/tyhv8PPRJA6oebr3qXp08oOrx1qse1MkDqt7cetVbdfKAqrc3q/r24Wx/AfCSdP9A6/5BDC9G9ywFC5vRtOpI' \
			b'g/tsgTi1PeAVjJ3JxoHX6POSQjKjOdttS6ZRtx0gmPOdD/LreecSICub7IS8Utb8y1sS6+R1ZhJU5N+E5g9usTjRKYsnVP+XnUROVG9O2SYrFRs+sinKpGYJ8pVf/uUznWx5lC8aFiVJCWmiyKizVjYaVheLmT7vhGvrZDlBhb5c/A9GT907'

	_PARSER_TOP = 'expr'

	_GREEK      = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'

	_SPECIAL    =  r'\\partial|\\pi|\\infty'
	_CHAR       = fr'[a-zA-Z]'
	_SHORT      =  r'pi|oo|True|False'
	_TEXTVAR    =  r'\\text\s*\{\s*(True|False)\s*\}'
	_ONEVAR     = fr'{_CHAR}|{_GREEK}'
	_DSONEVARSP = fr'(?:(\d)|({_SHORT})|({_CHAR}|{_GREEK}|{_SPECIAL})|{_TEXTVAR})'
	_STR        =  r'(?:\'([^\']*)\'|"([^"]*)["])'

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
		('VAR',          fr"(?<!{_CHAR}|['])_|({_SHORT})|(d|\\partial\s?)?({_ONEVAR})|{_SPECIAL}|{_TEXTVAR}"),
		('STR',          fr"(?<!{_CHAR}|['}}]){_STR}|\\text\s*\{{\s*{_STR}\s*\}}"),
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
		'abs'      : lambda expr: _expr_func (1, '|', expr.strip_paren ()),
		'exp'      : lambda expr: _expr_func (2, '^', ('@', 'e'), expr.strip_paren ()),
		'factorial': lambda expr: _expr_func (1, '!', expr.strip_paren ()),
		'ln'       : lambda expr: _expr_func (1, 'log', expr.strip_paren ()),
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
		name = FUNC.grp [0] or FUNC.grp [1] or FUNC.grp [2] or FUNC.grp [3] or FUNC.text
		func = self._FUNC_AST_REMAP.get (name)

		return func (expr_func_neg) if func else _expr_func (2, 'func', name, expr_func_neg)

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

	def expr_term_1     (self, CURLYL, expr_comma, CURLYR):                  return expr_comma
	def expr_term_2     (self, STR):                                         return AST ('"', STR.grp [0] or STR.grp [1] or STR.grp [2] or STR.grp [3] or '')
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

	def subvar_1        (self, SUB, CURLYL, expr_var, CURLYR):               return f'_{{{expr_var [1]}}}'
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
		self.stack [-1] = (s [0], s [1], AST ('*', (s [2], ('@', ''))))
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

		expr_vars -= {'_', 'e', 'i', '\\pi', '\\infty'}
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
if __name__ == '__main__':
	p = Parser ()
	a = p.parse ('\\left(1,2')
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
