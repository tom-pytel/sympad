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
			b'eJztXW2PGzeS/jMHZAZoAeI729/s2Js1znayjhPsYRAYjuMsgouTnOPs3iHY/35V9ZBNsrsltWY0Hs1oMBw12SLZxWI9fKkqts4uPnv+9MU3X3/Wffb0xSv6fPb0OX1+/Y18/u2l3PryC/r8yzcvPufEk7/wvUcPX9LnVw9fPnnxjMt+8eLLl09ef/7Ny2f/' \
			b'xXlfPvw8XVS6ai705IvXzx++evn07ynxqEl926S+GlJSKz/lEdXzn09ecfTrVy+FzEf0+UKI/VYo+o93v/zARb58/vxhLvqyFB2I5sjD51/R5+NHz75+9vDrv1L0yYvHhT5OPGpS3zapQt/Lp1/89VWq6ZVQ8Tk9gu88+ZvwVS5fPRMuP3767dPHTzjP4y9f' \
			b'SUMeppYwp54/efXXLx+/TkxGSiLPHz0ZKuaMT/7+ObPhq5dPnz/hal99SR9v33x49/H1rx9e//D9z79/fPOBbv3+x/f/lMi7//3tw+v3bz6+fvvrz3Xyw6//GiV/z+nf//jt3VD0xz9+efv6zYd/5PTbX9+/f9MkqnLfU7R67C9/vM/Rj+8+DPEffv2Yo99/' \
			b'ePP2v98Nybd/fPj5/yqyBiIoW47/Ro39JSfefD88/bfSoB/fvP1Y018IHGioqPz5p+HuT78M5d7/8fPrn97/NtD80z9L9Mcfhxa++0ddgCIDZT/8UGp99z85PsQ++667OFsZ3xl/3iESOKK6lZZr6M5CFzu6YVwXz/M9uTMkVypyzMq/XXcrd17SVZIidNWa' \
			b'61Q9PSJyrTqc59vpZrmz0kZiPT60o2edpzsU40jMX52nJKXyF7il5HlxeJ4fbqeb5Q49k2PUJGlRlH9L9/vzJr0ud1Z4muEPar0bHgP2DF94PGp0N+QkpSTGvdAZqtbgG44wlx0+LB6rmBHSZcSyM8WEr/n/fLil66QyKcL3OEZdQ91hUgZJ8beKWN/cduPU' \
			b'6Hs/San6DtEpYkW0KZtiZ0hISqTC0INzeiW5FOVS6Vkqf5luDomVkv6ntp/pjrqO+5Ja7ZQ0g0hBp85/z5JOgrok2yjXCrwkdkOIuZVGd0bVosyk5vvljsMdXe543DHlTsAdm++QUApnLD4g9ukOAGAMPpjJqRylOMoxnb88T0lK5S/klpN/q3MTU9qU9Erk' \
			b'rJd/Yvz5+RCjiJf+RLM9R5hsYgRGj8hM6keI4Lt9DQa+QR0qnM9YlIQgi5gkH6vESo4qPIcGIsasAiYoaSE+xBFT9aWJWSRYmlL9ZhBJ6nnji0wiuW5vhOEplLQyNhB6ASaOqBShx+WYFtFX3AH0aMe9gyEq36I03T5vc41z5DQl5elOmpwalnhVbur5e6sy' \
			b'6lEMTKLqaWyl4f9i3RmWK5IfGqNs6Hi87zsfO993Yd0F0wVuoVROOW0XVBc0cYEGI24XQcURYEznbBcpOJpDmOeEa4IYDZYkXCRPjBDdxXUX6U7nOt8FCvS42AV6OmWwLCTEe0d8oc/Qudg5okREg6BGcGAxoVZpngm4BYFkqOvXXa+6Xne96Xrb9a7rfdeT' \
			b'4FHNjoqY71hIuYsMf16cUWslxTd5AqR2c5razhd8xvQdsvqIS5/uBqnptjMlgCvUvWCLkiQ1SS4mtVVb5JJvb1kDNVpm0X1WOjMSPeZuSrlbo70OPenQkw49edYrfKuEDTQd0VBKEw4NhTRZncAY0Cd2QJ5jujgwxQD2RiTFykLu+JpwwUu9U+w76h8MxHZd' \
			b'+gdAPkZiLfBndUWs7yL1TOxif5wkG8i/SqO+AVii8LsinnAU0ziS5gVMnk5wxDsqueSpVe7effk882BJCCcJz7OAbg99GkxFmK7jQSYx2thre0KaEJw8yRMnfedD503nbedV5/UJdCg1P5x28+NpN78/4eafeeyLNC4qbSI0ZjiN+U5jvahjWlsjb592mD3m' \
			b'xh5FehTpUaQX0eqJw2umkShcax5C0wS6LptUfX6HuSzbbmrh3Wxb4KbdtUbFu9goL626K43p70xjWMemZSDUfGV9FDftNjZEoSFWJK3ZS12wTkpPlI4Rmy8obK6bvGgGpZGG0khDaaR5YlM9iFdpesJUppJKSQ26FC5jAvIaaWjSVZiyHcLCAZuiuzuxndmk' \
			b'T7XY/B4fgQo9bVLXsiHseHVerEwBmfqYySTQAhoxHGevE4HxkwwnfVYkaeiP0Hl8uftbhwtWh+kT1ABdsAJQQ/N3mu1X8SQbfoZuD2nqD/FUgG5kPXpdUJrq0lnlKQszD057ZPKYdXy21nqsyDz0+Gc+2bwCymJh5tLEr91JiuwF63BOseGstNJJPaWhl9JT' \
			b'TdQFq6009FUaPhB9EsSkEFsn4aLsUIIR5edQ6JjJXibIvbEDRZy5y0mDpEkbP3M7HQ8ueLdqbuVuVbap5m6q5XhfrdNW12Cra7DVpcuoTNopJVFUaXFjTmV2I8o28ES298w22fvz/szl3b6Bgd7A9M2XmCarKAPP8TWU90RMvMVI49Hb9CCDmfaEjSAKHanQ' \
			b'2eBIwGAecM+YzCaTFiQaKxHWEp8Imy54pXUSYwKvIQ3WkAZrSL5oCIbGzN8DR72DRPR92hKu01VYNT+oEF/sbZ3smdzJuodIt5hjLOYYK0smYIbaYpOm1B6vTouHbRnM0TwPmulBNu9DME5YjBMWQ4Nk8mjnsA1RWVospIUvfZ5c12moWUuu6XqUpQCsdGCl' \
			b'OwXAySR8Ei1lGDiRMwc5c0nOXJ5eIGcOcuYgSQ4iZNMIY5ME2bTA85AYD4mhC/HoO0Geh7uaTwVcKhDuiOHsgpsd0OwgnMMmDUYJojqMHfqICMnPR7qEaRGlYyoQ7xJn+rvTGHNnGsNS1ieP9XVyWV/LNLruLtZCDwa+4QGqsiuy6nXdsKA8XoZObpsR6uda' \
			b'jukXw+ss18YNlrUtbwcwBCvuAGrJwC8wEe7J4DjjrWcWVDNbJ64+a9pFrakVa14JUfukgfQ9N5HbyI3kVjKL2XGfT2fw0Qw+lcEeSeyOxE5I7LjLTpHsvsi+7OzIzj7T7DDN7sjsi8w+vnzWhQ+68FkIPi7A3vCsb+SZmlWKrJJhfQyfDeHFGB+h4NMufEiE' \
			b'e4vdfdnLlT0+2XLMbvTsQ8/WLzZ9sfmHnaHYE4q9oNgFiv2f2Pmpj9SjnjnKB8gCHxzjg1J81I+u9CTfrfigFEkLxYhbK85KtctX9EFhxUfT+BxblEyeP0g++aQeH27y6W/l1zgTKWen+JQm10tFSehWgU9PEvN99bfiRvKhPWq0EEhURX5U4C8tn+br8XxB' \
			b'l+LDibHHkTLq76oi6gW5co6e28GHx6i7uVYuRLTxPx+BkxaTnPDRTH4K08VnHIlWPpEX+dsoXKGifDSQCHLpMSSOK5LHFQnkqmeC+XSmiCtTSV2xCny6NRNFcX6+lwpwfpK/pkK9HObjG2tmqWK+c5dQTvqWZ1JUEfkAL98lvP7p1YMVRIiu8d88lTJQZdjY' \
			b'CVT9SfBZg9NfDpNzeLQJk9eFx6ticRf+GBBMdwNASWq5JABKtoJA1SKPkx6lCvaULmER/uoCqVgwuDAKeqCQuacHCDL+auCNK2CeIzbGXwu+UkKBGxvAJyxp0JeKzeBPqokN+DJVC+GnCuoKgQ3wFAGOZU2ZBzx+kNzQ1fxbFnj3ALwVAJTpT6aaCoCYAPmS' \
			b'AWhbANoWgFYAaFsA2hKWAdCOgwDQTgFoNwNwVIEZYjsAOORLp+g3AdBOAIhicwC0UwAmqpYC0BYADgQuBKC5B+DtAGAvAGyXoJLUcskA7FsA9i0AewFg3wKwL2EZAPtxEAD2UwD2mwE4qsDYHNsBwKFEumwCYD8BIPLPAbCfAjBRtRSAfQHgQOBCANrlALzB' \
			b'vaI+yHZxGzB3bRfDEWwZd4GUd4U991MNUknKa1oySCVbASnypJwVWjnpUbygtcm8BK11gUyNwaVCa9o1CgWimGHQSmooVaF3XKGxObYdvaVE2j/KE6YIlhwRLGtAnErPgFhqQpEKx5m+hTiWuoHjitRlOHb3OL47ODaCY9Pi2ADHpuDYtDg2JTQ4NoJj0+K4' \
			b'zrwIx5MgODbzODbAsQGODXCM7DWORxUam2M7cDyUyDg28zg2wLGZ4Bil53BsgGPT4jjRtxTHpuC4kLoMx/4ex3cHx7Jr1e2uNaltddm16nbXyt2ZQ4Nj2b7qdvvaZF6EYzsOgmM7j2NsYTUW0ZJSuVSN41GFZojtwPGQL+N4fksrOSJY1uIYpedwjF2tlKxw' \
			b'nOhbiuOysa1IXYbjcEAcZyPSJ0MzCdhGQK9PHNNRMB1bTEdgOhZMxxbTsYQG01EwHQXTPV6eKJdRkUXIjuMgyI4DsmtgRwA7AtgRwJZC/Wit3VbZp+U26t8B74GODO84D+8IeMcJvNPNGXhHwLvdNqf8i+EdC7wLqTPw9vqBKDemKI+McvbZs1fBejyyaTvs' \
			b'nLnDFuPrJ0Y761auF/EMhk5eyGqDgL/VgmlowXTRgulWC6b7EmrwR/FSYvy3GrEm/yLk9+MgyO/n53RoxaRViSSVS9W4r2pT6S2quOg5LZnU48cDwEBOHgDmNWaSI4KD7QCAInMDAJRmUjJIZw+DAMosHgSK7qwid9kc319xjj823J/4ct2I+sy06jMD9Zkp' \
			b'6jPTqs+MKqFBt5U7HjUUdDf5l6C7LpCKBYPLFN0GGjQDDZqBBi2VqtA9rtDYHNs+pZcSCdFmXoNmoEEzEw1aKj2DaAMNmmk1aJm+hWg2RYNWkboMzWp9v/W+O1gWjw3TemwYeGyY4rFhWo8NedV4CjWWjbhumNZ1o8m8CMh6HATIeh7IcN+Qt4+jIVblUjWQ' \
			b'RxUam2M7gDyUyECed+eQHBEsa4Gc+DgDZHh0mNajKtO3FMjFqaMidSGQ93CrOiYgb9t1nzSWRY1mWjWagRrNFDWaadVojIQcGiyLGs20arQm8yIs23EQLBc1GkczlKFFM9CiGWjRSrkazaMqS2wHmktlCc3zijQDRZqZKNJS6Tk0Q5FmWkVapm8pmosirSJ1' \
			b'r5222sNV6x7UtwDUXkDtW1B7gLr4NJvWqVl+dSeFBtTi1mxav+Ym8yJQ+3EQUPsCal9ADQ9neRS+sKoqV4N6VKWxObYD1KWyBOp5d2cDlxMzcXlOpedA7QFq34I60bcU1L6AupC6H6j3cP+6B/UtALXox/izBnUAqEMBdWhBHUpoQB0E1KEFdZ15EajDOAio' \
			b'QwF1KKAOAHUAqANAPZSrQT2q0tgc2wHqUlkCdZgHdQCowwTUKD0H6gBQhxbUib6loA4F1IXU/UB9SJeye9PXEaFbTF+mNX0ZmL5MMX2Z1vTF3ZZDg24xfRmYvuTH25AyoyKLMB7HQTBeTF8czRiH6cvA9GVg+irlaozLHe6T8rWxObYD56XChPN525eB7ctM' \
			b'bF+p9BzOYfsyre0r07cU58X2VZG6H84P6XJ2j/Mjwrn4epvWymVg5TLFymVaK5fpS2hwLiYuAxOXwUQul1GRRTjvx0FwXgxdHM04h53LwM6VfMBLuRrn01qNzbEdMC/1JZjPW7gMLFxmYuFKpedgDguX6VuYJ/qWwrxYtypS94P5IT3S7mF+PDBn8ZQOqGEu' \
			b'SY0fpAXMJVuBOXdYDjXMOelRHJUapMyoyBKY1wVSsWBwAcw5mmAuZOAXdCFODPNSroL5TK3G5th2mFf1AebynCnMJUcE9xqYp9IzMJfSKFLBPNO3EOZSN2BekbofzO8d1u4ozMWqbVurtoVV2xartm2t2laV0MBcTNoWJm0LhzULh7WmyCKYq3EQmBfDti3m' \
			b'MAu7toVd28KuXcrVMJ/WamyO7YB5qS/BfN66bWHdthPrdio9B3NYt21r3c70LYV5sW5XpO4H83hAnxV9nWC31QubLgF5tRn17kSQr0TFrloVu4KKXRUVu2pV7Nz0HBp/FtyRz4jVvPzCNG6bUcFFBzn9OMhBzqJuV1C3KxZJrow5DLW7gtpdQe1eytdHPCe1' \
			b'RyjfU9ZqKFB8/HLmsGepFsOBmlfAq3Tmc6KAT6XnznxCAa9aBXzKv/jYZ1HAV6TuNxwc2IXt2Cb+LaPAKYwAWrxgdOsFo+EFo4sXjG69YAIO2yNLPQI4ueNRA+o1fvixdF2VWuS1qsdBvFaLOwxHs9MqvGE0vGE0vGFKudpvdVIrkS2eq8i6w2W9VJk8Vufd' \
			b'YjTcYvTELSaVnvNYhVuMbt1iUv7F3qrFLaYidS/I60O6uR0b3k8Z7Fame9tO9xbTvS3TvW2ne+6eHJqFvsz1FhZ1i4neYqJviixa6PtxkIV+mehtsatbTPAWE7zFBF/K1Qv9aa3G5tiOhX6pLy3052d2i5ndTmb2VHpuoY+Z3bYze6Zv6UK/zOwVqfvBfJsT' \
			b'nG2QjtcQ3oP9usAermt972R979r1vRPAe8zu3mKJ7wbMMwJ4lS+Bf+nENbDnpEclqNogZXIRhE2w581VWd+7cZD1vSvrezfAXsiweBS+sKoqV6/rp7Uam2Pcd0zChre3lPrSgt7NL+gdFvRusqBH6bkFvcOC3rUL+nWhcemi3pVFfSF3Bvo2PuBBNo8AaxoB' \
			b'WDpmRoJDes7djwHbx4D4qSd9sdXZ1lZnYauzxVZnW1ud7UtoJn2x1Vns7i1sdRa2uqbIokm/HweZ9IutzhZbnYWtzsJWZ2GrK+XqSX9aq7E5tmPSL/WlSX/eVmdhq7MTW10qPbudT21AsXriTzQunfiLva4id7+J/5A+dXcJ7qGC/PqWw15gzeyuYe9gu3PF' \
			b'duda2x13Tw417J3Y7hxsdw62OwfbXVNkCezrAqlYMLgA9q7Y7hxsdw62OwfbXSlXwX6mVmNzbDvsq/rAG5XvzYHfwYLnJha8VGQG/LkylKqwnwldiH1XjHgVzfth33YX+TR6g35Af8B9xjoDPXvObsN0aF+QOHk7ouByjMdtZ8TjBvzFKe6WvvawwdcmbGVc' \
			b'1VhqD3fPvWI7w6nGUo2fVet3vggnjIrxCws3va1wNXsCZPbINQvEasuLCUdSvemN2OMXEtZCvFGAs/TWQoufnbh2ocSPTR1MNNWBxFNvEdFtU8DxiqmSd1/ag4vrlpfZ7iOyymwU261j7ybR9VtF1x9Iet2hBXjrK2azAPs9hXhdrWk81Bq7xlzWIfCWnRUL' \
			b'jWBTmtt1WQFX4ZqFnEXJX4+gz6scKkFnLu8j7Mz1QeGQOL9rvC4rzdgCIC83x0AIy8ZwfaBhHLsDczAsHHhAd/0e6w59+EFdhYPLfCPvCjKv0gscDyT3vDU64CDP3F66PmHubxzoaWGt1QNqvCyh4/6rFXXIBQsxQ8R8bot7iGF/TszdFlEPSdTtUSyzVTiw' \
			b'qG96QbiBXlkeePAhfk7MmbubRV2LqDOnr7wc729sj4hfsbrZnSK7PpmjEOXr3jEqcbeec3n4VDtHUKCuLLLE6xsTWXsvtZ9WauUskL1hyV0Rtw8iuerykkuPvarwmuuQ30268R1y7OJxy3K4LnlmafIHl2mmdyTXft40Xcu2EuoPKN/6CvLdH2xwZrm4rvF5' \
			b'iWyfoFzXMq1mj1YcZKxeINMHlWdzhZXG+nDyHO/l+Ubl+drWHp9anq9iENxu599Lnvt7eb5ReTZ3RZ5v1JY4eKMMfigHVNDJe7ZZ8cSeOmbHPtGehLFxkQ1GhfJ/eIWdvF6edaCioZt4hbQKPLuPQVKJF9o+8t/9SR35gB4rP5y53TQ5IMFeFgzr1l/r6nZJ' \
			b'/wn8PjbJebZ4xYPKO3cqkceXK0q81JSEPjlHHcroGK/dIWSTZZ1/316EmcvMyrP2D2i8EHFeaGC8F+drFOce4txfXZz7OynOIYlzv1ucY3dxJG54162iNgdcdjBHj1s9PRXV61RHs+PwIf2ZqFEXRyGUN+ETurcw6tsliNduEzmAABIVxyGAN+WYvE0InayY' \
			b'eJrZIJDmJgRSnnoJeeRy1yGS7pIunko2lPTFhsnbqwc4k7ima5SfRlfE85sX1WMT09kFZ5FL7rL7cfIq42T3Jx/oUCKC+l4El07X7vbM1Xwwzh25DLoHfLh8TaLIB+doUMSYaO4FcqlA+lskkL4Tbf4tFEjbXSg5xIoDeHixWCD+s6bHiLzgbQQiOF5WoU5e' \
			b'nkAyO5VHPxK1LB6lu2W6Q/8JxbMdIhnqWSfzpW6o0OIPRou6Mi3hYLToK9MSMy2X0Pn59b6qvkOo8y41cogKr2IdI5Qq5cslB4O4voLi7QDqtcsgnulxrlGhUU9mAdi39/eYSW6kz5v+Vlcb+S+1BL6BHk7dS4O4laPKjjUBacROfdEMJdI46So7DBWjIYJm' \
			b'iItq0B+PTHyaaTQ6xcy0mRGID+qPHkFlzlbyHiWFN7XhB1CrFyFQl4/eUjC8n4BtveIrmd4bgPcAcMvEvhz4Z7bpk70jcsA5pT59zwfsjM8xmgZTJp7UcKiOmbDSh6aP6ln+JySYbSS4y1FBOB/9sTlmenf4E0rkp2d4RbiZGGLkNnrcFposr1Pt5I+1SZN7' \
			b'JJVVWohzi4jDqzMuSyJtLGb/8pJ50/fyJ1T6PajECz4uRSuOH5YXXBDtodv8l5f62/KEySKc2yPvNfc306LI25t49T9pSLzBhvTdQf6kHf0l2kEz0Lam2D2bw3vHfQPvMTd9Z/udFUjT1Tq1fU+E7Wi+2cwCpmwzG7gwb78RuXqYrWruJrihjosbpruhAG7o' \
			b'MTfqtzOBLfjlyF3M8TLD8buVXPVWpcnLlOY5FrryhqQw4l5MWhK7jYuhu8kgiz5Ypevb/MKC+SLgvTkuSYzdDQVww+6WxAVsqQVwKYsmIrdL3FjjWAXafuETkYWBd4Aow3u/3dmpldOHtgGMdLeIka47vgAu+lvERd8dXwAXwy3iYuiOL4CL8fZwkbVlRxfA' \
			b'xf7qXFyyyDkgL013xcAa5vEtHa9aqwSogSZbixtZPl6Kua7bHvDmz53ZlgRW5l6qJJg82bHcGiazvvzYA3h8HPugS/HYdEcfwOPJfuf28Nh2Rx/A4wW7qGPlseuOPoDHCzZYx8rj0B19AI8XbL9ugV6KrcO3JoDxIXm2sC8L8S2JfJQf9qMeMDCsZeYltnFm' \
			b'x69OjJE/myOlcmw0VdPvrsZ3GwKMfvxSJpXkAD1KPcDl+mR4HwzqAct+eRmO5T0pv0s0so8UFeL3I3IP95ia+I0itSRRT7P9wfA7PvooJ8kd+MPvapjJabsqIKOdZGTh4cyuq4PyyZ7pRF6KK5HYltmuHGDC4MOXKq5FVUf8/O78/wH2c3oK' 

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
	def expr_pow_2      (self, expr_abs):                                       return expr_abs

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
	def expr_bracket_3  (self, expr_dot):                                       return expr_dot

	def expr_dot_1      (self, expr_term, METHOD_LEFT, expr_commas, RIGHT, PARENR):  return AST ('.', expr_term, METHOD_LEFT.grp [0] or METHOD_LEFT.grp [1], expr_commas)
	def expr_dot_2      (self, expr_term, METHOD, expr_commas, PARENR):              return AST ('.', expr_term, METHOD.grp [0] or METHOD.grp [1], expr_commas)
	def expr_dot_3      (self, expr_term, MEMBER):                                   return AST ('.', expr_term, MEMBER.grp [0] or MEMBER.grp [1])
	def expr_dot_4      (self, expr_term):                                           return expr_term

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

# if __name__ == '__main__':
# 	p = Parser ()
# 	a = p.parse ('$vars')
# 	print (a)
