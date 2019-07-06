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
			b'eJztXW2P3DaS/jMHZAZQA+KbSPmbHc9mjfNL1nGCPQwCw3GcRXBxknPs3TsE+9+vqh5KJCV1Sz3d49FMD4bTktgkVSzWwyJZRfbZ5RfPnjz/9psvqi+ePH9Fn0+fPKPPb76Vz7+9lKgXX9HnX759/iU/XPyF4x49fEmfXz98efH8Kef96vmLlxevv/z25dP/' \
			b'4rQvH34ZLypeNWe6+Or1s4evXj75e3x4VDx9Vzx93T9JqfyWR1TOf1684ttvXr0UMh/R53Mh9juh6D/e/fojZ3nx7NnDLuvLlLUnmm8ePvuaPh8/evrN04ff/JVuL54/TvTxw6Pi6bviKdH38slXf30VS3olVHxJr+CYi78JX+Xy9VPh8uMn3z15fMFpHr94' \
			b'JRV5GGvCnHp28eqvLx6/jkzGk9w8e3TRF8wJL/7+JbPh65dPnl1wsa9e0MfbNx/efXz924fXP/7wyx8f33ygqD8+/fBPuXn3v79/eP3+zcfXb3/7JX/88Nu/Bo9/dM9/fPr9XZ/1p0+/vn395sM/uue3v71//6Z4yPL9QLfZa3/99L67/fjuQ3//w4c3b//7' \
			b'3ce+kE8ffvm/jJb+zZSsu/+davhr9/Dmh/6VP/7WJ/89VeinN28/5vQnAnsaMip/+bmP/fnXPt/7T7+8/vn97/2Lfv5nuv3pp76G7/6RZ6Cbnsgff0ylvvuf7r6/++L76vJsY5rKNOcVbjzfqGqj5RqqM1+FiiKMq8J5Fycx/eNGtXxn5d/W1cadp+fskW7o' \
			b'qg2XqVp6ReBStT/vomNkitloK3ctPrSjd53HGLrjm9B9dR4f6an7AlFa3hf69zV9dIxMMfROvvPVJvA1yL8lbrTnxXOdYjbyNuXBCuv610T2dF80eNUg1neP9CQ0cCtUhoo1oIlvOIXDh8VrFTNCmkzXVA1uLvk/76N0/qhMvOE4zk5NQ81h6vP0xLxXxPoi' \
			b'2g2fBt83oyeVxxCdIlb0YmXj3Rke5EmkwtCLu+eNpFJcgfgu1X0ZI/uHjUJVVHWmK6q9yKGunJJqEClo1OnvWdJJUJckG6TaRF6qKMRcS6Mro3JRpi/7+BTjEKNTTIMYk2I8YmwXQ0IpnLH4gNjHGADAGHwwk2M+euJbvtPdl+fxkZ66LyTKyb/VXRXjs0nP' \
			b'G5GzVv6J8efn/R3dNNKeqHbDN0w2MQK9R8tMaoeIoNi2AANFUIMK5zssSk8gbyAmyccmspJvFd5DIBIWgSZ6tBAf4ojJ2tKETiRYmmL5phdJYrtpkkzisS4jfP8WerRAKrVG3d2oeEOv6+60iL7iBqBXO24ddFFdFD1T9HmZapiie6ZHebuTKseKRV6lSD0d' \
			b't0m9Ht2BSVQ89XXU/V/WlWG5IvmhPsr6ivv7tmpC1bSVrytvKs81lMIppa28qrwmLlBnxPUiqDgCjKmcrQIFRzqEeU64JohRZ0nCRfLECNFVqKuguB/n93uSgMpWrmoqT4FeHSpPlFBiywJD7eCIR/TpKxcqR1SJmJBwcKdGgWqoq7auWlW1dGOq1latq9qm' \
			b'aknwqDRHycz3LKTcRIY/L8+otvLEkawAqd78THXnCz5D/A5Jm4BLG2O9lHTbmeLBFWpesEXJI1VJLibWVVukkm9vWQU1ambRfFYaMxA95m5KuatRX4eWdGhJh5Y8axW+VcIGUkfUlZLCoa6QlNUJ9AFtZAfkOcSLA1MMYG9EUqzlgdz6qnDJQ71TbDtqH3TE' \
			b'tk7tAyCvkVgL/FmdEdtUgVomVKFdJ8kG8q9ir28AliD8zognHIXYj2gHRQHtqQEg3SnOqDXwpUNShX5YdYpXYu++9J41YJj3JwneM49m923sakXUjlW4icw19qilRrXgpPSGuNRUja8aUzW2alTV6BNoOKq+P+3qh9OufnvC1T9rMDvSuCjowxZPbZxJttBy' \
			b'LdRbC2XXQhO2Ijwt8bDmN9N7a82dYVSFdZqM6vM7zEeZXlMN72bdPFftrlUq3MVKNVKru1KZ9s5UhtfStHSEmq+87sRVu40VUaiIFUkr5kyXvPakR4uLISoVmVBdB0nB9AtCGgtCGgtCmheEVAuCVVRJUF8qLhepfp2E8xiPtEYqF9chTJrMYDiAKc3dVWZn' \
			b'Nq6VWkxd10egQkub2LRs5FrvehYvlIBMvWYyCaiARvDrbHUiMFxbF9J2C0Ma60E6rv3oE1zKuOTVrlOsOC/vAal8ufv1veSVy1Ns6Eteq9VYpD3N+qtwkhU/Q7P7iHMfTgXoRiYcx4TP2NTBq9My8m7A3QaJGgwrms7U3mDI3cAIc9ZEg6VHXoy8XRzZtSix' \
			b'lRKHq0yXvCSlsRal4cfQRnriclYd30HJscxF3D3HYo0ZzVO8xA2dIMJELD8aPJo4qTO303ngkmei5lbORGUKau7mkhvPmXWc0hpMaQ2mtHQZ5IkzoiiKKuo1cyodG1G2hScyjWe2yRyf52Gum9UbGNkNzNd8CbHPCtINra+iPPeRhSMn5Gp0YBb9ToO2d/ju' \
			b'pK15rIsMNJPwAgxC1+4RZ0zHJhO1lIZ64vXgE2HTJavfk+gheGBhMLAwGFjwpQVyWgcZaNs4G6jjVZgz3akQJ+xtVfZM7mjcQ6Rb6BgLHWNlyASUUF1sXBG161274m7boHe06B2t9I4WvaONvaPtBqfoJyz6CYuuQRI1qHU/NoWqaDvlWsfOpZb48XiUpQCs' \
			b'dGClOwWIiRI+iZoyDBzkzImAOQiYiwLmOr0CAXMQMAcRsrGHsVGCbBzgNZCYBhJDF6rY94K8Bk5lTczgYgZ/R4xil1xtj2p7YRkmaTA+ENV+6JRHL5b0vC1LmBaQO8QM4S5xpr07lTF3pjIsZW30Oq+j23ktarSuLmuhAR1fX6jK7Ie86lYXLMgrQF0n6sZE' \
			b'NxM1h/pF9zrJtWElZTTLEwB0wYobgGrS8whMhIsxOJ578DIjpNr0T1OomqpQ8zCIKie1o+px/biCXEOuIvOUPe95ewXvreBtFexBy+6z7DTLXpHsy8iO6OzszJ7O7EfMTsTsnMuWR7Y68mYV3qnCmxnY35/d2XnNiV31eCGJ12N4MYY3d/BIjPdA8HYV3uXB' \
			b'TcUeueyIyk6ZbB5mP3h2gmcTF9u32N7DXk7s4sTuTVxPdmxir6Y2UHM2zE7eAeZ555eNWw/pSm9qqg3vdCJRoTti0oaTUunyFX1Q2PDeMt6IFpRsAuPNdfxBQsnb7XiHUhP/Ng3vWKxlr9Om5XIpK0ncxvP2R2J+k/1tuJK8644qLQRS8YFf5flLy9vxWrxf' \
			b'oKV4d2FosSeMGluK0D4vkLfYtVwP3p1ZaymVMxFd/M871KTGJCS8X43fwnTxJkWilbfUBf5WqkhfeN7bRwS5WDw12IaEcUPSuGn5Vby9UmSVqQy85YxrFSIxvFWVUjANjRSCTZC8AVV24/FDzXxXzHfmLaWiDKxGUUTgHbgcS2D9s1EPNhAhuoZ/sx5llEo/' \
			b'MYtS/VnAmSOzuQIgp8BoIyCvC4yHAnEOfIIEbpUcffKo5RLRJ8kS/NQYdhzVIGcCntIpzIIvTxyzeIMLQ6AFBJmDuscfgy9HXcyn/aioIfhK5KV0CtzYgjxhSQG9mG0CfFJMKJDX0bIQeypBLhFYoE4R2ljWlHnAnQfJDV3Nv2Vod4++9aNPFJ8omQx9UH18' \
			b'6dBnS/TZMfqsoM+W6LMpzKPPDoOgz47RZ7ejD/m0HxU1g74+XdwAvw19doQ+ZJtCnx2jL9KyFH02oa8ncCH6zD36bgH6WkFfOfKURy2XDn1tib52jL5W0NeW6GtTmEdfOwyCvnaMvnY7+pBP+1FRM+jr08XLNvS1I/Qh/RT62jH6Ii1L0dcm9PUELkSfXY6+' \
			b'G5wf6sOniLtQOTdF9CuYJs4hlGeCLTdSjlB5lLNVOoRKsoRQpIkpB1DlqAZFJKgWGeagmifuqDG4ZFCNM0WhQFZiGLHy1OfKoBtjtB8VvRu6KV2cM8obxvCVFKh8ieCYewLBUhKyZCDuqFoIYikbIM5IXQZidw/iOwJiIyA2JYgNQGwSiE0JYpPCCMRGQGxK' \
			b'EOcZZkE8CgJiMw1iAxAbgNgAxEiegxgx2o+KngFxn64DsZkGsQGIzQjEyD0FYgMQmxLEkaqlIDYJxInUZSBu7kF8R0AsM1VdzlTjIq1OM1VdzlS5LbswArFMWXU5ZS0yzILYDoOA2E6DGNNWjbGzPKkuVw5ixGg/KnoGxH26DsTT01hJgcoPQIzcUyDGTFZy' \
			b'ZiCOVC0FcZrMZqQuA7E/LojFRjRpbroOKJNwzaPZnCCgZfKry8mvxuRXp8mvLie/uk1hBGiZBWvMgll2qe5yGWSbhXU7DALrNBfmQjtUYzrMFxOJUjFTOwA2vtZ+WHg7j+2ejg7b05NkSQE+DLCNLFPYxjxZcmbYRvrF2E5T5YzUCWw3+oEsaIwhHhji7I1n' \
			b'DwM6vFJWp7DrSZ3tdxhZbwDqfDjItcFdTvOs5ORUev9GmilHvjxquUTk822GfG7WLgyRT7zmWHxm2rzIMwf7PHHM4nEK6YQ2FyIszihFXazqcmWgjzHaF+VyS+F00wHqBY3NAP2JnIh+edsY/ZIigIMF+mPuCfRLScgS0c+NzT1AzLO0B5Dy0QNk5C7T7u3B' \
			b'2n2loD/BUboRa64prbkG1lyTrLmmtObKIcIxjKDtJbZBKRm08zyz0NbDINDW09CGdVeOFkZdrOpy5dBGjPajoncr85Sug/O0tVdSBHCthHNk5QScYfA1pbdFR9VSKCebb0bqMiir+n66fUeALGtmplwzM1gzM2nNzJRrZuyE14UhkI2smZlyzazIMIviURAU' \
			b'T6+ZGayZGayZGayZxVw5ihGj/ajoGRT36ToUT6+ZGayZmdGaWcw9hWKsmZlyzayjaimK05pZRupCFO/hOLUmFC+aaZ8ckJ0A2ZVAdgCyS0B2JZCzMAKyEyC7Esh5hlkgu2EQILseyHzb4dgBxw44dsBxny+HMmK0HxU+A+VUWISym4ayA5TdCMrIPQVlByi7' \
			b'EsqRqqVQdgnKidS9ZtdqD2ese0SvHdGYPvsS0R6I9gnRvkS0T2GEaC+I9iWi8wyziPbDIIj2CdE+IdoD0R6I9kB0ny9HNGL0uPAZRKfCIqL9NKI9EO1HiEbuKUR7INqXiI5ULUW0T4hOpO6H6D0cvO4RvXZEB0F0KBEdgOiQEB1KRIcURogOguhQIjrPMIvo' \
			b'MAyC6JAQHRKiAxAdgOgARPf5ckQjRvtR4TOIToVFRIdpRAcgOowQHSMnEB2A6NJZrKNqKaJDQnQidT9EH9lp7N7KtQpoi5XLlFYuAyuXSVYuU1q5TJvCCNpi5TKwchmgWy6DbLMAb4dBAJ6sXHzbARxWLgMrV3T9TPlygCNG+3jHrZMSzoA8FRhBPm3mMjBz' \
			b'mZGZK+aeAjnMXKY0c3VULQV5MnNlpO4H8iM7ld2DfA0gZ9kU7ucgtzBo2WTQsqVBi1urC0OQW7FmWViz+IKf95NfO8uzzYE8TxyzeIMLQM63EeQWJi0Lk5aFSSvly0AeY7SfKn83xrPygHE7bcyyMGbZkTEr5p7AuIUxy9YFxjuqFmLcJkNWRup+GD+yz9k9' \
			b'xleBcfEEt6UnuIUnuE2e4Lb0BLcqhRHGxRPcwhPcxp/wVMB4nm0W42oYBOPJH9ymVXELd3ALd3ALd/CUL8c4YrSfKn8G46m8iPFpp3ALp3A7cgqPuacwDqdwWzqFd1QtxXhyCs9I3Q/j9y5pdxHjYr22pfXawnptk/XaltZrq1MYYVxM1xama74YPJlBtlmM' \
			b'62EQjCcDtkAqYhz2awv7tYX9OuXLMY4Y7afKn8F4Ki9ifNqKbWHFtiMrdsw9hXFYsW1pxe6oWorxZMXOSN0P4+G4jinm2pBus6OXDsG7LSHvTgT2/APMLbdnsQ2zEdirdACIKk8A4ap3YeS0guLkuxbglx98RmIzyDy7N7MZBtmb2fTg51uuLcsjF8RcxhEh' \
			b'8joksCrLn+/aRIz2E+8J5Zxd8Y7Kif2bqVj0BWr65BAVt3GOTg+Juae2cTbSF0jObCdn5OPSnZxN3xdkpO7XFxzfSW2dKt+entbXovV1qfU1tL5OWl+XWt9j5zySDOGPHylvUArKNk3/w+U6yznri66HQXzRk+LXSfFrKH4Nxa+h+FO+3BcdMdpPlB9mF+Oz' \
			b'IoF3Pa37NXS/Hun+mHvKHR26X5e6P6Zf7I6edH9G6l5410d2ZFsn2E8N6VYUvS0VvYWit0nR21LRc9t0YTS+Fy0vRaBggyczyDY7vm+GQcb3ScXbJo3vodotVLuFak/58vE9YrSfKn9mfJ/Ki+P7aZ1uodPtSKfH3FPje+h0W+r0jqql4/uk0zNS98P4Ljc3' \
			b'W8AcZwfeI/1akO6va1gvnm+q9HxT8HxroNcbi5F9cn5j8efBvQT+uYqx/5sS/zcF/ze+GDyZLhvCFOZ5TpWG9W4YZFifvOBU8oJT8IJT8IJT8IJL+fLhPGK0nyrfYFq37RyWVF4cx087wik4wqmRI1zMPTWOhyOcKh3hZIoZKVs6lk/OcBm5E7i34QH3sB38' \
			b'a4I/S8dEN3Bk37j7DmBbBxA+t7oX27stbe8WtnebbO+2tL3bNoWRuhfbu4Xt3cL2bmF7L7LNqvt2GETdJ9u7TbZ3C9u7he3dwvae8uXqHjHaT5U/o+5TeVHdT5veLUzvdmR6j7knp/CxDsiWq/xI2VKVn8zvGbn7qfwje83dDaz7DO/1Lce8YJp5nWPewRTv' \
			b'kinelaZ4bpsuDDHvxBTvYIp3MMU7mOKLbHOYzxPHLN7gAsy7ZIp3MMU7mOIdTPEpX4b5GKP9VPm7MZ+VB96oLm4K+Q4GeTcyyMcsE8jvCkOuDPgdeQuB75JNPqN5P+Db6rLbXV5AH7jvQZ8DXSXH2K2A9uUJh+PjDd1+u77DFviFCdjtGmNnMBvBawpaHaxy' \
			b'KJXbtacOx+7QlENpCJ9NU/igzsKEQTE8c3DbgYMs9gs3UbM8bHacLTgQ6m1nWQ/PFBzK8KT8dsKbyyx+WOLaZRK/CnUsyVRHkk49I6HbFMB6pVTJ6ZX26NK64yzafSRWmZ1Su7Xn3Sa5zU7JbY4kvO7I8rvzjNhOfsMVZFjHAU2D1Yy5HpeXDXimThUp5ZpP' \
			b'GtVXl2/lr1nGWZKa65Hz6ZWGTM6Zw/vKOnNd1hki5+d66zTMDKX8d2PNIQ78sh5cH6kTx7zAHAsK19Gdq4WDDn38Ll2NN7YdPPjIxV1B5FU8hvFIYs/ToiN38cztJYMT5v7Wbp4G1Vo9oMrL8Dlcaaiijzdakbku/2DPMfv8+oqC3kDYXbuaEbbyRxT0bf26' \
			b'wl5MNbkB88r9u3Kj7ZdLBJ05DmE3h4/E25ucHVK7yK8L3uAckX+mm3/BewWSfN1zRSXulvoG54ygYOyvvI/EEq9vUmL9vdB+ZqHlfQD2hgV3w0PwQwVXHSS4vMp+oOw2xxbfbUviS8S4Xrco++sSZ14vb44q0s14FNFM26KHos3rTUcTb31Yv1wfsWuur6l7' \
			b'XirbpyfXuUwzj66hq14o00eTZ3OYPKsjyrO6l+cbledrsbN8bnk+0A64w7a/tzzre3m+UXl2d0Geb9aGaMQDpXc/OeLaHDWGMlwP9s2h79i58sRtjPus0cm1+z/mWh0vfYa49KnE9HU8O6QS37Ol0l/9SY34gF4pP3e52yLZ48BeFQp16aF1sDmy+UzOHlNi' \
			b'3hm6wlHFnduTyOTLgQIvJUWZjw5Rx7I1hs/iBTJlT+efoxdZ5vST4qybB9RdiDQvtCveS/P1SXMLaW4Pl+b2Tkqzj9LczktzqC7X4Xl33YvT5ohjDmbo+hemS0m9zoVodhU+pg8TVepyDTJ5U16ge8mivl1y+FmMIQfKH1GxCvm7SU/kbTLoZLTEOmaLPJqb' \
			b'kEd56xXEkfNdh0S6Kzp1KplLUtotmrtRD7D7sKZrkJ8zV8TzG5fUtUnp5GAziSW32H0veUgvWf3J+zeUSKC+l8CFutrdHkXNe+DcykXQPeBN5DVJoufWf7BBj2ju5XGhPDa3SB6bStbwb6E82upSyXZV7LbDsWGe+M9LPEbkBYcOiOA0MgJ1ckaCWiyjzfin' \
			b'GUTcphxgJkRLRGlWhESJQi54tWRfEZBmH2o6WdVWixpM1h7nG0b416ydf3bd/PNr559bN/9Cz7/9F4Kbes/132Os8V5JqYRhq9SiKPhyRT0R6gNWY4+w5noVZcD0ULPn66rUkF3779v4y8cYN9LkRXOrw8YEV5oa3UADx9Yl9W5lx7rj9aGoy2NbJB7x6UZc' \
			b'OWkq21Gdl8cdBI0dLrPhQFdM3zRqUKQwDkzLmdGf4xGGr6A8Zxs5RUvJoX4Gv4qbnYRBTR5PqiiPqRDbP3vOdodH4DAIrpd4G3j+yXT+bFPgDWv4jj0DcCcPQcz9MRG7s2BzJbNgo49LHQ2xlv8JAWYXAdQE+9NgquEfG+fGsf2f0CG/LqT0LlLcLo64HRRZ' \
			b'nrjY0R8vLo7iSBqzZyHNLSINx6ZcjUCaZ07+dVOobd/Ln9DY7EEjjna5AqXYfJrONiHKfbX9r5v47UrjR1Myro2cXt/cRH0Cz3TD4X9SjXBj1aAsx/iTWrRXqAVpnO0VsXtWhtcQ9g281rDtO9vOFiAVV3Ws+Z7I2ll5s50BTNd2JjCWeA0GN4eHyaKmIsEL' \
			b'tSZemOqGAnihh7zIzuKKTMHvk86xphGNxidpuewMrSlmcf0LfvkqHYjlB7zrDrWyu3joq5sMMriDS0IezUdUTGcB582apDBUNxTACzsvhQuYkgvfMgaNxG1O1Hi5OQs0xcInbhYGnuUhD8/v5pNTHccvLQPY6G4NG121vgAeNreGh021vgAe+lvDQ1+tL4CH' \
			b'4dbwMFTrC+Bhe1t4yCuJqwtY1BlNHPbn4fKh4RE4aasDAy+/D6N4sffggg2WYPRo+nEDQ+4rsbapdgcciDubbHng5e4984DFa5jVXIXFbEVYewCHR7OX28JhW60+gMML5kTr5LCrVh/A4QXTpXVy2FerD+DwgsnU6leX2JR7awLY7qOHEvskEdeiuAf5+UVe' \
			b'ZsqNT5F1nNTxgZetHHuJTcF1vikYhbRzhTTVlgATHR+mpaIEoC2J+5yvjRby3vTtsaghpxhZnl3yCT6B/dwoU4hWhBbqiM+CyWWIWpktByx5vATOx1mw/MUSzWRiX2UBCe0oIcsOJw5VHlSDPpu3iLNM9R5hYghmI7CH/YH3zqpQy4obMfT78/8HjMa8wQ==' 

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

# if __name__ == '__main__':
# 	p = Parser ()
# 	a = p.parse ('$vars')
# 	print (a)
