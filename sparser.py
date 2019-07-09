# TODO: Concretize empty matrix stuff.
# TODO: Concretize empty variable stuff.
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
			b'eJztXW2P3DaS/jMHZAZQA+K75G924s0aaztZxwn2MAgMx3EWwcZJzrH37nDIf7+qekhRlNRSd0/PjLo9GI4kskWyqlgP34qkLq4++4+3v/74WfXZsyfPv/2G7k+ev6Tr0yfP6PrNt3L9+wsJ+upLuv7l2+efs+fxXzjs0cMXdP364YvHz59y3C+ff/Xi8avP' \
			b'v33x9D/53RcPP483Fe+aIz3+8tWzhy9fPPlH9DwqfN8Vvq87n6TKuTyidP72+CU/fvPyhZD5iK7PhdjvhKLPv3r27GGK8yLH6ajlhxdPvvwrM/Hw2dd0/eLR02+ePvzmr/T4+PkXmUD2PCp83xW+TCCn8BLZUxac8uO/i0Dl9vVTEe8XT7578sVjfueLr14K' \
			b'Bw8jCyyihy9fdvHZ//gfnzObX7948uwxx375FV3evH7/9sOr396/+vGHX/748Po9Bf3x8Yd/y8Pb//n9/at3rz+8evPbL33v+9/+e+D9I/n/+Pj72y7qTx9/ffPq9ft/5h9/oMde2r9+fJceP7x93z3/8P71m3+9/ZC8bz6+/+V/exl2ydNr6fl3YuPX5Hn9' \
			b'Q0fP6w8futx+z2T/9PrNhz6VmcKOiB6Zv/zchf78axfv3cdfXv387vfk/fHnf+fHn37qWHz7z34EeuhI+/HHnOrb/0rP3VPH/m/v3r0uPH989n11dbExvjL+ssJDkIdqY/mu6+qiqdqKAnRbtZcpTEI670YrfvLyb8kfLrNfZe9G0lYtLtZdRi+lISk5zozT' \
			b'U5ybRjQOjWFdwEYLuVr+2W/wCz9wkjEc6dPbMRAv2eqC86T0fAqgNPmJQ4USVeNiKbJSl4OgIpAf6YkS3bjKNNUGuVp+4DcCLha009NGNZIrEa+IYG34/7ILKrzKxgcO4+gkUua2vsw+lg2VTiiC/dCn2yIkjHyqH0J0ihYwez4+XSjxXAqjXJqGkkz+jbxF' \
			b'/FzomJdKP8bAzrNRYMVUF0Q28chSt5WFklHezeX231lDScF2eU2Vb22UlAeJGzqmWI66ItdTNfqxC88hHiEmhwSE2BzSIMSlENIqkZvFhSWJ+OSBkhqDi0geKRkjj/yk04+X0Uu+9IMEBfm3OrEY/Sb7N6JnSuFCor+8zI/01EiRAsQNPzDloYKmacVyUh0W' \
			b'kSiHxrBegBLhmw5PjDhArsFlE9ngR4V8qA4QtY5iptpA+CbpX9hecTKgoBUspliYrtNKyt34Ti2jV5UBocuFvBb1hq9QY/GDjg+bCDYGC+opLjvdVJZpiHVJDCI/BV+Wbw3fSH7ySu5OWI6MRVnlQG0mw9iXwyEkSp60i2ruK1LjUJFU6V2SCimqyEqLHlhb' \
			b'hYrrbu8q7ysfqlBXQbFwOS/L9aZvKs8VMcmFaijmlPDj6sqpqiHHKk46XUmzwGVBkGf0NawSgRIUDaHytxWlVQVTBcrUVcGzwpO4BTaV05WjK73kKucrFxh/pCVUGRAwSRgNEdpUDTUwddWqqtVVS62LrVpKit6p6++rC8rnktoq5vdS8CY3YpoEwRBlr8E7' \
			b'Gj4d5MerCyvhFyQQviGBJv7Wis873HwMDZLbiUrKg0MqakhDQxoQgraRRR1ZFkGeBl8tGLKg3Eoph7Zq6rNSdBsim1BxCw11NTS9aWKpioZ+MuhvohQUwBtvGrIwALYRvaD+mV0R5Vfco/uESupKWuBLaXe70gBI10QjsGXaTGNjqoZiu6rxa6LU1qi2U3ul' \
			b'AYQg0u3RLK1WbBRjVaFiAxCbPdT/Dq0BEyHpCWbOVhsvPEQQ7KeEwYuAFjJE7o3o0FFSNrGLZdTxkoy1uJOkva68qbytfF15Vbmmcu35lhRxbT9Jrt0nybX/9Li+cBiNaHTZFBqjBoFtHNS1+LFF29SipWrxaiuq0vqqDVVLYmm5fouNWJ0HhRqjQX3GjZkM' \
			b'bInBM2SMWCLGzoolUckz4aU5I168VBInzoM/dR54hk3LPIYgn6elWMVOh37fgH4r6jQYiFkpn8FMY8DIDRM4x58gqbtZI41ZI41ZI81DQS3S5nkTvhkL2o1Ds2kwBuyGR2g/MUg6u8bmwqZhsXQi1kOXAhKMj4UjDcjKZrN44gTUtSukjhoqdB0bu6qiJbrc' \
			b'zYDep8khjTkhjekf1Exn3hkOgpdPZU7nimfuNGbuPiG2L9BEhdhihXMf4RkB79EUpjfVy1N20iUwEKXHrx41pq9jL8VjKO7Qa7lw0e5iERel4WIT1SLFVlIsRuhXPJbXGMRr2FlRVbVx4B+Tb9tkxuVFB1Sq5hKjQTPuPknY0FDbTISy18BrYhfTnJSl84q7' \
			b'w+aUusPSDzZnNYLn/rqOPWqDHrVBj5pugziIoGvoGzGy5RXpcnMqKmqq1akHbmAyM7BK8a2JQG3QkK9GLg0qAQuMGvBMKRtULp/eDKeKvEMgUS7wmTqJxcQ6V6Oy5Ur+vMVyxW3IOTfW3CgaNIoGjSLfWoWbRom3mAlo0TVvRSLTNQOxb0+slWIqR+00U4zq' \
			b'0qK6tLJsRbFX6j+7unEjV7FSxYMdA1IpZZv6S0C5BbDlVx+RnfpJaCTa2OVoUZO3EjroGZGAHATkICB3xiCR1vCcGWSNluKUK+Xkou64VO9Ddxy0w6IysFAOG/sXHvrgoQ90I2kANB5LNjzed/H9cNqTv1fMbACzQeSDaQzMyxGxYTCjyiLg94mnBqJqELuJ' \
			b'EZozEEh76jwQWSfOA6tSG9dc1nHRZS2tWl1dUWpUjUUiqjYSFZN3MiPTSp6aKzqQzwQa4axhniZlAMK5q6ylz+xEhFpYDFFCQAMbxmvKsmZyLf1z54FGEjVlXbOUiCihit5hupgkXicqUiA/LwHm9b+8PpoX8PDKG147yQsneUUcL4fj9WY8Q86z47xgmhfb' \
			b'sjh4nQrPDfC0Ac8Z8JCbx9u82JjFx6XEFg6e6eRpySaQ2GRvjyz697IrgzepUKK8z4bibYJsFKhkQw9pyMbyngV6m8po43i5P/3Gu4l4P0ngVHhPCT1yYkb2W2wcr+5XsqJ+QwW8obLdUIFuAu8zqXmnAudDd1LCjfVIn7dg8M4e3jrAGwwaXvJP98Cbc2ps' \
			b'NSBZb1omlTmQDUcUh8KYREqNKfZx8w7FsLKthWLyxhCK0fA2DHqHKeH9HvQKlfHG8a4gDqaoLWfCzDMxFEbluwlO1vvz5qHAO1bo55ZfZcZ4ZxHLg+mlqLzPxdXf8+CRVXNCJW3SyqanmAmTaI2zkgqEGIedqkoXDc31jNr28YYBDcZ8nS6TlFAjRI32EdK8' \
			b'JLSn2lh3SSXI4Byq+Tb1pt+YxTk15+WSI1Vn9Q8LKt9ktec5MJ4fK9TfTkCATWgUzqvveOldBwn6jQ0TbJUo4NGw1LaAoengUAKCMmmkDjQjbLBe8qWHjyb+LeKkKf4YMYr12YNEAWUtwGk66DAFRmhRTPMARF1SAzBxciMMcbR2FknNEEvgahpPlAcTFxEF' \
			b'KjKq3BhZVFCMKS6BDmWR/B7Wqv/z9gFXIqQhdHd/Sp/lKu0+WAafvSXMFYALu+NsCmMm4uwmMHYIvpYwpaR54WsPVOJFaASV4CCjSn4p0SRx5NrDE4siuUVM9V/OsUKNpMv2SM03SUUKw+apgFN+bQZNQn0Bp8TSGFCqbJ8SDbN4kqQAo0xPgSSlH3BNp+TO' \
			b'2ROytGVEmXtErQxRXhDlS0R5IMpnRPkSUX6MKC+IKntwyme3jCg/4QRRfowoP4+ofgrziOpem0OUHyEqsjSBKF8iKtIwjyifEdXRsyOi7D2i1oUoVvGWx6Z9RIkXoRFR/NhDlPxSIkriyLWHKK2yW0RU/+UcK9RIukSUELAdUUUKs4jKr80gSqgvEJVYGiNK' \
			b'KMuISjTMIkqSAqIyPTsiyu2DqLsdcpmDR11zSJsbdbk7Gnktos4I6kyJOgPUmYw6U6LOZDeCnxH4mRJ+/QiL8DMTTuBnSvjF0ZcQgYwNcjZNijWEYz/FeTjmjLcPwnREpRmhMnI6gUojqNR5KJaomQemycDskt8RmP4emCcITCfAdCUwMQ3CtwRMVwLTZTcC' \
			b'phNguhKY/QiLwHQTToDppoHpAEwHYDoAE7GGwOynOA/MnPEMMB2AOZptTJxOANMBmL0WM1IzD0yXgdlF2RGY4R6YJwhMGfnpcuSnMfLTeeSny5Efl1pyI2DKEFCXQ8AiwiIw/YQTYPppYGIYKCcI4V3TpFhDYPZTnAdmzngGmB7AHI0ME6cTwMTIUGJGYEZq' \
			b'5oGZB4eZsh2B2RwbmD0T3i3Bs96OUHX+IBVFlUPEeiA1GEyaPJg05WCSzabJDUEqkeVKYm7l5DHcBtGWoNp/OccKNTIAVDndiFSD4aXBCFNuTYwkb5Vg7acpxM3htZf7dryKhBw4K/Ca2B3j1WDcKTGB1/juPF5NHnpmyqbw6t0DmVobw7Zl2CZb9PXAq9bV' \
			b'sBK/U23rnJn7NuFb3wSE9cA6zgETNkEOTnDWJZx7bmQWdEhPrr1mt4iziGU94QTLerLZFTpEswTMGmBGrCGSU3LKxAgDKG81vScqZjCtgWk9wnRke7tBXqJaKV0BNiIsADubD7OQhsBmTuON8Gz0n9izdYRmeGVI/hS6yAZ4Lc2NBuZGk82NpjQ3cgElN4Kr' \
			b'R3y59uHaj7MIVzvhBK52Gq4wP8rZpMjZNCnWEK79FOdb3ZzxDEItEDqySCZOJ1rdCFCbW91IzTw4s1EyU7ZjL1mp+/HrCYJTJpZMObFkYluaJ5ZMObHESxGTG3WNZWLJlBNLRYRFZLoJJ8icnlgymFgymFgymFiKsYbI7Kc4j8yc8QwyMbFkRhNLidMJZGJi' \
			b'yeSJpUTNPDLzxFKmbFdk7rUCZ23InBm6nj04ZekbX/vgDABnyOAMJThDdiNwBgFnKMHZj7AIzjDhBJyhA6cQFLEZgM0AbAZgs4s3hGc/zXl45qxn4BkAzzCCZ+R1Ap4B8AwZnpGaeXiGDM/M3F7DVbXXqp57lK4Hpa2gtFyjKl6EJpS2JUrb7EYobav47YA+' \
			b'SvsRFlHaTjhBaZtR2maUtkBpC5S2QGkXb4jSfprzKM1Zz6C0BUrbEUojrxMobYHSNqM0UjOP0jajNDO3H0r3Wil0j9LVoJQhJjPufZSKF6ERpfzYQykXTXJDlEpkfMolo7SIsIRSO+UYpTbvxhCCgFKhAfniEx+bqDyIMEBpkeYsSntZb0ep5ODAVoHSxOsY' \
			b'pUIvokSUJmpmUSqpAaU95vZD6dFXH92bbG4ZrmKysaXJxsJkY7PJxpYmGy6a5EZwFZONhclG1ugZ3AbRFkGrJpyANptshKwIWphs4qJAC5NNjjcErYRycaQ4s8DN2c8AFzYbO7LZJH4ngAubjc02m0TNPHCzzabH4H7APfrqpHvg3jJwtQC3tM6IF6EJuKVx' \
			b'xvbcCLhimbGwzFjYWi1srUW0ReDqCSfAzfYZm22tFuYZC/OMhXkmxxsCd5DsPG5z7jO4hV3Gjuwyid0J3GrgVmfcRmrmcZtNMj3+9sPt0Rcv3eP2lnErS39tufTXYumvzUt/bbn0lwsluRFuZemvxdJfvhm8ZgbRFnFrJpzgNi8AFrIibrH+12L9r8X63xxv' \
			b'iNtBsvO4zbnP4BargO1oFXBidwK3WAVs8yrgRM08bvMq4B5/++H2fm3TqeNWrKu2tK5aWFdttq7a0rrKJZLcCLdiWrUwrfLNGNwG0RZxayec4DYbWIWsiFvYVy3sqxb21RxviNtBsvO4zbnP4BZWVjuysiZ2J3ALK6vNVtZEzTxus5W1x99+uG2PitvRySJH' \
			b'hC6pJanicQBszhTEfP4H/17uH22wfzQfc6DKcw5Uk91oI6mcdKBkoRjjWL4waqr4DdYi5uKO0mbCyY7SpsOxgjVW8a5LFTeX4hgE8cX8+/GHe00HyffwrKRrMtpyminZjmnJyIHLAtOJ9TGmhWxESZtPI0WzmJbU4ubTzONemNY3scBpbc2xPv8WWUuLrMsW' \
			b'WaNF1rlF1mWLzAdC2ehG650C4ss14GYMbjpH0zs0yv2Xc6xQIwOAWedGWaNR1miUNRrlHG+4O6BMtlky4vYImNkjgHZZj9rlxPEYw3F5os7tcnx3YY9Abpd7LO6H4aMvglobgM8dvVaaYls2xRZNsc1NsS2bYttkN+pPS1PM14Ab96fRDhfRFvvTzYST/nRu' \
			b'h21eFWXR/lq0vxbtb4437E8Pkp3vT+fcZ/rTaHvtqO1N7E70p9H22tz2Jmrm+9O57e3xtx9u55dI+RK66h69R0Rvc+zOtKyaUuWqKYVVUx5LGn3sT+eFU3y2XiOvkfNSVY+61LJ2SmHtFN+4Px3Qnw7ZTeGYRy65Px0mnPSn8woqlVdQKaygUlhBpbCCKscb' \
			b'9qMHyXLp1Ntw3Mt9pg+NRVRqtIgqsTvRh8YiKpUXUcnQLVI034/OC6l6PE5g2dUPuHZMkK7VA66vpqB99HVV96AuQW1uoVl2Yg92pT3YwR7ssj3YlfZgLoDkhnCWyHINuPEBqbAHF9GWmuX+yzlWqJEB4OyyPdjBHuxgD3awB+d4AzgPk51tlnu5b4ezgznY' \
			b'jczBid0JODsI1iJahHSiaBbOLpuEezzu1zQffcXVqePXA8PM9+nhWMzDrjQPO5iHXTYPu9I87HpuhGMxDzuYhx3Mww7m4SLaIo71hBMcZ/Owy+ZhB/Owg3nYwTyc4w1xPEh2Hsc5dwhFg4gpNMNI7EZG4sT0GM1JioiVwBzJmgdzthP3GN0PzK66urEjom/q' \
			b'fGj+hNiNnRE9BaQEogI4XB68zrC6iyOib/54aDnxb6zgRzgiekKTtxwTTRQua2dztDPMSaC3eoy52U9N+avkPDjbdqQ5f4aF7RMycumrLc/mq2p4zHmzr/6q9rg6PHHMuZIBydF1eV6PWbj76HIS+JZjz3PbW+p2an+HOh72qYHtMc7pR6/IrrE2Ngun9quZ' \
			b'Gvmap/ar8b6Po53cr7CfQ+ljqrWS6bmjVNEs5JmT/Fne26pp6mSo9gHJ/U981fXw7oQ92kcn+IMZN1Fh76rF6uBvT1xLgye0V7VH0uC5Y4mnDsC4re9PsHAP+wYFSermur67KiqGnUfUVf4Iumb9rG+xL3yC30uRr7xMbJc7WG9xzI6SNux6HWRu5XbRYap5' \
			b'+eMOzvyJrzZe3eUgDh+M2/38o2NWt9yF4wLwh1S5JzN+U7Knua12O2foyJ/4QebNAdUsUX63iunudfMWdJPCvLo7/dz4+lD91NfVT3VtFbVH1tKtM81L2qpXqbF+h3VUh2kt02SOqbl+tCpq46enfctO7LW12FxXi/XRKtq2uaG6dhcN/nS0t6+5LJfj17s7' \
			b'aO41tdZeV2vN8bS2vdfaW9fam+gt3LzWuutq7Xbb9v6d2vpebW9bbeXoktNTW7+r2vpDx2KmXH2xkyFtTl/nFkfdgK1XjGdaDDfH1NkAw0K4/pBMUopKG5c97GUp266oC58yPa7Fl782y4rKmU7Oa+nmAYFcprXCvdLeidKyehFJfLum0kpK56C0XpSWWVhS' \
			b'2qa6Wstympue4wrXXUZjT2F+q1DIm5zP4oV911szQ/lerUP1bmFq9TCVcyelbjc+dXqQmpFUVqJmtzSLv6hqVvo1SvaiTKqdvwu1c4dpHUe7CcUTcnbSO162Vn7dfum79sTe1RoUcg3KONkRzNrHI9n7Om+vOo/XOVEHTz59QoTca9pcC9ucTPPKu0fWp2rh' \
			b'Ae+YrGlEwa1b+2DTiNqZe7WbVbvT6dU5cSeidra6UrKJy8m+F1EG15DA+TQhL0qBjbSiHVa6h072/bJe7q6LbkrbRLPUblokmjOrNdwMRlVgQR1S8rIUfmqeokbZ7VBWYalsRIS+E+EBc1tmzymto0xb7QreMCwKhckmdTAeOeqhE0xHmEbaDXRMJJVtf6qI' \
			b'Si4V8r4lvHuFfWvlWpSpvl4Fe0i38VZKMRYh1ZW2liLk2b5YMUaBZ6Hw8Qe1itWjHMXb9hMTnLc5fq/QOuH7QXoiJhFRn/Vua/AgfYpwsZFDcJScokMiDQrrjpk22fMkC+Z5/IqFw0zURm+LQn2M/Cevmt6r8qWz/iZeEmBQxQ5brE6K+16xl5U/2lHxH3+W' \
			b'Q4zxyclaaNlhEuQF3jQVfxGro2x3EirsMaigWLv8SYZuIUNnd8uTmtXRH1sYJsIlXzmRm/cez2ZNuj3MneNMUuClAzjxx5MrPZ912SekhF1JwU7tnQmiV7f8pc7n5K9CU7MfTdg9vhtl2NaVt1ITpW0195e6yFt+HXRgmXo5RrK5PfqJQA6/QSdsqfq2+VLV' \
			b'DTvwpQ7ji1rSEWtmH/Z0dYibCOKB11wksKkjm/oonOppbpmU7Rxz3c9jVTxcx40TmUoWjJu7Z9xVt+vAuB0y3jvII37ZNciZHTvIwUtbxMdw+N4BHOWhG+WpGnyiBmfuBoIycaagd0TVWGBtdTdOZqNDGebCtvchZnfn+sXzRrfqwLhf1K8dJVCo1VZpDBVp' \
			b'SYl4Kq3nQrqGMnzR8bgL0XjENf0KDQDGeZUOMgsrl1moVuMgsGblAmuq1TgIrF25wGQ6cR0Oo+R63QLjuaS1OAhMrVxgplqNg8BGXe+DBLbYBbum2Hx1fcdz0MMgfXh6EN+oA3+b/dj95dhU8w7H0y2+tovjKd99IkCedzou2FuePHm+Ugdxjvr/6xanr9bq' \
			b'IM7lUcWqxBmqtTqIc3nAsSpxttVaHcS5PBxZ65wK26fW7iDjNq5VYLMGCwcWKuqms7BF0hAY8cuGhjqaTzu7qMfELp9awWb3hi3pKrDhiyI1UZZNNHxp+S5uV1YkVzYJWN4BLdtJa95Sj1fN5Kuu6jm8aEcvclnxy77qO+ViBCfFkxdliAWRrYceTTbv+1K+' \
			b'lYPY7feX31/+PyjTlW8=' 

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

	def expr_mat_1      (self, LEFT, BRACKETL, BEG_MATRIX, expr_mat_rows, END_MATRIX, RIGHT, BRACKETR):  return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_2      (self, BEG_MATRIX, expr_mat_rows, END_MATRIX):                                   return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_3      (self, BEG_BMATRIX, expr_mat_rows, END_BMATRIX):                                 return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_4      (self, BEG_VMATRIX, expr_mat_rows, END_VMATRIX):                                 return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_5      (self, BEG_PMATRIX, expr_mat_rows, END_PMATRIX):                                 return AST ('mat', expr_mat_rows) if expr_mat_rows else AST.MatEmpty
	def expr_mat_6      (self, expr_curly):                                                              return expr_curly
	def expr_mat_rows_1 (self, expr_mat_row, DBLSLASH):                         return expr_mat_row
	def expr_mat_rows_2 (self, expr_mat_row):                                   return expr_mat_row
	def expr_mat_rows_3 (self):                                                 return ()
	def expr_mat_row_1  (self, expr_mat_row, DBLSLASH, expr_mat_col):           return expr_mat_row + (expr_mat_col,)
	def expr_mat_row_2  (self, expr_mat_col):                                   return (expr_mat_col,)
	def expr_mat_col_1  (self, expr_mat_col, AMP, expr):                        return expr_mat_col + (expr,)
	def expr_mat_col_2  (self, expr):                                           return (expr,)

	def expr_curly_1    (self, CURLYL, expr_commas, CURLYR):                    return _expr_curly (expr_commas)
	def expr_curly_2    (self, expr_bracket):                                   return expr_bracket

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

	def _insert_symbol (self, sym, tokinc = 0):
		tokidx       = self.tokidx
		self.tokidx += tokinc

		for sym in ((sym,) if isinstance (sym, str) else sym):
			if sym in self.TOKENS:
				self.tokens.insert (tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

				if self.autocompleting:
					if sym in self._AUTOCOMPLETE_CONTINUE:
						self.autocomplete.append (self._AUTOCOMPLETE_CONTINUE [sym])
					else:
						self.autocompleting = False

			else:
				self.tokens.insert (tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, ('', '', '', '')))
				self._mark_error ()

			tokidx += 1

		return True # for convenience

	def _mark_error (self, sym_ins = None, tokinc = 0, at = None):
		self.autocompleting = False

		if self.erridx is None:
			self.erridx = self.tokens [self.tokidx].pos if at is None else at

		if sym_ins is not None:
			return self._insert_symbol (sym_ins, tokinc)

	def _parse_autocomplete_expr_commas (self, rule, pos):
		idx = -pos + (self.stack [-pos].sym == 'LEFT')

		if self.stack [idx].sym != 'CURLYL':
			if self.tokens [self.tokidx - 1] == 'COMMA':
				self._mark_error ()

			if self.stack [idx - 1].sym == 'LEFT':
				return self._insert_symbol ('RIGHT')

			return self._insert_symbol ('PARENR' if self.stack [idx].sym == 'PARENL' else 'BRACKETR')

		# vector or matrix potentially being entered
		if self.stack [idx - 1].sym == 'CURLYL':
			if self.stack [-1].red.is_null_var:
				return self._mark_error (('CURLYR', 'CURLYR'))
			elif not self.stack [-1].red.is_comma:
				return self._insert_symbol (('COMMA', 'CURLYR', 'COMMA', 'CURLYR'), 1)
			elif len (self.stack [-1].red.commas) == 1 or self.tokens [self.tokidx - 1] != 'COMMA':
				return self._insert_symbol (('CURLYR', 'COMMA', 'CURLYR'))
			else:
				return self._mark_error (('CURLYR', 'CURLYR'))

		if self.stack [-3].sym != 'COMMA' or self.stack [-4].sym != 'expr_comma' or self.stack [-5].sym != 'CURLYL':
			if self.stack [-1].red.is_vec:
				return self._insert_symbol (('COMMA', 'CURLYR'), 1)
			elif self.stack [-1].red.is_comma:
				if len (self.stack [-1].red.commas) == 1 or self.tokens [self.tokidx - 1] != 'COMMA':
					return self._insert_symbol ('CURLYR')
				else:
					return self._mark_error ('CURLYR')

		else:
			cols = \
					len (self.stack [-4].red.vec)             if self.stack [-4].red.is_vec else \
					len (self.stack [-4].red.commas [0].vec)  if self.stack [-4].red.is_comma and self.stack [-4].red.commas [0].is_vec else \
					None

			if cols is not None:
				vec             = self.stack [-1].red.commas if self.stack [-1].red.is_comma else (self.stack [-1].red,)
				self.stack [-1] = lalr1.State (self.stack [-1].idx, self.stack [-1].sym, AST (',', vec + (AST.VarNull,) * (cols - len (vec))))

				return self._mark_error (('CURLYR', 'CURLYR')) if len (vec) != cols else self._insert_symbol (('CURLYR', 'CURLYR'))

		return self._insert_symbol ('CURLYR')

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

		if pos == 1 and rule == ('expr_func', ('FUNC', 'expr_func_arg')): # and _FUNC_name (self.stack [-1].sym) in AST.Func.NO_PARMS:
			return self._insert_symbol (('PARENL', 'PARENR'))

		if pos and rule [1] [pos - 1] == 'expr_commas':
			return self._parse_autocomplete_expr_commas (rule, pos)

		assert rule [1] [pos - 1] != 'expr_comma'

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_int':
				return self._parse_autocomplete_expr_int ()

			return False

		return self._insert_symbol (rule [1] [pos])

	def parse_success (self, red):
		self.parse_results.append ((red, self.erridx, self.autocomplete))

		return True # continue parsing if conflict branches remain to find best resolution

	def parse (self, text):
		if not text.strip ():
			return (AST.VarNull, 0, [])

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
# 	a = p.parse ('1 + {{1,2,3},{3,4}')
# 	print (a)
