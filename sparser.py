# Builds expression tree from text, nodes are nested AST tuples.
#
# Time and interest permitting:
# sets
# var assumptions
# importing modules to allow custom code execution
# Proper implementation of vectors with "<b>\vec{x}</b>" and "<b>\hat{i}</b>" variables
# systems of equations, ODEs, graphical plots (using matplotlib?)...

import ast as py_ast
from collections import OrderedDict
import os
import re
import sys

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

def _FUNC_name (FUNC):
	return AST.Func.TEX2PY_TRIGHINV.get (FUNC.grp [1], FUNC.grp [1]) if FUNC.grp [1] else \
			FUNC.grp [0] or FUNC.grp [2] or FUNC.grp [3].replace ('\\', '') or FUNC.text

def _ast_from_tok_digit_or_var (tok, i = 0):
	return AST ('#', tok.grp [i]) if tok.grp [i] else \
			AST ('@', AST.Var.ANY2PY.get (tok.grp [i + 2].replace (' ', ''), tok.grp [i + 1]) if tok.grp [i + 2] else tok.grp [i + 1])

def _ast_func_tuple_args (ast):
	ast = ast.strip (1)

	return ast.comma if ast.is_comma else (ast,)

def _ast_func_reorder (ast):
	wrap = None

	if ast.is_fact:
		ast2, wrap = ast.fact, lambda a: AST ('!', a)
	elif ast.is_pow:
		ast2, wrap = ast.base, lambda a: AST ('^', a, ast.exp)
	elif ast.is_attr:
		ast2, wrap = ast.obj, lambda a: AST ('.', a, *ast [2:])

	if wrap:
		ast3, wrap2 = _ast_func_reorder (ast2)

		if ast3.is_paren:
			return ast3, lambda a: wrap (wrap2 (a))

	return ast, lambda a: a

def _ast_pre_slice (pre, post):
	if not post.is_slice:
		return AST ('slice', pre, post, None)
	elif post.step is None:
		return AST ('slice', pre, post.start, post.stop)

	raise SyntaxError ('invalid slice')

#...............................................................................................
def _expr_comma (lhs, rhs):
	if not rhs.is_slice or rhs.step is not None or not rhs.stop or not rhs.start or not rhs.start.is_var:
		return AST.flatcat (',', lhs, rhs)

	if lhs.is_mul:
		if lhs.mul.len == 2 and lhs.mul [0].is_var_lambda and lhs.mul [1].is_var:
			return AST ('lamb', rhs.stop, (lhs.mul [1], rhs.start))

	elif lhs.is_comma:
		for i in range (lhs.comma.len - 1, -1, -1):
			if lhs.comma [i].is_mul and lhs.comma [i].mul.len == 2 and lhs.comma [i].mul [0].is_var_lambda and lhs.comma [i].mul [1].is_var:
				if i:
					return AST (',', lhs.comma [:i] + (('lamb', rhs.stop, (lhs.comma [i].mul [1], *lhs.comma [i + 1:], rhs.start)),))
				else:
					return AST ('lamb', rhs.stop, (lhs.comma [0].mul [1], *lhs.comma [1:], rhs.start))

			if not lhs.comma [i].is_var:
				break

	return AST.flatcat (',', lhs, rhs)

def _expr_colon (lhs, rhs):
	if lhs.is_ass:
		l, wrap_ass = lhs.rhs, lambda rhs, lhs = lhs.lhs: AST ('=', '=', lhs, rhs)
	else:
		l, wrap_ass = lhs, lambda rhs: rhs

	if l.is_var:
		if l.is_var_lambda:
			return wrap_ass (AST ('lamb', rhs, ()))

	elif l.is_mul:
		if l.mul.len == 2 and l.mul [0].is_var_lambda and l.mul [1].is_var:
			return wrap_ass (AST ('lamb', rhs, (l.mul [1],)))

	return _ast_pre_slice (lhs, rhs)

def _expr_mapsto (args, lamb):
	if args.is_var:
		return AST ('lamb', lamb, (args,))

	elif args.is_comma:
		for var in args.comma:
			if not var.is_var:
				break
		else:
			return AST ('lamb', lamb, args.comma)

	raise SyntaxError ('invalid lambda function')

def _expr_piece (expr, expr_if, expr_else):
	if expr_else.is_piece:
		return AST ('piece', ((expr, expr_if),) + expr_else.piece)
	else:
		return AST ('piece', ((expr, expr_if), (expr_else, True)))

def _expr_mul_imp (lhs, rhs, user_funcs = {}):
	last      = lhs.mul [-1] if lhs.is_mul else lhs
	arg, wrap = _ast_func_reorder (rhs)
	ast       = None

	if last.is_attr: # {x.y} *imp* () -> x.y(), x.{y.z} -> {x.y}.z
		if last.args is None:
			if arg.is_paren:
				ast = wrap (AST ('.', last.obj, last.attr, _ast_func_tuple_args (arg)))
			elif rhs.is_attr:
				ast = AST ('.', _expr_mul_imp (last, rhs.obj), rhs.attr)

	elif last.is_pow: # {x^y.z} *imp* () -> x^{y.z()}
		if last.exp.is_attr and last.exp.args is None:
			if arg.is_paren:
				ast = AST ('^', last.base, wrap (AST ('.', last.exp.obj, last.exp.attr, _ast_func_tuple_args (arg))))
			elif rhs.is_attr:
				ast = AST ('^', last.base, ('.', _expr_mul_imp (last.exp, rhs.obj), rhs.attr))

	elif last.is_var: # user_func *imp* () -> user_func ()
		if last.var in user_funcs:
			if arg.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg)))
			else:
				ast = wrap (AST ('func', last.var, (arg,)))

	if arg.is_brack: # x * [y] -> x [y]
		if not arg.brack:
			raise SyntaxError ('missing index')

		ast = wrap (AST ('idx', last, arg.brack))

	if ast:
		return AST ('*', lhs.mul [:-1] + (ast,)) if lhs.is_mul else ast

	return AST.flatcat ('*', lhs, rhs)

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast.numer.is_diff_or_part_solo:
			p = 1
			v = ast.numer

		elif ast.numer.is_pow and ast.numer.base.is_diff_or_part_solo and ast.numer.exp.remove_curlys ().is_pos_int:
			p = int (ast.numer.exp.remove_curlys ().num)
			v = ast.numer.base

		else:
			return None

		ast_dv_check = (lambda n: n.is_differential) if v.is_diff_solo else (lambda n: n.is_partial)

		ns = ast.denom.mul if ast.denom.is_mul else (ast.denom,)
		ds = []
		cp = p

		for i in range (len (ns)):
			n = ns [i]

			if ast_dv_check (n):
				dec = 1
			elif n.is_pow and ast_dv_check (n.base) and n.exp.remove_curlys ().is_pos_int:
				dec = int (n.exp.remove_curlys ().num)
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
		end  = len (ast.mul)

		for i in range (end - 1, -1, -1):
			if ast.mul [i].is_div:
				diff = _interpret_divide (ast.mul [i])

				if diff:
					if diff.expr:
						if i < end - 1:
							tail [0 : 0] = ast.mul [i + 1 : end]

						tail.insert (0, diff)

					elif i < end - 1:
						tail.insert (0, AST ('diff', ast.mul [i + 1] if i == end - 2 else AST ('*', ast.mul [i + 1 : end]), diff.dvs))

					else:
						continue

					end = i

		if tail:
			tail = tail [0] if len (tail) == 1 else AST ('*', tuple (tail))

			return tail if end == 0 else AST.flatcat ('*', ast.mul [0], tail) if end == 1 else AST.flatcat ('*', AST ('*', ast.mul [:end]), tail)

	return ast

def _ast_strip_tail_differential (ast):
	if ast.is_differential or ast.is_null_var: # null_var is for autocomplete
		return None, ast

	if ast.is_intg:
		if ast.intg is not None:
			ast2, neg = ast.intg.strip_minus (retneg = True)
			ast2, dv  = _ast_strip_tail_differential (ast2)

			if dv:
				if ast2:
					return (AST ('intg', neg (ast2), dv, *ast [3:]), ast.dv)
				elif neg.has_neg:
					return (AST ('intg', neg (AST.One), dv, *ast [3:]), ast.dv)
				else:
					return (AST ('intg', None, dv, *ast [3:]), ast.dv)

	elif ast.is_diff:
		ast2, neg = ast.diff.strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			if ast2:
				return (AST ('diff', neg (ast2), ast.dvs), dv)
			elif len (ast.dvs) == 1:
				return (neg (AST ('/', ('@', ast.diff_type or 'd'), ast.dvs [0])), dv)
			else:
				return (neg (AST ('/', ('@', ast.diff_type or 'd'), ('*', ast.dvs))), dv)

	elif ast.is_div:
		ast2, neg = ast.denom.strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('/', ast.numer, neg (ast2)), dv

		ast2, neg = ast.numer.strip_minus (retneg = True)

		if dv:
			return AST ('/', neg (ast2) if ast2 else neg (AST.One), ast.denom), dv

	elif ast.is_mul:
		ast2, neg = ast.mul [-1].strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			if ast2:
				return (AST ('*', ast.mul [:-1] + (neg (ast2),)), dv)
			elif len (ast.mul) > 2:
				return (neg (AST ('*', ast.mul [:-1])), dv)
			else:
				return (neg (ast.mul [0]), dv)

	elif ast.is_add:
		ast2, neg = ast.add [-1].strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('+', ast.add [:-1] + (neg (ast2),)), dv

	return ast, None

def _expr_intg (ast, from_to = ()): # find differential for integration if present in ast and return integral ast
	ast, neg = ast.strip_minus (retneg = True)
	ast, dv  = _ast_strip_tail_differential (ast)

	if dv:
		if ast:
			return AST ('intg', neg (ast), dv, *from_to)
		elif neg.has_neg:
			return AST ('intg', neg (AST.One), dv, *from_to)
		else:
			return neg (AST ('intg', None, dv, *from_to))

	raise SyntaxError ('integration expecting a differential')

def _expr_func (iparm, *args, strip = 1): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	ast, wrap = _ast_func_reorder (args [iparm])

	return wrap (AST (*(args [:iparm] + ((_ast_func_tuple_args (ast) if args [0] == 'func' else ast.strip (strip)),) + args [iparm + 1:])))

def _expr_func_func (FUNC, expr_neg_func, expr_super = None):
	func = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC

	if expr_super is None:
		return _expr_func (2, 'func', func, expr_neg_func)
	elif expr_super.remove_curlys () != AST.NegOne or not AST ('func', func, ()).is_trigh_func_noninv:
		return AST ('^', _expr_func_func (FUNC, expr_neg_func), expr_super)
	else:
		return _expr_func_func (f'a{func}', expr_neg_func)

def _expr_mat (mat_rows):
	if not mat_rows:
		return AST.MatEmpty
	elif len (mat_rows [0]) > 1:
		return AST ('mat', mat_rows)
	else:
		return AST ('vec', tuple (c [0] for c in mat_rows))

def _expr_curly (ast): # convert curly expression to vector or matrix if appropriate
	if not ast.is_comma:
		return AST ('{', ast)
	elif not ast.comma: # empty {}?
		return AST.VarNull

	c = sum (bool (c.is_vec) for c in ast.comma)

	if c == len (ast.comma) and len (set (len (c.vec) for c in ast.comma)) == 1:
		if len (ast.comma [0].vec) > 1:
			return AST ('mat', tuple (c.vec for c in ast.comma))
		else:
			return AST ('vec', tuple (c.vec [0] for c in ast.comma))

	return AST ('vec', ast.comma) # raise SyntaxError ('invalid matrix syntax')

def _expr_num (NUM):
	num = NUM.grp [1] or (NUM.grp [0] if NUM.text [0] != '.' else f'0{NUM.grp [0]}')

	if not NUM.grp [2]:
		return AST ('#', num)

	g2  = NUM.grp [2].replace ('{', '').replace ('}', '')

	if g2 [1] in {'-', '+'}:
		return AST ('#', f'{num}{g2.lower ()}')
	else:
		return AST ('#', f'{num}{g2 [0].lower ()}+{g2 [1:]}')

def _expr_var (VAR, var_tex_xlat):
	if VAR.grp [0]:
		var = 'partial' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_'))
	elif VAR.grp [1]:
		var = 'd' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_'))
	elif VAR.grp [3] in var_tex_xlat:
		var = var_tex_xlat [VAR.grp [3]]
	else:
		var = AST.Var.ANY2PY.get (VAR.grp [3].replace (' ', ''), VAR.grp [3].replace ('\\_', '_'))

	return AST ('@', var + '_prime' * len (VAR.grp [4]))

#...............................................................................................
class Parser (lalr1.LALR1):
	def __init__ (self):
		self.TOKENS_LONG.update ([(v, self.TOKENS [v]) for v in self.TOKENS_QUICK])

		lalr1.LALR1.__init__ (self)

	def set_quick (self, yes = True):
		self.TOKENS.update (self.TOKENS_QUICK if yes else self.TOKENS_LONG)

		self.set_tokens (self.TOKENS)

	_USER_FUNCS = set () # set or dict of variable names to be translated into 'func' ASTs if variable followed by parentheses

	def set_user_funcs  (self, user_funcs):
		self._USER_FUNCS = user_funcs

	_PARSER_TABLES = \
			b'eJztXW1v3baS/jML1AZ0AIkiKSnf0jTtDTZJe5O02IURBGmaXhTbpt0kvbuL4v73nZlnKL5Ix5ZsH/v4+MD0EUVR5HA4z5Acvujk7It/e//hpy+qLx59+/Tb53R9+vjrV3T57uGLx8+fkufJN8+/ffH4zaPvXzz9T7r9+sXDR3pp9Gro+uXjb948evjy8Uv1' \
			b'P3v4Sn1fRu8P0fsdvJIq5/LsyfPv5V1K79854OWrF/z7/Zf0+/z7Z/T7w0MOefL81TdM5ZNn8lh+//6C03oq1H/LT7/+/jkT+aW88ejbZ88ehhK9CJm+CJmx58WTb/7GSTx89h39fvXl05dPH778G3kfP/9Ki8K+L6P3h+jVojz+O/88fflYgwM3OLVXIIQI' \
			b'4JjPHn738tW3nN0rKeTj/3j0NDxmnn715IcnX3Eyj7769pWwQksuWXz3VBj15Gv6kVSIR/zWu7cf339+8/vHNz/9+Ounz28/UtD7//3j45tPf/7xfrz58P4fb37+88O7+PBH8v729vObd7//qr6Pv/9P9H2SlD+9//Tp3ej7Y/SFZN7+GL2fP4+5/fz23efg' \
			b'/0NSRXBGwG/B++svo/eXD5//Efy//fnrm19++yPc/jOW7EN896df/hm8n99/TIJ//jn4f/z49t1/vf+ccCJ43/358df/S7Mjz3j7dnzj7U8/jW9w6SOx7/97LBplMpb4l/fv3o83VDsfYqJ/fPr8e7gb3x5T//3X3z/Em99+e5vdfPridXV2srFNZc1pBU/L' \
			b'ntbwT1u19lRv6U58lqNV9Gijj0IA7trwHr1gQxB7JdbGSUhTnZjKdNWmqVr2nI6hEhYDNh17GoMfR1Q0SDQENTYNYi+/WOPHulO9pbQkSscZN04zpsAQqmFjwKYZxEc09RUX3+ojoqkBI6RAdKsFx23wJ+ENLhshzci/6cNj5qukq+HIpNoYDcS9owRbIbAO' \
			b'AUSk+CglU0tKNX4sh2jiMYj5FEPZSz5KduOrdqg2/hT35OEYA34sgslHPGQfhXPOzAOUlAJ8ctPhwgH8HnO7FXaTfDBHhtMkfGPrSVB6a6cxbH5LCbf9JKh8yeW3fnKbv7ChSmDG1ipzXFhzqkHs5Wgk88xGzt3WY4QQHG83RgSeaDgxTUVyxdVoKFUrPOG4' \
			b'yuP5GAxIkvplEZsyxY2R6vT031XWBsRSkVHEVtHA9esqdhET9CwEjwHMAA7xMaRBSBdDDEL6EELCKj6LHzuMFIYgV6dB7GXyW/wQF09Po5fjUHk0nt4SCgRjAx5oXbJcG5FI5pfEEPi3Qe0gGoVJSLy1wlobwEYiIbqghwg4euYqrnXknwZrAN1Ltj1+SERO' \
			b'9Z6wJKTRk0bS1TsHMaGSUY3GuuUioFJtUrE+lIsCT6wZCyy3bUiV7ixUBPOhGX1GfWAze8Ajyhe0dfhJNHynyqv1+BHlrjrai5d9Ljw81Vu6Cw9OT6mdOau5KC2Y3xPDK6pUAglJKpWJoDdwgYlu31W+r3pX9b7qu6on/1ANdTVw68SCbKkCfOWIb5QGVZ1h' \
			b'hlHVkyx70kJ11TVVZ6qurTpbda7qfNVJiYjyvq56lgcqbkVgJeqamu5rSqOmRGriNxWCYlOulGJNb/dVN1Se6GoqbyrfVt5WnrLy1UCOoNWxiiXJJkl2AliSBsKlc5UjMqlgphqIcG5lie9SwXVF2GnM6+qk5hbi7KSV6wmxhy/En4Z4dkJMkqcG7YixuHTy' \
			b'9IyVm9x7vhy5+ZqVFrgp1xNbK6N8J/fcY2C2+h7RevDPI3bT4xJe6oWtR5mdcrnvlM3tkUNbOBQkDKI1AN1Do6JlhXEo5bRwKNNYmrIoKAFlYj0ysfZaUnNIzQEGTkEBzcP1AJUjCorKXVEdVsSve1rBTD1zq4EK6fTig+6QCgfV0mdS4nZJVcb7lOVXlAwq' \
			b'5HDE+awYnJ10UtGNBFEYtzA1kVcTx2qKXN9fxjRHxswzxhwZM8+Y9siYuaamQ6+/Qx+2xV2vA4UwfED703pcMEA4EcKlS2v0qq15bfU1tPWdXO5Wq3TSWy2LNr3a9ffoankp+WCrwcW6H2v6MBrmE6+dEI9q9eCIdzrKgTAMetE+u4UYWdS8Fa4NfTUwyogr' \
			b'RGy7j2Wlfikq1jV3h2KgzqF2nI0SeTfIB7CcyA/ojHTvJ8WQ7cFkIsJPBtSBHQdgqhC9KkoFR9McO7pbWmdiioFlyhxtTWAJcwFWuSNLdFTsmBVif6PrvSq7GBmp0Pey4sWUao6ac14uBAxsXj5yaJ5DTX1kzRY7sodC7e+vbuFZBqO2dANbOgvL/WOETBuY' \
			b'Kxv6z7L5Ljb8W/DXiYI61MHyGU9lUPkOr1j2AIvF80zoSWLcBhMP5FWn1nTuVgd0nfQ/DqPwZzyPdDCl4bkwqcoGBpyZSffXOjVf8UwT6/guvKLvNE0wZPZa32IWlpAwhK8x+O8apGBw0bajFYayYZSxche52PUoiRfWZMYNjyKXU7VDMJDK9TppGdxodzSw' \
			b'OxrYHQ3XxKB9FtuBLJgYY/cOTTc6eWjAi67ePWnP2fgKRknV7rElcOijCXA/CRyuW8TZxokVHGavy37St9oc1nstRGy3Ry/T7DmdoTfc7jmdampzfr/pHNAQW22j0A43TTAm80p0Uv98oXaBL9QktOgmtKcYrLToERwnh2fakAYspBBhmscFLGxbsLAHCweO' \
			b'81oWCbc63mtnug0NaqNc0cTLyyfB3E1v0U2X3hb/3ts1YTwkkX7Q/TXVdA5CAjFsRui2oTNvtBPPhob7jNszGbjcXzlpIBkGF1VILcTmLq5GOeOhZXs3h5YypmwP1/LHA2Gjw9UWw9UWw1UutA4gfHJju9AtmW664MGaNKY9jNGwV/To5Di0wg5i7ZCdU2XY' \
			b'hG6N1W6NDYYONOMWzbhF+2214bb3bBr1BLzXzh83FW1u5fGqKzrw707qCo9qLnteRL2FfFrIp1VzilVzit3njj6l61SyXWj1IdkOks2XftBIrdxSUR2K6u5pUyiq574WnmXawRbsVSo8pMJDKuhCRQQIPCJ2GrE7FPv4GZe3Q3k7QQzaG5h1iOwuM/dy2Xsw' \
			b'qcdLvcbrD4ojwwGVxh1OaVjQBl1rXOti41par7o6o86MbA1jEwBvDxtUMTFdkirlzMaecSZA8kxZAiWIAjHVTngwZIV2gWdEOLWFVFBeUdsxSEBtB7uQ2InonglgCrhsPBnBW9hYbXL/jjt3vMmW9922rEopjNnAqpEX0/NKet5FKvvr6Tlv3ONtd7yKWs5V' \
			b'oHd5gSyvPOWNc7xrjleg8/JzXp3NK7OZVTzbxaYTtpvw3jC2KrPlltnKuyl5ZyAVwRD9hrhtRHBw7gYfByF72SvZ+z2EMweqDTUUG6rdDb28sXySgas2TjZ5V3JGBNXqhnQ/n9Gx6TkZbODfcN1uuHI3zK8NV6+cZdDztvqaX+QzITgDzo8ScLxZnTeE8yuc' \
			b'IJ8hIccbUBgnrgSRQG98oynKVv+anvS8N55C+agCqsQNCS2fVyBb92VTvJz8QG9Syj1vKOdN7Lzpnd/j7fRMI+fGB4Iwdbzln+KTAG86DuOcOQ1mAbOD/+k58XjDhwvwuSGyP9/j8IqeS0D/nmljdsiWffIzazmcaWEaKD7V3ca719yBYfHORLuJLW8h4MSX' \
			b'q8p4H8Q8aIQ5YTcLBf66BN1dUtibhQLvuMSulHHHQefI+Q4l3SV/WyXdLZT1a5JxFtvLiDkntUzUDYs6NR+JiKNtQePQBClPpmwxm7tC6G0i91sat4iBvG0kkdC2K+njUq1jaMQIsREk0m2KzZjsFlLD4ziBkE4qCH6sYsgXOPIJhtocO7yTik8dmGCI0uKd' \
			b'1RMsUTzeysJ7RBZjqo644u1OE2zRMz60YMSXUYyRXiIgGOJDjjcuOARafYQyljQiVi5OAhVm0gPI3BrYMeJS1LE/AV5voytBWORaOCHUZgn0EajsVaxyxAElsoNG6wxwK2+0yLzBRUmRcqcwFjYpghm9CXIDV3L8htCI4kjlYBdjuQGVXonNAa15KKQlXpZN' \
			b'hHf1l60fsA4c+gdSMSSND1itkGTRtfsXzxuN+K8TFdDtE/hnkW8Xgf8IfAI+F1oAwlnghltYbV35VlGPh6lbg3pJN0E93yeoz5ItUT/JOItt7SSol96SaLOm6IsOKJMdQlxZ3tEI6CVvJQEUO8ROQd9sB70ypQC9hkbQRzrXgB5veCW2AL1yAqCXeFk2M6Cf' \
			b'AbudNvb7j/QjzJfBnEe5QAR8KcZNxLgp3SqMmwLjJsd4mmyJ8UnGWWxrJ0HarE8GmwMKZIcQUQBuAHADgBsA3ADgJge42Q5wza4AuIYmAB+JXANwvOGV2ALgygYFuAHAYzbLAO4OFODHTryC3FdyCCIsgD4HuY8g96VbBXJfgNznIE+TLUE+yTiLbe0kKIDc' \
			b'jyBn74Di2CGJKSj3QLkHyj1Q7oFyn6Pcb0e5sqRAuYYmKB/zXoNyvOGV2ALlygdFuQfKYzbr+u7+iPbDRntfidyYSn0p2vuI9r50q9BemMj4PkV7mmyJ9knGWWxrJ0EB7X1Eew+090D7GFPQ3gPtPdDeA+090N7naO+3o11ZUqBdQxO0j3mvQTve8EpsgXbl' \
			b'g6K9B9pjNuvQ3h3RfthoH7g2BR7wpWiPFnA8TN0qtA8F2nObeJZsifZJxllsaydBAe1DRPsAtA9A+xhT0D4A7QPQPgDtA9A+5GgftqNdWVKgXUMTtI95r0G7MkyJLdCufFC0w9qeZLMO7f3RLn8/YM9VCfOc+gj2BpNfcnFyUfAjSurWgN8UFjqTW+iyZAvw' \
			b'TzMu6bB2EqT4N9FCx94BJbJDEpPxb2CiMzDRGZjoDEx0JjfRme0musCVHP8hNOI/Rl2Bf33DK7E5/gMfgH8DE12SzTr8D0f83xP8e64+wQl8jH8P/KPxN3FgjyipW4X/YmBv8oF9lmyJ/0nGTUmItRPaggKIg3uDwb3B4D7GFAWAwb3B4N5gcG8wuDf54N5s' \
			b'H9wHthQKQEMTBTDmvUYB4A2vxBYKQPmgCgCD+ySbdQqgqY8a4J5ogA4fSJLvJLGPNUAHDdBBA3RRA3SlW6UBukIDdLkGSJMtNcBFThRAERQUQBcVQAcF0EEBjDFFAXRQAB0UQAcF0EEBdLkC6LYrAOVKoQA0NFEAY95rFADe8EpsoQCUD6oAOiiAmM1KBdAc' \
			b'FcA9UQC9fCaswWlosPMZDP7l4uQSFEBfulUKoLD2mdzalyVbKoBJxiUd1k6CggKIBj8Dg5+BwS/GFAUAg5+Bwc/A4Gdg8DO5wc9sN/gFrhQKQEMTBTDmvUYB4A2vxBYKQPmgCgAGvySblQrguDbvviiAgWtNgAJfL9UoCmCAAogGQERJ3SoFUBgATW4AzJIt' \
			b'FcAk45IOaydBQQFEG6CBDdDABhhjigKADdDABmhgAzSwAZrcBmi22wADVwoFoKGJAhjzXqMAlGdKbKEAlA+qAGADTLJZqQDaVAGYw9AB0+0mR12QTQNwIWA3b5m9fNPjwvS2mA9o43xAW7pV8wFtMR/Q5vMBabLlfMAk45IOaydBYUqgjVMCLaYE+OR8B4Ls' \
			b'kLwhEtNiagAL7uWCmA6sSKcG2u1TA8qdYmpAQ5OpgTHvNVMDeMMrscXUgPJDpwZaTA3EbFaqha3L+Oq9UQi3uZKv2OmyWgvchAbgmSGe3XIX9Qws16S0oPAlk4J8cKSN3QJbuivtlDH5mn3USvyf9A0muWeU2GlQ0ASMJ94c6atxdZ/BjrIxLzQauhig1tUA' \
			b'tS4HqHU9QF2MD2ymByT5pIegDCp6CBqa78Ex69buy5eLO84QJBcdBOWHdhBYBLjrU22w4C+yJ9MJQ/dAVGXn6VqLDnCz6/b3s2tgrrSG/9gxUFXguB5lHb/4DHbKyb5MjwsCg0KYuFXjBFfoA1foA5OkWyqDucxT57HDriSPF/WjhEKsDhccdAJ23sXIMlxw' \
			b'GC44DBcchgsOw4V8R55E3TJcUOYUykBDk+HCmPcadYA3vBJbaAMtl2oDBx0Qs1nZL5hZD7ifCuFoL7iaKuB6gcFQfT0uRGwLg2EbDYaIkro1eqDsF7S5wTBLtlAD04xLOqydBGm3oI0GwxYGwxYGwxiTFUCLTkGLPkGLLkGLHkGbdwja7QbDwJVcAYTQqABi' \
			b'3isUgL7hldhcAQQ+QAG0MBgm2axUADNLBHekAPzF51Uc1cDO1YAcJCRwga+X6hI1ALNhG82GiJK6VWqgMBsOUAOyD56/PchvsDqQhAeQUaqDCQElPdZOgoI6iObDFubDFubDGFPUAcyHLcyHLcyHLcyHbW4+bLebDwN3CnWgoYk6GPNeow7whldiC3WgfFB1' \
			b'APNhks1KdXBcQ3hPFAFXB9YQqo/PAcIaQos1hDauIUSU1K1RBLZYQ2jzNYRZsoUCmGZc0mHtJEgVgI1rCC3WEFqsIYwx5UuVWENosYbQYg2hxRpCm68htNvXEAau5AoghEYFEPNeoQD0Da/E5gog8AEKwGINYZLNSgVwXER4wwpAbdi3pwhMJWCTC/tYERgo' \
			b'AgNFYKIiMKVbpQhMoQhMrgjSZEtFMMm4pMPaSVBQBCYqAgNFYKAIxpiiCAwUgYEiMFAEBorA5IrAbFcEml+hCDQ0UQRj3oMdi7BQHSC2V5ILdaBJqTqAjTDJbJ06MDMrCne0g+haJwqWn321C1hfAspXh7Fldoq4w5dY/W00+eNh6lYB2BYAzi3+E9BOMssy' \
			b'ngkKiLVVtn/fwrq/uegMLWu341ILW+BSQxNcRvIWohGxZ47RCukoFC2gOKa/cH++mVnTd4TgXkLQs5FD5Be+FIJxQT4epm4VBIsF+dafD8FJZlnG1k6CAgR9AUG/EILbl9mHwhYQ1NAEgpG8hRBE7DkIajoKQayvj+kvheDMqrojBPcSgj1bGEV+4UshGO3b' \
			b'eJi6VRAs7Nu2Px+Ck8yyjK2dBAUI9gUE+4UQ3G62DoUtIKihCQQjeQshiNhzENR0FIKwV8f0l0KwPdCt7Ps0FL2tISizHCKvvgS1Lp4wiYepW4NaSTdBLd8nqM2SLY95nWScxbZ2EtSPxZmcQ+VwwGQoc60vtMi4wQXkOsROoO22ny4ZOJJDO4RGaEciV1ig' \
			b'9A2vxOYID2wAwiVels1ChB9PmjtghDfMcoEEfCnCo50ZD1O3CuGFndnlduYs2RLhk4yz2NZOggLCmxmEw8wcylzXeKFFxpo/yHWInSJ8u405cKRAuIYmCB+jrkE43vBKbIFwZYMiHDbmJJuFCD/Uo+aOCCeEG+a3QAK+FOHRgOxM6VYhvDAgu9yAnCVbInyS' \
			b'cRbb2klQQLiZQTjsx6HMjHAYjx2Mxw7GYwfjscuNx2678ThwpEC4hiYIH4lcg3C84ZXYAuHKBkU4zMZJNgsRfqjHyx0RTghvmdkCCfhShMfNJXiYulUILzaXuHxzSZZsifBJxllsaydBAeHtDMKxpySUmRGODSUO426HDSUOG0pcvqHEbd9QEjhSIFxDE4SP' \
			b'RK5BON7wSmyBcGWDIhwbSpJsFiK8m/2MT7qg3N3q1pLJp5Ju50T4euY7QqlCMNe08WStYugXKgd7GQXRX/Q5Io8v06ldrvhei4v2OURK3ZU2prjcQJelO/l2kcm+XzSlxMFmVwbxQnQY/10/o05gutO4ok6wDNVhGarDMlSHZaguX4bKNVd+CcklNr4tH4oJ' \
			b'jCtUjYZGVcMI19CFuoZFRPRNP35Cxk0XqvJXZAK/VOnA+BeZlikd94CCSPPIM/kd+NdLCKsivnQc61/4NvzZTXxNbL8+JeZWtP/bbOq2OucLS8P+fU1sP78kJqe2LGuWL/uZpWFGwpudCHlsO7u9EfUlYu5mRH2JmF/01bzW3JKsJy1Po6cj7JHML2oa6qnM' \
			b'L5N3KvtU3qddyuuV9+Fa5b2+AZm/QN6Jxw3Vb5D7hsvDXyG/e/LfNjuQf+bfbX9BEj1pP+Ig9KZLPDQLezjX8DnJySdTiVWXWEZwW92dbgEu+ku2BefhoF1nvryWr6g2tsRCa26nPeCR47I2wSzARDPbLlR/kRQ8oLqRD8+Zm+nzx+bhvK+rXgYQ3KzTc6qI' \
			b'2/ms8NJxwN5/VliG6fp/rY0EOpWdmEpu43PDrKiWdJgIGH3zgHIVYLTV2S4BweJfh5ZhqIgdK3Fwk4MClnnyd/YyA4N9kHM5A2lIFL4k2l1GuG+w5y8nGoFUf6nuv925DPOZMUMQ436nkjxrxL2sNFMYVcYhSDW/kAi2vDvsXLqni44vram5YExZf3k5dxfI' \
			b'OTW316CuIeTdleV8waTF7GTFZWTd36D2bppd9t2z/jqngI/KXl3Um/RLlEu1edNcTuK5vyhSfyV59xfJe3d98j4Ke3NTPZTLyvrByXkh4025gWS3HZbLivjVxbu7SLz7HYi3OYr3bYv3jfbHb0+8+4vEe9VSjoXi3R7F+7bFu1zEcKDiPezecHIZu+FN20vC' \
			b'UqB+rZ1w4OVWtz6wvIL574YtJEFGeWXVmvUA1V/dA9IabOyjSj/K7B22glyfsPIyvtuaxNxik27NA4KQiGmze3tel5n0dmTJ27Yk86rWvLsqv8yVjU0NeTtUu+0OrHfruwlU+uuX5S1LmTP169N1yTephNdsNLhgglFWpDSy4mE/hBqruvP/85S0PE9X895s' \
			b'z2LFBoCLVhryBwTkcxJSolJ5O/uA8C66exfziUd5vzV595P/8+XdH4y8O5V3f7682+qsr+JuNSMCbkS0U7kWoeaBf7axq5uXK1/sqxgaqn8mItk3JXXN9cx1zPU7V7djvZbHW8lnsGe4yJxJOeIHacTcikJGbDrpUQnYlhTaTgvO4JDCi4BdtvRMwiitYrHg' \
			b'pyx4S1gSBKYUFGWNX8MaN+XOnnCozzE9cilA9Bo41a3h1DkqH8p+haZfwNo1WnyivUO321+5GqQo+f9E3fLEYN2tVbFL6m+N+izrOHxtqu5y9diXlX57VoZUDG5ytdzWUdmcqGxpvQd76xaELdtSd2IxmJGsaSPc8tZSJ1I2HKVsjZSxUO2pnSqRMt5s29yy' \
			b'jJn2AT57SLIm38/zdLUsc5TFUebWyNxNTUddTeZA6L7KXJPL3C2b7fdd7Fjc9twsv2eNKsuY2VsZu+ltDkHO2ir/fOa5Mnd+P24nMte5S4qcvLgbqeOkto0ROAlmx4zum357ktJWedyX2cp9EMltYijTendnVjJVfzcxE7lQBVr5tkXTdcJZHpj3eODktHxn' \
			b'KJyyHYbXp+Q72cg56zjGBgd/jLu/iLX8lW3eHU958S5SOd8lbubqPSe8MRekQPKe/8lberJt+p5uQMvfbnlHWqt/YWuZ3ktCNkuoKU/cienmp+PI9k5e5z3OdOphMzgAhk9VrvBHImJlfVZwCGYLvPp4BzTxlx6x0FNF81ZkXiWFbclCprscmXxkzYWUUswL' \
			b'/3iSoAgTuvxSuubOF9pKGj8bySN1teWPZzK2PiMc01WI7EoiJwcrWfnwQGZ6O/9MtPxYJG4jZb+v1bkxVpgs1XziEYXxeTRz5UxPIxpPFxqq8RShwaQnB73m5mD8c1V+U7i5v7lY07D5hNNHMaqwt9+9DJDGudyfEDjcQP2PW76DCPgdigEntmvHduF40189' \
			b'SamKpt69sHC35fodyG9S8rk++2sSqObWZaqrRodPhaUhl3ftdSV0nkPlmPNlSw8gOxfVWyUs8HGUMu6Lb3fSTT3PcQd6JpSqP9ygTO3BChyPZO6qQ91c0HdcIm+ogBVS11ZXdGHUdm4slM8drOzx+PmuOtTNpOM9rZXF4oc6WCiEc9xsqtTxl4GbS7pgR7gg' \
			b'VmEFEI50hyutprqzDnUzGSLcprS21S058GI4XDm11Z11sEVNRie3KaeuuiUHXhzuUIdt5XfVoW7MXayb8NXmZXXUVXvumo7/+3OioK7aa9cpw3nj1HqBamGxuFbH9TwTSkRveQOsmQygtgnwdXFnTlVs51Jbne/4o9gXxVni0nTm0gSzJlMA+8UsV+2HA7MW' \
			b'DI9uk1ldtR8OzDqc+RFWQwuczHIn/wtfOy+J5cnNxkBFLBgm3ZGK4NUGd8aB+TcxS3RDzHfV3XGYzl8w8LorzPfV3XFgfnM4zO+qu+PAfD6emXcxdXrfhvse95bvmTUcxgukGoRTdzCtIeIfrw/o5BQ3w6cBNV6r18/G7KvEIWI3ichVwZGHKnVNhy4pn3M0' \
			b'LgryXJ0IHvB14iAq51Z7N/DcI68+S1edjavFZlaK9WAUn+hR7JWSzaMyA8w5Sk6aC08SOhYSDDz4mIWml5wHKsrr0/8Hz4HKow=='

	_PARSER_TOP             = 'expr_commas'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	_VAR_TEX_XLAT = {
		r'\mathbb{R}'  : 'Reals',
		r'\mathbb{C}'  : 'Complexes',
		r'\mathbb{N}'  : 'Naturals',
		r'\mathbb{N}_0': 'Naturals0',
		r'\mathbb{Z}'  : 'Integers',
	}

	_UPARTIAL = '\u2202'
	_USUM     = '\u2211'
	_UINTG    = '\u222b'
	_LETTER   = fr'[a-zA-Z]'
	_LETTERU  = fr'[a-zA-Z_]'

	_TEXGREEK = '(?:' + '|'.join (reversed (sorted (f'\\\\{g}' for g in AST.Var.GREEK))) + ')'
	_TEXXLAT  = '(?:' + '|'.join (reversed (sorted (x.replace ('\\', '\\\\') for x in _VAR_TEX_XLAT))) + ')'
	_VARPY    = fr'(?:{_LETTER}(?:\w|\\_)*)'
	_VARTEX   = fr'(?:{_TEXGREEK}|{_TEXXLAT}|\\partial|(?:(?:\\overline|\\bar|\\widetilde|\\tilde)\s*)?\\infty)'
	_VARTEX1  = fr'(?:(\d)|({_LETTER})|({_VARTEX}))'
	_VARUNI   = fr'(?:{"|".join (AST.Var.UNI2PY)})'
	_VAR      = fr'(?:{_VARPY}|{_VARTEX}(?!{_LETTERU})|{_VARUNI})'

	_STR      = r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY - AST.Func.PSEUDO)))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LETTERU})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\$?{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LETTER})'),
		('LOG',           r'log\b|\\log(?!{_LETTER})'),
		('LN',            r'ln\b|\\ln(?!{_LETTER})'),
		('LIM',          fr'\\lim(?!{_LETTER})'),
		('SUM',          fr'\\sum(?:\s*\\limits)?(?!{_LETTER})|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?(?!{_LETTER})|{_UINTG}'),
		('LEFT',         fr'\\left(?!{_LETTERU})'),
		('RIGHT',        fr'\\right(?!{_LETTERU})'),
		('CDOT',         fr'\\cdot(?!{_LETTERU})'),
		('TO',           fr'\\to(?!{_LETTERU})'),
		('MAPSTO',       fr'\\mapsto(?!{_LETTERU})'),
		('BEG_MAT',       r'\\begin\s*{\s*matrix\s*}'),
		('END_MAT',       r'\\end\s*{\s*matrix\s*}'),
		('BEG_BMAT',      r'\\begin\s*{\s*bmatrix\s*}'),
		('END_BMAT',      r'\\end\s*{\s*bmatrix\s*}'),
		('BEG_VMAT',      r'\\begin\s*{\s*vmatrix\s*}'),
		('END_VMAT',      r'\\end\s*{\s*vmatrix\s*}'),
		('BEG_PMAT',      r'\\begin\s*{\s*pmatrix\s*}'),
		('END_PMAT',      r'\\end\s*{\s*pmatrix\s*}'),
		('BEG_CASES',     r'\\begin\s*{\s*cases\s*}'),
		('END_CASES',     r'\\end\s*{\s*cases\s*}'),
		('FRAC2',        fr'\\frac\s*{_VARTEX1}\s*{_VARTEX1}'),
		('FRAC1',        fr'\\frac\s*{_VARTEX1}'),
		('FRAC',          r'\\frac'),
		('IF',            r'if(?!{_LETTERU})'),
		('ELSE',          r'else(?!{_LETTERU})'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))('*)"),
		('ATTR',         fr'\.(?:({_LETTERU}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"({_STR})|\\text\s*{{\s*({_STR})\s*}}"),
		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
		('COLON',         r'{:}|:'),
		('CARET1',       fr'\^{_VARTEX1}'),
		('CARET',         r'\^'),
		('DBLSTAR',       r'\*\*'),
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('CURLYL',        r'{'),
		('CURLYR',        r'}'),
		('BRACKL',        r'\['),
		('BRACKR',        r'\]'),
		('BAR',           r'\|'),
		('PLUS',          r'\+'),
		('MINUS',         r'-'),
		('STAR',          r'\*'),
		('INEQ',         fr'==|!=|\\neq?|<=|\\le|<|\\lt|>=|\\ge|>|\\gt|{"|".join (AST.Eq.UNI2PY)}'),
		('EQ',            r'='),
		('DIVIDE',        r'/'),
		('EXCL',          r'!'),
		('AMP',           r'&'),
		('DBLSLASH',      r'\\\\'),
		('COMMA',         r','),
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('ignore',        r'\\,|\\:|\\?\s+|\\text\s*{\s*[^}]*\s*}'),
	])

	_VARPY_QUICK = fr'(?:{_LETTER})'
	_VAR_QUICK   = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK = OrderedDict ([ # quick input mode different tokens
		('FUNC',         fr'(@|\%|{_FUNCPY})|\\({_FUNCTEX})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
		('SQRT',          r'sqrt|\\sqrt'),
		('LOG',           r'log|\\log'),
		('LN',            r'ln|\\ln'),
		('LIM',          fr'\\lim'),
		('SUM',          fr'\\sum(?:\s*\\limits)?|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?|{_UINTG}'),
		('LEFT',         fr'\\left'),
		('RIGHT',        fr'\\right'),
		('CDOT',         fr'\\cdot'),
		('TO',           fr'\\to'),
		('MAPSTO',       fr'\\mapsto'),
		('IF',            r'if'),
		('ELSE',          r'else'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR_QUICK})|({_VAR_QUICK}))('*)"),
	])

	TOKENS_LONG  = OrderedDict () # initialized in __init__()

	def expr_commas_1      (self, expr_comma, COMMA):                              return expr_comma if expr_comma.is_comma else AST (',', (expr_comma,))
	def expr_commas_2      (self, expr_comma):                                     return expr_comma
	def expr_commas_3      (self):                                                 return AST.CommaEmpty
	def expr_comma_1       (self, expr_comma, COMMA, expr_colon):                  return _expr_comma (expr_comma, expr_colon)
	def expr_comma_2       (self, expr_colon):                                     return expr_colon

	def expr_colon_1       (self, expr, COLON, expr_colon):                        return _expr_colon (expr, expr_colon)
	def expr_colon_2       (self, expr, COLON):                                    return AST ('slice', expr, False, None)
	def expr_colon_3       (self, COLON, expr_colon):                              return _ast_pre_slice (False, expr_colon)
	def expr_colon_4       (self, COLON):                                          return AST ('slice', False, False, None)
	def expr_colon_5       (self, expr):                                           return expr

	def expr               (self, expr_eq):                                        return expr_eq

	def expr_eq_1          (self, expr_mapsto1, EQ, expr_mapsto2):                 return AST ('=', '=', expr_mapsto1, expr_mapsto2)
	def expr_eq_2          (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr):                       return _expr_mapsto (expr_paren.strip (), expr)
	def expr_mapsto_2      (self, expr_piece):                                     return expr_piece

	def expr_piece_1       (self, expr_ineq, IF, expr_eq, ELSE, expr_mapsto):      return _expr_piece (expr_ineq, expr_eq, expr_mapsto)
	def expr_piece_2       (self, expr_ineq, IF, expr_eq):                         return AST ('piece', ((expr_ineq, expr_eq),))
	def expr_piece_3       (self, expr_ineq):                                      return expr_ineq

	def expr_ineq_2        (self, expr_add1, INEQ, expr_add2):                     return AST ('=', AST.Eq.ANY2PY.get (INEQ.text, INEQ.text), expr_add1, expr_add2)
	def expr_ineq_3        (self, expr_add):                                       return expr_add

	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                  return AST.flatcat ('+', expr_add, expr_mul_exp.neg (stack = True))
	def expr_add_3         (self, expr_mul_exp):                                   return expr_mul_exp

	def expr_mul_exp_1     (self, expr_mul_exp, CDOT, expr_neg):                   return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_2     (self, expr_mul_exp, STAR, expr_neg):                   return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_3     (self, expr_neg):                                       return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                return expr_neg.neg (stack = True)
	def expr_neg_2         (self, expr_diff):                                      return expr_diff

	def expr_diff          (self, expr_div):                                       return _expr_diff (expr_div)

	def expr_div_1         (self, expr_div, DIVIDE, expr_mul_imp):                 return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2         (self, expr_div, DIVIDE, MINUS, expr_mul_imp):          return AST ('/', expr_div, expr_mul_imp.neg (stack = True))
	def expr_div_3         (self, expr_mul_imp):                                   return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                        return _expr_mul_imp (expr_mul_imp, expr_intg, self._USER_FUNCS)
	def expr_mul_imp_2     (self, expr_intg):                                      return expr_intg

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add):           return _expr_intg (expr_add, (expr_sub, expr_super))
	def expr_intg_2        (self, INTG, expr_add):                                 return _expr_intg (expr_add)
	def expr_intg_3        (self, expr_lim):                                       return expr_lim

	def expr_lim_1         (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                           return AST ('lim', expr_neg, expr_var, expr)
	def expr_lim_2         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):   return AST ('lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg):  return AST ('lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                         return expr_sum

	def expr_sum_1         (self, SUM, SUB, CURLYL, expr_var, EQ, expr, CURLYR, expr_super, expr_neg):               return AST ('sum', expr_neg, expr_var, expr, expr_super)
	def expr_sum_2         (self, expr_func):                                                                        return expr_func

	def expr_func_1        (self, SQRT, BRACKL, expr, BRACKR, expr_neg_func):      return _expr_func (1, 'sqrt', expr_neg_func, expr)
	def expr_func_2        (self, SQRT, expr_super, expr_neg_func):                return AST ('^', _expr_func (1, 'sqrt', expr_neg_func), expr_super)
	def expr_func_3        (self, SQRT, expr_neg_func):                            return _expr_func (1, 'sqrt', expr_neg_func)
	def expr_func_4        (self, LN, expr_super, expr_neg_func):                  return AST ('^', _expr_func (1, 'log', expr_neg_func), expr_super)
	def expr_func_5        (self, LN, expr_neg_func):                              return _expr_func (1, 'log', expr_neg_func)
	def expr_func_6        (self, LOG, expr_sub, expr_neg_func):                   return _expr_func (1, 'log', expr_neg_func, expr_sub)
	def expr_func_7        (self, LOG, expr_super, expr_neg_func):                 return AST ('^', _expr_func (1, 'log', expr_neg_func), expr_super)
	def expr_func_8        (self, LOG, expr_neg_func):                             return _expr_func (1, 'log', expr_neg_func)
	def expr_func_9        (self, FUNC, expr_neg_func):                            return _expr_func_func (FUNC, expr_neg_func)
	def expr_func_10       (self, FUNC, expr_super, expr_neg_func):                return _expr_func_func (FUNC, expr_neg_func, expr_super)
	def expr_func_11       (self, expr_pow):                                       return expr_pow

	def expr_pow_1         (self, expr_pow, expr_super):                           return AST ('^', expr_pow, expr_super)
	def expr_pow_2         (self, expr_fact):                                      return expr_fact

	def expr_fact_1        (self, expr_fact, EXCL):                                return AST ('!', expr_fact)
	def expr_fact_2        (self, expr_attr):                                      return expr_attr

	def expr_attr_1        (self, expr_attr, ATTR):                                return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1])
	def expr_attr_2        (self, expr_abs):                                       return expr_abs

	def expr_abs_1         (self, LEFT, BAR1, expr_commas, RIGHT, BAR2):           return AST ('|', expr_commas)
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                        return AST ('|', expr_commas)
	def expr_abs_3         (self, expr_paren):                                     return expr_paren

	def expr_paren_1       (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):       return AST ('(', expr_commas)
	def expr_paren_2       (self, PARENL, expr_commas, PARENR):                    return AST ('(', expr_commas)
	def expr_paren_3       (self, IGNORE_CURLY, CURLYL, expr, CURLYR):             return AST ('{', expr)
	def expr_paren_4       (self, expr_frac):                                      return expr_frac

	def expr_frac_1        (self, FRAC, expr_cases1, expr_cases2):                 return AST ('/', expr_cases1.remove_curlys (), expr_cases2.remove_curlys ())
	def expr_frac_2        (self, FRAC1, expr_cases):                              return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_cases.remove_curlys ())
	def expr_frac_3        (self, FRAC2):                                          return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4        (self, expr_cases):                                     return expr_cases

	def expr_cases_1       (self, BEG_CASES, casess, END_CASES):                   return AST ('piece', casess)
	def expr_cases_2       (self, expr_mat):                                       return expr_mat
	def casess_1           (self, casessp, DBLSLASH):                              return casessp
	def casess_2           (self, casessp):                                        return casessp
	def casessp_1          (self, casessp, DBLSLASH, casessc):                     return casessp + (casessc,)
	def casessp_2          (self, casessc):                                        return (casessc,)
	def casessc_1          (self, expr1, AMP, expr2):                              return (expr1, expr2)
	def casessc_2          (self, expr, AMP):                                      return (expr, True)

	def expr_mat_1         (self, LEFT, BRACKL, BEG_MAT, mat_rows, END_MAT, RIGHT, BRACKR):  return _expr_mat (mat_rows)
	def expr_mat_2         (self, BEG_MAT, mat_rows, END_MAT):                               return _expr_mat (mat_rows)
	def expr_mat_3         (self, BEG_BMAT, mat_rows, END_BMAT):                             return _expr_mat (mat_rows)
	def expr_mat_4         (self, BEG_VMAT, mat_rows, END_VMAT):                             return _expr_mat (mat_rows)
	def expr_mat_5         (self, BEG_PMAT, mat_rows, END_PMAT):                             return _expr_mat (mat_rows)
	def expr_mat_6         (self, expr_curly):                                               return expr_curly
	def mat_rows_1         (self, mat_row, DBLSLASH):                              return mat_row
	def mat_rows_2         (self, mat_row):                                        return mat_row
	def mat_rows_3         (self):                                                 return ()
	def mat_row_1          (self, mat_row, DBLSLASH, mat_col):                     return mat_row + (mat_col,)
	def mat_row_2          (self, mat_col):                                        return (mat_col,)
	def mat_col_1          (self, mat_col, AMP, expr):                             return mat_col + (expr,)
	def mat_col_2          (self, expr):                                           return (expr,)

	def expr_curly_1       (self, CURLYL, expr_commas, CURLYR):                    return _expr_curly (expr_commas)
	def expr_curly_2       (self, expr_bracket):                                   return expr_bracket

	def expr_bracket_1     (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):       return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_2     (self, BRACKL, expr_commas, BRACKR):                    return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_3     (self, expr_term):                                      return expr_term

	def expr_term_1        (self, expr_num):                                       return expr_num
	def expr_term_2        (self, expr_var):                                       return expr_var
	def expr_term_3        (self, STR):                                            return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_4        (self, SUB):                                            return AST ('@', '_') # for last expression variable

	def expr_num           (self, NUM):                                            return _expr_num (NUM)
	def expr_var           (self, VAR):                                            return _expr_var (VAR, self._VAR_TEX_XLAT)

	def expr_sub_1         (self, SUB, expr_frac):                                 return expr_frac
	def expr_sub_2         (self, SUB1):                                           return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1       (self, DBLSTAR, expr_neg_func):                         return expr_neg_func
	def expr_super_3       (self, CARET, expr_frac):                               return expr_frac
	def expr_super_4       (self, CARET1):                                         return _ast_from_tok_digit_or_var (CARET1)

	def expr_neg_func_1    (self, MINUS, expr_neg_func):                           return expr_neg_func.neg (stack = True)
	def expr_neg_func_2    (self, expr_func):                                      return expr_func

	def caret_or_dblstar_1 (self, DBLSTAR):                                        return '**'
	def caret_or_dblstar_2 (self, CARET):                                          return '^'

	#...............................................................................................
	_AUTOCOMPLETE_SUBSTITUTE = { # autocomplete means autocomplete AST tree so it can be rendered, not necessarily expression
		'CARET1'          : 'CARET',
		'SUB1'            : 'SUB',
		'FRAC2'           : 'FRAC',
		'FRAC1'           : 'FRAC',
		'expr_super'      : 'CARET',
		'caret_or_dblstar': 'CARET',
	}

	_AUTOCOMPLETE_CONTINUE = {
		'RIGHT' : ' \\right',
		'COMMA' : ',',
		'PARENL': '(',
		'PARENR': ')',
		'CURLYR': '}',
		'BRACKR': ']',
		'BAR'   : '|',
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
				self.tokens.insert (tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, ('', '', '', '', '')))
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

			return self._insert_symbol ('PARENR' if self.stack [idx].sym == 'PARENL' else 'BRACKR')

		# vector or matrix potentially being entered
		if self.stack [idx - 1].sym == 'CURLYL':
			if self.stack [-1].red.is_null_var:
				return self._mark_error (('CURLYR', 'CURLYR'))
			elif not self.stack [-1].red.is_comma:
				return self._insert_symbol (('COMMA', 'CURLYR', 'COMMA', 'CURLYR'), 1)
			elif len (self.stack [-1].red.comma) == 1 or self.tokens [self.tokidx - 1] != 'COMMA':
				return self._insert_symbol (('CURLYR', 'COMMA', 'CURLYR'))
			else:
				return self._mark_error (('CURLYR', 'CURLYR'))

		if self.stack [-3].sym != 'COMMA' or self.stack [-4].sym != 'expr_comma' or self.stack [-5].sym != 'CURLYL':
			if self.stack [-1].red.is_vec:
				return self._insert_symbol (('COMMA', 'CURLYR'), 1)
			elif self.stack [-1].red.is_comma:
				if len (self.stack [-1].red.comma) == 1 or self.tokens [self.tokidx - 1] != 'COMMA':
					return self._insert_symbol ('CURLYR')
				else:
					return self._mark_error ('CURLYR')

		else:
			cols = \
					len (self.stack [-4].red.vec)             if self.stack [-4].red.is_vec else \
					len (self.stack [-4].red.comma [0].vec)  if self.stack [-4].red.is_comma and self.stack [-4].red.comma [0].is_vec else \
					None

			if cols is not None:
				vec             = self.stack [-1].red.comma if self.stack [-1].red.is_comma else (self.stack [-1].red,)
				self.stack [-1] = lalr1.State (self.stack [-1].idx, self.stack [-1].sym, AST (',', vec + (AST.VarNull,) * (cols - len (vec))))

				return self._mark_error (('CURLYR', 'CURLYR')) if len (vec) != cols else self._insert_symbol (('CURLYR', 'CURLYR'))

		return self._insert_symbol ('CURLYR')

	def _parse_autocomplete_expr_intg (self):
		s               = self.stack [-1]
		self.stack [-1] = lalr1.State (s.idx, s.sym, AST ('*', (s.red, AST.VarNull)))
		expr_vars       = set ()

		if self.autocompleting:
			stack = [s [2]]

			while stack:
				ast = stack.pop ()

				if ast.is_var:
					if not (ast.is_differential or ast.is_part_any):
						expr_vars.add (ast.var)
				else:
					stack.extend (filter (lambda a: isinstance (a, tuple), ast))

		expr_vars = expr_vars - {'_'} - {ast.var for ast in AST.CONSTS}

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

		if pos == 1 and rule == ('expr_func', ('FUNC', 'expr_neg_func')):
			return self._insert_symbol (('PARENL', 'PARENR'))

		if pos and rule [1] [pos - 1] == 'expr_commas':
			return self._parse_autocomplete_expr_commas (rule, pos)

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_intg': # TODO: Fix this!
				return self._parse_autocomplete_expr_intg ()

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

		lalr1.LALR1.parse (self, text)

		if not self.parse_results:
			return (None, 0, [])

		rated = sorted ((r is None, -e if e is not None else float ('-inf'), len (a), i, (r, e, a)) \
				for i, (r, e, a) in enumerate (self.parse_results))

		if os.environ.get ('SYMPAD_DEBUG'):
			rated = list (rated)

			print (file = sys.stderr)

			for res in rated [:32]:
				res = res [-1]
				res = (res [0].remove_curlys (),) + res [1:] if isinstance (res [0], AST) else res

				print ('parse:', res, file = sys.stderr)

			if len (rated) > 32:
				print (f'... total {len (rated)}', file = sys.stderr)

			print (file = sys.stderr)

		res = next (iter (rated)) [-1]

		return (res [0].remove_curlys (),) + res [1:] if isinstance (res [0], AST) else res

class sparser: # for single script
	Parser = Parser

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
# 	p = Parser ()
# 	a = p.parse (r'lambda x: y') [0]
# 	# a = sym.ast2spt (a)
# 	print (a)
