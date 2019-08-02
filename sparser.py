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

def _raise (exc):
	raise exc

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

#...............................................................................................
def _expr_colon (start = AST.CommaEmpty, stop = AST.CommaEmpty, step = AST.CommaEmpty):
	if start.is_var_lambda or (start.is_mul and start.mul [0].is_var_lambda) or \
			start.is_comma and start.comma and start.comma [0].is_mul and start.comma [0].mul [0].is_var_lambda:
		raise SyntaxError ('this is a lambda function, not a slice')




	return AST ('slice', None if start.is_empty_comma else start, None if stop.is_empty_comma else stop, None if step.is_empty_comma else step)




def _expr_lambda (lhs, expr):
	if lhs.is_var:
		return AST ('lamb', expr, (lhs,))

	elif lhs.is_comma:
		for var in lhs.comma:
			if not var.is_var:
				break
		else:
			return AST ('lamb', expr, lhs.comma)

	raise SyntaxError ('invalid lambda function')

def _expr_piece (expr_ineq, expr, expr_mapsto):
	if expr_mapsto.is_piece:
		return AST ('piece', ((expr_ineq, expr),) + expr_mapsto.piece)
	else:
		return AST ('piece', ((expr_ineq, expr), (expr_mapsto, True)))

def _expr_mul_imp (lhs, rhs, user_funcs = {}):
	last      = lhs.mul [-1] if lhs.is_mul else lhs
	arg, wrap = _ast_func_reorder (rhs)
	ast       = None

	if last.is_attr: # {x.y} * () -> x.y(), x.{y.z} -> {x.y}.z
		if last.args is None:
			if arg.is_paren:
				ast = wrap (AST ('.', last.obj, last.attr, _ast_func_tuple_args (arg)))
			elif rhs.is_attr:
				ast = AST ('.', _expr_mul_imp (last, rhs.obj), rhs.attr)

	elif last.is_pow: # {x^y.z} * () -> x^{y.z()}
		if last.exp.is_attr and last.exp.args is None:
			if arg.is_paren:
				ast = AST ('^', last.base, wrap (AST ('.', last.exp.obj, last.exp.attr, _ast_func_tuple_args (arg))))
			elif rhs.is_attr:
				ast = AST ('^', last.base, ('.', _expr_mul_imp (last.exp, rhs.obj), rhs.attr))

	elif last.is_var: # user_func * () -> user_func ()
		if last.var in user_funcs:
			if arg.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg)))
			elif arg.is_attr and arg.obj.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg.obj)))

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
				return \
						(AST ('intg', neg (ast2), dv, *ast [3:]), ast.dv) \
						if ast2 else \
						(AST ('intg', neg (AST.One), dv, *ast [3:]), ast.dv) \
						if neg.has_neg else \
						(AST ('intg', None, dv, *ast [3:]), ast.dv)

	elif ast.is_diff:
		ast2, neg = ast.diff.strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			return \
					(AST ('diff', neg (ast2), ast.dvs), dv) \
					if ast2 else \
					(neg (AST ('/', ('@', ast.diff_type or 'd'), ast.dvs [0])), dv) \
					if len (ast.dvs) == 1 else \
					(neg (AST ('/', ('@', ast.diff_type or 'd'), ('*', ast.dvs))), dv)

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
			return \
					(AST ('*', ast.mul [:-1] + (neg (ast2),)), dv) \
					if ast2 else \
					(neg (AST ('*', ast.mul [:-1])), dv) \
					if len (ast.mul) > 2 else \
					(neg (ast.mul [0]), dv)

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
		return \
				AST ('intg', neg (ast), dv, *from_to) \
				if ast else \
				AST ('intg', neg (AST.One), dv, *from_to) \
				if neg.has_neg else \
				neg (AST ('intg', None, dv, *from_to))

	raise SyntaxError ('integration expecting a differential')

def _expr_func (iparm, *args, strip = 1): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	ast, wrap = _ast_func_reorder (args [iparm])

	return wrap (AST (*(args [:iparm] + ((_ast_func_tuple_args (ast) if args [0] == 'func' else ast.strip (strip)),) + args [iparm + 1:])))

def _expr_func_func (FUNC, expr_neg_func, expr_super = None):
	func = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC

	return \
			_expr_func (2, 'func', func, expr_neg_func) \
			if expr_super is None else \
			AST ('^', _expr_func_func (FUNC, expr_neg_func), expr_super) \
			if expr_super.remove_curlys () != AST.NegOne or not AST ('func', func, ()).is_trigh_func_noninv else \
			_expr_func_func (f'a{func}', expr_neg_func)

def _expr_mat (expr_mat_rows):
	return \
			AST.MatEmpty \
			if not expr_mat_rows else \
			AST ('mat', expr_mat_rows) \
			if len (expr_mat_rows [0]) > 1 else  \
			AST ('vec', tuple (c [0] for c in expr_mat_rows))

def _expr_curly (ast): # convert curly expression to vector or matrix if appropriate
	if not ast.is_comma:
		return AST ('{', ast)
	elif not ast.comma: # empty {}?
		return AST.VarNull

	c = sum (bool (c.is_vec) for c in ast.comma)

	if c == len (ast.comma) and len (set (len (c.vec) for c in ast.comma)) == 1:
		return \
				AST ('mat', tuple (c.vec for c in ast.comma)) \
				if len (ast.comma [0].vec) > 1 else \
				AST ('vec', tuple (c.vec [0] for c in ast.comma))

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
		var = \
				'partial' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_')) \
				if VAR.grp [0] else \
				'd' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_')) \
				if VAR.grp [1] else \
				var_tex_xlat [VAR.grp [3]] \
				if VAR.grp [3] in var_tex_xlat else \
				AST.Var.ANY2PY.get (VAR.grp [3].replace (' ', ''), VAR.grp [3].replace ('\\_', '_'))

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
			b'eJztXf9v3LaS/2cOqA1oAYlfRCm/pWnaF1yS9iVpcQcjCNI0fSiuTXtJ+t4divvfb2Y+Q4mktLZke+31emF6JVEUZzicz5AckdTJ2Rf/9v7DT19UXzz69um3z+n49PHXr+jw3cMXj58/pZMn3zz/9sXjN4++f/H0P+ny6xcPH+mh0aOh45ePv3nz6OHLxy/1' \
			b'/NnDV3r25Xj6w3j6HU4lV6by7Mnz7+VZyu/fOeLlqxf8+/2X9Pv8+2f0+8NDjnny/NU3zOWTZ3Jbfv/+gvN6Ktx/y3e//v45M/mlPPHo22fPHsYSvYhEX0RifPLiyTd/4ywePvuOfr/68unLpw9f/o1OHz//SovCZ1+Opz+Mp1qUx3/nn6cvH2t0lAbn9gqM' \
			b'EAOc8tnD716++pbJvZJCPv6PR0/jbZbpV09+ePIVZ/Poq29fiSi05ELiu6ciqCdf04/kQjLip969/fj+85vfP7756cdfP31++5Gi3v/PHx/ffPrzj/fDxYf3/3jz858f3o03f4ynv739/Obd77+mlx9//1dx+Slev3v76f2nT+/yyz/yy3j19sfx9PPngZef' \
			b'3777HM//GCnl7P0WT3/9ZTj95cPnfwx8/fnrm19+Gwj/cyz3h/HZn375Zzz9/P5jEv3zz/H8x49v3/3X+8+JnIay/Pnx1/9NydFJIpWhZD/9lJV+ZPb9fw9FIyJDiX95/+79cEF192HM9I9Pn3+PV8PTMYJq+P1vf3weWKI6+/3DePHbb2+zi09fvK7OTjbO' \
			b'VM6cVjixfOKrTctHa6oTU5lQbZrK8snpECtxY8Sm45PG4sdTRONP06jGpVF8yg82+HG4QWeUlyTpmHDjlbBtTmOsxg0RG1PLGfFEF9ZWTm8xC05yZQ6sq6w71Uu6kjMvReUIpR8jcOXic/SAj1F8ymcsror4xc9pHqeXG0lq5N8wd6e43oiQG40Hu1QQjcR1' \
			b'S0W1UtQ6RlBx5ayntI3k1ODHsRhANIliiY+xfEpnlO0mVJayQNW1fMLM1vhx7aleUm0INbrBImdxmtMY06ZXQY8cxcS47qxUHsmSxYESaPzGzUQll26awuWXlDEXoIgqH/L5ZTu9zB7YmF6K0agG080G9dXglJORfphaqY8JYvR4uTECH6JyQqJvQsVVSQX1' \
			b'TmTCaSH+LSkYiYShZQmpnvOEGyM1Eui/q5yL2k2IRRGdYotKYduKlD5BGN2L0UMEVy3HtGNMg5gwxhjEdDGGFFYUqcNPArJOcWEDfgRUeI6u+JTP2njzVC/pKt4ADY8f1w9lj1G+TqP4lAXj8EP1c3o6nnIaYkQ41kfYtImkXI0bqiV0SZoiz5L85MRpWZwy' \
			b'JWbLRnPZxziJGS+dVKKP0CaBNGLEemibl5tMDQyl0RpB18JHj5+NGj0+tZIVqeiJFAQk6NLDGFFZmftBj1iXoZKi0apEIZaUIk9IxwYR8KUdsqVLB+GyaMxwZvUMOsAnSEVWoT+lNuesZntI3BJdUlgiR7eoQgg6fV31JL2K676rWl+1bdWbqrdV76qe7tNl' \
			b'qHpSbKLN7RVruG8rH1ilyUqGqiPNbkPV0uN9Fcg+NVUwVVdXXVN1rOpcOZ2vurYitUXbRPrZ1GQz675qSN8bkjebfpJMW3UcR0/YqiNSXeUp+7pqm6o1VWurlqqz5scdtWNkQEkkbH5JL0kPyY4QkL3g1RP3lFVds9CpeoVORfFV+7o6oYtTao1JLly1JBs5' \
			b'EIskMG5ucdci2kn0GVs5vu5rJLNIZSX1ie00VYtUmlfbIhVJVWKRuMFVzLiXrI6VVFRS71TCzVE8c+Lxqlot1BKq1Uc9dCI1FHFaOJRpKE1ZFJSAiDitA2euJTfFjAfLHizjN/LdSLHYZlKFkyGnTPuKrNo9rOEmGg8IqMahUUF1IigwTbyOvO2QqUzuqbiv' \
			b'qBln3P8+gnyiAtScSBMVQhW6KhDjvgpUGlsFdz/F0R/FkYgj1EdxpOJojuIYm4+AXmaHg9UrNL1N7Fuhj2sdDh69VmGcU9VoeqQAcmz0MeTSydN3q6k56WKZVCAqCY8ie7nb1FTQ2mjVDxV9GI3tSavDn7bBoETHJlaHLE7r3uoxdgExsHGoehcgJ4qsKaYm' \
			b'SVHo9q+0xDhq1vV3hmMPuHnUjzepSt6NAkB3vKgOuEz53keOdXBfKon0TWvUh+3j2ErNoXoColX0xy7sXKvMEoF7hQ5HebBfycCvRIf7KwYqMZX/PpWYykolvo91TaU0R9M4oxGCAfYHH8UzIx53FMuc41fajzP2j99Lc8IvBIx6vg083/dSDuLjN1f2yp9l' \
			b'b6VeyytIo156Oh7kEPjsRHTm4ErVHWCp+I2Q6GOjaqovbRt9W2sw+Gr0JW4dX4/UIouDEMEZv/U5mNLwmyupUDiaZl6Nv8b7c5mVxRa+7fBA0BeG0IDgtaoDEgd1YAXkS5zxs6HGQdsMK40mezpZnndSetr8exFK4arwWuj8lWrdpO7ba8VmbQZfooEv0cCX' \
			b'aOBIVmadR0dX/EJ27NOhzUbPDi332L+ba8LR6TuwhpydqZCStLh769UTXdtr/trr12+dDNSFPS76Sdepj77bYwViDzwsV73PXPrY/W32msvYCrh95rJHc2RxaNAU++gOtjrLzsIbarnF6NXVHiSWmgSLLoKkbTX2OCcinSUkwjlxkBSk2eOKOdaBssVAWWTs' \
			b'NNojOu8sQMSTyUYzsdwxt9oxN+iRc4fkns7WkhGIwQjkXrojWDsstMOiq6dYtdp1N+izs0/hnmL1jMco91M5iFeL0ZjFaMzqaMze0XkkZzyGtHdzDCmDR3ugvj0Z7hodk1qMSS3GpHQYhgrplUM3o5jg79A88qgHvRe4mztYMocm0UOhPUh56LMfujbu/r7h' \
			b'5V6b016bi04c9Fec9FccOipOeyjuPr0M5s6SKFevzSM0cHBhWbWPXqR0N+0j8esm3Uvi3QGTDph00U/k1E/k9nc4w0sBMRzxqtg+dnGg2F4UW9K0mqZBGtxrJYP7ZwtgcO9l0VmlPfzbrSpEC4VooRB0oPZKQdAiZdCU4VB8/mdc4IACBwEL3tbou5uaY6vM' \
			b'l83F7yCoDs91MWl3UFLpD6g09nBKI5rW6/ToWudH19KG1RWvqSVbxuRhlhrQC+r+MIbfY/D7DWypkMgC9g/FGNn1UvReywqzB2GxhTMsPi6h2EjMAm7BuXBN18wArxdjFvgNKb8H5Vek/HqUF7LyKlZe58qLKbn4bBd51j9P+efZ/LyMlQXLywZlnTsLh+J5' \
			b'nrfsb0DP8rI9Mcd0zfPkeR45zyFnCbF0uDp5+SuvSuF3cvy6jn1FvAKBp9nzijW2zSxiXvPK3kHuXHPHWl5fyVYIvK5a1kTz1gOVLGFvKdA/VfCGGogNL7PnhdGe11xzfLUJvCsGL4vnI2+Y4GR/ig3LaMPVu2lk0wRdTL/pJIYTU0Iqx6blNek1LzHnRew1' \
			b'L9GW9JXsV9A3svp/03lhpmPivWbnZOU3/XTMGq/wpoS8frzvsXsBE5adAij3npf3U9qWi8KlowyoSmU9uOf9ISpZoU53qVnbdLLvAaVmGXApeZk6l4AFwKWshVnmiPPgxf6UgrdT0B0LmO9e9tGgy07WoG96gx0mmBvemYGLxBwxrZqJ0b3WvubOKeu5S7W8' \
			b'iaCZ6LrxV1b3wTyIYSAJzal+s1D9r1v1/TL1z1Sf1d4uVX2qKtZDUZBc6xv93679fHuHCOi3/G9DRL8QFY2g4NoQwTktQ0WCCEYDZ7YMEYYR0SU4aHWlMkOhiVCQ19c6W3F40b0QGS4Bx6QNLIGStKPcoQ6xnTPqYaVR5ejccbGZjB3tEUxogtMVGmWrCJBZ' \
			b'BZovwNYmALM5sHhfBF43MQEY5cMriiZAo3S87oUXvaxqb5oEePUM+Di+SwDoFIRUZTxJgcqfA5LB0kpHoxbssZYR03KwEgnwdVYTDWENFBk3KRL5OgUj95ximACzoFuEAISmOQg1AaycAbNB1NwI51QTSIbIgHSdHFwPJgwOyC1Fcz0CmME7AFfvFfDV2ATE' \
			b'I4+smYugLDRZc8ETGM0hrXQU1CLfnNQI8OovVz9g49iHB1I7pJEP2LSQZtHR/x+/UlMLUCdGIOwT/GexbxfB/wh9hX7DEGEyXHq0vNrq8iVwj3tpWIN7Tp7iXkgmuM/yneD+3CDbVBVRJIbWij1rirZaNADttaYVHWgE9nKjBw9I5iGCFPbNNtgr6QL2iE1g' \
			b'P3K5HPbo1kbxgNEC9ioLwF5I5qRmYD8Dd1c2+PuP9SPQlwPdCCbEG5Ch3AwoN2VYhXJToNwUKE/znaB8QjpL7qZRaNrlbAJxA4jjTGrfAOIGEDeAODrpIo4E4mYbxJVuAXHEphA3I+WlEDeAuPIERguIa7EU4gYQT0gtg7g/SIgfu/IJzFvBhYQM5u0A87YM' \
			b'q2BeDKeFXgrzNN8JzCeks+Qs5CJKYT6OuqUctUH6kKSU6m+B8xY4b4HzFjhvi/H4NpwruQLniE1xnlBeivMWOFfhgNEC5yoJxXkLnCek1vXg2yPeDx3v4jzj4nU53rsB710ZVuG9K/DeFXhP853gfUI6S85CLqIU792I907x3gHvQ0qp/g54h9tNOEBKDwGk' \
			b'eO+24V0JF3hHbIr3hPJSvHfAuwpH6yjHu3KveO+A94TUOryHI94PHe+9AIST53jvB7xPwiq89wXe+wLvab4TvM9RH5OzkIsoxXs/4r1XvPfA+5BSqr8H3nvgHZ52OUAAKd77bXhXwgXeEZviPaG8FO898K6sgdEC7yoJxXsPvCek1uG9O/ro7wvwjTjquFLh' \
			b'pTPw0Rv46M3gq0OKNKyBvyl8dabw1WX5lvCfki454eX2RRQsgBl9dUaH8QaeujEl64GBs87AWWfgrDNw1pncWWe2Oesi4dwCaGxiAVLKCy2AgbMuygeM5hYgSgIWwMBZl5JaZwH6owW4NxZAhvZGgliAFhaghQUYBvimLcMqC1AM8E0xwM/ynViACemmZIVN' \
			b'QBGlJmAc5Bsd5BsM8seUYgIwyDcY5BsM8g0G+SYf5Jttg/xIuDABiE1NQEJ5qQnAID8KCIwWJkAloSYAg/yU1DoT0NRHG3BvbEAQqAT5dhLbgAAbEGADhmkySJGGVTYgFDYgFDYgzXdiAyakS06cmUSpCQijCQhqAgJMwJBSTADm2sg9JPVI6SGD1ASEbSZA' \
			b'sylMAGJTE5BQXmoCAkyAygeMFiZAJaEmADNwUlIrTUBzNAH3xgSIx4/rDx4/g3lycpDdRqIJ6MqwygQUfj9T+P2yfCcmYEK65MSZSZSagNH1Z9T1Z+D6G1OKCYDrz8D1Z+D6M3D9mdz1Z7a5/iLhwgQgNjUBCeWlJgCuvygfrazcBCj3agLg+ktJrTQBx/l6' \
			b'98cEiBOQfg2cgPKlLoeDlYOagElYZQIKV6ApXIFZvhMTMEc9e4JNQBGlJmD0Bhr1Bhp4A8eUYgLgDTTwBhp4Aw28gSb3Bppt3sBIuDABiE1NQEJ5qQmANzDKB4wWJkAloSYA3sCU1EoTYEcTYA7BCug6mKMxOPeNACa7WZYun/O3sqzYAzlYOeirAVuGVa8G' \
			b'ivm7TTF/N8t38mpgQrrkxJlJlL4dGOfvSlFYE9jh77WEIXlCVALzeBvM420wj7fBPN6mmMdrt70lUAaKtwSITd8SJJSXviWweEugcgKjxVsClYi+JcA83pTUSruwZWZfvTcW4TYn97kr2oGbsgH8folflYWLOgdOGlFXyRqs8Q0hb0fjhp6BK8OVFtWYYl0N' \
			b'amX8n3YPJvQzXrhvUESpLWAsdVKYccKfPJEQG07kUxxwEoALo0eLY9pDcJkl4PzHToJyUHQStNj5yhwR8eIugkMXAWt0eI/PeuopUIloH4Frm3moNpgDOAootwo9oZ/VMJBZ8J1YAT8znX8/ewfNlab2HzsHiTEQ1LSoUY/BAkyCHGQtYzQJvgyrBgu+sAi+' \
			b'tAhNkvHEHExoF6FVo1Aw2OFOiwsdM3i1Ch5jhiGxjBk8xgweYwaPMYPHmMHnFsFvGzMo7cIcIDYdMySUlxoErNiLUgKjhT3QGlR74GEFElIr+waTKYL7aRKOboOrGwMstOUagufQwnNo4Tm0g+cQKdKwxhLYwnNoC89hlm9pCKakS05I2mUUugZ29Bxa9Rxa' \
			b'eA7HlKwHFp5DC8+hhefQwnNoc8+h3eY5jIRzE6CxiQlIKS80ARaewygfrazMBERJwARYeA5TUitNwGTW4I5MwLl7XhwNwQ0aAvEf0q+F/9DCf2jhP7SD/9BOwipDUPgPe7xFZHzJZii12gPJmPdrnXEjTjkoGWJ7UESpPRjdiFbdiBZuxDGl2AO4ES3ciBZu' \
			b'RAs3os3diHabGzESLuwBYlN7kFBeag/gRtTHPBgt7IFKQu0B3IgpqZX24Dir8N5YAiezCp18ZmCDTYXYEjjMKnTDrEKkSMMaS+CKWYWumFWY5VuagCnpkhNWqiIKJsCNswqd+gocZhWOKeUbnZhV6DCr0GFWocOsQpfPKnTbZhVGwrkJ0NjEBKSUF5oAh1mF' \
			b'UT5gNDcBURIwAQ6zClNSK03AcVrhjZoA9WbfrikwAhnDQUyBgSkwMAVmMAWmDKtMgSlMgSlMQZrvxBRMSJeczESpKTCjKTBqCgxMwZBSTIGBKTAwBQamwMAUmNwUmG2mQAkXpgCxqSlIKDdDCZYYBAODoJyB3cIgaG5qEOAsTAmuMwhmMsdwRyuLrvWdwfIt' \
			b'tHYB7MuC+cpAFo8YSzV/AeAG7z/upWEVhF0B4Ys21ZqSy0izFhRRillXZav7Hfz8m4v22nJuGzA19wKYWoQEmCNvS9AIL74+Md1oK2alUHSA4hC/dO2+mczxO0JwbyEoU/WdhAyCwyR915ZhFQSL92+uvQiCE3IZadaCIkoh2BYQbBdCcNvM+5h7AUHEphAc' \
			b'eVsCQUy61ydmIKhZKQQx434ksRiCkzl2RwjuLQTF2c3exi6H4ODmxr00rIJg4eZ23UUQnJDLSLMWFFEKwa6AYLcQgtuc1zH3AoKITSE48rYEgvBb6xMzENSsFIJwWo8kFkPQHuQS930ajN7mIJR1qhXh1xlq+RKoxb00rEGtTB9JUCv0EtRm+ZYInpLOkpOQ' \
			b'yyggWOes5LtUyRMhJuTal2QdbvRgAMk8yp9gWy7nsB3p5tjW2ATbI4uLvVBCM0qIAS4RGcajIIBxIZmTWojx4050B41x8Tmz5Jsc44O3GffSsArjhbfZF97mLN8Jxs8NgvEiSjHezGEczmZNKBiHp9nD0+zhafbwNPvc0+y3eZoj3QLjiE0x3oyUl2IcnuYo' \
			b'GzBaYFwFoRiHpzkltRDjh7kV3RHjinFxJrPYTY7xwY2Me2lYhfHCjewLN3KW7wTjE9JZcjeNUoybOYzDi6wJBeNwIXu4kD1cyNpB97kL2W9zIUe6BcYRm2LcjJSXYhzO48gTGC0wrsVSjMN5nJJaiPHD3H7uiHHFuCw8YZnbHOPDehPcS8MqjBfrTXyx3iTL' \
			b'd4LxCeksuTOTKMW4ncM4lploQsE41ph4rDHxWGPiscakGIf7bWtMIt0C44hNMW5HyksxjjUmUTZgtMC4CkIxjjUmKamFGA8zHwhKZ5j7O7LaZGfbxvPWXrNfKEptgrmmxSiXsA1tv8U+NDM2or2MnejO+dARccC1pT664psvfvDVIU0arrRexRfOuizjyTdh' \
			b'5EtNzGEzw4eH766M4pnpMCjdnEGBD0/TikHBrFQPf57HrFSPWak+n5XKNTf3kSWfOPxmvyoTWSsMDmKLdSwDawstDguHVUTMTjd8cyb9EFP+6ZkoOrU/8AeO8pvYH4mX355/W4lhgyT76Ho5kFnCWheqrbPdf7Rsz75Y5lf2ByLWt+E84rv8fJPfhuVb+mjZ' \
			b'Hn6wTFZoLETN7EfLVnymqZ+oerMTbdcWtd0rnV/axrVbdH6Jvp/zlT5b35bSa3vU6E4K+6T8y5sLM6/8yxSfZF8q/rTHeY2K31274tc3o/yLFJ/iSfQjAGpZZ3qHgGB31Aqw+Pbj05XoaXcDIGJvewKMZlHn5xq+Ypl/tJUkf4k5B7fcE+JdHRYBpF7fOpwD' \
			b'CLvuteXVv+PaJBNgNcv6tloIHl6uaCXcMnDY+Zai+ov04QHVjnzRztzEuGDBp10viwxilXStMd3N9Z2uNFbY2y8cs/bH/+tuNqS7KR+N6a+IlCs1H2yzlvSlCCGdfUDkBSG2OtslNtj51scGo+MvkK9ExQ2OHETz+eiLeWmLNH8ftF32VOrHNoAOwV1Gy29y' \
			b'ZOCUUVtlXy5eOCpwu9df+u2iCoedavGs7/eymkzXwR6ERrONS3o2vHyh3a1mm+mkqktr90b2+eeHL6/l/gItp1bp6oquKt5eWcsXvOmYfcNxmR5LuDm7vXNNHzScX5x216HlYXWPJITLaXrT4R3kVbS8vUjLw/Vp+aDi9U31SC6p4Yem3almN+V6k132Ti6r' \
			b'2VfV6nCRVnc70OrmqNW3qNXh8LW6u0irV03yWKjV5qjVt6jV5cyGA9TqfuejyUu5Bm/aCaKqS3q20v1neQrWrY8YL+/du1m/R9RQnl+1ZhpA9Vd4QKaC/XdU6qPG3mHnxrWpKs/nuwFVXWpMq7+ozh8QfkRJm9076drMT7cj99y26ZlXddHdVe1lqWyazD23' \
			b'M6PbhB255dZ3E6jk16/PW+Y2ZwbYp3OVb9IML5xfPDHFcx2HRpW62w/Fnvs/z0wDDFHBuRpusmuxYoJuYbSnfQv+voB8cIJLNDXg3j0g0Iv93sVLwqO+35a++8n/+fruD0bfg+q7v0DfXXXWVeMCNiMKbkS1U70WpeZGPFvrFeb1KhRrsHqiecbEk6VUUtlB' \
			b'a7lx87U71Gy5IZ20kjNyZMmkEmmDNGJ+RSFHbMq+vgDbgkJHkJTgkMJv2ssXnjkYlLUdlHOZQPxUJm4QS7tGLH4qmf2QTsjhHCUUwXllKYU1UjrH1MPIr7DwC8S6xnpPrHbscndXrQIpSf4/NbMxfp1pXVJ76wxnUcnxS1R1m9vFrqz123MwbFlduxOHwpx+' \
			b'TFryGV2Zb7b7PXAezC5Q3Y2zYKpWM22v9Q+oNyM61h91bIWOcZXtq4cqUTJed1vftpIZ+0A+iki6xs6c9sFGXKiU9VHjVmhcczc0TsKealyTa9wt++r3XOnCua3pvundHjSnrGFmbzXsJt4AzWkZ/F3j9zTP0zh38xonNC+jcPzgbnQubB0YGPmYT/wmZWH0' \
			b'pp+iJO5VG/fl9eQ+KOQWJeQau0OvIVPTdwOvHheaPyfft2iCjOJFBTrxW1DZeb98byiePzjevT6ls5ON7LWOTWyMbJwxrOaicTR/dJsXwhNtrkDZ4GVcmNV5znhjLsiBtD3/k6ds+RSvJcsfJFzoHy8R03N52M09XGfP85Iu3hy5Gv94kdlw3jWSk09yasq9' \
			b'esaMJ1vrCAWe7j28GcViDllIho1jeAOJiv8C5cSTuIbAkVjt5iokwRJpIys6KQFPP6HGnwETNCnWLQvP7U55ptpe/yd8hWV8ze1UdC5rvF/PwB5Zvtk/fgOy7V6QdxJ0FDa7nM3JDk1OvquQue7O32Up32KJLZysCbbV+IFo3quCd0+iOG4J5kqa7moUS82W' \
			b'VHYoktLLuuhk96HX3Lbon6u6Kr0owtzfXKpp3HzG40X+lAi4vwk96KtL/gmLTb1zJRjWhkc98DvWBW7qdxrYuzxedNeSK2qjuQmNYWFff0ABkjaQe1vdNSlVvRd6FSoEfIdsuLxS4P7ntWR0QUD12PP0y7mLsb1Vy1JJDprGffwtoW+33kLgXvlMbAjpNUrl' \
			b'DljpeIx0VwNq59ye5RKdQxWs1DxbXSXE4eBFCVHC9oD1j0fndzWgdsJFPZzFKohaWKGIc/JsqiHQYD69XBWik+LihIWXQWTSHbLGmurOBtROv18aa6tbCvCq1Iesq666swG10+yXrvrqlgKkccjDH/bK39WA2rF3r3bid6KX11Ko9jk0gefB9uenQm25a7Ys' \
			b'/Xmj13qhgWHluL7AVT0TS5W8/SEIxy9z212XfLYajK1ystU5gb8aeG6ChaHIZy5biKvdd3H5aj8CxHXhkOm2xRWq/QgQ1yG9SGGLdFHAxzDG/yXPXJDFquxmE6EqLhw63aGq4FkOdybgXfbu3ybdoPh9dXcCxH/hYOwuib+t7k6A+M0hiT9UdydA/DS8Mzxd' \
			b'Jmh1uHit9z1fs3g4jochOgGHOodpLZEMeUJBK/vCNbzjUNNqDmE2ZaiSgITdJCFXByfuqjQ0QQ1nn0xK4glGmJTDW3uk6nJu1Xc1v6PkuW/pnLdhrtrMPLUOjSbvzVAs0JKpkvKuWCj2IxUeOHveiR7C43XwTS/zo3oyQq9P/x/2tuKO'

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
		('COLON',         r':'),
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
	def expr_comma_1       (self, expr_comma, COMMA, expr_colon):                  return AST.flatcat (',', expr_comma, expr_colon)
	def expr_comma_2       (self, expr_colon):                                     return expr_colon

	def expr_colon_1       (self, expr_or_empty1, COLON1, expr_or_empty2, COLON2, expr_or_empty3):  return _expr_colon (expr_or_empty1, expr_or_empty2, expr_or_empty3)
	def expr_colon_2       (self, expr_or_empty1, COLON, expr_or_empty2):                           return _expr_colon (expr_or_empty1, expr_or_empty2)
	def expr_colon_3       (self, expr):                                                            return expr

	def expr               (self, expr_eq):                                        return expr_eq

	def expr_eq_1          (self, expr_mapsto1, EQ, expr_mapsto2):                 return AST ('=', '=', expr_mapsto1, expr_mapsto2)
	def expr_eq_2          (self, expr_mapsto):                                    return expr_mapsto

	# def expr_lambda_1      (self, expr_var, expr_commas, COLON, expr):             return _expr_lambda (expr_commas, expr) if expr_var.is_var_lambda else _raise (SyntaxError ())
	# def expr_lambda_2      (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr):                       return _expr_lambda (expr_paren.strip (), expr)
	def expr_mapsto_2      (self, expr_piece):                                     return expr_piece

	def expr_piece_1       (self, expr_ineq, IF, expr, ELSE, expr_mapsto):         return _expr_piece (expr_ineq, expr, expr_mapsto)
	def expr_piece_2       (self, expr_ineq, IF, expr):                            return AST ('piece', ((expr_ineq, expr),))
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

	def expr_cases_1       (self, BEG_CASES, expr_casess, END_CASES):              return AST ('piece', expr_casess)
	def expr_cases_2       (self, expr_mat):                                       return expr_mat
	def expr_casess_1      (self, expr_casessp, DBLSLASH):                         return expr_casessp
	def expr_casess_2      (self, expr_casessp):                                   return expr_casessp
	def expr_casessp_1     (self, expr_casessp, DBLSLASH, expr_casessc):           return expr_casessp + (expr_casessc,)
	def expr_casessp_2     (self, expr_casessc):                                   return (expr_casessc,)
	def expr_casessc_1     (self, expr1, AMP, expr2):                              return (expr1, expr2)
	def expr_casessc_2     (self, expr, AMP):                                      return (expr, True)

	def expr_mat_1         (self, LEFT, BRACKL, BEG_MAT, expr_mat_rows, END_MAT, RIGHT, BRACKR):  return _expr_mat (expr_mat_rows)
	def expr_mat_2         (self, BEG_MAT, expr_mat_rows, END_MAT):                               return _expr_mat (expr_mat_rows)
	def expr_mat_3         (self, BEG_BMAT, expr_mat_rows, END_BMAT):                             return _expr_mat (expr_mat_rows)
	def expr_mat_4         (self, BEG_VMAT, expr_mat_rows, END_VMAT):                             return _expr_mat (expr_mat_rows)
	def expr_mat_5         (self, BEG_PMAT, expr_mat_rows, END_PMAT):                             return _expr_mat (expr_mat_rows)
	def expr_mat_6         (self, expr_curly):                                                    return expr_curly
	def expr_mat_rows_1    (self, expr_mat_row, DBLSLASH):                         return expr_mat_row
	def expr_mat_rows_2    (self, expr_mat_row):                                   return expr_mat_row
	def expr_mat_rows_3    (self):                                                 return ()
	def expr_mat_row_1     (self, expr_mat_row, DBLSLASH, expr_mat_col):           return expr_mat_row + (expr_mat_col,)
	def expr_mat_row_2     (self, expr_mat_col):                                   return (expr_mat_col,)
	def expr_mat_col_1     (self, expr_mat_col, AMP, expr):                        return expr_mat_col + (expr,)
	def expr_mat_col_2     (self, expr):                                           return (expr,)

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

	def expr_or_empty_1    (self, expr):                                           return expr
	def expr_or_empty_2    (self):                                                 return AST.CommaEmpty

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
# 	a = p.parse (r'Piecewise ((1,True))') [0]
# 	# a = sym.ast2spt (a)
# 	print (a)
