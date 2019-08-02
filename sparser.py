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
def _expr_colon (start = AST.CommaEmpty, stop = AST.CommaEmpty, step = None):
	return AST ('slice', None if start.is_empty_comma else start, None if stop.is_empty_comma else stop, None if step is None or step.is_empty_comma else step)


	if start.is_var_lambda or (start.is_mul and start.mul [0].is_var_lambda) or \
			start.is_comma and start.comma and start.comma [0].is_mul and start.comma [0].mul [0].is_var_lambda:
		raise SyntaxError ('this is a lambda function, not a slice')




	return AST ('slice', None if start.is_empty_comma else start, None if stop.is_empty_comma else stop, None if step.is_empty_comma else step)




def _expr_lambda (args, lamb):
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
			# elif arg.is_attr and arg.obj.is_paren:
			# 	ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg.obj)))
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
			b'eJztXWuP3LaS/TMLZAZQA5JIipK/2Y6Ta6zt5NpOsIuBYTi2cxFsXms7+8DF/vetqlOkSEozo+7pnunuaYymJT5EFot1imTxobOLr/7l4+8fvqq++vHhS/p99uSb13T7/uHLJy+e0cPTb1989/LJ28c/vHz27+T85uXDx3pr9N7S/dGTb98+fvjqySt9fv7w' \
			b'tT49Gh9/HB+/x6Okyrk8f/riB3mX0vtX9nj1mol59cMj+n3xw3Mm5MXrb5m+p88lQH7//pJTefaCf77j0G9+eMHkPZKiPP7u+fOHcn/23YtQppch25chO354+fTbv3FSD59/T79fP3r26tnDV3+jxycvvtbC8NOj8fHH8VEL8+Tv/PPs1RP1Dvzg1F6DICKA' \
			b'Yz5/+P2r199xdq+lmE/+7fGzEMxc/frpj0+/5mQef/3da2GGvP70hWTx/TNh1dNv6EdSIS7xW+/fffr45e0fn95++OnXz1/efSKvj//z56e3n//682N0/P7xH29//uv392PgT+Hxt3df3r7/49fU+emP/y6cn4P7/bvPHz9/fp87/8ydwfXup/Hxy5dIy8/v' \
			b'3n8Jz3+OOeXk/RYef/0lPv7y+5d/RLr++vXtL7/FjH8fX/jwy3+Fxy8fPyXeP/8cnn/69O79f3z8kjAnFuCvT7/+b5oHPSSsiMX58CEr8kjhx/+M5aFMYjF/+fj+Y3RQhf0+Jvrn5y9/BNd/jdX367vffvrwLrhisjHbP3777V3m+PzVm+ribGWbyrbnFR4M' \
			b'P5hqZeXeVGdt1XbVqqkMP5xHX/EbPVY9PzQGP66lUHeeejU29eJHfrHGj0UAPVFaEqXnjBunGZNn8FW/6LFqa3lqqzNyUFyrQUwCCtHyj6mMPVcnueTJSlEpaGXOMw+4THiPwm3w4kd6auW/9eFVTlSyVX/QQNSpJ9wd0W+E/jp4UBnkaaC4UvS2wY/lsmni' \
			b'oxezcfTlR643+neVoSTAR8sPHGPAj0U10ROxWHIjvjMfmUftefDpUpfXO3vxu54qBDVCHKGczXCe+K9sPfFKnWYaw+ROZnI/8SpfsrnTTZz5C6sWzG1ULInuBsxr8MjRiHvMfc6d39YIwXt0rlphqqN/CH8fKp/yFXYRAWdtXTW+4lruKmeFW5woBGI+AuOO' \
			b'ELMoHtV/Hm9FGKQnKv6qr6wNJFHZBymnVSBxCUlGXAonCgve0YOrnH260aeBjx99Wvj0wYcEWeDh8ZMgyisuTIcfARNSIhc/8pMLgefqJFcIQB4OP3aIZQ9erk69+JEZY/BD9XZ+Pj5yHKJRKNZXiMBGOEXwkQCVHkZTi7SIfyJGopNM0IWIRn7iMzqt1JkJ' \
			b'ECchaQRzA6TOcT1WLGggIPVWD3JLvj1+SCrP1U0QFtpYD3pJWJ0OeCcmk1aIYsNlgPzZRGa6UDDyPLMjUMVpYqrktCg/vdu24anThyY+SKSuas6pMbmoK5JJyoLARzwn1Ij+pHp0RORQNfVQdbbqXNUP1VBXQ1MNbTWYarDVwBLFNHPOwhESe6pSUpK+6kmA' \
			b'u67qfNX1VTdUnjRUU/mh6uuqFyySdutt1VP8tkJ7QwVvanLXRFxNPKl71lws/6bq+6pvq57yINIIYJRuXXVN1bVVRy/X/Co3i9QgMqosiV5H/GAVTDJIMucEs0NXDSTvxGpOv6KKtJWrujfVGTnOqXElbnBlth1uRtjEeoydBnGMuhx4eEasYrfQfX7iJ/jJ' \
			b'hRWmDGBaB6ZB7s46B98esTqwmyk/F0QKX4f6xM/ITyoZBLQ/MWVkSgumDILMswEyNgRgGuEVSjctF4oTC1KWgognRlImVjlvhq2kporGgWQHkr389kp3I+jgZoESpaQp0aEi1X1fq7nptJrBK9z6WrnVCwtBL5E5krU7mjKOp4y+oXRc8HDjBG+td2o0BBee' \
			b'iPeV7ytvK+8q31be3GOe9CeeTHgynHhS8sTXJ54U7Yhv0HLg1mo7gh5/Y7WVr9G5RxzTor8qNEt31uu91+hoxnvpiBxUW3PWY9jS66jGoYRO2tqB6nbQKo4VehRN7JnzOiBBRXeo6E4rujNav7XetfNndWiCYCvC0tTkWXNRiTFEsN+7whLdqFXbHQzBAJiF' \
			b'cNphlMZDoN5BbJxIDYhMyd5DgiHXQykfMv5GVZguDKeC7lOdqNBwpx7r2OoyH2A4otu95QIVm4p/z4rNdsBWTV33ufKpgO1JIcShSScKgag5MSUyxZ6YMdowa2gNKuH91Rps1m7VktvCksvMuI+sELN1e2ND80U2qfImTk+xGbtVAzTdj3GId3HmpWhHVqj+' \
			b'+ArFMx0ijI0OLTDq4zlxmXbV6Z0Glpo2WPy9iPBRcOCC5zGOpTA8FSPViUmtmcndN5gBlmVVrOc7jxc8fD3EwIcZYA/rhddXPawvXY93RQrYzilJGGk/2WLH7DxE5rWqmAUTxVjcoRuZzxMOYeGB3LdJyxBm7WuwGrztmMI3sI61ahVrUZmc/9ijQ8ONft09' \
			b'a77ZNgjeiITvq6FKxGufyTPbFmm2v2HNSbe/JT/r1Tpt3f5KD1uTIeJ+n4nUfq7t95hIp4rUNXtM5IC2x6glA01CtHPyclHW9+dYCWfu7xi2Ey5wt0eYQbQbdHFO87DFep5WOAN2UUnl1sit7cG8AYI1cBx6w6i3g3feDfLwK5cFzfjyeMPoeKPFQIO7Wvd5' \
			b'cZWMrlqMru6x/ckPwC6EsTEBukZHJy2GJTwCv8/QveCx2D0Wkw5apYO0+BryYaC7DnARyAWPl81BjpdloGyO04LJI/tWx98G42+D8bc5H4dIdeKyaFJbWE548Cl6rNYBeg1zSw9FZh3aXzScFjLtkAeCCNcWXRmrXRkbrDVov6203xYNt9UWm+77ogZYJe14' \
			b'xgL8arS359GbiaaqVlUDWHWQqoHItZPOFpFuIZEWEmmDRciqRcju7UCG0nUqzi407xBnJ+LMvySuTpHnUE6Hcrp72+pB19zf8rNQOxiyOxWNDqLRQTToRmQrDDrE9BrTH4lt/4LL61FeL6jBnIzO0NRS0sxozaXvwace7/Uhan9MTBmOpzDt0RRGxGzQ9b21' \
			b'LvCtpQWrK971SsoMBEAfMUmSI2+5qmXXFValBB5A84H+lE4uuJUi96rmlE+9KLVWmGdFJwoHAJFOiG2EEeTmgnDePA3Kc6A808mToLz/lDf8sfbjFem8HJ1XnPMOVN5+ykszeVsabyqTzeYUzit+ebkvL6TlVbS8rpsXdfO6Z96pypqb1z4zY5gpXIm8OZP3' \
			b'UPB8G0/FsbmEuyy8Npy3V7FVmjcgEv0tdyVrGgnXjpiJTfu8Qxk73nkrOJdu5XhbNDUQvPWeWogV1e5qcLIlXjY3O9mEXvHuac+nUfDZCPTc8/ucFO9/riUx2TfNW/cpeardFdG0orKsOtn6TO/x4RUD71vnmJxOoIG3UxP1TAIVZuU6TYl33fNswIqKtSJW' \
			b'rXiXOm9LH/gliVXJDnTe/E6sWQ3sphcHPfSAN3/Tq7xVnI8S4GzkIAKKzYSRf8flktMxKHUhlI9uqLkInB8zgvPmtLgEdHHyjRyIsaIaW/UDjnvg3HmrOT12zErhC2/rprhd+4Y7oCzOHYS4FUg43ToIu1bbqiiP660EQinArxJuM8p3iudM1r12CaJa4H5B' \
			b'F3DbqM0Epk8dpgEVZgQGT2byavtkuXQJbtlMLJhpFDdGseMK/FAY7+SO2GkLzFA83hw6wQ7rFDvFEC9D56XdvK6bV0zz5s1FuGJM1SOu2Bop2GoSfFEYT0lFjLWKM6o64kfLQ7gMc6TkIrbkmd7oBVk4EaMPyOqTv4Uo6yPG+hxlMZ0Cbf3MX0Rf4gUc9hGJ' \
			b'TPZQAYzxLSsRvHhLFCtRnJQpASdKraBkQEYwoqg5IMUvAaVmN+h9ETyHRkvvhMQBSAdAkQoA2gtEY4FGoFb/7B4IX2z9gFXZ4B8Iw0m8HrCWIBGhe/t/0qU6AfpWAX1XQJZCRyiri97ihoMK4HEOiEQBno1GitdSVI9NZ9l6wisE5Ni+4vJ1gnKTp6JQNxHr' \
			b'HJkXlDRAu8RCAhbRvNwsXrIDaKnllqA+MGgO94EdOfLVN8V+pHJYA/pNA5IcyM3Qr3kE/BsogJjNhjrAJDqgSdRAf/cK4FL0m0UK4AR+BT8XKoK/Exd7cEdZO8kSLshv2vJaiHyOqcjnxxT5WWol8if5jVED7Et/qvyuFUXWFv3tQSIz9mMSFrE8AvCORTSH' \
			b'gqfAV87MAl+5UQAfvgnwRzrXAr5yx4HcHPgIU+BLdnXGpsuBPwN4O9fo7zPaT1BfDnUj53uFdh6uFOcm4tyU11Kcjy18U7TwWWolzif5jVEjzgt/NO+NmQG5AcjD+zhZjdmE1r1B696gdW+K1l3ZMgtyZUUBcvimII9ErgVyZY0DuTnIERZAjtY95dFaIHdH' \
			b'CPJThz4Buq9wzB+ADlcKdB+B7strKdD9CHRfAD1NrQT6JL8xagR64a9A9xHoUhqJJzBPErCIBqdFTIuYDsVOka58mUW68qJAOnxTpEfPtZCuvHEgN0e6Eq9I90B6UsaN+vHdCfHHjfihakZLt7pSxA8R8ZNrKeKHEfFDgfg0tRLxc1lGchXxhb8ifhgRPwDx' \
			b'AxCfJGARzSMMMa0SgmKniFe+zCJeeVEgHr4p4mPmayFeSXIgN0e8FkwRPwDxSRk3Qrw/If6oEc8VWUfEqytBvAQK4hGWXgsRzzEV8fyYIj5LrUD8NL8xakB86Q/EyxMQ38JWxzfeyJQkYBHNIwwxLWI65cKI+MCXOcQHXuSIV98E8WPm6yA+8MaB3AzxGqaI' \
			b'l+xyJm2E+P5kr78n0G+5LiP04Rpws02lx+q30WqHGOm1VAGMVru2sNplqZUKYJJfFjvqgMJfdcBotZNiDSiPzRKwiOYRhpgWMR1KnuoAZdCsDlB2FDoAvqkOiJmvpQOUPQ7k5jpA60t1AMx2aRk30gHDSQfcEx3g5SMiQQfANeDLIqwDPHRAHOgjRnot1QHj' \
			b'QL8tBvpZaqUOyDPjCsiiRyVQEKVKYBzstxjstxjspwlYRIPTIqZFTIeip0pAOTSrBJQfhRKAb6oEoudaSkD540BurgSUeFUCGOynZdxICTT1SQvcEy3Qy9dkghaAi7UA1uHgIyCIAi3Ql9dSLTAuyGmLFTlZaqUWmOSXxY5KoPBXJTCu0mlh2G+xTidNwCKa' \
			b'RxhiWsR0KHmqBJRBs0pA2VEoAfimSiBmvpYSUPY4kJsrAYQFJYClO2kZN1MCp/V490UJDFxtUQnAxUpggBIYoASiBbCdXEuVwGgBbAsLYJZaqQTmshxjRyVQ+KsSGI2ALYyALYyAaQIW0TzCENMqLSh5qgSUQbNKQNlRKAH4pkogZr6WElCSHMjNlYAWTJUA' \
			b'jIBpGTdTAqc1fPdECXCFjeZAdQ34OJxtwre8TDQKIkZ6LVQCZjQKmsIomKVWKIFpflnsoARKfygBM9oFDeyCBnbBNAF84I4YZmAXNLALGtgFTW4XDAyaUwKBHbkSUN9ECYyZr6MEAnscyM2UgIapEjCwC6Zl3EwJmFwJmMPWA3ICe31SB1fPBzJh43ygMJo9' \
			b'BmkE9IOQMjEY97/glfRaOjFox4lBW0wMpqmVE4OT/LLYcW6w8Ne5QTvODVrMDYb9EBZzhElC+qJHGN6wA2gCB9I5QsSenyNUthRzhPBN5whj5mvNESqbHMjN5wgRFuYILeYIkzJuphmuWO3XHPA84ba0QLnDbU1NcCtagGfjeQ7ZXTdKcBU2pGGUAFcyX+g1' \
			b'HEMEV14b7I7jtzJlIHUy/k/GCZNMx9zjIKHwD9oAowTvlIpBYooeCJlBMnR1UK3Lg2pdH1TrAqG6MBoql0ZdwDmMowXlTDFagG+x+07SWWes4GQPHotDPTUbIoswWOCq5zFCtdJZhIRtM3phoLusouK7Ez3gLlnmv1c9hPqmS/5PHYREHXT4PLsu+zeVegz4' \
			b'bDvbDTrYDbqoFLryWmo36Ead0JU6oUmSKxXCJMP06pK1wSVdvAdAvmTcjntupXQDimWTuGI+6GA+6GA+wFZcoQgMSHWCpjRrPlCuFAoBvqn5IGa+lkpQJjmQm2sEpVo1AnbopmXcrH8wu2xwr5TCyXywHfNBz3UTzQdw4SQEMR9gIsHEiQTESK+l5oNxIsEU' \
			b'EwlZaqX5YJJfFjuaDwp/NR+MEwkGnQODiYQ0AYtoHmGIaRHToeSp+UAZNGs+UHYU5gP4puaDmPla5gNljwO5ufkAYcF8gImEtIybKYHZlYRbVwKXHNdxUgW3rgoGrp6oCuBiVYDpBIPpBBOnE8zkWqoKxumEASsLuBerZ7lAI0hyfFzLdFZhmm1GQtQIhb9q' \
			b'hHFWwWBWwWBWIU3AIhpyt4hpEejAgFQjKJ9mNYJypdAI8E01Qsx8LY2gJDmQm2sELZhqBMwqpGXcTCOcVhreE13A9TGeDKAuektsBnCh1lQXwC+9FuoCjqm6gB/TbkGWWqEEpvllsYMSKP2hBOQJSkCKNaA8NkvAIppHGGJaxHQoeaIEAoPmlEBgR64E1DdR' \
			b'AmPm6yiBwB4HcjMlECoKSkCyq7MybqYEZpcabnuDwXaNhSPYu+rqc692BeYNgHxzEJvKjtt+1ZVY/mzc9ouw9FoK39HqZ685Fmuax5hZxGvhr3gttvpabPNdXXeEVijxLCq1lAUq4ZuiMtKyGJHKCjeBo6ajcMRW3pQHa23lbWfX+p1guIcwdDzIiTCEK4Vh' \
			b'tL4jLL2WwtCNMHTXwHCSx5hZhGHhrzB0BQzdQhhqiWdhqKUsYAjfFIYx6mIYIvoMDDUdhaEDDBMerAfD2dV2JxjuIQw9WxkiDOFKYRiXzCMsvZbCcFwyb/01MJzkMWYWYVj4Kwx9AUO/EIZa4lkYaikLGMI3hWH0XAxDRJ+BoaajMMQK+JQH68Fwdr3bge96' \
			b'PQ1GFbkDcz4iF64UudEkZSfXUuSOJilbrHDNUitRPJdlJFdRXPgriodqcnyNhSkqvm8RyyMA7wQ6UOoU3sqWWXgrKwp4wzeFdyRyrSGokuRAbo5yLZWiHHaolEfrodycUH60KGeejwtZ1ZWg3MUlrAhLr4Uod+MSVlcsYc1SK1A+zW+MGlBe+gPlrp6i3GEF' \
			b'a3zfIpZHAN6BCK4CE0aUB585lAdW5ChX3wTlI5HroDywxoHcDOUapih3WL6a8mg9lJ+OojtilDfM84hyuFKUR5MywtJrKcpHk7IrTMpZaiXKL79GlBf+ivJmBuWwKMf3LWJ5BOAdi2gQwwzlypZZlCsrCpTDN0V5JHItlCtrHMjNUY6wgHKYk1MerYfyYzyL' \
			b'7oRyRXnLDI8ohytFeTyiAmHptRTl4xEVrjiiIkutRPkkvzFqRHnhryhvZ1COEyri+xaxPALwjkU0h1KnKFe2zKJcWVGgHL4pyiORa6FcWeNAbo5yhAWUY2FpyqP1UN5d9q2TdLVpt/drz3d2tDSf9RU/tsKqwBTqoNnOkvS11QKlQQxZph7sJirCL/puC9HB' \
			b'9aWmuuIDLi6a7BAnvTZYt+4Km12W3OQjL14+9DLN2CUWvNKfl6dCmfgZZQJDXkwC5evhtHjHIhrLdb5inSstfDJGyoDblR+OCYwqlAx8i2XsoRKWahmWKznlXl4NX5WRAmXqhj8uo2kHlQNTYMrMXOWQHykcCZTfnn9Z9/CNVI/zonl8dbHzbyztyQeW7BqY' \
			b'Hq4wqdvq8g8t8feB9ugbS/v0fSVmy8bfWMqhcNV3lojA3Us0kdjV+yLXm8r0Ennew4+GNekhafsg2Lv8cJh0Hluo6mFesNsdyLY7NNl2u5Tvdr5ftVMZ7w9TxpnzG34gj1g2K9/Twc/N5dtvUb75M5f7oL+J0w1VcpDzhsdeckTsIch7esjF1uSdWXb3eh2D' \
			b'vC7KfRjoTeS/Wd5xoVrc1hdPqQY3WPJyV/1yvwAH/Y76MssPhbzRR1CbZOE1UmsXrl3Znr5nA8YaOr+9HgPNZf0bqn/q4Vj5mlp7S133YM7aUiNAYSRajZzjeVed+aUD1D3s0MNIpP9bbQTQL/Rio7ujTj6ro2UdfarDB5S1AMFUF7dgkaEyaxvQy/e910PA' \
			b'XQxf6dnbTbr5eyLt48e6+lHd85E5ZhNJv/3hK4htN+re29uRaera90Gs/W4le25i4SbSze1ue1RSzkq9HSWd5dLtVtpnPllxM13ecoH45c0l3y2TfGr+tmJipwLdVPKXTK3NTaltKv3dXen3fuc2d2bOyvttSL5fuxfju5uYchog4AaS3y2U/H5Lkh/Fvr6t' \
			b'3sxNpP5IJT6V9qbcDrXLns1NpP2mku4XSvqwbUlvTpK+J5K+0Wj18CS9X9iPX7gUabmktydJ3xNJL5flHKmkD7cyYt3I/HiHawd8v67J0VQQ5v0YlW5uWby75QK8aHCddTDVP3ltqRxeSlw9SfFNVsDsmVFla+LbiEDu2WoXkoEHhCsR3OZ2DIZdZjPckQRf' \
			b'tg55G+bCQ5foRgS0T02FO1PO/I34nZkI1+9iUND2ZfyyFf2lonbpIv3bVNfrLK5fMM8pC18aWWOxN8KOnQ75/3XqXOKkS91vs1eyzpL1Batz+dB9+RQDUz/TOzEPSB2Ilt/FVOcJAfuAADf5vx4B7ogQ4BQB7hoE2OpCN3jGrZ1G5N2IpEcxb1R+802Q3byY' \
			b'dcUOpKFhURCec/0zHclOQ6lzr5WNL6ZklSyLGEJ9pVvxpE2dYSjzJ+VL10lz5xYXNQOslQ6ZIHBJ0c20+IyWggUsc+uxgCnIRTeIKkvhEra4KWdsZE63nDl2lj/7waM5iAc+BcTemFd+Ma+uaQvQCqzRBCxg7jqbiicqPfTau5tWhJQk/5/Xvxq2ns5dpASW' \
			b'atSZeg6fcqq7XFn2cxV/R+aLy/aib2OQd1Wrf+nA7kpxmW/SB3PzAdzmg7bZXd3bGZxd0UJfbn4w3QPq44igDSdB20zQuOb2z/iVSBrvV6/vWtJa+4A/KmjoxrYh92DVs9gR2Sex20zsmn0Xu0Zo3E+xa6Zid5cTAwcjebyga28N/vvVurKYtfsrZruYc1oi' \
			b'aqb4QOUysbvVeSbJbROpk7n3nQgep3zJiIFHHU341mOh/qbfdiRJSkRyL2ZF90Eqr5VErryDmPVMleAOZjo3VIS2uuAZWA/Wsh3Aib+T71E4tsLwt7z7N+f0dLbS49NxFlQrp7/ETWzEN/6iNR9IwScBed7RiQOTxn1pSH3VXptMW03+5E2TvdmWh07hsKji' \
			b'pCixAoeD28IMaDh5CSch8fe0KvxRbRhe5hUvo7vsQgTZaM2bRSl1CuYjlhhhAxZbYfez0Go3oJUPcVpELmH9mj+eFZj4CmFuCWGzJ24to40Uz+wfz1tcFiZ/Ql2XUsfKaBAaJweM4ZMomVnt6o9N5eeEDWbcaRxOBHN6IhifBkb+cgqYu7zA2UldFIc/ax5P' \
			b'3xqqeMoWf6x1PFnrDSt6/HkxpXf4yT3Tq5v8TeMkSV0SMvM2AV/WUWWxkrekPvxupIUZFSXGV+v/8awT3YXGvqTxZtIyFZVcTjaUkUWyMVThj1vs1FFcw+RvLs7Ur3h1ErdISfg73IIMcD9k+5eQ39S7lo9tqpJFYsKJ7fZqUoffSpKojOY2hKmrdnCB/vYg' \
			b'G6hlUsVravViitoq9dnwMltJ5foLtXNND9Gaa4B9pYwFRkY54wHa5Rf1/68I5VHVfIAf30Oh7PGKHI9vD/VC5VzTnb5W4lADa8qdrW5yhcH8dRFRwMPskS+SPrarHOqFypl0z6fVskwAUQlriOEcO9sqvfrcufwKBqbrIxYWImFJf8TyaqqDvVA5k6HEncqr' \
			b're7ogh2sPmJJddXBXqicyTjlTiW1q+7oAjOOeNDDMymHeqFyJmOem0nqcM0oKOXupVy1kIUtXVyr8wFE9SUvgTcTK/wlIrtF9swI4OVsaqurr8FeE2HhlaYzlya4NRnL7Bm3bLUfF7jV7Tm3umo/LnBrwUjlUIz0rI0WXPi2zPi/8LVL318rrdlIqIkjmi7h' \
			b'tQ4Hc4H7C0ZAB8N9Wx3OhQUEO58KukXuu+pwLnB/wZjqYLjfVYdzgft8rjWT7tVtghvjCD4aldljeDkQH6+iKwD44Mi0ioh/FIGYwsfbNXwgUtNpit1sTF8lFyL6SUSuCo7cV+nVeGhNOe4prEhyXKXwHuSD41FWrqx6P8g0c5uveYtr1WbWqSm1cnZJvn9L' \
			b'1kli2tpoTpoLzxQ6FhRdBdTwtJrkPFBR3pz/P09SyHM=' 

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
	def expr_comma_1       (self, expr_comma, COMMA, expr):                  return AST.flatcat (',', expr_comma, expr)
	def expr_comma_2       (self, expr):                                     return expr

	# def expr_colon_1       (self, expr_or_empty1, COLON1, expr_or_empty2, COLON2, expr_or_empty3):  return _expr_colon (expr_or_empty1, expr_or_empty2, expr_or_empty3)
	# def expr_colon_2       (self, expr_or_empty1, COLON, expr_or_empty2):                           return _expr_colon (expr_or_empty1, expr_or_empty2)
	# def expr_colon_3       (self, expr):                                                            return expr

	def expr               (self, expr_eq):                                        return expr_eq

	def expr_eq_1          (self, expr_lambda1, EQ, expr_lambda2):                 return AST ('=', '=', expr_lambda1, expr_lambda2)
	def expr_eq_2          (self, expr_lambda):                                    return expr_lambda

	def expr_lambda_1      (self, expr_var, expr_commas, COLON, expr):             return _expr_lambda (expr_commas, expr) if expr_var.is_var_lambda else _raise (SyntaxError ())
	def expr_lambda_2      (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr):                       return _expr_lambda (expr_paren.strip (), expr)
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
