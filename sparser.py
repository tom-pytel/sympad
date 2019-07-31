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

#...............................................................................................
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

def _expr_func_func (FUNC, expr_neg_func):
	func = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC

	return _expr_func (2, 'func', func, expr_neg_func)

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
			b'eJztXWuP3LaS/TMLZAZQAy2K1GO+2YmTa6zt5NpOsIuBYTiOcxFsXms7+8DF/vetqlN8Sj2t7umZ6ReG0xLJUpEs1qHIIileXH/xLx9+/+mL6osfHr2k32dPvn5Nl+8evXzy4hndPP3mxbcvn7z98vuXz/6dvF+/fPSlXmq9Gro+fvLN2y8fvXrySu+fP3qt' \
			b'd4/j7Q/x9jvcCldO5fnTF9/Ls8TvXzng1WvOzKvvH9Pvi++fc0ZevP6G8/f0uUTI799fMpdnL/jnW479+vsXnL3HUpQvv33+/JFcn337wpfppU/2pU+Ob14+/eZvzOrR8+/o96vHz149e/Tqb3T75MVXWhi+exxvf4i3Wpgnf+efZ6+eaLCXB3N7jQxRBpjy' \
			b'+aPvXr3+lpN7LcV88m9fPvPRLNWvnv7w9Ctm8+VX374WYcjjT19IEt89E1E9/Zp+hAtJiZ96/+7jh89v//j49qcff/30+d1HCvrwP39+fPvprz8/BM/vH/7x9ue/fn8fI3/0t7+9+/z2/R+/pt6Pf/x34f3k/e/fffrw6dP73Ptn7vW+dz/G28+fQ15+fvf+' \
			b's7//M6aUZ+83f/vrL+H2l98//yPk669f3/7yW0j49/jAT7/8l7/9/OFjEvzzz/7+x4/v3v/Hh8+JcEIB/vr46/+madBNIopQnJ9+yoocc/jhP0N5KJFQzF8+vP8QPFRhv0emf376/If3/Vesvl/f/fbjT++8L7ANyf7x22/vMs+nL95U1xcLW1fWXFa4afim' \
			b'qRZWrnV1YSrTVou6avjmMoRKWAxY9HxTN/hxhmLdZRpU2zSIb/nBJX4sIuiOeAlJzwnXThOmQB+qYSFgYZZyZ6oL8hCt1SjOAgph+KepGnupXvLJnZWiUtSiucwC4Gv8cxRvfRDf0p2Rf9P5R5mpJKvhyAPlTgPhbyn/jeR/6QOoDHI3EK0U3dT4sVw2ZR6D' \
			b'WIwxlG+53ujfVQ2xgBwt3zDFgB+LaqI7ErGkRnJnObKMzKUPaVNfp1cO4mc7qhAu5HCZeLkySEB1Ht7kXjv29nmQG3ntMg1aGMioVu2i9GrIoMYtk5EQWIjMm59WAh8cvQsjsnH0Dx3mBy4RtJBSUwYuzLKqu4orq62clVIyU9TrNAHDhxR/Fh1VY063ICjR' \
			b'HRV/0VfW+ixR2Qcpp1U8cAmpql2KCorzwSGAa45D2hhSI6SLIQYhvQ8hfRQt7/CTAKNT9W5a/AgmwIl8fMt3zkdeqpd8PgJpOPzYIZTdB7llGsS3LJgGP1Rvl5fxlmkoj5JjfYQyWIukCAUSodrDoDDgRfITNZKmpfFNGsgoTEKi10qdNR6ppCS1QGeA1jmJ' \
			b'ZEWDzNNgDSC/pNvjh7TyUv2ERMkbN2edMFavA2xJyATuoDZcBuifTXSm9QWjwAsboSneJnAlr0X56Vlj/F2rN3W4EaK2qi/pnXC9rEgnKQkCH8mcUCPNINWjI0dEy7Zq66o1Vd9WfVf1fdUP1bCshroaSLg955lTrrleCa9UpdTWESEpcNtUra1aV7XEpKva' \
			b'vuooqqu6nrFIjVRfVz1Vlqnw2qCC10vyLMm3pGpZOm5xWP+bqndVRw8sGXgkewKY6ypHgqRkKDddNRCa6J3QMKYsKV5L0uB2lDRwaKqBuJN8SdCUBrWvFWXqTXVBnkt6MZIIuAZNi0sjsuEGjL0NaBr1OQjuwuEZyezlSQvRtSqJFpKiorIfGnZBpZbQHlRt' \
			b'A2IJZeyJMEkoJy5EKg5UsT95SQyQxCDgvBigTYNRVWlEQCjSuDAoQ8h9mXXKMUmPErG1onrYCTdtRxyy7JBl0emLXvNdS3vBTT0xpfcPsRoqao5Pqm5rbSIGCAhNQtf5VkDkhkxS3kJedp2RTLapSG+pB9fc5z9t9FLrL+/JjmrNVh0lUVedqdqh6k5L1UkQ' \
			b'7iwICKI9CwKC6M6C4LdA26Pdx8XgZdCjR1hbfTHjVdrgVdrg7X8hGZW+ptWrU3J0Kzvhtf9vioseo4fedxxQLCelGGjw7yszVN3hvhUvnFapQ4fIodrdoOMD7eYhctBusNXxgQikJ0W0+1Icypvdx0xBoWwb8wY92p8cooZtn+SQHlxy81PvUTbRHA2AYsgg' \
			b'Rw1qAmj9UKTTRkgbJx1TuJPvA3LhYUihy2kVncpKZT6FsrIFzKi9h6v5hCqZSmVOHOKtYJvteKcuCXviEmDjrbQDVKwTa+7ZWmvUVmlgqzwxCYg91tzagnqdzQu8CdMqbJ81alml69GMia4vBDNHUZL+SErCFnrRtVq79WqeqHU2UOexaowPzFIHAZ30BQ63' \
			b'2Ndsfz/oEvC8gVQchmcTE41vMBspa3K4nW4tHujUaoQHu9pXKYwPrVooOlgoWgxq2hYXfek1kjYbqBgFhyKxzjerku18lOsgo3z2avCz3XLdZVaGNliHDKxDBtYhw7IfEGqN1rD2OqXemtjrwgsXfa/TeO32+2cZu+iBI2tRZ9qcWjSQe5VTq+i1/d7ljbA2' \
			b'7F3V0mtvudw18tnsp6Y2A7OagTVNGgBvQeLVaAzvS6y5aU7J0sCmlQavNCl/C3Gcp1h1NYERcVjIqMOll4vpITEqa4OBWcOvk0aDHYLzdxwYjBYlTIRyV7HRrqJBH5HHQCe3nkN6wwa94RMb+LJGNNCIBj0SRWajHUuDHiVdTg+Z19x3PjWFaB1UAHrRdtCE' \
			b'Bi34oUxMX/NIpjmckYwMYZojsgzxSMvoeKjBeKjBeIguvoPYJR6LlsdgKS2PCwzmgRtMtsrrb9Cule9bCUsqJ/oWVvsW1g+N8W618m61eKlafZvaE5ncMsBtPWiDDq83CbQa3EBKh4NupxnOOj6UXwtVs1A1q0Nvq2Nuu2fDEVZap0rr/GsXSutEafmXVNEp' \
			b'kBxK51A6d1ovJmkvTqzMrLQORsBWdaCFDrTQAbpQ3wxa3oKwU8LukG2h11zGDmXsBBKwVuuyayldau7jAveQTI+neiXsD14Mw4GXYDjsErASDbreb6kL/pbyvllWvO2MGiSkjzaFcyQJ8v6IpWyRwFS6LzdaL2Q/zSYX10pBey8SaeEYCGIZIfnxWjPLq+F4' \
			b'mSGbnTSvsmdpSRnk0nBxuDycDZ4D4gkgnubh3WGG/Lw1hwvOrRmvS+VFqbzulNeDsUh5ZwrvJ+G1i7xwkdcJ8rI8XtzJKzt5HSTvGuPWl9dCsmB4loI7FTzHwNMQbGdgIwOvjeXtECxM3gHD+ea1kcNAAsROWd4WiG2mvP+Sa2DheJ8rFYn3u1LLvqAKXVBj' \
			b'zvtQZUeh7KelOAqmelx0skGRyGQHdSW7srk2FyyeBctH9kFTHhY9P02BpGSLgbc4MmfZGlrJ1lzjs8BbGCnjnIOOtyk3yoj3Lfa825X/2S/bIYlw4Ick35Xs+uQNpy1vM5fdwBRfY6svbxulIN6eydt3mT+z4H2T/ASFtVxq3r/KT/PuW/Lz3uqBd2guuQDk' \
			b'uCzYPr7gvet9i83RxGLgbZfMjgXJ23Hp33HCwxvuCLLOttBUI2rvdDMPzD7GqL7GlSACkxS5N2lwE5WYZItXbsQ4FDogXd7bCsyWIckmBtH1YBSkCkPTwarfRO1nJRIA5KAFEDqAYUlllAaingAGl98koBgKMPB2WjcBCuIn26ELcPCCVV4ZKjveiY63UK0C' \
			b'jIDFJoBpFDQuAQ7F8apqDx6eDRQAER1PYvF0UwYmavYCaOSeQNMLZLC/vPeQ6ZO/mfDpA3j6DD6BTQGjfuIvwCoJAsD6ADFW8lYwhuiIs16QFjjleAOx4owxFvAlMQXGUO6IM2U6KPUqxPVK54xQtcArMAcZAHO9oM4zjdir/tleiQzs8oqbo6G7EtmS9lwx' \
			b'1Ekb6Gr+T3o5Z4zeNUbvFZtSuIBO9fViTmWAdtgoX4e3Gk+K1pmbC9T4muPbFKpNdCVcb3DdMgFuk3NR9DYBvkys+OVGoMkR3ADC8izY5ij2YpnCscYVSPaiSbAcMje4G6Gs+WMwNyWala3HM16jCeetMN0kmK4TWPcPD+iVaG5uBeijBbMYBDyYW5gHtJOq' \
			b'HVSJFyTXpnQzkSwcgWS+TZCcMSuRPEouknoYl+G9KAS3S6bo63osK13EsqTcRcYFkJV+EsiIK4GskolAjtlbB2RQOU0zB7LKCEAWsozzaiBPANhOvZT3Gb1n6I6h28gHavx7GL4Ut03AbVO6ubiNb+A6fwNnzErcjpKLpAG3RThev3WzArRKlIAWL+DAtQCt' \
			b'0k+CFnElaFUsCWhD3taBFlTOIM0ctCogBS3evgnnjUDrTgi0R92B5ocicOFLgdsF4HalmwvcLgK3y4GbMiuBO0oukgbgFuEK3C4Al289bJUkgW0H2CZsC+TqI5PIRVyJXJVLgtzAfR1yQeUM0syRqxJS5HZAbuS8Vb+5PSP4OBA8VPJVQ0UwfCmCh4DgkZuL' \
			b'4CEieMgRnDIrETyVYsitIrgIVwQPEcFDRLCSJAgegOCEbYFgfWQSwYgrEaxySRAcuK9DMKicQZo5glVCiuABCI6ct0Jwd0bwUSCYK2wZEKy+BMESKQhGXOpmIlg4AsEmn6jJmBUIHicXST2Cy3AgmO8UwSbarjxJRLAk2mVscwT7R6YQrHEFgr1cIoIj9zUI' \
			b'VipnkGaGYC8hIFjIMs5bIbg/26OPDMqG6yxAGT6CssEcq1yWIAGgTenmAjpasUxuxcqYlYAeJZdRB0wX4YrpaMXiW49pJUkwDRtWyrbAtD4yiWnElZhW0SSYDtzXYRpUTtPMMa1CUkzDjJVw3grTwxnTR4bpTj7u7jENH2O6A6Y7YDoMlEGRurmYjgNlkw+U' \
			b'M2YlpvO0WOYZeQB1kScFdRwsmzhY9iQJqDFYTtkWoNZHJkGNuBLUKpsE1IH7OlCDyuGz+wWoVUoKagyWE85bgbpenlF9ZKiWZWoB1fAxqrG0A19pBwlQ3ZduLqrjGg+TL/LImJWoHiWXUQdQF+EK6rjww8SVH54kATUWf6RsC1DrI5OgRlwJahVNAurAfR2o' \
			b'QeUM0sxBrUJSUGMpSMJ5O1Cfl2wdG6gHrp4Aavh6XBjUA0AdLGJm5OaCOlrETG4Ry5iVoJ5KMVIHUBfhCupoFDPRKOZJElDDKJayLUCtj0yCGnElqFU0CagD93WgBpUzSDMHtQpJQQ2jWMJ5O1Cf13gdGai5YqJ5TH39gFNQan8YShOMZKBI3UxQN9FI1uRG' \
			b'soxZAepxchm1B3UZDlA30U7WRDuZJ4mgbmAnS9nmoPaPTIFa4wpQe9FEUEfua0CtVHrCUQ5qLySAuoGdLOG8HaibHNTNYeM6+artGd5cIBvnr0SgHMCnfNhKT8iSiSwbJrJs6eZOZNk4kWXziayUWTmRNUouow5zWUW4zmXZOJdlBeF+FbvMaSlpMqdlMaeV' \
			b'sC/mtPSRyTktxJVzWiqiZE4rBK6b0wKVM0gzn9NSYemclsWcVuS8HdJvWA1WH+G81hxUl7uJNkX2HaGaj2RiFWGg3twrdxV2/6BXDl8yv9VpPLrkrnRb7ETip1JwSzXE/1G/fJRmTDx0yotwj25sY+pclS0S4/pbFqvElrpMzGdi1C9XxhHYzDV2zRFdds1V' \
			b'RPnuJg5a1zF3ssep8xnNe+bg6nvmXKmc4WqhJvKQmymQD3SVtTcEdgdQuxVrtPfq9b28q/Xax/z25qqKewpZWRDAg+4Wg+4Wg+42ILwt3dxBdxsB3hYANwm3Et2j9FLXJgtBy2zxAm45dtG0cezdRpArVTL2bjH2DhxGGNdHJsfemk4BcJVQMvYO3NdBHFQO' \
			b'x/YWCFdRKcJb4Dpy3u7lPbmmbK9Afh57bzb27rkOwtgbPuwCl7E3rORNsJKDInVzx97RSt7kVvKMWTn2HiWXUYexdxGuY+9oJW+ildyTJGNvWMlTtsXYWx+ZHHsjrhx7q2iSsXfgvm7sDSpnkGY+9lYh6dgbVvKE83agnlxmtnNQ518iOEP77qE9yGnCHtrw' \
			b'9bgwtGErb4KtvBm5udCOtvIB09qs0nyq01IRLtz4m1Vjk/k41SwHAeFFuCI8msybaDL3JAnCYTJP2RYI10cmEY64EuEqoQThgfs6hIPKGaSZI1zrRxEOk3nCeTuEn5ehHRm2We5xW7T6CNsy4IYPtaPYRljqZmJb+ALbfJu8tjNmBajHyWXUHtRlOEDNdwpq' \
			b'vlVQe5IIakm3y9jmoPaPTIFa4wpQe9FEUEfua0CtVM4gzQzUXkgAtZBlnLcD9eQ6tF2vDt+t5SyCNwXu1Md37gios0F6a4A2LMYAUPgSk5gN+yURl7q50IzmMJvvlxzBcZRETCtgsQhXLJZ7JKEea7/j45lMQg9xJfS06An0Yl5ugB0o/Id8EswhwmMOmyEj' \
			b'y802Q5rJ1WFnrO0J1hyPLgLW4EuxFmzPiEvdXKy5iDV3M9ZGScS0AtaKcMWam8Cam4E1ZTKJNcSVWNOiJ1iLebkBa6CYwBoiPNYcsBZYboi1yUVbZ6ztCda6ysa10upLsRZWSSMudXOxFldJ2+5mrI2SiGkFrBXhirVuAmvdDKwpk0msIa7EmhY9wVrMyw1Y' \
			b'A8UE1hDhsYbVz5HlhlibXEt1pDsMj3YsOLCEAyThSyEZLDx25OZCMlp4bL4aMmNWwnMqxZBbhWcRrvAcqslPc3iiZBAIy07gWsBV6SfhirgSriqWBK4hb+tGgKByBmnmqFUBKWph1kk4b4ba5ozag0ctyzYuelRfgloXljsiLnUzUevickeXL3fMmBWoHScX' \
			b'ST1qy3Cg1i2nUeuJImodVjsGrjlqPf0UajWuQK0XS0RtzNsa1CqVM0gzQ60XEFDrsNQx4bwZas+fwToC1NaVi3ZX9aWoDRZXxKVuLmqjxdXlFteMWYna1S6itghX1NYrUKtECWphcA1cC9Qq/SRqEVeiVsWSoDbkbR1qQeUM0sxRqwJS1MLamnDeDLWn9B2s' \
			b'o0WtYcEG1MKXojZs10dc6uaiNm7Xd/l2/YxZidpRcpE0oLYIV9Su+OKkJ0pQi936gWuBWqWfRC3iStSqWBLUhmTXoRZUPs0ctSogRS3WISacN0Ntu+p8gXRxYrv36453+xlZovGHGgi0lwW8+x0tR54Bczn4wMyEe78N5LtZ5yO0OD1DbVjFQQku2LJAk7ot' \
			b'1iy73JiVcRsdptDJgQrjdF1i2irDeTWjlcahtG75xkHpksahQ+PgGRc7EUSK7LcoM2Ry47kMyqpsNFRo+SpmDb2p1WClYT69CMwf2iC5yJoPPrvBy1KbEJjGoniKJoQH4MsriZPf/kp2Nzi5UFPiOmlJuur6zs8p2ZNDSuo1eG1usCP31erDSljo+3NOyT6d' \
			b'UcJS2eScklzfbzirhLJ092rLZ2kt90V5N1HcOUq7f6fr1Ol3FfdBe3d7wo506wwa3WFae80dKLA7AAXmc7PuTonNdO/nDhX5gI6KYllvd1wUyWhSicdjj9srcbdLJW4fsCWmeCpAVGYjG9MOQ6m7O1BqltiDtNAYYS2DcvtRVqnk9fx+BlXbrk7yozrZYu3F' \
			b'ffaV6xnKbu6o6zH/g3S3OdyvTrbXRAUvvip3xy032wtubr3b9YruVnRHqJKpQ2LlCCJzT91pbxfaUXPO1i6K45PB77WDPXdkuH+dbFhe9H+nzTl6cbXYve6v412LWGZ0vqnSrigx0famur4HewefYovWHAdPb6bm9zVu5Hdwv03Xez9UOh6BE9aZ1rLxoZyr' \
			b'n6XO9zJulPyRvLfoctv7UVw55lx1t7tb9Z2yu2+qwiyC9phUmQLjV6t5HmLRmbtV6YnP0G/cKhsuA68421q93Tz1JoXaiSk6PRV8S/WeM700Na20iYovH6il7mbvHtjWNl3LvlO7C/Xu3KatNnetNzKUqJpvr97tTPXud6TeQbeX99X52FS1j1OtU5Vmedxb' \
			b'R2RDlb6lOncz1XnYtTrXZ3V+OHVujlWd+5l965krZuarszmr88Opsz1WdR7uZai4lQXvvqfEzaZWu4aXse3LcHB749y9zoLz8rUN1nBU/+RFjU6Oz16eVfXATRY701FeLLkHKzWooq8ILqKd9f3Y3NrM7HZHarpqpeu2FrcDV1sWyqLuU2vbnTWzfM7xLq1s' \
			b'G/cIqCx3oMjmxpbWlcu676m9Xbs0e86EXqNKvNwbRcay9+XaNlhoysXR99VfWLPaecaaT/4ot3yRXYox6jc0VwRoaZrvZB7vrNH3qtG1/K/X6PqwNXpQja5v1mhbXetePOe1uBH9bURzg9rWqpj53rVmWn/aYtNJ77i+9RPubSUCGmLlcsW2WqM4vyGryT5b' \
			b'KtPFfVXylpsQIYsnFUvbyOvIzS5qhkQrvaLazSu633JXQqIQAWvZZiKopbSpsrYayXo3RyxuLBkbhNPOF46dlI/dCxlNgdrLyWP01rLq5stqsm1Hqz6/SZ8j03VbQEey9j3m5a1lbuR/ukFtEbdZIzqngtZsjCxrzh+5Upu8+eunqvJhhv4rNwVvOXa66QW9' \
			b'erx0oyZMv33loIuHGs5P7rPdesxzw4t15dC9aa+o/yHaNJy1ab42sW7snXUoUSfeNLy8f3Uy9mohdXa14GoyV4uedYs6kGfdmq9b9Z7rVi1Z3Bfdqse69YA28P1WL55U21fb9kO/DFmXzP7q0o7mUObo0+ikt3m6Ze9Rtzq7pWrJdPautEt2A0731dn+U/sD' \
			b'1PKGbHxgGvkSvduHqbyHUr316sa6dQhTdWlztpvpue2aNFtdkyy7GrJkcSPcyVfpHYfzEbX9m0u6u1jo55bxWRwjHw8J25BIlnyAK2/zpzxTdmUE3WY7i3rH3BdmLRtTjf7kySZ70pTf38F3c4ov5siGP15d7Kfs/Mdo8KEYPv2mwh8FNLyMKLhG9kghEptd' \
			b'2RZRcxQ/TPy5FeQ0sBtV8mhn5XH0YR/Jpv+M1sqsEpAn/9gwnvkpjYxCsubmZG3ys0M35o6rLeSQ2pbJPzbfr4pzYlinq+SyTXPJe9QGyevoa0s4GiH7htLNB8fkH03ibyV1Vfw8Et/7zyHVqwubfbaI2+Rl8lmipoqfH2rTTw694TYcf50YnFv85IGpa0d/' \
			b'Y5qE1apHQ2At/ybJQPacSL67B/3oqi3/JId9mcPbacVYJab1YYYuzNKBofJ//NJNPYUbRn9TNKueGJEUDESUwz1UNgtv906yXy/vWhVu2zrM0gjuT92pE/N54drtmEHu9X3oTVvdgUP+zcG8XuYpEPc+1HEuTJWGbOm4Z397LisdKmJNZ842a+B6ozp5+QWV' \
			b'4gHTakejnxtieZQzHdHFCBTKHpd28RjzwBzqYU1Xd61yQdgbqpitbuP8OHodIQp4OL3kWYrGZowDc6iHUZ95XAPzdA3y3kDjpqRoqtT1uXe+82ac9YSFTUZE0h+ZajbVoTnUw6iH/6CqaasHcrA5LY9MKV11aA71MBo+PKhSttUDOQjjyMYi/MY4MId6GA1F' \
			b'bqeUw7rBSTtDNy2qfUeOK3M6oh1WPQTZjOzZK7Rzh+KZ0ruVYjLVzY6o19LMcSmfKZ6Q1mjcsWfSstV+OEir3XNptdV+OEhrxlBjn43ffODFDIfp5/g/87Htn58kgsQPfLqBp/v33UHQM4Yqey1oW+29wwT6nc+a3LGgXbX3DoKeMc7Za0G31d47CJq/t8tr' \
			b'Rjr1N96Pvj1/6BES4TDe3qcVRD21tDZqeYjkwJ/4qvlTMnWLHjB/bGyCsqsSB8JuRMg1wMR9lbq61Qf6ZJ0NW5s1eJCTeoNajGq5a2Rutc6XaZVLq3pYKPmbENitI5WLadkBK7pYHQZdtlLzXJIw5uK8ufx/pcVBug=='

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

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY - {AST.Func.NOREMAP, AST.Func.NOEVAL})))})"
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
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
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
	def expr_commas_3      (self):                                                 return AST (',', ())
	def expr_comma_1       (self, expr_comma, COMMA, expr):                        return AST.flatcat (',', expr_comma, expr)
	def expr_comma_2       (self, expr):                                           return expr

	def expr               (self, expr_eq):                                        return expr_eq

	def expr_eq_1          (self, expr_lambda1, EQ, expr_lambda2):                 return AST ('=', '=', expr_lambda1, expr_lambda2)
	def expr_eq_2          (self, expr_lambda):                                    return expr_lambda

	def expr_lambda_1      (self, expr_var, expr_commas, COLON, expr_eq):
		if expr_var.is_var_lambda:
			return _expr_lambda (expr_commas, expr_eq)
		else:
			raise SyntaxError ()

	def expr_lambda_2      (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr_eq):                    return _expr_lambda (expr_paren.strip (), expr_eq)
	def expr_mapsto_2      (self, expr_piece):                                     return expr_piece

	def expr_piece_1       (self, expr_ineq, IF, expr, ELSE, expr_lambda):
		return \
				AST ('piece', ((expr_ineq, expr),) + expr_lambda.piece) \
				if expr_lambda.is_piece else \
				AST ('piece', ((expr_ineq, expr), (expr_lambda, True)))

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

	def expr_func_1        (self, SQRT, expr_neg_func):                            return _expr_func (1, 'sqrt', expr_neg_func)
	def expr_func_2        (self, SQRT, BRACKL, expr, BRACKR, expr_neg_func):      return _expr_func (1, 'sqrt', expr_neg_func, expr)
	def expr_func_3        (self, LN, expr_neg_func):                              return _expr_func (1, 'log', expr_neg_func)
	def expr_func_4        (self, LOG, expr_neg_func):                             return _expr_func (1, 'log', expr_neg_func)
	def expr_func_5        (self, LOG, expr_sub, expr_neg_func):                   return _expr_func (1, 'log', expr_neg_func, expr_sub)
	def expr_func_6        (self, FUNC, expr_neg_func):                            return _expr_func_func (FUNC, expr_neg_func)
	def expr_func_7        (self, FUNC, expr_super, expr_neg_func):
		func = _FUNC_name (FUNC)

		return \
				AST ('^', _expr_func_func (FUNC, expr_neg_func), expr_super) \
				if expr_super.remove_curlys () != AST.NegOne or not AST ('func', func, ()).is_trigh_func_noninv else \
				_expr_func_func (f'a{func}', expr_neg_func)

	def expr_func_8        (self, expr_pow):                                       return expr_pow

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

	def expr_cases_1       (self, BEG_CASES, expr_casess, END_CASES):              return AST ('piece', expr_casess) # translate this on the fly?
	def expr_cases_2       (self, expr_mat):                                       return expr_mat
	def expr_casess_1      (self, expr_casessp, DBLSLASH):                         return expr_casessp
	def expr_casess_2      (self, expr_casessp):                                   return expr_casessp
	def expr_casessp_1     (self, expr_casessp, DBLSLASH, expr_casessc):           return expr_casessp + (expr_casessc,)
	def expr_casessp_2     (self, expr_casessc):                                   return (expr_casessc,)
	def expr_casessc_1     (self, expr1, AMP, expr2):                              return (expr1, expr2)
	def expr_casessc_2     (self, expr, AMP):                                      return (expr, True)

	def expr_mat_1         (self, LEFT, BRACKL, BEG_MAT, expr_mat_rows, END_MAT, RIGHT, BRACKR):  return _expr_mat (expr_mat_rows) # translate these on the fly?
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

	def expr_num           (self, NUM):                                            return AST ('#', NUM.text) if NUM.grp [0] or NUM.grp [2] else AST ('#', NUM.grp [1])
	def expr_var           (self, VAR):
		var = \
				'partial' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_')) \
				if VAR.grp [0] else \
				'd' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_')) \
				if VAR.grp [1] else \
				self._VAR_TEX_XLAT [VAR.grp [3]] \
				if VAR.grp [3] in self._VAR_TEX_XLAT else \
				AST.Var.ANY2PY.get (VAR.grp [3].replace (' ', ''), VAR.grp [3].replace ('\\_', '_'))

		return AST ('@', var + '_prime' * len (VAR.grp [4]))

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
		'CARET1'             : 'CARET',
		'SUB1'               : 'SUB',
		'FRAC2'              : 'FRAC',
		'FRAC1'              : 'FRAC',
		'expr_super'         : 'CARET',
		'caret_or_doublestar': 'CARET',
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
