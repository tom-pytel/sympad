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

	return ast.commas if ast.is_comma else (ast,)

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
		for var in lhs.commas:
			if not var.is_var:
				break
		else:
			return AST ('lamb', expr, lhs.commas)

	raise SyntaxError ('invalid lambda function')

def _expr_mul_imp (lhs, rhs, user_funcs = {}):
	last      = lhs.muls [-1] if lhs.is_mul else lhs
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
		return AST ('*', lhs.muls [:-1] + (ast,)) if lhs.is_mul else ast

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

		ns = ast.denom.muls if ast.denom.is_mul else (ast.denom,)
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
						tail.insert (0, AST ('diff', ast.muls [i + 1] if i == end - 2 else AST ('*', ast.muls [i + 1 : end]), diff.dvs))

					else:
						continue

					end = i

		if tail:
			tail = tail [0] if len (tail) == 1 else AST ('*', tuple (tail))

			return tail if end == 0 else AST.flatcat ('*', ast.muls [0], tail) if end == 1 else AST.flatcat ('*', AST ('*', ast.muls [:end]), tail)

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
		ast2, neg = ast.muls [-1].strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			return \
					(AST ('*', ast.muls [:-1] + (neg (ast2),)), dv) \
					if ast2 else \
					(neg (AST ('*', ast.muls [:-1])), dv) \
					if len (ast.muls) > 2 else \
					(neg (ast.muls [0]), dv)

	elif ast.is_add:
		ast2, neg = ast.adds [-1].strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('+', ast.adds [:-1] + (neg (ast2),)), dv

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

def _expr_func (iparm, *args, strip = 0): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
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
	elif not ast.commas: # empty {}?
		return AST.VarNull

	c = sum (bool (c.is_vec) for c in ast.commas)

	if c == len (ast.commas) and len (set (len (c.vec) for c in ast.commas)) == 1:
		return \
				AST ('mat', tuple (c.vec for c in ast.commas)) \
				if len (ast.commas [0].vec) > 1 else \
				AST ('vec', tuple (c.vec [0] for c in ast.commas))

	return AST ('vec', ast.commas) # raise SyntaxError ('invalid matrix syntax')

#...............................................................................................
class Parser (lalr1.Parser):
	def __init__ (self):
		self.TOKENS_LONG.update ([(v, self.TOKENS [v]) for v in self.TOKENS_QUICK])

		lalr1.Parser.__init__ (self)

	def set_quick (self, yes = True):
		self.TOKENS.update (self.TOKENS_QUICK if yes else self.TOKENS_LONG)

		self.set_tokens (self.TOKENS)

	_USER_FUNCS = set () # set or dict of variable names to be translated into 'func' ASTs if variable followed by parentheses

	def set_user_funcs  (self, user_funcs):
		self._USER_FUNCS = user_funcs

	_PARSER_TABLES = \
			b'eJztXftv3EaS/mcOiARwALIffOg3J3GyxtpO1naCOwiG4TjOIti8znb27rDY//2q6qt+sMmZ4Yyk0YwkqDVkP1hdXV1fs7v6wbPLz/7j/W8/flZ99v2jF/T79PFXr+jy7aMXj58/pZsnXz//5sXjN1989+Lpf5H3qxePvtBLo1dD188ff/3mi0cvH7/U+2eP' \
			b'Xund5+n2+3T7LW6FKufy7Mnz7+RZovdXDnj5ipl5+d3n9Pv8u2fMyPNXXzN/T55JhPz+7QVTefoNR3z13XPm7HMpxRffPHv2SK5Pv3keivMi5Pgi5MQ3L558/Rem8ujZt/T75edPXz599PIvdPv4+ZdaDr77PN1+n261HI//xj9PXz7W4CAKpvYKDBEDnPLZ' \
			b'o29fvvqGs3slJXz8n188DdEs0C+ffP/kSybzxZffvBI5yONPnksW3z4VKT35in6ECgmIn3r39sP7T29+//Dmxx9++fjp7QcKev+/f3x48/HPP95Hz2/v//7mpz9/e5cifwi3v7799Obd77/k3g+//0/h/Rj8795+fP/x47ux94+xN/je/pBuP32KvPz09t2n' \
			b'cP9HymnM3q/h9pef4+3Pv336e+Trz1/e/PxrzPi39MCPP/8z3H56/yEL/umncP/Dh7fv/vH+UyacWIA/P/zyf3kedJOJIhbnxx9HRU4cvv/vWB7KJBbz5/fv3kcPVdhviegfHz/9Hnz/TNX3y9tff/jxbfBFsjHb33/99e3I8/Gz19Xl2co1lWvOK9wYvrHV' \
			b'ysm1qc5MZXy1aiq6N/48hkpYClj1fNNY/HgKaBAXghqXB/EtP1jjx7lz9RItSdJzxk3I2NbnIVTDYsDK1HJnqjPyWFM5jTKUDoUw/GMra8/VSz65c1JUCTgfBcBnw3MU70IQ39KdkX/ThkeFBmer4eCBuNNA+Fvi34rghhBAZZC7gdJK0U2DH9dRiBJPQSzG' \
			b'FMq3XG/07ytL5YeAHd9wigE/DsF0RyKW3EjuLEeWEQrLIW3u6/TKQfxsRxXChQTj6uXKIAHV43A79fbjIDfxuhGNlYFQGlUnZgOFbhq55WRUapYa03YpQQhO3pURYXj6b0X2HWs3glZSTFLmM1NXDYmXmG0rzyxXLK6mO1+fgPHim2XpqN7G6VakI3RHxV/1' \
			b'lbOBJeJtkHI6BQCXkOrW5TCguBAcA7iqOMSnkAYhbQoxCOlCCCmgqHWHnwwJneqzbfEjmo/nbCu3fOdD5Ll6yRcikIfHj+tj2WPQkAfxLQvG4ofq7fw83XIa4lE41keIwUYkZQdEqPZYBhJokfxEjaQtsaEN6881DECMXid1ZgM0mWHBygCt80ZUfQgYy4M1' \
			b'gPySb4+flbZEfGvAKrdfnRBWr0djQkImNEe1EbiIvohiq860oWAUeOaaWGLxmkiVvE4qgRSRZBDuQlATb4RWWzXn9BK4rLmVpywIHCRzQo0VnfPEYeV91dS+auuqbareV31b9V3V91U/VENdDQ0zTJLhnBuuV8IrVSk1bpSKFLg1VWur1lUtEWmrtqs6X3UU' \
			b'S3n1XMy+rnoqvqnwnqD2pKnJX1NATSE1lN+wEvau6vqqGxh4JHsCmCeYdZUnWRI3bTV09A5jQDlH7R6JgltNUr/BVAOViYRLUqYMiNGK2HldnZHnnF6DVH6uPtPiYkUw3Dax1yKNVZ+H1M48/MLp+f2VoPcqBg8xtSLSM+jWGRVZQnukag0S4+JUkn17ryVI' \
			b'ZYES9vdbDL2qyiDKMUCPhkaVxEo0yjMtCQoQWS/57jnIv5amE2AeroWaNh8OLHuwLNV51ivfjWg+N+9ElN45RGaoqAm+PxXbtJAShNShJejaAH4RGjgkxiIj18rFSKq5MK+oAZfcpb/HoKXmXsrfmaqjKiP6NHhoqrav2uFeScE9SIGk4B+kQFJoH6Rw1uIl' \
			b'2OFi0PT3DXp/Tt/BeF1ahFqDHqNwKR1Kq9eQHP5O+gFH/l446zE46Abw7lEmL/3ewVWD12qMlXaiL8Azr6Mjj6GTR4V79H7OvPblEDloR9dp918e7U3V26MoCzGGWnM+MYbKOhL2IEbXZewRG/RsXR8Liz1qGooemOOYAfC1od9nO4W3wl475v5+d6e45LBA' \
			b'0OUelZsKSgW+8wVlo5FRKwlX8H2p3l7U+v7CmvgzsHvdazG4+1x8NnMK9qlM96lxZ7umUcOegWHvPhVfLJfmyrbGy5Ht/HWcd2BLplEbJF3vxqji8kwgcvrF6O9CMdiELSrWaJcdfXzT6CyZQc+9wVjP1NrB7+SpEy3zJRuoT5d9tqqjVYDhZTr79hpTdLIm' \
			b'hVvl1uKBDmk6NbbEyoQBo9VxfYu6bh2exaCl1fcbT7TDoMPKfxLi6vQV5YX10bjVo+s2ntQZwtyvXK+Tk8FHe4qBPcXAnmJY7gNCndHaRd1hDsKmnhVerehf3YMXbG+Oy5B01gM9Tgd7Di3h8fDnFKmuOy7GCFj9cVUlcTRcN8TZWqdGMgOLmIEhTJAe7D+8' \
			b'AotxfI6lJvbeWAvYNmLx0pLCE7cWL6iHaZUGsnAQUItLJxdiz+ooy2KUZfmNYTXYIXj8GsOTkxn5mVDuA1rtAxp0/nhMc79WMkgf16CPe5+GsKwLFrpg0d1QQFrtMRp0FelyzwB5yT3ie6UKLdqeFhrRttABzvFU5mYveWRiT2RkIkMSe1fsOjxuMjq6sRjd' \
			b'WIxu6BL6W23mcWhqDFaKckffYH7WYh5U3nQ9zIqD9p+EIhUTXQinXQgXxrh4izp5izq8Pp2+N919mIEygGozaOuNzlYc2Gt3wUJEJwJoYtBNOjfErIOOOeiY0xG006GzO6aBBuuqV1314e0KXfWiq/xLGugVPh5F8yiav0evIGki7lOBWVc9zHet1n6L2m9R' \
			b'+3Sh7jiUu0XCThN2J2vCvOQCdihgJ0iAeVnXEkvRMkMdF7aHVHo81Gu6/rRFMJwy+/0Js8+6M+iStlrXtNXyZqkr3jJFDRDyRxvShCaF1/nXstQf89uh0GitwP6oOTJS0JaLqPKQFo3VX4wcJDxe6WV5IRqvpGPzkfLa1OQXWVAZuERcJGaD+eB5Gt7KxJub' \
			b'eGeToYLwHhMuPLdgvPCSNzXxjiZelsVi5R0NsmORaPH6PGkoWZTk56V+vOmJW1te7sd7e3idJ/cdeNqgozi2GrDJgBc+shWUN3OwSZv5HjoSHnZ48nY2J9sjed8gS3/l5cbzFrhVy3uK+2pFDTfvn5SdcLIPlOIGiiYSHZOh+573hDIpjq7ZU/PevpqD6IYq' \
			b'c9Xxvj26J+1aDbz/kynLlsZKtpSawAJv8Otr4aDj/bRGCfEGu553afI9byOlGlgN/IB4KtmpSJJc0Qto1XPZOIdat6cSUcqItxTyllP+56d4rx//81NcaN5XyaUmqqTzK94APDAV5p0cJes72eK84v3VvW7g5WDeKciUOIrlQ/+kOivfv+ZuHqtqCwU1ou1e' \
			b'96LAdmOMqmlalSHoyNG6SXFt0l28VhOoocQB2ng3Kxg9w5DUBvqdbHrhRcvqbpLG87rRevrKlS1nDICa4xmdwwwYWOnrDAhdAQBuBuwUCLzdiDcJlYDgJaK8PpTXYsqW7H49SAQgJgNJo0CxGVgojnvZETBOQUPpeMkkzzSNAEQvtggUue/ll3jEXug+wKTP' \
			b'/hZCpo+A6UeQUSIFcPqZvwikLAiQ6iOomIoXVCEayOoFW5HKGGFIqMhiVEVESUyBKpQ4IUuJDk7pzGOsRzkZXz0QxgAFylB8oKwXnAWaCW3Vv9oLKb6rL7jtGcTL6mIvGNukBnQ1/5ZOzAMqbwyVB0WjFCriUX29GEEZki22cUsSgNJoouiWQtMkbJoxOI26' \
			b'Ep8bHPMVkWpGLsDVRLxyYgUsoz69DCXPVp8DyTFsgzzmgKtxBXSDTDLwRsYGtwm7yppXDkfwVaoBwHhTZoT3ArHNQNxkOO5vGcFr4Wv2RfDdRa+p5BgUoLdFLRr0PbXfKfECXcTlbiF0mwTdZgzdRKmE7iSvlDTgtgzvRRO4FTJF/zWAV9MBvA3AG4kWyNW0' \
			b's8hFXIlcFUlCbmJtC3KRyDfIcoxcFQ+Q2wC5GeH1yJ1BrJt77R4tXB+wOsaqlQNSwpsWvhyoNgLVlm4pUNOAkW9zoEZKJVAneaWkEahFOF6wfDeLUk2kKLVAaaBYoFTTzqIUcSVKVR4ZSmPgFpQikW+Q5RilKhtFqQVKE+GdUOrvAUrvdp+YH0hIhS9HaheR' \
			b'2pVuKVK7hNRujNRIqUTqJK+UNCK1CFekdhGpfBtwqkkUpx1wmpEsoKrJZ6GKuBKqKpAMqpH6FqgikW+Q5RiqKhyFageoJsJ7dYXbB8ieOGQ5MkEWvhyyQ4TsxC2F7JAgOzbIJkolZOeyi6wqZItwheyQIJuNXjWJQnYAZDOSBWQ1+SxkEVdCVgWSQTZS3wJZ' \
			b'lUqDLMeQVeEoZAdANhHeC7LdA2RPG7JcU3WErPoyyJo4X4K43C2ErFAEZPk2g2yiVEB2mldKGiBbhgOyfKeQ5VuFbEgCyEqG7YjkGLIh+RxkNa6AbBBIgmyivhmymsg3yHIE2SAcQFaSjQjvBdn+wWp8V7BruLIiduEj7PLFNbjUSAIEm9ItRXAyPZmx6SlR' \
			b'KhE8yWuUbwRxEa4gTqYnvg0g1iQKYhiecpIFiDX5LIgRV4JYZZKBOFLfAmIk8hB6AWKVj4IYtqeM8F4gHh5AfFdA3Mlp0gHE8DGIO4C4A4jjYBcpcrcUxGmwa8aD3USpBPE4Ixb4KOOI4oIhRXEa8Jo04A1JFMUY8OYkCxRr8lkUI65EsQolQ3GkvgXFSOQh' \
			b'9QLFKiBFMQa8GeG9UNzUDzC+KzDuuWoijOHrcWEYY1WFicsqkCJ3S2GcVleY8fKKRKmE8SSvUb4RxUW4ojituDBpyUVIoijGqoucZIFiTT6LYsSVKFaZZCiO1LegGIk8hF6gWOWjKMYajIzwfih+WB11Z1A84BMLimL4+h7n6DfhOH0TzVhm4paiOJmxzNiM' \
			b'lSiVKJ7LLqWOKC7CFcXJkmWSJSskURTDkpWTLFCsyWdRjLgSxSqTDMWR+hYUq2Ag9ALFKh9FMSxZGeH9UPywmuquoJhrJNm01MerumtBsVw0iaAYKXK3EMU2Wbbs2LKVKBUonuY1yjeguAwHim0ybtlk3ApJgGIL41ZOcozikHwOxRpXoDjIJKE4Ud+MYk3k' \
			b'IfQxioN8gGIL41ZGeD8U2zGK7QkDOR3Ker/hzDXo0qySbMHgAP7Sg6v0y0gyveTi9JIr3dLpJZeml9x4eilSKqeXJnmN8o0zTEW4zjC5NMOExRthObjMNGlSnWnCvoGcdDHTpMlnZ5oQV840qWyymaZIfctMExJ5CL+YaVJedabJYaYpEd4P2RuWXTV3aLZp' \
			b'EYzL7Te7QvmmYMw1wluXum39bI8vAmo/G75s1qlziEcn25duj607/FSOZqkC/E862pP8Usaxl12EBzQDzp2rRouxuN7qbM1krYsmAwOTjrYSTUBmiqmvjeiyr62iGW8F4qAtPW0vG4I65avoaoNo6GpzHbKEq5WasSMzc6Ae/IU0bG1P10ZA7Nesdj6a13M7' \
			b'3MDK5zv9euY6aiOWW/miJQfwsLnFsLnFsLmNiG5Lt3TY3CZAtwWgm0CqhPMks9y1+WRUwRMvhTbSQKWtfHwbUK2pdPTcYvQcn56AWpPPjp41jwLRKpps9Bypb8E0EnnIvoC0Skkh3QLIifB+b+fZtVtHg+qH0fMOo2fZ/hxHz/BhT7SMnmHJttGSjRS5Wzp6' \
			b'TpZsO7ZkJ0rl6HmS1yjfOHouwnX0nCzZNlmyQxIdPcOSnZMsRs+afHb0jLhy9KwyyUbPkfqW0TMSeQi9GD2rfHT0DEt2Rng/FM8u57p2FGeb8R+wfLNYHuRzswHL8PVSKYJl2LNttGfbiVuK5WTPHvBiZlXmgxgU0RJup1btaY6j3COii3BFdLJq22TVDkkU' \
			b'0bBq5yQLRGvyWUQjrkS0SiZDdKS+BdFI5CH6AtGIC4iGVTsjvB+iH1Z73RUss8DTHmH1EZYdTrfQkbOLe4QRlruFWBa6wDLfZu/lRKlA8TSvUb4BxWU4UMx3imK+VRSHJECx5NmOSI5RHJLPoVjjChQHmSQUJ+qbUayJvGY5QnGQD1AsyUaE90Px7HKv615m' \
			b'fb32rgTYANa5M2ZuCJyLgXllUFoWYQQlfJkhy8XthIjL3VI4JiOWG28nnKBwkkXKK0KwCFcIlrsIoRobj6sJBGYRh7gScVrsDHGJj/VoQwI/hRoiAtSwXTBR3G27oJldivUAsSOAmOcRQ4QYfDnEoqEYcblbCjGfIOY3Q2ySRcorQqwIV4j5GYj5LRBTArMQ' \
			b'Q1wJMS12BrHEx3qIIcEMxBARIOYBsUhxR4jNrpN6gNgRQKzj4XiEGHw5xOLqY8TlbinE0upj122G2CSLlFeEWBGuEOtmINZtgZgSmIUY4kqIabEziCU+1kMMCWYghogAMSwsThR3hNjsIqY7th/v7o7wBhZthCF8OQyjncZN3FIYJjuNG687TJRKPM5lF1lV' \
			b'PBbhisehmj2bIiTSoR0MNJFigU9NO4tPxJX4VHlk+Ix8bRnXqVAaZDmGqcpGYQrrTEZ4N5jaB5ieLkxZqGl5ofoymKYjRhGXu4Uw9WlhoR8vLEyUCphO80pJA0zLcMDU1/MwDYkAU491hZHiGKYh7RxMNa6AaZBHgmniazNMNZFvkOUIpkE2gKnHosKM8G4w' \
			b'fTjp6ZRh2rBQI0zhy2EaLaWIy91SmCZLqR9bShOlEqbrXYJpEa4wbdbAVBMpTGEojRQLmGraWZgiroSpyiODaeRrC0yRKGQ5hqnKRmEKK2lGeDeY+nUHaecrjNrjXix4facqUpp4dDelkeO7czy317SGcAGu5XjveiG+230w3i46BbzF4fBYlFQeB+7jsiSk' \
			b'yd0eCw39eF1SIjU5L7yTM8OnmQpDoSkownlJkpXWoF3TGmg6bQ2wKCkSLdYLs5j00HEpLISx8ehxJVW2Eiqt8dpDDd3QTHhUvjQXbRXOJfeTNUt8PHkQo7YZWLeUJFO0Gdw7ry8kTn67C1mDbOXSsk+ajra6vPET+G//+H2qwd2O4C9xGfA4lPjrjukE/mM5' \
			b'fd9sVPjJCfxjNd9wCj9V/c1rK7+5hiPQ2Rv4ZMT2F8VhPxfR5IcG3rbSXusnI6TXZrp/44Ois0prrl9vW3fkesvfgLk53dWDQw6ov8aegv6ymPf77AmJalZ3pyOKq+tue126626x3aV4/jRB1OFa9ouchi77a9blRspx+PYYo6Y+6nQYORW6TeJa3JmgGruu' \
			b'708RcztOrh6wH0z6sV3H6xvqXyw/yekqn6Ri2Uz1OjuR6YbbaR77b2yrF+j3uj4H1S/1Opx8VaM5TFc5mneu3njzOayGLVbmwJ3npYO94+tAw4ai/9fWeEs3TZqCA3aquV1Z1LGm+rqgvETJTXV5AMsFCVLbbvk24g7afaihIBe63adbfRyanL7wYFMzzdmU' \
			b'8+dbtfgQQ0Gw1u/RnabiHURf8W1zqGx7c1o7YyzfWXMpjKR/hzSYOxMmaTFPMDU3p8kzJzHv2gYbZp+J1vtqtVum1aRD12JCzr9Tu4dWL5kKmpkC2snM0d9Su8ydx5u1KbM8VtRjuqJWSy93pzaabRi7mDwstHt/rfYLtbq/Jq3Ov7V+4z2MXTX6jmpzrsks' \
			b'j4P0NnbT5CtqcbtQi4dr1mISxYMW34oWl6tk7oIWdwv7zQvXryzX4uZBi29Hi80d1OL+IKO/nU1wh56vrnc1u1leSnYsI7z9rGuHnKLmFWQ7rKuo/uUvqEkQe9rwoKEnbHy4FtXkdYq3v3qC6viCQCJfG64PYzTzI7vZDWjnmvWle5vMTlxbWSgrElxmLruR' \
			b'RpXXGF2jmWzn1z5J9Ab0t9nYrrpyDfUBWtet66CXTLs1qrv90egvztXZ3uJKmnIx8iE6BZtXFy9YbMkn1so5xVKCSefAXBCEpSG+kdm2B0U+mCIP8r9dkYeTVeROFXnYrMi2utRNbT4orxW1taKwUVsb1cfRXjBRoRnVaYs9Hb3lqtbjjX0l8ulTvXKdtlqZ' \
			b'OMt8VIm9yyunTduV5JU2I0Euey6W1sjLxy0u6giAVro+jKolRQ9b2Eo0FCJgBdtNBMzBWE9bjWzqZWLxU8m4KBy/XDh2Vj7mKGRkZvAc5BQgemVZtctlNdukozFf1pIvkee27ZSTljl0i/sry7uW//l2FKXZoe1cUjGb9xmWFRY+O9DU41avm6vBw4/m1+6r' \
			b'3XNctPF1vHYstFEB5t+1g7mlEfrsbtV9xzMbXqNrR+OWBuMWg/H+QYmWKVF3bHae/GMKg7B3YC0y7oK/TGOGixW36/XFCu3S8KBSy1RKqv1IVYp3cdfHolJUJROVuiXb9XFrFU9/HaNN+pbfeKxCzXGq0DVNeSxSI1+NP2a0TKXsAVWqs3tolMwzX5NSyTKz' \
			b'+e43G0Ga8J2gcbM1/S4Q+TJ1u+0Jt1vTuK1axip17BNqeeN1LZNo+zVgtrrk2bwBYmQpdxLu5NBmT4PDS/7GIgXS3dlKzybFeTFGjpSIe3tIjPwZQt4XTywTtzIMdqMtO71j6iuzlYypJn/ypB09acqDaXCmTHGajGye4xW9cXJND2vBQSr8AYgKf1SFVlZX' \
			b'Bmdl8xEisWe0lf1xFMVGUCon2255jQ02dQqPbhGPk0NvhM1wrtRaVgm/s39s1B75+WiP/E9Y80tYmz2SZyN33JJFDn01/8em93VxMIrTVbhscy45z0F4nRxDhJPD0+FCmz+iMD5NiA8Raqt0bhBxMPo+wpqSjs704YatT2f2yHk9ejYP6346j+c1t9v447a2' \
			b'xrWtxoHRtZO/IkGWcsOjMbDhxVJZ6oKiyLw7gGZ01Z5/wmFfcngFfZgqw6wmLNGCRbU/VOGPX7G5J3fD5K9IIGnWPTFJUhAQIQ4HqGbuKFy/E/ab+kaV4KotwiJd4L7bzTmxeBfO7UcMEm8OoTFtdQMO/JvTeJksUx0OVMdcNFUeso/jzvsVSWxyqIItnTZn' \
			b't6B0oyIF4UVl4vHQekcjhw2xPJCZj2hTBArl7pBe8fjxlBxqYEtndqtaQdI7KperruLCIHlbQhTwRPrBi1SMjROn5FADk17xVPbLtAzC3kHX5kRoqtz1TVWELHTBOrM9YWFqEZH0d0kpbXVSDjUw6cPfqlK66pYcLEn1XVJHX52UQw1MBgi3qo5tdUsOwrhL' \
			b'ow2ePTglhxqYDDaupo7BNLRWqm6BVjpU+DU5rsn5CGJ/zUOQzcQyvUYvr1E8c0q3Vkym2uwo5dY0S1xOZ44mpDUZXxyZtFx1HA7Sao9cWm11HA7SWjCwOFpjNn/QYYHD5DH+Fz4y++yi52cTQdSnPG/As/RH7SDiBSOS4xWxrY7bYd77Zic+bljErjpuBxEv' \
			b'GMgcr4h9ddwOIqbhkTE8E6x+G/x4LfIhcXywq5UwXgek2k9dsbweSGaUgI94G+QMIV5JhNaejzKaSdlWmUPCbpKQxc+Juyp3Tau89tmSGDYba/AgX6SEQkzqt5MlMbKSSldRlSufugFrRmp8isvwBhhsPxEivOCKlWDQpSUNTwIJ0Z7yf33+/+zws+E='

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
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LETTER})'),
		('LOG',           r'log\b|\\log(?!{_LETTER})'),
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LETTERU})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\$?{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
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
		('SQRT',          r'sqrt\b|\\sqrt'),
		('LOG',           r'log\b|\\log'),
		('FUNC',         fr'(@|\%|{_FUNCPY})|\\({_FUNCTEX})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
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
				AST ('piece', ((expr_ineq, expr),) + expr_lambda.pieces) \
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
	def expr_func_3        (self, LOG, expr_neg_func):                             return _expr_func (1, 'log', expr_neg_func)
	def expr_func_4        (self, LOG, expr_sub, expr_neg_func):                   return _expr_func (1, 'log', expr_neg_func, expr_sub)
	def expr_func_5        (self, FUNC, expr_neg_func):                            return _expr_func_func (FUNC, expr_neg_func)
	def expr_func_6        (self, FUNC, expr_super, expr_neg_func):
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

	def expr_bracket_1     (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):       return AST ('[', expr_commas.commas if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_2     (self, BRACKL, expr_commas, BRACKR):                    return AST ('[', expr_commas.commas if expr_commas.is_comma else (expr_commas,))
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

		lalr1.Parser.parse (self, text)

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
