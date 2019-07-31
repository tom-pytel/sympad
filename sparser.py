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
			b'eJztXWuP3LaS/TMLZAZQAxIfouRvtuPkGms7ubYT7GJgGI7tXASb19rOPnCx/32r6hQpitLMqHu6Z7p7GqNpiQ+RxWKdIll86Oziq3/5+PuHr6qvfnz4kn6fPfnmNd2+f/jyyYtn9PD02xffvXzy9vEPL5/9Ozm/efnwsd4avRu6P3ry7dvHD189eaXPzx++' \
			b'1qdHw+OPw+P3eJRUOZfnT1/8IO9Sev/KHq9eMzGvfnhEvy9+eM6EvHj9LdP39LkEyO/fX3Iqz17wz3cc+s0PL5i8R1KUx989f/5Q7s++exHL9DJm+zJmxw8vn377N07q4fPv6ffrR89ePXv46m/0+OTF11oYfno0PP44PGphnvydf569eqLekR+c2msQRARw' \
			b'zOcPv3/1+jvO7rUU88m/PX4Wg5mrXz/98enXnMzjr797LcyQ15++kCy+fyasevoN/UgqxCV+6/27Tx+/vP3j09sPP/36+cu7T+T18X/+/PT2819/fkyO3z/+4+3Pf/3+fgj8KT7+9u7L2/d//Jo7P/3x34Xzc3S/f/f54+fP78fOP8fO6Hr30/D45Uui5ed3' \
			b'77/E5z+HnMbk/RYff/0lPf7y+5d/JLr++vXtL7+ljH8fXvjwy3/Fxy8fP2XeP/8cn3/69O79f3z8kjEnFeCvT7/+b54HPWSsSMX58GFU5IHCj/+ZykOZpGL+8vH9x+SgCvt9SPTPz1/+iK7/Gqrv13e//fThXXSlZFO2f/z227uR4/NXb6qLs5VrKmfOKzxY' \
			b'frDVysm9qc5MZdpq1VSWH86Tr/gNHquOHxqLH28o1J/nXo3LvfiRX6zx4xBAT5SWROk448ZrxuQZfdUveaxMLU+mOiMHxXUaxCSgEIZ/bGXduTrJJU9OikpBK3s+8oDLxvco3EUvfqQnI/8mxFc5UclW/UEDUaeecLdEvxX66+hBZZCnnuJK0U2DH8dl08QH' \
			b'L2bj4MuPXG/07ytLSYCPjh84Ro8fh2qiJ2Kx5EZ8Zz4yj8x59GlzV9A7e/G7gSoENUIcoZxtf575r1w98cqddhrDjp3M5G7iVb7kxk4/cY5fWBkwt1GxJLobMK/BI0cj7jH3OXd+WyNE78G5MsJUT/8Qfn7hHF4rYRcRcGbqqgkV13JbeSfc4kQhEPMRGHeE' \
			b'mEXxqP7H8VaEQXqi4q+6yrlIEpW9l3I6BRKXkGTE53CisOidPLjK2acdfBr4hMHHwKeLPiTIAo+AnwxRQXFhW/wImJASufiRn3wMPFcnuWIA8vD4cX0qe/Tyde7Fj8wYix+qt/Pz4ZHjEI1Csb5CBDbCKYKPBKj0MJoM0iL+iRiJTrJRFyIa+YnP4HRSZzZC' \
			b'nISkEcz1kDovgSxo4HnurR7klnw7/JBUnqubICy0sR4MkrA6PfBOTCatkMSGywD5c5nMtLFg5HnmBqCK06ZUyelQfnrXmPjU6kOTHiRSWzXn1Jhc1BXJJGVB4COeE2pEf1I9eiKyr5q6r1pXtb7q+qqvq76pelP1tupd1bNEMc2cs3CExJ6qlJRkqDoS4Lat' \
			b'2lC1XdX2VSAN1VShr7q66gSLpN06V3UU31Rob6jgTU3umoiriSd1x5qL5d9WXVd1puooDyKNAEbp1lXbVK2pWnq55le5WaQGkVHlSPRa4gerYJJBkjkvmO3bqid5J1Zz+hVVpKt81b6pzshxTo0rcYMr07S4WWET6zF2WsSx6vLg4Rmxit1C9/mJn+AnF1aY' \
			b'0oNpLZgGuTtrPXw7xGrBbqb8XBApfO3rEz8TP6lkENDuxJSBKQZM6QWZZz1krI/AtMIrlG5aLhQnFaQsBRFPjKRMnHLe9ltJTRWNB8keJAf57ZTuRtDBzQIlSklTon1Fqvu+VnPTajWDV7h1tXKrExaCXiJzIGt3NI04njP6htJxwcONE7y13qnREFwEIj5U' \
			b'oauCq4KvgqmCvcc86U48mfCkP/Gk5EmoTzwp2pHQoOXAzWg7gh5/47SVr9G5Rxxr0F8VmqU7G/TeaXQ04510RA6qrTnrMGzpdFTjUUIvbW1PddtrFacKPYom9swHHZCgoltUdKsV3Vqt31rv2vlzOjRBsBNhaWryrLmoxBgiOOxdYYlu1KprD4ZgAMxBOF0/' \
			b'SOMhUO8hNl6kBkTmZO8hwZDrvpQPGX+jKmwbh1NR96lOVGj4U491aHWZDzAc0e3ecoGKTcW/Z8VmO6BRUxdX/v2seiqgOamDNDBpRR0QNSemJKa4EzMGC2YNnUElvL8NBhu1jdpxDey495cZYrY2NzY0X4wmVd6k6Sk2Yxs1QNP9GId4F2dBinZkheqOr1A8' \
			b'0yHC2OjQAqM+nhOXaVed3mlgqTHR4h9EhI+CAxc8j3EsheGpGKlOTGrNTO6+wQywLKtiTd8GvBDgGyAGIc4AB1gvgr4aYH1pO7wrUsB2TknCSgvKFjtm5yEyz6hiFkwUY3GPjuR4nrCPCw/kvk1a+jhrX4PV4G3LFL6BdcyoVcygMjn/oU+Hhhs9u3vWfLNt' \
			b'ELwRCd9XQ5WI1z6TZ7ct0mx/w5qTdn9Lftapddr5/ZUetiZDxMM+E6n9XNftMZFeFalv9pjIHm2PVVsGmoRk5+Tloqzvz7ESzt5Tyxdb/Sw6PcIKot2ig3OahS1W8xjhDNhFJZVbIzfTgXk9xKrnOPSGVW8P73EnKMCvXBQ048ujDaujDYNhBne07vPSKhlb' \
			b'GYyt7q/JheXEQk4surMKXatjE4NBCY+/7zN0L3gkdo/FpIVWaSEtoYZ8WOiuA1wCcsGjZXuQo2UZJtvjtF/yuN7o6Nti9G0x+rbnwwCpzlwOTaqB3YSHnqLHah2e1zC2dFBkzqP9RcPpINMeeSCIcO3QlXHalXHRVoP220n77dBwO22x3f2b8TXgWqN9voA+' \
			b'TTJXGVUQYNhBKggi1026XES6g1w6yKWLViGnViG3t4MZSterUPvYyEOovQg1/5KoesWfRzk9yunvbdsHjXN/y89C7WHMblU0WohGC9GgG5GtMGgRM2jMcCT2/Qsub0B5g6AG8zI6S1NLSUeGay59Bz51eK+LUbtjYkp/PIUxR1MYEbNe1/jWusi3lhasrnjn' \
			b'KykzEAB9xCRJjrztqpadV1ibEnkAzQf6czq54E6K3KmaUz51otSMMM+JThQOACKtENsII8jNBeG8eSqU50F5tpMnQnkPKm/6Y+3Hq9J5STqvOuddqLwFlZdn8tY03lgmG84pnFf98pJfXkzLK2l5bTcv7Oa1z7xblTU3r39mxjBTuBJ5gybvo+A5N56OY6MJ' \
			b'd1l4fThvsWLLNG9CJPoNdyhrGg/XnpiJjfu8Sxm73nk7OJdu5XlrNDUQvP2eWogV1e6q97ItXjY4e9mIXvEO6sAnUvD5CPTc8fucFO+BriUx2TvNpw1Q8lS7K6JpRWVZtbL9md7jAyx63rvOMTmdSANvqSbqmQQqzMq3mhLvvOcZgRUVa0WsWvFOdd6a3vNL' \
			b'EquSXei8AZ5Ys+rZTS/2evABbwCnV3m7OB8nwNnIYQQUmwkj/5bLJSdkUOpCKB/fUHMROD9mBOfNaXEJ6OLkGzkUY0U1tup6HPnAufNpAvTYMiuFL7y1m+K25g13QFmcWwixEUh43T4I65YxKsrDqiuBUA7wq4TbDvKd43kk60G7BEktcL+gjbht1HICA6gO' \
			b'1oAKOwCDJzR5xX22ZLoEt2woFsw0ihur2PEFfiiMd3Mn7JgCMxSPN4hOsMM6xU0xxEvReXk3r+3mVdO8gXMRrhhT9YArtkkKtpoMXxTG01IJY0ZxRlVH/DA8kBthjpRcwpY80xudIAunYnQRWV32txBlXcJYN0ZZSqdAWzfzl9CXeQGHXUIik91XAGN6y0mE' \
			b'IN4SxUkUL2XKwIlSKygZkAmMKOoYkOKXgVKz6/W+CJ59o6X3QmIPpAOgSAUA7QSiqUADUKt/tg+EL65+wKqsDw+E4SReD1hLkIjQ3fyfdKlOgL5VQN8VkKXQCcrqore44aACBJwFIlGAZ6uR0rUU1UPTWbae8IoBY2xfcYU6Q7kdp6JQtwnrHJkXlTRAu8RC' \
			b'Ag7RgtwcXnI9aKnllqE+MmgO95EdY+Srb479RGW/BvSbBiR5kDtCv+YR8W+hAFI2G+oAm+mAJlMD3d0rgEvRbxcpgBP4FfxcqAT+VlzswR1l7SRLuCC/MeW1EPkcU5HPjznyR6mVyJ/kN0SNsC/9qfJbI4rMFP3tXiIz9lMSDrECAvCOQzSPgufAV87MAl+5' \
			b'UQAfvhnwBzrXAr5yx4PcMfARpsCX7OoRmy4H/gzg3Vyjv89oP0F9OdStnPEV23m4cpzbhHNbXktxPrTwTdHCj1IrcT7Jb4iacF74o3lv7AzILUAe38fpaswmtO4NWvcGrXtTtO7KllmQKysKkMM3B3kici2QK2s8yB2DHGER5Gjdcx6tBXJ/hCA/degzoIcK' \
			b'R/0B6HDlQA8J6KG8lgI9DEAPBdDz1EqgT/IboiagF/4K9JCALqWReALzLAGHaHA6xHSI6VHsHOnKl1mkKy8KpMM3R3ryXAvpyhsPcsdIV+IV6QFIz8q4UT++PSH+uBHfV81g6VZXjvg+IX5yLUV8PyC+LxCfp1Yifi7LRK4ivvBXxPcD4nsgvgfiswQcogWE' \
			b'IaZTQlDsHPHKl1nEKy8KxMM3R3zKfC3EK0ke5I4RrwVTxPdAfFbGjRAfTog/asRzRdYJ8erKEC+BgniE5ddCxHNMRTw/5ogfpVYgfprfEDUivvQH4uUJiDew1fGNNzNlCThECwhDTIeYXrkwID7yZQ7xkRdjxKtvhvgh83UQH3njQe4I8RqmiJfsxkzaCPHd' \
			b'yV5/T6BvuC4T9OHqcXNNpUfrm2S1Q4z8WqoABqudKax2o9RKBTDJbxQ76YDCX3XAYLWTYvUojxsl4BAtIAwxHWJ6lDzXAcqgWR2g7Ch0AHxzHZAyX0sHKHs8yB3rAK0v1QEw2+Vl3EgH9CcdcE90QJAPiUQdAFePr4uwDgjQAWmgjxj5tVQHDAN9Uwz0R6mV' \
			b'OmCcGVfAKHpSAgVRqgSGwb7BYN9gsJ8n4BANToeYDjE9ip4rAeXQrBJQfhRKAL65EkieaykB5Y8HuWMloMSrEsBgPy/jRkqgqU9a4J5ogU6+KBO1AFysBbAOBx8CQRRoga68lmqBYUGOKVbkjFIrtcAkv1HspAQKf1UCwyodA8O+wTqdPAGHaAFhiOkQ06Pk' \
			b'uRJQBs0qAWVHoQTgmyuBlPlaSkDZ40HuWAkgLCoBLN3Jy7iZEjitx7svSqDnaktKAC5WAj2UQA8lkCyAZnItVQKDBdAUFsBRaqUSmMtyiJ2UQOGvSmAwAhoYAQ2MgHkCDtECwhDTKS0oea4ElEGzSkDZUSgB+OZKIGW+lhJQkjzIHSsBLZgqARgB8zJupgRO' \
			b'a/juiRLgChvMgerq8YE418TvedlkFESM/FqoBOxgFLSFUXCUWqEEpvmNYkclUPpDCdjBLmhhF7SwC+YJ4CN3xDALu6CFXdDCLmjHdsHIoDklENkxVgLqmymBIfN1lEBkjwe5IyWgYaoELOyCeRk3UwJ2rATsYesBOYW9PqmDq+cDmbBhPlAYzR69NAL6UUiZ' \
			b'GEz7X/BKfi2dGHTDxKArJgbz1MqJwUl+o9hpbrDw17lBN8wNOswNxv0QDnOEWUL6YkAY3nA9aAIH8jlCxJ6fI1S2FHOE8M3nCFPma80RKps8yB3PESIszhE6zBFmZdxMM1yx2q854HnCbWmBcofbmprgVrQAz8bzHLK/bpTgK2xIwygBrmy+MGg4hgi+vDbY' \
			b'HcdvjZSB1MnwPxknTDIdck+DhMI/agOMEoJXKnqJKXogZgbJ0NVBtS4PqnV9UK0LhOrCaKhcGnQB5zCMFpQzxWgBvsXuO0lnnbGClz14LA711GyILOJggauexwjVSmcRMrbN6IWe7rKKiu9e9IC/ZJn/XvUQ6psu+T91EDJ10OIT7brs31bq0ePT7Ww3aGE3' \
			b'aJNSaMtrqd2gHXRCW+qEJkuuVAiTDPOrzdYGl3TxHgD5mrEZ9txK6XoUy2VxxXzQwnzQwnyArbhCERiQ6wRNadZ8oFwpFAJ8c/NBynwtlaBM8iB3rBGUatUI2KGbl3Gz/sHsssG9Ugon88F2zAcd100yH8CFkxDEfICJBJsmEhAjv5aaD4aJBFtMJIxSK80H' \
			b'k/xGsZP5oPBX88EwkWDRObCYSMgTcIgWEIaYDjE9Sp6bD5RBs+YDZUdhPoBvbj5Ima9lPlD2eJA7Nh8gLJoPMJGQl3EzJTC7knDrSuCS4zpOquDWVUHP1ZNUAVysCjCdYDGdYNN0gp1cS1XBMJ3QY2UB92L1LBdoBEmOj2uZzipMsx2RkDRC4a8aYZhVsJhV' \
			b'sJhVyBNwiIbcHWI6BHowINcIyqdZjaBcKTQCfHONkDJfSyMoSR7kjjWCFkw1AmYV8jJuphFOKw3viS7g+hhOBlAXvSU2A7hQa6oL4JdfC3UBx1RdwI95t2CUWqEEpvmNYkclUPpDCcgTlIAUq0d53CgBh2gBYYjpENOj5JkSiAyaUwKRHWMloL6ZEhgyX0cJ' \
			b'RPZ4kDtSArGioAQku3pUxs2UwOxSw21vMNiusXAAe1tdfe7VrsC8AZBvDmJbuWHbr7oyy59L234Rll9L4TtY/dw1x2JN8xgyS3gt/BWvxVZfh22+q+uO0IolnkWllrJAJXxzVCZaFiNSWeEncNR0FI7YypvzYK2tvGZ2rd8JhnsIQ8+DnARDuHIYJus7wvJr' \
			b'KQz9AEN/DQwneQyZJRgW/gpDX8DQL4ShlngWhlrKAobwzWGYoi6GIaLPwFDTURh6wDDjwXownF1td4LhHsIwsJUhwRCuHIZpyTzC8mspDIcl8y5cA8NJHkNmCYaFv8IwFDAMC2GoJZ6FoZaygCF8cxgmz8UwRPQZGGo6CkOsgM95sB4MZ9e7Hfiu19NgVJHb' \
			b'M+cTcuHKkZtMUm5yLUXuYJJyxQrXUWoliueyTOQqigt/RXFfTY6vcTBFpfcdYgUE4J1IB0qdw1vZMgtvZUUBb/jm8E5ErjUEVZI8yB2jXEulKIcdKufReii3J5QfLcqZ58NCVnVlKPdpCSvC8mshyv2whNUXS1hHqRUon+Y3RI0oL/2Bcl9PUe6xgjW97xAr' \
			b'IADvQARXkQkDyqPPHMojK8YoV98M5QOR66A8ssaD3BHKNUxR7rF8NefReig/HUV3xChvmOcJ5XDlKE8mZYTl11KUDyZlX5iUR6mVKL/8GlBe+CvKmxmUw6Kc3neIFRCAdxyiQQxHKFe2zKJcWVGgHL45yhORa6FcWeNB7hjlCIsohzk559F6KD/Gs+hOKFeU' \
			b'G2Z4QjlcOcrTERUIy6+lKB+OqPDFERWj1EqUT/IboiaUF/6KcjODcpxQkd53iBUQgHcconmUOke5smUW5cqKAuXwzVGeiFwL5coaD3LHKEdYRDkWluY8Wg/l7WXfOslXm7Z7v/Z8Z0dL81lf6WMrrApsoQ6a7SxJX1stUBrEkGXqwW2iIsKi77YQHVxfaqor' \
			b'PuDik8kOcfJrg3XrvrDZjZKbfOQlyIdephn7zIJX+vPyVCiTMKNMYMhLSaB8HZwO7zhEY7ker1jnSoufjJEy4Hblh2MiowolA99iGXushKVahuVKTrmXV+NXZaRAI3XDH5fRtKPKgSkwZ+ZY5ZAfKRwJlN+Of1n38I1Ujw+ieUJ1sfNvLO3JB5bcGpjurzCp' \
			b'u+ryDy3x94H26BtL+/R9JWbLxt9YGkPhqu8sEYG7l2gisa33Ra43lekl8ryHHw1r8kPS9kGwd/nhMOk8Gqjqfl6wzQ5k2x+abPtdyreZ71ftVMa7w5Rx5vyGH8gjls3K93Twc3P5DluUb/7M5T7ob+J0Q5Uc5bzhsZccEXsI8p4fcrE1eWeW3b1exyCvTXIf' \
			b'B3oT+W+Wd1yoFrf1xVOqwQ2WvNxVvzwswEG3o77M8kMhb/QR1CZbeI3UzMK1K9vT92zAWEPnm+sx0FzWv6H6px6Ok6+pmVvqukdz1pYaAQoj0WrkHM+76swvHaDuYYceRiL932ojgH5hEBvdHXXyWR0t6+hTHT6grAUItrq4BYsMlVnbgE6+770eAu5i+ErP' \
			b'wW3Szd8TaR8+1tUN6p6PzLGbSPrtD19BrNmoe+9uR6apa99FsQ67ley5iYWbSDe3u+aopJyVuhkkneXS71baZz5ZcTNdbrhA/PLmku+XST41f1sxsVOBbir5S6bW5qbUNpX+9q70e7dzmzszZxXCNiQ/rN2LCe1NTDkNEHADyW8XSn63JclPYl/fVm/mJlJ/' \
			b'pBKfS3tTbofaZc/mJtJ+U0kPCyW937akNydJ3xNJ32i0eniS3i3sxy9cirRc0s1J0vdE0stlOUcq6f2tjFg3Mj/e4dqB0K1rcrQVhHk/RqWbWxbvbrkALxpcZx1M9U9eWyqHlxJXT1J8kxUwe2ZU2Zr4NiKQe7bahWTgAeFKBLe5HYNhO7IZ7kiCL1uHvA1z' \
			b'4aFLdCMC2uWmwp0pZ/5G/M5MhOt3MSho+zJ+2Yr+UlH7fJH+barrdRbXL5jnlIUvjayx2Bthx06H8f916lzi5Evdb7NXss6S9QWrc/nQffkUA1M/0zuxD0gdiJbfxVTnCQH7gAA/+b8eAf6IEOAVAf4aBLjqQjd4pq2dVuTdiqQnMW9UfsebINt5MWuLHUh9' \
			b'w6IgPOf6ZzqynYZS50ErG19MGVWyLGKI9ZVvxZM2dYahzJ+cL20rzZ1fXNQRYJ10yASBS4pup8VntBQsYJlbjwVMwVh0o6iyFC5hi59yxiXmtMuZ42b5sx88moN45FNE7I15FRbz6pq2AK3AGk3AAuaus6l4otJjr729aUVIScb/8/pXw9bTuYuUwFKNOlPP' \
			b'8VNOdTtWlt1cxd+R+eKyvejbGORd1epfOrC7Ulzmm/Te3nwAt/mgbXZX93YGZ1e00JebH2z7gPo4Imj9SdA2EzSuuf0zfmWSxvvV67uWNOMe8EcFLd3YNuQfrDoWOyL7JHabiV2z72LXCI37KXbNVOzucmLgYCSPF3TtrcF/v1pXFjOzv2K2izmnJaJmiw9U' \
			b'LhO7W51nktw2kTqZe9+J4HHKl4wYeNTRxG89Fupv+m1HkqRMJPdiVnQfpPJaSeTKO4hZz1wJ7mCmc0NF6KoLnoENYC3bAbz4e/kehWcrDH/Lu3tzTk9nKz0+HWdBGTn9JW1iI77xF635QAo+CSjwjk4cmDTsS0PqK3NtMqaa/MmbdvSmKQ+dwmFRxTFRYgWW' \
			b'zb06+xlPXcIpSPwtrQp/VBOWl3ily8oOOwRig3UjG0UpiI9WYmT1WGSFXc9Co1tE4+Q0K5BpriGVMD77x/MBI3dbxBDS/BLSZs/aupI6PnIqUUhqZ/aPZy0uC/Myh0B3obLNqWR11AutkyPG8FGUkWHt6s9NjU8K6+2w1zieCeb1TDA+D4z85Rwwf3nBR2d1' \
			b'URz+sHk6f6uv0jlb/LnW4WytN6zq8RfEmN7iZ+yZX+3kbxonS+qSkJm3CfqykqrNImUvSXWEWxCaUG34JxR2JYU3E5WpnIyFZEMBWSQYfRX/uMHOHcXVT/7m4kz9ilcncYuUhL/9LUgAd0O2fwn5Tb1r+dimHlkkJpzYbq8md4StJInKaG5DmNpqBxfoNwfZ' \
			b'Oi2TKl5SqxdTZKrcZ8PLbiWV6y/UzjUdRGevAfaVMhYZmeSMx2eXX9T9vyKUB1XzAWF4D4VyxytyPLw91AuVc02f+lqJQw2sKXeuuskVx/LXRUQBD7M7vkj62KxyqBcqZ9I5n1bLMgFEJawhhnPsNFV+dWPn8ival66PWBiIhCXdEcurrQ72QuVMhhJ3Kq+u' \
			b'uqMLZrD6iCXVVwd7oXIm45Q7ldS2uqMLzDjiQQ9PpBzqhcqZjHluJqn9NaOgnLuXctVBFrZ0ca3OBxDVl7wE3kyM8ZeI7BbZMyOAl7PJVFdfvbsmwsIrT2cuTXBrMpbZM265aj8ucKvdc2611X5c4NaCkcqhGOlZGy248GmZ4X/ha5e+v1Zas5FQE0c0XcJL' \
			b'HQ7mAvcXjIAOhvuuOpwL6wd2PhV0i9z31eFc4P6CMdXBcL+tDucC9/lYayY9qNtGN8YRfDIqs8fyaiA+XUXn//ncyLyKiH8UgZjCp9s1fB5S02qK7WzMUGUXIoZJRK4KjtxV+dUEaE057SkuSPJcpfDu5XvjSVaurPrQyzSzGS95S0vVZpapKbVydMl4+5Ys' \
			b'k8S0tdWcNBeeKfQsKLoYqOFpNcm5p6K8Of9/7LjJIA==' 

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

	def expr_func_1        (self, SQRT, BRACKL, expr, BRACKR, expr_neg_func):      return _expr_func (1, 'sqrt', expr_neg_func, expr)
	def expr_func_2        (self, SQRT, expr_super, expr_neg_func):                return AST ('^', _expr_func (1, 'sqrt', expr_neg_func), expr_super)
	def expr_func_3        (self, SQRT, expr_neg_func):                            return _expr_func (1, 'sqrt', expr_neg_func)
	def expr_func_4        (self, LN, expr_super, expr_neg_func):                  return AST ('^', _expr_func (1, 'log', expr_neg_func), expr_super)
	def expr_func_5        (self, LN, expr_neg_func):                              return _expr_func (1, 'log', expr_neg_func)
	def expr_func_6        (self, LOG, expr_sub, expr_neg_func):                   return _expr_func (1, 'log', expr_neg_func, expr_sub)
	def expr_func_7        (self, LOG, expr_super, expr_neg_func):                 return AST ('^', _expr_func (1, 'log', expr_neg_func), expr_super)
	def expr_func_8        (self, LOG, expr_neg_func):                             return _expr_func (1, 'log', expr_neg_func)
	def expr_func_9        (self, FUNC, expr_neg_func):                            return _expr_func_func (FUNC, expr_neg_func)
	def expr_func_10       (self, FUNC, expr_super, expr_neg_func):
		func = _FUNC_name (FUNC)

		return \
				AST ('^', _expr_func_func (FUNC, expr_neg_func), expr_super) \
				if expr_super.remove_curlys () != AST.NegOne or not AST ('func', func, ()).is_trigh_func_noninv else \
				_expr_func_func (f'a{func}', expr_neg_func)

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
