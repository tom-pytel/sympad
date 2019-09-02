# Builds expression tree from text, nodes are nested AST tuples.

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

def _ast_from_tok_digit_or_var (tok, i = 0, noerr = False):
	return AST ('#', tok.grp [i]) if tok.grp [i] else \
			AST ('@', AST.Var.ANY2PY.get (tok.grp [i + 2].replace (' ', ''), tok.grp [i + 1]) if tok.grp [i + 2] else tok.grp [i + 1])

def _ast_func_tuple_args (ast):
	ast = ast.strip (1)

	return ast.comma if ast.is_comma else (ast,)

def _ast_func_reorder (ast):
	wrap2 = None

	if ast.is_fact:
		ast2, wrap2 = ast.fact, lambda a: AST ('!', a)
	elif ast.is_pow:
		ast2, wrap2 = ast.base, lambda a: AST ('^', a, ast.exp)
	elif ast.is_attr:
		ast2, wrap2 = ast.obj, lambda a: AST ('.', a, *ast [2:])

	if wrap2:
		ast3, wrap3 = _ast_func_reorder (ast2)

		if ast3.is_paren or ast3.is_brack:
			return ast3, lambda a: wrap2 (wrap3 (a))

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

	elif lhs.is_ass:
		if lhs.rhs.is_mul and lhs.rhs.mul.len == 2 and lhs.rhs.mul [0].is_var_lambda and lhs.rhs.mul [1].is_var:
			return AST ('=', '=', lhs.lhs, ('lamb', rhs.stop, (lhs.rhs.mul [1], rhs.start)))

	elif lhs.is_comma:
		for i in range (lhs.comma.len - 1, -1, -1):
			if lhs.comma [i].is_mul:
				if lhs.comma [i].mul.len == 2 and lhs.comma [i].mul [0].is_var_lambda and lhs.comma [i].mul [1].is_var:
					ast = AST ('lamb', rhs.stop, (lhs.comma [i].mul [1], *lhs.comma [i + 1:], rhs.start))

					return AST (',', lhs.comma [:i] + (ast,)) if i else ast

			elif lhs.comma [i].is_ass:
				if lhs.comma [i].rhs.is_mul and lhs.comma [i].rhs.mul.len == 2 and lhs.comma [i].rhs.mul [0].is_var_lambda and lhs.comma [i].rhs.mul [1].is_var:
					ast = AST ('=', '=', lhs.comma [i].lhs, ('lamb', rhs.stop, (lhs.comma [i].rhs.mul [1], *lhs.comma [i + 1:], rhs.start)))

					return AST (',', lhs.comma [:i] + (ast,)) if i else ast

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

def _expr_mul_exp (lhs, rhs): # isolate explicit multiplication so it doesn't trigger imp mul grammar rewriting
	if lhs.is_curly:
		lhs = lhs.curly

	return AST ('{', AST.flatcat ('*', lhs, rhs))

def _expr_neg (expr):
	if expr.is_mul:
		return AST ('*', (expr.mul [0].neg (stack = True),) + expr.mul [1:])
	else:
		return expr.neg (stack = True)

def _expr_mul_imp (lhs, rhs, user_funcs = {}): # rewrite certain cases of adjacent terms not handled by grammar
	ast         = None
	arg, wrap   = _ast_func_reorder (rhs)
	last, wrapl = lhs, lambda ast: ast

	if last.is_mul:
		last, wrapl = last.mul [-1], lambda ast, last=last: AST ('*', last.mul [:-1] + (ast,))

	if last.is_pow:
		last, wrapl = last.exp, lambda ast, last=last, wrapl=wrapl: wrapl (AST ('^', last.base, ast))

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

	elif last.is_var: # user_func *imp* () -> user_func (), var (tuple) -> func ()
		if last.var in user_funcs or arg.strip_paren ().is_comma:
			if arg.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg)))
			else:
				ast = wrap (AST ('func', last.var, (arg,)))

	if arg.is_brack: # x * [y] -> x [y]
		if not arg.brack:
			raise SyntaxError ('missing index')

		ast = wrap (AST ('idx', last, arg.brack))

	if ast:
		return wrapl (ast)

	return AST.flatcat ('*', lhs, rhs)

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast.numer.is_diff_or_part_solo:
			p = 1
			v = ast.numer

		elif ast.numer.is_pow and ast.numer.base.is_diff_or_part_solo and ast.numer.exp.no_curlys.is_pos_int_num:
			p = ast.numer.exp.no_curlys.as_int
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
			elif n.is_pow and ast_dv_check (n.base) and n.exp.no_curlys.is_pos_int_num:
				dec = n.exp.no_curlys.as_int
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
	elif expr_super.no_curlys != AST.NegOne or not AST ('func', func, ()).is_trigh_func_noninv:
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

def _expr_vec (ast):
	e = ast.comma if ast.is_comma else (ast,)

	if all (c.is_brack for c in e):
		if len (e) == 1 or len (set (len (c.brack) for c in e)) == 1:
			return AST ('mat', tuple (c.brack for c in e))
		elif e [-1].brack.len < e [0].brack.len:
			return AST ('mat', tuple (c.brack for c in e [:-1]) + (e [-1].brack + (AST.VarNull,) * (e [0].brack.len - e [-1].brack.len),))

	return AST ('vec', e)

def _expr_curly (ast, forceset = False):
	e   = ast.comma if ast.is_comma else (ast,)
	kvs = []

	for kv in e:
		if not kv.is_slice or kv.step is not None or kv.start is False or kv.stop is False:
			if ast.is_comma:
				return AST ('set', ast.comma)
			elif forceset:
				return AST ('set', e)
			else:
				return AST ('{', ast)

		kvs.append ((kv.start, kv.stop))

	return AST ('dict', tuple (kvs))

def _expr_num (NUM):
	num = NUM.grp [1] or (NUM.grp [0] if NUM.text [0] != '.' else f'0{NUM.grp [0]}')

	if not NUM.grp [2]:
		return AST ('#', num)

	g2  = NUM.grp [2].replace ('{', '').replace ('}', '')

	if g2 [1] in {'-', '+'}:
		return AST ('#', f'{num}{g2.lower ()}')
	else:
		return AST ('#', f'{num}{g2 [0].lower ()}+{g2 [1:]}')

def _expr_var (VAR):
	if VAR.grp [0]:
		var = 'partial' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_'))
	elif VAR.grp [1]:
		var = 'd' + AST.Var.ANY2PY.get (VAR.grp [2], VAR.grp [2].replace ('\\_', '_'))
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

	_USER_FUNCS = set () # set or dict of names of user functions to map to AST ('func', ...)

	def set_user_funcs (self, user_funcs):
		self._USER_FUNCS = user_funcs

	_PARSER_TABLES = \
			b'eJztffuP3LaS7j9zgeMB1ID4lOTfnMTnrLF+ZB3n4C4GRuAkPotgEyc38dndi+D+77eqvqJEvbqlme6Znh5h2COSzSaLxaqPZPGhJ9d/+V8fP/34l+IvX755+eY1PV8+/+s7enz97O3z1y/J8+Jvr9+8ff7dl9++ffnvFPzr22df6sPo09Lzixev37xKT5M8' \
			b'8s3zv3335bNvnn+j/lfP3qnvi8779877NbzfvHz2zb98Qbn/KxPReiRaaOFQ63n14vW3XMA3797y/2+/oP/PX3397t+/ec6Zvf6Wafv7M/7yxet3f+NqvnglKeX/v73lVC+l+m/4279++5pr+YX84ss3r149Syx5m4p9m8hiz9sXf/sXzuL5v9G/Z6++pv9f' \
			b'ffFSiOXY119ptdn3Ref9e+fVaj9/+c1zjUlM44zegRAigBO9evb1N+/ecEnvpL7P//eXL9PXzPuvXvz9xVeczZdfvRFe4udfvwSPnr9L7KKsQeyXz5TkVMSblOTFa6kTfaXM+JZTvvgr/RMSiNem1y6c6IcPv3/8/N2vv3/34/c///H5w+8U9fF/fvv9uz/+' \
			b'+dvHNvDp4398949/fvqh+/J78v7y4fN3P/z6s/p+//W/O98fkvMfH//444fW91vrS9l8+L7zfv7clvaPDz98Tv7fJFdE9wj4JXl//qn1/vTp838k/y///Pm7n375LQV//Om/kve/ukp+6rL58ad//CP5P3/8/Zes6sn7wz9///n/5vmTJwW///3DD//5sSX7' \
			b'w48/tsV9bKn+/sOnNpoY1Ub/z68tRcKg9osu/vufPv2a1fPj/2m5QgW3zPrp4w8f2wA17KeutN/++PxrCrW/bkv99edfP3WBX3750Av88Zf3xfWTnY+Fr68KeBr2uIr/1YU3VxqkkPgaTlb4stj5q14EQnX6Hf2gSVHslVS7IDGxeGIL54qdKehb565SrMa1' \
			b'EbuKPabGv0BUWJSTomw5igp1HsVezivgX9D6BKIpSpKIf6GhkuurPCqWeRR72WeKJ5SrYUJBJsc0eciU6uE49ln8i1R/A6a1USGPYi/7GmaPqRJ7qqsUq3FtxM4a8Xn8i1xkvOpF2TyKvexzlBU3UFV4zYurg7aRduIvr7Jg8mfxBo+dkGzl43z62rKH89V4' \
			b'FEL0aiQSGalnrfWMTRurcbGLaPoROyvZWyrQiojYCv8Cx6DNsiiRkjaWveRjiYgFie8O2Qb2cJ08/gV7pUESF/ZRA3BzMZPBEIqIWaDCgyP4d8QT20gz+oL1x6u+IH7nwziqC7pylEKisiDR4d04KoyjsqAdB3s/2Dm0W6nyyXIBPphSvMxCls+opYdWR1J0' \
			b'F9w56B5lRmy31NYssqRY4Amltcrj6RQMR6TzyxJSG/cT7py0AyszCUGZRJPSQJGDahkrHsGZt7my0ZdtfBfjEOO6GI8Y38UExIQUszMQ0BL/QmhpbKNiHsVe9tX4R3y8uuq87GNpKbufEJlWlNB7fKHUeBZc5BUKpKgEdxOugESKQ0wb9MJcn9SNOCzl1hCC' \
			b'SNSGghiuapNHa8QOCOgc/u2UGex1oJS+YbpRNQpF9C0MCHXWuq5JguI7trFIo14U+cTXXYU52LS5EtgDJKhYG1pfVB+gkz02eZCcRElSk2g8EdxvhYLRFx2Zxb+uF/RWkdAb/OMOUEVHvewr05dXGqRQ+uLqivriaxYmkh5mMBfgGDq4sRoujH7asASRxNSu' \
			b'qKmhSu5uiF8lAXLJ4UCfSJ+KezTqwahPoD6g8kUVmLFcTcJD8lM1SZFYDJjBTvpjwro6FDXlXhV1XdRN0ZTcFiRVBLqGfmzo16QGJPck2sQd0nJSNWqShpwtGkc9Co0laBTBKtfEoiEFYyUjSDeUk6GsDOUVmG72WsJZaihG6YZcKKpYVFVR1UXVFHVZ1Kao' \
			b'qX6GP47xiHpR6jWjqH7kXqOoyqIyRUW1ZCZQOWXDsEHjAC6YwwX3yvZ98aTkbuv6iffSfRGb5UF5E++feIdvieMcTVyXb418S9ENwpLH1ipHbJUGfA9oDmIjGF5jkGG0eWqPZMJdiq+R3GqzoNE4V/mx8P9qU6YTNpvwSdSp2Vh9ala3wh9UzqM+KxX4II2Q' \
			b'swocmmCM8qPlQV71qUprjYmOaEFGLO+iMIPCKqB1pfqOittUbysknaB4G1C8dacqQNvUoqNxFg+X+hspnwSzoOIKEp1Nh26lQy5q9w5xMug3bOowXLmB2EkbgDp0aQHDPTZz23E8z78oFSub3ST8tgyuNgaflsH1xuDTMrjZGHzSqZbOgC3mUEanWNolhjR5' \
			b'wphn6wxPOKJPoz+D8WyDBmmsNkEj0SCbSLwz0kYNmTfeiQf8TnmQppX1JoSnFcJQguFqOzHpWeuzUQNMqU+dkAW0U8CEJWDC8kQqIMl0khiAKo08LlNiG50jVlDiCuMvocz0BKOVh8el0VWt/IEk1ZCQ2qhFz6qcpacqfkSvFCE/MYCpFGJeMjPromkeLFOo' \
			b'fpCWWF1cxQAcEa1dlT1tuKB6VgDASuQWlcmr94ArpuPBsh6IJkzqaNfQmhy1n6i0A1BlN2brt088TSLmWqxc2W0t6risJW5arP5trD2yAbZhlso6Hz03Ht7MQOI2uTw2T5lhduuxTiu3ovS8Wr9x+sRjg2pj8ckBY2PxqTc8WAwWmGHk2bh5G276JjETKMy8' \
			b'oufG0ltgQBCennpCPrHJjXfGlGjPSqaBXQMk1neMfvQmyGveMMQj5o03U7ypNt7M8gbGlRPs+3LQXicFbDzPeO7cxpLBmmhQYUEHALuzLp/oMhts7mnpXrqljXHXvLNv44SIkDCCd99hEKiDCePSem2y5xvdiSpbbcSir5tta9hE6xqPNJrEyPxRMvWa98w8' \
			b'5tqHx1t72R4lGtCI3fBRVf6atyg9tkrzbiydQOv6qJk7gvReDyzJyUQsdwi/eJsMs+2SmeR1VirMGiweV+hC5jYcJsZiq9Fd6rIx7RYViy0qFltUrLSlUTtUdFgWFPqazvYHGwosgLCkDOyAm2Flna0q6oA3on994DtFDCT94Vcj3Lle6nGdpn74DHzS6BHX' \
			b'GB++UPO+NWhofQGVqdSUGptLqIzRHtheQGWYLovtZha7zORh0s4nvq2B+1pOEuRB/a/T0Zm7gvHcYeK7nSk5YY/N5GL4C+7rw+oTjeIbtAkz0+kSlOMRVtAviJtu6nhvREPb/uFYW01Es8nWqWXVTR3xdBPRbGHDj0SwRMq2w7a3Xx4TbsZt7fb2mw2gXjMz' \
			b'J1vOf8uzFQVAlyx/Vi1+PEPb0O8o7WPDJuW37UNq4DnVzcHC7NTC7CbOxhk/HR0mosVYp9EO0Q7GGafGGXfZZ5Su2fLkLtryJCYnt631yLQ5bQ1Br1FrDyDC307mbRaKLo2kzejSKzbCSO+CxQ4xA/Czwcg8YmwWobQRJVY69jLtWNzrWNynRSiMGT3GjB5j' \
			b'Rq9jRZ8GiX7bIn4zKNUpUerydVTeLenpN0F4fdnIR9Xy80OnCjJYQ/hqFlS1+Hq1+PoLmESTHKr+hTQUhP4F6F+A/uERkLjCtzWia8liG9/cbpRIGW1cvO3agINAUgYqphFiGiGm9DCFVSWOSFlpyuqRrVleM18q8KUSYIPVI53RtPxlb5GOuVSDnzV+V6ek' \
			b'9WNkXvP4Km0eXaVFvBtIvVxbzJcTlDI+KItrAk65gY8NgnwLX5Ogs0q4ahMgA429kCgrwFj+9S47J5IRlbOX+gNiCVc4Y1/LO6ot15BhWzS17irBxlIxaRPnePsuX3HHI3i+o5aH8HyzLd91yxfdUvmGdyjwdR180ypfs8onubkx+O5IvtKRb1zkKx75Aga+' \
			b'fYFvKOAz/Xygn0/zczPybYx8FSNfecH3XfAVD3y9A/OPeccywTe3StdDYZ6H840uPNDk6zL4YhvuVXgOQS1tecLCRn2eWrCNn+pnmbfCXL6dmeJ4WyifHqV6WW+obfjCb9xcztdLG7lym69e56u0+d7umu+6L+VfVez4Eny+G7/iS6T5I5fEF/KCAb7eveHb' \
			b'tPladytX5BdyxTTRvONbwxu+9dnIP77ZWm6it3IXOiUK/KtSQlQGXz5PVdwRS3Y1X7zPF4ZXfLt2ybTxz+W26kLfiUBUccmUoFG6iUm7qtIS5OUATE7DKSmWmmBXSYn0c34ZApPFN0/z9fJ8sXgtZfFV1ExlyVdyk6fycpk2rr7n1HLNeyEvQZCLtvludPrU' \
			b'fDU6pamZ/EbfccAc4XRCJbOFc+fimaf8paTgJNSgO74FPPKTi7V6WX7JnGROcCVLvryfr/Vm8plxJd+7T9/WzDi5PZ/bj8kx73lMykrYU0CTjWBm1JBhwKehUa6M9ub62IMzGY+1eLhPQ8NCLb0HDeW71m6kpXGFpgZmWRgqZ+CoxQoaWhUNYyUNp1HTABqp' \
			b'LqH926uuYanC3o+yMhk31Vcua7HOFn/6pwzJ4SmDcmWeEtj9Pxl4XjOT6kyBYxoGNDw/6fp5zG1SV97ObVplbvdWLdXnkKm0jCn2jVbcSL1LHujwjG007tBpU8VmArmKWQc5uPDGZphQDXDBdtjQLkZnC9SCFU7xIihmVMANvoi+hx1NhhmVYgSzl6d4McMG' \
			b'iucra1ZhBKXjXY68hr4UK/iQYYsXfgYzuL1thxsM2oIdlI5v4ODrN3o4wkNFUeAi+ago7uapNeVh5EE8lYeXNMy1sucYSJAPUETUQZGE49dBifyaWcDPHE4wr+o+I3gZkDV2Uqeyl4lUbJz31CchFPxAKRkTyeuJBKnyXE3ihF5kxOAFskt9GjxzIEMjKH4x' \
			b'dAlchcRoBSkNLYWqXiWMkLoYtEwiNiZix9il5Ch4IXkzLDUHs+CecodBbf9UpIC04injKUk4PR0jm2uRrczADUMTe8aAlqHZYihL5oIFcLZB2RyUMUNFPZlsDZS+GwbpEEhe0RU1ResEwUyOYB2AmfUApvg1hK+svBF0mQMOuJUC1u1NSxyvgmLVYP5jUnYd' \
			b'l7S+AlOKUgpSilEDiDIzEIWkCaIQWg5RHTnr8En5GZWuCXTSCid0UnDqyptCpjEg+fFQ6zLRaEOiWyIRMwvKp74pGLKAIdtzAkM2gyHbwZBdDUMWMGQHMJSXN4Ihe8AJDLUB6/amTeOloQ3GwD4pGKQs0soyBllgkAUGWWCQHWCQncEgZJcwCKHFGNS12EoM' \
			b'UmZGpWsCg5R5ikEWGJSVtwyDwoZB2+RuMQ5xRaCA6pvCoQgc6jvBoZjhUGcZYu9KHIrAoTjAoby8EQ6NSBpSKHa7FLBub9qmZUPCIakcS1wECrVJTfpJg++QtAI7KqN8zIAozgCRMk2BCKHFQJSRsw6IlJupvSeASLmnQBQBRFl5K6dpcUOkDZEWI1KNFxPb' \
			b'IvmmEAkmaqRonSBSnSFS3SFSvRqRaiBSPUCkvLwRIh1ygkhtwLq9aRMi1R0i1YpINRCpTWq0toxINRCpBiLVQKR6gEj1DCIhu4RICC1GpIycdYik3IxK1wQiKfcUkWogUlbeSkSqNkTaEGkxIjUFcKJIvilEaoBITc/tsA2sQ6SmQ6RmNSI1QKRmgEh5eSNE' \
			b'ag44QaQ2YN3etAmRmg6RGkWkBojUJjVa20ZLQdIK7KiM8jFDpGYGkfD7hEgILUakjJx1iKTcjErXBCJpvRSRGiBSVt5KRKr3L9KdMy65DZruC5r4BzBoJ59sGRB0kkcHUBY2baRrHQNUvgHHdjZtu9qmbWHTtgObdq+8IUAN6Jl0jFFdwLq9aRWjbGfTlvoZ' \
			b'zSlkSY1WuGnwHZJW4EiVGNphlJ0xamt2ilEaWopROTmrMCoxNCpdY4xK3ANGWRi18/JWYlSzYdSGUesxir+ETqqPi3LAKNfHKAeMcj0nGOUyjHIdRq3eKij5BXn0MCovb4RR7rATjGoDB9ImjHIdRjnFKAeMapMarTBjlANGOWCUA0a5AUa5GYxCdgmjEFqM' \
			b'URk56zBKGRqVrgmMUu4pRjlgVFbeSowy5QZSG0itBylfCLpAPHQPs8U0z/o+SHmAlO85ASmfgVS3u4m9K0EKm5vsYG9Tr7wRSPnDTkCqDVi3N20CqW4fk9V9TJJTyJIarTCDFPYwWWxhstjBZAcbmBCeACnlroIUQotBKiNnHUgpQ6PSNQFSyj0FKWxdystb' \
			b'C1Jm25K5odUt0CqyXIh2qq8USRG0ioJWspM54IHvXNTUrRPMylbwbLeCZ1ev4Fms4NnBCl6vvBFmjUgaO8GsPGzd3uRNy5gWtnQdz2Idr0tqtM4MW1jHs1jHs1jHs4N1PDuzjqfZJdhCaDFsZeSsgy3laZKACdhSBipsYR0vL28tbG07yTfYugVssSxgJ3ny' \
			b'UVH8jBYPIw8+bVgKbDnsJEfq1jFsuWwnuaQCbLnVG8klPxSYw1avvCFsDejh9vbNiMo4CFs38cOsUjFxJuGW011QDtvGu6RGK900+A5JKyXWKGs73HIz+8U1O8UtDS3FrZycVbiVmBqVrjFuJQYCtyRx0ytvLW65Dbc23LoFbhmWBdFO9TFuwcruYGV3mB/K' \
			b'A9+xxJieE9zKbO2us7W71bZ2B1u7G9jae+WNcMscdgJbedi6vckTbHXmdqfmdgdze5fUaJ0ZtmBudzC3O5jb3cDc7mbM7Zpdgi2EFsNWRs462FKeRqVrAra0zgpbMLfn5a2FrYnd5BtsbbC1GLYsC4Jop/oYtixgC7sX+MGwZQFb2G/ubM8JbGX7zV2339yt' \
			b'3m/usN/cDfab98obwZY97AS28rB1e5Mn2Op2nUsVDVgSQ5bUaJ0ZtrDt3GHbucO2czfYdu5mtp1rdgm2EFoMWxk562BLeRqVrgnYUgYqbGHbeV7eWtia2IC+wdYGW4thy7EUiHaqj2EL64UO64X8YNhygC2sGiJ16wS2slVD160autWrhg6rhm6watgrbwRb' \
			b'7rAT2MrDdn/yBFvdwqHThUOHhcMuqdE6M2xh4dBh4dBh4dANFg7dzMKhZpdgC6HFsJWRsw62lKdR6ZqALWWgwhYWDvPy1sLWxC71DbY22FoMW5HbX7RTfaVIhMAWbPIONnkHm7yDTX7gBLYym7zrbPJutU3ewSbvBjb5Xnkj2BqRNEFkLPth6/Ymb1rGtLCl' \
			b'NnkHm3yX1GidGbZgk3ewyTvY5N3AJu9mbPKaXYIthBbDVkbOOthSniYJmIAtZaDCFmzyeXlrYauavAPhwSHX1AWaR78YYQOwfYuKDQuGXI4g15Na3enOT15XbLCu2GBdscG6Ina9I3XrZF0x2/Vuu13vdvWud4td73a46x1EaIGjhcXmsKt0bTEn3Lp9v5Ar' \
			b'E3R5sdsCb3ULvMUW+C610ao3CEYkrcCbyiiDs+XFmS3wml1aXkRo8fJiRs665UXlbFS6JpYXtV66vIgt8Hl5a6Gs3qBsg7JjQBm3OCxfRG4KUGkexi8P45eH8cvD+OVh/ELq1jGU+cz45Tvjl19t/PIwfvmB8atX3hDJBvRMOr4zIZb9fKzb9wtBMrlpASEg' \
			b'mVcTmIcJrEtttOaEZB4mMA8TmIcJzA9MYH7GBKbZKZJpaCmS5eSsQrLE2ah0jZFMUyiSeZjA8vLWIllvp7x9sEh25Okk99p+g7J1hw+ZGaKo9GAq1SBmYBAzMIgZGMQMDGIGBjH8tHVyFjEziJnOIGZWG8QMDGJmYBDrlTc6i+gOOzmOmIft/uTpRGJnEDNq' \
			b'EDM161qNTEP2E6N155OJMIwZGMYMDGNmYBgzM4YxzS6dTERo8cnEjJx1JxOVt1HpGoNZYiTAzMAwlpe3EszsxI76JYelw30D2EO714rj6lvC1h1BFg/xHR/eMIesYg03vhh/1DdxdtphFokUrcOFobX+Xq1h3UzSrZ5JpuuH3XAqKS3ZfcYmseaAE3tYG7Bu' \
			b'b9r2WgdsrBeoaW+8co2ilZICsDKKVkbhyiheGQWs4caJmYkkCIDgd7c8KFlrrjR266eT0lwOhc9uoFBmqm2MZYwJoDSwkrUs7GMYMe8pznkSiFVRMGvbYL9NIG8zgawKr9Mj9fHsEfely0PecyGzxwqzxwqzx6rnZPZYZbPHqps9VqtnjxVmj9Vg9piXN5o9' \
			b'VoedTB3zsHV7kyt+iVfnjZXOGyvMG9ukRuvM88YK88YK88YK88ZqMG+sZuaN+CrNGxFaPG/MyFk3b1Ryo9I1MW9UBuq8scK8MStv7VDr/jfYyzti8pfAbOD14MCr5hYWHVUfg1cN8KoBXjXAqwZ41QCvuucEvOoMvOoOvOrV4FVjvqh3Q4iOMuNwfM5pkfw1' \
			b'pxzB2AInMJaHrdubPMFY3cFYrTBWA8bapEZrzzBWA8ZqwFgNGKsHMFbPwBiySzCG0GIYy8hZB2P4VRWVrgkYUwYqjNWAsay8tTC27bffAOw2ANYUHpPG5GMAwzKkxzKkxzKkxzKkxwQSqVsnAJZNHn03efSrJ48ey5B+MHfslTeCreawE9jKw9btTZ5gq1t/' \
			b'9Lr+6DF17JIarXOjBSFpBaZURjmbwdbMtFGzS7CF0GLYyshZB1vK06h0TcCW1kthC+uPeXlrYWvbb7/B1i1gK8jbWVk7k4/fp4hjQgHHhAKMXgHHhAKOCSF16xi2QnZMKHTHhMLqY0IBx4TC4JhQr7zRC7jMYcew1Qtbtze5wlbojgkFPSYUcEyoS2q0zgRb' \
			b'AQavAHtXgLkrDKxdYeaYkGansKWhpbCVk7MKthJPo9I1hq3EQMBWwDGhvLy1sLXtt3/osJWWqu4XvuSN0qKl6mP4wo6JAIN9wI6JgB0TATsmgu05ga9sx0TodkyE1TsmAnZMhMGOiV55I/iyh53AVx62bm/yBF/dXomgeyUC9kp0SY3WmeELeyUC9koE7JUI' \
			b'g70SYWavhGaX4AuhxfCVkZNqugbElLNRqZsAMc1SQQwG+rzUtSB2n3fE38uqokKUwJIt5l9PegcQdCPYOQrkBG4I0Sz1TawOcjzDTOg5gZnspaSSSmFm9YtJJT9ku//VpOGAE1xpA9btTZtAJRT915kufZ8pGDaBHMg+IQdCi5Gjq8pyuFDWzWx5T/kpVuDN' \
			b'pV05S99rY+/z0vYNIu4LIqoiYCUu+aYgAqtvSNE6gYhs9S10q29h9epbwOpbqA5BRHXACUS0Aev2pk0QUQ0goloKETMLapp9ggiEFkNEV5XlEIEfzEKE5qcQgYW0rpzFEDFxi/oGERcPEQ0vWIqeqG8KImAiRorWCURkJuLQmYjDahNxgIk4NIcgojngBCLa' \
			b'gHV70yaIaAYQ0SyFiBmrr2afIAKhxRDRVWU5ROAHsxCh+SlEwNrblbMYIiYuMb8ziHg0WxkvwZzLrQVzbvJNwEqECRcpWsewEjMTbuxMuHG1CTfChBsHJtxeeUOIGdAzdjsVRwSs25tWISaaYvyKzgjzbWKRVpYAJ8J2G2G7jbDdxgH4xBnbrWan4KOhpeDT' \
			b'Eb7SdpuYGZWuMQgl5gGEImy3eXnLQMjdcEv1BkKPDoQst5Zon/qmQAiG2Gh7TkAoM8TGzhAbVxtiIwyxcWCI7ZU3AiF7wAkItQHr9qZNIGSnQAhG2MQirSyDECywERbYCAtsHFhg44wFVrNLIITQYhDqWmwlCCkzo9I1AULKPAUh2F7z8haC0MQe6Q2ENhCa' \
			b'ACHHTSXap74pEMKhM6RonYBQdugsdofO4upDZxGHzuLg0FmvvBEIuQNOQKgN2P1pEwi5KRDCQbPEIq0sgxBOmUWcMos4ZRYHp8zizCkzzS6BEEKLQch15KwDIWVmVLomQEiZpyCEU2Z5eQtBaGLH8wZCGwhNgJAvRH5tkXxTIOQBQr7nBIR8BkK+AyG/GoRw' \
			b'iIwfPRDKyxuBkD/gBITagHV70yYQ8lMg5AFCyiKtLIOQBwh5gJAHCPkBCPkZEFLOKgghtBiEfEfOOhBSZkalawKElHkKQh4glJW3EIRkvzJhS0EAUZCuExw1/UtIQoKlMiFTSOBU3+vhV3tclFpxA8mNkIq5SemIA4ZYYIgHffSKQDCqvSH5M3waXNCMfktc' \
			b'OP552bXo5lYgXHkTlGPhJr0gRu2IaRxkVYTG74jcSho/Jis3t2QLglVogXBnJd1O7kDz+pPWMSDuLLJvQbEzfcfVpu8I03ccmL57ZY5Asf3GNUMCu+9YCdqAdbMJI0zhFQ6+xGYKG2EST+zTOjdaTgUiSzyUN70XFJNfbi/htUNeUXeaRvHSlBGgWTH7Gagq' \
			b'BVD+OACpls11KTtARexiQG26OiwFVIv3GCf+Cag206BKn5bQhKywtucF95D16Y4EWPE1NhSihiB0JU2vzNMdA8EE6PriegS5c0grMKu4KqCqiLoETqcW6ICcVDNW+nZ4lgPekkW1AZCtArEheK0BrWb5UGzvQlvZAZOAUg5EvFSkIMSNO0Chw+CTkCdBTYsz' \
			b'CWRueHh//9Iay9pOD+Tvsjdt9sFg0brYUNfXKfpQxVcdrxemLx8n8bn62WUz0eakx6zEPd1lPQwTemjuUBXbcUzzUBVygTIavgRwpJBLlTEfEkxpo4/nq5Het1rJDfLANXNhZxumNHOVVsYJrdwzFZnTyoVTjr2KSaI+VMx4JOX0Z6Ogy5ST4nnW1yqplytK' \
			b'7kVZ/erboG+isGGksMzUYyktM/2cFHeh0mIaZ1vlTVO5kRJXa4e4bEnoWw+O1btCg/kWITPXwy7dS3buw16zUJn9DXvb5crrY6fAPrvU/c563KS8YHgz0+v6eP49L5tZlva+1XJFrqZ74OJPEjeawBqZqdb3OVNth8e5ge+442S+eYNoMUSMIWrOadx8u0ns' \
			b'8TT53sbMopz55/jjZ8xNGDWtWDjPbjw91mYr7bN0PF38SWLzlIgTbW6K6wdsczrP6W1fTd2NVLVV0cqdv4Ye0c50zjPZnubxSsYNbEzFn9VTQl3WPWrf+9c9Fltis1yme4lqWPKzubGl6WH1lKNxbpRFwB234kUrpdYy3MLGRE19BtroCxZiov3+lHJqMfkU' \
			b'ikkQShr0yBWUlUoW63e8i+AeFTXeXQfKNHIu1a1V1q5S2fJk49eyPL7Ort4IMrUB5Nh6W55Fp4orwO9VcVn7uDlPoLa9F73fqJM1a16JtWYhJ6oGH0N33SrdNafT3Uxv+U0i9z4IPoXebjrrhvrKTD6PMfGJ1PV4qupXqaq9G1UNm6o+HlX1m6ouU9WwSlXd' \
			b'3ahq3FT18ahq2FR1marGM7A33b9e3se+pQu0JB1b5/hMx7kYd2+oY8WfJJFPGTxksaU6A3UjaVAL753r3dwxoRNadh+jHjKzd56NuvfTC7p7sOTevAus71InZw4PznaHRET/xN+ZdotrziIv2jsUVDXtg1NPXG/e/yzuNiVx74jcea+Orjw/vOxcjBVSgjJj' \
			b'1KPG8JQgUPrTO904tOnuI9DdZvRZobvNprv8/mHobrNfd6m1rutieLlIJVpaiX66kWaKWqqmTd6uMSX9jUg6pHcgtbbiY5VJ+gYXV4jANaUKGlcrlHuEqxOs1igxcW3DdEtxarwJzk2wtw48TqHK34xfQKmETwF45O1qDnYYMKX7zElRhGOykskUrWtZalO6' \
			b'6kb8NXM8NmXLZ3tTPscZVj8gdpsO6EYsT2h1Ira7m7J9plvOWkE64hWd8NqWWtWBTrVmmofak7SqVLf/6fdpWVOrIXVd/3UTiVjX9UwKjk7qiOR+x+L3SdLtbSm3NFouFq67OKkxawBZJoRrRl+IX2nYOIJhcblwnspYOCO3E6OjwFdxyAEnkpBNiO9EiAXn' \
			b'Tmqdu0Mhxs1R+NyXELv66U7edsd2b5aF6ulOBJnjgwh33IT7roTbXpJw2/ZzxsJdzQv3kVZzTiHf931mNN3G1oj1j60IN5B5sR/dzZLLlP2nvL3c4xrA6k5GKKB3j/xb2d1BX02ua1oarFTchIaesrxJvNlE/w4hXgTyHsW9OYK4N8jnTsS9WQ33U0LeTAv5' \
			b'cRfsjy3n53Q9wI3knSX6bhfVTzCy4ateq3vctrJU8EnM44x5fhPz04p5fQliXks9HoSYT66qnGAH1hEl/Wy2Nd5a4rnB72fH1JGlnm/yNmeyN3GN9E+udW3Sf0fSby9F+q3U5cFJ/2DJ8ZQbcDcFyBRA2ujeN80efeBzThvU16iBf5hqcE4HPG6uCtUFqoJU' \
			b'6qFqQ9i04f60ob5EbagfsDa0K7V3ckxpUwhVCBbO8zpidOzR0tkd6VujFVVxLfcf6349fpsUvqjpC371IsVjt6GV6Ka4tiUnJhF4f0XPJzt50yteZsY3jEd+LwCly68UNjZwPvIWDtPdE86nA0jwBjcENw2XtLNLsyWap/4kE4cXQE5kg5uP/UR+jg9BuOyv' \
			b'u9K46mIle9/LPo7e1ba3NNZHvhadb6ZK5wn1NWP6aq/3fCYEfySsXo//dx8/8SevPeAtBvR9g5ODRl4s1qQ3DAjl4ZaUM4gcJJ7AcOEfnwwZ/AmZcR2ZMy+rm6WU37TWUks/2PPHZ1nmv+UTI/QUmquDNPNL+9B7hP6m34PvBm1fuXfwfXuV3rlf6fv0mBqS' \
			b'GnmHHsXJu/PGHMnfW9e9h84X3bvm6vz9cu+5T536Y8Sqtesbf+Z/s/az/1fTede97we/kRas71DqmuJWf0JvczYSZ/pSx+eOTiZ5PJa7X8e75dsAD6Num6W0JlX87sSPpf6EDhUyeYW416+PLaXurAW1KlrHlIYijzmCC8fNboVD+9qjCCxr0yKZ5YnbrR1P' \
			b'q+a/Rr3chNzybr4TSm/dnKEAS2TPMZnlMPKIjie6p8t9yqHFVw7oD3WaC+U5FEdxyUownwSVDJtYQ6yr4tIdGvw4s6hBD7tQtuviiC7ZvuaToMLVJuEi4WzQvHCHBl80YwvhpvOdGVFvG6IVdzYfH3JsZ1ySrvcbNfSOv2HTbAqAF80m/BD+qrh0B0Ppovni' \
			b'zYU/b8zlilAXp3P50sbelODP1PTzMSoEL2lduEODH56PaiMfRSdSey7Tjal2McV+x+tYBxMtcWkNcH+q4Wqe8HSbC2tjueLSHRr88FT4vJTIF2fpwMxtyq2tFIpLd2jwePENbqhUU9dLGz4Wl+Gs4e0Sbk8SCMDiVeDzgE/e03SODsw8PL0/BTPTGvokQ/0S' \
			b'prriLh1r5ziWdXPmF2DuytXjO+LvRM8yz2dfLHG8gWxh0pu5XgGTpWFT0uEJ+9lzPBYPwYHd5uGzuy4eggO7F8++L2L/E+/7Xeyw57f7rPrxuqyXFzOZAk3pHldThuJSHJpv8RT+MpovFpfi0HyH9+heVPNVxaU4NN/hVfeLar66uBSH5qMJvI28QRfTJFen' \
			b'sA7i+SQEvwGIjww0zCVorafBfd7MxF3eAiivtPZ4z6a80Ac9rDfTqU0x+CC1HaXmFpNf2GL4sSVqwq8Gbo9y8AXSulDM7yHNpW6fjFDby0EQPqqUHVlqjxCNjw9Zq0ckQr8UFjQ+OSQ3REuRUlQSxRIi55SZkTefySEP27y/en/1/wFbw4Z7'

	_PARSER_TOP             = 'expr_commas'
	# _PARSER_CONFLICT_REDUCE = {'BAR'}

	_UPARTIAL = '\u2202' # \partial
	_USUM     = '\u2211' # \sum
	_UINTG    = '\u222b' # \int
	_UXSECT   = '\u2229' # &
	_UUNION   = '\u222a' # |
	_USYMDIFF = '\u2296' # ^^

	_LETTER   = fr'[a-zA-Z]'
	_LETTERU  = fr'[a-zA-Z_]'

	_VARTEX   = '(?:' + '|'.join (reversed (sorted (x.replace ('\\', '\\\\').replace ('+', '\\+').replace ('*', '\\*').replace ('^', '\\^') for x in AST.Var.TEX2PY))) + ')'
	_VARTEX1  = fr'(?:(\d)|({_LETTER})|(\\partial|\\infty))'
	_VARPY    = fr'(?:{_LETTER}(?:\w|\\_)*)'
	_VARUNI   = fr'(?:{"|".join (AST.Var.UNI2PY)})'
	_VAR      = fr'(?:{_VARPY}|{_VARTEX}(?!{_LETTERU})|{_VARUNI})'

	_STR      = r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY)))})"
	_FUNCTEX  = f"(?:{'|'.join (reversed (sorted (AST.Func.TEX)))})"

	TOKENS    = OrderedDict ([ # order matters
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LETTERU})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\$?(?:{_LETTER}|\\_)(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
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
		('CUP',          fr'\\cup(?!{_LETTERU})'),
		('OMINUS',       fr'\\ominus(?!{_LETTERU})'),
		('CAP',          fr'\\cap(?!{_LETTERU})'),
		('MAPSTO',       fr'\\mapsto(?!{_LETTERU})'),
		('EMPTYSET',     fr'\\emptyset(?!{_LETTERU})'),
		('SETMINUS',     fr'\\setminus(?!{_LETTERU})'),
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
		('FRAC',          r'\\frac(?!{_LETTERU})'),
		('BINOM2',       fr'\\binom\s*{_VARTEX1}\s*{_VARTEX1}'),
		('BINOM1',       fr'\\binom\s*{_VARTEX1}'),
		('BINOM',         r'\\binom(?!{_LETTERU})'),
		('IF',            r'if(?!{_LETTERU})'),
		('ELSE',          r'else(?!{_LETTERU})'),
		('INEQ',         fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)(?!{_LETTERU})|{"|".join (AST.Eq.UNI2PY)}'),
		('EQ',            r'='),
		('NUM',           r'(?:(\d*\.\d+)|(\d+\.?))((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))('*)"),
		('ATTR',         fr'\.(?:({_LETTERU}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"({_STR})|\\text\s*{{\s*({_STR})\s*}}"),
		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
		('COLON',         r'{:}|:'),
		('DBLBAR',        r'\|\|'),
		('DBLCARET',      r'\^\^'),
		('DBLAMP',        r'&&'),
		('CARET1',       fr'\^{_VARTEX1}'),
		('CARET',         r'\^'),
		('DBLSTAR',       r'\*\*'),
		('CURLYL',        r'{'),
		('CURLYR',        r'}'),
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('BRACKL',        r'\['),
		('BRACKR',        r'\]'),
		('SLASHCURLYL',   r'\\{'),
		('SLASHCURLYR',   r'\\}'),
		('SLASHBRACKL',   r'\\\['),
		('BAR',           r'\|'),
		('PLUS',          r'\+'),
		('MINUS',         r'-'),
		('STAR',          r'\*'),
		('DIVIDE',        r'/'),
		('EXCL',          r'!'),
		('AMP',           r'&'),
		('DBLSLASH',      r'\\\\'),
		('COMMA',         r','),
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('ignore',        r'\\[,:;]|\\?\s+|\\text\s*{\s*[^}]*\s*}'),
	])

	_PYGREEK_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.GREEK))) + ')'
	_PYMULTI_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.PY2TEXMULTI))) + ')'
	_VARPY_QUICK   = fr'(?:{_PYGREEK_QUICK}|{_LETTER})'
	_VAR_QUICK     = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK   = OrderedDict ([ # quick input mode different tokens
		('FUNC',         fr'(@|\%|{_FUNCPY})(?!\w|\\_)|\\({_FUNCTEX})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!
		('SQRT',          r'sqrt\b|\\sqrt'),
		('LOG',           r'log\b|\\log'),
		('LN',            r'ln\b|\\ln'),
		('LIM',          fr'\\lim'),
		('SUM',          fr'\\sum(?:\s*\\limits)?|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?|{_UINTG}'),
		('LEFT',         fr'\\left'),
		('RIGHT',        fr'\\right'),
		('CDOT',         fr'\\cdot'),
		('TO',           fr'\\to'),
		('CUP',          fr'\\cup'),
		('OMINUS',       fr'\\ominus'),
		('CAP',          fr'\\cap'),
		('MAPSTO',       fr'\\mapsto'),
		('EMPTYSET',     fr'\\emptyset'),
		('SETMINUS',     fr'\\setminus'),
		('INEQ',         fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)|{"|".join (AST.Eq.UNI2PY)}'),
		('VAR',          fr"(?:(?:(\\partial\s?|partial|{_UPARTIAL})|(d(?!elta)))({_VAR_QUICK})|(None|True|False|{_PYMULTI_QUICK}|{_VAR_QUICK}))('*)"),
	])

	TOKENS_LONG    = OrderedDict () # initialized in __init__()

	# grammar definition and implementation

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

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr_colon):                 return _expr_mapsto (expr_paren.strip (), expr_colon)
	def expr_mapsto_2      (self, expr_piece):                                     return expr_piece

	def expr_piece_1       (self, expr_ineq, IF, expr_eq, ELSE, expr_mapsto):      return _expr_piece (expr_ineq, expr_eq, expr_mapsto)
	def expr_piece_2       (self, expr_ineq, IF, expr_eq):                         return AST ('piece', ((expr_ineq, expr_eq),))
	def expr_piece_3       (self, expr_ineq):                                      return expr_ineq

	def expr_ineq_1        (self, expr_bor1, INEQ, expr_bor2):                     return AST ('=', AST.Eq.ANY2PY.get (INEQ.text.replace (' ', ''), INEQ.text.replace (' ', '')), expr_bor1, expr_bor2)
	def expr_ineq_2        (self, expr_bor):                                       return expr_bor

	def expr_bor_1         (self, expr_bor, DBLBAR, expr_bxor):                    return AST.flatcat ('||', expr_bor, expr_bxor)
	def expr_bor_2         (self, expr_bor, CUP, expr_bxor):                       return AST.flatcat ('||', expr_bor, expr_bxor)
	def expr_bor_3         (self, expr_bxor):                                      return expr_bxor

	def expr_bxor_1        (self, expr_bxor, DBLCARET, expr_band):                 return AST.flatcat ('^^', expr_bxor, expr_band)
	def expr_bxor_2        (self, expr_bxor, OMINUS, expr_band):                   return AST.flatcat ('^^', expr_bxor, expr_band)
	def expr_bxor_3        (self, expr_band):                                      return expr_band

	def expr_band_1        (self, expr_band, DBLAMP, expr_add):                    return AST.flatcat ('&&', expr_band, expr_add)
	def expr_band_2        (self, expr_band, CAP, expr_add):                       return AST.flatcat ('&&', expr_band, expr_add)
	def expr_band_3        (self, expr_add):                                       return expr_add

	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                  return AST.flatcat ('+', expr_add, _expr_neg (expr_mul_exp))
	def expr_add_3         (self, expr_add, SETMINUS, expr_mul_exp):               return AST.flatcat ('+', expr_add, _expr_neg (expr_mul_exp))
	def expr_add_4         (self, expr_mul_exp):                                   return expr_mul_exp

	def expr_mul_exp_1     (self, expr_mul_exp, CDOT, expr_neg):                   return _expr_mul_exp (expr_mul_exp, expr_neg)
	def expr_mul_exp_2     (self, expr_mul_exp, STAR, expr_neg):                   return _expr_mul_exp (expr_mul_exp, expr_neg)
	def expr_mul_exp_3     (self, expr_neg):                                       return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                return _expr_neg (expr_neg)
	def expr_neg_2         (self, expr_diff):                                      return expr_diff

	def expr_diff          (self, expr_div):                                       return _expr_diff (expr_div)

	def expr_div_1         (self, expr_div, DIVIDE, expr_mul_imp):                 return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2         (self, expr_div, DIVIDE, MINUS, expr_mul_imp):          return AST ('/', expr_div, _expr_neg (expr_mul_imp))
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

	def expr_frac_1        (self, FRAC, expr_binom1, expr_binom2):                 return AST ('/', expr_binom1.no_curlys, expr_binom2.no_curlys)
	def expr_frac_2        (self, FRAC1, expr_binom):                              return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_binom.no_curlys)
	def expr_frac_3        (self, FRAC2):                                          return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4        (self, expr_binom):                                     return expr_binom

	def expr_binom_1       (self, BINOM, expr_cases1, expr_cases2):                return AST ('func', 'binomial', (expr_cases1.no_curlys, expr_cases2.no_curlys))
	def expr_binom_2       (self, BINOM1, expr_cases):                             return AST ('func', 'binomial', (_ast_from_tok_digit_or_var (BINOM1), expr_cases.no_curlys))
	def expr_binom_3       (self, BINOM2):                                         return AST ('func', 'binomial', (_ast_from_tok_digit_or_var (BINOM2), _ast_from_tok_digit_or_var (BINOM2, 3)))
	def expr_binom_4       (self, expr_cases):                                     return expr_cases

	def expr_cases_1       (self, BEG_CASES, casess, END_CASES):                   return AST ('piece', casess)
	def expr_cases_2       (self, expr_mat):                                       return expr_mat
	def casess_1           (self, casessp, DBLSLASH):                              return casessp
	def casess_2           (self, casessp):                                        return casessp
	def casessp_1          (self, casessp, DBLSLASH, casessc):                     return casessp + (casessc,)
	def casessp_2          (self, casessc):                                        return (casessc,)
	def casessc_1          (self, expr1, AMP, expr2):                              return (expr1, expr2)
	def casessc_2          (self, expr, AMP):                                      return (expr, True)

	def expr_mat_1         (self, LEFT, BRACKL, BEG_MAT, mat_rows, END_MAT, RIGHT, BRACKR): return _expr_mat (mat_rows)
	def expr_mat_2         (self, BEG_MAT, mat_rows, END_MAT):                     return _expr_mat (mat_rows)
	def expr_mat_3         (self, BEG_BMAT, mat_rows, END_BMAT):                   return _expr_mat (mat_rows)
	def expr_mat_4         (self, BEG_VMAT, mat_rows, END_VMAT):                   return _expr_mat (mat_rows)
	def expr_mat_5         (self, BEG_PMAT, mat_rows, END_PMAT):                   return _expr_mat (mat_rows)
	def expr_mat_6         (self, expr_vec):                                       return expr_vec
	def mat_rows_1         (self, mat_row, DBLSLASH):                              return mat_row
	def mat_rows_2         (self, mat_row):                                        return mat_row
	def mat_rows_3         (self):                                                 return ()
	def mat_row_1          (self, mat_row, DBLSLASH, mat_col):                     return mat_row + (mat_col,)
	def mat_row_2          (self, mat_col):                                        return (mat_col,)
	def mat_col_1          (self, mat_col, AMP, expr):                             return mat_col + (expr,)
	def mat_col_2          (self, expr):                                           return (expr,)

	def expr_vec_1         (self, SLASHBRACKL, expr_commas, BRACKR):               return _expr_vec (expr_commas)
	def expr_vec_2         (self, expr_bracket):                                   return expr_bracket

	def expr_bracket_1     (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):       return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_2     (self, BRACKL, expr_commas, BRACKR):                    return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_3     (self, expr_curly):                                     return expr_curly

	def expr_curly_1       (self, LEFT, SLASHCURLYL, expr_commas, RIGHT, SLASHCURLYR): return _expr_curly (expr_commas, forceset = True)
	def expr_curly_2       (self, SLASHCURLYL, expr_commas, CURLYR):               return AST ('set', expr_commas.comma) if expr_commas.is_comma else AST ('set', (expr_commas,))
	def expr_curly_3       (self, CURLYL, expr_commas, CURLYR):                    return _expr_curly (expr_commas)
	def expr_curly_4       (self, expr_term):                                      return expr_term

	def expr_term_1        (self, expr_num):                                       return expr_num
	def expr_term_2        (self, expr_var):                                       return expr_var
	def expr_term_3        (self, STR):                                            return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_4        (self, SUB):                                            return AST ('@', '_') # for last expression variable
	def expr_term_5        (self, EMPTYSET):                                       return AST.SetEmpty

	def expr_num           (self, NUM):                                            return _expr_num (NUM)
	def expr_var           (self, VAR):                                            return _expr_var (VAR)

	def expr_sub_1         (self, SUB, expr_frac):                                 return expr_frac
	def expr_sub_2         (self, SUB1):                                           return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1       (self, DBLSTAR, expr_neg_func):                         return expr_neg_func
	def expr_super_3       (self, CARET, expr_frac):                               return expr_frac
	def expr_super_4       (self, CARET1):                                         return _ast_from_tok_digit_or_var (CARET1)

	def expr_neg_func_1    (self, MINUS, expr_neg_func):                           return _expr_neg (expr_neg_func)
	def expr_neg_func_2    (self, expr_func):                                      return expr_func

	def caret_or_dblstar_1 (self, DBLSTAR):                                        return '**'
	def caret_or_dblstar_2 (self, CARET):                                          return '^'

	#...............................................................................................
	# autocomplete means autocomplete AST tree so it can be rendered, not necessarily expression
	_AUTOCOMPLETE_SUBSTITUTE = {
		'CARET1'          : 'CARET',
		'SUB1'            : 'SUB',
		'FRAC2'           : 'FRAC',
		'FRAC1'           : 'FRAC',
		'expr_super'      : 'CARET',
		'caret_or_dblstar': 'CARET',
	}

	_AUTOCOMPLETE_CONTINUE = {
		'RIGHT'      : ' \\right',
		'COMMA'      : ',',
		'PARENL'     : '(',
		'PARENR'     : ')',
		'CURLYR'     : '}',
		'BRACKR'     : ']',
		'BAR'        : '|',
		'SLASHCURLYR': '\\}',
	}

	_AUTOCOMPLETE_COMMA_CLOSE = {
		'CURLYL'     : 'CURLYR',
		'PARENL'     : 'PARENR',
		'BRACKL'     : 'BRACKR',
		'SLASHCURLYL': 'CURLYR', # normal non-latex set closing, latex closing special cased
		'SLASHBRACKL': 'BRACKR',
	}

	def _insert_symbol (self, sym, tokinc = 0):
		tokidx       = self.tokidx
		self.tokidx += tokinc

		for sym in ((sym,) if isinstance (sym, str) else sym):
			if sym in self.TOKENS:
				self.tokens.insert (tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

				if self.autocompleting:
					if sym not in self._AUTOCOMPLETE_CONTINUE:
						self.autocompleting = False
					elif self.autocomplete and self.autocomplete [-1] == ' \\right':
						self.autocomplete [-1] = self.autocomplete [-1] + self._AUTOCOMPLETE_CONTINUE [sym]
					else:
						self.autocomplete.append (self._AUTOCOMPLETE_CONTINUE [sym])

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

		if self.tokens [self.tokidx - 1] == 'COMMA' and (self.stack [idx].sym not in {'CURLYL', 'PARENL'} or \
				not self.stack [-1].red.is_comma or self.stack [-1].red.comma.len > 1):
			self._mark_error ()

		if self.stack [idx - 1].sym == 'LEFT':
			return self._insert_symbol ('RIGHT')

		return self._insert_symbol (self._AUTOCOMPLETE_COMMA_CLOSE [self.stack [idx].sym])

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

		if pos and rule [1] [pos - 1] == 'expr_commas' and rule [0] != 'expr_abs':
			return self._parse_autocomplete_expr_commas (rule, pos)

		if pos >= len (rule [1]): # end of rule
			if rule [0] == 'expr_intg':
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
				res = (res [0].no_curlys.flat (),) + res [1:] if isinstance (res [0], AST) else res

				print ('parse:', res, file = sys.stderr)

			if len (rated) > 32:
				print (f'... total {len (rated)}', file = sys.stderr)

			print (file = sys.stderr)

		res = next (iter (rated)) [-1]

		return (res [0].no_curlys.flat (),) + res [1:] if isinstance (res [0], AST) else res

class sparser: # for single script
	Parser = Parser

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
# 	p = Parser ()
# 	a = p.parse (r'\left\{1')
# 	# a = sym.ast2spt (a)
# 	print (a)
