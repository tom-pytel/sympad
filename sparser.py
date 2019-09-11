# Builds expression tree from text, nodes are nested AST tuples.

import ast as py_ast
from collections import OrderedDict
import os
import re
import sys

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

class AST_MulExp (AST): # for isolating explicit multiplications from implicit mul grammar rewriting rules, appears only in this module
	op, is_mulexp = 'mulexp', True

	def _init (self, mul):
		self.mul = mul

	@staticmethod
	def to_mul (ast): # convert explicit multiplication ASTs to normal multiplication ASTs
		if not isinstance (ast, AST):
			return ast

		if ast.is_mulexp:
			return AST ('*', tuple (AST_MulExp.to_mul (a) for a in ast.mul))

		return AST (*tuple (AST_MulExp.to_mul (a) for a in ast))

AST.register_AST (AST_MulExp)

def _FUNC_name (FUNC):
	return AST.Func.TEX2PY_TRIGHINV.get (FUNC.grp [1], FUNC.grp [1]) if FUNC.grp [1] else \
			FUNC.grp [0] or FUNC.grp [2] or FUNC.grp [3].replace ('\\', '') or FUNC.text

def _ast_from_tok_digit_or_var (tok, i = 0, noerr = False):
	return AST ('#', tok.grp [i]) if tok.grp [i] else \
			AST ('@', AST.Var.ANY2PY.get (tok.grp [i + 2].replace (' ', ''), tok.grp [i + 1]) if tok.grp [i + 2] else tok.grp [i + 1])

def _ast_func_tuple_args (ast):
	ast = ast._strip (1)

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
			return AST ('=', lhs.lhs, ('lamb', rhs.stop, (lhs.rhs.mul [1], rhs.start)))

	elif lhs.is_comma:
		for i in range (lhs.comma.len - 1, -1, -1):
			if lhs.comma [i].is_mul:
				if lhs.comma [i].mul.len == 2 and lhs.comma [i].mul [0].is_var_lambda and lhs.comma [i].mul [1].is_var:
					ast = AST ('lamb', rhs.stop, (lhs.comma [i].mul [1], *lhs.comma [i + 1:], rhs.start))

					return AST (',', lhs.comma [:i] + (ast,)) if i else ast

			elif lhs.comma [i].is_ass:
				if lhs.comma [i].rhs.is_mul and lhs.comma [i].rhs.mul.len == 2 and lhs.comma [i].rhs.mul [0].is_var_lambda and lhs.comma [i].rhs.mul [1].is_var:
					ast = AST ('=', lhs.comma [i].lhs, ('lamb', rhs.stop, (lhs.comma [i].rhs.mul [1], *lhs.comma [i + 1:], rhs.start)))

					return AST (',', lhs.comma [:i] + (ast,)) if i else ast

			if not lhs.comma [i].is_var:
				break

	return AST.flatcat (',', lhs, rhs)

def _expr_colon (lhs, rhs):
	if lhs.is_ass:
		l, wrap_ass = lhs.rhs, lambda rhs, lhs = lhs.lhs: AST ('=', lhs, rhs)
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

def _expr_cmp (lhs, CMP, rhs):
	cmp = AST.Cmp.ANY2PY.get (CMP.text.replace (' ', ''), CMP.text.replace (' ', ''))

	if lhs.is_cmp:
		return AST ('<>', lhs.lhs, lhs.cmp + ((cmp, rhs),))
	else:
		return AST ('<>', lhs, ((cmp, rhs),))

def _expr_mul (expr): # ONLY FOR CONSISTENCY! pull negative(s) out of first term of nested curly/multiplication
	mcs = lambda ast: ast
	ast = expr
	mul = False

	while 1:
		if ast.is_curly:
			mcs = lambda ast, mcs = mcs: mcs (AST ('{', ast))
			ast = ast.curly

			continue

		elif ast.is_mul or ast.is_mulexp:
			mcs = lambda ast, mcs = mcs, op = ast.op, mul = ast.mul: mcs (AST (op, (ast,) + mul [1:]))
			ast = ast.mul [0]
			mul = True

			continue

		elif ast.is_minus:
			mcs = lambda ast, mcs = mcs: AST ('-', mcs (ast))
			ast = ast.minus

			continue

		elif ast.is_num_neg:
			if mul:
				return AST ('-', mcs (ast.neg ()))

		break

	if mul:
		return mcs (ast)

	return expr

def _expr_neg (expr):
	return expr.neg (stack = True)

def _expr_mul_imp (lhs, rhs, user_funcs = {}): # rewrite certain cases of adjacent terms not handled by grammar
	ast         = None
	arg, wrap   = _ast_func_reorder (rhs)
	last, wrapl = lhs, lambda ast: ast

	while 1:
		if last.is_mul:
			last, wrapl = last.mul [-1], lambda ast, last = last: AST ('*', last.mul [:-1] + (ast,))
		elif last.is_pow:
			last, wrapl = last.exp, lambda ast, last = last, wrapl = wrapl: wrapl (AST ('^', last.base, ast))

		elif last.is_minus:
			last, neg = last._strip_minus (retneg = True)
			wrapl     = lambda ast, last = last, wrapl = wrapl, neg = neg: wrapl (neg (ast))

		else:
			break

	if last.is_attr: # {x.y} *imp* () -> x.y(), x.{y.z} -> {x.y}.z
		if last.is_attr_var:
			if arg.is_paren:
				ast = wrap (AST ('.', last.obj, last.attr, _ast_func_tuple_args (arg)))
			elif rhs.is_attr:
				ast = AST ('.', _expr_mul_imp (last, rhs.obj), rhs.attr)

	elif last.is_pow: # {x^y.z} *imp* () -> x^{y.z()}
		if last.exp.is_attr_var:
			if arg.is_paren:
				ast = AST ('^', last.base, wrap (AST ('.', last.exp.obj, last.exp.attr, _ast_func_tuple_args (arg))))
			elif rhs.is_attr:
				ast = AST ('^', last.base, ('.', _expr_mul_imp (last.exp, rhs.obj), rhs.attr))

	elif last.is_var: # user_func *imp* () -> user_func (), var (tuple) -> func ()
		if last.var in user_funcs or arg.strip_paren.is_comma:
			if arg.is_paren:
				ast = wrap (AST ('func', last.var, _ast_func_tuple_args (arg)))
			else:
				ast = wrap (AST ('func', last.var, (arg,)))

	if arg.is_brack: # x * [y] -> x [y]
		if not arg.brack:
			raise SyntaxError ('missing index')

		if last.is_num_neg: # really silly, trying to index negative number, will fail but rewrite to neg of idx of pos number for consistency of parsing
			ast = AST ('-', wrap (AST ('idx', last.neg (), arg.brack)))
		else:
			ast = wrap (AST ('idx', last, arg.brack))

	if ast:
		return wrapl (ast)

	return AST.flatcat ('*', lhs, rhs)

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast.numer.is_diff_or_part_solo:
			p = 1
			v = ast.numer

		elif ast.numer.is_pow and ast.numer.base.is_diff_or_part_solo and ast.numer.exp.no_curlys.is_num_pos_int:
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
			elif n.is_pow and ast_dv_check (n.base) and n.exp.no_curlys.is_num_pos_int:
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
					return AST ('diff', _expr_mul (ns [-1]), tuple (ds))
				else:
					return AST ('diff', _expr_mul (AST ('*', ns [i + 1:])), tuple (ds))

		return None # raise SyntaxError?

	# start here
	if ast.is_div: # this part handles d/dx
		diff = _interpret_divide (ast)

		if diff and diff [1]:
			return diff

	elif ast.is_mul: # this part needed to handle \frac{d}{dx}
		tail = []
		end  = ast.mul.len

		for i in range (end - 1, -1, -1):
			if ast.mul [i].is_div:
				diff = _interpret_divide (ast.mul [i])

				if diff:
					if diff.expr:
						if i < end - 1:
							tail [0 : 0] = ast.mul [i + 1 : end]

						tail.insert (0, diff)

					elif i < end - 1:
						tail.insert (0, AST ('diff', _expr_mul (ast.mul [i + 1] if i == end - 2 else AST ('*', ast.mul [i + 1 : end])), diff.dvs))

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
			ast2, neg = ast.intg._strip_minus (retneg = True)
			ast2, dv  = _ast_strip_tail_differential (ast2)

			if dv:
				if ast2:
					return (AST ('intg', neg (ast2), dv, *ast [3:]), ast.dv)
				elif neg.has_neg:
					return (AST ('intg', neg (AST.One), dv, *ast [3:]), ast.dv)
				else:
					return (AST ('intg', None, dv, *ast [3:]), ast.dv)

	elif ast.is_diff:
		ast2, neg = ast.diff._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			if ast2:
				return (AST ('diff', neg (ast2), ast.dvs), dv)
			elif ast.dvs.len == 1:
				return (neg (AST ('/', ('@', ast.diff_type or 'd'), ast.dvs [0])), dv)
			else:
				return (neg (AST ('/', ('@', ast.diff_type or 'd'), ('*', ast.dvs))), dv)

	elif ast.is_div:
		ast2, neg = ast.denom._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('/', ast.numer, neg (ast2)), dv

		ast2, neg = ast.numer._strip_minus (retneg = True)

		if dv:
			return AST ('/', neg (ast2) if ast2 else neg (AST.One), ast.denom), dv

	elif ast.is_mul or ast.is_mulexp:
		ast2, neg = ast.mul [-1]._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv:
			if ast2:
				return (AST (ast.op, ast.mul [:-1] + (neg (ast2),)), dv)
			elif ast.mul.len > 2:
				return (neg (AST (ast.op, ast.mul [:-1])), dv)
			else:
				return (neg (ast.mul [0]), dv)

	elif ast.is_add:
		ast2, neg = ast.add [-1]._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('+', ast.add [:-1] + (neg (ast2),)), dv

	return ast, None

def _expr_intg (ast, from_to = ()): # find differential for integration if present in ast and return integral ast
	ast, neg = ast._strip_minus (retneg = True)
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

	return wrap (AST (*(args [:iparm] + ((_ast_func_tuple_args (ast) if args [0] == 'func' else ast._strip (strip)),) + args [iparm + 1:])))

def _expr_func_func (FUNC, expr_neg_func, expr_super = None):
	func = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC

	if expr_super is None:
		return _expr_func (2, 'func', func, expr_neg_func)
	elif expr_super.no_curlys != AST.NegOne or not AST ('func', func, ()).is_trigh_func_noninv:
		return AST ('^', _expr_func_func (FUNC, expr_neg_func), expr_super)
	else:
		return _expr_func_func (f'a{func}', expr_neg_func)

def _expr_subs (expr_commas, subsvars):
	if len (subsvars) == 1:
		return AST ('func', 'Subs', (expr_commas, subsvars [0] [0], subsvars [0] [1]))
	else:
		return AST ('func', 'Subs', (expr_commas, ('(', (',', tuple (sv [0] for sv in subsvars))), ('(', (',', tuple (sv [1] for sv in subsvars)))))

def _expr_mat (mat_rows):
	if not mat_rows:
		return AST.MatEmpty
	elif len (mat_rows [0]) > 1:
		return AST ('mat', mat_rows)
	else:
		return AST ('mat', tuple ((c [0],) for c in mat_rows))

def _expr_vec (ast):
	e = ast.comma if ast.is_comma else (ast,)

	if all (c.is_brack for c in e):
		if len (e) == 0:
			return AST.MatEmpty

		elif len (e) == 1 or len (set (c.brack.len for c in e)) == 1:
			if e [0].brack.len == 1:
				return AST ('mat', tuple ((c.brack [0],) for c in e))
			elif e [0].brack.len:
				return AST ('mat', tuple (c.brack for c in e))
			else:
				return AST.MatEmpty

		elif e [-1].brack.len < e [0].brack.len:
			raise lalr1.Incomplete (AST ('mat', tuple (c.brack for c in e [:-1]) + (e [-1].brack + (AST.VarNull,) * (e [0].brack.len - e [-1].brack.len),)))

	return AST ('mat', tuple ((c,) for c in e))

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
			b'eJztfW2P3LaS7p+5wPEAaqD5Lvqb4zhnjbWdbJwc7MIIAsfHZxHcJA5sJ/csDva/X1Y9RZFSS93STHdPz4wwnJZEUWSxWPXwrUg+evOX//P+t7//pfnL069ffP0qXV88++q7dPnmybfPXr1IN199++SpXJRcdbp+8fzV1y/zVeUbLRF8+TXF8Yp/v3j21x+f' \
			b'Pnn97LXcv3ySfb8ot38rt9/g9vWLJ6//7YuU2r8TFd0Nez/9/tsX/0VP3c3r776l3++/SL/PXn7z3X+9fsYUfE80/u0JvXz5/NX3RMPzV9/9lch8/pK/4N//+JZCv+D8f01vv/r+FeX6C/7y6dcvXz7JPCGPb5//9d++y8l/m8mjmy+/eMEUEhn/kX6evPyG' \
			b'bl99Kdmmuy/K7d/KrWT72YvXz8QnM43i/A6EJAIo0Msn37z+7muK/jvO97P/fPoiv6ay+PL5355/SdE8RUHI59+8YAYk1mRe/OfrZ085wJfPv/oqXb9/9ZyF4CmT/eTVl8QvevE1fc9JJh6rXjkI41MaT/893X7646dPf779+OnP6v5Tun/39uP7zz9++Pjj' \
			b'33/65dPntx+r1+k2Xd5ysPf//D0F+fnPX/P9pz9+f/8xP/z2/r9//Mcfv70rL39Kt7++/fzjuw+/yN3HD/+v3CHlT+8/fXrX3f3e3eVo3v5Ubj9/7lL7x9t3n/P97xwrvHsEdIT+8nN3+/Nvn/873//6xy8//vzr71XWyu0//lFlrP6AbvLzn29L9ktqEio/' \
			b'fn7/sXv19u9/z7fv/vj4y//kh39+el/y89PHt+/+7/vu8VNNzJ/vu/z98dvPH37r0nzbhX9XcsSs7Cj8UKL8o+Lqbx1JP/3824eO1A+F14mejtc/v3/3vntIclNR8Punzx+6WLsS7Gj58Esh992HX39923v49JcfmjePNs42Nl41fOO2dGM1/ZjGbq/kMT3x' \
			b'naWfhj2ueh54Mvm79N5mL7rlUBvHV9U80o1Jj6oxId1cZV/x6zw2gW60xY9rm432V7WX9jteLtZedJvulMaPpwQQfXqiW8p1+vcNJYfPHN0QAVv8OMkb5Unxp4nUkL429H+Vfdr6KcqVvIgSzrJqc5bjVfYVv85jo/kDlYgiChOjbXslPhvF/FAeP57Sl5ee' \
			b'b9MdF0CT4gEp8pjvK3+Fy4ZZoPnfuPxa0w3FK/5IJBEnnghkOFNRMuVj5yt+bQm27XtsNEuCIXo4TqPx4xIJTsglIpgKR9zz3Qun8gsT8eMkUylZy/Kb/Kmkif/4Jnm46sHjQh70XUiit83FQ5EgK+K/cdsdr/pR7YZQ/UcqyHbHa/iR7j+ancf+BxuDAk9y' \
			b'rwMSoAAa4p29y+PGgOdJsnTbaN1QoaQ7Tx+nskkBoO0TIRgd2pkBU3H1A24M85xENzSuk8NUqpwLFURBSKmsaxJqFD2hl51/8bHwscXHwccVHw8fn302ijWTcQN3ET/Od9R2XqH2olvKisHPRlBKbuluCynNeU4sMSxeNuKFFJ2luKDIqYxYRiULJLLMpVRw' \
			b'muNUW/x40m/AkNryLfORYDRDCrJIksI++XHDuWwlGtKuxoaMdLW3eKRnpr7FTxKpK3lO6sW0bfHjCQ5AEpc+k5SE8FESh43kNEkESpcwYdvhfZYYZzIkMJRCPJOEJG7nELoxIteZrT5zL3k+skVZ6ZHCdU8OyJbypkN318qdVvlG5xsAXosfnzKhkSLBgmam' \
			b'kKwzkQnfHrEwdRJKlQ6i1PjxRRWJISjOxHn+qarPIAhsPX64lglX4kW3dOfyyyt5TE/5BfKbOBy24JnLXHWEGZw/RxG4LgJGWY7A+fyCg4pX/koj01Q1JuRMbYU3W3qgSskQUKavUmkm7U6lQiXbNpHqg0RFCE1IyrxNqLpV6T/p9jbVOdtUF20doXxKJelX' \
			b'wpOYXPrENFSdOwKOxFkCglT9qSQX0TUxxZ5SStxO4mCaEJt227SqaXXTmqZNcWr6d+k/faopXfpPsSY9SmWWiKL/FEdqrTAckA6kuJPGJcxIIKEUhUnEphpYpfJSiZ42JUzR+aZNLjRtIjRV7FQhp+ZSaig1bWxiympyqgm6CYk02wTXBIowRZ3iTq0Rz7qS' \
			b'BCrV16n9kZQtaXNCSp+kLKW6TYG3iROmIdhUJPlJVRTR8UPzaEv19JtHiekkXYnxdEmcV6k0Hll5ayy8HS4tv03eHs+BLms5nbScIkpC8ZWaOyiCwLynlhwXGLGag2255B4FCY5QFsWo8sdcIlerwp21IJlzKCMjxZGLBeoVs3o5fu7xUTgI3o1xDdzquNTj' \
			b'zghHwI5ElRPBcf6MaQakGSGkJCScb818OV262iNdbU+cDspTZZ1kJV217ZzaRlxfmX52iNMCcdavzD8785URWGX4EWYwG7pMS2ZzHut8pTzcFvG9wq8L/CzVUWKYNGd1bt5yG8o0KZNN26R8rLJ6ZFk1SvoX0hLiGpmbAO0KHGevKluWd0W9POrZUbeOCoY6' \
			b'f1RQiSMry4/NcrWy/Nws1yvLz81ys7L8vBVra6XPmfug2zyooDAWtFat5+0QdeNyMtahZYRV53E9NDYfKWkJyZCQk1Kzbi20cxealaFVGS2KXFU/qC7RI6WyuIp0aiVX6WO2gJcWPacWI3iPYh6UFu8W45p5UACPNuZhTsTdclL3lpVRplKCDMyj4cfEqbUD' \
			b'ziwKIiABGBiAgcHJ1AaESWVoZGwk8YGIevDVC1+JTkou8TClYO8yX9488piV8+Y+5g3F6QEk3vfU4p5lFbDoGf+QnzqHdztvUlFs/UBGMc+InDuTIR+FzrXJD2zQkSehNWaf9TqffOpOGVnJYE5/ZfbJxzk9MZln79N15eqRRDgxcpXd08+gJhbqtfN5btlm' \
			b'qCDLnZX35+a9tSvTbwFmVqaf3xZNScMksU+LLVq6rlw+qmgn9hBTmSWrPcbsPqXjrsmZEhuxlCUTxdxw52p4LbvZ7NSMJye0rUTvlRLAlS+Wi4ssnwTVZFBi0hj6BzGdpv4wx7QW6z6umy0YiwFaGZ8FG7P9MIa4uslGVCcrM8dEmGsFsrqBsMrqCiWrKniK' \
			b'HFyU5Rc8Wc4iazAg3ELqW+hAa7LUo7pZmV3PZKEj9YZnXok7K1cgWsSMh8wA+9AZ4B40A8iygpsM0hFquQXxoFjwhubtH16mLdcDTjVO3/O8kmmFFtsDvTM5F9CImDA8UrkNjTm62zBBUZ1VgIZVgIZVgOamEACczQB4vHQ1HD/7KJIX7PQsXvdgol7B5ute' \
			b'5CTcltpKhzCae8HKR1Esar2+F0JOxkRQWntP8iMjdd7dk/xIf9W39yM/RJqGDZCG6Y+Y+tCuKFRBX/GuTnRJ9bKRYTtzhaFZg4GSdRXBWSt2jYKwUjpbuSgUC/HUyJyRuZJ5DlMW8tP4vTzSRUvoxFlcEbdHZEZ8ZQUgjTTCH609bqqvCzCPPzWF3i86vStv' \
			b'jzyjrbPitGLn2GYgM3nEV8tILw9Jrih2mnIwapXvE6wxA4K3QO7W5FpBKoG8wkmhFsHIu5kaaSBfA18DX64dcGk9LlIdRcTneGDgIQzgpLzqB7BGhgeozDo3k3vQMjEYoBkBmhFYJbruPXsqmssWQYGO8dziD7wqBo0tL9PkAaPdaFZ5qK5HzB7K5tuu9W2l' \
			b'9W3zNCXahBZtQos2oc1tQbtaNh9vDxfN7AXgudxcEIgs08BAYKe64V07PZIbDKJEwSV6bR4/5Y+s7ZZT2avcVLkP3c5t40SMXW57QYwdxNhBjHExuCZynKieA88ceObWZsQJduhi9g7XDK1GuOfHHQclCbx/NXas81Qfp/zRlqClmkmJeyiGh2JQsKYrTv/A' \
			b'ZhNZWg04FwRA+GpasdyJ3SRWeGC8eUNSEiAlgascWOF1q3kzw1pUcjBeop1naU9a2pDWmiJ6xMEWktcizlb4jDrSynSl7GfL33OiVlaspw/jwysB9+AyzTJhs0xokQV9VYsSVQ8QIr5SAAxkbps36Rve+o1GHWn7t8g5MozgXGOkdFOSlBdPpFEGuL5ARYVK' \
			b'S4gNxHTaMJz7quBVzZDCZsMMDsPyQP2WSityBmnDVM5yVQfxUHgQnFaiNOk9sYl2XKDtFminBeo1U2+S1uLS0nlaN0+L5mmNOS0wp/XYtAqbFivTSmUqZFqYT4vyiWG04TDVtWRMSyPytIMVbalEe/xQedGOELQdBO0FQRs/UJeVts6gcqGdban2pQVltPJg' \
			b'S3uwJwbSogPqoVDvhGUo+ZOE8O7pyZ8Kn8xzCRvIxNfS7vUpHprz99tUYDgDhPY8p33caSd52pe+4X3j6ZCLwNvO03kcW9qYnDZ8pwB8kEfD+7bz0QyaQtBO8ZH2gOdDIJpNS5vmcxDNsdBHdLADH9JAW7TTzvl8HgVSo63MNX2XPon0npJInNhEXc5QSEW5' \
			b'CUQYf0zngVAESZHoaAPez522RMepBg1vmE5HjUSH7CR+bhJfN0EJ0Z7PoaA0Uig6tYO286ezEkg/eZd2IosOnuADUOhTfkmfbSnilnd15/MLiHY6M4A2h+cTMjhXlo9f2KQS37SUenrRUsAt842zGeXAEkoB5yRsWso6bUAfeaf9De1Zr8Aw4j8RSr5ENPGA' \
			b'qKAzWXDWw4bwg04qoCNgcCrBlvabJ+r5ZA0+gIOYmHyTaG6C+4G0mHS3p7dqWnUzDAFeig7brMaqr8n+aMo8wLn9uq1n6vdd0W0zot/qgI47YpwbqrWbodiOQ6WE3a56u6LgoyruTqnknGZScNf9HVR1N1vZ75qityPK7g6oe/Mv+5jw3j0mxA8hXdz/cuPy' \
			b'DRVdm3W/63gF6TCipTJQfxqfRq+v38skKAAO2IIAaEMdBgFdcABNptEGF2HCTtundAS30nYjiIjSrnLSSut6zdIcKk2hnX4qd0szltjBVHru4400vBln/ABrnGCMHuAKYUqKgzY46nCFgNcP8EUdwJWtYEuKn2yIDmLMdgbOxApnvGCNHuBNCkurvjrcoeYs' \
			b'8AZSyZMNBDV8CXyhXntkvOlCS3AaUmj5lkbttj1HyIPALQOOKi0K0tMleEPhSUraPuLEtrgd9BlQU7soufP5TjNG9uIrEZNsdg8CVi2rLGeZAAsv4SkfWRBlcEGWkwBxzisgA9MVYKsHWR0bBa8yU2vU0mEvVhWyFRN6CLUokABXnMAtocJFFEaU2CvwkhQ7' \
			b'CPPbx1RdJCl4DLmJ6jGBaBLjxylvhGemw7Oub8VtGWnI3AUYEwwzMgJ3XAxb8WsPfqmGjwDTVCh8R+2l3FSSZlIXSONKrWV4GSV3nWPYUhVsqQ628O182KLwkUW6B1u91HZga4egXnAHKhLbWuR6PFjsZajuS6mcbvcacsmQxS8MLkiIZEYNIEvtgSy8zpAl' \
			b'6S+ALFWRNQuyVAdZoGsEsoRzKMoQJfYKsiTEDmTtIpUdtLzuLkyt7awz4xQxABprJ0Aqh5AgMqViAVK25xikbAVStoCUXQhSFiBlByBVp7YDUnafY5CyXatqPExUdW6AUCAdV1+/Z7G0gCj0CvmCZEhc7ACi7B6IQhwZooSAJRBVkTULomyBKDsBUcI3FGSI' \
			b'EnsNUQixpFXlVqxasep6WEUZg+76CazKISQIYRW8CKt8zzFW+QqrfMGqheNOFJ645AdYVae2g1V+n2Os8gWrRsNEVedGsMoLVnlgVfeexdIDqzywygOrMI4FllZY5fdglRAnWCUELMGqiqxZWOULVvkJrBK+oSBDlNhrrEKIJVjlV6xasep6WEVEQ3fDBFbl' \
			b'EBKEsApehFWh5xirQoVVoWBVWIhVAVgVBlhVp7aDVWGfY6wKBatGw0RV50awKghWBWBV957FMgCrArAqAKsCsGow7K7CHqxC8IxVQsASrKrImoVVoWBVmMAq4RsKMkSJvcYqhFiCVWF69P0OIVYZd19B6/ygxZZ9rMQRoKUw6K5iH7pyOAlI0AUvgq7Ycwxd' \
			b'sYKuWKArLoSuCOiKA+iqU9uBrnjAMXqVsfbxMFHVGRL0ymPtEejVvWf5jECvCPSKQK8I9IoD9Ip70AtRZvQSApagV0XWLPSKBb3iBHoJ33AJOfYaveTVAvRqV/Ra0etm6EWRYfBZy3g7XcnyTfXQqwsnAWk3LngZJXedI/TS1ai7LqPueuGou8aoux6MuvdS' \
			b'G6KX3iFoSJ8DIYJe42FiL0NAL1AvqdbvST41ht01ht01ht01ht31YNhd7xl2l9eCXpmABehVkzUHvXQZdtcTw+6ZbyjLECX2Cr0kxBL0iit6reh1Q/SiiKDEWtALfUa+VOiVw8mV0Au3Rsld5xi9dIVeuqCXXoheGuilB+hVp7aDXocco5cu6DUaJqo6Q4Je' \
			b'MmMoVpjlPaOXBnppoJcGemmglx6gl96DXogyo5cQsAS9KrJmoZcu6KUn0Ev4hrIMUWKv0QshlqCX2q6GWyuOHQvHbJPVWSYU6Uo4ZhnH2NTR4+KaLrQEVyZ7UcK25xjNqslFXSYX9cLJRY3JRT2YXOyltoNm9oBjNMNd4cBIsKjqPAmgyRSjxhRjec+AhilG' \
			b'jSlGjSlGjSlGPZhi1HumGDNxAmhCwBJAq8iaBWhlilFPTDFm1qE4Q5TYa0BDiEWApgBoYCiJWcho1Ycqwil/aAxdAQVIgztNhYayFkFLSPJjcxbH5varre0K2ceCbBIJdJyNdJwNOs4GHWe6pMj54poutASnZWTwwqV2BNmm6j6b0n02C7vPBt1nM+g+91Ib' \
			b'QvYuQUP6nM93AtnjwWIvT4BsIz1ogx50eU+CatCDNuhBG/SgDXrQZtCDNnt60Jk4QHYmYAFk12TNgWxTetBmogedWYfiDFFiryBbQiyCbLMC2gpoxwI0R8LA6iwrlQzWKfEl8IUAzQHQcmgJToAGLxIt13MMaK4CtLJSCd8uADQHQHMDQKtT2wG0/nsq0SGB' \
			b'zue7jGg7YThlVWdKEM0JomG5U3nPiOaAaA6I5oBoDojmBojm9iCaECeIJgQsQbSKrFmI5gqiuQlEE9ahPEOU2GtEQ4hFiDY0yl0RbUW0ayOaJ0lgdRbTN16h3OIS+KIRRkNoxAzOiBmceJFo+Z5jRKvM4EwxgzMLzeAMzODMwAyul9oOovkDjgFNcmYzB0aC' \
			b'RVXnSQBNjOEMjOHKewY0GMMZGMMZGMMZGMOZgTGc2WMMl4kTQBMClgBaRdYsQCvGcGbCGC6zDsUZosReAxpCLAK0oeXuCmgroF0b0AKJAauz2MfRlQAtANAw48EX13ShJTgBGrxItELPMaBVtnKm2MqZhbZyBrZyZmAr10ttB9DCAceAJhm0mQMjwaKq8ySA' \
			b'JhZzBhZz5T0DGizmDCzmDCzmDCzmzMBizuyxmMvECaAJAUsArSJrFqAVizkzYTGXWYfiDFFirwENIRYB2tC8dwW0FdCuDWgtyQCrs2x7Q1cHX8cCwoDWAtByaAlOgAYvEq225xjQ2grQ2gJoCxesGyxYN4MF673UdgCtPeAY0HCXAW00WFR1ngTQWgG0FoDW' \
			b'vWdAw4J1gwXrBgvWDRasm8GCdTxPAJoQJ4AmBCwBtIqsWYBWdtowEwvWM+tQnCFK7DWgIcQiQNtjA7wC2gpoiwCNih6zAlZmBSxmBSxmBSxmBSxmBbrQEjxpk3gZJXedI0Cz1ayALbMCduGsgMWsgB3MCvRSGwKa3SFoSJ/z+U4AbTxY7OUJgGZlVsBiVqC8' \
			b'J0G1mBWwmBWwmBWwmBWwg1kBu2dWIBMHQMsELAC0mqw5gGbLrICdmBXIrENxhiixV4AmIRYBWru7BccdxzTs/1hg7QT7cqzIdqCpZhsDvW417ra4UmsNVioGVioGVirdBxJcmewlJgWV49ZaZaViipWKWWilYmClYgZWKkqkGunsNNfsAdfC7k4+1/BQEx9y' \
			b'o61kTRptYqxiYKxS3nOjDcYqBsYqBsYqBsYqZmCsYvYYq2T6pNEmBCxptFVkzWq0FWMVM2GsIvE5lGqIEnvdaEOIRRgXV4xbMe7orTdPRc8YZ3BHDTjMGVjMGVjMGVjMGXQfIBg34OBllNx1jhtw1ZyBLXMGduGcgcWcgR3MGfRS22nA+QOO4MF1nxPEGTTj' \
			b'xgJzM67kTJpxMnNgMXNQ3nMzDjMHFjMHFjMHFjMHdjBzYPfMHGT6pBknBCxpxlVkzWrGlZkDOzFzIPE5FGqIEnvdjEOIJRCnVwPjaWRL3xr1wBGunUC57RyD49Bgg1Rctri6Fhe8hEhtxBJUZhK0zCSIFyUeeo4NjquZBF1mEvTCmQSNmQQ9mEnopbZjcBwO' \
			b'ODY4lgzazIGRYFHVeRKDY5lJULxK1YGAOhwbHmNGQWNGQWNGQWNGQQ9mFPSeGYVMpBgeCyFLDI8rsmYZHpcZBT0xo6CN7diIomXj41ZSqQ2QEWoR4KkV8Nam3JGaclS+6KI5WRnmsDLMYWUYXVLkfHFNF1quSavEyyi56xwBnKvWh7myPswtXB/msD7MDdaH' \
			b'9VLb2Yj7kCOAkzsBuPFgUdV5AsA5WSLmsESsvCdBdVgi5rBEzGGJmMMSMTdYIub2LBHLxAHYMgELgK0maw6wubJEzE0sEcusQ3GGKLFXgCYhFgHaxa032DkUZYW108GaOtViMU+ywi0X6aJqdFE1uqgaXdS89DWHluDKZC9K2Pcct92qLqouXVS9sIuq0UXl' \
			b'mOjcBtqxn7gOs/dMFh+XM9JZHdC167gVJ3m0mRcjwaKqcyetOOmmanRTy3tuvaGbqtFN1eimanRT9aCbqvd0UzNx0noTApa03iqyZrXe0CXoWnATXdXMPhRuiJJC3XJDiEVAt65DeJgQd5KWm6Hy5XaLkZabQcvNoOVm0HIzaLnl0BJcmexFLTfTc9xyM1XL' \
			b'zZSWm1nYcjNouZlBy61ObaflZg44brnhLrfcRoNFVedJWm5GWm4GLbfuPbfcDFpuBi03g5abQcvNDFpuZk/LTYiTlpsQsKTlVpE1q+VmSsvNTLTchHUozhAl9rrlhhCLAG1dhrAC2tEAjY91ZXWWhVUOC6scFlY5LKxyWFjVhZbgBGjwIkBzPceAVi2scmVh' \
			b'lVu4sMphYZUbLKzqpbYDaO6AY0DDXQa00WBR1XkSQJN1VQ7rqsp7BjSsq3JYV+WwrsphXZUbrKtye9ZVZeIE0ISAJYBWkTUL0Mq6KjexriqzDsUZosReAxpCLAK0dRnC/QM0DEIfH9jsBLi1A4Bra5DzVNSs4tIpdeiUOnRKHTqlDp3SLrQEJ5CDF4Gc7zkG' \
			b'uapT6kqn1C3slDp0St1g3rSX2g7I+QNuU+4yyI0Gi6rOk4CcdEUduqLlPYMcuqIOXVGHrqhDV9QNuqJuT1c0EycgJwQsAbmKrC6Cw1BX5k3dRGc0MzAnwWhX90fZz1QELMK8I29E7m4B6k63tdxtAZy+oFYb7ZNDG+W4Q3YhkUqcjSFki9/hvuRdCAlChiDw' \
			b'IkOQ2HNsCFJv7qtYoDpjkIUb/ObzO+1wh18u3vK/axES9zm2BSlb/I6HiTlzVG4Eaqo6nJjf8S6/mQKWVlmgoGSFgpIlCkrWKKjhIgW7Z6dfISMbgwh7B9AGmqbhjWl3ueBmmYRgv98uO6M2IcJFXAJfNOEh2SAPGnQStgO3RPVj7DdK120P1IarFW4IajdA' \
			b'tDOj2OyThc/ZDLutPiWVA6Y3vR5HpC6EXJMCiJdRctc5QiRfTWn6MqXpF05pekxp+sGU5g74+L2OwMeXCczxMFHVOajOxfOYvdwcPHnY75mllHgFWnIqC1pNhbaDeOLLBOXkIcOZMSidEKVkKhSREBMn3zF4DDcMX8HjQYKHpZlgViw7AR45hARRJnsReNie' \
			b'Y/CobPd9sd33C233PWz3vT0EHnafY/CwBTxGw0RV56AGDzsXPPbY4Uu8GTwklSXg0dF2GDzsDPAQxqB0QpSSqcEDIfaBx3C/7hU8HiR4eDIgYcXyE+CRQ0gQAg94EXj4nmPwqAZ3fBnc8QsHdzwGd7w/BB5+n2PwKEM542GiqnNQg4efCx57xmsk3gweksoS' \
			b'8OhoOwwefgZ4CGNQOiFKydTggRB7wMMMjdlvDzzWgZi7M3VGZYX9IXw7ATY5hAQhsIEXgU3bcww21Z4QvuwJ4RfuCeGxJ4Qf7AnRS20HeNp9joGn7AYxHiaqOjcV8PBwi8d+EJklSr5Bpr3BBalAD/qQtGczCIkyQ5KkvwSS2kLWnBEWXyyZ/BQsSSiUY4gS' \
			b'ew1LCDHjKHAzND1f4WmFpxnwFBuPcWE/MS7chZAgBE/wIniKPcfwVI0L+zIm7BeOCXsc+uYHQ8K91HbgKe5zDE9lOHg8TFR1bnbgCaPBmSVKyESmvcEFqZAeDA5883uGgSXKDE+S/hJ4ioWsWfBUDnzzEwe+ZbbhEnLsNTzJqxnwNDQkX+FphafD8ESlxHCB' \
			b'ywg8dSEkSFIR8UqJ4a5zBE8IDHiie4EnfDsfngJmrOhSw1MvtSE8DagZEudAhcDTeJio6twM4YkTzSEYnvgbZNobXJAKDUFs+/CE53F4kigFnnL6C+CpUD0PnpghgCfQtQtPmW0oxxAl9gqeJMQceBqaf6/wtMLTDHhSDRQQlzF4yiEkCMETvIySu84xPFX7' \
			b'Y4WyP1ZYuD9WwP5YYbA/Vi+1HXjaIagX3IGKDE+jYWIvNzvwhL2xMkuUkIlMe4MLUiF4GmyMFfZsjCVRZniS9JfAU0XWLHgqG2OFiY2xMttQjiFK7DU8IcQceGJj7gQ5TQKQJrEoAVWs9o0xAli0+geYZcZga5uRy4yB1zbjlzm9rVA7A8hckyT7FHvIXAfR' \
			b'Ujgyl3BUNZgK4ZI/mYcw0hlBO1chXjtAPX0A+bansTHaxpkoGK67oo90irCHGl40dEV6k/QBjbdNyl/L8giQpLLskDLGDi03JMAUk6yH0WI+Ttfo+UKr7wz71I6gc6PkXmEYODKIbmjdni5W5XqhVXm2TdIDs/Je6kMo3fAGiEStH1JaPnIgRqOC3CR5b2Ud' \
			b'4GhwWgdYsjvEVg0b88wB4WMEzz046JEgLQMcGJhvDHXnKXWKN79nYKOJxhagS1hIAqNUBb4aawUz58uUYaa0RuFtm6EYJTOJx8yfXP6z1g5qZO7QTED6N10BIJ0QJZ16BSFCdNDsHrMP/SaUpnrd82+gXwJsViC6MFy7pBBDsJ6CaU/oTNAMXAYQ1yjMEDwL' \
			b'f0cnFxltCVUN42kGzHpycM7E4BAAp8BvCHw14F0H6NSM5t0MUGMwawcg1jXj/D7gOgxZWQ0No1SGqA6TRgApo9G1oGj/5GDGnU02544OWYnDNtmsab4hNEzjwhATemhwTRzYuDnGR/O0nvSdlL2v6VnHSW39iNruaWCdWnNzUynJw73W36RZuzq8RH8PtDzQ' \
			b'nLhbSlw1IKisHpAyU/HvKvRyZQ4L6mB7RmWuejyi1faoik3L4khoUphE1UUp+o0r6kOKfljJc8/iEhWdiav/RempR3lkxWfM3dK15c7hJQLBDghoKqZlQND8KwnZ40QqN8vbZc3ycAgS/NFQQZDAd0iwvX/VfNZ+Wqw7Wc3ncYfkZwKQwND+fGqACFteiaK5' \
			b'j0jdNerohnpBZ/pXR0EMVjKGjUWIYc6GGh1KhA4lqHzucROh2yHI7G0iWKADDV5taGQPOz3yQPAQL8qAFr3mIwy4yHlplO3mkOhBc+siXr+HbydGW48LJcCRLY2VuhEsmWsPfJt44md0HcLMroM5aativEVha4xAw+O2WhaD7gOXTatGMILIvCM4QQU+pzsx' \
			b'trhgrBWh5USmyS5FEpHLGdYbV/dETcoN8ZHEjIZOz9uMGE5xnKopke5pWkDR/ZzRg9ysCCMwkJsPJ2g2XGInYwcKSAl5NmqjWJ/NbQwv+HM2H4gzFA/X8GoOPEhTomtGDFsPrTQYBs2ExPc3F4EWR5oEuPCeBfPz2mMLRdW5gO+mph978P+udATUjQb/m3+F' \
			b'xwnfaZAgad2lqmxi/c1q9UtV37m1+Ez1vcs19WQtrdhY5Ga182Urs+RvVn18aPQ/if+1tNidR5HDEZroc62R9im0O+Gknr9QxVZyVvxFaTe3u1n8b9oCr3XcXF/RyVLuxNN8XBbzm+AHVd5eT+X9eVS+Une2KbiN+vuE6r6q+jxVH6g5lcctVucn1/Ljari7' \
			b'noaH82u4XjV81XDR8HbV8Nka7q+n4e35NdysGr5quGh4XDV8toaHix1eu1dDapekwhemvUdSVVpPdTmDZzdVzeZfipYfJvjhQfD2YrU0cb6b5j6bxo6t3jv11PaqwZPDZbytDM1an7faNbcyTX2EOjfenjZPrgPeU//6wfrdS66H5+w+MMfqfVvZvd4rrcaS' \
			b'6/7/onqaP+itdb0T013zlq3OW7nGLGBL1jHrk2oSWz9OIEoVeCqJVeVXlb8tlfc7/wtV3q8q70Xl3VyVV82bdmfvIui3Zs3G1kShr82sylDK/p49QVRmTF0Uq8aOaLMYhyS2PC4xshtOJZUkkZDGFjLI4jciep3YdcdT1ZvAyAYw48XHTHUjXAZD2UQvseHa' \
			b'bAOuCaJFwBdDU81HP5OXE1DR8RQjT0dmquKzZ3TFXC3xcdCJ7Xb2c3tSrmuumxtw3Ywz/g4yvy2QuFMAGdNOWAj2+oUwVclXZeIX1ufLy21WXTxZttuqE326MuZs9//7dWFV8Hi5sM67nnzMrKumxIgpLf1O3a+J3Fy5usnYUCVp1xkGWiptJ176vH8459qS' \
			b'uaA5x62geeMyNVZdcwRmudSeYZeQAyOkLj5ObV6WcL9K+EVLOH91g5HHhyrh9nHCBpbwsEr4hUu4WSX8RhLezpPwG09inVnIz7BPSyfoU6fP3kTouehPOKk0Ivic5CkFHwkcQ/j53SHhp+0xxg5pnTyelfUhrvpwKcDPYn9uHYin1oFj2TlwTNetAEYkPyV6' \
			b'WPKPZNFwRuE/48ZdR1UALv9zmBecuQkEuT7nrpeHDAP8wSmDo1rznEj2L2DjumPJPwrqrDY2J1QCzs1l7P96UBP2zwKdwLTtBMpwm/alJ1AInt6+JcuzE2kFZ+nCtkY+qBp7pupOZvi5asc+7eByvGXbzJPVG/ruaUh/HvWcBtI3X8AQL3TBwo1UhgTyQoyh' \
			b'pjXnhusRSHuiOo9l0zmUqJs0vo2FBqse9fSIyv8CDQtPqkuXvJZnsTL5VZkuR5nCqkx3WplC84a2hlYtSpXsBSO/aJs3nk5qTf5s5ibetDf0lgInQSGPQPvGGksedvvDVbo+2vBp7XRuF07pC7QtNG0I7XsHRCiWMNqQVPEpMJZPxfPVvs7b3RMf6KA0Eyjh' \
			b'jV6YSrpO/XF8ckrqaIzYkXZwpl+J2pDxv+n9lW1me/6ckh1JSQ1PLTyQMO+L1a3do3suOiEo0d39kZm4lYX95d+O/PE7xgbD97xgPtFkmWp3Q6oJpA4S7pu5f7QmYuDHZPqlZI4e1jhJKbGlozZ9vPeP1nBMvaN1EumPaQ67NMtJvGNkW1RQum+nuv8EXXXg' \
			b'mEnddEdM8vbp+ThJqrToGMnkx8dH+lGu1Ec2gkOqKUctehyxiF3oyYC+KX+pzmgHf8lr1w0DTQTb+epAZP2Qg2i5aNozilNK9CZ/TG+8JFHiNlEtTv5EIsV7Et2qI2vt8hBvGB8XZcr1+WSPIP+EDhlSXYZIcvypRDS1Di9TSl0D1/JSwe7xyM7rk0U97lC4' \
			b'+ijSSt2YeQJLfZ0bO+qJTb5GvsxAaOmIn5OhK0SXLNYvTnqpi1259E00zcDzuI76xidNoO9Q3CON8z1FfLiunCXM1PnuuxiGPjMdDSpMv0Ye3SrSEOm2udcOpT3SIzq9RNMI3DkcshhWgWaBpkHP++xQ2iN9shsJNBXjPKE2zREdDfdOv0ZW4yrYEOzY3GuH' \
			b'Ec2RDt+NBZuKcZZw0zzJUR1NY0y/Ro6HPcKHKt80Q3WfHUp7pIt4FPlWe8bE+zJumqM7mpWbfo2Mr31IEXPb3GuH0l7WhaRZtsUjrhPSXkqhk3jXzHc0NbkgdKJz15cmlfMD2LH2NkX4Q3OvHUp7WW/zWsJfl+R8RWib07naGmNvSPBo7a5CI8gK5z47lHb7' \
			b'IEpbxRQuupFSt6XkbVudRk5WJGSEdS+cJiM0ve37dc+9O0jFsona8+EkWcPdsoM5zrLOMKnKTXmUtWIer8bwLDTzHZm2Lfqg97GY++0PBeO9YrjHfFV3kK9tc5EODF3Wq70MhsbmIh0YOmKJdyaG6umBBNR1hxhL1fUZHVW+c33ZgcHLOqhdK+RMPFZz+Kya' \
			b'RY4sjpd+c/Oowe0Rw8m7xm3TXLwDr5f1Pi+S1665eAdePyyrVdr8fbnjpSDV//Vi2RfjzNhHX6Mcl02n3vVypMU898Gh7C7K3Pf0ZWeae+GwCmR5B/dOl51t7oVD2S3vRN/psnPNvXAou9RfhwXxFg10azoPoGri2xvaowWL32jBpFjk0yHNdekmznIIKpcU' \
			b'nkz36XizLVYi0YGvY6HbZvCP0GEnNJUWfxGb4b9WIoi9ZXqeyh3+qWKohW2ffKSy5wUApr9oVRaQji4eFUssOolnsFm+wvbzHKGVpEQMaRUsiZsBe+hMDxbfyKFbypS8SSXEQ8k0dMxDxrzgkMbNE4HaJV/pW9FRC7L6UGxoaN9/bRyvRwTO0o7tKRbycUK2' \
			b'Lz4pzA9X/x9DWBvw'

	_PARSER_TOP             = 'expr_commas'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	_UPARTIAL = '\u2202' # \partial
	_USUM     = '\u2211' # \sum
	_UINTG    = '\u222b' # \int
	_UUNION   = '\u222a' # ||
	_USYMDIFF = '\u2296' # ^^
	_UXSECT   = '\u2229' # &&
	_UOR      = '\u2228' # or
	_UAND     = '\u2227' # and
	_UNOT     = '\u00ac' # not

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
		('LEFTDOT',      fr'\\left\s*\.'),

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
		('UNION',        fr'\\cup(?!{_LETTERU})|\|\|'),
		('SDIFF',        fr'\\ominus(?!{_LETTERU})|\^\^'),
		('XSECT',        fr'\\cap(?!{_LETTERU})|&&'),
		('MAPSTO',       fr'\\mapsto(?!{_LETTERU})'),
		('EMPTYSET',     fr'\\emptyset(?!{_LETTERU})'),
		('SETMINUS',     fr'\\setminus(?!{_LETTERU})'),
		('SUBSTACK',      r'\\substack(?!{_LETTERU})'),

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
		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)(?!{_LETTERU})|{"|".join (AST.Cmp.UNI2PY)}'),
		('OR',           fr'or\b|\\vee(?!{_LETTER})|{_UOR}'),
		('AND',          fr'and\b|\\wedge(?!{_LETTER})|{_UAND}'),
		('NOT',          fr'not\b|\\neg(?!{_LETTER})|{_UNOT}'),
		('EQ',            r'='),
		('NUM',           r'(?:(\d*\.\d+)|(\d+\.?))((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))('*)"),
		('ATTR',         fr'\.\s*(?:({_LETTERU}\w*)|\\operatorname\s*{{\s*({_LETTER}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"({_STR})|\\text\s*{{\s*({_STR})\s*}}"),
		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
		('COLON',         r'{:}|:'),
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
		('ignore',        r'\\[,:;]|\\?\s+|\\text\s*{\s*[^}]*\s*}'),
	])

	_PYGREEK_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.GREEK))) + ')'
	_PYMULTI_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.PY2TEXMULTI))) + ')'
	_VARPY_QUICK   = fr'(?:{_PYGREEK_QUICK}|{_LETTER})'
	_VAR_QUICK     = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK   = OrderedDict ([ # quick input mode different tokens
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})|(\${_LETTERU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LETTER}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

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
		('UNION',        fr'\\cup|\|\|'),
		('SDIFF',        fr'\\ominus|\^\^'),
		('XSECT',        fr'\\cap|&&'),
		('MAPSTO',       fr'\\mapsto'),
		('EMPTYSET',     fr'\\emptyset'),
		('SETMINUS',     fr'\\setminus'),
		('SUBSTACK',      r'\\substack'),

		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\neq?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)|{"|".join (AST.Cmp.UNI2PY)}'),
		('OR',           fr'or\b|\\vee|{_UOR}'),
		('AND',          fr'and\b|\\wedge|{_UAND}'),
		('NOT',          fr'not\b|\\neg|{_UNOT}'),
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

	def expr               (self, expr_ass):                                       return expr_ass

	def expr_ass_1         (self, expr_mapsto1, EQ, expr_mapsto2):                 return AST ('=', expr_mapsto1, expr_mapsto2)
	def expr_ass_2         (self, expr_mapsto):                                    return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr_colon):                 return _expr_mapsto (expr_paren.strip, expr_colon)
	def expr_mapsto_2      (self, expr_piece):                                     return expr_piece

	def expr_piece_1       (self, expr_or, IF, expr_ass, ELSE, expr_mapsto):       return _expr_piece (expr_or, expr_ass, expr_mapsto)
	def expr_piece_2       (self, expr_or, IF, expr_ass):                          return AST ('piece', ((expr_or, expr_ass),))
	def expr_piece_3       (self, expr_or):                                        return expr_or

	def expr_or_1          (self, expr_or, OR, expr_and):                          return AST.flatcat ('or', expr_or, expr_and)
	def expr_or_2          (self, expr_and):                                       return expr_and

	def expr_and_1         (self, expr_and, AND, expr_not):                        return AST.flatcat ('and', expr_and, expr_not)
	def expr_and_2         (self, expr_not):                                       return expr_not

	def expr_not_1         (self, NOT, expr_not):                                  return AST ('not', expr_not)
	def expr_not_2         (self, expr_cmp):                                       return expr_cmp

	def expr_cmp_1         (self, expr_cmp, CMP, expr_union):                      return _expr_cmp (expr_cmp, CMP, expr_union)
	def expr_cmp_2         (self, expr_union):                                     return expr_union

	def expr_union_1       (self, expr_union, UNION, expr_sdiff):                  return AST.flatcat ('||', expr_union, expr_sdiff)
	def expr_union_2       (self, expr_sdiff):                                     return expr_sdiff

	def expr_sdiff_1       (self, expr_sdiff, SDIFF, expr_xsect):                  return AST.flatcat ('^^', expr_sdiff, expr_xsect)
	def expr_sdiff_2       (self, expr_xsect):                                     return expr_xsect

	def expr_xsect_1       (self, expr_xsect, XSECT, expr_add):                    return AST.flatcat ('&&', expr_xsect, expr_add)
	def expr_xsect_2       (self, expr_add):                                       return expr_add

	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                  return AST.flatcat ('+', expr_add, _expr_neg (expr_mul_exp))
	def expr_add_3         (self, expr_add, SETMINUS, expr_mul_exp):               return AST.flatcat ('+', expr_add, _expr_neg (expr_mul_exp))
	def expr_add_4         (self, expr_mul_exp):                                   return expr_mul_exp

	def expr_mul_exp       (self, expr_mul_expr):                                  return _expr_mul (expr_mul_expr)
	def expr_mul_expr_1    (self, expr_mul_expr, CDOT, expr_neg):                  return AST.flatcat ('mulexp', expr_mul_expr, expr_neg)
	def expr_mul_expr_2    (self, expr_mul_expr, STAR, expr_neg):                  return AST.flatcat ('mulexp', expr_mul_expr, expr_neg)
	def expr_mul_expr_3    (self, expr_neg):                                       return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                return _expr_neg (expr_neg)
	def expr_neg_2         (self, expr_diff):                                      return expr_diff

	def expr_diff          (self, expr_div):                                       return _expr_diff (expr_div)

	def expr_div_1         (self, expr_div, DIVIDE, expr_divm):                    return AST ('/', _expr_mul (expr_div), _expr_mul (expr_divm))
	def expr_div_2         (self, expr_mul_imp):                                   return expr_mul_imp
	def expr_divm_1        (self, MINUS, expr_divm):                               return _expr_neg (expr_divm)
	def expr_divm_2        (self, expr_mul_imp):                                   return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                        return _expr_mul_imp (expr_mul_imp, expr_intg, self._USER_FUNCS)
	def expr_mul_imp_2     (self, expr_intg):                                      return expr_intg

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add):           return _expr_intg (expr_add, (expr_sub, expr_super))
	def expr_intg_2        (self, INTG, expr_add):                                 return _expr_intg (expr_add)
	def expr_intg_3        (self, expr_lim):                                       return expr_lim

	def expr_lim_1         (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                          return AST ('lim', _expr_mul (expr_neg), expr_var, expr)
	def expr_lim_2         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):  return AST ('lim', _expr_mul (expr_neg), expr_var, expr, '+')
	def expr_lim_3         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg): return AST ('lim', _expr_mul (expr_neg), expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                        return expr_sum

	def expr_sum_1         (self, SUM, SUB, CURLYL, varass, CURLYR, expr_super, expr_neg):                          return AST ('sum', _expr_mul (expr_neg), varass [0], varass [1], expr_super)
	def expr_sum_2         (self, expr_func):                                                                       return expr_func

	def expr_func_1        (self, SQRT, BRACKL, expr_commas, BRACKR, expr_neg_func): return _expr_func (1, 'sqrt', expr_neg_func, expr_commas)
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

	def expr_attr_1        (self, expr_attr, ATTR):                                return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1].replace ('\\', ''))
	def expr_attr_2        (self, expr_abs):                                       return expr_abs

	def expr_abs_1         (self, LEFT, BAR1, expr_commas, RIGHT, BAR2):           return AST ('|', expr_commas)
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                        return AST ('|', expr_commas)
	def expr_abs_3         (self, expr_paren):                                     return expr_paren

	def expr_paren_1       (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):       return AST ('(', expr_commas)
	def expr_paren_2       (self, PARENL, expr_commas, PARENR):                    return AST ('(', expr_commas)
	def expr_paren_3       (self, expr_frac):                                      return expr_frac

	def expr_frac_1        (self, FRAC, expr_binom1, expr_binom2):                 return AST ('/', expr_binom1.no_curlys, expr_binom2.no_curlys)
	def expr_frac_2        (self, FRAC1, expr_binom):                              return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_binom.no_curlys)
	def expr_frac_3        (self, FRAC2):                                          return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4        (self, expr_binom):                                     return expr_binom

	def expr_binom_1       (self, BINOM, expr_subs1, expr_subs2):                  return AST ('func', 'binomial', (expr_subs1.no_curlys, expr_subs2.no_curlys))
	def expr_binom_2       (self, BINOM1, expr_subs):                              return AST ('func', 'binomial', (_ast_from_tok_digit_or_var (BINOM1), expr_subs.no_curlys))
	def expr_binom_3       (self, BINOM2):                                         return AST ('func', 'binomial', (_ast_from_tok_digit_or_var (BINOM2), _ast_from_tok_digit_or_var (BINOM2, 3)))
	def expr_binom_4       (self, expr_subs):                                      return expr_subs

	def expr_subs_1        (self, LEFTDOT, expr_commas, RIGHT, BAR, SUB, CURLYL, subsvars, CURLYR): return _expr_subs (expr_commas, subsvars)
	def expr_subs_2        (self, expr_cases):                                     return expr_cases
	def subsvars_1         (self, SUBSTACK, CURLYL, subsvarss, CURLYR):            return subsvarss
	def subsvars_2         (self, varass):                                         return (varass,)
	def subsvarss_1        (self, subsvarsv, DBLSLASH):                            return subsvarsv
	def subsvarss_2        (self, subsvarsv):                                      return subsvarsv
	def subsvarsv_1        (self, subsvarsv, DBLSLASH, varass):                    return subsvarsv + (varass,)
	def subsvarsv_2        (self, varass):                                         return (varass,)

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

	def varass             (self, expr_var, EQ, expr_commas):                      return (expr_var, expr_commas)

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

		if pos == 1:
			if rule == ('expr_func', ('FUNC', 'expr_neg_func')):
				return self._insert_symbol (('PARENL', 'PARENR'))

			if rule == ('expr_paren', ('PARENL', 'expr_commas', 'PARENR')) and self.stack [-2].sym == 'expr_mul_imp' and \
					(self.stack [-2].red.is_attr or (self.stack [-2].red.is_var and self.stack [-2].red.var in self._USER_FUNCS)):
				return self._insert_symbol ('PARENR')

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
		if not text.strip:
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
				res = (AST_MulExp.to_mul (res [0].no_curlys).flat (),) + res [1:] if isinstance (res [0], AST) else res

				print ('parse:', res, file = sys.stderr)

			if len (rated) > 32:
				print (f'... total {len (rated)}', file = sys.stderr)

			print (file = sys.stderr)

		res = next (iter (rated)) [-1]

		return (AST_MulExp.to_mul (res [0].no_curlys).flat (),) + res [1:] if isinstance (res [0], AST) else res

class sparser: # for single script
	Parser = Parser

_RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: # DEBUG!
	p = Parser ()
	# p.set_user_funcs ({'f': 1})
	# a = p.parse (r'x - {1 * 2}')
	# a = p.parse (r'x - {{1 * 2} * 3}')

	a = p.parse ('{-x} y / z')
	print (a)

	# a = sym.ast2spt (a)
	# print (a)
