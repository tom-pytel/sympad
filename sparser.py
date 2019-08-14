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

def _expr_mul_exp (lhs, rhs): # isolate explicit multiplication so it doesn't trigger imp mul grammar reductions
	if lhs.is_curly:
		lhs = lhs.curly

	return AST ('{', AST.flatcat ('*', lhs, rhs))

def _expr_neg (expr):
	if expr.is_mul:
		return AST ('*', (expr.mul [0].neg (stack = True),) + expr.mul [1:])
	else:
		return expr.neg (stack = True)

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
		return AST ('*', lhs.mul [:-1] + (ast,)) if lhs.is_mul else ast

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
	# expr_neg_func = expr_neg_func.strip_curlys ()

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

	_USER_FUNCS = set () # set of names of user functions to map to AST ('func', ...)

	def set_user_funcs (self, user_funcs):
		self._USER_FUNCS = user_funcs

	_PARSER_TABLES = \
			b'eJztXWuP3LaS/TMLxAOoAVEiJdLfnMTJNdaPXNsJdmEYhuM4F8EmdtZ29oGL/e9bVacoUWx1NzXT8+gZYThNii+RxapDsvjQvVdf/cv7D798VX31zbPHz56S/fjhdy/J+uHB84dPH5Pj0fdPnz1/+OabH58//nd6/O75g2/UMmo3ZH/96OmzJ9E20SEhD79/' \
			b'882DFw9fqPvJg5fq+np0/jQ6f4DzyaOnP3ISeS+X42t607+y48XL5/z749f0+/RHfulPD9jn0dOX33P5Hz2RYPn9+3PO67HU6xmHfvfjUy7+15Lim2dPnjyIdX0eX/Y8vowdzx99/zfO4uHf6efBkx/o99uvH794/ODF39j36bdaH3Z9PTp/Gp1an4ePXzxU' \
			b'n0gNzuglCkIFkEo/+OHFy2f8ppdSyYf/9s3jGMxE/fbRT4++5Wy++fbZSyGF1lyK98Njodij7+hHciEacap3bz+9//Lm46c3v/z8++cvbz+R1/v/+fPTm89//fl+ePjw/h9vfv3rw7sx8Gdy/vH2y5t3H39X16eP/z26PkvOn99//vxucP05uGI2b38enV++' \
			b'DG/79e27L9H9p+QK70kB/ojO338bnL99+PKP6P6vsSofxsh//PX7m9/++DM+fnn/aQj65bf/is6fP7199x/vv4whv/4a3e/++vT7/yZkGTJ++yV9BzmGFFzloZq//DK85LcPH5OSv//PoZ709qH6v71/9354oKb6ML7wz89fPsanIfXw1o+/f/wwPvzxx9vJ' \
			b'w+evXlev7m1sU1l3VsHRsaNt+cdWrT/TR3oSl+NoVdtXG3s28cCTjekogYte7JRYG7HbprrXVG1dbUxFydv6LPqq3+Cx6dlhGvw4R6F4a/QyXerFTk5o8GO18IYK0EgUCqCCmZb/z6JPSJ9MrQ72Y1fgshofy6rvIl/1Gzw2jREXUY6TE8mshvHrUHEhAgee' \
			b'JY/RnfgbWBupTiP/7RDcsIPzVX+8hN6vnnjuKcNeSthGDyqluKjgjVSzqfHjOHVzlnkxbUdfdpKLW7urWgrqzvC8AcPU+LHhTB+J7uwiSnGzMUFRUvLokoceFnvwizyRuxN6ExMRw1jwgvpvrNn2Sh777Rj99JH5Mmx55Yn89DFsP04SbBoQtlY+pXIbEM7U' \
			b'4uRoRLmm1bebIUL0Hh83jRCUqnavsRVRnluOXK4XmnBckH5HDBZikpSyiNTG04ibRhqEUmz6yvaR5yjAS32cigNLG3EB1SaRCgoc/EefVnyUWuJj4WNGHwefJvoQu4rL4sc1QxkHrzb1YidXoMEP0fHsbHRyHKqRgIUmYafUyNYI0PJZ5nQJoFaBRPeCVhEA' \
			b'UETyg8/waIW4NoobuYUnPJjA0RtcZdsoNqm3emwAPcRd8rNR8rCzlZCWoajmfPXJoZxcPpe0LgsnGEX4TJu2j/Uiz3vWjRXmxy7mSk8OxWBIaAeXVRcQhBwKIMRVwt2tx0/SL3iFL/KSH+kSFJF7cbKri4Fn+khPMeDsjHqnVzXjAFOeuKrhalFVSOaILgQy' \
			b'hIqByWpt1ZuqbyofqlBXgbybKrRVsFVwzMfWEzRR3aquqbpWODgwzbhO9EitRyQk01V9qHxdecqtrXrK1lU9efZV7ytvK+8q1IXoT9zFTGKJt4mZKxan2tE/4Vfd0z8loAK1laeX1aHqbNW5quuqrq86X3WEfdRmNf8bxlticmJqAg+SXmIMElLnK0fpqNBU' \
			b'n64KVA2qTMdSa/gFFXdYzevqXs09xqt7rZWeg4glFpWHKHivbRFKdGNvop2EGgl9xXAmz5LHStst2gZQz6JXtlbJ1ht5NkrkvkE0D2r2iN00iFRroiBEXvn5IM2NMnS/0quIXsp9AWwXgAPBKdtZIWNaZ63qVg1Rt6FiW/WRmtALnSKO9cfO2aq8dRCdDjUy' \
			b'akXpM/Lei76rUTYz4Si5KU0M4LcHEvgo+14aRVkojDwDHrks5pgIRCoHR2yzVzz+YDmtKHlFxaq6VSpfYyLDHKBc1rQrmBWQjbpWkRTD9WBZ4gjczXLVJNpKJpDJrWQqIVO3kqmETP1KpsOQ3mPy5HWG5XWYiq7e1rAws2KVC8ZIGMl4sU65n78nATKf6dTu' \
			b'1VayYJTmvfrGoRyGo50kDr4KYWSFgQlu48DoXtcpBUCnDoTpgs4Za6VTtHWg4DC1dOAbJ0Q1NTM9OWuiU1f5/qbXnaqBZnfuVMsPJndoO+cT7j3BygCiOmE1lDmtxY0vfweZCF3GTKJVQQvZYbqr6NRBzEyv8zKzjr+LhgJEogb6w2bVCM4RiGkCTepKoNmJ' \
			b'b2DCiM6U7DtMCVETrzwySxkvTLLC8WEWaoE2zUqvInqReyVUyaJBDZQOAlErRSpebmp0GaXBMgpZd54ssn7UHHWV59VkgZRXfTwo3wnI3Q3twCte1eLx0S2vpL0LlcRU4KL6NR0392LfTkr5+rbWjVd4pfkM9HkzW0Fe64YR7NgS1TFUF4iJGKpUhqpVdRgN' \
			b'eqQ+vsEghdG1ZqPbUDhEV8p1z8k9A7UHrxZJDh0s7emstAarrLlRbkETNNqPCKEyPVEHEuR7CUJUV4t9WSULURkO3UHnYbGkv4YOuFHdrwz2pYxhHMViFIKxLMYi2Yj2Tg5NWDkOskm7n4guVtjyhErbXqZcsPYZO+e6kyHKPa8qZWdPhu14HQai0p1QmXVa' \
			b'4PoTKrMO4rr6dMocMCqw2kHiyZi4DMD7wKm7YYv6IbaoC2oxxGnPMJtrMTxZ9xAc1o6DoOTDVlALBG17EDSAoESRVqbH6t1p0nw3pJI/23Fo7Iw3T1XUt4Vvi+Foi+GojA75d93Fp9oPCEW3KsmUfQdZb+NUpNEpCA+5V0FPNNFQRa+0kOlni+lni+lnq9PP' \
			b'9lZsjXrFU+j2NkyhZe7c3hUdLE/+G52Wt5iWt5iWMwniBKhOnpyJw6Htw1Q8DUXX3gATa/SnHgMqh/7YQQacvhEiYIYBldUBlY36HgwZLIYMFmMFq4MEe6eX1++BhC72REr9UfVVK8wIwW4FzFDp7cwIkOpiwb4W7GujVsmqVsmeylyE3uFUBFwcZ0AEHESA' \
			b'rdAiEtXbod4O9XZrd9tE0FppAR2hASNRT6Us04FlOrAMWcS1Ki4dYvYas7+dSxWvuPo9qt8LUqA3042SVIk+054zMTzI5pHOx6j+FtMo3Nq6hdtaN+HJoLvta91uX0svWVev6A1yTpG1G3xWMSi8cSFRgIYz5zJgcQV7iCKqDXQCrKKOXJEgZGkndOgiIan8' \
			b'TFeHXdcmSpUAH7RjrC2jMD6IyqDLyz9cRT5XySNNHmbyOX0+pM+n+/lcNB8+4YMnfOqEj5wwwvIhdT6hzluhmfh8mJapy2cIeDs+78Xnbe0M8nwqg49k8BkFPp/A5GJScUvz4XY+N8UjJj7UweXm5Uw+v85ns/mAMY+cqQ4Nz3FZVSj9Dm5wcBVuDOIra/jC' \
			b'impj5UqUakOd0CbwP0Whgm2ogBsqDC6Z4LtS5P6TakM9zIaafOM5K72zpcGVJRtu+A23/IabfsNtv6FCbrzcocEZUlDPmRGpN9QOm8C3UnB8vnfCVnplC/lxCrK9lo6qu+mcZikXjFAFN1T5DV895NiTYge+X4NjcVX5ghHOnSL3/Ca+94bv/uCykt01et0Q' \
			b'v4HS9/w2vmKE68lpyJ94fNNzkeWqGnqH1FF+uFZ8RQjfnMQ251jjNp1gcL9HxyVk6kgC8qc0fJ9Pz3eNCHnIk9p204XXPH5iEZiwf9LH7xSC+mJy0IyikALKbrHwhaJxbLFozikavlA8HFPB5RLhxKtMKtwlyYVDKYiaLrr3SYcrlI8jywYz+/nEgzMrEZHq' \
			b'n/Y+A5e7z9DV0UPj/0+GRiQ3xKmJvKBnQ8dlxn4J3Ve2Oo+F+3FP6kE58oko7ehmR7Ga9tPEUdpzSrc56m8w3raDxNWZ1LlE8qDFHZdv0iUdlkavElmrVDZTyeS7ZwaJDHskkcL5DolBIiken3vLJZMPYfEJLD7GVCqhfKJ1kNJuRlIpjC/MUGk1IUBiSXia' \
			b'mqU3ZNLLRJH7vCp1UQ7MnFRwtqgObBE5xILc8ovrQXqRbjBzouy7w5LMcVJh5ol9NLlgZ6/MjJTbj6n52YSYlUq+OCH8HC4H4ET+kzQ4CcdYIBLpYHlYKHGCC0I8hQOGgh0woFRSMIg0GyFhrHTwC4CBchFCaZGn6KBvUXyQeOmLMqyo78stajXhhMiO6+4z' \
			b'ThHfkW0YONoBOOoEO9DRNjcJL1KwSJGiKweLFSgUKJgYIjodOgyD/j327Um/rqERH6ZmDh8k4wP4wHFSfJjkmePD1lsnsa1PHkyILuINFgLpHrJxc8D7uWE0VY1S+x4BDpaHhdgpNpgybFDCKTYovUZsGEu9DBuUSFrkDBsQqNgg8dIXzWPDNiTY7bHECeHB' \
			b'CgYLwaCRyzJhmWY3EiA0IkEzMbNIUDDm5zgTJEjzzJGg2WcECYYHaUVx6Rhha/oc8HJuEk1So8i+R4CD5WEhdgoDTRkMKNUUBpRYCQyMZF8EA0ohLXIGAwiMMNAABkbaFMKAuxMwsE4gEijocGF1U6lrFxQgNEJBNzGzUFAwaTDZpGGSZw4F3T4jUDA8mBBd' \
			b'EQrG6YLR6UIHIBjT1Ciz7xGGmM7DQoIUC7oyLFCyKRYotRIsGN6/DAuURFrkDAsQGLEA04W0ogunC90KCncNFDyul28qde0CBYRGUPATMwsKvgAUfAYKaZ45KPh9RkBheDAhuiIo+BEUdHQAHXuSpkaZhaIABQ9QgGJR0iWg4MtAQcmmoKDUSkBheP8yUFAS' \
			b'aZEzUNAyKyh4gEJS0YWg0K+gcNdAgRNCcODaBQoIjaAQJmYWFEIBKGRrBZM8c1AI+4yAwvAwuiIohBEUAkAhABTGNDXK7HuEIabzsJQ2CSiEMlBQsikoKLUSUBjevwwUlERa5AwUtHYKCgGgkFR0ISj4/SsSNwoa3IoOx0QHXm6CflFdQVwMEGxlGKFxFCOa' \
			b'qZnDiKZAxdhkKsZJnhlGNFtvzQvB1z8MD7qeZgaYaEYVo1QWb+ejn2OaGsX2PcIQ03lYSJDARFOmY4yUA0xEgo0wMb5/EUxEKmmRpzChgQoTDXSMaUUXwkRYYeLOwkRb4dNClbqCuAQm2m2YQJwIE+3EzMJEWwATbQYTaZ45TLQHjMDE8GBCdEWYaEeYaAET' \
			b'LWBiTFOj2L5HGGI6DwsJUphoy2BCKacwoQRLYGJ4/zKYUCppkTOYQGCECexkSCu6ECZMveLEncUJy40rIgRXEJfghN3GCcSJOGEnZhYnbAFO2Awn0jxznLAHjODE8GBCdPmhkgNOWOCEBU6MaWpN0SMMMZ2HhQQpTtgynFDKKU4owRKcGDyX4YRSSYuc4QR8' \
			b'I05Y4ERS0aU4YdaNUCtg9NysIktwBXEJYPQCGPK5OQNLYQMxI2z0EzMLG30BbPQZbKR55rBxyAhspM8mRFdEjn5Ejh7I0QM5xjQ1Su7x6BDTeVhIkCJHX4YcSjxFDqVZghzD+5chhxJKi5whh9ZAkaMHciQVXYoc6xbKFTm4HaG5UFfAl22dNDEjB1sNwhQ5' \
			b'NKYiRzs1c8jRFugv2kx/MckzQ452663cOJMU1ACTZxOiS6GjHXUYLXQYLXQYSZoaRfc9whDTeVhIkEBHW6bDiNQDdESijdAxvn8RdERKaZGn0KGBCh0tdBhpRZdCR7tCxwodDbejyBJcARZDRwPoaAAdzQgdiBKho5mYWego2FPVZnuqJnnm0NEcMIIc6bMJ' \
			b'0RWRY9xZJbVGARg5xjQ1Su57hCGm87CQIEWOsq1VkXiKHEqzBDnGlliEHEooLXKGHNqmihzYWpVWdClyzOy1XJHjriFHi4+coy2hB22hB22hB21x2EosRQ7EjMjRTswschRoQ9tMGzrJM0eO9oAR5EifTYiuiByjQrSFQrSFQjRJU6PkvkcYYjoPCwlS5ChT' \
			b'iEbiKXIozRLkGN6/DDmUUFrkDDkQGJEDCtG0okuRY2Z75oocdw05LLegyBJcQVyCHNCMynFiA0uRAzEjctiJmUWOAv1om+lHJ3nmyGEPGEGO9NmE6PJDbQfkgIq0hYo0SVNrih5hiOk8LCRIkaNMRRqJp8ihNEuQY/BchhxKKC1yhhzwjcgBFWla0aXIsXMP' \
			b'Z33D1lFuwhGP+ghQcRUwQW3HCka+2Wu/brTjthVtIVzJzi1h8mQlBRGiSrSbmHMf827yfd7SROP/ll6022dEKTo8mBBdcQeXg0rU11qSgAK4dnwfzn8BKsSWE2AAC9gBdqoXne74lux3qEaViKoaVdpNj403S7d8S8UNvxYFzzSjeEnUjNKTtAaFQ0c6kmsC' \
			b'HfTS+9j/yrYVqJjs7Gxu9TiDKqU3tazjjZ3bPtvKYKZCVi+/jB8GkxWDyYrBZMWMkxVNFneBthMzuwu0YLJissnKJM98F2h7wMhG0PTZhOiKSDJOVkyrp0b4eAUq6iZpa9TA9whDCudhoeTpntCySUskou4JVdole0KH9y/bE6oE0yJne0IRGPeEYtKSVnTp' \
			b'0MPPnja/+XjS7YWUBUfQVzRJZi81t6kcQ0fr4soKthyerPjLBKYeJzAIixOYemJmJzB1wQSmztCEIoyZ5jOY+oDpsLV8UjAz1JEPp2PzvDzpPKbGPAY3VyTJalTA9whDTOdhIUE6j6nL5jFKQ53HKOmSeczw/mXzGCWXFjmbxyAwzmNqzGOSii4FkwNbR28m' \
			b'kqwakKNiCLcRRiTqCuJiALEYjlgMR+w4HNGYCiB4GswcgNiC4YjNhiOTPDP8yF65bRg8Js8mRJcOR+w4HLEYjlgMQ5I0NUrue4QhpvOwkCBBDls2DInEA3JEmo3IMb5/EXJEQmmRp8ihgYocFsOQtKILkaM5sJn0kpCjPnw15YofV40fttKb7tQVxCX4AQ2q' \
			b'hQbVjhpUjRnxw07MLH4UaFDlqjqueg0Q0VgxfxHmbeVI9vJtI0iSPpsQXX6o94Ak0KVa6FKTNPpy3yMMMZ2HhQQpkpTpUiMZFUmUegmSDJ7LkEQJpUXOkAS+EUmgS00ruhRJ1u2mK4Zw00Clqq4gLsGQDhjSAUO6EUMQM2JINzGzGNIVjEEy1eokzxw5ugNG' \
			b'kCN9NiG6InJ0I3J0QA6oVpM0NUrue4QhpvOwkCBFjq4MOZR4ihxKswQ5hvcvQw4llBY5Qw4ERuTogBxJRZcix7rd9OYghyryrg9B+spiw7q6cP24IAg2rFtsWLfjhnWNGRGkn5hZBCnYsG6zDeuTPHMEOWQEQdJnE6IrIsi4Yd1iw7rFhvUkTY2Sezw6xHQe' \
			b'FhKkCFK2YT0STxFEaZYgyPD+EOuwAEeUXFrwDEc0M8URbFtPq7sUR2b2nvaXeSTucpZvI0q01d4btS8LBc4l+ReWel/JHdZNpa4dl2hoaJR0PzGzku4LJN1Xey/czl6Tv3XyYEJ0Rbn21eS2PX4uuY9biFAgvUoQlV6lQyK9Q8nKZRbxZ67jjjmpwHoI7Fj3' \
			b'wtv0mqu+VXOV02PJKStusE6hrh1yqqHxJvx6Yubk1BUsTLh6v5xmr8nfSsQdH0yILpVTV0/l1NVlcurKVhkiQSCnkQ6jnI4lK5ZTjT8jpzEnyKnD8kJS91I5veprL1c5PZqcNpXDCQx17ZJThEY5bSZmVk4LtjW55oCcNvuMyOnwYEJ0RTltMjltCuW07CRF' \
			b'JIjKqdIhkdOhZOVyivhzcqo5qZxiT1JS91I5vRs3Ud60mfJ1zZCZ/CoLcO2SbYRG2bYTMyvbBbp5l+1unuSZy7ndZ0TOhwcTossPddu6pdpBGx+T1JqgR4CD5WEhdgoAZar4SDUFACVWAgCD5yKFWqSQFjnDAfhGHIAqPqFNKQ7cjcsnVxxQHHBMfpEVuHbh' \
			b'AEIjDriJmcUBV4ADLsOBNM8cB9w+IzgwPJgQXREH3AwO4JtWMUmNIvseAfB1HhZipzjgynBAqaY4oMRKcGCIsgwHlEJa5AwHtOiKAw44MNKmFAdm7ptcceD24kDHtBdZgWsXDiA04kA3MbM4ULDO5rJ1tkmeOQ50+4zgwPBgQnRFHOhmcABrbDFJjSL7HgEO' \
			b'loeF2CkOlC2wRaopDiixEhwYirwMB5RCWuQMBxAYcQALbAltSnFgZlfgigO3Fwd6JrzICly7cAChEQf6iZnFgYLVMpetlk3yzHFgrxEcGB5MiK6IA/0MDmClLCapUWSPR+dgeViIneJA2TJZpJrigBIrwYGhyMtwQCmkRc5wQGugOIAFsoQ2hTjQzn9MOT12' \
			b'4G7Aucetr1hf69fuqPbb33NOYcNXxzsVuRQ+XCGEmHPACH/rdf9noakY3GqqVdzzJVyNpUiDp8Gc+9Rkl6kXJ5lufUO6m3xHOiuDJqI2Gh9MjMWI02Oxo2u2QaeD4jGmIpp2uNelw70uHe516XCvSze914WbMf8idZdoKAs+vBuJC0CKNJ2epozNVIpIzDWM' \
			b'SkIU3BnVbd/8wl/l1ZwVmjqoLhMiTqDJ3Sc/wicJlN9Wfi3/MmCx5TlE4MpUr67wy+839LPvTflI4lzft2ZRvbFffr/ZX32XC9NKO/hzfdqapaCZkQJzmYIQe2Ei080ThxJRaGbEoUQUDnR30odcrzwkPRiT84bKRVkXw6XK5aJUJtoZmdgzgD2iTLSXIBPd' \
			b'FcnFIZmg8NCPskGcyrcknLSM9JckI0zMq5GTQzKCgXw7yEoczG/JjF08mqqPJDOJwPAs5DybMq51aGULZMeds08plZV2XjV7XHnJZYVJN5WXtru+fsWIhJT1LaFAbvx8/1L9kzjjPrWXzEHclc5BBgXIoPo4amfDah4Kpxa/usHYeeclxxKcyxcaUS3o/9E7' \
			b'G4xmreh6rm5wlgsP41vR4IyEx/v79GIRnq56dTqT9+uYqaTC4RYLyCAYXXdT5OJ4E/ZrmZSkfM/a0kWT9eqf/X2CKOH8/vo4n6pA7c+D+ZMRAe7bzbkm7Dexb9g5mPKi9d/wUsQpCYQWuj7fVN1fnyRQMYlQRKOrlgd/cZkg1jTUindGNnjRUxbGNkYY+Wpl' \
			b'pDtGv8Hl4qeLSEtYJC3m2F1HeyxpWbpAmi6Mnkdi2mvuSXg5+YpFRk7wGHc8gZE6nKdnkQtXz6kE9pCdC0kNvW6J1DTHlpooMuE6ph3nlZi7JS2ZpDDJrmEIdn5BOYKQmEVC0l6akPhVSE5FSOydE5JmkZCUb4BbKiRhFZJTERJ354SkXdW6F1toP/n5+nE4' \
			b'3gjjXufi+a41jNbfJ3FkTS41xfXpr7yqsK6O6/ONyhfVXt1qKTByJSArrq6wB2iPqq06D/y7S5WIXccDdnQFTbbj/xq6hCWHfQ4uhXcqGO1NFQ4cpJj+l3YZEjfdO389Kx+LDuYc2rfLn5iSL4FI3ba6Ekc9SSdbSezlroavcnPT5abZ+i+Xm+YWyk2jctMc' \
			b'kJu+euWr/MyqFwnpRTZSwRCpALtPT3a2u5mxz49MeT4X0VezByfjd96YGZgRZpkgMkBsy8m5Qr+byky3lF59Kz2uX0wBCL+KfQ85lwOvpSQxM2SplTTClhelDRdH+D7SSKakHCNdhjhEsMhsOZMp4cJiwg3AmdHuBtLPjtixRcMIAcehI5VzMR139EcJWZtl' \
			b'3U8p6Rd1K3nzxHlJe7RmkmpN/yewnzQdlEqLIL4YWBZBd84F8WNnpp0gM3nPsMUx5sIXUvkUHei/rC2tOye2u5hpx0BDesPjzF4vrrspOBZ/ZD3NDPfNDBJYTdMGYcVmZcWLsiJz1OXqUY7KiXwBQHsz+LBx9+Wbntbc38g5tIZsUR9SpVa+vChf2tPiSysl' \
			b'vuF8aad8eVRN9u1nTWbDq1M/39YOnPnQnQQfXsfhqMiL2Vfs9/Pl4YHl5fIlF+BcbCkJL5MzJcN5xmyECtVmVhE18wl4eoMy7eWsBN4Ovt3Fq9wA17OMd1wcvbpF61Is7eWrScZboTYzS2gkwMuHVVzHn6sXdYt7fUbuexv5VB9u/2pxS1A8eEo04dhyCUgr' \
			b'x7b5IqzkBCmy3jQHciCpmP5JKv1AzyQdzr72eQYtr1+0+jccaeWz6fiT/GyaX9Pn15TNZs8HK/n4eduM697xYi5clsXfo6nwx59DkY1Z0djJn9zhQG/hMCNL37wgwTuicKmCFNKdr5B8+PNgObvq8B8v1mR+Uq6utFxzt7LtLBrfSTYUj/B9xx+vKO0MI1qS' \
			b'LYXsJ4XsZspp5bs0qd7xwH2Tw2VycpMcLpDjy+BqXde0ekkcL3uRH18MN1fR9OK24SK2rhovXAvpJWuvuevQv77y6V+/Zeb+5mJt+/WzSdKgMarQ118+E5BQnO9PChiuhgFsxgTNJTICZ3zZxoXkgfv0i2YpjWHqy2cXHuQc36D4Ji0+t60/Eku5G8BVfTUY' \
			b'fJ/SHMXwgPJYee00aJ5mP3fpNY17JXsnj0U6DnzGY/fdxsiOgr0x7KyvH9OhUu0Mzxn5nOnROc9cG/PxLGhq8E3Ubf8LGp7PHD3TaNBgBwaVJVyI9ljAi666oInzvb2xUD93JxjSV6dv0F7d4RFQMUvG5ihizDmyhmowNFFPH5eaqJU4EDHTJwhF+rvAwaxJ' \
			b'OnmD9vI3iINZO3c9BrQId4J3++r0DfRc9U3iXV9dkwEt5qZPt493Q3X6Bu3VXALv7hvW9gU8zFxxVMMtPOPrm10pQJs7MS3jtaeTN2gve+Lt1VG8zpS2W1OdijFMKJoK7I6C9nOFetwjwtGMtOymuKv2G15ZPBipxEwyms0VBCuY9l0rwUJ1MwyoVbpOdE3U' \
			b'4sX+G2FArYIJ2amsqvEeigKDvRPjf2GyfVmUZzcbAy1xRctbV9ISvjodg+0IBZO7k6F+qE7HgPrm9lCfN3CdjAH1CyaHJ0N9U52OAfX5SzY9bwpRJLLxWWWDvz/AZGE/+e6IxqNRYdpERD+O0PIdhMHL/VE4usfb1eZi2ioxiOi3InJTcGRXpcZ45ZyQbivj' \
			b'6RDKxtcxpsyyt909UvPGRo6pGxqHTYgzGxC1uHyfXXbI0MgeWdk7IK/sxtfwDknHbAJtHt/zZUInq79Umddn/w802pXr'

	_PARSER_TOP             = 'expr_commas'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	_UPARTIAL = '\u2202'
	_USUM     = '\u2211'
	_UINTG    = '\u222b'
	_LETTER   = fr'[a-zA-Z]'
	_LETTERU  = fr'[a-zA-Z_]'

	_VARTEX   = '(?:' + '|'.join (reversed (sorted (x.replace ('\\', '\\\\').replace ('+', '\\+').replace ('*', '\\*').replace ('^', '\\^') for x in AST.Var.TEX2PY))) + ')'
	_VARTEX1  = fr'(?:(\d)|({_LETTER})|(\\partial|\\infty))'
	_VARPY    = fr'(?:{_LETTER}(?:\w|\\_)*)'
	_VARUNI   = fr'(?:{"|".join (AST.Var.UNI2PY)})'
	_VAR      = fr'(?:{_VARPY}|{_VARTEX}(?!{_LETTERU})|{_VARUNI})'

	_STR      = r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPY   = f"(?:{'|'.join (reversed (sorted (AST.Func.PY - AST.Func.PSEUDO)))})"
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
		('FRAC',          r'\\frac(?!{_LETTERU})'),
		('BINOM2',       fr'\\binom\s*{_VARTEX1}\s*{_VARTEX1}'),
		('BINOM1',       fr'\\binom\s*{_VARTEX1}'),
		('BINOM',         r'\\binom(?!{_LETTERU})'),
		('IF',            r'if(?!{_LETTERU})'),
		('ELSE',          r'else(?!{_LETTERU})'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+\.?))((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
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

	_PYGREEK_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.GREEK))) + ')'
	_PYMULTI_QUICK = '(?:' + '|'.join (reversed (sorted (g for g in AST.Var.PY2TEXMULTI))) + ')'
	_VARPY_QUICK   = fr'(?:{_PYGREEK_QUICK}|{_LETTER})'
	_VAR_QUICK     = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK   = OrderedDict ([ # quick input mode different tokens
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
		('VAR',          fr"(?:(?:(\\partial\s?|partial|{_UPARTIAL})|(d))({_VAR_QUICK})|(None|True|False|{_PYMULTI_QUICK}|{_VAR_QUICK}))('*)"),
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

	def expr_ineq_2        (self, expr_add1, INEQ, expr_add2):                     return AST ('=', AST.Eq.ANY2PY.get (INEQ.text, INEQ.text), expr_add1, expr_add2)
	def expr_ineq_3        (self, expr_add):                                       return expr_add

	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                  return AST.flatcat ('+', expr_add, _expr_neg (expr_mul_exp))
	def expr_add_3         (self, expr_mul_exp):                                   return expr_mul_exp

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
	def expr_mat_6         (self, expr_curly):                                     return expr_curly
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
# 	a = p.parse (r'''{Limit ({[True] if \fraca'"str" else \int True dx if Determinant() else ()  \left|\sqrt['str']partial\right|  \int_\left|\tilde\infty \right|^\partial x! dx if partial dx}, x, ({{log"str"^oo^partial,['str' <= None,"str" [partial]],\left|(1e-100,'str',a)\right|,},}))+[sqrt\log_1.0'str',({{({1,}),{'str'  1e100},1e-100 if a else \tilde\infty  if partialx else 'str' if 0,},})]^\sum_{x = [dx,dx,1e-100]**{1e-100*partial*1.0}}^1 == oo**\fracoo\tilde\infty  -\partial !+\int_\log_d [None]!{dx*\partial x} [\sinh(-1.0,"str")]^lambda x, y, z: {{oo \cdot \partial } \cdot Float(\partial ,\tilde\infty ) \cdot \sqrt\infty zoo} \int d^\partialx [\frac\partial 1.0] dx dx}''')
# 	# a = sym.ast2spt (a)
# 	print (a)
