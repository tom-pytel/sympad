# Builds expression tree from text, nodes are nested AST tuples.

import ast as py_ast
from collections import OrderedDict
import os
import re
import sys

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

_SP_USER_FUNCS = set () # set user funcs {name, ...}
_SP_USER_VARS  = {} # user vars {name: ast, ...}

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

	if ast.is_diffp:
		ast2, wrap2 = ast.diffp, lambda a, count = ast.count: AST ('-diffp', a, count)
	elif ast.is_fact:
		ast2, wrap2 = ast.fact, lambda a: AST ('!', a)
	elif ast.is_pow:
		ast2, wrap2 = ast.base, lambda a: AST ('^', a, ast.exp)
	elif ast.is_attr:
		ast2, wrap2 = ast.obj, lambda a: AST ('.', a, *ast [2:])

	if wrap2:
		ast3, wrap3 = _ast_func_reorder (ast2)

		if ast3.is_curly or ast3.is_paren or ast3.is_brack:
			return ast3, lambda a: wrap2 (wrap3 (a))

	return ast, lambda a: a

def _ast_pre_slice (pre, post):
	if not post.is_slice:
		return AST ('-slice', pre, post, None)
	elif post.step is None:
		return AST ('-slice', pre, post.start, post.stop)

	raise SyntaxError ('invalid slice')

def _ast_mulexps_to_muls (ast): # convert explicit multiplication ASTs to normal multiplication ASTs with index information for explicit muls
	if not isinstance (ast, AST):
		return ast
	elif ast.is_mulexp:
		return AST ('*', tuple (_ast_mulexps_to_muls (a) for a in ast.mul), frozenset (range (1, ast.mul.len)))
	else:
		return AST (*tuple (_ast_mulexps_to_muls (a) for a in ast))

#...............................................................................................
def _expr_ass_lvals (ast): # process assignment lvalues
	def is_valid_ufunc (ast):
		return ast.is_func and ast.func in _SP_USER_FUNCS and all (a.is_var_nonconst for a in ast.args)

	if ast.is_ass: # if assigning to function call then is assignment to function instead, rewrite
		if is_valid_ufunc (ast.lhs):
			ast = AST ('=', ('-ufunc', ast.lhs.func, ast.lhs.args), ast.rhs)

	elif ast.is_comma: # tuple assignment? ('x, y = y, x' comes from parsing as ('x', 'y = y', 'x')) so rewrite
		vars = []
		itr  = iter (ast.comma)

		for c in itr:
			if c.op in {'@', '-ufunc'}:
				vars.append (c)
			elif is_valid_ufunc (c):
				vars.append (AST ('-ufunc', c.func, c.args))

			else:
				if c.is_ass:
					t = (c.rhs,) + tuple (itr)
					v = c.lhs if c.lhs.op in {'@', '-ufunc'} else AST ('-ufunc', c.lhs.func, c.lhs.args) if is_valid_ufunc (c.lhs) else None

					if v:
						ast = AST ('=', (',', tuple (vars) + (v,)), t [0] if len (t) == 1 else AST (',', t))
						vars.append (c.lhs)

				break

	return ast

def _expr_comma (lhs, rhs):
	if rhs.is_slice and rhs.step is None and rhs.stop and rhs.start and rhs.start.is_var_nonconst:
		if lhs.is_comma:
			for i in range (lhs.comma.len - 1, -1, -1):
				first_var, wrap = lhs.comma [i].tail_lambda # ._tail_lambda (has_var = True)

				if first_var and wrap:
					ast = wrap (AST ('-lamb', rhs.stop, (first_var.var, *(v.var for v in lhs.comma [i + 1:]), rhs.start.var)))

					return ast if not i else AST (',', lhs.comma [:i] + (ast,))

				if not lhs.comma [i].is_var_nonconst:
					break

		else:
			first_var, wrap = lhs.tail_lambda # ._tail_lambda (has_var = True)

			if first_var and wrap:
				return wrap (AST ('-lamb', rhs.stop, (first_var.var, rhs.start.var)))

	return AST.flatcat (',', lhs, rhs)

def _expr_colon (lhs, rhs):
	first_var, wrap = lhs.tail_lambda

	if wrap is None:
		return _ast_pre_slice (lhs, rhs)

	return wrap (AST ('-lamb', rhs, () if first_var is None else (first_var.var,)))

def _expr_mapsto (args, lamb):
	if args.is_var:
		return AST ('-lamb', lamb, (args.var,))

	elif args.is_comma:
		for var in args.comma:
			if not var.is_var:
				break
		else:
			return AST ('-lamb', lamb, tuple (c.var for c in args.comma))

	raise SyntaxError ('invalid lambda function')

def _expr_piece (expr, expr_if, expr_else):
	if expr_else.is_piece:
		return AST ('-piece', ((expr, expr_if),) + expr_else.piece)
	else:
		return AST ('-piece', ((expr, expr_if), (expr_else, True)))

def _expr_cmp (lhs, CMP, rhs):
	cmp = AST.Cmp.ANY2PY.get (CMP.text.replace (' ', ''), CMP.text.replace (' ', ''))

	if lhs.is_cmp:
		return AST ('<>', lhs.lhs, lhs.cmp + ((cmp, rhs),))
	else:
		return AST ('<>', lhs, ((cmp, rhs),))

def _expr_neg (expr): # conditionally push negation into certain operations to make up for grammar higherarchy missing negative numbers
	if expr.op in {'!', '-diffp', '-idx'}:
		if expr [1].is_num_pos:
			return AST (expr.op, expr [1].neg (), *expr [2:])

	elif expr.is_mul:
		return AST ('*', (_expr_neg (expr.mul [0]),) + expr.mul [1:])

	return expr.neg (stack = True)

def _expr_mul_imp (lhs, rhs): # rewrite certain cases of adjacent terms not handled by grammar
	ast         = None
	arg, wrapa  = _ast_func_reorder (rhs)
	tail, wrapt = lhs.tail_mul_wrap # lhs, lambda ast: ast

	if tail.is_attr: # {x.y} *imp* () -> x.y(), x.{y.z} -> {x.y}.z
		if tail.is_attr_var:
			if arg.is_paren:
				ast = wrapa (AST ('.', tail.obj, tail.attr, _ast_func_tuple_args (arg)))
			elif rhs.is_attr:
				ast = AST ('.', _expr_mul_imp (tail, rhs.obj), rhs.attr)

	elif tail.is_pow: # {x^y.z} *imp* () -> x^{y.z()}
		if tail.exp.is_attr_var:
			if arg.is_paren:
				ast = AST ('^', tail.base, wrapa (AST ('.', tail.exp.obj, tail.exp.attr, _ast_func_tuple_args (arg))))
			elif rhs.is_attr:
				ast = AST ('^', tail.base, ('.', _expr_mul_imp (tail.exp, rhs.obj), rhs.attr))

	elif tail.is_var: # user_func *imp* (...) -> user_func (...)
		if tail.var in _SP_USER_FUNCS: # or arg.strip_paren.is_comma:
			if arg.is_paren:
				ast = wrapa (AST ('-func', tail.var, _ast_func_tuple_args (arg)))
			elif tail.var not in {'beta', 'Lambda'}: # special case beta and Lambda reject if they don't have two parenthesized args
				ast = wrapa (AST ('-func', tail.var, (arg,), src = AST ('*', (tail, arg))))

		elif arg.is_paren and not tail.is_diff_or_part and arg.as_pvarlist: # var (vars) -> ('-ufunc', 'var', (vars)) ... implicit undefined function
			ast = wrapa (AST ('-ufunc', tail.var, arg.as_pvarlist))

	if arg.is_brack: # x *imp* [y] -> x [y]
		if not arg.brack:
			raise SyntaxError ('missing index')

		ast = wrapa (AST ('-idx', tail, arg.brack))

	if ast:
		return wrapt (ast)

	return AST.flatcat ('*', lhs, rhs)

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('-diff', expr, 'd', ('x', 1))
	def _interpret_divide (ast):
		numer = ast.numer.strip_curlys
		d     = e = None
		p     = 1

		if numer.is_var:
			if numer.is_diff_or_part_solo:
				d = numer.var

			elif numer.is_diff_or_part:
				d = numer.diff_or_part_type
				e = numer.as_var

		elif numer.is_pow:
			if numer.base.is_diff_or_part_solo and numer.exp.strip_curlys.is_num_pos_int:
				d = numer.base.var
				p = numer.exp.strip_curlys.as_int

		elif numer.is_mul and numer.mul.len == 2 and numer.mul [1].is_var and numer.mul [0].is_pow and numer.mul [0].base.is_diff_or_part_solo and numer.mul [0].exp.strip_curlys.is_num_pos_int:
			d = numer.mul [0].base.var
			p = numer.mul [0].exp.strip_curlys.as_int
			e = numer.mul [1]

		if d is None:
			return None, None

		ast_dv_check = (lambda n: n.is_differential) if d == 'd' else (lambda n: n.is_partial)

		denom = ast.denom.strip_curlys
		ns    = denom.mul if denom.is_mul else (denom,)
		ds    = []
		cp    = p

		for i in range (len (ns)):
			n = ns [i]

			if ast_dv_check (n):
				dec = 1
				ds.append ((n.as_var.var, 1))

			elif n.is_pow and ast_dv_check (n.base) and n.exp.strip_curlys.is_num_pos_int:
				dec = n.exp.strip_curlys.as_int
				ds.append ((n.base.as_var.var, dec))

			else:
				return None, None

			cp -= dec

			if cp < 0:
				return None, None # raise SyntaxError?

			if not cp:
				if i == len (ns) - 1:
					return AST ('-diff', e, d, tuple (ds), src = ast), None

				elif not ast.denom.is_curly:
					if e:
						return AST ('-diff', e, d, tuple (ds), src = ast), ns [i + 1:]
					elif i == len (ns) - 2:
						return AST ('-diff', ns [-1], d, tuple (ds), src = ast), None
					else:
						return AST ('-diff', AST ('*', ns [i + 1:]), d, tuple (ds), src = ast), None

		return None, None # raise SyntaxError?

	# start here
	if ast.is_div: # this part handles d/dx
		diff, tail = _interpret_divide (ast)

		if diff and diff.diff:
			if tail:
				return AST ('*', (diff, *tail))
			else:
				return diff

	elif ast.is_mul: # this part needed to handle \frac{d}{dx}
		mul = []
		end = ast.mul.len

		for i in range (end - 1, -1, -1):
			if ast.mul [i].is_div:
				diff, tail = _interpret_divide (ast.mul [i])

				if diff:
					if diff.diff:
						if i < end - 1:
							mul [0 : 0] = ast.mul [i + 1 : end]

						if tail:
							mul [0 : 0] = tail

						mul.insert (0, diff)

					elif i < end - 1:
						mul.insert (0, AST ('-diff', ast.mul [i + 1] if i == end - 2 else AST ('*', ast.mul [i + 1 : end]), diff.d, diff.dvs, src = AST ('*', ast.mul [i : end])))

					else:
						continue

					end = i

		if mul:
			mul = mul [0] if len (mul) == 1 else AST ('*', tuple (mul))

			return mul if end == 0 else AST.flatcat ('*', ast.mul [0], mul) if end == 1 else AST.flatcat ('*', AST ('*', ast.mul [:end]), mul)

	return ast

def _ast_strip_tail_differential (ast):
	if ast.is_differential or ast.is_var_null: # null_var is for autocomplete
		return None, ast

	if ast.is_intg:
		if ast.intg is not None:
			ast2, neg = ast.intg._strip_minus (retneg = True)
			ast2, dv  = _ast_strip_tail_differential (ast2)

			if dv:
				if ast2:
					return (AST ('-intg', neg (ast2), dv, *ast [3:]), ast.dv)
				elif neg.has_neg:
					return (AST ('-intg', neg (AST.One), dv, *ast [3:]), ast.dv)
				else:
					return (AST ('-intg', None, dv, *ast [3:]), ast.dv)

	elif ast.is_diff:
		ast2, neg = ast.src._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return neg (_expr_diff (ast2)), dv

	elif ast.is_func:
		if ast.src and _SP_USER_VARS.get (ast.func, AST.Null).is_lamb:
			ast2, neg = ast.src._strip_minus (retneg = True)
			ast2, dv  = _ast_strip_tail_differential (ast2)

			if dv and ast2:
				return neg (ast2), dv

	elif ast.is_div:
		ast2, neg = ast.denom._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('/', ast.numer, neg (ast2)), dv

		ast2, neg = ast.numer._strip_minus (retneg = True)
		ast2, dv  = _ast_strip_tail_differential (ast2)

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
		ast2, neg = ast.add [-1]._strip_minus (retneg = True, negnum = False)
		ast2, dv  = _ast_strip_tail_differential (ast2)

		if dv and ast2:
			return AST ('+', ast.add [:-1] + (neg (ast2),)), dv

	return ast, None

def _expr_intg (ast, from_to = ()): # find differential for integration if present in ast and return integral ast
	ast, neg = ast._strip_minus (retneg = True)
	ast, dv  = _ast_strip_tail_differential (ast)

	if dv:
		if ast:
			return AST ('-intg', neg (ast), dv, *from_to)
		elif neg.has_neg:
			return AST ('-intg', neg (AST.One), dv, *from_to)
		else:
			return neg (AST ('-intg', None, dv, *from_to))

	raise SyntaxError ('integration expecting a differential')

def _expr_func (iparm, *args, strip = 1): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	ast, wrapf = _ast_func_reorder (args [iparm])

	return wrapf (AST (*(args [:iparm] + ((_ast_func_tuple_args (ast) if args [0] == '-func' else ast._strip (strip)),) + args [iparm + 1:])))

def _expr_func_func (FUNC, args, expr_super = None):
	func = _FUNC_name (FUNC) if isinstance (FUNC, lalr1.Token) else FUNC

	if expr_super is None:
		return _expr_func (2, '-func', func, args)
	elif expr_super.strip_curlys != AST.NegOne or not AST ('-func', func, ()).is_trigh_func_noninv:
		return AST ('^', _expr_func_func (FUNC, args), expr_super)
	else:
		return _expr_func_func (f'a{func}', args)

def _expr_subs (expr_commas, subsvars):
	if len (subsvars) == 1:
		return AST ('-func', 'Subs', (expr_commas, subsvars [0] [0], subsvars [0] [1]))
	else:
		return AST ('-func', 'Subs', (expr_commas, ('(', (',', tuple (sv [0] for sv in subsvars))), ('(', (',', tuple (sv [1] for sv in subsvars)))))

def _expr_mat (mat_rows):
	if not mat_rows:
		return AST.MatEmpty
	elif len (mat_rows [0]) > 1:
		return AST ('-mat', mat_rows)
	else:
		return AST ('-mat', tuple ((c [0],) for c in mat_rows))

def _expr_vec (ast):
	e = ast.comma if ast.is_comma else (ast,)

	if all (c.is_brack for c in e):
		if len (e) == 0:
			return AST.MatEmpty

		elif len (e) == 1 or len (set (c.brack.len for c in e)) == 1:
			if e [0].brack.len == 1:
				return AST ('-mat', tuple ((c.brack [0],) for c in e))
			elif e [0].brack.len:
				return AST ('-mat', tuple (c.brack for c in e))
			else:
				return AST.MatEmpty

		elif e [-1].brack.len < e [0].brack.len:
			raise lalr1.Incomplete (AST ('-mat', tuple (c.brack for c in e [:-1]) + (e [-1].brack + (AST.VarNull,) * (e [0].brack.len - e [-1].brack.len),)))

	return AST ('-mat', tuple ((c,) for c in e))

def _expr_curly (ast, forceset = False):
	e   = ast.comma if ast.is_comma else (ast,)
	kvs = []

	for kv in e:
		if not kv.is_slice or kv.step is not None or kv.start is False or kv.stop is False:
			if ast.is_comma:
				return AST ('-set', ast.comma)
			elif forceset:
				return AST ('-set', e)
			else:
				return AST ('{', ast)

		kvs.append ((kv.start, kv.stop))

	return AST ('-dict', tuple (kvs))

def _expr_ufunc (args, argspy = None, name = ''):
	kw = None

	if argspy:
		name, kw = AST.args2kwargs (args.comma if args.is_comma else (args,))

		if len (name) != 1 or not name [0].is_str:
			raise SyntaxError ('Function() takes a single string name argument')

		name = name [0].str_
		args = argspy

	args, kw2 = AST.args2kwargs (args.comma if args.is_comma else (args,))

	if kw is None:
		kw = kw2
	elif kw2:
		raise SyntaxError ('keyword arguments not allowed here')

	return AST ('-ufunc', name, tuple (args), tuple (sorted (kw.items ())))

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

	return AST ('@', f'{var}{VAR.grp [4]}' if VAR.grp [4] else var, text = VAR.text) # include original text for check to prevent \lambda from creating lambda functions

#...............................................................................................
class Parser (lalr1.LALR1):
	def __init__ (self):
		self.TOKENS_LONG.update ([(v, self.TOKENS [v]) for v in self.TOKENS_QUICK])

		lalr1.LALR1.__init__ (self)

	def set_quick (self, yes = True):
		self.TOKENS.update (self.TOKENS_QUICK if yes else self.TOKENS_LONG)
		self.set_tokens (self.TOKENS)

	_PARSER_TABLES = \
			b'eJztffuP3DaW7j9zgekGVIBIig/5N8fxzBobJ1k7GezACALH41kEN4kDO8ndRbD/+z0vPqRSlVTq6q5HE5ZbKooSyXPI7yN5jsibN395/eyrL7768i/NX/7P+1/+Caf484vnf/0GTl8/ffX8yy/g4q+vnj6Tk5KzhvNnL7786mU8q3ih5QWff4Xv+JL+fvb8' \
			b'b98/e/r6+Wu5fvk0hn6WL/+eL7/my9dfPH39b59Bav+OuUgXFPzs21df/AN/pYtv//rtl8++/ke8wojfvMK/334Gf5+//Pqbf7x+Tnn6FnP996d48+WLL7/FXL348pu/YcZfvKQn6O9/vMLYX5BEvsK78trP6MlnX718+TRKCQNevfjbv30TM/QqZvjVIMP4' \
			b'6/PPvqAAzNR/wJ+nL7/Gyy8/F7Hg1Wf58u/5UsTy/IvXzzHhVy9e4vnzF39/8TlePGORv/6G8vf1F1QwKHIs43++fv6MInz+4q9/RTF9+YLU/Ywy8PTLz1EOeOOrV5Jg1Blmmd/6DEr7TTyjzl8+/fr1N1/h89+QtJ//5zNUBgWB5BWf4Oln/w6Xn37/4dMf' \
			b'bz9++qO4/gTX795+fP/b9x8+fv/PH3769Nvbj8VtuITTW4r2/r9/hSg//vFzvP70+6/vP8Yfv7z/r+/ffvyvfO8HuPz57W/fv/vwk1x9/PD/8hUn/On9p0/v0tWv6Sq+5u0P+fK331Ji/3r77rd4/Su9lYN//+Vdzui//vVrzk3K9E8/pssff/kt5ffn33/6' \
			b'/seffy2KWb6oKGS6zK/EZ/Ei/v7t/cd074+3H0fR4s/fy9y+/ec/4+W73z/+9D/xx39/ep9L+sPHt+/+7/v081OZsz/ep3f9/suPH35Jib5N8d/l4pGQU0k+5Ff+Xsj7l5SlH3785UMq0YesBchP0sK7Dz///DY9/OuP79+9Tz+gfhUZ+vXTbx9SIknVKWsf' \
			b'fsq5p5cOfnwqnvz+pz/e/pQCPvGT3zVvbja2b5y7bfjC40Xn8U9ouu5WfsIvuurhj2s612zc7SCAf4X4HDzQxyC8pFgbfrlrbkxj4J2m6Vq4uE2hFJYDNvSc9vzHQoDml8Yg3W8FWV8G4SVcKct/nG42il8Pv/ASrvBByDL8Drf8e0NlhbiGMmL5j29v5Sfk' \
			b'jV7RNTdQOuXw/20M6ctfqpULDMN3dlh21UvZO30bQyUsBWw0pwESVaZBFTh7KyEbza/t+Y9TEKJuJQgvUZckcSgDPyU/43URrvm0oeQ6+m9CvN3hBZyNhN/yj00ngZxbUqhuY6FMCpWwrQCVA9QwYKNJ9gYyZDhHiv9YzjtcbTrKsnH8x0J2LAscfm0M6dTi' \
			b'q/t0w6YbXcd/PKdIFZVKqHRzg1UCVcW1HkNc+cvLGYPwWbhvMHFpJPGnHQdF1Q7Du+2foycnfk4EjXLgtn8OHtp0psharvWSiVGAHQe4IgCqyY1pJQsQqv0gOP/cGGqFBuqrUY2GOodabxsP2YEX4g/O344YCEx2aURQ+zDipqPWgtAEbaWPVRtbLt2AOslt' \
			b'EnVvof76smnCzRSeQyyHhBziOKTPIZ5CbBtDNprqLVZLwzVY8x/b5ezGIFsG4SVeef6zie2QL/Gq4+oeH8EXUq22ckP0jyl1BA+QuxtVoCG8SrGSoCVzRTf8x2GLEOgxdEmC3CgVL6gwSqEUuwjqLAcMpKD4u5V3wosAqlWsSYPwGAIBVO0M/4Eqdiu/odlS' \
			b'HPqPguVH8AIFbPiPRSzkZ+AXXqIE4Ka2lGn56SkV0N+NUomSYs2yIWIToTxzINYXnWJ4qm6FwuC+CBkCb1xukPTT57SBj1h7mK5JV61c6S5e2HjBHAI1WaPqFCkhBRlqCOOg/BPeQFeK/zgUnCCzoktMpG0YgCGBG2SaTEmQIudIW/5jQ2rjmls/Fkrzn9xD' \
			b'sFq4xSr+g5graI41wDIBtfHmrfyEX/EGB0GBfEcyh6yLVjAPlhJ2+AKXXoClc/QCp+INiipB8pT1XGgENZAFdIfetI2C1qCg8JAUYB7UN3gUEUE1gIeAgFA9ANQAWXpEDWjZwTbBAdcH+A9h0K4UVGaF/K/wdQrrIuQI0oUeiGoxLlSxjuoQsDIkBwc8DQpT' \
			b'GnsNcG6BbyFF3UCLhAYdfBNCEyDRtulV08N7DEIWvB8yqTpMD35rVCBioMEb8KqOIBzUgbAGtRniGEQ6gDCo0gpKpAyeIQNQqB7u4ZOQsjKYBP7umh4O2/SYb4gPgujhNS2CG9IvoErvmz40Ho6+CSAQ1QTdBNMESAgKqaCUFjkcWzgAioOq76CvCQ0AEdkD' \
			b'fiuEcA/NEbgZ+lqu8agEeBRyCVoCRUMNRPmgQOGF2HOFy1tsthATVHeDOsMA0Buc3tygXOAnigZPLcfq5C6W/JYYjU493X2DfVD6Ta+q+j4jfd/0rDjVs5Zb0VhgRaIWUL+BFUraoXN8TGmpLkbOnURw8iJSHoQErgKaX9DJ69sUiypQRYbzrSlvbiwpfSBH' \
			b'kSBLbkJmIqskoy3ZDOUxJQyRAVRCp7nSufbE+RCww1pFtdhLLdZU+R82M9pzZrQ9QdqCCkHkoU1txOfeiCvQnruObih31NcKVVfnrivGfCQDUloSGwksiUfEEqVRFh+Km4p2+iIVNWi71pyMclG83LGkpkFDCsIxnByBpBsoeG0Jp20JRnpnRkYAafCn+4pi' \
			b'5607GO4R0yjIhYK3K4tygCAsIxRYQYmrhk6sob5q6Lw11LdVQ2euIVU1dM4auumlD0FCoOnE2IlQPO9cexFnrD3VmTgRJOrDAuP0sWmjXmXeV2aLpatoRckdzyd1vqr6zFXdsblAOdZrTz9Pn7OzHb2yXUxyxSEyd8qmMVRsunujeHB7o4zMrPbcXnpuL70V' \
			b'05yRZmbECCNDrz4aa6SxdfK2Vlqh5cdsHEpbeYxyUtV104vUPduqPPe80QCqdZ26OVSaQWpd4FoYuK4GI4ZFoQA2XyB1cOXF/hnet9Hmwy3AcXTHNduzvaWFuC3Eo6IhlPePQ7Rv0A+GxMF2KG8fuzi4wTomJ88w590uqcQm/Uik47kBem6A3j/yyuKlD6rE' \
			b'cJoEwFYygaFo2rXiBSP+EDr2dKH3qG+rU9N5d1fJa0mzu5KuDkhnphvD7vLGVd2cmW7Qb0+LdxicqxJONPVva8s4O6WgpLV4PsK5KuOkymiJPER41QXjfiaxFPWeakf3nFtCIMZGN+uqqjNXVWerjs5dRxXyzl1H9OkIDVIsDVJOSJATn7jg1wKtjKEImWvn' \
			b'5H5kj0k/+OcPPHGBifJIgOeYAv9qjeg9ujK0u76D+k6+s8K5EB5M1GpxHA0ZgQae6mXbkRfDk9hC2WIQvUwMYUiV+11bBokRvUq5CYjFmbyuyCIdkluPOBJ0ThoCO3+guyO+oW/5JHpUPBFV9bJSL4rnwd+QZw4BTRXgoZ4cKLcqq0Wy6qqsFsvKVlktlVXn' \
			b'uKOFHWp01+kF09iQVLhRqeh2yLal0sFKDBs9V9Eq6h2i7m2Vzz75WKIDa3ElpSoV6WX00rh84DHZwLPCc8duhwew0tHzke6fR3nI7U9c2DS7sGl2YdM8duNxoOW7TsZ9jntY4mDzKDT/Bh3zaPq5rx7czVlPm72hZZ+qTf90E8uq9L97JPBArobZuxfx3j9G' \
			b'MfDs31nk5kYxWKMvMfOWf4S85W0Fw5NZcJxME7r+Mda89jEW2tXmdrLm5mUy3evHWPN8rXknNNXLSFmclKIHJQwJ2TkfTzhMvKWl2/EU6Be7WxpxtzS30efP5NX3aLaPogZ+XV3S5MxrAxTUsAnc8FKgrF9FZ9tH5eIJ8UEs7RyJnwyscCOhsuIQWn05nKoX' \
			b'1bW6PtSp1Y2mdpoeownlqorTzj4YaV6yvgZO2Almmmiw12KoJ3t7BcyzUFtXW8/J1YCuKYZdUwy7ppjommLKNU9QPib6WphdJo8bJeQlcZgMO+7adF4eFIo0HNxz3J5DreFkLLkyVVPUyEDn6toWwwEQQXx1/DlMbmSY1GIDNGwDNGwDNLd5WpdapMJ10nmh' \
			b'8I6bpuOWSl5x39GyFdzjVeI/6uXMnqOOW73nhxzDime08YwAnlP3Pg+OujqqPdmotkXp08Czi16PPL7peHzT8fimkyFMR6MSwu7IEEFIIHlBsp6tTZb0brfRHIrZcZXsuEp20SxND/Gy/VQLu9vY1XtU0z7UQKw4YVtRlY39XVaVZVVZVpUVVVlp8pbla1m+' \
			b'tvbBTt4V1qSr8bId/A1IdTw4X9UhDFn+DsLFTSMckiZEwoXIInlSs3Pc7Bw3O4zWJO276pe2G+9k+gzS8YJkdLZCILziG4nYVzHu+aKL96cMKD4UK3+6k1Ysi7INPGfC3+7gOAxHHbh0EK4alHqDKEeuz4HfGUQlMuViRTdOznFe28qnKvBgX5W1R1mmymcv' \
			b'Jhjupior362xGaaooJh1rpp0xghsa2kb3MGv0bTfAs6l454LfVFiJqeAtIoDJRML2VPhjFCw8HJRClSTkkkLlmUprLFKelIGa2JLm0znuHYjdW0tsTU5t5AofMG88vUQmYYi7cB93NcJFxjE1QVxZT1cVg+XlMP15HAxOVxADVdPw5XDcFFIXNkQVzVEuWF1' \
			b'wj3TsEeBn/jhYuC43DSqEdfrRBbGSQjMHzqsQxXVOP6DLrjGLwWh36AhzxoXssBeRouyhHj4ATKuNIJfj2K3BQWMEsYqh2LG+oSyRmHjOBLrCo4zO9zqEqsbhKOjPE7k4qQuOqla3GcTwtBTFY3BaAhGb8CA/y3oG3fwDbTNJe5GiZsD4/aguI0mbocKYbgJ' \
			b'KO6KqZtNwC08W9r3lfYv7ZoNbgiNu0GiAni/aNrmE/cexZdq3Pu0xR1MaRNWeBvt/ovv6+h+K3tudrgpdC97QRt8IaWNceg+Pq/oBZQH2miYkm0b3usSb8EToKdNwEQxH7hzpqeyOdqJlLYxpR2LMTe0pTHthUnbb2KXjkrZYzbwDuhw43spCu60ibur4kBq' \
			b'g1VtgxuTQpXZeNpG1NJOphveVxS3+8aS4WshZsAz7f3aYu6Von12ac9YEhBKHbcKxQ1Iqei0Kzc8hwWCM1SwTU+p4FMdiRCfM7LdMm2oTVtcbxSliWXrUSJxf2PMKvz2pA58k6ZtVOH9uJ+qx92r4dVQ8TcedxlHuXnek9UHzouizW4VCgs3JCeBwVO4lzG9' \
			b'iraEhaQC7kmLdcV8h7CCYFKh5PFAScWRiiP3gCMacWQXfrgpCPG5K1ViCegjzxgMu1hHBxUQO3fuZNb9AIzBL6NnceZK8AVEP8QYN4MzHuXrZxDF78YU33hujH4CWXzGFj+FLv6B8MVzNo1v8r8DMcYvQpnrBBfMVQEwfgZimj/dE2Qq/wS5Klg4uf9FB7UZ' \
			b'3OFJwT6iD40Ny2HfAIPiROFojpInLmdQScsQdyk8hSFCxbHs5NhY0GprTCqwRb0jGWoPAAyHvigK/GRO5yE2z9P2MkQthqeDIWwEPFWAHnueJNe90p0vAeHEjAvuEUzgCPFw7fhZkLTzQIkehbgN1wAw4VncluHOwKkEPCEefjd/KIiCXJcBaVeAqWJAxS8+' \
			b'BqCKs9GqAFdsp6gcO4OvEKFnjKWTwGzPSNtnsMXJE8u4RGeaPHeMuZQWwy5HS0fCYHpmC4RV7uXRXD1NhKhViEyZIWp226jMhoD8fwulc4axUqcCYPSiND1DNwaTZAoEH6cwSA0bXS6aH91kxO8J0nQC/SJtFrNO6UYekChIB+mNlpghXs4TBMfazxFJ9Zkp' \
			b'JOgYfDEQBprsV5AHFZP5Q1hvB39Ivp1INfiYbMElKTOJU5hNHFCL7YRUEPWeUGsACHiCnAdN+AmI539p0aI9bGOXdXQvlGSEYSK7uAMYRh2JZSrDPBDDOGYYN8MwKBS3uxePrcEJsTghlsgrLvOKGxyZV9wkr7jMKy6ncDipCKdMUUr56i06SXew9rrpg6jE' \
			b'ZRohENU74vYkaBGlKt86HDIMKGRQ+laLfIU8JA+hiONVij1PHAsGF0nwBXFw0FGII5dtJWu4zBp7SUNExfUqeEmzpAwp1T7CmOAJe9fZkDuSxMnpYQk11EHHBVGCZ0qYm9RRe2Z1FPnoMB/IxA6dWz5HPvCDI/PB5GSPyrM9/O7DmcAzE/gJJijzscUE6Y7x' \
			b'40zne44TGAwoJiPGeaIihNFfjYcPZRzCfrmM8C8JhyIaVXOONQ//fgH8R00W8M9BR4H/XLyV8J8nnbg0u+BfRMXVKMQ0S/iXUq0dL7jKA5UHrooHeuaBfo4H+j08wM+T4nvhgV54oM880A+OzAP9JA/0mQf6dTzQMw/0EzxQ5mOLB9IdrLj99EE80I94YDJi' \
			b'4oEcIjzQj3igfIp4IMYRHpCEQxENq7nEmueBfgEPRE0WPMBBR+GBXLyVPNBnHthne4ii4moUvKRZ8oCUai0P+MoDlQeuiQcIe8mqtp8H8M4uHsCCtMwD/AKOrlo+Cw9wrHQkHtCTriV4LTzA7z6YBygNytwWDwzyMeaBfAeXs22nD+QBPTIRT0eMPFCEMA+w' \
			b'qDIPDJ5SrU6XwgMx4VBEQ9VKrFke4Fj7eSBpMvOABB2DB4rireMBfFR4gEuzgweiqLgaBS9pFjwQS7WWB8Jh1uqrYQNXCeHaCUEzIeg5QtAUx8lpihb4FrUgLbSghRZ0pgU9ODIt6Ela0JkW9Dpa0EwLeoIWynxs0UK6g2Cudx7EDHrEDJMREzPkEGEGPWKG' \
			b'8iliBrmMzCAJhyKaVynWPDPoBcwQlVkwAwcdhRmKMq1jBp2ZQe9jBhEV16TgJc2SGaRUa5mhr8xQmeE6maFjZujmmIGODX+WNc0MHINaUCfMIM6hOvuH6uGRmaGbZIYuM0O3jhnYYRRPW8xQ5mOLGdId48eZHjzoOI0BM0xGTMyQQ4QZuhEzlE8RM8hlZAZJ' \
			b'OBTRUMcSa54ZugXMEJVZMAMHHYUZcvFWMkOXmaHbxwwiKq5JwUuaJTNIqdYyg2orNVRquE5qYFdWPefKihmzTA12BzVwDGpC4sTKeMnnSA12cGRqmPRh1dmHld99ODVYpgY7QQ1lPraoId1BNLc7D6IGO6KGyYiJGnKIUIMdUUP5FFGDXEZqkIRDEQ11LLHm' \
			b'qWGBW2pSZkENHHQUasjFW0kN2SeVS7OLGkRUknUvaZbUILdWU4M6o68fLum7h0oSF0QS7Hqk51yPMEPsfaSL7x0080RJFfyLmpS4IWlxQ9LZDYljpSNTxaQbks5uSHqdG5JmNyQ94YY0yMcWVaQ7xo8zPXjQtfFqwBaTcRNb5BBhi5Ez0uApYgu5jGwhaYci' \
			b'GimbY82zxQJnpKTPgi046ChskYu3ki2yM5Le54wURcWVKcQ0S7aQUq1mC/pGl5xcGfoR9zUh/gjrO0T2DMG78LfP6IgISKgnaJbQihGKEIJbP7RoTPQEx3e8aF9lzMqY182YhmfczNyMm6EDGdMUM254reXEjCnxFFd2Ykwj824mz7uNjsSYZnLezeR5N7Nu' \
			b'3s3wvJuZmHcb5GPMmPmO8eNMDx50bbwqGXM6bmTMIoQZ04ym3gZPIWPGS2HMmHYoooGyY6xZxjQLpt6SPjNjStAxGLMo3jrGNHnqzeybeoui4soUvKRZMGYs1WrG3Pu9X2WLyhbXwBaB2WJuBSCsrYHZIhRsEZgtQmYLjkdsEYQtgrBFyGwRBkdmizDJFiGz' \
			b'RVjHFoHZYmJlj0E+ttgi3ZEGWxxYr/J918arAV2EiSPTRQ4RuggjuiifIrqQy0gXkvagCCrFmqeLsIAuokILuhBJHoMucvFW0kXIdBH20YWIimtT8JJmSRdSqtV0MffZX6WLShcXTxc900U/RxccB+miL+iiZ7roM11wPKKLXuiiF7roM130gyPTRT9JF32m' \
			b'i34dXfRMF/0EXZT52KKLdMf4caYHD7o2Xg3YYjJuYoscImzRj9iifIrYIsYRtpC0QxEN2UJizbNFv4Atoj4LtuCgo7BFLt5KtugzW/T72EJExZUpeEmzZAsp1Wq2mPs4sLJFZYtLZ4uOvxPp5r4TwXrKn4rQSdgCr7WcmC0kHlaCTr4Z6eSbkS5/M8Kx0pHY' \
			b'Yno50i5/M9Kt+2ak429GuolvRgb5GLNFvmP8ONODB126KtliOm5kiyKE2aIbfTkyeArZIl4KW8S0QxENlB1jzbJFt+DLkaTPzBYSdAy2KIq3ji26/OVIt+/LkSgqrkzBS5oFW8RSrWaLuU8IK1tUtrh4tlDMFmqOLRTFQbZQBVsoZguV2YLjEVsoYQslbKEy' \
			b'W6jBkdlCTbKFymyh1rGFYrZQE2xR5mOLLdId48eZHjzo2ng1YIvJuIktcoiwhRqxRfkUsYVcRraQtEMRzecH5tlCLWCLqM+CLTjoKGyRE1jJFiqzhdrHFiIqrkzBS5olW0ipVrPFgR8aVraobHF5bMFm7m7OzN3RQWxRmLk7NnN32cwt8YgtxMzdiZm7y2bu' \
			b'bnhktpg0c3fZzN2tM3N3bObuJszcg3xssUW6Y/w404MHXRuvBmwxGTexRQ4RthiZuQdPEVvIZWQLSTsU0bxKsebZYoGZO+mzYAsOOgpb5OKtZIts5u72mbmjqLgyBS9plmwhpVrNFns/PrSPgzD8JGe4yhtXxxuGHYrNnEMxCASrLvsUm8Kn2LBPsck+xRKP' \
			b'jBjiU2zEp9hkn2KOlY5sxJj0KTbZp9is8yk27FNsJnyKsRbmjGxZMdKdUZZHR8/frUvcSB9ULD39RLZl5BCxZYxciwdxyJYhl9GWIaoJRTS0ZUiseVvGAtfipNbClsFBR7Fl5OKttGVk12Kzz7U4iorrVIhplrYMKdVaBtF7v1GsDFIZ5KoYpGMbeDdnAwdh' \
			b'dBwNBx+FGbxjM3iXzeASjwYfYgbvxAzeZTM4x0pHHnxMmsG7bAbv1pnBOzaDdxNm8EE+tgYf6Y7x40yXB2bEtTFuIhAZgkw9kYcgOUSGICNj+OApGoLEODIEEc2EIhoOQSTW/BBkgTE8abUYgnDQUYYguXgrhyDZGN7tM4ZHUXGVCl7SLIcgUqrVBFK/ZLyf' \
			b'CSvs6plKH/dGH2YHhdglAxE2jps54zjWajaOm8I4btg4brJxXOLRKESM40aM4yYbxzlWOvIoZNI4brJx3Kwzjhs2jpsJ4/ggH1uDkHTH+HGmBw+6dDVwpZqMm4YfOUSGH2Ic14C6mnIhw5DyaRqGyGUchkgeQhENhyESa34YssBInvRaDEM46CjDkFy8lcOQ' \
			b'bCQ3+4zk2vZJXFyx6CvHWFnL4YiUbjWbzO1GWtmkDkLOiUXWDEJwR05QDp72sgfuGGaIPegk7IHXWk7MHhIPKwGddcfnls/CHhwrHYk9KOoWe2CosAe/+2D2oDQoc1vsMcjHmD3yHePHmR486Np4VbLHdNzIHkUIswcLLI89Bk8ha8RLYY2YdiiigbJjrFnW' \
			b'4Fj7WSPpM7OGBB2DNYrirWMN2lCWWYNLs4M1oqi4MgUvaRZsEUu1mi3qN+GVLa6eLdhYbueM5ZYOYovCWG7ZWG6zsVziEVuIsdyKsdxmY7kdHpktJo3lNhvL7TpjuWzebSeM5YN8bLFFumP8ONODB10brwZsMRk3sUUOEbYYGcsHTxFbyGVkC0k7FNGQLSTW' \
			b'PFssMJYnfRZswUFHYYtcvJVskY3ldp+xPIqKK1PwkmbJFlKq1WxRvwmvbHH1bMEGDjtn4LAcB9misG5Ytm7YbN2QeMQWYt2wYt2w2brBsdKR2WLSumGzdcOus25Ytm7YCevGIB9bbJHuGD/O9OBB18arAVtMxk1skUOELUZ2jcFTxBYxjrCFpB2KaMgWEmue' \
			b'LRbYNZI+C7bgoKOwRS7eSrbIdg27z64RRcWVKXhJs2QLKdVqtrjYT8JbIgxdOePKOAM3LL433tDMG3qONzTHwbUaC97QzBs684bEo8YlvKGFN3TmDY6VjrxW4yRv6Mwbeh1vaOYNJd/7EcJhNeCkZNFGykrMxdaqjSmvxo+zPyiKa+PVYNXGybhp1cYcwgyi' \
			b'RwwyeIpWbYxxmEFi2qGIhmqXWPOrNi5gkKTZzCASdJRVG3PxVq7a2JNtL63cuI9Fori4agUv6RYsEku2mkXqp+KVP86EP+6NOxxbw92cNRxrHFvDXWENd2wNd9kaLvGwEjixhjuxhrtsDedY6Ujc4Sat4S5bw906a7hja7ibsIYP8jFmjHzH+HGmBw/mq5Ix' \
			b'puNGxihCmDFcO2SMwVPIGPFSGCOmHYpooOwYa5Yx3AIreNJnZgwJOgZjFMVbxxguW8HdPit4FBVXpuAlzYItYqlWs0X9VLyyxdWzhWa20HNsoSlOPEW20MwWOrMFRyC20MIWWthCZ7bQgyOzhZ5kC53ZQq9jC81soSfYoszHFlukO8aPMz140LXxasAWk3ET' \
			b'W+QQYQs9YovyKWILuYxsIWmHIppXKdY8W+gFbBH1WbAFBx2FLYoyrWMLndlC72MLERVXpuAlzZItpFSr2eKcPhXvKmFcE2GwK+WDEAfIa5o8zIhATEki7ELl5lyosPKxC5UrXKgcu1C57EIl8YhExIXKiQuVyy5UHCsdmUQmXahcdqFKrz+cR9iLyk14UQ2y' \
			b'ssUj6Y7x43wPHnRtvBrwyGTcxCM5RHhk5EU1eIp4JMpVeETSDkU05BGJNc8jC7yokswLHuGgo/BILp5Oaa1gkzxT5fb5UsUEbCqDl8SFUJxwSsrWelqZ29A2REK5mv0KT7BZ4TWTxwOPNnC2G+SifTtnG+eRh50beVgedkxuV4gVVEYbVkYbVkYbNo82OFY6' \
			b'sj18PNrASmXzYMOuG2xsovfUxGiDql3xf9smnnKJNmw9fZBBfDTWmI6YrOH0EysHkgTlBoU2oAnMD8dT8VM/VX7oJ/eRJ2L2LY844uUCo/iCIUdSamEU56BJqpDCLGQKEoGVjKy0ivOYgxBo7+d+UVmWM09PanwRpDQefsQSDnmiC0+o8xKJwvRPyBDVImEA' \
			b'qkErfcJb6ybCMHPb3J4nYZyYJCJBCDkQMURSEEJIRHBpJHBW002BRwphbqQQdoO+o4NHB0FGB0FGByGPDsLgyKODMDk6CHl0ENYNDQIPDcI26G8PB1KujB9nNN9z/NLBQGAyYhoI5BAeCDDGx1GAiK0tZ5ACd/sDd/jDot5+WNDbjyoqevsim2P09rOIDu/i' \
			b'h9TF3+y1RscUuG4EL3WtnDGSEu3r2kuPnoB57tPsCswVmE8GzJ6txn7Oauzb3cCMvm5iKfZiKfZiKfbZUsyx0pGA2U9ain22FPt1lmLPlmI/YSneAuacK6iEo4zme45PJTBPR4zAXIRMAHMUWwnMnq3Anu2/fpHx1y8w/iYVZWCWoGMAcyGig4HZtwuBOabA' \
			b'dSN4qWsFMMcSLQXmua+cKzBXYD4dMPM0iZ+bJvF7pknQ/VimSbxMk3iZJvF5moRjpSMD86RR1ud5Er9unsSzUdZPTJNsA3PKFcKpnj4ImEfTItMREzDnkClgFrENgJknQDxPfPhFkx5+waRHUlEBzBx0FGDOIjocmPVSYJYUuG4EL3WtBGYp0VJgnvug+DyB' \
			b'uc59nwWIn5unDTYvBHI7B+R2D5Bbuk1AbgXIrQC5zUBuB0cGcjsJ5DYDuV0H5JaB3G4D+SAfW6Ce7iAU2+mDQN2OQH0yYgL1HFKCejnVPXgO8Z2lKRAv6YYy6yrFnod7uwDuoyILuOego8B9Ltu6KW4MFszn0uyCfBGVZN1LmiXky60FkD+YxZ77OrhCf4X+' \
			b'y4F+x9Dv5qDf7YF+R7cJ+p1AvxPodxn63eDI0O8mod9l6HfroN8x9LsJ6C/zsQX96Q4Ctps+CPrdCPonIybozyE7ob98jqDfFdAv6YYy6yrFnod+twD6o7AL6Oego0B/LttK6HcZ+t0+6BdRcS0KXtIsoV9KdSj0z33qW6G/Qv/lQL9n6Pdz0O/3QL+n2wT9' \
			b'XqDfC/T7DP1+cGTo95PQ7zP0+3XQ7xn6/QT0l/nYgv50x/hxpvM9xwkMoH8yYoL+HLIT+stYBP2+gH5JN5RZVyn2PPT7BdAfFVlAPwcdBfpz2VZCv8/Q7/dBv4iKa1GIaZbQL6U6FPrnvs+t0F+h/3Kgn31d/Jyvi9/j6+LpYOgXXxcvvi4++7r4MDgy9E/6' \
			b'uvjs6+LX+bp49nXxE74ug3xsQX+6Y/w40/me4wQG0D8ZMUF/DtkJ/eVzBP2hgH5Jd5B1lWLPQ/8Cj5ikyAL6RYLHgP5ctpXQn91iuDS7oF9ExbUoeEmzhH4p1aHQTx/bdo2d2f3mqhnAPPBeN2uZIBzABubyGAHkeY9L+2Bjwm+RFLHDxszRQ49P7mYIel/H' \
			b'kKeFIrRQhM4UocPgyGv7TFKEzhSh11FEdILXExwxyMjWkj6YNOaZ54ZG+c7POc47tgl6d0utCWU4HT+t6pNDdpHF4Dla16cgi5j8oAwqxS7JAtc1ml7YZ4IwcEGprcV95KXl4j4i0iOQBr7HSmZWru4TqCEsMw9HwXHtCl4SLqgjli1TB4XgX+AP+Bs6+msp' \
			b'HDhEs+e7DsQgoXmzjz+2maMnwjBCFcINBTEIKyykhF2+OYT+CGVlJz/B94RLzcCVxgsML4HfmY74AG7vCrP6cGhdBKmeYXQAoRE6sZ0vhs2dgBnbe8cYGQEyIeIEHEYsvAsQzvu4RMjbjBedSdg16aUy9E/ZiC/3QiSa7bcOwOcosIOYswJrloEMwgtiyxBY' \
			b'IqQgSvT7UWKyi/kwQBF7iiCnChcgfTUNGYvh4rBuFnWiLg8ziq4SarRix2Q/pQu78OMQ7ABJHNjD8A+OHcORJYOIvmcggTgeFzjBKhjOH1ju3A85EFh2gkoctp07sFBGy/8CMji4fwigISrA4S2OY80C76qzAZ5p0NH2kE5L8yfUzidQEhzkgDIPH+S0MxCU' \
			b'J8COhUIReboCecLj7MYktOn2dGPiJBKE4VrONJEE8XG6oUQgqGX4/bhGSsOvvvFT8KDLxXjgvzsiQlETpoZyGEJ1p0CphEpF9wdVWbtABRJpPO/uAhG6856rGyWL+Wvy49/aACZPbdJtFAZqRdG+Yjb5fOIPT70nfbf5Gdyremr6/p6gS2ALc6bNfujCufWL' \
			b'gq9w4EjMLBuJ2fAAnaYdHaauhCRqUOfQcRqPxliV/RwkUf4vE5awghw6OiP5LhmdaVlra/cIzRx7Dvj++kaPvF+EffmHnN456tTOKfs3Rd+mq30bBhB1lOmd7jwNSDu7Jpg/+I1z1ri6rDoRkmyZ8k+BJnANbVDjpjndDqeuyRGX3kaYNLK6txHVuc/3bHVb' \
			b'qIGTk8aGlzzr/GmhZ/QBxUlHVji4wiTIk8ItQSIZZaUR1nhgRYOmsD2Css2bcwCnXd5Ox7d0X2C/JiGPvcsMc0YZrh4XCTK8MIgTZzLzoBbvC+/S5OkadyeLd/Nn/wR4iqaO3XmgxyxiYLaO0p+5QPRY3H9ZiB7X1UfZ3T/pyXv0SP2SC8cOkcSinsjsmMiv' \
			b'Bw1cv/ZBccMecSy08mOXLZfmU2CIPm8cUeUa3GcIJpQ1hIsjDnV2QMqS5bCHuII197SuNJTc8rHOLMKEOyBM/8AIU6ALiP20vZNToUtFltV+vENUQfWdR2fl1KByXEDp7zDOaU8HKLqtgFIB5W6A4iqgHB9QoCzrAUWdEFBUBZQKKHcDlHOZTrkuQFEXMhP7' \
			b'2GZfzxExzhgsjokMmjJ9UfOsd0WC5k9oGE8QEtE8A6KvoHApoLDWmHuBwEBN6Yi4wE3zmu0vx/hSufnTmyeEydCmniCWEkaYihEVI06LEdRIzqzz8HhRwtknANqEDV3FhooN94UNBAYXObB4vNhg/ROAdMKGM3EcrdhwndhgKzZcLjZciltoxYbd2ICrEUIZ' \
			b'NZTxDHCC6twZzU1yGzgXmJDc3D9KUEKLUELTtk1waydedOEJoT8U7wmiLtT+J4R3UEUhgNYmsXfwFa1IciZIcg7o4c8MPfxZoYd/KPTwd+xjLMKMO3h/Vsx47JhBt6/RGnoMzGDZXdi4BDcEIE/IHsFD0dYA9i4OnRUjHiVG0HLu1+0xcQBGkDSuZu6iQ8so' \
			b'tq0e+xOGMMLdxUezYsSjwghqN4/ErWoBSFCM65vhNNCTwM1xAp5pptNVt8uKEfsxgh54ZJ6Xj9cIYrAj0XaEDdX7smIDyAsb1vn4Xp4FNNALHxcwaPWESEKRE2brCCGq7+VjRQisz2fgeXm2CPEoOw+qwwlK7jxU18vHCg1YhSs0VGjYCQ2X4nkJdTktKPzQ' \
			b'MDG5H/AJFxGun4EeAhqowg08GU4HH3ByZwQiiCO7oOSQ78Tdmbhmrl/vN0xvSH4RfY3unvobtsl7PV05iPAu88P/azyw8LHJnbovrkuycqPtZf0SkhNtk9Lv7Z949Mdik8iZuGxWhKkIsxJhtv+vQhhdEWYRwmhGGHx6GcKciYNnRZj7QJirRxez9X8VupiK' \
			b'LovQxczOrRTI0jdv8CGGE8YSBhJGEUv4YRE5EDYYMxJgEFrEdm/KtqmlTfodbbHfbnfjNkLtQkM7oKXLUp2P1T3V9FTLsYJy5TZcpak2p5o8qsW5BqdqhzUtVQl8I1UFtaMGoPK3db2lElYDDUVBn3cVNgNuglrPYkdYRbgciL9boQI3DVVJFdQq71EXWAqC' \
			b'hKQTHfWCryZ/1FJBqb0epiRuQBNzkqWy1N2V1e7Tl70andkM5dN6iyj8YLpDRxTcb9VQ+ZGNbUc30P4MnRcP4dwRURTcNW+07SFQO/vdLZxvNqD+FmPh/Q28D3SJbwONONpHamMwTOFG0sDXtD+4p111oWMEoKgaECWQZ9/R1rba4v5n8BM7R/AOYDja2Dvt' \
			b'jAtvgLoAvzzWCbSa4/6y+EWqptS6w1ODu7v/0UstvtTvfK1smhd2vJ96fXb0L2+Ap8pwSs5NJNdhilC9cBX6llZ6nU2d9pBI0924PmqH+pVcQa81/UOSdLLSfP7vJv/xXU2T13hNq59iU6as+3VZhxwelnt4ZPYf9oR33KO8hjV59buyO9p+ajL7pi2KAO+Y' \
			b'+Ydd+mEId6476UQP7kAe4EwF6ycKpneWDUAQhzBhMGyZKHA7KHPfk/8i9hGxj0n+jLgfOi4ipj0t4YJYhFCEC5kmEUGCPDlnWVwWxdaL2PRu0QEK8ijDsBgRzlmUUPsU7SEue4R/x3w0Pvx20ODerv/zb9r39O43jkJGl/vzuPNFjLgQfNKaTfuEPtjBRVaH' \
			b'1nno/kOG76Pmg5jQ8f+0LUA3hx2Ua3PgQ3uP2PM64iu3Dta9Pje8a3doXN+31k1z8gPngcZBWh/l3axtc2Jw65oHPLjIXSoyLrff32c1dxdS0/FhPHqeUL3Ho73Xt+8/WP1Tw4/lNb49QqXHudy1B05GH/4Yl9yNKz7OFT9A9W8voAngLEtxcKZVMwo++oET' \
			b'MPedxo6D68TUEHN3PVhE7OvahGtGB071bIcuPNBOsywqiyHUprGzaeC84yM6uEIcNuq/v3aBFtUTHDz/2NZWsbtV2OYxHVwhDpsXWDwMXNcyXHPcA235y6KyMHRtHTtbB1qpHtHBFWJqLH2E1kEuN2taCHrgHPtAR5dlUVkmW4Pt2khyI7HNYzq4QkwNv4/U' \
			b'SFDR6xqKa+7jQOevZVFZNHV8vqet+OYxHVwhDhucu5UT70ubTNRTbjahWX6gU9tBD6DL5EwM5F75wQKrw/jdLQj9hR7RwRXisGH82hZU6np1a0Lv6Ps8SvfjxU+xz9Gd5gFW2oXPp2UpC//ddguD96RWhrPy3NLgP3psoWve2gMN3nd5/r4P3aGX2zhs8orr' \
			b'j6qwvBuWXfOYDq4Qh/kYnBaWfXNmB4vQ1Da1u02F5jEdXCG6g/12juios655TagOPwdbfODXNwc9MDriV1cHPEHfTOXvpUjyh01pnK3ku+YSDhb5lFP3BYrcNpdwsMgPm4w4ssiNO0DsaonoXfPAB9LX6hisgikf+wU8fzot6CWa8M1BB37gc+gz6449KbE+' \
			b'Vn4acOb66JtLO/hbpSk//YvXBn4Gf2EHa+PgTwiu7bMZXL3g8IMXJ8j/171l/Mbtdxc/B3Hm31IcrOmz+2DgwTXdNdd4sHYPc2q4Ru32zTUerN3DJw2uTLv4tfwVHqzdwycmrk27qrnGg7V7+BzItWlXN9d4sHZ988Z09PW1QHWIAUpad48BKEIKxG9VeFgK' \
			b'PbU3pf5B0BQDxK1A1LhFI63cxQmBliZj49oEg/8cW2/FRuXRE6D60X9tOO+2XADDUFXgcKCfsjpyFSqrTqw2tKoVfS+IoXndLlojK62PZYp1sXDhX5GHHaaCa5/gWsGWCopJxqSoZsrEneNWBhXvDdZuqJn05RbWSbnj8bfYgcn+Syt14Ca5OJeDu+YGEVrI' \
			b'C33IEhg9XrcUwtP3uAsevAVDPGcb97yKIRDnu9v/Dwf2dPs='

	_UPARTIAL = '\u2202' # \partial
	_USUM     = '\u2211' # \sum
	_UINTG    = '\u222b' # \int
	_UUNION   = '\u222a' # ||
	_USYMDIFF = '\u2296' # ^^
	_UXSECT   = '\u2229' # &&
	_UOR      = '\u2228' # or
	_UAND     = '\u2227' # and
	_UNOT     = '\u00ac' # not

	_LTR      = fr'[a-zA-Z]'
	_LTRU     = fr'[a-zA-Z_]'

	_VARTEX   = '(?:' + '|'.join (sorted ((x.replace ('\\', '\\\\').replace ('+', '\\+').replace ('*', '\\*').replace ('^', '\\^') for x in AST.Var.TEX2PY), reverse = True)) + ')'
	_VARTEX1  = fr'(?:(\d)|({_LTR})|(\\partial|\\infty))'
	_VARPY    = fr'(?:{_LTR}(?:\w|\\_)*(?<!_))'
	_VARUNI   = fr'(?:{"|".join (AST.Var.UNI2PY)})'
	_VAR      = fr'(?:{_VARPY}|{_VARTEX}(?!{_LTR})|{_VARUNI})'

	_STRS     = r"'(?:\\.|[^'])*'"
	_STRD     = r'"(?:\\.|[^"])*"'

	_FUNCPY   = f"(?:{'|'.join (sorted (AST.Func.PY, reverse = True))})"
	_FUNCTEX  = f"(?:{'|'.join (sorted (AST.Func.TEX, reverse = True))})"

	TOKENS    = OrderedDict ([ # order matters due to Python regex non-greedy or
		('UFUNC',        fr'\?'),
		('UFUNCPY',       r'Function'),
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})(?!{_LTRU})|(\${_LTRU}\w*)|\\operatorname\s*{{\s*(@|\\\%|\$?(?:{_LTR}|\\_)(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

		('LIM',          fr'\\lim(?!{_LTR})'),
		('SUM',          fr'\\sum(?:\s*\\limits)?(?!{_LTR})|{_USUM}'),
		('INTG',         fr'\\int(?:\s*\\limits)?(?!{_LTR})|{_UINTG}'),
		('LEFTDOT',      fr'\\left\s*\.'),
		('LEFT',         fr'\\left(?!{_LTRU})'),
		('RIGHT',        fr'\\right(?!{_LTRU})'),
		('CDOT',         fr'\\cdot(?!{_LTRU})'),
		('TO',           fr'\\to(?!{_LTRU})'),
		('UNION',        fr'\\cup(?!{_LTRU})|\|\|'),
		('SDIFF',        fr'\\ominus(?!{_LTRU})|\^\^'),
		('XSECT',        fr'\\cap(?!{_LTRU})|&&'),
		('MAPSTO',       fr'\\mapsto(?!{_LTRU})'),
		('EMPTYSET',     fr'\\emptyset(?!{_LTRU})'),
		('SETMINUS',     fr'\\setminus(?!{_LTRU})'),
		('SUBSTACK',      r'\\substack(?!{_LTRU})'),

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
		('FRAC',          r'\\frac(?!{_LTRU})'),
		('BINOM2',       fr'\\binom\s*{_VARTEX1}\s*{_VARTEX1}'),
		('BINOM1',       fr'\\binom\s*{_VARTEX1}'),
		('BINOM',         r'\\binom(?!{_LTRU})'),

		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\ne(?!g)q?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)(?!{_LTRU})|{"|".join (AST.Cmp.UNI2PY)}'),
		('IF',            r'if(?!{_LTRU})'),
		('ELSE',          r'else(?!{_LTRU})'),
		('OR',           fr'or\b|\\vee(?!{_LTRU})|{_UOR}'),
		('AND',          fr'and\b|\\wedge(?!{_LTRU})|{_UAND}'),
		('NOT',          fr'not\b|\\neg(?!{_LTRU})|{_UNOT}'),
		('SQRT',          r'sqrt\b|\\sqrt(?!{_LTRU})'),
		('LOG',           r'log\b|\\log(?!{_LTR})'),
		('LN',            r'ln\b|\\ln(?!{_LTRU})'),

		('NUM',           r'(?:(\d*\.\d+)|(\d+\.?))((?:[eE]|{[eE]})(?:[+-]?\d+|{[+-]?\d+}))?'),
		('VAR',          fr"(?:(?:(\\partial\s?|{_UPARTIAL})|(d))({_VAR})|({_VAR}))(?:_{{(\d+)}})?"),
		('ATTR',         fr'\.\s*(?:({_LTRU}\w*)|\\operatorname\s*{{\s*({_LTR}(?:\w|\\_)*)\s*}})'),
		('STR',          fr"((?<![.'|!)}}\]\w]){_STRS}|{_STRD})|\\text\s*{{\s*({_STRS}|{_STRD})\s*}}"),

		('SUB1',         fr'_{_VARTEX1}'),
		('SUB',           r'_'),
		('COLON',         r'{:}|:'),
		('SCOLON',        r';'),
		('CARET1',       fr'\^{_VARTEX1}'),
		('CARET',         r'\^'),
		('DBLSLASH',      r'\\\\'),
		('DBLSTAR',       r'\*\*'),
		('SLASHCURLYL',   r'\\{'),
		('SLASHCURLYR',   r'\\}'),
		('SLASHBRACKL',   r'\\\['),
		('CURLYL',        r'{'),
		('CURLYR',        r'}'),
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('BRACKL',        r'\['),
		('BRACKR',        r'\]'),
		('BAR',           r'\|'),
		('PLUS',          r'\+'),
		('MINUS',         r'-'),
		('STAR',          r'\*'),
		('DIVIDE',        r'/'),
		('EXCL',          r'!'),
		('AMP',           r'&'),
		('COMMA',         r','),
		('PRIME',         r"'"),
		('EQ',            r'='),
		('ignore',        r'\\[,:;]|\\?\s+|\\text\s*{\s*[^}]*\s*}'),
	])

	_PYGREEK_QUICK = '(?:' + '|'.join (sorted ((g for g in AST.Var.GREEK), reverse = True)) + ')'
	_PYMULTI_QUICK = '(?:' + '|'.join (sorted ((g for g in AST.Var.PY2TEXMULTI), reverse = True)) + ')'
	_VARPY_QUICK   = fr'(?:{_PYGREEK_QUICK}|{_LTR})'
	_VAR_QUICK     = fr'(?:{_VARPY_QUICK}|{_VARTEX}|{_VARUNI})'

	TOKENS_QUICK   = OrderedDict ([ # quick input mode different tokens (differences from normal)
		('FUNC',         fr'(@|\%|{_FUNCPY}(?!\w|\\_))|\\({_FUNCTEX})|(\${_LTRU}\w*)|\\operatorname\s*{{\s*(@|\\\%|{_LTR}(?:\w|\\_)*)\s*}}'), # AST.Func.ESCAPE, AST.Func.NOREMAP, AST.Func.NOEVAL HERE!

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

		('CMP',          fr'==|!=|<=|<|>=|>|in\b|not\s+in\b|(?:\\ne(?!g)q?|\\le|\\lt|\\ge|\\gt|\\in(?!fty)|\\notin)|{"|".join (AST.Cmp.UNI2PY)}'),
		('OR',           fr'or\b|\\vee|{_UOR}'),
		('AND',          fr'and\b|\\wedge|{_UAND}'),
		('NOT',          fr'not\b|\\neg|{_UNOT}'),
		('SQRT',          r'sqrt\b|\\sqrt'),
		('LOG',           r'log\b|\\log'),
		('LN',            r'ln\b|\\ln'),

		('VAR',          fr"(?:(?:(\\partial\s?|partial|{_UPARTIAL})|(d(?!elta)))({_VAR_QUICK})|(None|True|False|{_PYMULTI_QUICK}|{_VAR_QUICK}))(?:_{{(\d+)}})?"),
	])

	TOKENS_LONG    = OrderedDict () # initialized in __init__()

	_PARSER_TOP             = 'expr_scolon'
	_PARSER_CONFLICT_REDUCE = {'BAR'}

	# grammar definition and implementation

	def expr_scolon_1      (self, expr_scolon, SCOLON, expr_ass_lvals):                return expr_scolon if expr_ass_lvals == AST.CommaEmpty else AST.flatcat (';', expr_scolon, expr_ass_lvals)
	def expr_scolon_2      (self, expr_ass_lvals):                                     return expr_ass_lvals

	def expr_ass_lvals     (self, expr_commas):                                        return _expr_ass_lvals (expr_commas)

	def expr_commas_1      (self, expr_comma, COMMA):                                  return expr_comma if expr_comma.is_comma else AST (',', (expr_comma,))
	def expr_commas_2      (self, expr_comma):                                         return expr_comma
	def expr_commas_3      (self):                                                     return AST.CommaEmpty
	def expr_comma_1       (self, expr_comma, COMMA, expr_colon):                      return _expr_comma (expr_comma, expr_colon)
	def expr_comma_2       (self, expr_colon):                                         return expr_colon

	def expr_colon_1       (self, expr, COLON, expr_colon):                            return _expr_colon (expr, expr_colon)
	def expr_colon_2       (self, expr, COLON):                                        return AST ('-slice', expr, False, None)
	def expr_colon_3       (self, COLON, expr_colon):                                  return _ast_pre_slice (False, expr_colon)
	def expr_colon_4       (self, COLON):                                              return AST ('-slice', False, False, None)
	def expr_colon_5       (self, expr):                                               return expr

	def expr               (self, expr_ass):                                           return expr_ass

	def expr_ass_1         (self, expr_mapsto1, EQ, expr_mapsto2):                     return AST ('=', expr_mapsto1, expr_mapsto2)
	def expr_ass_2         (self, expr_mapsto):                                        return expr_mapsto

	def expr_mapsto_1      (self, expr_paren, MAPSTO, expr_colon):                     return _expr_mapsto (expr_paren.strip, expr_colon)
	def expr_mapsto_2      (self, expr_piece):                                         return expr_piece

	def expr_piece_1       (self, expr_or, IF, expr_ass, ELSE, expr_mapsto):           return _expr_piece (expr_or, expr_ass, expr_mapsto)
	def expr_piece_2       (self, expr_or, IF, expr_ass):                              return AST ('-piece', ((expr_or, expr_ass),))
	def expr_piece_3       (self, expr_or):                                            return expr_or

	def expr_or_1          (self, expr_or, OR, expr_and):                              return AST.flatcat ('-or', expr_or, expr_and)
	def expr_or_2          (self, expr_and):                                           return expr_and

	def expr_and_1         (self, expr_and, AND, expr_not):                            return AST.flatcat ('-and', expr_and, expr_not)
	def expr_and_2         (self, expr_not):                                           return expr_not

	def expr_not_1         (self, NOT, expr_not):                                      return AST ('-not', expr_not)
	def expr_not_2         (self, expr_cmp):                                           return expr_cmp

	def expr_cmp_1         (self, expr_cmp, CMP, expr_union):                          return _expr_cmp (expr_cmp, CMP, expr_union)
	def expr_cmp_2         (self, expr_union):                                         return expr_union

	def expr_union_1       (self, expr_union, UNION, expr_sdiff):                      return AST.flatcat ('||', expr_union, expr_sdiff)
	def expr_union_2       (self, expr_sdiff):                                         return expr_sdiff

	def expr_sdiff_1       (self, expr_sdiff, SDIFF, expr_xsect):                      return AST.flatcat ('^^', expr_sdiff, expr_xsect)
	def expr_sdiff_2       (self, expr_xsect):                                         return expr_xsect

	def expr_xsect_1       (self, expr_xsect, XSECT, expr_add):                        return AST.flatcat ('&&', expr_xsect, expr_add)
	def expr_xsect_2       (self, expr_add):                                           return expr_add

	def expr_add_1         (self, expr_add, PLUS, expr_mul_exp):                       return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2         (self, expr_add, MINUS, expr_mul_exp):                      return AST.flatcat ('+', expr_add, AST ('-', expr_mul_exp))
	def expr_add_3         (self, expr_add, SETMINUS, expr_mul_exp):                   return AST.flatcat ('+', expr_add, AST ('-', expr_mul_exp))
	def expr_add_4         (self, expr_mul_exp):                                       return expr_mul_exp

	def expr_mul_exp       (self, expr_mul_expr):                                      return expr_mul_expr
	def expr_mul_expr_1    (self, expr_mul_expr, CDOT, expr_neg):                      return AST.flatcat ('*exp', expr_mul_expr, expr_neg)
	def expr_mul_expr_2    (self, expr_mul_expr, STAR, expr_neg):                      return AST.flatcat ('*exp', expr_mul_expr, expr_neg)
	def expr_mul_expr_3    (self, expr_neg):                                           return expr_neg

	def expr_neg_1         (self, MINUS, expr_neg):                                    return _expr_neg (expr_neg)
	def expr_neg_2         (self, expr_diff):                                          return expr_diff

	def expr_diff          (self, expr_div):                                           return _expr_diff (expr_div)

	def expr_div_1         (self, expr_div, DIVIDE, expr_divm):                        return AST ('/', expr_div, expr_divm)
	def expr_div_2         (self, expr_mul_imp):                                       return expr_mul_imp
	def expr_divm_1        (self, MINUS, expr_divm):                                   return _expr_neg (expr_divm)
	def expr_divm_2        (self, expr_mul_imp):                                       return expr_mul_imp

	def expr_mul_imp_1     (self, expr_mul_imp, expr_intg):                            return _expr_mul_imp (expr_mul_imp, expr_intg)
	def expr_mul_imp_2     (self, expr_intg):                                          return expr_intg

	def expr_intg_1        (self, INTG, expr_sub, expr_super, expr_add):               return _expr_intg (expr_add, (expr_sub, expr_super))
	def expr_intg_2        (self, INTG, expr_add):                                     return _expr_intg (expr_add)
	def expr_intg_3        (self, expr_lim):                                           return expr_lim

	def expr_lim_1         (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                          return AST ('-lim', expr_neg, expr_var, expr)
	def expr_lim_2         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):  return AST ('-lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3         (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg): return AST ('-lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6         (self, expr_sum):                                                                        return expr_sum

	def expr_sum_1         (self, SUM, SUB, CURLYL, varass, CURLYR, expr_super, expr_neg):                          return AST ('-sum', expr_neg, varass [0], varass [1], expr_super)
	def expr_sum_2         (self, expr_diffp):                                                                      return expr_diffp

	def expr_diffp_1       (self, expr_diffp, PRIME):                                  return AST ('-diffp', expr_diffp.diffp, expr_diffp.count + 1) if expr_diffp.is_diffp else AST ('-diffp', expr_diffp, 1)
	def expr_diffp_2       (self, expr_func):                                          return expr_func

	def expr_func_1        (self, SQRT, expr_neg_arg):                                 return _expr_func (1, '-sqrt', expr_neg_arg)
	def expr_func_2        (self, SQRT, expr_super, expr_neg_arg):                     return AST ('^', _expr_func (1, '-sqrt', expr_neg_arg), expr_super)
	def expr_func_3        (self, SQRT, BRACKL, expr_commas, BRACKR, expr_neg_arg):    return _expr_func (1, '-sqrt', expr_neg_arg, expr_commas)
	def expr_func_4        (self, LN, expr_neg_arg):                                   return _expr_func (1, '-log', expr_neg_arg)
	def expr_func_5        (self, LN, expr_super, expr_neg_arg):                       return AST ('^', _expr_func (1, '-log', expr_neg_arg), expr_super)
	def expr_func_6        (self, LOG, expr_neg_arg):                                  return _expr_func (1, '-log', expr_neg_arg)
	def expr_func_7        (self, LOG, expr_super, expr_neg_arg):                      return AST ('^', _expr_func (1, '-log', expr_neg_arg), expr_super)
	def expr_func_8        (self, LOG, expr_sub, expr_neg_arg):                        return _expr_func (1, '-log', expr_neg_arg, expr_sub)
	def expr_func_9        (self, FUNC, expr_neg_arg):                                 return _expr_func_func (FUNC, expr_neg_arg)
	def expr_func_10       (self, FUNC, expr_super, expr_neg_arg):                     return _expr_func_func (FUNC, expr_neg_arg, expr_super)
	def expr_func_11       (self, expr_pow):                                           return expr_pow

	def expr_func_12       (self, SQRT, EQ, expr_mapsto):                              return AST ('=', ('@', 'sqrt'), expr_mapsto) # allow usage of function names in keyword arguments
	def expr_func_13       (self, LN, EQ, expr_mapsto):                                return AST ('=', ('@', 'ln'), expr_mapsto)
	def expr_func_14       (self, LOG, EQ, expr_mapsto):                               return AST ('=', ('@', 'log'), expr_mapsto)
	def expr_func_15       (self, FUNC, EQ, expr_mapsto):                              return AST ('=', ('@', _FUNC_name (FUNC)), expr_mapsto)

	def expr_pow_1         (self, expr_pow, expr_super):                               return AST ('^', expr_pow, expr_super)
	def expr_pow_2         (self, expr_fact):                                          return expr_fact

	def expr_fact_1        (self, expr_fact, EXCL):                                    return AST ('!', expr_fact)
	def expr_fact_2        (self, expr_attr):                                          return expr_attr

	def expr_attr_1        (self, expr_attr, ATTR):                                    return AST ('.', expr_attr, ATTR.grp [0] or ATTR.grp [1].replace ('\\', ''))
	def expr_attr_2        (self, expr_abs):                                           return expr_abs

	def expr_abs_1         (self, LEFT, BAR1, expr_commas, RIGHT, BAR2):               return AST ('|', expr_commas)
	def expr_abs_2         (self, BAR1, expr_commas, BAR2):                            return AST ('|', expr_commas)
	def expr_abs_3         (self, expr_paren):                                         return expr_paren

	def expr_paren_1       (self, expr_pcommas):                                       return AST ('(', expr_pcommas)
	def expr_paren_2       (self, expr_frac):                                          return expr_frac

	def expr_frac_1        (self, FRAC, expr_binom1, expr_binom2):                     return AST ('/', expr_binom1, expr_binom2)
	def expr_frac_2        (self, FRAC1, expr_binom):                                  return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_binom)
	def expr_frac_3        (self, FRAC2):                                              return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4        (self, expr_binom):                                         return expr_binom

	def expr_binom_1       (self, BINOM, expr_subs1, expr_subs2):                      return AST ('-func', 'binomial', (expr_subs1, expr_subs2))
	def expr_binom_2       (self, BINOM1, expr_subs):                                  return AST ('-func', 'binomial', (_ast_from_tok_digit_or_var (BINOM1), expr_subs))
	def expr_binom_3       (self, BINOM2):                                             return AST ('-func', 'binomial', (_ast_from_tok_digit_or_var (BINOM2), _ast_from_tok_digit_or_var (BINOM2, 3)))
	def expr_binom_4       (self, expr_subs):                                          return expr_subs

	def expr_subs_1        (self, LEFTDOT, expr_commas, RIGHT, BAR, SUB, CURLYL, subsvars, CURLYR): return _expr_subs (expr_commas, subsvars)
	def expr_subs_2        (self, expr_cases):                                         return expr_cases
	def subsvars_1         (self, SUBSTACK, CURLYL, subsvarss, CURLYR):                return subsvarss
	def subsvars_2         (self, varass):                                             return (varass,)
	def subsvarss_1        (self, subsvarsv, DBLSLASH):                                return subsvarsv
	def subsvarss_2        (self, subsvarsv):                                          return subsvarsv
	def subsvarsv_1        (self, subsvarsv, DBLSLASH, varass):                        return subsvarsv + (varass,)
	def subsvarsv_2        (self, varass):                                             return (varass,)

	def expr_cases_1       (self, BEG_CASES, casess, END_CASES):                       return AST ('{', ('-piece', casess))
	def expr_cases_2       (self, expr_mat):                                           return expr_mat
	def casess_1           (self, casessp, DBLSLASH):                                  return casessp
	def casess_2           (self, casessp):                                            return casessp
	def casessp_1          (self, casessp, DBLSLASH, casessc):                         return casessp + (casessc,)
	def casessp_2          (self, casessc):                                            return (casessc,)
	def casessc_1          (self, expr1, AMP, expr2):                                  return (expr1, expr2)
	def casessc_2          (self, expr, AMP):                                          return (expr, True)

	def expr_mat_1         (self, LEFT, BRACKL, BEG_MAT, mat_rows, END_MAT, RIGHT, BRACKR): return _expr_mat (mat_rows)
	def expr_mat_2         (self, BEG_MAT, mat_rows, END_MAT):                         return _expr_mat (mat_rows)
	def expr_mat_3         (self, BEG_BMAT, mat_rows, END_BMAT):                       return _expr_mat (mat_rows)
	def expr_mat_4         (self, BEG_VMAT, mat_rows, END_VMAT):                       return _expr_mat (mat_rows)
	def expr_mat_5         (self, BEG_PMAT, mat_rows, END_PMAT):                       return _expr_mat (mat_rows)
	def expr_mat_6         (self, expr_vec):                                           return expr_vec
	def mat_rows_1         (self, mat_row, DBLSLASH):                                  return mat_row
	def mat_rows_2         (self, mat_row):                                            return mat_row
	def mat_rows_3         (self):                                                     return ()
	def mat_row_1          (self, mat_row, DBLSLASH, mat_col):                         return mat_row + (mat_col,)
	def mat_row_2          (self, mat_col):                                            return (mat_col,)
	def mat_col_1          (self, mat_col, AMP, expr):                                 return mat_col + (expr,)
	def mat_col_2          (self, expr):                                               return (expr,)

	def expr_vec_1         (self, SLASHBRACKL, expr_commas, BRACKR):                   return _expr_vec (expr_commas)
	def expr_vec_2         (self, expr_bracket):                                       return expr_bracket

	def expr_bracket_1     (self, LEFT, BRACKL, expr_commas, RIGHT, BRACKR):           return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_2     (self, BRACKL, expr_commas, BRACKR):                        return AST ('[', expr_commas.comma if expr_commas.is_comma else (expr_commas,))
	def expr_bracket_3     (self, expr_curly):                                         return expr_curly

	def expr_curly_1       (self, LEFT, SLASHCURLYL, expr_commas, RIGHT, SLASHCURLYR): return _expr_curly (expr_commas, forceset = True)
	def expr_curly_2       (self, SLASHCURLYL, expr_commas, SLASHCURLYR):              return AST ('-set', expr_commas.comma) if expr_commas.is_comma else AST ('-set', (expr_commas,))
	def expr_curly_3       (self, SLASHCURLYL, expr_commas, CURLYR):                   return AST ('-set', expr_commas.comma) if expr_commas.is_comma else AST ('-set', (expr_commas,))
	def expr_curly_4       (self, CURLYL, expr_commas, CURLYR):                        return _expr_curly (expr_commas)
	def expr_curly_5       (self, expr_ufunc):                                         return expr_ufunc

	def expr_ufunc_1       (self, UFUNCPY, expr_pcommas1, expr_pcommas2):              return _expr_ufunc (expr_pcommas1, expr_pcommas2)
	def expr_ufunc_2       (self, UFUNC, expr_var, expr_pcommas):                      return _expr_ufunc (expr_pcommas, name = expr_var.var)
	def expr_ufunc_3       (self, UFUNC, expr_pcommas):                                return _expr_ufunc (expr_pcommas)
	def expr_ufunc_4       (self, expr_term):                                          return expr_term

	def expr_term_1        (self, expr_num):                                           return expr_num
	def expr_term_2        (self, expr_var):                                           return expr_var
	def expr_term_3        (self, STR):                                                return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1].replace ('\\}', '}')))
	def expr_term_4        (self, SUB):                                                return AST ('@', '_') # for last expression variable
	def expr_term_5        (self, EMPTYSET):                                           return AST.SetEmpty

	def expr_num           (self, NUM):                                                return _expr_num (NUM)
	def expr_var           (self, VAR):                                                return _expr_var (VAR)

	def expr_sub_1         (self, SUB, expr_frac):                                     return expr_frac
	def expr_sub_2         (self, SUB1):                                               return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1       (self, DBLSTAR, expr_neg_arg):                              return expr_neg_arg
	def expr_super_3       (self, CARET, expr_frac):                                   return expr_frac
	def expr_super_4       (self, CARET1):                                             return _ast_from_tok_digit_or_var (CARET1)

	def expr_neg_arg_1     (self, MINUS, expr_neg_arg):                                return _expr_neg (expr_neg_arg)
	def expr_neg_arg_2     (self, expr_diffp):                                         return expr_diffp

	def expr_pcommas_1     (self, LEFT, PARENL, expr_commas, RIGHT, PARENR):           return expr_commas
	def expr_pcommas_2     (self, PARENL, expr_commas, PARENR):                        return expr_commas

	def varass             (self, expr_var, EQ, expr_commas):                          return (expr_var, expr_commas)

	def caret_or_dblstar_1 (self, DBLSTAR):                                            return '**'
	def caret_or_dblstar_2 (self, CARET):                                              return '^'

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
			if rule == ('expr_func', ('FUNC', 'expr_neg_arg')):
				return self._insert_symbol (('PARENL', 'PARENR'))

			if rule == ('expr_paren', ('PARENL', 'expr_commas', 'PARENR')) and self.stack [-2].sym == 'expr_mul_imp' and \
					(self.stack [-2].red.is_attr or (self.stack [-2].red.is_var and self.stack [-2].red.var in _SP_USER_FUNCS)):
				return self._insert_symbol ('PARENR')

		if pos and rule [1] [pos - 1] == 'expr_commas' and rule [0] not in {'expr_abs', 'varass', 'expr_func'}: # {'expr_abs', 'expr_ufunc', 'varass'}:
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
		def postprocess (res):
			return (_ast_mulexps_to_muls (res [0].no_curlys).flat,) + res [1:] if isinstance (res [0], AST) else res

		if not text.strip:
			return (AST.VarNull, 0, [])

		self.parse_results  = [] # [(reduction, erridx, autocomplete), ...]
		self.autocomplete   = []
		self.autocompleting = True
		self.erridx         = None

		lalr1.LALR1.parse (self, text)

		if not self.parse_results:
			return (None, 0, [])

		rated = sorted ((r is None, -e if e is not None else float ('-inf'), len (a), i, (r, e, a))
			for i, (r, e, a) in enumerate (self.parse_results))

		if os.environ.get ('SYMPAD_DEBUG'):
			rated = list (rated)

			print (file = sys.stderr)

			for res in rated [:32]:
				print ('parse:', res [-1], file = sys.stderr)

			if len (rated) > 32:
				print (f'... total {len (rated)}', file = sys.stderr)

			print (file = sys.stderr)

		res = next (iter (rated)) [-1]

		return postprocess (res)

def set_sp_user_funcs (user_funcs):
	global _SP_USER_FUNCS
	_SP_USER_FUNCS = user_funcs

def set_sp_user_vars (user_vars):
	global _SP_USER_VARS
	_SP_USER_VARS = user_vars

class sparser: # for single script
	set_sp_user_funcs = set_sp_user_funcs
	set_sp_user_vars  = set_sp_user_vars
	Parser            = Parser

_RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: # DEBUG!
	p = Parser ()

	# p.set_quick (True)
	# print (p.tokenize (r"""{\partial x : Sum (\left|\left|dz\right|\right|, (x, lambda x, y, z: 1e100 : \partial !, {\emptyset&&0&&None} / {-1.0 : a,"str" : False,1e100 : True})),.1 : \sqrt[\partial ' if \frac1xyzd]Sum (\fracpartialx1, (x, xyzd / "str", Sum (-1, (x, partialx, \partial ))))}'''"""))

	# p.set_sp_user_funcs ({'N'})

	a = p.parse (r"x_{1}")
	print (a)

	# a = sym.ast2spt (a)
	# print (a)
