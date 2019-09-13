# AST translations for funtions to display or convert to internal AST or SymPy S() escaping.

from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT

_AST_StrPlus = AST ('"', '+')

#...............................................................................................
def _xlat_f2a_slice (*args):
	if len (args) == 1:
		return AST ('slice', None, args [0], None)
	if len (args) == 2:
		return AST ('slice', args [0], args [1], None)
	else:
		return AST ('slice', args [0], args [1], args [2])

_xlat_f2a_Add_invert = {'==': '==', '!=': '!=', '<': '>', '<=': '>=', '>': '<', '>=': '<='}

def _xlat_f2a_And (*args): # patch together out of order extended comparison objects potentially inverting comparisons
	def concat (lhs, rhs):
		return AST ('<>', lhs.lhs, lhs.cmp + rhs.cmp)

	def invert (ast):
		cmp = []
		lhs = ast.lhs

		for c in ast.cmp:
			v = _xlat_f2a_Add_invert.get (c [0])

			if v is None:
				return None

			cmp.append ((v, lhs))

			lhs = c [1]

		return AST ('<>', lhs, tuple (cmp [::-1]))

	def match (ast):
		li, ll = None, 0
		ri, rl = None, 0

		for i in range (len (args)):
			if args [i].is_cmp:
				if ast.lhs == args [i].cmp [-1] [1] and (li is None or args [i].cmp.len > ll):
					li, ll = i, args [i].cmp.len

				if ast.cmp [-1] [1] == args [i].lhs and (ri is None or args [i].cmp.len > rl):
					ri, rl = i, args [i].cmp.len

		return li, ri, ll + rl

	itr  = iter (args)
	args = []

	for arg in itr:
		if not args or not arg.is_cmp:
			args.append (arg)

		else:
			while 1:
				li, ri, l = match (arg)
				argv      = invert (arg)

				if argv is not None:
					liv, riv, lv = match (argv)

					if lv > l:
						li, ri = liv, riv
						arg    = argv

				if li is None or li == ri:
					if ri is None:
						args.append (arg)
						break

					else:
						arg = concat (arg, args [ri])
						del args [ri]

				elif ri is None:
					arg = concat (args [li], arg)
					del args [li]

				else:
					i1, i2 = min (li, ri), max (li, ri)
					arg    = concat (concat (args [li], arg), args [ri])

					del args [i2], args [i1]

	if len (args) == 1:
		return args [0]
	else:
		return AST ('and', tuple (args))

def _xlat_f2a_Lambda (args, expr):
	args = args.strip_paren
	args = args.comma if args.is_comma else (args,)

	return AST ('lamb', expr, tuple (c.var for c in args))

def _xlat_f2a_Pow (ast = AST.VarNull, exp = AST.VarNull):
	return AST ('^', ast, exp)

def _xlat_f2a_Matrix (ast = AST.VarNull):
	if ast.is_null_var:
		return AST.MatEmpty

	if ast.is_brack:
		if not ast.brack:
			return AST.MatEmpty

		elif not ast.brack [0].is_brack: # single layer or brackets, column matrix?
			return AST ('mat', tuple ((c,) for c in ast.brack))

		elif ast.brack [0].brack:
			rows = [ast.brack [0].brack]
			cols = len (rows [0])

			for row in ast.brack [1 : -1]:
				if row.brack.len != cols:
					break

				rows.append (row.brack)

			else:
				l = ast.brack [-1].brack.len

				if l <= cols:
					if ast.brack.len > 1:
						rows.append (ast.brack [-1].brack + (AST.VarNull,) * (cols - l))

					if l != cols:
						return AST ('mat', tuple (rows))
					elif cols > 1:
						return AST ('mat', tuple (rows))
					else:
						return AST ('mat', tuple ((r [0],) for r in rows))

	return None

def _xlat_f2a_Piecewise (*args):
	pcs = []

	if not args or args [0].is_null_var:
		return AST ('piece', ((AST.VarNull, AST.VarNull),))

	if len (args) > 1:
		for c in args [:-1]:
			c = c.strip

			if not c.is_comma or c.comma.len != 2:
				return None

			pcs.append (c.comma)

	ast = args [-1]

	if not ast.is_paren:
		return None

	ast = ast.strip
	pcs = tuple (pcs)

	if not ast.is_comma:
		return AST ('piece', pcs + ((ast, AST.VarNull),))
	elif ast.comma.len == 0:
		return AST ('piece', pcs + ())

	if not ast.comma [0].is_comma:
		if ast.comma.len == 1:
			return AST ('piece', pcs + ((ast.comma [0], AST.VarNull),))
		elif ast.comma.len == 2:
			return AST ('piece', pcs + ((ast.comma [0], True if ast.comma [1] == AST.True_ else ast.comma [1]),))

	return None

def _xlat_f2a_Derivative_NAT (ast = AST.VarNull, *dvs, **kw):
	if not kw:
		return _xlat_f2a_Derivative (ast, *dvs)

def _xlat_f2a_Derivative (ast = AST.VarNull, *dvs, **kw):
	ds = []

	if not dvs:
		# vars = ast.free_vars

		# if len (vars) == 1:
		# 	ds = [AST ('@', f'd{vars.pop ().var}')]
		if ast.is_diffp:
			return AST ('diffp', ast.diffp, ast.count + 1)
		else:
			return AST ('diffp', ast, 1)

	else:
		dvs = list (dvs [::-1])

		while dvs:
			v = dvs.pop ()

			if not v.is_var:
				return None
			elif dvs and dvs [-1].is_num_pos_int:
				ds.append (AST ('^', ('@', f'd{v.var}'), dvs.pop ()))
			else:
				ds.append (AST ('@', f'd{v.var}'))

	return AST ('diff', ast, tuple (ds))

def _xlat_f2a_Integral_NAT (ast = None, dvab = None, *args, **kw):
	if not kw:
		return _xlat_f2a_Integral (ast, dvab, *args, **kw)

def _xlat_f2a_Integral (ast = None, dvab = None, *args, **kw):
	if ast is None:
		return AST ('intg', AST.VarNull, AST.VarNull)

	if dvab is None:
		vars = ast.free_vars

		if len (vars) == 1:
			return AST ('intg', ast, ('@', f'd{vars.pop ().var}'))

		return AST ('intg', AST.VarNull, AST.VarNull)

	dvab = dvab.strip_paren
	ast2 = None

	if dvab.is_comma:
		if dvab.comma and dvab.comma [0].is_nonconst_var:
			if dvab.comma.len == 1:
				ast2 = AST ('intg', ast, ('@', f'd{dvab.comma [0].var}'))
			elif dvab.comma.len == 2:
				ast2 = AST ('intg', ast, ('@', f'd{dvab.comma [0].var}'), AST.Zero, dvab.comma [1])
			elif dvab.comma.len == 3:
				ast2 = AST ('intg', ast, ('@', f'd{dvab.comma [0].var}'), dvab.comma [1], dvab.comma [2])

	elif dvab.is_var:
		ast2 = AST ('intg', ast, ('@', f'd{dvab.var}'))

	if ast2 is None:
		return None

	return _xlat_f2a_Integral (ast2, *args) if args else ast2

_xlat_f2a_Limit_dirs = {AST ('"', '+'): ('+',), AST ('"', '-'): ('-',), AST ('"', '+-'): ()}

def _xlat_f2a_Limit (ast = AST.VarNull, var = AST.VarNull, to = AST.VarNull, dir = _AST_StrPlus):
	return AST ('lim', ast, var, to, *_xlat_f2a_Limit_dirs [dir])

def _xlat_f2a_Sum_NAT (ast = AST.VarNull, ab = None, **kw):
	if not kw:
		return _xlat_f2a_Sum (ast, ab, **kw)

def _xlat_f2a_Sum (ast = AST.VarNull, ab = None, **kw):
	if ab is None:
		return AST ('sum', ast, AST.VarNull, AST.VarNull, AST.VarNull)

	ab = ab.strip_paren

	if ab.is_var:
		return AST ('sum', ast, ab, AST.VarNull, AST.VarNull)
	elif ab.is_comma and ab.comma and ab.comma.len <= 3 and ab.comma [0].is_var:
		return AST ('sum', ast, *ab.comma, *((AST.VarNull,) * (3 - ab.comma.len)))

	return None

_XLAT_FUNC2AST_ALL    = {
	'slice'                : _xlat_f2a_slice,

	'Eq'                   : lambda a, b: AST ('<>', a, (('==', b),)),
	'Ne'                   : lambda a, b: AST ('<>', a, (('!=', b),)),
	'Lt'                   : lambda a, b: AST ('<>', a, (('<',  b),)),
	'Le'                   : lambda a, b: AST ('<>', a, (('<=', b),)),
	'Gt'                   : lambda a, b: AST ('<>', a, (('>',  b),)),
	'Ge'                   : lambda a, b: AST ('<>', a, (('>=', b),)),

	'Or'                   : lambda *args: AST ('or', tuple (args)),
	'And'                  : _xlat_f2a_And,
	'Not'                  : lambda not_: AST ('not', not_),
}

_XLAT_FUNC2AST_REIM = {
	'Re'                   : lambda *args: AST ('func', 're', tuple (args)),
	'Im'                   : lambda *args: AST ('func', 'im', tuple (args)),
}

_XLAT_FUNC2AST_TEXNAT = {
	'abs'                  : lambda ast: AST ('|', ast),
	'Abs'                  : lambda ast: AST ('|', ast),
	'exp'                  : lambda ast: AST ('^', AST.E, ast),
	'factorial'            : lambda ast: AST ('!', ast),
	'Lambda'               : _xlat_f2a_Lambda,
	'Matrix'               : _xlat_f2a_Matrix,
	'MutableDenseMatrix'   : _xlat_f2a_Matrix,
	'Piecewise'            : _xlat_f2a_Piecewise,
	'Pow'                  : _xlat_f2a_Pow,
	'pow'                  : _xlat_f2a_Pow,
	'Tuple'                : lambda *args: AST ('(', (',', args)),

	'Limit'                : _xlat_f2a_Limit,
	'limit'                : _xlat_f2a_Limit,

	'EmptySet'             : lambda *args: AST.SetEmpty,
	'FiniteSet'            : lambda *args: AST ('set', tuple (args)),
	'Contains'             : lambda a, b: AST ('<>', a, (('in', b),)),
	'Complement'           : lambda *args: AST ('+', (args [0], ('-', args [1]))),
	'Intersection'         : lambda *args: AST ('&&', tuple (args)),
	'Union'                : lambda *args: AST ('||', tuple (args)),
}

XLAT_FUNC2AST_TEX = {**_XLAT_FUNC2AST_ALL, **_XLAT_FUNC2AST_TEXNAT,
	'Add'                  : lambda *args, **kw: AST ('+', args),
	'Mul'                  : lambda *args, **kw: AST ('*', args),

	'Derivative'           : _xlat_f2a_Derivative,
	'Integral'             : _xlat_f2a_Integral,
	'Sum'                  : _xlat_f2a_Sum,
	'diff'                 : _xlat_f2a_Derivative,
	'integrate'            : _xlat_f2a_Integral,
	'summation'            : _xlat_f2a_Sum,

	'SparseMatrix'         : _xlat_f2a_Matrix,
	'MutableSparseMatrix'  : _xlat_f2a_Matrix,
	'ImmutableDenseMatrix' : _xlat_f2a_Matrix,
	'ImmutableSparseMatrix': _xlat_f2a_Matrix,

	'diag'                 : True,
	'eye'                  : True,
	'ones'                 : True,
	'zeros'                : True,
}

XLAT_FUNC2AST_NAT = {**_XLAT_FUNC2AST_ALL, **_XLAT_FUNC2AST_REIM, **_XLAT_FUNC2AST_TEXNAT,
	'Add'                  : lambda *args, **kw: None if kw else AST ('+', args),
	'Mul'                  : lambda *args, **kw: None if kw else AST ('*', args),

	'Derivative'           : _xlat_f2a_Derivative_NAT,
	'Integral'             : _xlat_f2a_Integral_NAT,
	'Sum'                  : _xlat_f2a_Sum_NAT,
}

XLAT_FUNC2AST_PY  = {**_XLAT_FUNC2AST_ALL, **_XLAT_FUNC2AST_REIM,
	'Gamma'                : lambda *args: AST ('func', 'gamma', tuple (args)),
}

def xlat_funcs2asts (ast, xlat, func_call = None): # translate eligible functions in tree to other AST representations
	if not isinstance (ast, AST):
		return ast

	if ast.is_func:
		xact = xlat.get (ast.func)

		if xact is not None:
			args = AST (*(xlat_funcs2asts (arg, xlat, func_call = func_call) for arg in ast.args))

			try:
				if xact is True: # True means execute function and use return value for ast
					return func_call (ast.func, args) # not checking func_call None because that should never happen

				xargs, xkw = AST.args2kwargs (args)
				ast2       = xact (*xargs, **xkw)

				if ast2 is not None:
					return ast2

			except:
				pass

			return AST ('func', ast.func, args)

	return AST (*(xlat_funcs2asts (e, xlat, func_call = func_call) for e in ast))

#...............................................................................................
def _xlat_f2t_SUBS_collect (ast, tail): # collapse multiple nested Subs() and .subs()
	try:
		if ast.is_func_Subs:
			if len (ast.args) == 3:
				vars = ast.args [1].strip_paren
				subs = ast.args [2].strip_paren

				if vars.is_comma and subs.is_comma and vars.comma.len == subs.comma.len:
					return _xlat_f2t_SUBS_collect (ast.args [0], list (zip (vars.comma, subs.comma)) + tail)

				return _xlat_f2t_SUBS_collect (ast.args [0], [(vars, subs)] + tail)

		elif ast.is_attr_func and ast.attr == 'subs':
			if ast.args.len == 2:
				return _xlat_f2t_SUBS_collect (ast.obj, [(ast.args [0], ast.args [1])] + tail)

			elif ast.args.len == 1:
				arg = ast.args [0].strip_paren

				if arg.is_dict:
					return _xlat_f2t_SUBS_collect (ast.obj, list (arg.dict) + tail)

				elif arg.op in {',', '[', 'set'}:
					args = []

					for arg in arg [1]:
						arg = arg.strip_paren

						if arg.op not in {',', '['} or arg [1].len != 2:
							break

						args.append (arg [1])

					else:
						return _xlat_f2t_SUBS_collect (ast.obj, args + tail)

	except:
		pass

	return ast, tail

def _xlat_f2t_SUBS (ast2tex, ast): # handles both Subs() and .subs() and collapses nested calls into one substitution
	ast, subs = _xlat_f2t_SUBS_collect (ast, [])

	if len (subs) == 1:
		return f'\\left. {ast2tex (ast)} \\right|_{{{ast2tex (subs [0] [0])}={ast2tex (subs [0] [1])}}}'

	elif len (subs) > 1:
		asss = ' \\\\ '.join (f'{ast2tex (v)}={ast2tex (s)}' for v, s in subs)

		return f'\\left. {ast2tex (ast)} \\right|_{{\\substack{{{asss}}}}}'

	return None

_XLAT_FUNC2TEX = {
	'beta'    : lambda ast2tex, *args: f'\\beta\\left({ast2tex (AST.tuple2ast (args))} \\right)',
	'gamma'   : lambda ast2tex, *args: f'\\Gamma\\left({ast2tex (AST.tuple2ast (args))} \\right)',
	'Gamma'   : lambda ast2tex, *args: f'\\Gamma\\left({ast2tex (AST.tuple2ast (args))} \\right)',
	'Lambda'  : lambda ast2tex, *args: f'\\Lambda\\left({ast2tex (AST.tuple2ast (args))} \\right)',
	'zeta'    : lambda ast2tex, *args: f'\\zeta\\left({ast2tex (AST.tuple2ast (args))} \\right)',

	're'      : lambda ast2tex, *args: f'\\Re\\left({ast2tex (AST.tuple2ast (args))} \\right)',
	'im'      : lambda ast2tex, *args: f'\\Im\\left({ast2tex (AST.tuple2ast (args))} \\right)',

	'binomial': lambda ast2tex, *args: f'\\binom{{{ast2tex (args [0])}}}{{{ast2tex (args [1])}}}' if len (args) == 2 else None,

	'Subs'    : lambda ast2tex, *args: _xlat_f2t_SUBS (ast2tex, AST ('func', 'Subs', args)),
}

_XLAT_ATTRFUNC2TEX = {
	'diff'     : lambda ast2tex, ast, *dvs, **kw: ast2tex (_xlat_f2a_Derivative (ast, *dvs, **kw)),
	'integrate': lambda ast2tex, ast, dvab = None, *args, **kw: ast2tex (_xlat_f2a_Integral (ast, dvab, *args, **kw)),
	'limit'    : lambda ast2tex, ast, var = AST.VarNull, to = AST.VarNull, dir = _AST_StrPlus: ast2tex (_xlat_f2a_Limit (ast, var, to, dir)),

	'subs'     : lambda ast2tex, ast, *args: _xlat_f2t_SUBS (ast2tex, AST ('.', ast, 'subs', args)),
}

def xlat_func2tex (ast, ast2tex):
	xact = _XLAT_FUNC2TEX.get (ast.func)

	if xact:
		args, kw = AST.args2kwargs (ast.args)

		try:
			return xact (ast2tex, *args, **kw)
		except:
			pass

	return None

def xlat_attr2tex (ast, ast2tex):
	if ast.is_attr_func:
		xact = _XLAT_ATTRFUNC2TEX.get (ast.attr)

		if xact:
			args, kw = AST.args2kwargs (ast.args)

			try:
				return xact (ast2tex, ast.obj, *args, **kw)
			except:
				pass

	return None

#...............................................................................................
def _xlat_pyS (ast, need = False): # Python S(1)/2 escaping where necessary
	if not isinstance (ast, AST):
		return ast, False

	if ast.is_num:
		if need:
			return AST ('func', 'S', (ast,)), True
		else:
			return ast, False

	if ast.is_comma or ast.is_brack:
		return AST (ast.op, tuple (_xlat_pyS (a) [0] for a in ast [1])), False

	if ast.is_curly or ast.is_paren or ast.is_minus:
		expr, has = _xlat_pyS (ast [1], need)

		return AST (ast.op, expr), has

	if ast.is_add or ast.is_mul:
		es  = [_xlat_pyS (a) for a in ast [1] [1:]]
		has = any (e [1] for e in es)
		e0  = _xlat_pyS (ast [1] [0], need and not has)

		return AST (ast.op, (e0 [0],) + tuple (e [0] for e in es)), has or e0 [1]

	if ast.is_div:
		denom, has = _xlat_pyS (ast.denom)
		numer      = _xlat_pyS (ast.numer, not has) [0]

		return AST ('/', numer, denom), True

	if ast.is_pow:
		exp, has = _xlat_pyS (ast.exp)
		base     = _xlat_pyS (ast.base, not (has or exp.is_num_pos)) [0]

		return AST ('^', base, exp), True

	es = [_xlat_pyS (a) for a in ast]

	# TODO: '<>' might be problematic in cases where it has an 'in' or 'notin'
	return AST (*tuple (e [0] for e in es)), \
			ast.op in {'=', '<>', '@', '.', '|', '!', 'log', 'sqrt', 'func', 'lim', 'sum', 'diff', 'intg', 'vec', 'mat', 'piece', 'lamb', '||', '^^', '&&', 'or', 'and', 'not'} or any (e [1] for e in es)

xlat_pyS = lambda ast: _xlat_pyS (ast) [0]

#...............................................................................................
class sxlat: # for single script
	XLAT_FUNC2AST_TEX = XLAT_FUNC2AST_TEX
	XLAT_FUNC2AST_NAT = XLAT_FUNC2AST_NAT
	XLAT_FUNC2AST_PY  = XLAT_FUNC2AST_PY
	xlat_funcs2asts   = xlat_funcs2asts
	xlat_func2tex     = xlat_func2tex
	xlat_attr2tex     = xlat_attr2tex
	xlat_pyS          = xlat_pyS
	_xlat_f2a_And     = _xlat_f2a_And

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: # DEBUG!
# 	ast = AST ('func', 'Matrix', (('[', ()),))
# 	res = _xlat_f2a_Matrix (ast.args [0])
# 	print (res)
