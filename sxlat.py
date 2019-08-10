# Translate SymPy functions to other ASTs or text for further use or just display.

import sympy as sp

from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT
import sym           # AUTO_REMOVE_IN_SINGLE_SCRIPT

def _xlat_func_Derivative (ast = AST.VarNull, *dvs):
	ds = []

	if not dvs:
		vars = ast.free_vars ()

		if len (vars) == 1:
			ds = [AST ('@', f'd{vars.pop ().var}')]

	else:
		dvs = list (dvs [::-1])

		while dvs:
			v = dvs.pop ()

			if not v.is_var:
				return None
			elif dvs and dvs [-1].is_pos_int:
				ds.append (AST ('^', ('@', f'd{v.var}'), dvs.pop ()))
			else:
				ds.append (AST ('@', f'd{v.var}'))

	return AST ('diff', ast, tuple (ds))

def _xlat_func_Integral (ast = None, dvab = None, *args):
	if ast is None:
		return AST ('intg', AST.VarNull, AST.VarNull)

	if dvab is None:
		vars = ast.free_vars ()

		if len (vars) == 1:
			return AST ('intg', ast, ('@', f'd{vars.pop ().var}'))

		return AST ('intg', AST.VarNull, AST.VarNull)

	dvab = dvab.strip_paren ()
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

	return _xlat_func_Integral (ast2, *args) if args else ast2

_xlat_func_Limit_dirs = {AST ('"', '+'): ('+',), AST ('"', '-'): ('-',), AST ('"', '+-'): ()}

def _xlat_func_Lambda (args, expr):
	args = args.strip_paren ()
	args = args.comma if args.is_comma else (args,)

	return AST ('lamb', expr, args)

def _xlat_func_Limit (ast = AST.VarNull, var = AST.VarNull, to = AST.VarNull, dir = AST ('"', '+')):
	return AST ('lim', ast, var, to, *_xlat_func_Limit_dirs [dir])

def _xlat_func_Pow (ast = AST.VarNull, exp = AST.VarNull):
	return AST ('^', ast, exp)

def _xlat_func_Matrix (ast = AST.VarNull):
	if ast.is_null_var:
		return AST ('vec', ())

	if ast.is_brack and ast.brack:
		if not ast.brack [0].is_brack: # single layer or brackets, column matrix?
			return AST ('vec', ast.brack)

		elif ast.brack [0].brack:
			rows = [ast.brack [0].brack]
			cols = len (rows [0])

			for row in ast.brack [1 : -1]:
				if len (row.brack) != cols:
					break

				rows.append (row.brack)

			else:
				l = len (ast.brack [-1].brack)

				if l <= cols:
					if len (ast.brack) > 1:
						rows.append (ast.brack [-1].brack + (AST.VarNull,) * (cols - l))

					if l != cols:
						return AST ('mat', tuple (rows))
					elif cols > 1:
						return AST ('mat', tuple (rows))
					else:
						return AST ('vec', tuple (r [0] for r in rows))

	return None

def _xlat_func_Piecewise (*args):
	pcs = []

	if not args or args [0].is_null_var:
		return AST ('piece', ((AST.VarNull, AST.VarNull),))

	if len (args) > 1:
		for c in args [:-1]:
			c = c.strip ()

			if not c.is_comma or len (c.comma) != 2:
				return None

			pcs.append (c.comma)

	ast = args [-1]

	if not ast.is_paren:
		return None

	ast = ast.strip ()
	pcs = tuple (pcs)

	if not ast.is_comma:
		return AST ('piece', pcs + ((ast, AST.VarNull),))
	elif len (ast.comma) == 0:
		return AST ('piece', pcs + ())

	if not ast.comma [0].is_comma:
		if len (ast.comma) == 1:
			return AST ('piece', pcs + ((ast.comma [0], AST.VarNull),))
		elif len (ast.comma) == 2:
			return AST ('piece', pcs + ((ast.comma [0], True if ast.comma [1] == AST.True_ else ast.comma [1]),))

	return None

def _xlat_func_Sum (ast = AST.VarNull, ab = None):
	if ab is None:
		return AST ('sum', ast, AST.VarNull, AST.VarNull, AST.VarNull)

	ab = ab.strip_paren ()

	if ab.is_var:
		return AST ('sum', ast, ab, AST.VarNull, AST.VarNull)
	elif ab.is_comma and ab.comma and ab.comma.len <= 3 and ab.comma [0].is_var:
		return AST ('sum', ast, *ab.comma, *((AST.VarNull,) * (3 - ab.comma.len)))

	return None

XLAT_FUNC2AST_NAT = {
	'abs'                  : lambda ast: AST ('|', ast),
	'Abs'                  : lambda ast: AST ('|', ast),
	'Derivative'           : _xlat_func_Derivative,
	'diff'                 : _xlat_func_Derivative,
	'exp'                  : lambda ast: AST ('^', AST.E, ast),
	'factorial'            : lambda ast: AST ('!', ast),
	'Integral'             : _xlat_func_Integral,
	'integrate'            : _xlat_func_Integral,
	'Lambda'               : _xlat_func_Lambda,
	'Limit'                : _xlat_func_Limit,
	'limit'                : _xlat_func_Limit,
	'Matrix'               : _xlat_func_Matrix,
	'MutableDenseMatrix'   : _xlat_func_Matrix,
	'Piecewise'            : _xlat_func_Piecewise,
	'Pow'                  : _xlat_func_Pow,
	'pow'                  : _xlat_func_Pow,
	'Sum'                  : _xlat_func_Sum,
	'Tuple'                : lambda *args: AST ('(', (',', args)),
}

XLAT_FUNC2AST_TEX = {**XLAT_FUNC2AST_NAT,
	'SparseMatrix'         : _xlat_func_Matrix,
	'MutableSparseMatrix'  : _xlat_func_Matrix,
	'ImmutableDenseMatrix' : _xlat_func_Matrix,
	'ImmutableSparseMatrix': _xlat_func_Matrix,
	'diag'                 : True,
	'eye'                  : True,
	'ones'                 : True,
	'zeros'                : True,
}

def _xlat_func2ast (xact, args):
	xargs = []
	xkw   = {}

	for arg in args:
		if arg.is_ass:
			xkw [arg.lhs.as_identifier ()] = arg.rhs
		elif xkw:
			raise SyntaxError ('positional argument follows keyword argument')
		else:
			xargs.append (arg)

	return xact (*xargs, **xkw)

def xlat_func2asts (ast, xlat): # translate eligible functions in tree to other AST representations
	if not isinstance (ast, AST):
		return ast

	if ast.is_func:
		xact = xlat.get (ast.func)

		if xact is not None:
			args = AST (*(xlat_func2asts (arg, xlat) for arg in ast.args))

			if xact is True: # True means execute function and use return value for ast
				return sym.spt2ast (sym._ast_func_call (getattr (sp, ast.func), args))

			try:
				ast2 = _xlat_func2ast (xact, args)

				if ast2 is not None:
					return ast2

			except:
				pass

			return AST ('func', ast.func, args)

	return AST (*(xlat_func2asts (e, xlat) for e in ast))

_XLAT_FUNC2TEX = {
	'beta'    : lambda args: f'\\beta\\left({sym._ast2tex (sym._tuple2ast (args))} \\right)',
	'gamma'   : lambda args: f'\\Gamma\\left({sym._ast2tex (sym._tuple2ast (args))} \\right)',
	'Gamma'   : lambda args: f'\\Gamma\\left({sym._ast2tex (sym._tuple2ast (args))} \\right)',
	'Lambda'  : lambda args: f'\\Lambda\\left({sym._ast2tex (sym._tuple2ast (args))} \\right)',
	'zeta'    : lambda args: f'\\zeta\\left({sym._ast2tex (sym._tuple2ast (args))} \\right)',
	'binomial': lambda args: f'\\binom{{{sym._ast2tex (args [0])}}}{{{sym._ast2tex (args [1])}}}' if len (args) == 2 else None,
}

def xlat_func2tex (ast):
	xact = _XLAT_FUNC2TEX.get (ast.func)

	if xact:
		return xact (ast.args)

	return None

class sxlat: # for single script
	XLAT_FUNC2AST_NAT = XLAT_FUNC2AST_NAT
	XLAT_FUNC2AST_TEX = XLAT_FUNC2AST_TEX
	xlat_func2asts    = xlat_func2asts
	xlat_func2tex     = xlat_func2tex

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
# 	ast = AST ('(', (',', (('#', '1'), ('#', '2'))))
# 	res = _XLAT_FUNC2AST_NAT ['Piecewise'] (ast)
# 	print (res)
