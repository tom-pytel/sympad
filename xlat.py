# Translate SymPy functions to other ASTs for display.

from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT

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
		if dvab.commas and dvab.commas [0].is_nonconst_var:
			if dvab.commas.len == 1:
				ast2 = AST ('intg', ast, ('@', f'd{dvab.commas [0].var}'))
			elif dvab.commas.len == 2:
				ast2 = AST ('intg', ast, ('@', f'd{dvab.commas [0].var}'), AST.Zero, dvab.commas [1])
			elif dvab.commas.len == 3:
				ast2 = AST ('intg', ast, ('@', f'd{dvab.commas [0].var}'), dvab.commas [1], dvab.commas [2])

	elif dvab.is_var:
		ast2 = AST ('intg', ast, ('@', f'd{dvab.var}'))

	if ast2 is None:
		return None

	return _xlat_func_Integral (ast2, *args) if args else ast2

_xlat_func_Limit_dirs = {AST ('"', '+'): ('+',), AST ('"', '-'): ('-',), AST ('"', '+-'): ()}

def _xlat_func_Limit (ast = AST.VarNull, var = AST.VarNull, to = AST.VarNull, dir = AST ('"', '+')):
	return AST ('lim', ast, var, to, *_xlat_func_Limit_dirs [dir])

def _xlat_func_Pow (ast = AST.VarNull, exp = AST.VarNull):
	return AST ('^', ast, exp)

def _xlat_func_Matrix (ast = AST.VarNull):
	if ast == AST.VarNull:
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

					return \
							AST ('mat', tuple (rows)) \
							if cols > 1 else \
							AST ('vec', tuple (r [0] for r in rows))

	return None

def _xlat_func_Piecewise (*args):
	pcs = []

	if not args or args [0].is_null_var:
		return AST ('piece', ((AST.VarNull, AST.VarNull),))

	if len (args) > 1:
		for c in args [:-1]:
			c = c.strip ()

			if not c.is_comma or len (c.commas) != 2:
				return None

			pcs.append (c.commas)

	ast = args [-1]

	if not ast.is_paren:
		return None

	ast = ast.strip ()
	pcs = tuple (pcs)

	if not ast.is_comma:
		return AST ('piece', pcs + ((ast, AST.VarNull),))
	if len (ast.commas) == 0:
		return AST ('piece', pcs + ())

	if not ast.commas [0].is_comma:
		if len (ast.commas) == 1:
			return AST ('piece', pcs + ((ast.commas [0], AST.VarNull),))
		if len (ast.commas) == 2:
			return AST ('piece', pcs + ((ast.commas [0], True if ast.commas [1] == AST.True_ else ast.commas [1]),))

	return None

def _xlat_func_Sum (ast = AST.VarNull, ab = None):
	if ab is None:
		return AST ('sum', ast, AST.VarNull, AST.VarNull, AST.VarNull)

	ab = ab.strip_paren ()

	if ab.is_var:
		return AST ('sum', ast, ab, AST.VarNull, AST.VarNull)
	if ab.is_comma and ab.commas and ab.commas.len <= 3 and ab.commas [0].is_var:
		return AST ('sum', ast, *ab.commas, *((AST.VarNull,) * (3 - ab.commas.len)))

	return None

XLAT_FUNC = {
	'abs'                  : lambda ast: AST ('|', ast),
	'Abs'                  : lambda ast: AST ('|', ast),
	'Derivative'           : _xlat_func_Derivative,
	'diff'                 : _xlat_func_Derivative,
	'exp'                  : lambda ast: AST ('^', AST.E, ast),
	'factorial'            : lambda ast: AST ('!', ast),
	'Integral'             : _xlat_func_Integral,
	'integrate'            : _xlat_func_Integral,
	'Limit'                : _xlat_func_Limit,
	'limit'                : _xlat_func_Limit,
	'Piecewise'            : _xlat_func_Piecewise,
	'Pow'                  : _xlat_func_Pow,
	'pow'                  : _xlat_func_Pow,
	'Sum'                  : _xlat_func_Sum,

	'Matrix'               : _xlat_func_Matrix,
	'MutableDenseMatrix'   : _xlat_func_Matrix,
	'MutableSparseMatrix'  : _xlat_func_Matrix,
	'ImmutableDenseMatrix' : _xlat_func_Matrix,
	'ImmutableSparseMatrix': _xlat_func_Matrix,
	'diag'                 : True,
	'eye'                  : True,
	'ones'                 : True,
	'zeros'                : True,

	'beta'                 : '\\beta', # hack - represent SymPy Greek functions as Greek letters
	'gamma'                : '\\Gamma',
	'Gamma'                : '\\Gamma',
	'zeta'                 : '\\zeta',
}

def xlat_func (xact, args):
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

class xlat: # for single script
	XLAT_FUNC = XLAT_FUNC
	xlat_func = xlat_func

_RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
	ast = AST ('@', 'x')
	res = XLAT_FUNC ['ln'] (ast)
	print (res)
