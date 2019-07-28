# Translate SymPy functions to other AST representations for display.

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
		if dvab.commas and dvab.commas [0].is_var:
			if dvab.commas.len == 1:
				ast2 = AST ('intg', ast, ('@', f'd{dvab.commas [0].var}'))
			if dvab.commas.len == 2:
				ast2 = AST ('intg', ast, ('@', f'd{dvab.commas [0].var}'), AST.Zero, dvab.commas [1])
			if dvab.commas.len == 3:
				ast2 = AST ('intg', ast, ('@', f'd{dvab.commas [0].var}'), dvab.commas [1], dvab.commas [2])

	elif dvab.is_var:
		ast2 = AST ('intg', ast, ('@', f'd{dvab.var}'))

	if ast2 is None:
		return None

	return _xlat_func_Integral (ast2, *args) if args else ast2



XLAT_FUNC = {
	'abs'       : lambda ast: AST ('|', ast),
	'Abs'       : lambda ast: AST ('|', ast),
	'Derivative': _xlat_func_Derivative,
	'diff'      : _xlat_func_Derivative,
	'exp'       : lambda ast: AST ('^', AST.E, ast),
	'factorial' : lambda ast: AST ('!', ast),
	'Integral'  : _xlat_func_Integral,
	'integrate' : _xlat_func_Integral,
	# 'ln'        : lambda ast: AST ('log', ast),

	'diag'      : True,
	'eye'       : True,
	'ones'      : True,
	'zeros'     : True,

	'beta'      : '\\beta', # represent SymPy Greek functions as Greek letters
	'gamma'     : '\\Gamma',
	'Gamma'     : '\\Gamma',
	'zeta'      : '\\zeta',
}

class xlat: # for single script
	XLAT_FUNC = XLAT_FUNC

# _RUNNING_AS_SINGLE_SCRIPT = False # AUTO_REMOVE_IN_SINGLE_SCRIPT
# if __name__ == '__main__' and not _RUNNING_AS_SINGLE_SCRIPT: ## DEBUG!
# 	ast = AST ('@', 'x')
# 	res = _xlat_func_Derivative (ast, ast)
# 	print (res)
