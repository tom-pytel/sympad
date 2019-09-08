# Patch SymPy bugs and inconveniences.

from collections import defaultdict

#...............................................................................................
def _Complement__new__ (cls, a, b, evaluate = True): # sets.Complement patched to sympify args
	if evaluate:
		return Complement.reduce (sympify (a), sympify (b))

	return Basic.__new__ (cls, a, b)

#...............................................................................................
# matrix multiplication itermediate simplification routines

def _dotprodsimp (a, b, simplify = True):
	"""Sum-of-products with optional intermediate product simplification
	targeted at the kind of blowup that occurs during summation of products.
	Intended to reduce expression blowup during matrix multiplication or other
	similar operations.

	Parameters
	==========

	a, b : iterable
		These will be multiplied then summed together either normally or
		using simplification on the intermediate products and cancelling at
		the end according to the 'simplify' flag. The elements must already be
		sympyfied and the sequences need not be of the same length, the shorter
		will be used.

	simplify : bool
		When set intermediate and final simplification will be used, not set
		will indicate a normal sum of products.
	"""

	expr = S.Zero
	itra = iter (a)
	itrb = iter (b)

	# simple non-simplified sum of products
	if not simplify:
		try:
			expr = next (itra) * next (itrb)

			for a in itra:
				expr += a * next (itrb)

		except StopIteration:
			pass

		return expr

	# part 1, the expanded summation
	try:
		prod    = next (itra) * next (itrb)
		_expand = getattr (prod, 'expand', None)
		expr    = _expand (power_base = False, power_exp = False, log = False, \
				multinomial = False, basic = False) if _expand else prod

		for a in itra:
			prod     = a * next (itrb)
			_expand  = getattr (prod, 'expand', None)
			expr    += _expand (power_base = False, power_exp = False, log = False, \
					multinomial = False, basic = False) if _expand else prod

	except StopIteration:
		pass

	# part 2, the cancelation and grouping
	exprops  = count_ops (expr)
	expr2    = expr.expand (power_base = False, power_exp = False, log = False, multinomial = True, basic = False)
	expr2ops = count_ops (expr2)

	if expr2ops < exprops:
		expr    = expr2
		exprops = expr2ops

	if exprops < 6: # empirically tested cutoff for expensive simplification
		return expr

	expr2    = cancel (expr)
	expr2ops = count_ops (expr2)

	if expr2ops < exprops:
		expr    = expr2
		exprops = expr2ops

	expr3    = together (expr2, deep = True)
	expr3ops = count_ops (expr3)

	if expr3ops < exprops:
		return expr3

	return expr

def _MatrixArithmetic_eval_matrix_mul (self, other):
	return self._new (self.rows, other.cols, lambda i, j:
		_dotprodsimp ((self [i,k] for k in range (self.cols)),
		(other [k,j] for k in range (self.cols))))

def _DenseMatrix_eval_matrix_mul (self, other):
	other_len = other.rows * other.cols
	new_len   = self.rows * other.cols
	new_mat   = [S.Zero] * new_len

	# if we multiply an n x 0 with a 0 x m, the
	# expected behavior is to produce an n x m matrix of zeros
	if self.cols != 0 and other.rows != 0:
		for i in range (new_len):
			row, col    = i // other.cols, i % other.cols
			row_indices = range (self.cols * row, self.cols * (row + 1))
			col_indices = range (col, other_len, other.cols)
			new_mat [i] = _dotprodsimp (
				(self._mat [a] for a in row_indices),
				(other._mat [b] for b in col_indices))

	return classof (self, other)._new (self.rows, other.cols, new_mat, copy = False)

def _SparseMatrix_eval_matrix_mul (self, other):
	"""Fast multiplication exploiting the sparsity of the matrix."""
	if not isinstance (other, SparseMatrix):
		return self.mul (self._new (other))

	# if we made it here, we're both sparse matrices
	# create quick lookups for rows and cols
	row_lookup = defaultdict (dict)
	for (i,j), val in self._smat.items ():
		row_lookup [i][j] = val
	col_lookup = defaultdict (dict)
	for (i,j), val in other._smat.items ():
		col_lookup [j][i] = val

	smat = {}
	for row in row_lookup.keys ():
		for col in col_lookup.keys ():
			# find the common indices of non-zero entries.
			# these are the only things that need to be multiplied.
			indices = set (col_lookup [col].keys ()) & set (row_lookup [row].keys ())
			if indices:
				smat [row, col] = _dotprodsimp ((row_lookup [row][k] for k in indices),
					(col_lookup [col][k] for k in indices))

	return self._new (self.rows, other.cols, smat)

#...............................................................................................
SPATCHED = False

try: # try to patch and fail silently if SymPy has changed too much since this was written
	from sympy import sympify, S, count_ops, cancel, together, SparseMatrix, Basic, Complement, boolalg
	from sympy.matrices.common import MatrixArithmetic, classof
	from sympy.matrices.dense import DenseMatrix
	from sympy.matrices.sparse import SparseMatrix

	_DEFAULT_MatrixArithmetic_eval_matrix_mul = MatrixArithmetic._eval_matrix_mul
	_DEFAULT_DenseMatrix_eval_matrix_mul      = DenseMatrix._eval_matrix_mul
	_DEFAULT_SparseMatrix_eval_matrix_mul     = SparseMatrix._eval_matrix_mul

	MatrixArithmetic._eval_matrix_mul         = _MatrixArithmetic_eval_matrix_mul
	DenseMatrix._eval_matrix_mul              = _DenseMatrix_eval_matrix_mul
	SparseMatrix._eval_matrix_mul             = _SparseMatrix_eval_matrix_mul

	Complement.__new__                        = _Complement__new__

	boolalg.BooleanTrue.__int__               = lambda self: 1
	boolalg.BooleanTrue.__float__             = lambda self: 1.0
	boolalg.BooleanTrue.__complex__           = lambda self: 1+0j
	boolalg.BooleanFalse.__int__              = lambda self: 0
	boolalg.BooleanFalse.__float__            = lambda self: 0.0
	boolalg.BooleanFalse.__complex__          = lambda self: 0j
	boolalg.BooleanAtom.__add__               = lambda self, other: int (self) + other
	boolalg.BooleanAtom.__radd__              = lambda self, other: other + int (self)
	boolalg.BooleanAtom.__sub__               = lambda self, other: int (self) - other
	boolalg.BooleanAtom.__rsub__              = lambda self, other: other - int (self)
	boolalg.BooleanAtom.__mul__               = lambda self, other: int (self) * other
	boolalg.BooleanAtom.__rmul__              = lambda self, other: other * int (self)
	boolalg.BooleanAtom.__pow__               = lambda self, other: int (self) ** other
	boolalg.BooleanAtom.__rpow__              = lambda self, other: other ** int (self)
	boolalg.BooleanAtom.__div__               = lambda self, other: int (self) / other
	boolalg.BooleanAtom.__rdiv__              = lambda self, other: other / int (self)
	boolalg.BooleanAtom.__truediv__           = lambda self, other: int (self) / other
	boolalg.BooleanAtom.__rtruediv__          = lambda self, other: other / int (self)
	boolalg.BooleanAtom.__floordiv__          = lambda self, other: int (self) // other
	boolalg.BooleanAtom.__rfloordiv__         = lambda self, other: other // int (self)
	boolalg.BooleanAtom.__mod__               = lambda self, other: int (self) % other
	boolalg.BooleanAtom.__rmod__              = lambda self, other: other % int (self)

	SPATCHED = True

except:
	pass

def set_matmulsimp (state):
	if SPATCHED:
		idx                               = bool (state)
		MatrixArithmetic._eval_matrix_mul = (_DEFAULT_MatrixArithmetic_eval_matrix_mul, _MatrixArithmetic_eval_matrix_mul) [idx]
		DenseMatrix._eval_matrix_mul      = (_DEFAULT_DenseMatrix_eval_matrix_mul, _DenseMatrix_eval_matrix_mul) [idx]
		SparseMatrix._eval_matrix_mul     = (_DEFAULT_SparseMatrix_eval_matrix_mul, _SparseMatrix_eval_matrix_mul) [idx]

class spatch: # for single script
	SPATCHED       = SPATCHED
	set_matmulsimp = set_matmulsimp
