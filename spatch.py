# Patch SymPy bugs and inconveniences.

from collections import defaultdict

#...............................................................................................
def _Complement__new__ (cls, a, b, evaluate = True): # sets.Complement patched to sympify args
	if evaluate:
		return Complement.reduce (sympify (a), sympify (b))

	return Basic.__new__ (cls, a, b)

#...............................................................................................
# matrix multiplication itermediate simplification routines

def _dotprodsimp(expr, withsimp=False):
	def count_ops_alg(expr):
		ops  = 0
		args = [expr]

		while args:
			a = args.pop()

			if not isinstance(a, Basic):
				continue

			if a.is_Rational:
				if a is not S.One: # -1/3 = NEG + DIV
					ops += bool (a.p < 0) + bool (a.q != 1)

			elif a.is_Mul:
				if _coeff_isneg(a):
					ops += 1
					if a.args[0] is S.NegativeOne:
						a = a.as_two_terms()[1]
					else:
						a = -a

				n, d = fraction(a)

				if n.is_Integer:
					ops += 1 + bool (n < 0)
					args.append(d) # won't be -Mul but could be Add

				elif d is not S.One:
					if not d.is_Integer:
						args.append(d)
					ops += 1
					args.append(n) # could be -Mul

				else:
					ops += len(a.args) - 1
					args.extend(a.args)

			elif a.is_Add:
				laargs = len(a.args)
				negs   = 0

				for ai in a.args:
					if _coeff_isneg(ai):
						negs += 1
						ai	= -ai
					args.append(ai)

				ops += laargs - (negs != laargs) # -x - y = NEG + SUB

			elif a.is_Pow:
				ops += 1
				args.append(a.base)

		return ops

	def nonalg_subs_dummies(expr, dummies):
		if not expr.args:
			return expr

		if expr.is_Add or expr.is_Mul or expr.is_Pow:
			args = None

			for i, a in enumerate(expr.args):
				c = nonalg_subs_dummies(a, dummies)

				if c is a:
					continue

				if args is None:
					args = list(expr.args)

				args[i] = c

			if args is None:
				return expr

			return expr.func(*args)

		return dummies.setdefault(expr, Dummy())

	simplified = False # doesn't really mean simplified, rather "can simplify again"

	if isinstance(expr, Basic) and (expr.is_Add or expr.is_Mul or expr.is_Pow):
		expr2 = expr.expand(deep=True, modulus=None, power_base=False,
			power_exp=False, mul=True, log=False, multinomial=True, basic=False)

		if expr2 != expr:
			expr	   = expr2
			simplified = True

		exprops = count_ops_alg(expr)

		if exprops >= 6: # empirically tested cutoff for expensive simplification
			dummies = {}
			expr2   = nonalg_subs_dummies(expr, dummies)

			if expr2 is expr or count_ops_alg(expr2) >= 6: # check again after substitution
				expr3 = cancel(expr2)

				if expr3 != expr2:
					expr	   = expr3.subs([(d, e) for e, d in dummies.items()])
					simplified = True

		# very special case: x/(x-1) - 1/(x-1) -> 1
		elif (exprops == 5 and expr.is_Add and expr.args [0].is_Mul and
				expr.args [1].is_Mul and expr.args [0].args [-1].is_Pow and
				expr.args [1].args [-1].is_Pow and
				expr.args [0].args [-1].exp is S.NegativeOne and
				expr.args [1].args [-1].exp is S.NegativeOne):

			expr2	= together (expr)
			expr2ops = count_ops_alg(expr2)

			if expr2ops < exprops:
				expr	   = expr2
				simplified = True

		else:
			simplified = True

	return (expr, simplified) if withsimp else expr

def _MatrixArithmetic__mul__(self, other):
	other = _matrixify(other)
	# matrix-like objects can have shapes.  This is
	# our first sanity check.
	if hasattr(other, 'shape') and len(other.shape) == 2:
		if self.shape[1] != other.shape[0]:
			raise ShapeError("Matrix size mismatch: %s * %s." % (
				self.shape, other.shape))

	# honest sympy matrices defer to their class's routine
	if getattr(other, 'is_Matrix', False):
		m = self._eval_matrix_mul(other)
		return m.applyfunc(_dotprodsimp)

	# Matrix-like objects can be passed to CommonMatrix routines directly.
	if getattr(other, 'is_MatrixLike', False):
		return MatrixArithmetic._eval_matrix_mul(self, other)

	# if 'other' is not iterable then scalar multiplication.
	if not isinstance(other, Iterable):
		try:
			return self._eval_scalar_mul(other)
		except TypeError:
			pass

	raise NotImplementedError()

def _MatrixArithmetic_eval_pow_by_recursion(self, num, prevsimp=None):
	if prevsimp is None:
		prevsimp = [True]*len(self)

	if num == 1:
		return self

	if num % 2 == 1:
		a, b = self, self._eval_pow_by_recursion(num - 1, prevsimp=prevsimp)
	else:
		a = b = self._eval_pow_by_recursion(num // 2, prevsimp=prevsimp)

	m     = a.multiply(b)
	lenm  = len(m)
	elems = [None]*lenm

	for i in range(lenm):
		if prevsimp[i]:
			elems[i], prevsimp[i] = _dotprodsimp(m[i], withsimp=True)
		else:
			elems[i] = m[i]

	return m._new(m.rows, m.cols, elems)

def _MatrixReductions_row_reduce(self, iszerofunc, simpfunc, normalize_last=True,
				normalize=True, zero_above=True):
	def get_col(i):
		return mat[i::cols]

	def row_swap(i, j):
		mat[i*cols:(i + 1)*cols], mat[j*cols:(j + 1)*cols] = \
			mat[j*cols:(j + 1)*cols], mat[i*cols:(i + 1)*cols]

	def cross_cancel(a, i, b, j):
		"""Does the row op row[i] = a*row[i] - b*row[j]"""
		q = (j - i)*cols
		for p in range(i*cols, (i + 1)*cols):
			mat[p] = _dotprodsimp(a*mat[p] - b*mat[p + q])

	rows, cols = self.rows, self.cols
	mat = list(self)
	piv_row, piv_col = 0, 0
	pivot_cols = []
	swaps = []

	# use a fraction free method to zero above and below each pivot
	while piv_col < cols and piv_row < rows:
		pivot_offset, pivot_val, \
		_, newly_determined = _find_reasonable_pivot(
			get_col(piv_col)[piv_row:], iszerofunc, simpfunc)

		# _find_reasonable_pivot may have simplified some things
		# in the process.  Let's not let them go to waste
		for (offset, val) in newly_determined:
			offset += piv_row
			mat[offset*cols + piv_col] = val

		if pivot_offset is None:
			piv_col += 1
			continue

		pivot_cols.append(piv_col)
		if pivot_offset != 0:
			row_swap(piv_row, pivot_offset + piv_row)
			swaps.append((piv_row, pivot_offset + piv_row))

		# if we aren't normalizing last, we normalize
		# before we zero the other rows
		if normalize_last is False:
			i, j = piv_row, piv_col
			mat[i*cols + j] = self.one
			for p in range(i*cols + j + 1, (i + 1)*cols):
				mat[p] = _dotprodsimp(mat[p] / pivot_val)
			# after normalizing, the pivot value is 1
			pivot_val = self.one

		# zero above and below the pivot
		for row in range(rows):
			# don't zero our current row
			if row == piv_row:
				continue
			# don't zero above the pivot unless we're told.
			if zero_above is False and row < piv_row:
				continue
			# if we're already a zero, don't do anything
			val = mat[row*cols + piv_col]
			if iszerofunc(val):
				continue

			cross_cancel(pivot_val, row, val, piv_row)
		piv_row += 1

	# normalize each row
	if normalize_last is True and normalize is True:
		for piv_i, piv_j in enumerate(pivot_cols):
			pivot_val = mat[piv_i*cols + piv_j]
			mat[piv_i*cols + piv_j] = self.one
			for p in range(piv_i*cols + piv_j + 1, (piv_i + 1)*cols):
				mat[p] = _dotprodsimp(mat[p] / pivot_val)

	return self._new(self.rows, self.cols, mat), tuple(pivot_cols), tuple(swaps)

#...............................................................................................
SPATCHED = False

try: # try to patch and fail silently if sympy has changed too much since this was written
	from sympy import sympify, S, cancel, together, Basic, Complement, boolalg, Dummy
	from sympy.core.compatibility import Iterable
	from sympy.core.function import _coeff_isneg
	from sympy.matrices.common import MatrixArithmetic, ShapeError, _matrixify, classof
	from sympy.matrices.matrices import MatrixReductions, _find_reasonable_pivot
	from sympy.matrices.dense import DenseMatrix
	from sympy.matrices.sparse import SparseMatrix
	from sympy.simplify.radsimp import fraction

	Complement.__new__ = _Complement__new__ # sets.Complement sympify args fix

	# enable math on booleans
	boolalg.BooleanTrue.__int__       = lambda self: 1
	boolalg.BooleanTrue.__float__     = lambda self: 1.0
	boolalg.BooleanTrue.__complex__   = lambda self: 1+0j
	boolalg.BooleanTrue.as_coeff_Add  = lambda self, *a, **kw: (S.Zero, S.One)
	boolalg.BooleanTrue.as_coeff_Mul  = lambda self, *a, **kw: (S.One, S.One)
	boolalg.BooleanTrue._eval_evalf   = lambda self, *a, **kw: S.One

	boolalg.BooleanFalse.__int__      = lambda self: 0
	boolalg.BooleanFalse.__float__    = lambda self: 0.0
	boolalg.BooleanFalse.__complex__  = lambda self: 0j
	boolalg.BooleanFalse.as_coeff_Mul = lambda self, *a, **kw: (S.Zero, S.Zero)
	boolalg.BooleanFalse.as_coeff_Add = lambda self, *a, **kw: (S.Zero, S.Zero)
	boolalg.BooleanFalse._eval_evalf  = lambda self, *a, **kw: S.Zero

	boolalg.BooleanAtom.__add__       = lambda self, other: self.__int__ () + other
	boolalg.BooleanAtom.__radd__      = lambda self, other: other + self.__int__ ()
	boolalg.BooleanAtom.__sub__       = lambda self, other: self.__int__ () - other
	boolalg.BooleanAtom.__rsub__      = lambda self, other: other - self.__int__ ()
	boolalg.BooleanAtom.__mul__       = lambda self, other: self.__int__ () * other
	boolalg.BooleanAtom.__rmul__      = lambda self, other: other * self.__int__ ()
	boolalg.BooleanAtom.__pow__       = lambda self, other: self.__int__ () ** other
	boolalg.BooleanAtom.__rpow__      = lambda self, other: other ** self.__int__ ()
	boolalg.BooleanAtom.__div__       = lambda self, other: self.__int__ () / other
	boolalg.BooleanAtom.__rdiv__      = lambda self, other: other / self.__int__ ()
	boolalg.BooleanAtom.__truediv__   = lambda self, other: self.__int__ () / other
	boolalg.BooleanAtom.__rtruediv__  = lambda self, other: other / self.__int__ ()
	boolalg.BooleanAtom.__floordiv__  = lambda self, other: self.__int__ ()          // other
	boolalg.BooleanAtom.__rfloordiv__ = lambda self, other: other                    // self.__int__ ()
	boolalg.BooleanAtom.__mod__       = lambda self, other: self.__int__ () % other
	boolalg.BooleanAtom.__rmod__      = lambda self, other: other % self.__int__ ()

	# itermediate matrix multiplication simplification
	_SYMPY_MatrixArithmetic__mul__                = MatrixArithmetic.__mul__
	_SYMPY_MatrixArithmetic_eval_pow_by_recursion = MatrixArithmetic._eval_pow_by_recursion
	_SYMPY_MatrixReductions_row_reduce            = MatrixReductions._row_reduce
	MatrixArithmetic.__mul__                      = _MatrixArithmetic__mul__
	MatrixArithmetic._eval_pow_by_recursion       = _MatrixArithmetic_eval_pow_by_recursion
	MatrixReductions._row_reduce                  = _MatrixReductions_row_reduce

	SPATCHED = True

except:
	pass

def set_matmulsimp (state):
	if SPATCHED:
		idx                                     = bool (state)
		MatrixArithmetic.__mul__                = (_SYMPY_MatrixArithmetic__mul__, _MatrixArithmetic__mul__) [idx]
		MatrixArithmetic._eval_pow_by_recursion = (_SYMPY_MatrixArithmetic_eval_pow_by_recursion, _MatrixArithmetic_eval_pow_by_recursion) [idx]
		MatrixReductions._row_reduce            = (_SYMPY_MatrixReductions_row_reduce, _MatrixReductions_row_reduce) [idx]

class spatch: # for single script
	SPATCHED       = SPATCHED
	set_matmulsimp = set_matmulsimp
