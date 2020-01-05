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

#...............................................................................................
SPATCHED = False

try: # try to patch and fail silently if sympy has changed too much since this was written
	from sympy import sympify, S, cancel, together, Basic, Complement, boolalg, Dummy
	from sympy.core.compatibility import Iterable
	from sympy.core.function import _coeff_isneg
	from sympy.matrices.common import MatrixArithmetic, ShapeError, _matrixify, classof
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
	MatrixArithmetic.__mul__                      = _MatrixArithmetic__mul__
	MatrixArithmetic._eval_pow_by_recursion       = _MatrixArithmetic_eval_pow_by_recursion

	SPATCHED = True

except:
	pass

def set_matmulsimp (state):
	if SPATCHED:
		idx                                     = bool (state)
		MatrixArithmetic.__mul__                = (_SYMPY_MatrixArithmetic__mul__, _MatrixArithmetic__mul__) [idx]
		MatrixArithmetic._eval_pow_by_recursion = (_SYMPY_MatrixArithmetic_eval_pow_by_recursion, _MatrixArithmetic_eval_pow_by_recursion) [idx]

class spatch: # for single script
	SPATCHED       = SPATCHED
	set_matmulsimp = set_matmulsimp
