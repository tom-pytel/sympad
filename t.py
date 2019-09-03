from sympy import *

# s = FiniteSet (slice (1, 2, 3))
# a = s.args [0]

a = sympify (slice (1, 2, 3))

print (repr (a), a.__class__.__mro__)