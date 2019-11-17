#!/usr/bin/env python3
# python 3.6+

# Testing of server state machine (vars, env, lambdas).

import os
import sys
import time
import subprocess
import unittest

import requests

if __name__ == '__main__':
	if len (sys.argv) == 1:
		subprocess.run ([sys.executable, '-m', 'unittest', '-v', os.path.basename (sys.argv [0])])
		sys.exit (0)

class Test (unittest.TestCase):
	def test_unicode_greek (self):
		reset ()
		self.assertEqual (get ('env (quick)'), {'msg': ['Quick input mode is on.']})
		self.assertEqual (get ('α, β, γ, δ, ε, ζ, η, θ, ι, κ, λ, μ, ν, ξ, π, ρ, σ, τ, υ, φ, χ, ψ, ω, Γ, Δ, Θ, Λ, Ξ, Π, Σ, Υ, Φ, Ψ, Ω'), {'math': ('(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '\\left(\\alpha, \\beta, \\gamma, \\delta, \\epsilon, \\zeta, \\eta, \\theta, \\iota, \\kappa, \\lambda, \\mu, \\nu, \\xi, \\pi, \\rho, \\sigma, \\tau, \\upsilon, \\phi, \\chi, \\psi, \\omega, \\Gamma, \\Delta, \\Theta, \\Lambda, \\Xi, \\Pi, \\Sigma, \\Upsilon, \\Phi, \\Psi, \\Omega \\right)')})
		self.assertEqual (get ('env (noquick)'), {'msg': ['Quick input mode is off.']})
		self.assertEqual (get ('α, β, γ, δ, ε, ζ, η, θ, ι, κ, λ, μ, ν, ξ, π, ρ, σ, τ, υ, φ, χ, ψ, ω, Γ, Δ, Θ, Λ, Ξ, Π, Σ, Υ, Φ, Ψ, Ω'), {'math': ('(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '\\left(\\alpha, \\beta, \\gamma, \\delta, \\epsilon, \\zeta, \\eta, \\theta, \\iota, \\kappa, \\lambda, \\mu, \\nu, \\xi, \\pi, \\rho, \\sigma, \\tau, \\upsilon, \\phi, \\chi, \\psi, \\omega, \\Gamma, \\Delta, \\Theta, \\Lambda, \\Xi, \\Pi, \\Sigma, \\Upsilon, \\Phi, \\Psi, \\Omega \\right)')})

	#...............................................................................................
	# BEGIN UPDATE BLOCK
	def test_vars (self):
		reset ()
		self.assertEqual (get ('x'), {'math': ('x', 'x', 'x')})
		self.assertEqual (get ('x = 2'), {'math': ('x = 2', 'x = 2', 'x = 2')})
		self.assertEqual (get ('x'), {'math': ('2', '2', '2')})
		self.assertEqual (get ('x*3'), {'math': ('6', '6', '6')})
		self.assertEqual (get ('x**2'), {'math': ('4', '4', '4')})
		self.assertEqual (get ('y'), {'math': ('y', 'y', 'y')})
		self.assertEqual (get ('y = x'), {'math': ('y = 2', 'y = 2', 'y = 2')})
		self.assertEqual (get ('y'), {'math': ('2', '2', '2')})
		self.assertEqual (get ('del (x, y)'), {'msg': ["Variable 'x' deleted.", "Variable 'y' deleted."]})
		self.assertEqual (get ('x'), {'math': ('x', 'x', 'x')})
		self.assertEqual (get ('y'), {'math': ('y', 'y', 'y')})
		self.assertEqual (get ('x = x'), {'err': "server.CircularReferenceError: I'm sorry, Dave. I'm afraid I can't do that."})
		self.assertEqual (get ('x, y = x, y'), {'err': "server.CircularReferenceError: I'm sorry, Dave. I'm afraid I can't do that."})
		self.assertEqual (get ('x, y = y, x'), {'err': "server.CircularReferenceError: I'm sorry, Dave. I'm afraid I can't do that."})
		self.assertEqual (get ('x, y = 1, 2'), {'math': [('x = 1', 'x = 1', 'x = 1'), ('y = 2', 'y = 2', 'y = 2')]})
		self.assertEqual (get ('x, y = y, x'), {'math': [('x = 2', 'x = 2', 'x = 2'), ('y = 1', 'y = 1', 'y = 1')]})
		self.assertEqual (get ('x, y'), {'math': ('(2, 1)', '(2, 1)', '\\left(2, 1 \\right)')})
		self.assertEqual (get ('del vars'), {'err': "TypeError: invalid argument 'vars()'"})
		self.assertEqual (get ('x'), {'math': ('2', '2', '2')})
		self.assertEqual (get ('y'), {'math': ('1', '1', '1')})

	def test_lambdas (self):
		reset ()
		self.assertEqual (get ('f = lambda: 2'), {'math': ('f() = 2', 'f = Lambda((), 2)', 'f\\left( \\right) = 2')})
		self.assertEqual (get ('f'), {'math': ('lambda: 2', 'Lambda((), 2)', '\\left(\\left( \\right) \\mapsto 2 \\right)')})
		self.assertEqual (get ('f ()'), {'math': ('2', '2', '2')})
		self.assertEqual (get ('f = lambda: y'), {'math': ('f() = y', 'f = Lambda((), y)', 'f\\left( \\right) = y')})
		self.assertEqual (get ('f'), {'math': ('lambda: y', 'Lambda((), y)', '\\left(\\left( \\right) \\mapsto y \\right)')})
		self.assertEqual (get ('f ()'), {'math': ('y', 'y', 'y')})
		self.assertEqual (get ('y = 2'), {'math': ('y = 2', 'y = 2', 'y = 2')})
		self.assertEqual (get ('f'), {'math': ('lambda: y', 'Lambda((), y)', '\\left(\\left( \\right) \\mapsto y \\right)')})
		self.assertEqual (get ('f ()'), {'math': ('2', '2', '2')})
		self.assertEqual (get ('f = lambda: y'), {'math': ('f() = 2', 'f = Lambda((), 2)', 'f\\left( \\right) = 2')})
		self.assertEqual (get ('f'), {'math': ('lambda: 2', 'Lambda((), 2)', '\\left(\\left( \\right) \\mapsto 2 \\right)')})
		self.assertEqual (get ('f ()'), {'math': ('2', '2', '2')})
		self.assertEqual (get ('f = lambda: @y'), {'math': ('f() = y', 'f = Lambda((), y)', 'f\\left( \\right) = y')})
		self.assertEqual (get ('f'), {'math': ('lambda: y', 'Lambda((), y)', '\\left(\\left( \\right) \\mapsto y \\right)')})
		self.assertEqual (get ('f ()'), {'math': ('2', '2', '2')})
		self.assertEqual (get ('del y'), {'msg': ["Variable 'y' deleted."]})
		self.assertEqual (get ('f = lambda x: x'), {'math': ('f(x) = x', 'f = Lambda(x, x)', 'f\\left(x \\right) = x')})
		self.assertEqual (get ('f'), {'math': ('lambda x: x', 'Lambda(x, x)', '\\left(x \\mapsto x \\right)')})
		self.assertEqual (get ('f (x)'), {'math': ('x', 'x', 'x')})
		self.assertEqual (get ('f (y)'), {'math': ('y', 'y', 'y')})
		self.assertEqual (get ('f (2)'), {'math': ('2', '2', '2')})
		self.assertEqual (get ('f = lambda x: x**2'), {'math': ('f(x) = x**2', 'f = Lambda(x, x**2)', 'f\\left(x \\right) = x^2')})
		self.assertEqual (get ('f (x)'), {'math': ('x**2', 'x**2', 'x^2')})
		self.assertEqual (get ('f (y)'), {'math': ('y**2', 'y**2', 'y^2')})
		self.assertEqual (get ('f (2)'), {'math': ('4', '4', '4')})
		self.assertEqual (get ('g = lambda x: f(x) + f(2x)'), {'math': ('g(x) = 5x**2', 'g = Lambda(x, 5*x**2)', 'g\\left(x \\right) = 5 x^2')})
		self.assertEqual (get ('g'), {'math': ('lambda x: 5x**2', 'Lambda(x, 5*x**2)', '\\left(x \\mapsto 5 x^2 \\right)')})
		self.assertEqual (get ('g (x)'), {'math': ('5x**2', '5*x**2', '5 x^2')})
		self.assertEqual (get ('g (y)'), {'math': ('5y**2', '5*y**2', '5 y^2')})
		self.assertEqual (get ('g (2)'), {'math': ('20', '20', '20')})
		self.assertEqual (get ('del f'), {'msg': ["Lambda function 'f' deleted."]})
		self.assertEqual (get ('g (2)'), {'math': ('20', '20', '20')})
		self.assertEqual (get ('f = lambda x: x**2'), {'math': ('f(x) = x**2', 'f = Lambda(x, x**2)', 'f\\left(x \\right) = x^2')})
		self.assertEqual (get ('g = lambda x: @(f(x) + f(2x))'), {'math': ('g(x) = f(2 x) + f(x)', 'g = Lambda(x, f(2*x) + f(x))', 'g\\left(x \\right) = \\operatorname{f}{\\left(2 x \\right)} + \\operatorname{f}{\\left(x \\right)}')})
		self.assertEqual (get ('h = lambda x: @(f(x)) + @(f(2x))'), {'math': ('h(x) = f(2 x) + f(x)', 'h = Lambda(x, f(2*x) + f(x))', 'h\\left(x \\right) = \\operatorname{f}{\\left(2 x \\right)} + \\operatorname{f}{\\left(x \\right)}')})
		self.assertEqual (get ('g == h'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('g'), {'math': ('lambda x: f(2 x) + f(x)', 'Lambda(x, f(2*x) + f(x))', '\\left(x \\mapsto \\operatorname{f}{\\left(2 x \\right)} + \\operatorname{f}{\\left(x \\right)} \\right)')})
		self.assertEqual (get ('g (x)'), {'math': ('5x**2', '5*x**2', '5 x^2')})
		self.assertEqual (get ('g (y)'), {'math': ('5y**2', '5*y**2', '5 y^2')})
		self.assertEqual (get ('g (2)'), {'math': ('20', '20', '20')})
		self.assertEqual (get ('del f'), {'msg': ["Lambda function 'f' deleted."]})
		self.assertEqual (get ('g (2)'), {'err': "NameError: function 'f' is not defined"})
		self.assertEqual (get ('f = lambda x, y: x + y'), {'math': ('f(x, y) = x + y', 'f = Lambda((x, y), x + y)', 'f\\left(x, y \\right) = x + y')})
		self.assertEqual (get ('f (1, 2)'), {'math': ('3', '3', '3')})
		self.assertEqual (get ('g (2)'), {'err': "TypeError: lambda function 'f' takes 2 argument(s)"})
		self.assertEqual (get ('f = lambda x, y, z: x + y + z'), {'math': ('f(x, y, z) = x + y + z', 'f = Lambda((x, y, z), x + y + z)', 'f\\left(x, y, z \\right) = x + y + z')})
		self.assertEqual (get ('f (1, 2, 3)'), {'math': ('6', '6', '6')})
		self.assertEqual (get ('f = lambda x, y, z, w: x + y + z + w'), {'math': ('f(x, y, z, w) = w + x + y + z', 'f = Lambda((x, y, z, w), w + x + y + z)', 'f\\left(x, y, z, w \\right) = w + x + y + z')})
		self.assertEqual (get ('f (1, 2, 3, 4)'), {'math': ('10', '10', '10')})
		self.assertEqual (get ('f (1, 2, 3)'), {'err': "TypeError: lambda function 'f' takes 4 argument(s)"})
		self.assertEqual (get ('f (1, 2, 3, 4, 5)'), {'err': "TypeError: lambda function 'f' takes 4 argument(s)"})
		self.assertEqual (get ('f = lambda x: lambda: x**2'), {'math': ('f(x) = lambda: x**2', 'f = Lambda(x, Lambda((), x**2))', 'f\\left(x \\right) = \\left(\\left( \\right) \\mapsto x^2 \\right)')})
		self.assertEqual (get ('f (2)'), {'math': ('lambda: 4', 'Lambda((), 4)', '\\left(\\left( \\right) \\mapsto 4 \\right)')})
		self.assertEqual (get ('_ ()'), {'math': ('4', '4', '4')})
		self.assertEqual (get ('f = lambda x: lambda: lambda: x**2'), {'math': ('f(x) = lambda: {lambda: x**2}', 'f = Lambda(x, Lambda((), Lambda((), x**2)))', 'f\\left(x \\right) = \\left(\\left( \\right) \\mapsto \\left(\\left( \\right) \\mapsto x^2 \\right) \\right)')})
		self.assertEqual (get ('f (3)'), {'math': ('lambda: {lambda: 9}', 'Lambda((), Lambda((), 9))', '\\left(\\left( \\right) \\mapsto \\left(\\left( \\right) \\mapsto 9 \\right) \\right)')})
		self.assertEqual (get ('_ ()'), {'math': ('lambda: 9', 'Lambda((), 9)', '\\left(\\left( \\right) \\mapsto 9 \\right)')})
		self.assertEqual (get ('_ ()'), {'math': ('9', '9', '9')})
		self.assertEqual (get ('solve (x**2 + 2 x - 1 > 7)'), {'math': ('-oo < x < -4 or 2 < x < oo', 'Or(And(Lt(-oo, x), Lt(x, -4)), And(Lt(2, x), Lt(x, oo)))', '-\\infty < x < -4 \\vee 2 < x < \\infty')})
		self.assertEqual (get ('f = lambda x: _'), {'math': ('f(x) = -oo < x < -4 or 2 < x < oo', 'f = Lambda(x, Or(And(Lt(-oo, x), Lt(x, -4)), And(Lt(2, x), Lt(x, oo))))', 'f\\left(x \\right) = -\\infty < x < -4 \\vee 2 < x < \\infty')})
		self.assertEqual (get ('f (-4.1), f (-4), f (0), f (2), f (2.1)'), {'math': ('(True, False, False, False, True)', '(True, False, False, False, True)', '\\left(True, False, False, False, True \\right)')})
		self.assertEqual (get ('f (x) = x**2'), {'math': ('f(x) = x**2', 'f = Lambda(x, x**2)', 'f\\left(x \\right) = x^2')})
		self.assertEqual (get ('f (2)'), {'math': ('4', '4', '4')})
		self.assertEqual (get ('f (x, y) = sqrt {x**2 + y**2}'), {'math': ('f(x, y) = sqrt(x**2 + y**2)', 'f = Lambda((x, y), sqrt(x**2 + y**2))', 'f\\left(x, y \\right) = \\sqrt{x^2 + y^2}')})
		self.assertEqual (get ('f (3, 4)'), {'math': ('5', '5', '5')})
		self.assertEqual (get ('del f'), {'msg': ["Lambda function 'f' deleted."]})

	def test_lambdas2 (self):
		reset ()
		self.assertEqual (get ('f = lambda x: x**2'), {'math': ('f(x) = x**2', 'f = Lambda(x, x**2)', 'f\\left(x \\right) = x^2')})
		self.assertEqual (get ('f (2)'), {'math': ('4', '4', '4')})
		self.assertEqual (get ('f (x) = x**2'), {'math': ('f(x) = x**2', 'f = Lambda(x, x**2)', 'f\\left(x \\right) = x^2')})
		self.assertEqual (get ('f (3)'), {'math': ('9', '9', '9')})
		self.assertEqual (get ('f (x, y) = sqrt (x**2 + y**2)'), {'math': ('f(x, y) = sqrt(x**2 + y**2)', 'f = Lambda((x, y), sqrt(x**2 + y**2))', 'f\\left(x, y \\right) = \\sqrt{x^2 + y^2}')})
		self.assertEqual (get ('f (3, 4)'), {'math': ('5', '5', '5')})
		self.assertEqual (get ('x, y, z = 3, 4, 5'), {'math': [('x = 3', 'x = 3', 'x = 3'), ('y = 4', 'y = 4', 'y = 4'), ('z = 5', 'z = 5', 'z = 5')]})
		self.assertEqual (get ('f (x, y) = sqrt (x**2 + y**2) + z'), {'math': ('f(x, y) = sqrt(x**2 + y**2) + 5', 'f = Lambda((x, y), sqrt(x**2 + y**2) + 5)', 'f\\left(x, y \\right) = \\sqrt{x^2 + y^2} + 5')})
		self.assertEqual (get ('f (x, y) = sqrt (x**2 + y**2) + @z'), {'math': ('f(x, y) = z + sqrt(x**2 + y**2)', 'f = Lambda((x, y), z + sqrt(x**2 + y**2))', 'f\\left(x, y \\right) = z + \\sqrt{x^2 + y^2}')})
		self.assertEqual (get ('f (x) = x**2'), {'math': ('f(x) = x**2', 'f = Lambda(x, x**2)', 'f\\left(x \\right) = x^2')})
		self.assertEqual (get ('f (x) = @x**2'), {'math': ('f(x) = 9', 'f = Lambda(x, 9)', 'f\\left(x \\right) = 9')})
		self.assertEqual (get ('f (x) = y**2'), {'math': ('f(x) = 16', 'f = Lambda(x, 16)', 'f\\left(x \\right) = 16')})
		self.assertEqual (get ('f (2)'), {'math': ('16', '16', '16')})
		self.assertEqual (get ('f (x) = @y**2'), {'math': ('f(x) = y**2', 'f = Lambda(x, y**2)', 'f\\left(x \\right) = y^2')})
		self.assertEqual (get ('f (2)'), {'math': ('16', '16', '16')})
		self.assertEqual (get ('y = 6'), {'math': ('y = 6', 'y = 6', 'y = 6')})
		self.assertEqual (get ('f (2)'), {'math': ('36', '36', '36')})
		self.assertEqual (get ('f = 2'), {'math': ('f = 2', 'f = 2', 'f = 2')})
		self.assertEqual (get ('f (x) = x**2'), {'math': ('f(x) = x**2', 'f = Lambda(x, x**2)', 'f\\left(x \\right) = x^2')})
		self.assertEqual (get ('delall'), {'msg': ['All variables deleted.']})
		self.assertEqual (get ('f (x) = x**2'), {'math': ('f(x) = x**2', 'f = Lambda(x, x**2)', 'f\\left(x \\right) = x^2')})
		self.assertEqual (get ('g (x, y) = sqrt (f(x) + f(y))'), {'math': ('g(x, y) = sqrt(x**2 + y**2)', 'g = Lambda((x, y), sqrt(x**2 + y**2))', 'g\\left(x, y \\right) = \\sqrt{x^2 + y^2}')})
		self.assertEqual (get ('g (3, 4)'), {'math': ('5', '5', '5')})
		self.assertEqual (get ('f (x) = x**3'), {'math': ('f(x) = x**3', 'f = Lambda(x, x**3)', 'f\\left(x \\right) = x^3')})
		self.assertEqual (get ('g (3, 4)'), {'math': ('5', '5', '5')})
		self.assertEqual (get ('g (x, y) = @sqrt (f(x) + f(y))'), {'math': ('g(x, y) = sqrt(f(x) + f(y))', 'g = Lambda((x, y), sqrt(f(x) + f(y)))', 'g\\left(x, y \\right) = \\sqrt{\\operatorname{f}{\\left(x \\right)} + \\operatorname{f}{\\left(y \\right)}}')})
		self.assertEqual (get ('g (3, 4)'), {'math': ('sqrt(91)', 'sqrt(91)', '\\sqrt{91}')})
		self.assertEqual (get ('f (x) = x**2'), {'math': ('f(x) = x**2', 'f = Lambda(x, x**2)', 'f\\left(x \\right) = x^2')})
		self.assertEqual (get ('g (3, 4)'), {'math': ('5', '5', '5')})
		self.assertEqual (get ('delall'), {'msg': ['All variables deleted.']})
		self.assertEqual (get ('f (x) = \\int x dx'), {'math': ('f(x) = \\int x dx', 'f = Lambda(x, Integral(x, x))', 'f\\left(x \\right) = \\int x \\ dx')})
		self.assertEqual (get ('f (sin x)'), {'math': ('-cos(x)', '-cos(x)', '-\\cos{\\left(x \\right)}')})
		self.assertEqual (get ('f (x) = %(\\int x dx)'), {'math': ('f(x) = x**2 / 2', 'f = Lambda(x, x**2 / 2)', 'f\\left(x \\right) = \\frac{x^2}{2}')})
		self.assertEqual (get ('f (sin x)'), {'math': ('sin**2(x) / 2', 'sin(x)**2 / 2', '\\frac{\\sin^2{\\left(x \\right)}}{2}')})
		self.assertEqual (get ('f (sin y)'), {'math': ('sin**2(y) / 2', 'sin(y)**2 / 2', '\\frac{\\sin^2{\\left(y \\right)}}{2}')})
		self.assertEqual (get ('f (x) = \\int x dx'), {'math': ('f(x) = \\int x dx', 'f = Lambda(x, Integral(x, x))', 'f\\left(x \\right) = \\int x \\ dx')})
		self.assertEqual (get ('f (sin x)'), {'math': ('-cos(x)', '-cos(x)', '-\\cos{\\left(x \\right)}')})
		self.assertEqual (get ('f (sin y)'), {'math': ('x sin(y)', 'x*sin(y)', 'x \\sin{\\left(y \\right)}')})
		self.assertEqual (get ('\\int sin y dx'), {'math': ('x sin(y)', 'x*sin(y)', 'x \\sin{\\left(y \\right)}')})

	def test_env (self):
		reset ()
		self.assertEqual (get ('env (quick)'), {'msg': ['Quick input mode is on.']})
		self.assertEqual (get ('env (noquick)'), {'msg': ['Quick input mode is off.']})
		self.assertEqual (get ('env'), {'msg': ['Uppercase E and I is off.', 'Quick input mode is off.', 'Python S escaping on.', 'Post-evaluation simplify is off.', 'Matrix simplify is on.', 'Expression doit is on.', 'Function N is on.', 'Function O is on.', 'Function S is on.', 'Function beta is on.', 'Function gamma is on.', 'Function Gamma is on.', 'Function Lambda is on.', 'Function zeta is on.']})
		self.assertEqual (get ('env (EI, quick, nopyS, nosimplify, nomatsimp, nodoit, noN, noO, noS, nogamma, noGamma, nozeta)'), {'msg': ['Uppercase E and I is on.', 'Quick input mode is on.', 'Python S escaping off.', 'Post-evaluation simplify is off.', 'Matrix simplify is off.', 'Expression doit is off.', 'Function N is off.', 'Function O is off.', 'Function S is off.', 'Function gamma is off.', 'Function Gamma is off.', 'Function zeta is off.']})
		self.assertEqual (get ('env'), {'msg': ['Uppercase E and I is on.', 'Quick input mode is on.', 'Python S escaping off.', 'Post-evaluation simplify is off.', 'Matrix simplify is off.', 'Expression doit is off.', 'Function N is off.', 'Function O is off.', 'Function S is off.', 'Function beta is on.', 'Function gamma is off.', 'Function Gamma is off.', 'Function Lambda is on.', 'Function zeta is off.']})
		self.assertEqual (get ('envreset'), {'msg': ['Environment has been reset.', 'Uppercase E and I is off.', 'Quick input mode is off.', 'Python S escaping on.', 'Post-evaluation simplify is off.', 'Matrix simplify is on.', 'Expression doit is on.', 'Function N is on.', 'Function O is on.', 'Function S is on.', 'Function beta is on.', 'Function gamma is on.', 'Function Gamma is on.', 'Function Lambda is on.', 'Function zeta is on.']})
		self.assertEqual (get ('env'), {'msg': ['Uppercase E and I is off.', 'Quick input mode is off.', 'Python S escaping on.', 'Post-evaluation simplify is off.', 'Matrix simplify is on.', 'Expression doit is on.', 'Function N is on.', 'Function O is on.', 'Function S is on.', 'Function beta is on.', 'Function gamma is on.', 'Function Gamma is on.', 'Function Lambda is on.', 'Function zeta is on.']})

	def test_idx_and_attr (self):
		reset ()
		self.assertEqual (get ('x [y]'), {'math': ('x[y]', 'x[y]', 'x\\left[y \\right]')})
		self.assertEqual (get ('x.y'), {'math': ('x.y', 'x.y', 'x.y')})
		self.assertEqual (get ('x = [1, 2, 3]'), {'math': ('x = [1, 2, 3]', 'x = [1, 2, 3]', 'x = \\left[1, 2, 3 \\right]')})
		self.assertEqual (get ('x [y]'), {'math': ('[1, 2, 3][y]', '[1, 2, 3][y]', '\\left[1, 2, 3 \\right]\\left[y \\right]')})
		self.assertEqual (get ('x.y'), {'err': "AttributeError: 'list' object has no attribute 'y'"})
		self.assertEqual (get ('[1, 2, 3] [y]'), {'math': ('[1, 2, 3][y]', '[1, 2, 3][y]', '\\left[1, 2, 3 \\right]\\left[y \\right]')})
		self.assertEqual (get ('[1, 2, 3].y'), {'err': "AttributeError: 'list' object has no attribute 'y'"})
		self.assertEqual (get ('y = 2'), {'math': ('y = 2', 'y = 2', 'y = 2')})
		self.assertEqual (get ('x [y]'), {'math': ('3', '3', '3')})
		self.assertEqual (get ('x.y'), {'err': "AttributeError: 'list' object has no attribute 'y'"})
		self.assertEqual (get ('[1, 2, 3] [y]'), {'math': ('3', '3', '3')})
		self.assertEqual (get ('[1, 2, 3].y'), {'err': "AttributeError: 'list' object has no attribute 'y'"})

	def test_greek (self):
		reset ()
		self.assertEqual (get ('env (quick)'), {'msg': ['Quick input mode is on.']})
		self.assertEqual (get ('alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega'), {'math': ('(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '\\left(\\alpha, \\beta, \\gamma, \\delta, \\epsilon, \\zeta, \\eta, \\theta, \\iota, \\kappa, \\lambda, \\mu, \\nu, \\xi, \\pi, \\rho, \\sigma, \\tau, \\upsilon, \\phi, \\chi, \\psi, \\omega, \\Gamma, \\Delta, \\Theta, \\Lambda, \\Xi, \\Pi, \\Sigma, \\Upsilon, \\Phi, \\Psi, \\Omega \\right)')})
		self.assertEqual (get ('\\alpha, \\beta, \\gamma, \\delta, \\epsilon, \\zeta, \\eta, \\theta, \\iota, \\kappa, \\lambda, \\mu, \\nu, \\xi, \\pi, \\rho, \\sigma, \\tau, \\upsilon, \\phi, \\chi, \\psi, \\omega, \\Gamma, \\Delta, \\Theta, \\Lambda, \\Xi, \\Pi, \\Sigma, \\Upsilon, \\Phi, \\Psi, \\Omega'), {'math': ('(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '\\left(\\alpha, \\beta, \\gamma, \\delta, \\epsilon, \\zeta, \\eta, \\theta, \\iota, \\kappa, \\lambda, \\mu, \\nu, \\xi, \\pi, \\rho, \\sigma, \\tau, \\upsilon, \\phi, \\chi, \\psi, \\omega, \\Gamma, \\Delta, \\Theta, \\Lambda, \\Xi, \\Pi, \\Sigma, \\Upsilon, \\Phi, \\Psi, \\Omega \\right)')})
		self.assertEqual (get ('env (noquick)'), {'msg': ['Quick input mode is off.']})
		self.assertEqual (get ('alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega'), {'math': ('(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '\\left(\\alpha, \\beta, \\gamma, \\delta, \\epsilon, \\zeta, \\eta, \\theta, \\iota, \\kappa, \\lambda, \\mu, \\nu, \\xi, \\pi, \\rho, \\sigma, \\tau, \\upsilon, \\phi, \\chi, \\psi, \\omega, \\Gamma, \\Delta, \\Theta, \\Lambda, \\Xi, \\Pi, \\Sigma, \\Upsilon, \\Phi, \\Psi, \\Omega \\right)')})
		self.assertEqual (get ('\\alpha, \\beta, \\gamma, \\delta, \\epsilon, \\zeta, \\eta, \\theta, \\iota, \\kappa, \\lambda, \\mu, \\nu, \\xi, \\pi, \\rho, \\sigma, \\tau, \\upsilon, \\phi, \\chi, \\psi, \\omega, \\Gamma, \\Delta, \\Theta, \\Lambda, \\Xi, \\Pi, \\Sigma, \\Upsilon, \\Phi, \\Psi, \\Omega'), {'math': ('(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '\\left(\\alpha, \\beta, \\gamma, \\delta, \\epsilon, \\zeta, \\eta, \\theta, \\iota, \\kappa, \\lambda, \\mu, \\nu, \\xi, \\pi, \\rho, \\sigma, \\tau, \\upsilon, \\phi, \\chi, \\psi, \\omega, \\Gamma, \\Delta, \\Theta, \\Lambda, \\Xi, \\Pi, \\Sigma, \\Upsilon, \\Phi, \\Psi, \\Omega \\right)')})

	def test_simplification (self):
		reset ()
		self.assertEqual (get ('env (nosimplify, nomatsimp)'), {'msg': ['Post-evaluation simplify is off.', 'Matrix simplify is off.']})
		self.assertEqual (get ('\\[[x + 1, x - 1], [x - 1, x + 1]]**2'), {'math': ('\\[[(x + 1)**2 + (x - 1)**2, 2 {x + 1} {x - 1}], [2 {x + 1} {x - 1}, (x + 1)**2 + (x - 1)**2]]', 'Matrix([[(x + 1)**2 + (x - 1)**2, 2*(x + 1)*(x - 1)], [2*(x + 1)*(x - 1), (x + 1)**2 + (x - 1)**2]])', '\\begin{bmatrix} \\left(x + 1 \\right)^2 + \\left(x - 1 \\right)^2 & 2 \\left(x + 1 \\right) \\left(x - 1 \\right) \\\\ 2 \\left(x + 1 \\right) \\left(x - 1 \\right) & \\left(x + 1 \\right)^2 + \\left(x - 1 \\right)^2 \\end{bmatrix}')})
		self.assertEqual (get ('solve (x**3 = 5)'), {'math': ('[5**{1/3}, -{i sqrt(3) * 5**{1/3}} / 2 - 5**{1/3} / 2, {i sqrt(3) * 5**{1/3}} / 2 - 5**{1/3} / 2]', '[5**(S(1) / 3), -(i*sqrt(3)*5**(S(1) / 3)) / 2 - 5**(S(1) / 3) / 2, (i*sqrt(3)*5**(S(1) / 3)) / 2 - 5**(S(1) / 3) / 2]', '\\left[5^\\frac{1}{3}, -\\frac{i \\sqrt{3} \\cdot 5^\\frac{1}{3}}{2} - \\frac{5^\\frac{1}{3}}{2}, \\frac{i \\sqrt{3} \\cdot 5^\\frac{1}{3}}{2} - \\frac{5^\\frac{1}{3}}{2} \\right]')})
		self.assertEqual (get ("env ('simplify', nomatsimp)"), {'msg': ['Post-evaluation simplify is on.', 'Matrix simplify is off.']})
		self.assertEqual (get ('\\[[x + 1, x - 1], [x - 1, x + 1]]**2'), {'math': ('\\[[2x**2 + 2, 2x**2 - 2], [2x**2 - 2, 2x**2 + 2]]', 'Matrix([[2*x**2 + 2, 2*x**2 - 2], [2*x**2 - 2, 2*x**2 + 2]])', '\\begin{bmatrix} 2 x^2 + 2 & 2 x^2 - 2 \\\\ 2 x^2 - 2 & 2 x^2 + 2 \\end{bmatrix}')})
		self.assertEqual (get ('solve (x**3 = 5)'), {'math': ('[5**{1/3}, -5**{1/3} {i sqrt(3) + 1} / 2, 5**{1/3} {i sqrt(3) - 1} / 2]', '[5**(S(1) / 3), -(5**(S(1) / 3)*(i*sqrt(3) + 1)) / 2, (5**(S(1) / 3)*(i*sqrt(3) - 1)) / 2]', '\\left[5^\\frac{1}{3}, -\\frac{5^\\frac{1}{3} \\left(i \\sqrt{3} + 1 \\right)}{2}, \\frac{5^\\frac{1}{3} \\left(i \\sqrt{3} - 1 \\right)}{2} \\right]')})
		self.assertEqual (get ('env (nosimplify, matsimp)'), {'msg': ['Post-evaluation simplify is off.', 'Matrix simplify is on.']})
		self.assertEqual (get ('\\[[x + 1, x - 1], [x - 1, x + 1]]**2'), {'math': ('\\[[2x**2 + 2, 2x**2 - 2], [2x**2 - 2, 2x**2 + 2]]', 'Matrix([[2*x**2 + 2, 2*x**2 - 2], [2*x**2 - 2, 2*x**2 + 2]])', '\\begin{bmatrix} 2 x^2 + 2 & 2 x^2 - 2 \\\\ 2 x^2 - 2 & 2 x^2 + 2 \\end{bmatrix}')})
		self.assertEqual (get ("env ('simplify', matsimp)"), {'msg': ['Post-evaluation simplify is on.', 'Matrix simplify is on.']})
		self.assertEqual (get ('\\[[x + 1, x - 1], [x - 1, x + 1]]**2'), {'math': ('\\[[2x**2 + 2, 2x**2 - 2], [2x**2 - 2, 2x**2 + 2]]', 'Matrix([[2*x**2 + 2, 2*x**2 - 2], [2*x**2 - 2, 2*x**2 + 2]])', '\\begin{bmatrix} 2 x^2 + 2 & 2 x^2 - 2 \\\\ 2 x^2 - 2 & 2 x^2 + 2 \\end{bmatrix}')})
		self.assertEqual (get ('solve (x**3 = 5)'), {'math': ('[5**{1/3}, -5**{1/3} {i sqrt(3) + 1} / 2, 5**{1/3} {i sqrt(3) - 1} / 2]', '[5**(S(1) / 3), -(5**(S(1) / 3)*(i*sqrt(3) + 1)) / 2, (5**(S(1) / 3)*(i*sqrt(3) - 1)) / 2]', '\\left[5^\\frac{1}{3}, -\\frac{5^\\frac{1}{3} \\left(i \\sqrt{3} + 1 \\right)}{2}, \\frac{5^\\frac{1}{3} \\left(i \\sqrt{3} - 1 \\right)}{2} \\right]')})

	def test_calculate_eigen (self):
		reset ()
		self.assertEqual (get ('m = \\[[1, 2], [3, 4]]'), {'math': ('m = \\[[1, 2], [3, 4]]', 'm = Matrix([[1, 2], [3, 4]])', 'm = \\begin{bmatrix} 1 & 2 \\\\ 3 & 4 \\end{bmatrix}')})
		self.assertEqual (get ('l = m - lambda eye 2'), {'math': ('l = \\[[1 - lambda, 2], [3, 4 - lambda]]', 'l = Matrix([[1 - lambda, 2], [3, 4 - lambda]])', 'l = \\begin{bmatrix} 1 - \\lambda & 2 \\\\ 3 & 4 - \\lambda \\end{bmatrix}')})
		self.assertEqual (get ('l.det ()'), {'math': ('{1 - lambda} {4 - lambda} - 6', '(1 - lambda)*(4 - lambda) - 6', '\\left(1 - \\lambda \\right) \\left(4 - \\lambda \\right) - 6')})
		self.assertEqual (get ('solve _'), {'math': ('[5/2 - sqrt(33) / 2, sqrt(33) / 2 + 5/2]', '[S(5) / 2 - sqrt(33) / 2, sqrt(33) / 2 + S(5) / 2]', '\\left[\\frac{5}{2} - \\frac{\\sqrt{33}}{2}, \\frac{\\sqrt{33}}{2} + \\frac{5}{2} \\right]')})
		self.assertEqual (get ('a, b = _'), {'math': [('a = 5/2 - sqrt(33) / 2', 'a = S(5) / 2 - sqrt(33) / 2', 'a = \\frac{5}{2} - \\frac{\\sqrt{33}}{2}'), ('b = sqrt(33) / 2 + 5/2', 'b = sqrt(33) / 2 + S(5) / 2', 'b = \\frac{\\sqrt{33}}{2} + \\frac{5}{2}')]})
		self.assertEqual (get ('m.eigenvals ()'), {'math': ('{5/2 - sqrt(33) / 2: 1, sqrt(33) / 2 + 5/2: 1}', '{S(5) / 2 - sqrt(33) / 2: 1, sqrt(33) / 2 + S(5) / 2: 1}', '\\left\\{\\frac{5}{2} - \\frac{\\sqrt{33}}{2}{:} 1, \\frac{\\sqrt{33}}{2} + \\frac{5}{2}{:} 1 \\right\\}')})
		self.assertEqual (get ('Subs (l, lambda, a) \\[x, y]'), {'math': ('\\[2 y - 3 x / 2 + x sqrt(33) / 2, 3 x + 3 y / 2 + y sqrt(33) / 2]', 'Matrix([2*y - (3*x) / 2 + (x*sqrt(33)) / 2, 3*x + (3*y) / 2 + (y*sqrt(33)) / 2])', '\\begin{bmatrix} 2 y - \\frac{3 x}{2} + \\frac{x \\sqrt{33}}{2} \\\\ 3 x + \\frac{3 y}{2} + \\frac{y \\sqrt{33}}{2} \\end{bmatrix}')})
		self.assertEqual (get ('solve (_ [0], _ [1], x, y)'), {'math': ('[{x: -y/2 - y sqrt(33) / 6}]', '[{x: -y/2 - (y*sqrt(33)) / 6}]', '\\left[\\left\\{x{:} -\\frac{y}{2} - \\frac{y \\sqrt{33}}{6} \\right\\} \\right]')})
		self.assertEqual (get ('\\[_ [0] [x], y].subs (y, 1)'), {'math': ('\\[-sqrt(33) / 6 - 1/2, 1]', 'Matrix([-sqrt(33) / 6 - S(1) / 2, 1])', '\\begin{bmatrix} -\\frac{\\sqrt{33}}{6} - \\frac{1}{2} \\\\ 1 \\end{bmatrix}')})
		self.assertEqual (get ('Subs (l, lambda, b) \\[x, y]'), {'math': ('\\[2 y - 3 x / 2 - x sqrt(33) / 2, 3 x + 3 y / 2 - y sqrt(33) / 2]', 'Matrix([2*y - (3*x) / 2 - (x*sqrt(33)) / 2, 3*x + (3*y) / 2 - (y*sqrt(33)) / 2])', '\\begin{bmatrix} 2 y - \\frac{3 x}{2} - \\frac{x \\sqrt{33}}{2} \\\\ 3 x + \\frac{3 y}{2} - \\frac{y \\sqrt{33}}{2} \\end{bmatrix}')})
		self.assertEqual (get ('solve (_ [0], _ [1], x, y)'), {'math': ('[{x: y sqrt(33) / 6 - y/2}]', '[{x: (y*sqrt(33)) / 6 - y/2}]', '\\left[\\left\\{x{:} \\frac{y \\sqrt{33}}{6} - \\frac{y}{2} \\right\\} \\right]')})
		self.assertEqual (get ('\\[_ [0] [x], y].subs (y, 1)'), {'math': ('\\[sqrt(33) / 6 - 1/2, 1]', 'Matrix([sqrt(33) / 6 - S(1) / 2, 1])', '\\begin{bmatrix} \\frac{\\sqrt{33}}{6} - \\frac{1}{2} \\\\ 1 \\end{bmatrix}')})
		self.assertEqual (get ('m.eigenvects ()'), {'math': ('[(5/2 - sqrt(33) / 2, 1, [\\[{-2} / {sqrt(33) / 2 - 3/2}, 1]]), (sqrt(33) / 2 + 5/2, 1, [\\[{-2} / {-sqrt(33) / 2 - 3/2}, 1]])]', '[(S(5) / 2 - sqrt(33) / 2, 1, [Matrix([(-2) / (sqrt(33) / 2 - S(3) / 2), 1])]), (sqrt(33) / 2 + S(5) / 2, 1, [Matrix([(-2) / (-sqrt(33) / 2 - S(3) / 2), 1])])]', '\\left[\\left(\\frac{5}{2} - \\frac{\\sqrt{33}}{2}, 1, \\left[\\begin{bmatrix} \\frac{-2}{\\frac{\\sqrt{33}}{2} - \\frac{3}{2}} \\\\ 1 \\end{bmatrix} \\right] \\right), \\left(\\frac{\\sqrt{33}}{2} + \\frac{5}{2}, 1, \\left[\\begin{bmatrix} \\frac{-2}{-\\frac{\\sqrt{33}}{2} - \\frac{3}{2}} \\\\ 1 \\end{bmatrix} \\right] \\right) \\right]')})
		self.assertEqual (get ('simplify _'), {'math': ('[(5/2 - sqrt(33) / 2, 1, [\\[-sqrt(33) / 6 - 1/2, 1]]), (sqrt(33) / 2 + 5/2, 1, [\\[sqrt(33) / 6 - 1/2, 1]])]', '[(S(5) / 2 - sqrt(33) / 2, 1, [Matrix([-sqrt(33) / 6 - S(1) / 2, 1])]), (sqrt(33) / 2 + S(5) / 2, 1, [Matrix([sqrt(33) / 6 - S(1) / 2, 1])])]', '\\left[\\left(\\frac{5}{2} - \\frac{\\sqrt{33}}{2}, 1, \\left[\\begin{bmatrix} -\\frac{\\sqrt{33}}{6} - \\frac{1}{2} \\\\ 1 \\end{bmatrix} \\right] \\right), \\left(\\frac{\\sqrt{33}}{2} + \\frac{5}{2}, 1, \\left[\\begin{bmatrix} \\frac{\\sqrt{33}}{6} - \\frac{1}{2} \\\\ 1 \\end{bmatrix} \\right] \\right) \\right]')})

	def test_sets (self):
		reset ()
		self.assertEqual (get ('1 in {1, 2, 3}'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('0 in {1, 2, 3}'), {'math': ('False', 'False', 'False')})
		self.assertEqual (get ('1 not in {1, 2, 3}'), {'math': ('False', 'False', 'False')})
		self.assertEqual (get ('0 not in {1, 2, 3}'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('a in {a, b, c}'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('z in {a, b, c}'), {'math': ('Contains(z, {a, b, c})', 'Contains(z, {a, b, c})', 'z \\in \\left\\{a, b, c\\right\\}')})
		self.assertEqual (get ('a not in {a, b, c}'), {'math': ('False', 'False', 'False')})
		self.assertEqual (get ('z not in {a, b, c}'), {'math': ('not Contains(z, {a, b, c})', 'Not(Contains(z, {a, b, c}))', '\\neg\\ z \\in \\left\\{a, b, c\\right\\}')})
		self.assertEqual (get ('{1, 2} || {2, 3}'), {'math': ('{1, 2, 3}', 'FiniteSet(1, 2, 3)', '\\left\\{1, 2, 3 \\right\\}')})
		self.assertEqual (get ('{1, 2} && {2, 3}'), {'math': ('{2,}', 'FiniteSet(2)', '\\left\\{2 \\right\\}')})
		self.assertEqual (get ('{1, 2} ^^ {2, 3}'), {'math': ('{1, 3}', 'FiniteSet(1, 3)', '\\left\\{1, 3 \\right\\}')})
		self.assertEqual (get ('{1, 2, 3} || {2, 3, 4} ^^ {3, 4, 5} && {4, 5, 6}'), {'math': ('{1, 2, 3, 5}', 'FiniteSet(1, 2, 3, 5)', '\\left\\{1, 2, 3, 5 \\right\\}')})
		self.assertEqual (get ('{a, b} || {b, c}'), {'math': ('{a, b, c}', 'FiniteSet(a, b, c)', '\\left\\{a, b, c \\right\\}')})
		self.assertEqual (get ('{a, b} && {b, c}'), {'math': ('{b,} || {a,} && {c,}', 'Union(FiniteSet(b), Intersection(FiniteSet(a), FiniteSet(c)))', '\\left\\{b \\right\\} \\cup \\left\\{a \\right\\} \\cap \\left\\{c \\right\\}')})
		self.assertEqual (get ('{a, b} ^^ {b, c}'), {'math': ('{a,} ^^ {c,}', 'Union(Complement(FiniteSet(a), FiniteSet(c)), Complement(FiniteSet(c), FiniteSet(a)))', '\\left\\{a \\right\\} \\ominus \\left\\{c \\right\\}')})
		self.assertEqual (get ('{a, b, c} || {b, c, d} ^^ {c, d, f} && {d, f, g}'), {'math': ('{a, b, c} || {f,} - {b, c} || ({b, c} && {b, c, d} - ({c,} && {g,})) - {f,}', 'Union(FiniteSet(a, b, c), FiniteSet(f) - FiniteSet(b, c), Intersection(FiniteSet(b, c), FiniteSet(b, c, d) - Intersection(FiniteSet(c), FiniteSet(g))) - FiniteSet(f))', '\\left\\{a, b, c \\right\\} \\cup \\left\\{f \\right\\} - \\left\\{b, c \\right\\} \\cup \\left(\\left\\{b, c \\right\\} \\cap \\left\\{b, c, d \\right\\} - \\left(\\left\\{c \\right\\} \\cap \\left\\{g \\right\\} \\right) \\right) - \\left\\{f \\right\\}')})
		self.assertEqual (get ('{a, b} < {a, b, c}'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('{a, b} <= {a, b, c}'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('{a, b, c} < {a, b, c}'), {'math': ('False', 'False', 'False')})
		self.assertEqual (get ('{a, b, c} <= {a, b, c}'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('{a, b, c, d} <= {a, b, c}'), {'math': ('False', 'False', 'False')})
		self.assertEqual (get ('{a, b, c} > {a, b}'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('{a, b, c} >= {a, b}'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('{a, b, c} > {a, b, c}'), {'math': ('False', 'False', 'False')})
		self.assertEqual (get ('{a, b, c} >= {a, b, c}'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('{a, b, c} >= {a, b, c, d}'), {'math': ('False', 'False', 'False')})
		self.assertEqual (get ('1 + i in Complexes'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('1 + i in Reals'), {'math': ('False', 'False', 'False')})
		self.assertEqual (get ('1.1 in Reals'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('1.1 in Integers'), {'math': ('False', 'False', 'False')})
		self.assertEqual (get ('0 in Naturals0'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('0 in Naturals'), {'math': ('False', 'False', 'False')})

	def test_logic (self):
		reset ()
		self.assertEqual (get ('not 0'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('not 1'), {'math': ('False', 'False', 'False')})
		self.assertEqual (get ('0 or 0'), {'math': ('False', 'False', 'False')})
		self.assertEqual (get ('0 or 1'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('1 or 1'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('0 and 0'), {'math': ('False', 'False', 'False')})
		self.assertEqual (get ('0 and 1'), {'math': ('False', 'False', 'False')})
		self.assertEqual (get ('1 and 1'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('not x'), {'math': ('not x', 'Not(x)', '\\neg\\ x')})
		self.assertEqual (get ('x or y'), {'math': ('x or y', 'Or(x, y)', 'x \\vee y')})
		self.assertEqual (get ('x and y'), {'math': ('x and y', 'And(x, y)', 'x \\wedge y')})
		self.assertEqual (get ('x or y and not z'), {'math': ('x or y and not z', 'Or(x, And(y, Not(z)))', 'x \\vee y \\wedge \\neg\\ z')})
		self.assertEqual (get ('(1 > 0) + (1 > 1) + (1 > 2)'), {'math': ('1', '1', '1')})
		self.assertEqual (get ('(1 >= 0) + (1 >= 1) + (1 >= 2)'), {'math': ('2', '2', '2')})
		self.assertEqual (get ('(1 < 0) + (1 < 1) + (1 < 2)'), {'math': ('1', '1', '1')})
		self.assertEqual (get ('(1 <= 0) + (1 <= 1) + (1 <= 2)'), {'math': ('2', '2', '2')})

	def test_funcs (self):
		reset ()
		self.assertEqual (get ('x = 1'), {'math': ('x = 1', 'x = 1', 'x = 1')})
		self.assertEqual (get ('f = lambda x: x**2'), {'math': ('f(x) = x**2', 'f = Lambda(x, x**2)', 'f\\left(x \\right) = x^2')})
		self.assertEqual (get ('y = ?(x, real = True)'), {'math': ('y = y(x, real = True)', "y = Function('y', real = True)(x)", 'y = y\\left(x, real = True \\right)')})
		self.assertEqual (get ('z = z(x)'), {'math': ('z = z(x)', "z = Function('z')(x)", 'z = z\\left(x \\right)')})
		self.assertEqual (get ('g (x) = x**3'), {'math': ('g(x) = x**3', 'g = Lambda(x, x**3)', 'g\\left(x \\right) = x^3')})
		self.assertEqual (get ('vars'), {'math': [('f(x) = x**2', 'f = Lambda(x, x**2)', 'f\\left(x \\right) = x^2'), ('g(x) = x**3', 'g = Lambda(x, x**3)', 'g\\left(x \\right) = x^3'), ('y = y(x, real = True)', "y = Function('y', real = True)(x)", 'y = y\\left(x, real = True \\right)'), ('z = z(x)', "z = Function('z')(x)", 'z = z\\left(x \\right)'), ('x = 1', 'x = 1', 'x = 1')]})
		self.assertEqual (get ('z = y'), {'math': ('z = y(x, real = True)', "z = Function('y', real = True)(x)", 'z = y\\left(x, real = True \\right)')})
		self.assertEqual (get ('vars'), {'math': [('f(x) = x**2', 'f = Lambda(x, x**2)', 'f\\left(x \\right) = x^2'), ('g(x) = x**3', 'g = Lambda(x, x**3)', 'g\\left(x \\right) = x^3'), ('y = y(x, real = True)', "y = Function('y', real = True)(x)", 'y = y\\left(x, real = True \\right)'), ('z = y(x, real = True)', "z = Function('y', real = True)(x)", 'z = y\\left(x, real = True \\right)'), ('x = 1', 'x = 1', 'x = 1')]})
		self.assertEqual (get ('del y'), {'msg': ["Undefined function 'y' deleted."]})
		self.assertEqual (get ('vars'), {'math': [('f(x) = x**2', 'f = Lambda(x, x**2)', 'f\\left(x \\right) = x^2'), ('g(x) = x**3', 'g = Lambda(x, x**3)', 'g\\left(x \\right) = x^3'), ('z = y(x, real = True)', "z = Function('y', real = True)(x)", 'z = y\\left(x, real = True \\right)'), ('x = 1', 'x = 1', 'x = 1')]})
		self.assertEqual (get ('delall'), {'msg': ['All variables deleted.']})
		self.assertEqual (get ('vars'), {'msg': ['No variables defined.']})

	def test_ufuncs (self):
		reset ()
		self.assertEqual (get ('f = ? ()'), {'math': ('f = f()', "f = Function('f')", 'f = f\\left( \\right)')})
		self.assertEqual (get ('f (x)'), {'math': ('f(x)', "Function('f')(x)", 'f\\left(x \\right)')})
		self.assertEqual (get ('f (x) (0)'), {'math': ('f(0)', "Function('f')(0)", 'f\\left(0 \\right)')})
		self.assertEqual (get ('f (0)'), {'math': ('f(0)', "Function('f')(0)", 'f\\left(0 \\right)')})
		self.assertEqual (get ('f = ?g ()'), {'math': ('f = ?g()', "f = Function('g')", 'f = ?g\\left( \\right)')})
		self.assertEqual (get ('f (x)'), {'math': ('?g(x)', "Function('g')(x)", '?g\\left(x \\right)')})
		self.assertEqual (get ('f (x) (0)'), {'math': ('?g(0)', "Function('g')(0)", '?g\\left(0 \\right)')})
		self.assertEqual (get ('f (0)'), {'math': ('?g(0)', "Function('g')(0)", '?g\\left(0 \\right)')})
		self.assertEqual (get ('f = g ()'), {'math': ('f = g()', "f = Function('g')", 'f = g\\left( \\right)')})
		self.assertEqual (get ('f (x)'), {'math': ('g(x)', "Function('g')(x)", 'g\\left(x \\right)')})
		self.assertEqual (get ('f (x) (0)'), {'math': ('g(0)', "Function('g')(0)", 'g\\left(0 \\right)')})
		self.assertEqual (get ('f (0)'), {'math': ('g(0)', "Function('g')(0)", 'g\\left(0 \\right)')})
		self.assertEqual (get ("f' (x)"), {'err': 'ValueError: Since there are no variables in the expression, the variable(s) of differentiation must be supplied to differentiate g()'})
		self.assertEqual (get ('d/dx (f) (x)'), {'math': ('0', '0', '0')})
		self.assertEqual (get ('f = f (x)'), {'math': ('f = g(x)', "f = Function('g')(x)", 'f = g\\left(x \\right)')})
		self.assertEqual (get ('f (x)'), {'math': ('x g(x)', "x*Function('g')(x)", 'x g\\left(x \\right)')})
		self.assertEqual (get ('f (x) (0)'), {'math': ('0', '0', '0')})
		self.assertEqual (get ('f (0)'), {'math': ('g(0)', "Function('g')(0)", 'g\\left(0 \\right)')})
		self.assertEqual (get ('f = ?g (x)'), {'math': ('f = ?g(x)', "f = Function('g')(x)", 'f = ?g\\left(x \\right)')})
		self.assertEqual (get ('f (x)'), {'math': ('x ?g(x)', "x*Function('g')(x)", 'x ?g\\left(x \\right)')})
		self.assertEqual (get ('f (x) (0)'), {'math': ('0', '0', '0')})
		self.assertEqual (get ('f (0)'), {'math': ('g(0)', "Function('g')(0)", 'g\\left(0 \\right)')})
		self.assertEqual (get ('f = g (x)'), {'math': ('f = g(x)', "f = Function('g')(x)", 'f = g\\left(x \\right)')})
		self.assertEqual (get ('f (x)'), {'math': ('x g(x)', "x*Function('g')(x)", 'x g\\left(x \\right)')})
		self.assertEqual (get ('f (x) (0)'), {'math': ('0', '0', '0')})
		self.assertEqual (get ('f (0)'), {'math': ('g(0)', "Function('g')(0)", 'g\\left(0 \\right)')})
		self.assertEqual (get ("f' (x)"), {'math': ("x g(x)'", "x*diff(Function('g')(x))", "x g\\left(x \\right)'")})
		self.assertEqual (get ('d/dx (f) (x)'), {'math': ("x g(x)'", "x*diff(Function('g')(x))", "x g\\left(x \\right)'")})
		self.assertEqual (get ('u = u (x, t)'), {'math': ('u = u(x, t)', "u = Function('u')(x, t)", 'u = u\\left(x, t \\right)')})
		self.assertEqual (get ('du/dx (x, t)'), {'math': ('d / dx (u(x, t)) * (x, t)', "Derivative(Function('u')(x, t), x)*(x, t)", '\\frac{d}{dx}\\left(u\\left(x, t \\right) \\right) \\cdot \\left(x, t \\right)')})
		self.assertEqual (get ('du/dx (1, t)'), {'math': ('d / dx (u(x, t))(1, t)', "Subs(Derivative(Function('u')(x, t), x), x, 1)", '\\frac{d}{dx}\\left(u\\left(x, t \\right) \\right)\\left(1, t \\right)')})
		self.assertEqual (get ('du/dx (1, 0)'), {'math': ('d / dx (u(x, t))(1, 0)', "Subs(Derivative(Function('u')(x, t), x), (x, t), (1, 0))", '\\frac{d}{dx}\\left(u\\left(x, t \\right) \\right)\\left(1, 0 \\right)')})
		self.assertEqual (get ('d**2u / dx dt (1, 0)'), {'math': ('d**2 / dt dx (u(x, t))(1, 0)', "Subs(Derivative(Function('u')(x, t), t, x), (x, t), (1, 0))", '\\frac{\\partial^2}{\\partial t \\partial x}\\left(u\\left(x, t \\right) \\right)\\left(1, 0 \\right)')})
		self.assertEqual (get ('d/dx u (1, 0)'), {'math': ('0', '0', '0')})
		self.assertEqual (get ('d/dx (u) (1, 0)'), {'math': ('d / dx (u(x, t))(1, 0)', "Subs(Derivative(Function('u')(x, t), x), (x, t), (1, 0))", '\\frac{d}{dx}\\left(u\\left(x, t \\right) \\right)\\left(1, 0 \\right)')})
		self.assertEqual (get ('d**2 / dx dt u (1, 0)'), {'math': ('0', '0', '0')})
		self.assertEqual (get ('d**2 / dx dt (u) (1, 0)'), {'math': ('d**2 / dt dx (u(x, t))(1, 0)', "Subs(Derivative(Function('u')(x, t), t, x), (x, t), (1, 0))", '\\frac{\\partial^2}{\\partial t \\partial x}\\left(u\\left(x, t \\right) \\right)\\left(1, 0 \\right)')})
		self.assertEqual (get ('f () = x**2'), {'math': ('f() = x**2', 'f = Lambda((), x**2)', 'f\\left( \\right) = x^2')})
		self.assertEqual (get ('g (2) = x**2'), {'err': 'server.RealityRedefinitionError: cannot assign to a function containing non-variable parameters'})
		self.assertEqual (get ('h (x) = x**2'), {'math': ('h(x) = x**2', 'h = Lambda(x, x**2)', 'h\\left(x \\right) = x^2')})
		self.assertEqual (get ('delall'), {'msg': ['All variables deleted.']})
		self.assertEqual (get ('?f () = x**2'), {'math': ('?f() = x**2', "Eq(Function('f'), x**2)", '?f\\left( \\right) = x^2')})
		self.assertEqual (get ('?g (2) = x**2'), {'math': ('?g(2) = x**2', "Eq(Function('g')(2), x**2)", '?g\\left(2 \\right) = x^2')})
		self.assertEqual (get ('?h (x) = x**2'), {'math': ('?h(x) = x**2', "Eq(Function('h')(x), x**2)", '?h\\left(x \\right) = x^2')})
		self.assertEqual (get ('f (x) = x**3'), {'math': ('f(x) = x**3', 'f = Lambda(x, x**3)', 'f\\left(x \\right) = x^3')})
		self.assertEqual (get ("f'(3)"), {'math': ('27', '27', '27')})
		self.assertEqual (get ("f''(3)"), {'math': ('18', '18', '18')})
		self.assertEqual (get ('df / dx (3)'), {'math': ('27', '27', '27')})
		self.assertEqual (get ('d**2 f / dx**2 (3)'), {'math': ('18', '18', '18')})
		self.assertEqual (get ('d / dx (f) (3)'), {'math': ('27', '27', '27')})
		self.assertEqual (get ('d**2 / dx**2 (f) (3)'), {'math': ('18', '18', '18')})
		self.assertEqual (get ('f (x, y) = x**2 y**3'), {'math': ('f(x, y) = x**2 y**3', 'f = Lambda((x, y), x**2*y**3)', 'f\\left(x, y \\right) = x^2 y^3')})
		self.assertEqual (get ("f'(3, 2)"), {'err': 'ValueError: Since there is more than one variable in the expression, the variable(s) of differentiation must be supplied to differentiate x**2*y**3'})
		self.assertEqual (get ('df / dx (3, 2)'), {'math': ('48', '48', '48')})
		self.assertEqual (get ('df / dy (3, 2)'), {'math': ('108', '108', '108')})
		self.assertEqual (get ('d**2 f / dx dy (3, 2)'), {'math': ('72', '72', '72')})
		self.assertEqual (get ('d / dx (f) (3, 2)'), {'math': ('48', '48', '48')})
		self.assertEqual (get ('d / dy (f) (3, 2)'), {'math': ('108', '108', '108')})
		self.assertEqual (get ('d**2 / dx dy (f) (3, 2)'), {'math': ('72', '72', '72')})

	def test_intro_examples (self):
		reset ()
		self.assertEqual (get ('cos**-1 0 \\log_2 8'), {'math': ('3 pi / 2', '(3*pi) / 2', '\\frac{3 \\pi}{2}')})
		self.assertEqual (get ('expand ((1 + x)**4)'), {'math': ('x**4 + 4 x + 4x**3 + 6x**2 + 1', 'x**4 + 4*x + 4*x**3 + 6*x**2 + 1', 'x^4 + 4 x + 4 x^3 + 6 x^2 + 1')})
		self.assertEqual (get ('factor (x^3 + 3y x^2 + 3x y^2 + y^3)'), {'math': ('(x + y)**3', '(x + y)**3', '\\left(x + y \\right)^3')})
		self.assertEqual (get ('series (e^x, x, 0, 5)'), {'math': ('1 + x + x**2 / 2 + x**3 / 6 + x**4 / 24 + O(x**5)', '1 + x + x**2 / 2 + x**3 / 6 + x**4 / 24 + O(x**5)', '1 + x + \\frac{x^2}{2} + \\frac{x^3}{6} + \\frac{x^4}{24} + \\operatorname{O}{\\left(x^5 \\right)}')})
		self.assertEqual (get ("Limit (\\frac1x, x, 0, dir='-')"), {'math': ('-oo', '-oo', '-\\infty')})
		self.assertEqual (get ('\\sum_{n=0}**oo x^n / n!'), {'math': ('e**x', 'e**x', 'e^x')})
		self.assertEqual (get ('d**6 / dx dy**2 dz**3 x^3 y^3 z^3'), {'math': ('108 y x**2', '108*y*x**2', '108 y x^2')})
		self.assertEqual (get ('Integral (e^{-x^2}, (x, 0, \\infty))'), {'math': ('sqrt(pi) / 2', 'sqrt(pi) / 2', '\\frac{\\sqrt{\\pi}}{2}')})
		self.assertEqual (get ('\\int_0^\\pi \\int_0^{2pi} \\int_0^1 rho**2 sin\\phi drho dtheta dphi'), {'math': ('4 pi / 3', '(4*pi) / 3', '\\frac{4 \\pi}{3}')})
		self.assertEqual (get ('\\[[1, 2], [3, 4]]**-1'), {'math': ('\\[[-2, 1], [3/2, -1/2]]', 'Matrix([[-2, 1], [S(3) / 2, -S(1) / 2]])', '\\begin{bmatrix} -2 & 1 \\\\ \\frac{3}{2} & -\\frac{1}{2} \\end{bmatrix}')})
		self.assertEqual (get ('Matrix (4, 4, lambda r, c: c + r if c > r else 0)'), {'math': ('\\[[0, 1, 2, 3], [0, 0, 3, 4], [0, 0, 0, 5], [0, 0, 0, 0]]', 'Matrix([[0, 1, 2, 3], [0, 0, 3, 4], [0, 0, 0, 5], [0, 0, 0, 0]])', '\\begin{bmatrix} 0 & 1 & 2 & 3 \\\\ 0 & 0 & 3 & 4 \\\\ 0 & 0 & 0 & 5 \\\\ 0 & 0 & 0 & 0 \\end{bmatrix}')})
		self.assertEqual (get ('(({1, 2, 3} && {2, 3, 4}) ^^ {3, 4, 5}) - \\{4} || {7,}'), {'math': ('{2, 5, 7}', 'FiniteSet(2, 5, 7)', '\\left\\{2, 5, 7 \\right\\}')})
		self.assertEqual (get ('f (x, y) = sqrt (x**2 + y**2)'), {'math': ('f(x, y) = sqrt(x**2 + y**2)', 'f = Lambda((x, y), sqrt(x**2 + y**2))', 'f\\left(x, y \\right) = \\sqrt{x^2 + y^2}')})
		self.assertEqual (get ('solve (x**2 + y = 4, x)'), {'math': ('[-sqrt(4 - y), sqrt(4 - y)]', '[-sqrt(4 - y), sqrt(4 - y)]', '\\left[-\\sqrt{4 - y}, \\sqrt{4 - y} \\right]')})
		self.assertEqual (get ("dsolve (y(x)'' + 9y(x))"), {'math': ('y(x) == C1 sin(3 x) + C2 cos(3 x)', "Eq(Function('y')(x), C1*sin(3*x) + C2*cos(3*x))", 'y\\left(x \\right) == C_{1}\\ \\sin{\\left(3 x \\right)} + C_{2}\\ \\cos{\\left(3 x \\right)}')})
		self.assertEqual (get ("y = y(t); dsolve (y'' - 4y' - 12y = 3e**{5t})"), {'math': ('y = y(t)', "y = Function('y')(t)", 'y = y\\left(t \\right)')})
	# END UPDATE BLOCK

def get (text):
	resp = requests.post (URL, {'idx': 1, 'mode': 'evaluate', 'text': text}).json ().get ('data', [{}]) [0]
	ret  = {}

	if 'math' in resp:
		math         = [(resp ['math'] [i] ['nat'], resp ['math'] [i] ['py'], resp ['math'] [i] ['tex']) for i in range (len (resp ['math']))]
		ret ['math'] = math if len (math) > 1 else math [0]

	if 'msg' in resp:
		ret ['msg'] = resp ['msg']

	if 'err' in resp:
		ret ['err'] = resp ['err'] [-1]

	return ret

def reset ():
	get ('envreset')
	get ('delall')
	get ('0')

_SESSIONS = (

('vars', """

x
x = 2
x
x*3
x**2
y
y = x
y
del (x, y)
x
y
x = x
x, y = x, y
x, y = y, x
x, y = 1, 2
x, y = y, x
x, y
del vars
x
y

"""), ('lambdas', """

f = lambda: 2
f
f ()
f = lambda: y
f
f ()
y = 2
f
f ()
f = lambda: y
f
f ()
f = lambda: @y
f
f ()
del y
f = lambda x: x
f
f (x)
f (y)
f (2)
f = lambda x: x**2
f (x)
f (y)
f (2)

g = lambda x: f(x) + f(2x)
g
g (x)
g (y)
g (2)
del f
g (2)
f = lambda x: x**2
g = lambda x: @(f(x) + f(2x))
h = lambda x: @(f(x)) + @(f(2x))
g == h
g
g (x)
g (y)
g (2)
del f
g (2)
f = lambda x, y: x + y
f (1, 2)
g (2)
f = lambda x, y, z: x + y + z
f (1, 2, 3)
f = lambda x, y, z, w: x + y + z + w
f (1, 2, 3, 4)
f (1, 2, 3)
f (1, 2, 3, 4, 5)

f = lambda x: lambda: x**2
f (2)
_ ()
f = lambda x: lambda: lambda: x**2
f (3)
_ ()
_ ()
solve (x**2 + 2 x - 1 > 7)
f = lambda x: _
f (-4.1), f (-4), f (0), f (2), f (2.1)
f (x) = x**2
f (2)
f (x, y) = sqrt {x**2 + y**2}
f (3, 4)
del f

"""), ('lambdas2', """

f = lambda x: x**2
f (2)
f (x) = x**2
f (3)
f (x, y) = sqrt (x**2 + y**2)
f (3, 4)
x, y, z = 3, 4, 5
f (x, y) = sqrt (x**2 + y**2) + z
f (x, y) = sqrt (x**2 + y**2) + @z
f (x) = x**2
f (x) = @x**2
f (x) = y**2
f (2)
f (x) = @y**2
f (2)
y = 6
f (2)
f = 2
f (x) = x**2

delall
f (x) = x**2
g (x, y) = sqrt (f(x) + f(y))
g (3, 4)
f (x) = x**3
g (3, 4)
g (x, y) = @sqrt (f(x) + f(y))
g (3, 4)
f (x) = x**2
g (3, 4)

delall
f (x) = \\int x dx
f (sin x)
f (x) = %(\\int x dx)
f (sin x)
f (sin y)
f (x) = \\int x dx
f (sin x)
f (sin y)
\\int sin y dx

"""), ('env', """

env (quick)
env (noquick)
env
env (EI, quick, nopyS, nosimplify, nomatsimp, nodoit, noN, noO, noS, nogamma, noGamma, nozeta)
env
envreset
env

"""), ('idx_and_attr', """

x [y]
x.y
x = [1, 2, 3]
x [y]
x.y
[1, 2, 3] [y]
[1, 2, 3].y
y = 2
x [y]
x.y
[1, 2, 3] [y]
[1, 2, 3].y

"""), ('greek', """

env (quick)
alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega
\\alpha, \\beta, \\gamma, \\delta, \\epsilon, \\zeta, \\eta, \\theta, \\iota, \\kappa, \\lambda, \\mu, \\nu, \\xi, \\pi, \\rho, \\sigma, \\tau, \\upsilon, \\phi, \\chi, \\psi, \\omega, \\Gamma, \\Delta, \\Theta, \\Lambda, \\Xi, \\Pi, \\Sigma, \\Upsilon, \\Phi, \\Psi, \\Omega
env (noquick)
alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega
\\alpha, \\beta, \\gamma, \\delta, \\epsilon, \\zeta, \\eta, \\theta, \\iota, \\kappa, \\lambda, \\mu, \\nu, \\xi, \\pi, \\rho, \\sigma, \\tau, \\upsilon, \\phi, \\chi, \\psi, \\omega, \\Gamma, \\Delta, \\Theta, \\Lambda, \\Xi, \\Pi, \\Sigma, \\Upsilon, \\Phi, \\Psi, \\Omega

"""), ('simplification', """

env (nosimplify, nomatsimp)
\\[[x + 1, x - 1], [x - 1, x + 1]]**2
solve (x**3 = 5)
env ('simplify', nomatsimp)
\\[[x + 1, x - 1], [x - 1, x + 1]]**2
solve (x**3 = 5)
env (nosimplify, matsimp)
\\[[x + 1, x - 1], [x - 1, x + 1]]**2
env ('simplify', matsimp)
\\[[x + 1, x - 1], [x - 1, x + 1]]**2
solve (x**3 = 5)

"""), ('calculate_eigen', """

m = \\[[1, 2], [3, 4]]
l = m - lambda eye 2
l.det ()
solve _
a, b = _
m.eigenvals ()
Subs (l, lambda, a) \\[x, y]
solve (_ [0], _ [1], x, y)
\\[_ [0] [x], y].subs (y, 1)
Subs (l, lambda, b) \\[x, y]
solve (_ [0], _ [1], x, y)
\\[_ [0] [x], y].subs (y, 1)
m.eigenvects ()
simplify _

"""), ('sets', """

1 in {1, 2, 3}
0 in {1, 2, 3}
1 not in {1, 2, 3}
0 not in {1, 2, 3}
a in {a, b, c}
z in {a, b, c}
a not in {a, b, c}
z not in {a, b, c}
{1, 2} || {2, 3}
{1, 2} && {2, 3}
{1, 2} ^^ {2, 3}
{1, 2, 3} || {2, 3, 4} ^^ {3, 4, 5} && {4, 5, 6}
{a, b} || {b, c}
{a, b} && {b, c}
{a, b} ^^ {b, c}
{a, b, c} || {b, c, d} ^^ {c, d, f} && {d, f, g}
{a, b} < {a, b, c}
{a, b} <= {a, b, c}
{a, b, c} < {a, b, c}
{a, b, c} <= {a, b, c}
{a, b, c, d} <= {a, b, c}
{a, b, c} > {a, b}
{a, b, c} >= {a, b}
{a, b, c} > {a, b, c}
{a, b, c} >= {a, b, c}
{a, b, c} >= {a, b, c, d}
1 + i in Complexes
1 + i in Reals
1.1 in Reals
1.1 in Integers
0 in Naturals0
0 in Naturals

"""), ('logic', """

not 0
not 1
0 or 0
0 or 1
1 or 1
0 and 0
0 and 1
1 and 1
not x
x or y
x and y
x or y and not z
(1 > 0) + (1 > 1) + (1 > 2)
(1 >= 0) + (1 >= 1) + (1 >= 2)
(1 < 0) + (1 < 1) + (1 < 2)
(1 <= 0) + (1 <= 1) + (1 <= 2)

"""), ('funcs', """

x = 1
f = lambda x: x**2
y = ?(x, real = True)
z = z(x)
g (x) = x**3
vars
z = y
vars
del y
vars
delall
vars

"""), ('ufuncs', """

f = ? ()
f (x)
f (x) (0)
f (0)
f = ?g ()
f (x)
f (x) (0)
f (0)
f = g ()
f (x)
f (x) (0)
f (0)
f' (x)
d/dx (f) (x)

f = f (x)
f (x)
f (x) (0)
f (0)
f = ?g (x)
f (x)
f (x) (0)
f (0)
f = g (x)
f (x)
f (x) (0)
f (0)
f' (x)
d/dx (f) (x)

u = u (x, t)
du/dx (x, t)
du/dx (1, t)
du/dx (1, 0)
d**2u / dx dt (1, 0)
d/dx u (1, 0)
d/dx (u) (1, 0)
d**2 / dx dt u (1, 0)
d**2 / dx dt (u) (1, 0)

f () = x**2
g (2) = x**2
h (x) = x**2
delall
?f () = x**2
?g (2) = x**2
?h (x) = x**2

f (x) = x**3
f'(3)
f''(3)
df / dx (3)
d**2 f / dx**2 (3)
d / dx (f) (3)
d**2 / dx**2 (f) (3)
f (x, y) = x**2 y**3
f'(3, 2)
df / dx (3, 2)
df / dy (3, 2)
d**2 f / dx dy (3, 2)
d / dx (f) (3, 2)
d / dy (f) (3, 2)
d**2 / dx dy (f) (3, 2)

"""), ('intro_examples', """

cos**-1 0 \\log_2 8
expand ((1 + x)**4)
factor (x^3 + 3y x^2 + 3x y^2 + y^3)
series (e^x, x, 0, 5)
Limit (\\frac1x, x, 0, dir='-')
\\sum_{n=0}**oo x^n / n!
d**6 / dx dy**2 dz**3 x^3 y^3 z^3
Integral (e^{-x^2}, (x, 0, \\infty))
\\int_0^\\pi \\int_0^{2pi} \\int_0^1 rho**2 sin\\phi drho dtheta dphi
\\[[1, 2], [3, 4]]**-1
Matrix (4, 4, lambda r, c: c + r if c > r else 0)
(({1, 2, 3} && {2, 3, 4}) ^^ {3, 4, 5}) - \\{4} || {7,}
f (x, y) = sqrt (x**2 + y**2)
solve (x**2 + y = 4, x)
dsolve (y(x)'' + 9y(x))
y = y(t); dsolve (y'' - 4y' - 12y = 3e**{5t})

"""),

)

SYSARGV  = sys.argv [:]
sys.argv = [os.path.abspath ('server.py'), '--child', '127.0.0.1:9001']

import server

HTTPD = server.start_server (logging = False)
URL   = f'http://{HTTPD.server_address [0]}:{HTTPD.server_address [1]}/'
# URL   = f'http://127.0.0.1:9000/'

if __name__ == '__main__':
	if SYSARGV [1] in {'--print', '--update'}:
		lines = []

		for name, texts in _SESSIONS:
			reset ()

			lines.extend (['', f'\tdef test_{name} (self):\n\t\treset ()'])

			texts = [s.strip () for s in texts.strip ().split ('\n')]

			for text in texts:
				if text:
					lines.append (f'\t\tself.assertEqual (get ({text!r}), {get (text)!r})')

		if SYSARGV [1] == '--print':
			for line in lines:
				print (line)

		else: # '--update'
			testserver = open ('test_server.py', encoding = 'utf8').readlines ()

			start  = testserver.index ('\t# BEGIN UPDATE BLOCK\n')
			end    = testserver.index ('\t# END UPDATE BLOCK\n')

			testserver [start + 1 : end] = (f'{line}\n' for line in lines [1:])

			open ('test_server.py', 'w', encoding = 'utf8').writelines (testserver)

	elif SYSARGV [1] == '--human':
		session = SYSARGV [2] if len (SYSARGV) > 2 else None

		for name, texts in _SESSIONS:
			if session and name != session:
				continue

			reset ()

			print (f'\n{name}\n')

			texts = [s.strip () for s in texts.strip ().split ('\n')]

			for text in texts:
				if not text:
					print ()

				else:
					resp = get (text)

					print (text)

					if 'msg' in resp:
						print ('\n'.join (resp ['msg']))

					if 'err' in resp:
						print (resp ['err'])

					if 'math' in resp:
						math = resp ['math']

						if isinstance (math [0], tuple):
							math = ['\n'.join (m) for m in math]

						print ('\n'.join (math))

					print ()
