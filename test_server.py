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
		self.assertEqual (get ('env (quick)'), {'msg': ['Quick input mode is on.<i> - "quick"</i>']})
		self.assertEqual (get ('α, β, γ, δ, ε, ζ, η, θ, ι, κ, λ, μ, ν, ξ, π, ρ, σ, τ, υ, φ, χ, ψ, ω, Γ, Δ, Θ, Λ, Ξ, Π, Σ, Υ, Φ, Ψ, Ω'), {'math': ('(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '\\left(\\alpha, \\beta, \\gamma, \\delta, \\epsilon, \\zeta, \\eta, \\theta, \\iota, \\kappa, \\lambda, \\mu, \\nu, \\xi, \\pi, \\rho, \\sigma, \\tau, \\upsilon, \\phi, \\chi, \\psi, \\omega, \\Gamma, \\Delta, \\Theta, \\Lambda, \\Xi, \\Pi, \\Sigma, \\Upsilon, \\Phi, \\Psi, \\Omega \\right)')})
		self.assertEqual (get ('env (noquick)'), {'msg': ['Quick input mode is off.<i> - "quick"</i>']})
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

	def test_lambda (self):
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

	def test_lambda2 (self):
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

	def test_lambda_expr (self):
		reset ()
		self.assertEqual (get ('a = lambda l: l'), {'math': ('a(l) = l', 'a = Lambda(l, l)', 'a\\left(l \\right) = l')})
		self.assertEqual (get ('a; a'), {'math': ('lambda l: l', 'Lambda(l, l)', '\\left(l \\mapsto l \\right)')})
		self.assertEqual (get ('{a = a}'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('a == a'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('a.b'), {'math': ('l.b', 'l.b', 'l.b')})
		self.assertEqual (get ('a, a'), {'math': ('(lambda l: l, lambda l: l)', '(Lambda(l, l), Lambda(l, l))', '\\left(\\left(l \\mapsto l \\right), \\left(l \\mapsto l \\right) \\right)')})
		self.assertEqual (get ('{a}'), {'math': ('lambda l: l', 'Lambda(l, l)', '\\left(l \\mapsto l \\right)')})
		self.assertEqual (get ('(a)'), {'math': ('l', 'l', 'l')})
		self.assertEqual (get ('[a]'), {'math': ('[lambda l: l]', '[Lambda(l, l)]', '\\left[\\left(l \\mapsto l \\right) \\right]')})
		self.assertEqual (get ('|a|'), {'math': ('{|l|}', 'abs(l)', '\\left|l \\right|')})
		self.assertEqual (get ('-a'), {'math': ('-l', '-l', '-l')})
		self.assertEqual (get ('a!'), {'math': ('l!', 'factorial(l)', 'l!')})
		self.assertEqual (get ('a + a'), {'math': ('2 l', '2*l', '2 l')})
		self.assertEqual (get ('a a'), {'math': ('lambda l: l', 'Lambda(l, l)', '\\left(l \\mapsto l \\right)')})
		self.assertEqual (get ('{a} a'), {'math': ('l**2', 'l**2', 'l^2')})
		self.assertEqual (get ('a * a'), {'math': ('l**2', 'l**2', 'l^2')})
		self.assertEqual (get ('a / a'), {'math': ('1', '1', '1')})
		self.assertEqual (get ('a ** a'), {'math': ('l**l', 'l**l', 'l^l')})
		self.assertEqual (get ('ln a'), {'math': ('ln(l)', 'ln(l)', '\\ln{\\left(l \\right)}')})
		self.assertEqual (get ('sqrt a'), {'math': ('sqrt(l)', 'sqrt(l)', '\\sqrt{l}')})
		self.assertEqual (get ('sin a'), {'math': ('sin(lambda l: l)', 'sin(Lambda(l, l))', '\\sin{\\left(\\left(l \\mapsto l \\right) \\right)}')})
		self.assertEqual (get ('\\lim_{a\\to0} a'), {'math': ('0', '0', '0')})
		self.assertEqual (get ('\\sum_{n=0}^9 a'), {'math': ('10 l', '10*l', '10 l')})
		self.assertEqual (get ('d/dx a'), {'math': ('0', '0', '0')})
		self.assertEqual (get ("a'"), {'math': ('1', '1', '1')})
		self.assertEqual (get ('\\int a dx'), {'math': ('l x', 'l*x', 'l\\ x')})
		self.assertEqual (get ('\\[[a, a], [a, a]]'), {'math': ('\\[[l, l], [l, l]]', 'Matrix([[l, l], [l, l]])', '\\begin{bmatrix} l & l \\\\ l & l \\end{bmatrix}')})
		self.assertEqual (get ('a if a else a'), {'math': ('lambda l: l', 'Lambda(l, l)', '\\left(l \\mapsto l \\right)')})
		self.assertEqual (get ('a if a'), {'math': ('{lambda l: l} if l', 'Piecewise((Lambda(l, l), l))', '\\begin{cases} \\left(l \\mapsto l \\right) & \\text{for}\\: l \\end{cases}')})
		self.assertEqual (get ('lambda: a'), {'math': ('lambda: {lambda l: l}', 'Lambda((), Lambda(l, l))', '\\left(\\left( \\right) \\mapsto \\left(l \\mapsto l \\right) \\right)')})
		self.assertEqual (get ('a [a]'), {'math': ('[lambda l: l]', '[Lambda(l, l)]', '\\left[\\left(l \\mapsto l \\right) \\right]')})
		self.assertEqual (get ('{a} [a]'), {'math': ('l[l]', 'l[l]', 'l\\left[l \\right]')})
		self.assertEqual (get (': a'), {'math': (':l', 'slice(l)', '{:}l')})
		self.assertEqual (get ('a: a'), {'math': ('l:l', 'slice(l, l)', 'l{:}l')})
		self.assertEqual (get (':b a'), {'math': (':b l', 'slice(b*l)', '{:}b\\ l')})
		self.assertEqual (get ('a:b: a'), {'math': ('l:b:l', 'slice(l, b, l)', 'l{:}b{:}l')})
		self.assertEqual (get ('::c a'), {'math': ('::c l', 'slice(None, None, c*l)', '{:}{:}c\\ l')})
		self.assertEqual (get ('a:b:c a'), {'math': ('l:b:c l', 'slice(l, b, c*l)', 'l{:}b{:}c\\ l')})
		self.assertEqual (get ('{a, a}'), {'math': ('{lambda l: l,}', 'FiniteSet(Lambda(l, l))', '\\left\\{\\left(l \\mapsto l \\right) \\right\\}')})
		self.assertEqual (get ('{a, a + 1}'), {'math': ('{l + 1, lambda l: l}', 'FiniteSet(l + 1, Lambda(l, l))', '\\left\\{l + 1, \\left(l \\mapsto l \\right) \\right\\}')})
		self.assertEqual (get ('{a: a}'), {'math': ('{(lambda l: l): {lambda l: l}}', '{Lambda(l, l): Lambda(l, l)}', '\\left\\{\\left(l \\mapsto l \\right){:} \\left(l \\mapsto l \\right) \\right\\}')})
		self.assertEqual (get ('a || a'), {'err': 'TypeError: Input args to Union must be Sets'})
		self.assertEqual (get ('a ^^ a'), {'err': "AttributeError: 'Symbol' object has no attribute 'is_subset'"})
		self.assertEqual (get ('a && a'), {'err': 'TypeError: Input args to Union must be Sets'})
		self.assertEqual (get ('a or a'), {'math': ('l', 'l', 'l')})
		self.assertEqual (get ('a and a'), {'math': ('l', 'l', 'l')})
		self.assertEqual (get ('not a'), {'math': ('not l', 'Not(l)', '\\neg\\ l')})
		self.assertEqual (get ('\\. a |_{a = a}'), {'math': ('l', 'l', 'l')})
		self.assertEqual (get ('\\. a |_{a = b}'), {'math': ('l', 'l', 'l')})

	def test_env (self):
		reset ()
		self.assertEqual (get ('env (quick)'), {'msg': ['Quick input mode is on.<i> - "quick"</i>']})
		self.assertEqual (get ('env (noquick)'), {'msg': ['Quick input mode is off.<i> - "quick"</i>']})
		self.assertEqual (get ('env'), {'msg': ['Uppercase E and I is off.<i> - "EI"</i>', 'Quick input mode is off.<i> - "quick"</i>', 'Python S escaping is on.<i> - "pyS"</i>', 'Post-evaluation simplify is off.<i> - "simplify"</i>', 'Matrix simplify is on.<i> - "matsimp"</i>', 'Undefined function map to variable is on.<i> - "ufuncmap"</i>', 'Leading product rational is off.<i> - "prodrat"</i>', 'Expression doit is on.<i> - "doit"</i>', 'Strict LaTeX formatting is on.<i> - "strict"</i>', 'Function N is on.', 'Function O is on.', 'Function S is on.', 'Function beta is on.', 'Function gamma is on.', 'Function Gamma is on.', 'Function Lambda is on.', 'Function zeta is on.']})
		self.assertEqual (get ('env (EI, quick, nopyS, nosimplify, nomatsimp, nodoit, noN, noO, noS, nogamma, noGamma, nozeta)'), {'msg': ['Uppercase E and I is on.<i> - "EI"</i>', 'Quick input mode is on.<i> - "quick"</i>', 'Python S escaping is off.<i> - "pyS"</i>', 'Post-evaluation simplify is off.<i> - "simplify"</i>', 'Matrix simplify is off.<i> - "matsimp"</i>', 'Expression doit is off.<i> - "doit"</i>', 'Function N is off.', 'Function O is off.', 'Function S is off.', 'Function gamma is off.', 'Function Gamma is off.', 'Function zeta is off.']})
		self.assertEqual (get ('env'), {'msg': ['Uppercase E and I is on.<i> - "EI"</i>', 'Quick input mode is on.<i> - "quick"</i>', 'Python S escaping is off.<i> - "pyS"</i>', 'Post-evaluation simplify is off.<i> - "simplify"</i>', 'Matrix simplify is off.<i> - "matsimp"</i>', 'Undefined function map to variable is on.<i> - "ufuncmap"</i>', 'Leading product rational is off.<i> - "prodrat"</i>', 'Expression doit is off.<i> - "doit"</i>', 'Strict LaTeX formatting is on.<i> - "strict"</i>', 'Function N is off.', 'Function O is off.', 'Function S is off.', 'Function beta is on.', 'Function gamma is off.', 'Function Gamma is off.', 'Function Lambda is on.', 'Function zeta is off.']})
		self.assertEqual (get ('envreset'), {'msg': ['Environment has been reset.<br><br>', 'Uppercase E and I is off.<i> - "EI"</i>', 'Quick input mode is off.<i> - "quick"</i>', 'Python S escaping is on.<i> - "pyS"</i>', 'Post-evaluation simplify is off.<i> - "simplify"</i>', 'Matrix simplify is on.<i> - "matsimp"</i>', 'Undefined function map to variable is on.<i> - "ufuncmap"</i>', 'Leading product rational is off.<i> - "prodrat"</i>', 'Expression doit is on.<i> - "doit"</i>', 'Strict LaTeX formatting is on.<i> - "strict"</i>', 'Function N is on.', 'Function O is on.', 'Function S is on.', 'Function beta is on.', 'Function gamma is on.', 'Function Gamma is on.', 'Function Lambda is on.', 'Function zeta is on.']})
		self.assertEqual (get ('env'), {'msg': ['Uppercase E and I is off.<i> - "EI"</i>', 'Quick input mode is off.<i> - "quick"</i>', 'Python S escaping is on.<i> - "pyS"</i>', 'Post-evaluation simplify is off.<i> - "simplify"</i>', 'Matrix simplify is on.<i> - "matsimp"</i>', 'Undefined function map to variable is on.<i> - "ufuncmap"</i>', 'Leading product rational is off.<i> - "prodrat"</i>', 'Expression doit is on.<i> - "doit"</i>', 'Strict LaTeX formatting is on.<i> - "strict"</i>', 'Function N is on.', 'Function O is on.', 'Function S is on.', 'Function beta is on.', 'Function gamma is on.', 'Function Gamma is on.', 'Function Lambda is on.', 'Function zeta is on.']})

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
		self.assertEqual (get ('env (quick)'), {'msg': ['Quick input mode is on.<i> - "quick"</i>']})
		self.assertEqual (get ('alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega'), {'math': ('(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '\\left(\\alpha, \\beta, \\gamma, \\delta, \\epsilon, \\zeta, \\eta, \\theta, \\iota, \\kappa, \\lambda, \\mu, \\nu, \\xi, \\pi, \\rho, \\sigma, \\tau, \\upsilon, \\phi, \\chi, \\psi, \\omega, \\Gamma, \\Delta, \\Theta, \\Lambda, \\Xi, \\Pi, \\Sigma, \\Upsilon, \\Phi, \\Psi, \\Omega \\right)')})
		self.assertEqual (get ('\\alpha, \\beta, \\gamma, \\delta, \\epsilon, \\zeta, \\eta, \\theta, \\iota, \\kappa, \\lambda, \\mu, \\nu, \\xi, \\pi, \\rho, \\sigma, \\tau, \\upsilon, \\phi, \\chi, \\psi, \\omega, \\Gamma, \\Delta, \\Theta, \\Lambda, \\Xi, \\Pi, \\Sigma, \\Upsilon, \\Phi, \\Psi, \\Omega'), {'math': ('(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '\\left(\\alpha, \\beta, \\gamma, \\delta, \\epsilon, \\zeta, \\eta, \\theta, \\iota, \\kappa, \\lambda, \\mu, \\nu, \\xi, \\pi, \\rho, \\sigma, \\tau, \\upsilon, \\phi, \\chi, \\psi, \\omega, \\Gamma, \\Delta, \\Theta, \\Lambda, \\Xi, \\Pi, \\Sigma, \\Upsilon, \\Phi, \\Psi, \\Omega \\right)')})
		self.assertEqual (get ('env (noquick)'), {'msg': ['Quick input mode is off.<i> - "quick"</i>']})
		self.assertEqual (get ('alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega'), {'math': ('(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '\\left(\\alpha, \\beta, \\gamma, \\delta, \\epsilon, \\zeta, \\eta, \\theta, \\iota, \\kappa, \\lambda, \\mu, \\nu, \\xi, \\pi, \\rho, \\sigma, \\tau, \\upsilon, \\phi, \\chi, \\psi, \\omega, \\Gamma, \\Delta, \\Theta, \\Lambda, \\Xi, \\Pi, \\Sigma, \\Upsilon, \\Phi, \\Psi, \\Omega \\right)')})
		self.assertEqual (get ('\\alpha, \\beta, \\gamma, \\delta, \\epsilon, \\zeta, \\eta, \\theta, \\iota, \\kappa, \\lambda, \\mu, \\nu, \\xi, \\pi, \\rho, \\sigma, \\tau, \\upsilon, \\phi, \\chi, \\psi, \\omega, \\Gamma, \\Delta, \\Theta, \\Lambda, \\Xi, \\Pi, \\Sigma, \\Upsilon, \\Phi, \\Psi, \\Omega'), {'math': ('(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '(alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, kappa, lambda, mu, nu, xi, pi, rho, sigma, tau, upsilon, phi, chi, psi, omega, Gamma, Delta, Theta, Lambda, Xi, Pi, Sigma, Upsilon, Phi, Psi, Omega)', '\\left(\\alpha, \\beta, \\gamma, \\delta, \\epsilon, \\zeta, \\eta, \\theta, \\iota, \\kappa, \\lambda, \\mu, \\nu, \\xi, \\pi, \\rho, \\sigma, \\tau, \\upsilon, \\phi, \\chi, \\psi, \\omega, \\Gamma, \\Delta, \\Theta, \\Lambda, \\Xi, \\Pi, \\Sigma, \\Upsilon, \\Phi, \\Psi, \\Omega \\right)')})

	def test_simplification (self):
		reset ()
		self.assertEqual (get ('env (nosimplify, nomatsimp)'), {'msg': ['Post-evaluation simplify is off.<i> - "simplify"</i>', 'Matrix simplify is off.<i> - "matsimp"</i>']})
		self.assertEqual (get ('\\[[x + 1, x - 1], [x - 1, x + 1]]**2'), {'math': ('\\[[(x + 1)**2 + (x - 1)**2, 2 {x + 1} {x - 1}], [2 {x + 1} {x - 1}, (x + 1)**2 + (x - 1)**2]]', 'Matrix([[(x + 1)**2 + (x - 1)**2, 2*(x + 1)*(x - 1)], [2*(x + 1)*(x - 1), (x + 1)**2 + (x - 1)**2]])', '\\begin{bmatrix} \\left(x + 1 \\right)^2 + \\left(x - 1 \\right)^2 & 2 \\left(x + 1 \\right) \\left(x - 1 \\right) \\\\ 2 \\left(x + 1 \\right) \\left(x - 1 \\right) & \\left(x + 1 \\right)^2 + \\left(x - 1 \\right)^2 \\end{bmatrix}')})
		self.assertEqual (get ('solve (x**3 = 5)'), {'math': ('[5**{1/3}, -{i sqrt(3) * 5**{1/3}} / 2 - 5**{1/3} / 2, {i sqrt(3) * 5**{1/3}} / 2 - 5**{1/3} / 2]', '[5**(S(1)/3), -(i*sqrt(3)*5**(S(1)/3)) / 2 - 5**(S(1)/3) / 2, (i*sqrt(3)*5**(S(1)/3)) / 2 - 5**(S(1)/3) / 2]', '\\left[5^\\frac{1}{3}, -\\frac{i \\sqrt{3} \\cdot 5^\\frac{1}{3}}{2} - \\frac{5^\\frac{1}{3}}{2}, \\frac{i \\sqrt{3} \\cdot 5^\\frac{1}{3}}{2} - \\frac{5^\\frac{1}{3}}{2} \\right]')})
		self.assertEqual (get ("env ('simplify', nomatsimp)"), {'msg': ['Post-evaluation simplify is on.<i> - "simplify"</i>', 'Matrix simplify is off.<i> - "matsimp"</i>']})
		self.assertEqual (get ('\\[[x + 1, x - 1], [x - 1, x + 1]]**2'), {'math': ('\\[[2x**2 + 2, 2x**2 - 2], [2x**2 - 2, 2x**2 + 2]]', 'Matrix([[2*x**2 + 2, 2*x**2 - 2], [2*x**2 - 2, 2*x**2 + 2]])', '\\begin{bmatrix} 2 x^2 + 2 & 2 x^2 - 2 \\\\ 2 x^2 - 2 & 2 x^2 + 2 \\end{bmatrix}')})
		self.assertEqual (get ('solve (x**3 = 5)'), {'math': ('[5**{1/3}, -5**{1/3} {i sqrt(3) + 1} / 2, 5**{1/3} {i sqrt(3) - 1} / 2]', '[5**(S(1)/3), -(5**(S(1)/3)*(i*sqrt(3) + 1)) / 2, (5**(S(1)/3)*(i*sqrt(3) - 1)) / 2]', '\\left[5^\\frac{1}{3}, -\\frac{5^\\frac{1}{3} \\left(i \\sqrt{3} + 1 \\right)}{2}, \\frac{5^\\frac{1}{3} \\left(i \\sqrt{3} - 1 \\right)}{2} \\right]')})
		self.assertEqual (get ('env (nosimplify, matsimp)'), {'msg': ['Post-evaluation simplify is off.<i> - "simplify"</i>', 'Matrix simplify is on.<i> - "matsimp"</i>']})
		self.assertEqual (get ('\\[[x + 1, x - 1], [x - 1, x + 1]]**2'), {'math': ('\\[[2x**2 + 2, 2x**2 - 2], [2x**2 - 2, 2x**2 + 2]]', 'Matrix([[2*x**2 + 2, 2*x**2 - 2], [2*x**2 - 2, 2*x**2 + 2]])', '\\begin{bmatrix} 2 x^2 + 2 & 2 x^2 - 2 \\\\ 2 x^2 - 2 & 2 x^2 + 2 \\end{bmatrix}')})
		self.assertEqual (get ("env ('simplify', matsimp)"), {'msg': ['Post-evaluation simplify is on.<i> - "simplify"</i>', 'Matrix simplify is on.<i> - "matsimp"</i>']})
		self.assertEqual (get ('\\[[x + 1, x - 1], [x - 1, x + 1]]**2'), {'math': ('\\[[2x**2 + 2, 2x**2 - 2], [2x**2 - 2, 2x**2 + 2]]', 'Matrix([[2*x**2 + 2, 2*x**2 - 2], [2*x**2 - 2, 2*x**2 + 2]])', '\\begin{bmatrix} 2 x^2 + 2 & 2 x^2 - 2 \\\\ 2 x^2 - 2 & 2 x^2 + 2 \\end{bmatrix}')})
		self.assertEqual (get ('solve (x**3 = 5)'), {'math': ('[5**{1/3}, -5**{1/3} {i sqrt(3) + 1} / 2, 5**{1/3} {i sqrt(3) - 1} / 2]', '[5**(S(1)/3), -(5**(S(1)/3)*(i*sqrt(3) + 1)) / 2, (5**(S(1)/3)*(i*sqrt(3) - 1)) / 2]', '\\left[5^\\frac{1}{3}, -\\frac{5^\\frac{1}{3} \\left(i \\sqrt{3} + 1 \\right)}{2}, \\frac{5^\\frac{1}{3} \\left(i \\sqrt{3} - 1 \\right)}{2} \\right]')})

	def test_calculate_eigen (self):
		reset ()
		self.assertEqual (get ('m = \\[[1, 2], [3, 4]]'), {'math': ('m = \\[[1, 2], [3, 4]]', 'm = Matrix([[1, 2], [3, 4]])', 'm = \\begin{bmatrix} 1 & 2 \\\\ 3 & 4 \\end{bmatrix}')})
		self.assertEqual (get ('l = m - lambda eye 2'), {'math': ('l = \\[[1 - lambda, 2], [3, 4 - lambda]]', 'l = Matrix([[1 - lambda, 2], [3, 4 - lambda]])', 'l = \\begin{bmatrix} 1 - \\lambda & 2 \\\\ 3 & 4 - \\lambda \\end{bmatrix}')})
		self.assertEqual (get ('l.det ()'), {'math': ('{1 - lambda} {4 - lambda} - 6', '(1 - lambda)*(4 - lambda) - 6', '\\left(1 - \\lambda \\right) \\left(4 - \\lambda \\right) - 6')})
		self.assertEqual (get ('solve _'), {'math': ('[5/2 - sqrt(33) / 2, sqrt(33) / 2 + 5/2]', '[S(5)/2 - sqrt(33) / 2, sqrt(33) / 2 + S(5)/2]', '\\left[\\frac{5}{2} - \\frac{\\sqrt{33}}{2}, \\frac{\\sqrt{33}}{2} + \\frac{5}{2} \\right]')})
		self.assertEqual (get ('a, b = _'), {'math': [('a = 5/2 - sqrt(33) / 2', 'a = S(5)/2 - sqrt(33) / 2', 'a = \\frac{5}{2} - \\frac{\\sqrt{33}}{2}'), ('b = sqrt(33) / 2 + 5/2', 'b = sqrt(33) / 2 + S(5)/2', 'b = \\frac{\\sqrt{33}}{2} + \\frac{5}{2}')]})
		self.assertEqual (get ('m.eigenvals ()'), {'math': ('{5/2 - sqrt(33) / 2: 1, sqrt(33) / 2 + 5/2: 1}', '{S(5)/2 - sqrt(33) / 2: 1, sqrt(33) / 2 + S(5)/2: 1}', '\\left\\{\\frac{5}{2} - \\frac{\\sqrt{33}}{2}{:} 1, \\frac{\\sqrt{33}}{2} + \\frac{5}{2}{:} 1 \\right\\}')})
		self.assertEqual (get ('Subs (l, lambda, a) \\[x, y]'), {'math': ('\\[2 y - 3 x / 2 + x sqrt(33) / 2, 3 x + 3 y / 2 + y sqrt(33) / 2]', 'Matrix([2*y - (3*x) / 2 + (x*sqrt(33)) / 2, 3*x + (3*y) / 2 + (y*sqrt(33)) / 2])', '\\begin{bmatrix} 2 y - \\frac{3 x}{2} + \\frac{x \\sqrt{33}}{2} \\\\ 3 x + \\frac{3 y}{2} + \\frac{y \\sqrt{33}}{2} \\end{bmatrix}')})
		self.assertEqual (get ('solve (_ [0], _ [1], x, y)'), {'math': ('[{x: -y/2 - y sqrt(33) / 6}]', '[{x: -y/2 - (y*sqrt(33)) / 6}]', '\\left[\\left\\{x{:} -\\frac{y}{2} - \\frac{y \\sqrt{33}}{6} \\right\\} \\right]')})
		self.assertEqual (get ('\\[_ [0] [x], y].subs (y, 1)'), {'math': ('\\[-sqrt(33) / 6 - 1/2, 1]', 'Matrix([-sqrt(33) / 6 - S(1)/2, 1])', '\\begin{bmatrix} -\\frac{\\sqrt{33}}{6} - \\frac{1}{2} \\\\ 1 \\end{bmatrix}')})
		self.assertEqual (get ('Subs (l, lambda, b) \\[x, y]'), {'math': ('\\[2 y - 3 x / 2 - x sqrt(33) / 2, 3 x + 3 y / 2 - y sqrt(33) / 2]', 'Matrix([2*y - (3*x) / 2 - (x*sqrt(33)) / 2, 3*x + (3*y) / 2 - (y*sqrt(33)) / 2])', '\\begin{bmatrix} 2 y - \\frac{3 x}{2} - \\frac{x \\sqrt{33}}{2} \\\\ 3 x + \\frac{3 y}{2} - \\frac{y \\sqrt{33}}{2} \\end{bmatrix}')})
		self.assertEqual (get ('solve (_ [0], _ [1], x, y)'), {'math': ('[{x: y sqrt(33) / 6 - y/2}]', '[{x: (y*sqrt(33)) / 6 - y/2}]', '\\left[\\left\\{x{:} \\frac{y \\sqrt{33}}{6} - \\frac{y}{2} \\right\\} \\right]')})
		self.assertEqual (get ('\\[_ [0] [x], y].subs (y, 1)'), {'math': ('\\[sqrt(33) / 6 - 1/2, 1]', 'Matrix([sqrt(33) / 6 - S(1)/2, 1])', '\\begin{bmatrix} \\frac{\\sqrt{33}}{6} - \\frac{1}{2} \\\\ 1 \\end{bmatrix}')})
		self.assertEqual (get ('m.eigenvects ()'), {'math': ('[(5/2 - sqrt(33) / 2, 1, [\\[{-2} / {sqrt(33) / 2 - 3/2}, 1]]), (sqrt(33) / 2 + 5/2, 1, [\\[{-2} / {-sqrt(33) / 2 - 3/2}, 1]])]', '[(S(5)/2 - sqrt(33) / 2, 1, [Matrix([(-2) / (sqrt(33) / 2 - S(3)/2), 1])]), (sqrt(33) / 2 + S(5)/2, 1, [Matrix([(-2) / (-sqrt(33) / 2 - S(3)/2), 1])])]', '\\left[\\left(\\frac{5}{2} - \\frac{\\sqrt{33}}{2}, 1, \\left[\\begin{bmatrix} \\frac{-2}{\\frac{\\sqrt{33}}{2} - \\frac{3}{2}} \\\\ 1 \\end{bmatrix} \\right] \\right), \\left(\\frac{\\sqrt{33}}{2} + \\frac{5}{2}, 1, \\left[\\begin{bmatrix} \\frac{-2}{-\\frac{\\sqrt{33}}{2} - \\frac{3}{2}} \\\\ 1 \\end{bmatrix} \\right] \\right) \\right]')})
		self.assertEqual (get ('simplify _'), {'math': ('[(5/2 - sqrt(33) / 2, 1, [\\[-sqrt(33) / 6 - 1/2, 1]]), (sqrt(33) / 2 + 5/2, 1, [\\[sqrt(33) / 6 - 1/2, 1]])]', '[(S(5)/2 - sqrt(33) / 2, 1, [Matrix([-sqrt(33) / 6 - S(1)/2, 1])]), (sqrt(33) / 2 + S(5)/2, 1, [Matrix([sqrt(33) / 6 - S(1)/2, 1])])]', '\\left[\\left(\\frac{5}{2} - \\frac{\\sqrt{33}}{2}, 1, \\left[\\begin{bmatrix} -\\frac{\\sqrt{33}}{6} - \\frac{1}{2} \\\\ 1 \\end{bmatrix} \\right] \\right), \\left(\\frac{\\sqrt{33}}{2} + \\frac{5}{2}, 1, \\left[\\begin{bmatrix} \\frac{\\sqrt{33}}{6} - \\frac{1}{2} \\\\ 1 \\end{bmatrix} \\right] \\right) \\right]')})

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
		self.assertEqual (get ('y = ?(x, real = True)'), {'math': ('y = ?y(x, real = True)', "y = Function('y', real = True)(x)", 'y = ?y\\left(x, real = True \\right)')})
		self.assertEqual (get ('z = z(x)'), {'math': ('z = z(x)', "z = Function('z')(x)", 'z = z\\left(x \\right)')})
		self.assertEqual (get ('g (x) = x**3'), {'math': ('g(x) = x**3', 'g = Lambda(x, x**3)', 'g\\left(x \\right) = x^3')})
		self.assertEqual (get ('vars'), {'math': [('f(x) = x**2', 'f = Lambda(x, x**2)', 'f\\left(x \\right) = x^2'), ('g(x) = x**3', 'g = Lambda(x, x**3)', 'g\\left(x \\right) = x^3'), ('y = ?y(x, real = True)', "y = Function('y', real = True)(x)", 'y = ?y\\left(x, real = True \\right)'), ('z = z(x)', "z = Function('z')(x)", 'z = z\\left(x \\right)'), ('x = 1', 'x = 1', 'x = 1')]})
		self.assertEqual (get ('z = y'), {'math': ('z = ?y(x, real = True)', "z = Function('y', real = True)(x)", 'z = ?y\\left(x, real = True \\right)')})
		self.assertEqual (get ('vars'), {'math': [('f(x) = x**2', 'f = Lambda(x, x**2)', 'f\\left(x \\right) = x^2'), ('g(x) = x**3', 'g = Lambda(x, x**3)', 'g\\left(x \\right) = x^3'), ('y = ?y(x, real = True)', "y = Function('y', real = True)(x)", 'y = ?y\\left(x, real = True \\right)'), ('z = ?y(x, real = True)', "z = Function('y', real = True)(x)", 'z = ?y\\left(x, real = True \\right)'), ('x = 1', 'x = 1', 'x = 1')]})
		self.assertEqual (get ('del y'), {'msg': ["Undefined function 'y' deleted."]})
		self.assertEqual (get ('vars'), {'math': [('f(x) = x**2', 'f = Lambda(x, x**2)', 'f\\left(x \\right) = x^2'), ('g(x) = x**3', 'g = Lambda(x, x**3)', 'g\\left(x \\right) = x^3'), ('z = y(x, real = True)', "z = Function('y', real = True)(x)", 'z = y\\left(x, real = True \\right)'), ('x = 1', 'x = 1', 'x = 1')]})
		self.assertEqual (get ('delall'), {'msg': ['All variables deleted.']})
		self.assertEqual (get ('vars'), {'msg': ['No variables defined.']})

	def test_ufuncs (self):
		reset ()
		self.assertEqual (get ('f = ? ()'), {'math': ('f = f()', "f = Function('f')", 'f = f\\left( \\right)')})
		self.assertEqual (get ('f (x)'), {'math': ('f(x)', "Function('f')(x)", 'f\\left(x \\right)')})
		self.assertEqual (get ('f (x) (0)'), {'math': ('0', '0', '0')})
		self.assertEqual (get ('f (0)'), {'math': ('f(0)', "Function('f')(0)", 'f\\left(0 \\right)')})
		self.assertEqual (get ('f = ?g ()'), {'math': ('f = g()', "f = Function('g')", 'f = g\\left( \\right)')})
		self.assertEqual (get ('f (x)'), {'math': ('g(x)', "Function('g')(x)", 'g\\left(x \\right)')})
		self.assertEqual (get ('f (x) (0)'), {'math': ('0', '0', '0')})
		self.assertEqual (get ('f (0)'), {'math': ('g(0)', "Function('g')(0)", 'g\\left(0 \\right)')})
		self.assertEqual (get ('f = g ()'), {'math': ('f = g()', "f = Function('g')", 'f = g\\left( \\right)')})
		self.assertEqual (get ('f (x)'), {'math': ('g(x)', "Function('g')(x)", 'g\\left(x \\right)')})
		self.assertEqual (get ('f (x) (0)'), {'math': ('0', '0', '0')})
		self.assertEqual (get ('f (0)'), {'math': ('g(0)', "Function('g')(0)", 'g\\left(0 \\right)')})
		self.assertEqual (get ("f' (x)"), {'err': 'ValueError: Since there are no variables in the expression, the variable(s) of differentiation must be supplied to differentiate g()'})
		self.assertEqual (get ('d/dx (f) (x)'), {'math': ('0', '0', '0')})
		self.assertEqual (get ("f (x)' (0)"), {'math': ("g(x)'(0)", "Subs(diff(Function('g')(x)), x, 0)", "g\\left(x \\right)'\\left(0 \\right)")})
		self.assertEqual (get ('d/dx (f (x)) (0)'), {'math': ("g(x)'(0)", "Subs(diff(Function('g')(x)), x, 0)", "g\\left(x \\right)'\\left(0 \\right)")})
		self.assertEqual (get ('f = ?f (x)'), {'math': ('f = f(x)', "f = Function('f')(x)", 'f = f\\left(x \\right)')})
		self.assertEqual (get ('f (x)'), {'math': ('f(x)', "Function('f')(x)", 'f\\left(x \\right)')})
		self.assertEqual (get ('f (x) (0)'), {'math': ('0', '0', '0')})
		self.assertEqual (get ('f (0)'), {'math': ('f(0)', "Function('f')(0)", 'f\\left(0 \\right)')})
		self.assertEqual (get ('f = ?g (x)'), {'math': ('f = g(x)', "f = Function('g')(x)", 'f = g\\left(x \\right)')})
		self.assertEqual (get ('f (x)'), {'math': ('g(x)', "Function('g')(x)", 'g\\left(x \\right)')})
		self.assertEqual (get ('f (x) (0)'), {'math': ('0', '0', '0')})
		self.assertEqual (get ('f (0)'), {'math': ('g(0)', "Function('g')(0)", 'g\\left(0 \\right)')})
		self.assertEqual (get ('f = g (x)'), {'math': ('f = g(x)', "f = Function('g')(x)", 'f = g\\left(x \\right)')})
		self.assertEqual (get ('f (x)'), {'math': ('g(x)', "Function('g')(x)", 'g\\left(x \\right)')})
		self.assertEqual (get ('f (x) (0)'), {'math': ('0', '0', '0')})
		self.assertEqual (get ('f (0)'), {'math': ('g(0)', "Function('g')(0)", 'g\\left(0 \\right)')})
		self.assertEqual (get ("f' (x)"), {'math': ("f'", 'diff(f)', "f'")})
		self.assertEqual (get ('d/dx (f) (x)'), {'math': ("f'", 'diff(f)', "f'")})
		self.assertEqual (get ('d/dy (f) (x)'), {'math': ('0', '0', '0')})
		self.assertEqual (get ("f (x)' (0)"), {'math': ("f'(0)", 'Subs(diff(f), x, 0)', "f'\\left(0 \\right)")})
		self.assertEqual (get ('d/dx (f (x)) (0)'), {'math': ("f'(0)", 'Subs(diff(f), x, 0)', "f'\\left(0 \\right)")})
		self.assertEqual (get ('d/dy (f (x)) (0)'), {'math': ('0', '0', '0')})
		self.assertEqual (get ('u = u (x, t)'), {'math': ('u = u(x, t)', "u = Function('u')(x, t)", 'u = u\\left(x, t \\right)')})
		self.assertEqual (get ('du/dx (x, t)'), {'math': ('du / dx', 'Derivative(u, x)', '\\frac{\\partial u}{\\partial x}')})
		self.assertEqual (get ('du/dx (1, t)'), {'math': ('du / dx(1, t)', 'Subs(Derivative(u, x), x, 1)', '\\frac{\\partial u}{\\partial x}\\left(1, t \\right)')})
		self.assertEqual (get ('du/dx (1, 0)'), {'math': ('du / dx(1, 0)', 'Subs(Derivative(u, x), (x, t), (1, 0))', '\\frac{\\partial u}{\\partial x}\\left(1, 0 \\right)')})
		self.assertEqual (get ('d**2u / dx dt (1, 0)'), {'math': ('d**2 u / dt dx(1, 0)', 'Subs(Derivative(u, t, x), (x, t), (1, 0))', '\\frac{\\partial^2 u}{\\partial t \\partial x}\\left(1, 0 \\right)')})
		self.assertEqual (get ('d/dx u (1, 0)'), {'math': ('0', '0', '0')})
		self.assertEqual (get ('d/dx (u) (1, 0)'), {'math': ('du / dx(1, 0)', 'Subs(Derivative(u, x), (x, t), (1, 0))', '\\frac{\\partial u}{\\partial x}\\left(1, 0 \\right)')})
		self.assertEqual (get ('d**2 / dx dt u (1, 0)'), {'math': ('0', '0', '0')})
		self.assertEqual (get ('d**2 / dx dt (u) (1, 0)'), {'math': ('d**2 u / dt dx(1, 0)', 'Subs(Derivative(u, t, x), (x, t), (1, 0))', '\\frac{\\partial^2 u}{\\partial t \\partial x}\\left(1, 0 \\right)')})
		self.assertEqual (get ('f () = x**2'), {'math': ('f() = x**2', 'f = Lambda((), x**2)', 'f\\left( \\right) = x^2')})
		self.assertEqual (get ('g (2) = x**2'), {'err': 'server.RealityRedefinitionError: cannot assign to a function containing non-variable parameters'})
		self.assertEqual (get ('h (x) = x**2'), {'math': ('h(x) = x**2', 'h = Lambda(x, x**2)', 'h\\left(x \\right) = x^2')})
		self.assertEqual (get ('delall'), {'msg': ['All variables deleted.']})
		self.assertEqual (get ('?f () = x**2'), {'math': ('?f() = x**2', "Eq(Function('f'), x**2)", '?f\\left( \\right) = x^2')})
		self.assertEqual (get ('?g (2) = x**2'), {'math': ('?g(2) = x**2', "Eq(Function('g')(2), x**2)", '?g\\left(2 \\right) = x^2')})
		self.assertEqual (get ('?h (x) = x**2'), {'math': ('?h(x) = x**2', "Eq(Function('h')(x), x**2)", '?h\\left(x \\right) = x^2')})
		self.assertEqual (get ('f (x) = x'), {'math': ('f(x) = x', 'f = Lambda(x, x)', 'f\\left(x \\right) = x')})
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
		self.assertEqual (get ('f = ?f (x)'), {'math': ('f = f(x)', "f = Function('f')(x)", 'f = f\\left(x \\right)')})
		self.assertEqual (get ('f'), {'math': ('f(x)', "Function('f')(x)", 'f\\left(x \\right)')})
		self.assertEqual (get ('1 + f'), {'math': ('f + 1', 'f + 1', 'f + 1')})
		self.assertEqual (get ('g = f'), {'math': ('g = f(x)', "g = Function('f')(x)", 'g = f\\left(x \\right)')})
		self.assertEqual (get ('g'), {'math': ('f(x)', "Function('f')(x)", 'f\\left(x \\right)')})
		self.assertEqual (get ('1 + g'), {'math': ('f + 1', 'f + 1', 'f + 1')})
		self.assertEqual (get ('del f'), {'msg': ["Undefined function 'f' deleted."]})
		self.assertEqual (get ('g'), {'math': ('f(x)', "Function('f')(x)", 'f\\left(x \\right)')})
		self.assertEqual (get ('1 + g'), {'math': ('g + 1', 'g + 1', 'g + 1')})
		self.assertEqual (get ('delall'), {'msg': ['All variables deleted.']})
		self.assertEqual (get ('f (x) = x**2'), {'math': ('f(x) = x**2', 'f = Lambda(x, x**2)', 'f\\left(x \\right) = x^2')})
		self.assertEqual (get ('y = 1 + (?f (x) = 2)'), {'math': ('y = (?f(x) = 2) + 1', "y = Eq(Function('f')(x), 2) + 1", 'y = \\left(?f\\left(x \\right) = 2 \\right) + 1')})
		self.assertEqual (get ('g (x) = ?f (x)'), {'math': ('g(x) = ?f(x)', "g = Lambda(x, Function('f')(x))", 'g\\left(x \\right) = ?f\\left(x \\right)')})
		self.assertEqual (get ('g (2)'), {'math': ('4', '4', '4')})
		self.assertEqual (get ('del (f, g)'), {'msg': ["Lambda function 'f' deleted.", "Lambda function 'g' deleted."]})
		self.assertEqual (get ('f = f (x, y)'), {'math': ('f = f(x, y)', "f = Function('f')(x, y)", 'f = f\\left(x, y \\right)')})
		self.assertEqual (get ('f = 1 + f (x, y)'), {'math': ('f = ?f(x, y) + 1', "f = Function('f')(x, y) + 1", 'f = ?f\\left(x, y \\right) + 1')})
		self.assertEqual (get ('del f'), {'msg': ["Variable 'f' deleted."]})
		self.assertEqual (get ('f (x, y) = ?g (x + y)'), {'math': ('f(x, y) = ?g(x + y)', "f = Lambda((x, y), Function('g')(x + y))", 'f\\left(x, y \\right) = ?g\\left(x + y \\right)')})
		self.assertEqual (get ('f (x, y)'), {'math': ('?g(x + (?f(x) = 2) + 1)', "Function('g')(x + Eq(Function('f')(x), 2) + 1)", '?g\\left(x + \\left(?f\\left(x \\right) = 2 \\right) + 1 \\right)')})
		self.assertEqual (get ('f (1, y)'), {'err': 'TypeError: cannot determine truth value of Relational'})
		self.assertEqual (get ('f (x, 2)'), {'math': ('?g(x + 2)', "Function('g')(x + 2)", '?g\\left(x + 2 \\right)')})
		self.assertEqual (get ('f (a, b)'), {'math': ('?g(a + b)', "Function('g')(a + b)", '?g\\left(a + b \\right)')})

	def test_intro_examples (self):
		reset ()
		self.assertEqual (get ('cos -pi'), {'math': ('-1', '-1', '-1')})
		self.assertEqual (get ('N cos**-1 -\\log_2 sqrt[4] 16'), {'math': ('3.14159265358979', '3.14159265358979', '3.14159265358979')})
		self.assertEqual (get ('factor (x^3 + 3y x^2 + 3x y^2 + y^3)'), {'math': ('(x + y)**3', '(x + y)**3', '\\left(x + y \\right)^3')})
		self.assertEqual (get ("Limit (\\frac1x, x, 0, dir='-')"), {'math': ('-oo', '-oo', '-\\infty')})
		self.assertEqual (get ('\\sum_{n=0}**oo x**n / n!'), {'math': ('e**x', 'e**x', 'e^x')})
		self.assertEqual (get ('d**3 / dx dy^2 x^3 y^3'), {'math': ('18 y x**2', '18*y*x**2', '18 y\\ x^2')})
		self.assertEqual (get ('Integral (e^{-x^2}, (x, 0, \\infty))'), {'math': ('sqrt(pi) / 2', 'sqrt(pi) / 2', '\\frac{\\sqrt{\\pi}}{2}')})
		self.assertEqual (get ('\\int^\\pi \\int^{2pi} \\int^1 rho**2 sin\\phi drho dtheta dphi'), {'math': ('4 pi / 3', '(4*pi) / 3', '\\frac{4 \\pi}{3}')})
		self.assertEqual (get ('\\[[1, 2], [3, 4]]**-1'), {'math': ('\\[[-2, 1], [3/2, -1/2]]', 'Matrix([[-2, 1], [S(3)/2, -S(1)/2]])', '\\begin{bmatrix} -2 & 1 \\\\ \\frac{3}{2} & -\\frac{1}{2} \\end{bmatrix}')})
		self.assertEqual (get ('Matrix (4, 4, lambda r, c: c + r if c &gt; r else 0)'), {})
		self.assertEqual (get ('f (x, y) = sqrt (x**2 + y**2)'), {'math': ('f(x, y) = sqrt(x**2 + y**2)', 'f = Lambda((x, y), sqrt(x**2 + y**2))', 'f\\left(x, y \\right) = \\sqrt{x^2 + y^2}')})
		self.assertEqual (get ('f (3, 4)'), {'math': ('5', '5', '5')})
		self.assertEqual (get ('solve (x**2 + y = 4, x)'), {'math': ('[-sqrt(4 - y), sqrt(4 - y)]', '[-sqrt(4 - y), sqrt(4 - y)]', '\\left[-\\sqrt{4 - y}, \\sqrt{4 - y} \\right]')})
		self.assertEqual (get ("dsolve (y(x)'' + 9y(x))"), {'math': ('y(x) = C1 sin(3 x) + C2 cos(3 x)', 'y = Lambda(x, C1*sin(3*x) + C2*cos(3*x))', 'y\\left(x \\right) = C_{1}\\ \\sin{\\left(3 x \\right)} + C_{2}\\ \\cos{\\left(3 x \\right)}')})
		self.assertEqual (get ("y = y(t); dsolve (y'' - 4y' - 12y = 3e**{5t}); del y"), {'math': ('y = y(t)', "y = Function('y')(t)", 'y = y\\left(t \\right)')})
		self.assertEqual (get ('pdsolve (x * d/dx u (x, y) - y * d/dy u (x, y) + y**2u (x, y) - y**2)'), {'math': ('u(x, y) = ?F(x y) e**{y**2 / 2} + 1', "u = Lambda((x, y), Function('F')(x*y)*e**(y**2 / 2) + 1)", 'u\\left(x, y \\right) = ?F\\left(x\\ y \\right) e^\\frac{y^2}{2} + 1')})
		self.assertEqual (get ('simplify (not (not a and not b) and not (not a or not c))'), {'math': ('a and c', 'And(a, c)', 'a \\wedge c')})
		self.assertEqual (get ('(({1, 2, 3} && {2, 3, 4}) ^^ {3, 4, 5}) - \\{4} || {7,}'), {'math': ('{2, 5, 7}', 'FiniteSet(2, 5, 7)', '\\left\\{2, 5, 7 \\right\\}')})

	def test_LSDI (self):
		reset ()
		self.assertEqual (get ('delall'), {'msg': ['All variables deleted.']})
		self.assertEqual (get ('\\lim_{h\\to0} {(x + h)**2 - x**2} / h'), {'math': ('2 x', '2*x', '2 x')})
		self.assertEqual (get ('Limit ((1 + 1/x)**x, x, \\infty)'), {'math': ('e', 'e', 'e')})
		self.assertEqual (get ('{(1 - 1/x)**x}.limit (x, \\infty)'), {'math': ('e**-1', 'e**-1', 'e^{-1}')})
		self.assertEqual (get ('limit (sin x / x, x, 0)'), {'math': ('1', '1', '1')})
		self.assertEqual (get ('\\sum_{n=0}^\\infty (-1)**n x**{2n} / (2n)!'), {'math': ('cos(x)', 'cos(x)', '\\cos{\\left(x \\right)}')})
		self.assertEqual (get ('Sum ((-1)**n x**{2n + 1} / (2n + 1)!, (n, 0, oo))'), {'math': ('sin(x)', 'sin(x)', '\\sin{\\left(x \\right)}')})
		self.assertEqual (get ('summation ((-3)^n / n 7^{n+1} * (x - 5)^n, (n, 1, oo))'), {'math': ('{7 {15/7 - 3 x / 7} ln(3 x / 7 - 8/7) / 3 {x - 5} if 8/3 < x <= 22/3 else {7 {15/7 - 3 x / 7} ln(3 x / 7 - 8/7) / 3 {x - 5} if 8/3 < x <= 22/3 else \\sum_{n = 1}^{oo} {(-3)**n * 7**-n{(x - 5)**n}} / n}} / 7', 'Piecewise(((7*(S(15)/7 - (3*x) / 7)*ln((3*x) / 7 - S(8)/7)) / (3*(x - 5)), And(Lt(S(8)/3, x), Le(x, S(22)/3))), (Piecewise(((7*(S(15)/7 - (3*x) / 7)*ln((3*x) / 7 - S(8)/7)) / (3*(x - 5)), And(Lt(S(8)/3, x), Le(x, S(22)/3))), (Sum(((-3)**n*7**-n*(x - 5)**n) / n, (n, 1, oo)), True)), True)) / 7', '\\frac{\\begin{cases} \\frac{7 \\left(\\frac{15}{7} - \\frac{3 x}{7} \\right) \\ln{\\left(\\frac{3 x}{7} - \\frac{8}{7} \\right)}}{3 \\left(x - 5 \\right)} & \\text{for}\\: \\frac{8}{3} < x \\le \\frac{22}{3} \\\\ \\begin{cases} \\frac{7 \\left(\\frac{15}{7} - \\frac{3 x}{7} \\right) \\ln{\\left(\\frac{3 x}{7} - \\frac{8}{7} \\right)}}{3 \\left(x - 5 \\right)} & \\text{for}\\: \\frac{8}{3} < x \\le \\frac{22}{3} \\\\ \\sum_{n = 1}^\\infty \\frac{\\left(-3 \\right)^n \\cdot {7^{-n}}\\left(x - 5 \\right)^n}{n} & \\text{otherwise} \\end{cases} & \\text{otherwise} \\end{cases}}{7}')})
		self.assertEqual (get ('d/dx ln x'), {'math': ('1/x', '1/x', '\\frac{1}{x}')})
		self.assertEqual (get ('Derivative (x**3y**2, x, y)'), {'math': ('6 y x**2', '6*y*x**2', '6 y\\ x^2')})
		self.assertEqual (get ('diff (sin x + cos x, x, 2)'), {'math': ('-cos(x) - sin(x)', '-cos(x) - sin(x)', '-\\cos{\\left(x \\right)} - \\sin{\\left(x \\right)}')})
		self.assertEqual (get ('{x**2sin**2y}.diff (x, y)'), {'math': ('4 x cos(y) sin(y)', '4*x*cos(y)*sin(y)', '4 x \\cos{\\left(y \\right)} \\sin{\\left(y \\right)}')})
		self.assertEqual (get ('d**3/dx**2dy x**3y**2'), {'math': ('12 x y', '12*x*y', '12 x\\ y')})
		self.assertEqual (get ("sin (x)'"), {'math': ('cos(x)', 'cos(x)', '\\cos{\\left(x \\right)}')})
		self.assertEqual (get ("(e**{2x})''"), {'math': ('4 * e**{2 x}', '4*e**(2*x)', '4 e^{2 x}')})
		self.assertEqual (get ('d/dx ln (y(x))'), {'math': ("y(x)' / y(x)", "diff(Function('y')(x)) / Function('y')(x)", "\\frac{y\\left(x \\right)'}{y\\left(x \\right)}")})
		self.assertEqual (get ('\\int x**a dx'), {'math': ('x**{a + 1} / {a + 1} if a != -1 else ln(x)', 'Piecewise((x**(a + 1) / (a + 1), Ne(a, -1)), (ln(x), True))', '\\begin{cases} \\frac{x^{a + 1}}{a + 1} & \\text{for}\\: a \\ne -1 \\\\ \\ln{\\left(x \\right)} & \\text{otherwise} \\end{cases}')})
		self.assertEqual (get ('Integral (a**x, x)'), {'math': ('a**x / ln(a) if ln(a) != 0 else x', 'Piecewise((a**x / ln(a), Ne(ln(a), 0)), (x, True))', '\\begin{cases} \\frac{a^x}{\\ln{\\left(a \\right)}} & \\text{for}\\: \\ln{\\left(a \\right)} \\ne 0 \\\\ x & \\text{otherwise} \\end{cases}')})
		self.assertEqual (get ('{x**3y**2}.integrate (x, y)'), {'math': ('x**4 y**3 / 12', '(x**4*y**3) / 12', '\\frac{x^4 y^3}{12}')})
		self.assertEqual (get ('\\int_0**oo e**{-st} dt'), {'math': ('oo sign(e**-st)', 'oo*sign(e**-st)', '\\infty \\operatorname{sign}{\\left(e^{-st} \\right)}')})
		self.assertEqual (get ('Integral (r, (r, 0, 1), (theta, 0, 2pi))'), {'math': ('pi', 'pi', '\\pi')})
		self.assertEqual (get ('integrate (sin x / x, (x, -oo, oo))'), {'math': ('pi', 'pi', '\\pi')})

	def test_solve (self):
		reset ()
		self.assertEqual (get ('delall'), {'msg': ['All variables deleted.']})
		self.assertEqual (get ('solve (x**2 = 4)'), {'math': ('[-2, 2]', '[-2, 2]', '\\left[-2, 2 \\right]')})
		self.assertEqual (get ('solve (x**2 - 4)'), {'math': ('[-2, 2]', '[-2, 2]', '\\left[-2, 2 \\right]')})
		self.assertEqual (get ('solve (|x| >= x**2)'), {'math': ('-1 <= x <= 1', 'And(Le(-1, x), Le(x, 1))', '-1 \\le x \\le 1')})
		self.assertEqual (get ('solve (x**2 + 2 x - 1 > 7)'), {'math': ('-oo < x < -4 or 2 < x < oo', 'Or(And(Lt(-oo, x), Lt(x, -4)), And(Lt(2, x), Lt(x, oo)))', '-\\infty < x < -4 \\vee 2 < x < \\infty')})
		self.assertEqual (get ('solve (y = x**2 + 2 x - 1, x)'), {'math': ('[-sqrt(y + 2) - 1, sqrt(y + 2) - 1]', '[-sqrt(y + 2) - 1, sqrt(y + 2) - 1]', '\\left[-\\sqrt{y + 2} - 1, \\sqrt{y + 2} - 1 \\right]')})
		self.assertEqual (get ('solve (x + (e**x)**2, e**x)'), {'math': ('[-sqrt(-x), sqrt(-x)]', '[-sqrt(-x), sqrt(-x)]', '\\left[-\\sqrt{-x}, \\sqrt{-x} \\right]')})
		self.assertEqual (get ('solve (x + e**x, x)'), {'math': ('[-LambertW(1)]', '[-LambertW(1)]', '\\left[-\\operatorname{LambertW}{\\left(1 \\right)} \\right]')})
		self.assertEqual (get ('solve (x + e**x, x, implicit = True)'), {'math': ('[-e**x]', '[-e**x]', '\\left[-e^x \\right]')})
		self.assertEqual (get ('solve ((x + 2y = 5, y - 2x = 0))'), {'math': ('{x: 1, y: 2}', '{x: 1, y: 2}', '\\left\\{x{:} 1, y{:} 2 \\right\\}')})
		self.assertEqual (get ('solve ((a + b)x - b + 2, a, b)'), {'math': ('{a: -2, b: 2}', '{a: -2, b: 2}', '\\left\\{a{:} -2, b{:} 2 \\right\\}')})
		self.assertEqual (get ('solve ((a + b)x - b**2 + 2, a, b)'), {'math': ('[(-sqrt(2), sqrt(2)), (sqrt(2), -sqrt(2))]', '[(-sqrt(2), sqrt(2)), (sqrt(2), -sqrt(2))]', '\\left[\\left(-\\sqrt{2}, \\sqrt{2} \\right), \\left(\\sqrt{2}, -\\sqrt{2} \\right) \\right]')})
		self.assertEqual (get ('a, b = x**2 + y -2, y**2 - 4'), {'math': [('a = y + x**2 - 2', 'a = y + x**2 - 2', 'a = y + x^2 - 2'), ('b = y**2 - 4', 'b = y**2 - 4', 'b = y^2 - 4')]})
		self.assertEqual (get ('solve ([a, b])'), {'math': ('[{x: -2, y: -2}, {x: 0, y: 2}, {x: 0, y: 2}, {x: 2, y: -2}]', '[{x: -2, y: -2}, {x: 0, y: 2}, {x: 0, y: 2}, {x: 2, y: -2}]', '\\left[\\left\\{x{:} -2, y{:} -2 \\right\\}, \\left\\{x{:} 0, y{:} 2 \\right\\}, \\left\\{x{:} 0, y{:} 2 \\right\\}, \\left\\{x{:} 2, y{:} -2 \\right\\} \\right]')})
		self.assertEqual (get ('s = _'), {'math': ('s = [{x: -2, y: -2}, {x: 0, y: 2}, {x: 0, y: 2}, {x: 2, y: -2}]', 's = [{x: -2, y: -2}, {x: 0, y: 2}, {x: 0, y: 2}, {x: 2, y: -2}]', 's = \\left[\\left\\{x{:} -2, y{:} -2 \\right\\}, \\left\\{x{:} 0, y{:} 2 \\right\\}, \\left\\{x{:} 0, y{:} 2 \\right\\}, \\left\\{x{:} 2, y{:} -2 \\right\\} \\right]')})
		self.assertEqual (get ('a.subs (s [0]), b.subs (s [0])'), {'math': ('(0, 0)', '(0, 0)', '\\left(0, 0 \\right)')})
		self.assertEqual (get ('a.subs (s [1]), b.subs (s [1])'), {'math': ('(0, 0)', '(0, 0)', '\\left(0, 0 \\right)')})
		self.assertEqual (get ('a.subs (s [2]), b.subs (s [2])'), {'math': ('(0, 0)', '(0, 0)', '\\left(0, 0 \\right)')})
		self.assertEqual (get ('a.subs (s [3]), b.subs (s [3])'), {'math': ('(0, 0)', '(0, 0)', '\\left(0, 0 \\right)')})
		self.assertEqual (get ('w = {x: 1, y: 2}'), {'math': ('w = {x: 1, y: 2}', 'w = {x: 1, y: 2}', 'w = \\left\\{x{:} 1, y{:} 2 \\right\\}')})
		self.assertEqual (get ('a.subs (w), b.subs (w)'), {'math': ('(1, 0)', '(1, 0)', '\\left(1, 0 \\right)')})

	def test_ode (self):
		reset ()
		self.assertEqual (get ('delall'), {'msg': ['All variables deleted.']})
		self.assertEqual (get ('dsolve (d**2/dx**2 ?(x) + 9?(x))'), {'math': ('?(x) = C1 sin(3 x) + C2 cos(3 x)', "Eq(Function('')(x), C1*sin(3*x) + C2*cos(3*x))", '?\\left(x \\right) = C_{1}\\ \\sin{\\left(3 x \\right)} + C_{2}\\ \\cos{\\left(3 x \\right)}')})
		self.assertEqual (get ("dsolve (?(x)'' + 9?(x))"), {'math': ('?(x) = C1 sin(3 x) + C2 cos(3 x)', "Eq(Function('')(x), C1*sin(3*x) + C2*cos(3*x))", '?\\left(x \\right) = C_{1}\\ \\sin{\\left(3 x \\right)} + C_{2}\\ \\cos{\\left(3 x \\right)}')})
		self.assertEqual (get ("dsolve (y(x)'' + 9y(x))"), {'math': ('y(x) = C1 sin(3 x) + C2 cos(3 x)', 'y = Lambda(x, C1*sin(3*x) + C2*cos(3*x))', 'y\\left(x \\right) = C_{1}\\ \\sin{\\left(3 x \\right)} + C_{2}\\ \\cos{\\left(3 x \\right)}')})
		self.assertEqual (get ('y = y(x)'), {'math': ('y = y(x)', "y = Function('y')(x)", 'y = y\\left(x \\right)')})
		self.assertEqual (get ("dsolve (y'' + 9y)"), {'math': ('y(x) = C1 sin(3 x) + C2 cos(3 x)', 'y = Lambda(x, C1*sin(3*x) + C2*cos(3*x))', 'y\\left(x \\right) = C_{1}\\ \\sin{\\left(3 x \\right)} + C_{2}\\ \\cos{\\left(3 x \\right)}')})
		self.assertEqual (get ("dsolve (sin x cos y + cos x sin y y')"), {'math': ('[y(x) = 2 pi - acos(C1 / cos(x)), y(x) = acos(C1 / cos(x))]', "[Eq(Function('y')(x), 2*pi - acos(C1 / cos(x))), Eq(Function('y')(x), acos(C1 / cos(x)))]", '\\left[y\\left(x \\right) = 2 \\pi - \\cos^{-1}{\\left(\\frac{C_{1}}{\\cos{\\left(x \\right)}} \\right)}, y\\left(x \\right) = \\cos^{-1}{\\left(\\frac{C_{1}}{\\cos{\\left(x \\right)}} \\right)} \\right]')})
		self.assertEqual (get ("dsolve (y' + 4/x * y = x**3 y**2)"), {'math': ('y(x) = 1 / x**4 {C1 - ln(x)}', 'y = Lambda(x, 1 / (x**4*(C1 - ln(x))))', 'y\\left(x \\right) = \\frac{1}{x^4 \\left(C_{1} - \\ln{\\left(x \\right)} \\right)}')})
		self.assertEqual (get ("dsolve (y' + 4/x * y = x**3 y**2, ics = {y(2): -1})"), {'math': ('y(x) = 1 / x**4 {-ln(x) + ln(2) - 1/16}', 'y = Lambda(x, 1 / (x**4*(-ln(x) + ln(2) - S(1)/16)))', 'y\\left(x \\right) = \\frac{1}{x^4 \\left(-\\ln{\\left(x \\right)} + \\ln{\\left(2 \\right)} - \\frac{1}{16} \\right)}')})
		self.assertEqual (get ("dsolve (cos y - y' * (x sin y - y**2))"), {'math': ('y**3 / 3 + x cos(y) = C1', 'Eq(y**3 / 3 + x*cos(y), C1)', '\\frac{y^3}{3} + x \\cos{\\left(y \\right)} = C_{1}')})
		self.assertEqual (get ('delall'), {'msg': ['All variables deleted.']})
		self.assertEqual (get ('y = y(x)'), {'math': ('y = y(x)', "y = Function('y')(x)", 'y = y\\left(x \\right)')})
		self.assertEqual (get ("eq = y' + 4/x * y == x**3 y**2"), {'math': ("eq = 4 y / x + y' == x**3 y**2", 'eq = Eq((4*y) / x + diff(y), x**3*y**2)', "eq = \\frac{4 y}{x} + y' == x^3 y^2")})
		self.assertEqual (get ('dsolve (eq, ics = {y(2): -1})'), {'math': ('y(x) = 1 / x**4 {-ln(x) + ln(2) - 1/16}', 'y = Lambda(x, 1 / (x**4*(-ln(x) + ln(2) - S(1)/16)))', 'y\\left(x \\right) = \\frac{1}{x^4 \\left(-\\ln{\\left(x \\right)} + \\ln{\\left(2 \\right)} - \\frac{1}{16} \\right)}')})
		self.assertEqual (get ('sol = _.args [1]'), {'math': ('sol = 1 / x**4 {-ln(x) + ln(2) - 1/16}', 'sol = 1 / (x**4*(-ln(x) + ln(2) - S(1)/16))', 'sol = \\frac{1}{x^4 \\left(-\\ln{\\left(x \\right)} + \\ln{\\left(2 \\right)} - \\frac{1}{16} \\right)}')})
		self.assertEqual (get ('checkodesol (eq, sol, y)'), {'math': ('(True, 0)', '(True, 0)', '\\left(True, 0 \\right)')})
		self.assertEqual (get ('\\. eq |_{y (x) = sol}'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('y (x) = sol'), {'math': ('y(x) = 1 / x**4 {-ln(x) + ln(2) - 1/16}', 'y = Lambda(x, 1 / (x**4*(-ln(x) + ln(2) - S(1)/16)))', 'y\\left(x \\right) = \\frac{1}{x^4 \\left(-\\ln{\\left(x \\right)} + \\ln{\\left(2 \\right)} - \\frac{1}{16} \\right)}')})
		self.assertEqual (get ('eq'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ("y' + 4/x * y, x**3 y**2"), {'math': ('(1 / x**5 (-ln(x) + ln(2) - 1/16)**2, 1 / x**5 (-ln(x) + ln(2) - 1/16)**2)', '(1 / (x**5*(-ln(x) + ln(2) - S(1)/16)**2), 1 / (x**5*(-ln(x) + ln(2) - S(1)/16)**2))', '\\left(\\frac{1}{x^5 \\left(-\\ln{\\left(x \\right)} + \\ln{\\left(2 \\right)} - \\frac{1}{16} \\right)^2}, \\frac{1}{x^5 \\left(-\\ln{\\left(x \\right)} + \\ln{\\left(2 \\right)} - \\frac{1}{16} \\right)^2} \\right)')})
		self.assertEqual (get ('delall'), {'msg': ['All variables deleted.']})
		self.assertEqual (get ('x, y = x(t), y(t)'), {'math': [('x = x(t)', "x = Function('x')(t)", 'x = x\\left(t \\right)'), ('y = y(t)', "y = Function('y')(t)", 'y = y\\left(t \\right)')]})
		self.assertEqual (get ("dsolve (y'' + 11y' + 24y, ics = {y(0): 0, y'(0): -7})"), {'math': ('y(t) = {{7 * e**{-5 t}} / 5 - 7/5} e**{-3 t}', 'y = Lambda(t, ((7*e**(-5*t)) / 5 - S(7)/5)*e**(-3*t))', 'y\\left(t \\right) = \\left(\\frac{7 e^{-5 t}}{5} - \\frac{7}{5} \\right) e^{-3 t}')})
		self.assertEqual (get ("dsolve ((x' = 12t x + 8y, y' = 21x + 7t y))"), {'math': ('[x(t) = C1 x0(t) + 8 C2 {\\int e**{19t**2 / 2} / x0(t)**2 dt} * x0(t), y(t) = C1 y0(t) + C2 {e**{19t**2 / 2} / x0(t) + 8 {\\int e**{19t**2 / 2} / x0(t)**2 dt} * y0(t)}]', "[Eq(Function('x')(t), C1*Function('x0')(t) + 8*C2*Integral(e**((19*t**2) / 2) / Function('x0')(t)**2, t)*Function('x0')(t)), Eq(Function('y')(t), C1*Function('y0')(t) + C2*(e**((19*t**2) / 2) / Function('x0')(t) + 8*Integral(e**((19*t**2) / 2) / Function('x0')(t)**2, t)*Function('y0')(t)))]", '\\left[x\\left(t \\right) = C_{1}\\ x_{0}\\left(t \\right) + 8\\ C_{2} {\\int \\frac{e^\\frac{19 t^2}{2}}{x_{0}\\left(t \\right)^2} \\ dt} \\cdot x_{0}\\left(t \\right), y\\left(t \\right) = C_{1}\\ y_{0}\\left(t \\right) + {C_{2}}\\left(\\frac{e^\\frac{19 t^2}{2}}{x_{0}\\left(t \\right)} + 8 {\\int \\frac{e^\\frac{19 t^2}{2}}{x_{0}\\left(t \\right)^2} \\ dt} \\cdot y_{0}\\left(t \\right) \\right) \\right]')})

	def test_pde (self):
		reset ()
		self.assertEqual (get ('delall'), {'msg': ['All variables deleted.']})
		self.assertEqual (get ('u, X, T = u (x, t), X (x), T (t)'), {'math': [('u = u(x, t)', "u = Function('u')(x, t)", 'u = u\\left(x, t \\right)'), ('X = X(x)', "X = Function('X')(x)", 'X = X\\left(x \\right)'), ('T = T(t)', "T = Function('T')(t)", 'T = T\\left(t \\right)')]})
		self.assertEqual (get ('eq = (du / dx = e**u * du / dt)'), {'math': ('eq = (du / dx = du / dt * e**u)', 'eq = Eq(Derivative(u, x), Derivative(u, t)*e**u)', 'eq = \\left(\\frac{\\partial u}{\\partial x} = \\frac{\\partial u}{\\partial t} \\cdot e^u \\right)')})
		self.assertEqual (get ('pde_separate_add (eq, u, [X, T])'), {'math': ("[X' e**-X, T' e**T]", '[diff(X)*e**-X, diff(T)*e**T]', "\\left[X' e^{-X}, T' e^T \\right]")})
		self.assertEqual (get ('u, Y = u (x, y), Y (y)'), {'math': [('u = u(x, y)', "u = Function('u')(x, y)", 'u = u\\left(x, y \\right)'), ('Y = Y(y)', "Y = Function('Y')(y)", 'Y = Y\\left(y \\right)')]})
		self.assertEqual (get ('eq = d**2u / dx**2 == d**2u / dy**2'), {'math': ('eq = d**2 u / dx**2 == d**2 u / dy**2', 'eq = Eq(Derivative(u, x, 2), Derivative(u, y, 2))', 'eq = \\frac{\\partial^2 u}{\\partial x^2} == \\frac{\\partial^2 u}{\\partial y^2}')})
		self.assertEqual (get ('pde_separate_mul (eq, u, [X, Y])'), {'math': ("[X'' / X, Y'' / Y]", '[diff(diff(X)) / X, diff(diff(Y)) / Y]', "\\left[\\frac{X''}{X}, \\frac{Y''}{Y} \\right]")})
		self.assertEqual (get ('eq = Eq (1 + 2 * {du/dx / u} + 3 * {du/dy / u})'), {'math': ('eq = ({2 * du / dx} / u + {3 * du / dy} / u + 1 = 0)', 'eq = Eq((2*Derivative(u, x)) / u + (3*Derivative(u, y)) / u + 1, 0)', 'eq = \\left(\\frac{2 {\\frac{\\partial u}{\\partial x}}}{u} + \\frac{3 {\\frac{\\partial u}{\\partial y}}}{u} + 1 = 0 \\right)')})
		self.assertEqual (get ('pdsolve (eq)'), {'math': ('u(x, y) = ?F(3 x - 2 y) e**{-3 y / 13 - 2 x / 13}', "u = Lambda((x, y), Function('F')(3*x - 2*y)*e**(-(3*y) / 13 - (2*x) / 13))", 'u\\left(x, y \\right) = ?F\\left(3 x - 2 y \\right) e^{-\\frac{3 y}{13} - \\frac{2 x}{13}}')})
		self.assertEqual (get ('sol = _.args [1]'), {'math': ('sol = ?F(3 x - 2 y) e**{-3 y / 13 - 2 x / 13}', "sol = Function('F')(3*x - 2*y)*e**(-(3*y) / 13 - (2*x) / 13)", 'sol = ?F\\left(3 x - 2 y \\right) e^{-\\frac{3 y}{13} - \\frac{2 x}{13}}')})
		self.assertEqual (get ('checkpdesol (eq, sol)'), {'math': ('(True, 0)', '(True, 0)', '\\left(True, 0 \\right)')})
		self.assertEqual (get ('u (x, y) = sol'), {'math': ('u(x, y) = ?F(3 x - 2 y) e**{-3 y / 13 - 2 x / 13}', "u = Lambda((x, y), Function('F')(3*x - 2*y)*e**(-(3*y) / 13 - (2*x) / 13))", 'u\\left(x, y \\right) = ?F\\left(3 x - 2 y \\right) e^{-\\frac{3 y}{13} - \\frac{2 x}{13}}')})
		self.assertEqual (get ('eq'), {'math': ("2 {3 F(xi_1)'(3 x - 2 y) e**{-3 y / 13 - 2 x / 13} - 2 ?F(3 x - 2 y) e**{-3 y / 13 - 2 x / 13} / 13} e**{2 x / 13 + 3 y / 13} / ?F(3 x - 2 y) + 3 {-{2 F(xi_1)'(3 x - 2 y) e**{-3 y / 13 - 2 x / 13}} - 3 ?F(3 x - 2 y) e**{-3 y / 13 - 2 x / 13} / 13} e**{2 x / 13 + 3 y / 13} / ?F(3 x - 2 y) + 1 = 0", "Eq((2*(3*Subs(diff(Function('F')(xi_1)), xi_1, 3*x - 2*y)*e**(-(3*y) / 13 - (2*x) / 13) - (2*Function('F')(3*x - 2*y)*e**(-(3*y) / 13 - (2*x) / 13)) / 13)*e**((2*x) / 13 + (3*y) / 13)) / Function('F')(3*x - 2*y) + (3*(-(2*Subs(diff(Function('F')(xi_1)), xi_1, 3*x - 2*y)*e**(-(3*y) / 13 - (2*x) / 13)) - (3*Function('F')(3*x - 2*y)*e**(-(3*y) / 13 - (2*x) / 13)) / 13)*e**((2*x) / 13 + (3*y) / 13)) / Function('F')(3*x - 2*y) + 1, 0)", "\\frac{2 \\left(3 F\\left(xi\\_1 \\right)'\\left(3 x - 2 y \\right) e^{-\\frac{3 y}{13} - \\frac{2 x}{13}} - \\frac{2 ?F\\left(3 x - 2 y \\right) e^{-\\frac{3 y}{13} - \\frac{2 x}{13}}}{13} \\right) e^{\\frac{2 x}{13} + \\frac{3 y}{13}}}{?F\\left(3 x - 2 y \\right)} + \\frac{3 \\left(-{2 F\\left(xi\\_1 \\right)'\\left(3 x - 2 y \\right) e^{-\\frac{3 y}{13} - \\frac{2 x}{13}}} - \\frac{3 ?F\\left(3 x - 2 y \\right) e^{-\\frac{3 y}{13} - \\frac{2 x}{13}}}{13} \\right) e^{\\frac{2 x}{13} + \\frac{3 y}{13}}}{?F\\left(3 x - 2 y \\right)} + 1 = 0")})
		self.assertEqual (get ('simplify _'), {'math': ('True', 'True', 'True')})
		self.assertEqual (get ('u = ?u (x, y)'), {'math': ('u = u(x, y)', "u = Function('u')(x, y)", 'u = u\\left(x, y \\right)')})
		self.assertEqual (get ('eq = x * du/dx - y * du/dy + y**2u - y**2'), {'math': ('eq = -y**2 + x * du / dx + y**2 u - y * du / dy', 'eq = -y**2 + x*Derivative(u, x) + y**2*u - y*Derivative(u, y)', 'eq = -y^2 + x \\frac{\\partial u}{\\partial x} + y^2 u - y \\frac{\\partial u}{\\partial y}')})
		self.assertEqual (get ('pdsolve (eq)'), {'math': ('?u(x, y) = ?F(x y) e**{y**2 / 2} + 1', "Eq(Function('u')(x, y), Function('F')(x*y)*e**(y**2 / 2) + 1)", '?u\\left(x, y \\right) = ?F\\left(x\\ y \\right) e^\\frac{y^2}{2} + 1')})
		self.assertEqual (get ('v (x, y) = _.args [1]'), {'math': ('v(x, y) = ?F(x y) e**{y**2 / 2} + 1', "v = Lambda((x, y), Function('F')(x*y)*e**(y**2 / 2) + 1)", 'v\\left(x, y \\right) = ?F\\left(x\\ y \\right) e^\\frac{y^2}{2} + 1')})
		self.assertEqual (get ('eq'), {'math': ('-y**2 + x * du / dx + y**2 u - y * du / dy', '-y**2 + x*Derivative(u, x) + y**2*u - y*Derivative(u, y)', '-y^2 + x \\frac{\\partial u}{\\partial x} + y^2 u - y \\frac{\\partial u}{\\partial y}')})
		self.assertEqual (get ('\\. eq |_{u (x, y) = v}'), {'math': ("-y**2 + y**2 {?F(x y) e**{y**2 / 2} + 1} - y {x F(xi_1)'(x y) e**{y**2 / 2} + y ?F(x y) e**{y**2 / 2}} + x y F(xi_1)'(x y) e**{y**2 / 2}", "-y**2 + y**2*(Function('F')(x*y)*e**(y**2 / 2) + 1) - y*(x*Subs(diff(Function('F')(xi_1)), xi_1, x*y)*e**(y**2 / 2) + y*Function('F')(x*y)*e**(y**2 / 2)) + x*y*Subs(diff(Function('F')(xi_1)), xi_1, x*y)*e**(y**2 / 2)", "-y^2 + y^2 \\left(?F\\left(x\\ y \\right) e^\\frac{y^2}{2} + 1 \\right) - {y}\\left(x\\ F\\left(xi\\_1 \\right)'\\left(x\\ y \\right) e^\\frac{y^2}{2} + y\\ ?F\\left(x\\ y \\right) e^\\frac{y^2}{2} \\right) + x\\ y\\ F\\left(xi\\_1 \\right)'\\left(x\\ y \\right) e^\\frac{y^2}{2}")})
		self.assertEqual (get ('simplify _'), {'math': ('0', '0', '0')})
		self.assertEqual (get ('F (x) = e**x'), {'math': ('F(x) = e**x', 'F = Lambda(x, e**x)', 'F\\left(x \\right) = e^x')})
		self.assertEqual (get ('\\. eq |_{u (x, y) = v}'), {'math': ('-y**2 + y**2 {e**{y**2 / 2} e**{x y} + 1} - y {x e**{y**2 / 2} e**{x y} + y e**{y**2 / 2} e**{x y}} + x y e**{y**2 / 2} e**{x y}', '-y**2 + y**2*(e**(y**2 / 2)*e**(x*y) + 1) - y*(x*e**(y**2 / 2)*e**(x*y) + y*e**(y**2 / 2)*e**(x*y)) + x*y*e**(y**2 / 2)*e**(x*y)', '-y^2 + y^2 \\left(e^\\frac{y^2}{2} e^{x\\ y} + 1 \\right) - {y}\\left(x\\ e^\\frac{y^2}{2} e^{x\\ y} + y\\ e^\\frac{y^2}{2} e^{x\\ y} \\right) + x\\ y\\ e^\\frac{y^2}{2} e^{x\\ y}')})
		self.assertEqual (get ('simplify _'), {'math': ('0', '0', '0')})

	def test_pseudo_functions (self):
		reset ()
		self.assertEqual (get ('delall'), {'msg': ['All variables deleted.']})
		self.assertEqual (get ('1 + 2'), {'math': ('3', '3', '3')})
		self.assertEqual (get ('%(1 + 2)'), {'math': ('1 + 2', '1 + 2', '1 + 2')})
		self.assertEqual (get ('_'), {'math': ('3', '3', '3')})
		self.assertEqual (get ('x, y = 1, 2'), {'math': [('x = 1', 'x = 1', 'x = 1'), ('y = 2', 'y = 2', 'y = 2')]})
		self.assertEqual (get ('x + y'), {'math': ('3', '3', '3')})
		self.assertEqual (get ('%(x + y)'), {'math': ('1 + 2', '1 + 2', '1 + 2')})
		self.assertEqual (get ('%@(x + y)'), {'math': ('x + y', 'x + y', 'x + y')})
		self.assertEqual (get ('@(x + y)'), {'math': ('x + y', 'x + y', 'x + y')})
		self.assertEqual (get ('delall'), {'msg': ['All variables deleted.']})
		self.assertEqual (get ('x'), {'math': ('x', 'x', 'x')})
		self.assertEqual (get ('x = 2'), {'math': ('x = 2', 'x = 2', 'x = 2')})
		self.assertEqual (get ('x'), {'math': ('2', '2', '2')})
		self.assertEqual (get ('@x'), {'math': ('x', 'x', 'x')})
		self.assertEqual (get ('lambda x: x'), {'math': ('lambda x: x', 'Lambda(x, x)', '\\left(x \\mapsto x \\right)')})
		self.assertEqual (get ('lambda x: @x'), {'math': ('lambda x: 2', 'Lambda(x, 2)', '\\left(x \\mapsto 2 \\right)')})
		self.assertEqual (get ('lambda x: @@x'), {'math': ('lambda x: x', 'Lambda(x, x)', '\\left(x \\mapsto x \\right)')})
		self.assertEqual (get ('delall'), {'msg': ['All variables deleted.']})
		self.assertEqual (get ('lambda x: \\int x + 1 + 2 dx'), {'math': ('lambda x: \\int x + 3 dx', 'Lambda(x, Integral(x + 3, x))', '\\left(x \\mapsto \\int x + 3 \\ dx \\right)')})
		self.assertEqual (get ('lambda x: %(\\int x + 1 + 2 dx)'), {'math': ('lambda x: x**2 / 2 + 3 x', 'Lambda(x, x**2 / 2 + 3*x)', '\\left(x \\mapsto \\frac{x^2}{2} + 3 x \\right)')})
		self.assertEqual (get ('lambda x: %%(\\int x + 1 + 2 dx)'), {'math': ('lambda x: \\int x + 1 + 2 dx', 'Lambda(x, Integral(x + 1 + 2, x))', '\\left(x \\mapsto \\int x + 1 + 2 \\ dx \\right)')})
		self.assertEqual (get ('lambda x: %%(\\int x + y + y dx)'), {'math': ('lambda x: \\int x + y + y dx', 'Lambda(x, Integral(x + y + y, x))', '\\left(x \\mapsto \\int x + y + y \\ dx \\right)')})
		self.assertEqual (get ('y = 2'), {'math': ('y = 2', 'y = 2', 'y = 2')})
		self.assertEqual (get ('lambda x: %%(\\int x + y + y dx)'), {'math': ('lambda x: \\int x + 2 + 2 dx', 'Lambda(x, Integral(x + 2 + 2, x))', '\\left(x \\mapsto \\int x + 2 + 2 \\ dx \\right)')})
		self.assertEqual (get ('lambda x: %%@(\\int x + y + y dx)'), {'math': ('lambda x: \\int x + y + y dx', 'Lambda(x, Integral(x + y + y, x))', '\\left(x \\mapsto \\int x + y + y \\ dx \\right)')})
		self.assertEqual (get ('lambda x: %%(\\int x + @y + y dx)'), {'math': ('lambda x: \\int x + y + 2 dx', 'Lambda(x, Integral(x + y + 2, x))', '\\left(x \\mapsto \\int x + y + 2 \\ dx \\right)')})

	def test_assign_and_mapback (self):
		reset ()
		self.assertEqual (get ('f = ?()'), {'math': ('f = f()', "f = Function('f')", 'f = f\\left( \\right)')})
		self.assertEqual (get ('g = f'), {'math': ('g = f()', "g = Function('f')", 'g = f\\left( \\right)')})
		self.assertEqual (get ('f = ?f(x)'), {'math': ('f = f(x)', "f = Function('f')(x)", 'f = f\\left(x \\right)')})
		self.assertEqual (get ('g = f'), {'math': ('g = f(x)', "g = Function('f')(x)", 'g = f\\left(x \\right)')})
		self.assertEqual (get ('$'), {'math': ('$', "Symbol('')", '\\$')})
		self.assertEqual (get ('$()'), {'math': ('$', "Symbol('')", '\\$')})
		self.assertEqual (get ('$(real = True)'), {'math': ('$(real = True)', "Symbol('', real = True)", '\\$\\left(real = True \\right)')})
		self.assertEqual (get ('$s'), {'math': ('s', 's', 's')})
		self.assertEqual (get ('$s()'), {'math': ('s', 's', 's')})
		self.assertEqual (get ('$s(real = True)'), {'math': ('$s(real = True)', "Symbol('s', real = True)", '\\$s\\left(real = True \\right)')})
		self.assertEqual (get ('s = $'), {'err': 'server.CircularReferenceError: cannot asign unqualified anonymous symbol'})
		self.assertEqual (get ('t = s'), {'math': ('t = s', 't = s', 't = s')})
		self.assertEqual (get ('s = $r'), {'math': ('s = r', 's = r', 's = r')})
		self.assertEqual (get ('t = s'), {'math': ('t = r', 't = r', 't = r')})
		self.assertEqual (get ('s = $s'), {'err': "server.CircularReferenceError: I'm sorry, Dave. I'm afraid I can't do that."})
		self.assertEqual (get ('del s'), {'msg': ["Variable 's' deleted."]})
		self.assertEqual (get ('s = $s'), {'err': "server.CircularReferenceError: I'm sorry, Dave. I'm afraid I can't do that."})
		self.assertEqual (get ('s = $(real = True)'), {'math': ('s = $s(real = True)', "s = Symbol('s', real = True)", 's = \\$s\\left(real = True \\right)')})
		self.assertEqual (get ('s'), {'math': ('s', 's', 's')})
		self.assertEqual (get ('s = $s'), {'err': 'server.CircularReferenceError: trying to assign unqualified symbol to variable of the same name'})
		self.assertEqual (get ('s'), {'math': ('s', 's', 's')})
		self.assertEqual (get ('s = $s(real = True)'), {'math': ('s = $s(real = True)', "s = Symbol('s', real = True)", 's = \\$s\\left(real = True \\right)')})
		self.assertEqual (get ('s'), {'math': ('s', 's', 's')})
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

"""), ('lambda', """

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

"""), ('lambda2', """

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

"""), ('lambda_expr', """

a = lambda l: l
a; a
{a = a}
a == a
a.b
a, a
{a}
(a)
[a]
|a|
-a
a!
a + a
a a
{a} a
a * a
a / a
a ** a
ln a
sqrt a
sin a
\\lim_{a\\to0} a
\\sum_{n=0}^9 a
d/dx a
a'
\\int a dx
\\[[a, a], [a, a]]
a if a else a
a if a
lambda: a
a [a]
{a} [a]
: a
a: a
:b a
a:b: a
::c a
a:b:c a
{a, a}
{a, a + 1}
{a: a}
a || a
a ^^ a
a && a
a or a
a and a
not a
\\. a |_{a = a}
\\. a |_{a = b}

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
f (x)' (0)
d/dx (f (x)) (0)

f = ?f (x)
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
d/dy (f) (x)
f (x)' (0)
d/dx (f (x)) (0)
d/dy (f (x)) (0)

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

f (x) = x
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

f = ?f (x)
f
1 + f
g = f
g
1 + g
del f
g
1 + g

delall
f (x) = x**2
y = 1 + (?f (x) = 2)
g (x) = ?f (x)
g (2)
del (f, g)
f = f (x, y)
f = 1 + f (x, y)
del f
f (x, y) = ?g (x + y)
f (x, y)
f (1, y)
f (x, 2)
f (a, b)

"""), ('intro_examples', """

cos -pi
N cos**-1 -\\log_2 sqrt[4] 16
factor (x^3 + 3y x^2 + 3x y^2 + y^3)
Limit (\\frac1x, x, 0, dir='-')
\\sum_{n=0}**oo x**n / n!
d**3 / dx dy^2 x^3 y^3
Integral (e^{-x^2}, (x, 0, \\infty))
\\int^\\pi \\int^{2pi} \\int^1 rho**2 sin\\phi drho dtheta dphi
\\[[1, 2], [3, 4]]**-1
Matrix (4, 4, lambda r, c: c + r if c &gt; r else 0)
f (x, y) = sqrt (x**2 + y**2)
f (3, 4)
solve (x**2 + y = 4, x)
dsolve (y(x)'' + 9y(x))
y = y(t); dsolve (y'' - 4y' - 12y = 3e**{5t}); del y
pdsolve (x * d/dx u (x, y) - y * d/dy u (x, y) + y**2u (x, y) - y**2)
simplify (not (not a and not b) and not (not a or not c))
(({1, 2, 3} && {2, 3, 4}) ^^ {3, 4, 5}) - \\{4} || {7,}

"""), ('LSDI', """

delall
\\lim_{h\\to0} {(x + h)**2 - x**2} / h
Limit ((1 + 1/x)**x, x, \\infty)
{(1 - 1/x)**x}.limit (x, \\infty)
limit (sin x / x, x, 0)

\\sum_{n=0}^\\infty (-1)**n x**{2n} / (2n)!
Sum ((-1)**n x**{2n + 1} / (2n + 1)!, (n, 0, oo))
summation ((-3)^n / n 7^{n+1} * (x - 5)^n, (n, 1, oo))

d/dx ln x
Derivative (x**3y**2, x, y)
diff (sin x + cos x, x, 2)
{x**2sin**2y}.diff (x, y)
d**3/dx**2dy x**3y**2
sin (x)'
(e**{2x})''
d/dx ln (y(x))

\\int x**a dx
Integral (a**x, x)
{x**3y**2}.integrate (x, y)
\\int_0**oo e**{-st} dt
Integral (r, (r, 0, 1), (theta, 0, 2pi))
integrate (sin x / x, (x, -oo, oo))

"""), ('solve', """

delall
solve (x**2 = 4)
solve (x**2 - 4)
solve (|x| >= x**2)
solve (x**2 + 2 x - 1 > 7)
solve (y = x**2 + 2 x - 1, x)
solve (x + (e**x)**2, e**x)
solve (x + e**x, x)
solve (x + e**x, x, implicit = True)
solve ((x + 2y = 5, y - 2x = 0))
solve ((a + b)x - b + 2, a, b)
solve ((a + b)x - b**2 + 2, a, b)

a, b = x**2 + y -2, y**2 - 4
solve ([a, b])
s = _
a.subs (s [0]), b.subs (s [0])
a.subs (s [1]), b.subs (s [1])
a.subs (s [2]), b.subs (s [2])
a.subs (s [3]), b.subs (s [3])
w = {x: 1, y: 2}
a.subs (w), b.subs (w)

"""), ('ode', """

delall
dsolve (d**2/dx**2 ?(x) + 9?(x))
dsolve (?(x)'' + 9?(x))
dsolve (y(x)'' + 9y(x))
y = y(x)
dsolve (y'' + 9y)
dsolve (sin x cos y + cos x sin y y')
dsolve (y' + 4/x * y = x**3 y**2)
dsolve (y' + 4/x * y = x**3 y**2, ics = {y(2): -1})
dsolve (cos y - y' * (x sin y - y**2))

delall
y = y(x)
eq = y' + 4/x * y == x**3 y**2
dsolve (eq, ics = {y(2): -1})
sol = _.args [1]
checkodesol (eq, sol, y)
\\. eq |_{y (x) = sol}
y (x) = sol
eq
y' + 4/x * y, x**3 y**2

delall
x, y = x(t), y(t)
dsolve (y'' + 11y' + 24y, ics = {y(0): 0, y'(0): -7})
dsolve ((x' = 12t x + 8y, y' = 21x + 7t y))

"""), ('pde', """

delall
u, X, T = u (x, t), X (x), T (t)
eq = (du / dx = e**u * du / dt)
pde_separate_add (eq, u, [X, T])
u, Y = u (x, y), Y (y)
eq = d**2u / dx**2 == d**2u / dy**2
pde_separate_mul (eq, u, [X, Y])

eq = Eq (1 + 2 * {du/dx / u} + 3 * {du/dy / u})
pdsolve (eq)
sol = _.args [1]
checkpdesol (eq, sol)
u (x, y) = sol
eq
simplify _

u = ?u (x, y)
eq = x * du/dx - y * du/dy + y**2u - y**2
pdsolve (eq)
v (x, y) = _.args [1]
eq
\\. eq |_{u (x, y) = v}
simplify _
F (x) = e**x
\\. eq |_{u (x, y) = v}
simplify _

"""), ('pseudo_functions', """

delall
1 + 2
%(1 + 2)
_
x, y = 1, 2
x + y
%(x + y)
%@(x + y)
@(x + y)

delall
x
x = 2
x
@x
lambda x: x
lambda x: @x
lambda x: @@x

delall
lambda x: \\int x + 1 + 2 dx
lambda x: %(\\int x + 1 + 2 dx)
lambda x: %%(\\int x + 1 + 2 dx)
lambda x: %%(\\int x + y + y dx)
y = 2
lambda x: %%(\\int x + y + y dx)
lambda x: %%@(\\int x + y + y dx)
lambda x: %%(\\int x + @y + y dx)

"""), ('assign_and_mapback', """

f = ?()
g = f
f = ?f(x)
g = f

$
$()
$(real = True)
$s
$s()
$s(real = True)

s = $
t = s
s = $r
t = s
s = $s
del s
s = $s

s = $(real = True)
s
s = $s
s
s = $s(real = True)
s

"""),

)

SYSARGV  = sys.argv [:]
sys.argv = [os.path.abspath ('server.py'), '--child', '--strict', '127.0.0.1:9001']

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
