#!/usr/bin/env python

import unittest

from sast import AST
from sparser import Parser
from sym import *

parser = Parser ()
p      = lambda s: parser.parse (s) [0]

class Test (unittest.TestCase):
	def test_sparser (self):
		self.assertEqual (p ('1'), AST ('#', '1'))
		self.assertEqual (p ('-1.23456789012345678901234567890123456789012345678901234567890123456789012345678901'), AST ('#', '-1.23456789012345678901234567890123456789012345678901234567890123456789012345678901'))
		self.assertEqual (p ('x'), AST ('@', 'x'))
		self.assertEqual (p ('-1'), AST ('#', '-1'))
		self.assertEqual (p ('-x'), AST ('-', ('@', 'x')))
		self.assertEqual (p ('{x}'), AST ('@', 'x'))
		self.assertEqual (p ('{{x}}'), AST ('@', 'x'))
		self.assertEqual (p ('()'), AST ('(', (',', ())))
		self.assertEqual (p ('(x)'), AST ('(', ('@', 'x')))
		self.assertEqual (p ('(x,)'), AST ('(', (',', (('@', 'x'),))))
		self.assertEqual (p ('(x,y)'), AST ('(', (',', (('@', 'x'), ('@', 'y')))))
		self.assertEqual (p ('(x,y,)'), AST ('(', (',', (('@', 'x'), ('@', 'y')))))
		self.assertEqual (p ('[]'), AST ('[', ()))
		self.assertEqual (p ('[x]'), AST ('[', (('@', 'x'),)))
		self.assertEqual (p ('[x,]'), AST ('[', (('@', 'x'),)))
		self.assertEqual (p ('[x,y]'), AST ('[', (('@', 'x'), ('@', 'y'))))
		self.assertEqual (p ('[x,y,]'), AST ('[', (('@', 'x'), ('@', 'y'))))
		self.assertEqual (p ('"x\\x20\\n"'), AST ('"', 'x \n'))
		self.assertEqual (p ("'x\\x20\\n'"), AST ('"', 'x \n'))
		self.assertEqual (p ('|x|'), AST ('|', ('@', 'x')))
		self.assertEqual (p ('x!'), AST ('!', ('@', 'x')))
		self.assertEqual (p ('x+y'), AST ('+', (('@', 'x'), ('@', 'y'))))
		self.assertEqual (p ('x-y'), AST ('+', (('@', 'x'), ('-', ('@', 'y')))))
		self.assertEqual (p ('x*y'), AST ('*', (('@', 'x'), ('@', 'y'))))
		self.assertEqual (p ('xy'), AST ('*', (('@', 'x'), ('@', 'y'))))
		self.assertEqual (p ('x(y)'), AST ('*', (('@', 'x'), ('(', ('@', 'y')))))
		self.assertEqual (p ('x/y'), AST ('/', ('@', 'x'), ('@', 'y')))
		self.assertEqual (p ('x^y'), AST ('^', ('@', 'x'), ('@', 'y')))
		self.assertEqual (p ('log x'), AST ('log', ('@', 'x')))
		self.assertEqual (p ('log {x}'), AST ('log', ('@', 'x')))
		self.assertEqual (p ('log (x)'), AST ('log', ('(', ('@', 'x'))))
		self.assertEqual (p ('log_2 x'), AST ('log', ('@', 'x'), ('#', '2')))
		self.assertEqual (p ('log_2 {x}'), AST ('log', ('@', 'x'), ('#', '2')))
		self.assertEqual (p ('log_2 (x)'), AST ('log', ('(', ('@', 'x')), ('#', '2')))
		self.assertEqual (p ('sqrt x'), AST ('sqrt', ('@', 'x')))
		self.assertEqual (p ('sqrt {x}'), AST ('sqrt', ('@', 'x')))
		self.assertEqual (p ('sqrt (x)'), AST ('sqrt', ('(', ('@', 'x'))))
		self.assertEqual (p ('sqrt[3] x'), AST ('sqrt', ('@', 'x'), ('#', '3')))
		self.assertEqual (p ('sqrt[3] {x}'), AST ('sqrt', ('@', 'x'), ('#', '3')))
		self.assertEqual (p ('sqrt[3] (x)'), AST ('sqrt', ('(', ('@', 'x')), ('#', '3')))
		self.assertEqual (p ('sin x'), AST ('func', 'sin', ('@', 'x')))
		self.assertEqual (p ('sin^2 x'), AST ('^', ('func', 'sin', ('@', 'x')), ('#', '2')))
		self.assertEqual (p ('sin (x)'), AST ('func', 'sin', ('@', 'x')))
		self.assertEqual (p ('sin (x)^2'), AST ('^', ('func', 'sin', ('(', ('@', 'x'))), ('#', '2')))
		self.assertEqual (p ('{sin x}^2'), AST ('^', ('func', 'sin', ('@', 'x')), ('#', '2')))
		self.assertEqual (p ('sin**2 x'), AST ('^', ('func', 'sin', ('@', 'x')), ('#', '2')))
		self.assertEqual (p ('sin**-1 x'), AST ('func', 'asin', ('@', 'x')))
		self.assertEqual (p ('\\lim_{x\\to0} 1/x'), AST ('lim', ('/', ('#', '1'), ('@', 'x')), ('@', 'x'), ('#', '0')))
		self.assertEqual (p ('\\lim_{x\\to0^+} 1/x'), AST ('lim', ('/', ('#', '1'), ('@', 'x')), ('@', 'x'), ('#', '0'), '+'))
		self.assertEqual (p ('\\lim_{x\\to0**-} 1/x'), AST ('lim', ('/', ('#', '1'), ('@', 'x')), ('@', 'x'), ('#', '0'), '-'))
		self.assertEqual (p ('Limit (1/x, x, 0)'), AST ('lim', ('/', ('#', '1'), ('@', 'x')), ('@', 'x'), ('#', '0'), '+'))
		self.assertEqual (p ('Limit (1/x, x, 0, "-")'), AST ('lim', ('/', ('#', '1'), ('@', 'x')), ('@', 'x'), ('#', '0'), '-'))
		self.assertEqual (p ('Limit (1/x, x, 0, dir="+-")'), AST ('lim', ('/', ('#', '1'), ('@', 'x')), ('@', 'x'), ('#', '0')))
		self.assertEqual (p ('\\sum_{n=0}^\\infty x^n/n!'), AST ('sum', ('/', ('^', ('@', 'x'), ('@', 'n')), ('!', ('@', 'n'))), ('@', 'n'), ('#', '0'), ('@', '\\infty')))
		self.assertEqual (p ('Sum (x^n/n!, (n, 0, oo))'), AST ('sum', ('/', ('^', ('@', 'x'), ('@', 'n')), ('!', ('@', 'n'))), ('@', 'n'), ('#', '0'), ('@', '\\infty')))
		self.assertEqual (p ('d/dx x**2y**2z'), AST ('diff', ('*', (('^', ('@', 'x'), ('#', '2')), ('^', ('@', 'y'), ('#', '2')), ('@', 'z'))), (('@', 'dx'),)))
		self.assertEqual (p ('d^2/dx^2 x^2y**2z'), AST ('diff', ('*', (('^', ('@', 'x'), ('#', '2')), ('^', ('@', 'y'), ('#', '2')), ('@', 'z'))), (('^', ('@', 'dx'), ('#', '2')),)))
		self.assertEqual (p ('d^3/dx^2dy x^2y**2z'), AST ('diff', ('*', (('^', ('@', 'x'), ('#', '2')), ('^', ('@', 'y'), ('#', '2')), ('@', 'z'))), (('^', ('@', 'dx'), ('#', '2')), ('@', 'dy'))))
		self.assertEqual (p ('\\partial^4/\\partialx^2\\partial y\\partialz x^2y**2z'), AST ('diff', ('*', (('^', ('@', 'x'), ('#', '2')), ('^', ('@', 'y'), ('#', '2')), ('@', 'z'))), (('^', ('@', '\\partial x'), ('#', '2')), ('@', '\\partial y'), ('@', '\\partial z'))))
		self.assertEqual (p ('Derivative (x^2y**2z, x, 2, y, z)'), AST ('diff', ('*', (('^', ('@', 'x'), ('#', '2')), ('^', ('@', 'y'), ('#', '2')), ('@', 'z'))), (('^', ('@', 'dx'), ('#', '2')), ('@', 'dy'), ('@', 'dz'))))
		self.assertEqual (p ('\\int dx'), AST ('intg', None, ('@', 'dx')))
		self.assertEqual (p ('\\int x dx'), AST ('intg', ('@', 'x'), ('@', 'dx')))
		self.assertEqual (p ('\\int_0^1 x dx'), AST ('intg', ('@', 'x'), ('@', 'dx'), ('#', '0'), ('#', '1')))
		self.assertEqual (p ('\\int_0^1 \\int y dy dx'), AST ('intg', ('intg', ('@', 'y'), ('@', 'dy')), ('@', 'dx'), ('#', '0'), ('#', '1')))
		self.assertEqual (p ('Integral (\\int y dy, (x, 0, 1))'), AST ('intg', ('intg', ('@', 'y'), ('@', 'dy')), ('@', 'dx'), ('#', '0'), ('#', '1')))
		self.assertEqual (p ('{1,}'), AST ('vec', (('#', '1'),)))
		self.assertEqual (p ('{1,2}'), AST ('vec', (('#', '1'), ('#', '2'))))
		self.assertEqual (p ('{1,2,}'), AST ('vec', (('#', '1'), ('#', '2'))))
		self.assertEqual (p ('{{1,},}'), AST ('mat', ((('#', '1'),),)))
		self.assertEqual (p ('{{1,},{2,}}'), AST ('mat', ((('#', '1'),), (('#', '2'),))))
		self.assertEqual (p ('{{1,},{2,},}'), AST ('mat', ((('#', '1'),), (('#', '2'),))))
		self.assertEqual (p ('\\left[\\begin{matrix} 1 \\end{matrix}\\right]'), AST ('mat', ((('#', '1'),),)))
		self.assertEqual (p ('\\begin{bmatrix} 1 \\\\ \\end{bmatrix}'), AST ('mat', ((('#', '1'),),)))
		self.assertEqual (p ('\\begin{vmatrix} 1 & 2 \\\\ \\end{vmatrix}'), AST ('mat', ((('#', '1'), ('#', '2')),)))
		self.assertEqual (p ('\\begin{pmatrix} 1 & 2 \\\\ 3 & 4 \\end{pmatrix}'), AST ('mat', ((('#', '1'), ('#', '2')), (('#', '3'), ('#', '4')))))
		self.assertEqual (p ('\\begin{matrix} 1 & 2 \\\\ 3 & 4 \\\\ \\end{matrix}'), AST ('mat', ((('#', '1'), ('#', '2')), (('#', '3'), ('#', '4')))))

		# self.assertEqual (p (''), ast ('', ))

	def test_ast2tex (self):
		self.assertEqual (ast2tex (p ('1')), '1')
		self.assertEqual (ast2tex (p ('-1.23456789012345678901234567890123456789012345678901234567890123456789012345678901')), '-1.23456789012345678901234567890123456789012345678901234567890123456789012345678901')
		self.assertEqual (ast2tex (p ('x')), 'x')
		self.assertEqual (ast2tex (p ('-1')), '-1')
		self.assertEqual (ast2tex (p ('-x')), '-x')
		self.assertEqual (ast2tex (p ('(x)')), '\\left(x \\right)')
		self.assertEqual (ast2tex (p ('(x,)')), '\\left(x, \\right)')
		self.assertEqual (ast2tex (p ('(x,y)')), '\\left(x, y \\right)')
		self.assertEqual (ast2tex (p ('[x]')), '\\left[x \\right]')
		self.assertEqual (ast2tex (p ('[x,y]')), '\\left[x, y \\right]')
		self.assertEqual (ast2tex (p ('"x\\x20\\n"')), "\\text{'x \\n'}")
		self.assertEqual (ast2tex (p ('|x|')), '\\left|x \\right|')
		self.assertEqual (ast2tex (p ('x!')), 'x!')
		self.assertEqual (ast2tex (p ('x+y')), 'x + y')
		self.assertEqual (ast2tex (p ('x-y')), 'x - y')
		self.assertEqual (ast2tex (p ('x*y')), 'x y')
		self.assertEqual (ast2tex (p ('x/y')), '\\frac{x}{y}')
		self.assertEqual (ast2tex (p ('x^y')), 'x^y')
		self.assertEqual (ast2tex (p ('log x')), '\\log\\left(x \\right)')
		self.assertEqual (ast2tex (p ('log (x)')), '\\log\\left(x \\right)')
		self.assertEqual (ast2tex (p ('log_2 x')), '\\log_2\\left(x \\right)')
		self.assertEqual (ast2tex (p ('log_2 (x)')), '\\log_2\\left(x \\right)')
		self.assertEqual (ast2tex (p ('sqrt x')), '\\sqrt{x}')
		self.assertEqual (ast2tex (p ('sqrt (x)')), '\\sqrt{x}')
		self.assertEqual (ast2tex (p ('sqrt[3] x')), '\\sqrt[3]{x}')
		self.assertEqual (ast2tex (p ('sqrt[3] (x)')), '\\sqrt[3]{x}')
		self.assertEqual (ast2tex (p ('sin x')), '\\sin\\left(x \\right)')
		self.assertEqual (ast2tex (p ('sin^2 x')), '\\sin^2\\left(x \\right)')
		self.assertEqual (ast2tex (p ('sin (x)')), '\\sin\\left(x \\right)')
		self.assertEqual (ast2tex (p ('sin (x)^2')), '\\sin^2\\left(x \\right)')
		self.assertEqual (ast2tex (p ('sin**-1 x')), '\\sin^{-1}\\left(x \\right)')
		self.assertEqual (ast2tex (p ('\\lim_{x\\to0} 1/x')), '\\lim_{x \\to 0} \\frac{1}{x}')
		self.assertEqual (ast2tex (p ('\\lim_{x\\to0^+} 1/x')), '\\lim_{x \\to 0^+} \\frac{1}{x}')
		self.assertEqual (ast2tex (p ('\\lim_{x\\to0**-} 1/x')), '\\lim_{x \\to 0^-} \\frac{1}{x}')
		self.assertEqual (ast2tex (p ('\\sum_{n=0}^\\infty x^n/n!')), '\\sum_{n = 0}^\\infty \\frac{x^n}{n!}')
		self.assertEqual (ast2tex (p ('d/dx x**2y**2z')), '\\frac{d}{dx}\\left(x^2 y^2 z \\right)')
		self.assertEqual (ast2tex (p ('d^2/dx^2 x^2y**2z')), '\\frac{d^2}{dx^2}\\left(x^2 y^2 z \\right)')
		self.assertEqual (ast2tex (p ('d^3/dx^2dy x^2y**2z')), '\\frac{\\partial^3}{\\partial x^2\\partial y}\\left(x^2 y^2 z \\right)')
		self.assertEqual (ast2tex (p ('\\partial^4/\\partialx^2\\partial y\\partialz x^2y**2z')), '\\frac{\\partial^4}{\\partial x^2\\partial y\\partial z}\\left(x^2 y^2 z \\right)')
		self.assertEqual (ast2tex (p ('\\int dx')), '\\int \\ dx')
		self.assertEqual (ast2tex (p ('\\int x dx')), '\\int x \\ dx')
		self.assertEqual (ast2tex (p ('\\int_0^1 x dx')), '\\int_0^1 x \\ dx')
		self.assertEqual (ast2tex (p ('\\int_0^1 \\int y dy dx')), '\\int_0^1 \\int y \\ dy \\ dx')
		self.assertEqual (ast2tex (p ('{1,}')), '\\begin{bmatrix} 1 \\end{bmatrix}')
		self.assertEqual (ast2tex (p ('{1,2}')), '\\begin{bmatrix} 1 \\\\ 2 \\end{bmatrix}')
		self.assertEqual (ast2tex (p ('{{1,},}')), '\\begin{bmatrix} 1 \\end{bmatrix}')
		self.assertEqual (ast2tex (p ('{{1,},{2,}}')), '\\begin{bmatrix} 1 \\\\ 2 \\end{bmatrix}')
		self.assertEqual (ast2tex (p ('\\left[\\begin{matrix} 1 \\end{matrix}\\right]')), '\\begin{bmatrix} 1 \\end{bmatrix}')
		self.assertEqual (ast2tex (p ('\\begin{vmatrix} 1 & 2 \\\\ \\end{vmatrix}')), '\\begin{bmatrix} 1 & 2 \\end{bmatrix}')
		self.assertEqual (ast2tex (p ('\\begin{pmatrix} 1 & 2 \\\\ 3 & 4 \\end{pmatrix}')), '\\begin{bmatrix} 1 & 2 \\\\ 3 & 4 \\end{bmatrix}')
		self.assertEqual (ast2tex (p ('{{0,1},{1,0}}**x')), '{\\begin{bmatrix} 0 & 1 \\\\ 1 & 0 \\end{bmatrix}}^x')

	def test_ast2simple (self):
		self.assertEqual (ast2simple (p ('1')), '1')
		self.assertEqual (ast2simple (p ('-1.23456789012345678901234567890123456789012345678901234567890123456789012345678901')), '-1.23456789012345678901234567890123456789012345678901234567890123456789012345678901')
		self.assertEqual (ast2simple (p ('x')), 'x')
		self.assertEqual (ast2simple (p ('-1')), '-1')
		self.assertEqual (ast2simple (p ('-x')), '-x')
		self.assertEqual (ast2simple (p ('(x)')), '(x)')
		self.assertEqual (ast2simple (p ('(x,)')), '(x,)')
		self.assertEqual (ast2simple (p ('(x,y)')), '(x, y)')
		self.assertEqual (ast2simple (p ('[x]')), '[x]')
		self.assertEqual (ast2simple (p ('[x,y]')), '[x, y]')
		self.assertEqual (ast2simple (p ('"x\\x20\\n"')), "'x \\n'")
		self.assertEqual (ast2simple (p ('|x|')), '|x|')
		self.assertEqual (ast2simple (p ('x!')), 'x!')
		self.assertEqual (ast2simple (p ('x+y')), 'x + y')
		self.assertEqual (ast2simple (p ('x-y')), 'x - y')
		self.assertEqual (ast2simple (p ('x*y')), 'xy')
		self.assertEqual (ast2simple (p ('x/y')), 'x/y')
		self.assertEqual (ast2simple (p ('x^y')), 'x**y')
		self.assertEqual (ast2simple (p ('log x')), 'log(x)')
		self.assertEqual (ast2simple (p ('log (x)')), 'log(x)')
		self.assertEqual (ast2simple (p ('log_2 x')), 'log_2(x)')
		self.assertEqual (ast2simple (p ('log_2 (x)')), 'log_2(x)')
		self.assertEqual (ast2simple (p ('sqrt x')), '\\sqrt{x}')
		self.assertEqual (ast2simple (p ('sqrt (x)')), '\\sqrt{x}')
		self.assertEqual (ast2simple (p ('sqrt[3] x')), '\\sqrt[3]{x}')
		self.assertEqual (ast2simple (p ('sqrt[3] (x)')), '\\sqrt[3]{x}')
		self.assertEqual (ast2simple (p ('sin x')), 'sin(x)')
		self.assertEqual (ast2simple (p ('sin^2 x')), 'sin^2(x)')
		self.assertEqual (ast2simple (p ('sin (x)')), 'sin(x)')
		self.assertEqual (ast2simple (p ('sin (x)^2')), 'sin^2(x)')
		self.assertEqual (ast2simple (p ('sin**-1 x')), 'asin(x)')
		self.assertEqual (ast2simple (p ('\\lim_{x\\to0} 1/x')), '\\lim_{x \\to 0} 1/x')
		self.assertEqual (ast2simple (p ('\\lim_{x\\to0^+} 1/x')), '\\lim_{x \\to 0**+} 1/x')
		self.assertEqual (ast2simple (p ('\\lim_{x\\to0**-} 1/x')), '\\lim_{x \\to 0**-} 1/x')
		self.assertEqual (ast2simple (p ('\\sum_{n=0}^\\infty x^n/n!')), '\\sum_{n=0}^oo x**n / n!')
		self.assertEqual (ast2simple (p ('d/dx x**2y**2z')), 'd/dx(x**2y**2z)')
		self.assertEqual (ast2simple (p ('d^2/dx^2 x^2y**2z')), 'd^2/dx**2(x**2y**2z)')
		self.assertEqual (ast2simple (p ('d^3/dx^2dy x^2y**2z')), 'd^3/dx**2dy(x**2y**2z)')
		self.assertEqual (ast2simple (p ('\\partial^4/\\partialx^2\\partial y\\partialz x^2y**2z')), '\\partial ^4/\\partial x**2\\partial y\\partial z(x**2y**2z)')
		self.assertEqual (ast2simple (p ('\\int dx')), '\\int dx')
		self.assertEqual (ast2simple (p ('\\int x dx')), '\\int x dx')
		self.assertEqual (ast2simple (p ('\\int_0^1 x dx')), '\\int_0^1 x dx')
		self.assertEqual (ast2simple (p ('\\int_0^1 \\int y dy dx')), '\\int_0^1 \\int y dy dx')
		self.assertEqual (ast2simple (p ('{1,}')), '{1,}')
		self.assertEqual (ast2simple (p ('{1,2}')), '{1,2}')
		self.assertEqual (ast2simple (p ('{{1,},}')), '{{1,},}')
		self.assertEqual (ast2simple (p ('{{1,},{2,}}')), '{{1,},{2,}}')
		self.assertEqual (ast2simple (p ('\\left[\\begin{matrix} 1 \\end{matrix}\\right]')), '{{1,},}')
		self.assertEqual (ast2simple (p ('\\begin{vmatrix} 1 & 2 \\\\ \\end{vmatrix}')), '{{1,2},}')
		self.assertEqual (ast2simple (p ('\\begin{pmatrix} 1 & 2 \\\\ 3 & 4 \\end{pmatrix}')), '{{1,2},{3,4}}')
		self.assertEqual (ast2simple (p ('{{0,1},{1,0}}**x')), '{{0,1},{1,0}}**x')

	def test_ast2py (self):
		self.assertEqual (ast2py (p ('1')), '1')
		self.assertEqual (ast2py (p ('-1.23456789012345678901234567890123456789012345678901234567890123456789012345678901')), '-1.23456789012345678901234567890123456789012345678901234567890123456789012345678901')
		self.assertEqual (ast2py (p ('x')), 'x')
		self.assertEqual (ast2py (p ('-1')), '-1')
		self.assertEqual (ast2py (p ('-x')), '-x')
		self.assertEqual (ast2py (p ('(x)')), '(x)')
		self.assertEqual (ast2py (p ('(x,)')), '(x,)')
		self.assertEqual (ast2py (p ('(x,y)')), '(x, y)')
		self.assertEqual (ast2py (p ('[x]')), '[x]')
		self.assertEqual (ast2py (p ('[x,y]')), '[x, y]')
		self.assertEqual (ast2py (p ('"x\\x20\\n"')), "'x \\n'")
		self.assertEqual (ast2py (p ('|x|')), 'abs(x)')
		self.assertEqual (ast2py (p ('x!')), 'factorial(x)')
		self.assertEqual (ast2py (p ('x+y')), 'x + y')
		self.assertEqual (ast2py (p ('x-y')), 'x - y')
		self.assertEqual (ast2py (p ('x*y')), 'x*y')
		self.assertEqual (ast2py (p ('x/y')), 'x/y')
		self.assertEqual (ast2py (p ('x^y')), 'x**y')
		self.assertEqual (ast2py (p ('log x')), 'log(x)')
		self.assertEqual (ast2py (p ('log (x)')), 'log(x)')
		self.assertEqual (ast2py (p ('log_2 x')), 'log(x) / log(2)')
		self.assertEqual (ast2py (p ('log_2 (x)')), 'log(x) / log(2)')
		self.assertEqual (ast2py (p ('sqrt x')), 'sqrt(x)')
		self.assertEqual (ast2py (p ('sqrt (x)')), 'sqrt(x)')
		self.assertEqual (ast2py (p ('sqrt[3] x')), 'x**(1/3)')
		self.assertEqual (ast2py (p ('sqrt[3] (x)')), 'x**(1/3)')
		self.assertEqual (ast2py (p ('sin x')), 'sin(x)')
		self.assertEqual (ast2py (p ('sin^2 x')), 'sin(x)**2')
		self.assertEqual (ast2py (p ('sin (x)')), 'sin(x)')
		self.assertEqual (ast2py (p ('sin (x)^2')), 'sin(x)**2')
		self.assertEqual (ast2py (p ('sin**-1 x')), 'asin(x)')
		self.assertEqual (ast2py (p ('\\lim_{x\\to0} 1/x')), "Limit(1/x, x, 0, dir='+-')")
		self.assertEqual (ast2py (p ('\\lim_{x\\to0^+} 1/x')), 'Limit(1/x, x, 0)')
		self.assertEqual (ast2py (p ('\\lim_{x\\to0**-} 1/x')), "Limit(1/x, x, 0, dir='-')")
		self.assertEqual (ast2py (p ('\\sum_{n=0}^\\infty x^n/n!')), 'Sum(x**n / factorial(n), (n, 0, oo))')
		self.assertEqual (ast2py (p ('d/dx x**2y**2z')), 'Derivative(x**2*y**2*z, x)')
		self.assertEqual (ast2py (p ('d^2/dx^2 x^2y**2z')), 'Derivative(x**2*y**2*z, x, 2)')
		self.assertEqual (ast2py (p ('d^3/dx^2dy x^2y**2z')), 'Derivative(x**2*y**2*z, x, 2, y)')
		self.assertEqual (ast2py (p ('\\partial^4/\\partialx^2\\partial y\\partialz x^2y**2z')), 'Derivative(x**2*y**2*z, x, 2, y, z)')
		self.assertEqual (ast2py (p ('\\int dx')), 'Integral(1, x)')
		self.assertEqual (ast2py (p ('\\int x dx')), 'Integral(x, x)')
		self.assertEqual (ast2py (p ('\\int_0^1 x dx')), 'Integral(x, (x, 0, 1))')
		self.assertEqual (ast2py (p ('\\int_0^1 \\int y dy dx')), 'Integral(Integral(y, y), (x, 0, 1))')
		self.assertEqual (ast2py (p ('{1,}')), 'Matrix([[1]])')
		self.assertEqual (ast2py (p ('{1,2}')), 'Matrix([[1],[2]])')
		self.assertEqual (ast2py (p ('{{1,},}')), 'Matrix([[1]])')
		self.assertEqual (ast2py (p ('{{1,},{2,}}')), 'Matrix([[1],[2]])')
		self.assertEqual (ast2py (p ('\\left[\\begin{matrix} 1 \\end{matrix}\\right]')), 'Matrix([[1]])')
		self.assertEqual (ast2py (p ('\\begin{vmatrix} 1 & 2 \\\\ \\end{vmatrix}')), 'Matrix([[1,2]])')
		self.assertEqual (ast2py (p ('\\begin{pmatrix} 1 & 2 \\\\ 3 & 4 \\end{pmatrix}')), 'Matrix([[1,2],[3,4]])')
		self.assertEqual (ast2py (p ('{{0,1},{1,0}}**x')), 'Matrix([[0,1],[1,0]])**x')

	# def test_ast2spt (self):
	# 	self.assertEqual (ast2spt (p ('1')), r'')
	# 	self.assertEqual (ast2spt (p ('-1.23456789012345678901234567890123456789012345678901234567890123456789012345678901')), r'')
	# 	self.assertEqual (ast2spt (p ('x')), r'')
	# 	self.assertEqual (ast2spt (p ('-1')), r'')
	# 	self.assertEqual (ast2spt (p ('-x')), r'')
	# 	self.assertEqual (ast2spt (p ('(x)')), r'')
	# 	self.assertEqual (ast2spt (p ('(x,)')), r'')
	# 	self.assertEqual (ast2spt (p ('(x,y)')), r'')
	# 	self.assertEqual (ast2spt (p ('[x]')), r'')
	# 	self.assertEqual (ast2spt (p ('[x,y]')), r'')
	# 	self.assertEqual (ast2spt (p ('"x\\x20\\n"')), r'')
	# 	self.assertEqual (ast2spt (p ('|x|')), r'')
	# 	self.assertEqual (ast2spt (p ('x!')), r'')
	# 	self.assertEqual (ast2spt (p ('x+y')), r'')
	# 	self.assertEqual (ast2spt (p ('x-y')), r'')
	# 	self.assertEqual (ast2spt (p ('x*y')), r'')
	# 	self.assertEqual (ast2spt (p ('x/y')), r'')
	# 	self.assertEqual (ast2spt (p ('x^y')), r'')
	# 	self.assertEqual (ast2spt (p ('log x')), r'')
	# 	self.assertEqual (ast2spt (p ('log (x)')), r'')
	# 	self.assertEqual (ast2spt (p ('log_2 x')), r'')
	# 	self.assertEqual (ast2spt (p ('log_2 (x)')), r'')
	# 	self.assertEqual (ast2spt (p ('sqrt x')), r'')
	# 	self.assertEqual (ast2spt (p ('sqrt (x)')), r'')
	# 	self.assertEqual (ast2spt (p ('sqrt[3] x')), r'')
	# 	self.assertEqual (ast2spt (p ('sqrt[3] (x)')), r'')
	# 	self.assertEqual (ast2spt (p ('sin x')), r'')
	# 	self.assertEqual (ast2spt (p ('sin^2 x')), r'')
	# 	self.assertEqual (ast2spt (p ('sin (x)')), r'')
	# 	self.assertEqual (ast2spt (p ('sin (x)^2')), r'')
	# 	self.assertEqual (ast2spt (p ('sin**-1 x')), r'')
	# 	self.assertEqual (ast2spt (p ('\\lim_{x\\to0} 1/x')), r'')
	# 	self.assertEqual (ast2spt (p ('\\lim_{x\\to0^+} 1/x')), r'')
	# 	self.assertEqual (ast2spt (p ('\\lim_{x\\to0**-} 1/x')), r'')
	# 	self.assertEqual (ast2spt (p ('\\sum_{n=0}^\\infty x^n/n!')), r'')
	# 	self.assertEqual (ast2spt (p ('d/dx x**2y**2z')), r'')
	# 	self.assertEqual (ast2spt (p ('d^2/dx^2 x^2y**2z')), r'')
	# 	self.assertEqual (ast2spt (p ('d^3/dx^2dy x^2y**2z')), r'')
	# 	self.assertEqual (ast2spt (p ('\\partial^4/\\partialx^2\\partial y\\partialz x^2y**2z')), r'')
	# 	self.assertEqual (ast2spt (p ('\\int dx')), r'')
	# 	self.assertEqual (ast2spt (p ('\\int x dx')), r'')
	# 	self.assertEqual (ast2spt (p ('\\int_0^1 x dx')), r'')
	# 	self.assertEqual (ast2spt (p ('\\int_0^1 \\int y dy dx')), r'')
	# 	self.assertEqual (ast2spt (p ('{1,}')), r'')
	# 	self.assertEqual (ast2spt (p ('{1,2}')), r'')
	# 	self.assertEqual (ast2spt (p ('{{1,},}')), r'')
	# 	self.assertEqual (ast2spt (p ('{{1,},{2,}}')), r'')
	# 	self.assertEqual (ast2spt (p ('\\left[\\begin{matrix} 1 \\end{matrix}\\right]')), r'')
	# 	self.assertEqual (ast2spt (p ('\\begin{vmatrix} 1 & 2 \\\\ \\end{vmatrix}')), r'')
	# 	self.assertEqual (ast2spt (p ('\\begin{pmatrix} 1 & 2 \\\\ 3 & 4 \\end{pmatrix}')), r'')

_EXPRESSIONS = """
1
-1.23456789012345678901234567890123456789012345678901234567890123456789012345678901
x
-1
-x
(x)
(x,)
(x,y)
[x]
[x,y]
"x\\x20\\n"
|x|
x!
x+y
x-y
x*y
x/y
x^y
log x
log (x)
log_2 x
log_2 (x)
sqrt x
sqrt (x)
sqrt[3] x
sqrt[3] (x)
sin x
sin^2 x
sin (x)
sin (x)^2
sin**-1 x
\\lim_{x\\to0} 1/x
\\lim_{x\\to0^+} 1/x
\\lim_{x\\to0**-} 1/x
\\sum_{n=0}^\\infty x^n/n!
d/dx x**2y**2z
d^2/dx^2 x^2y**2z
d^3/dx^2dy x^2y**2z
\\partial^4/\\partialx^2\\partial y\\partialz x^2y**2z
\\int dx
\\int x dx
\\int_0^1 x dx
\\int_0^1 \\int y dy dx
{1,}
{1,2}
{{1,},}
{{1,},{2,}}
\\left[\\begin{matrix} 1 \\end{matrix}\\right]
\\begin{vmatrix} 1 & 2 \\\\ \\end{vmatrix}
\\begin{pmatrix} 1 & 2 \\\\ 3 & 4 \\end{pmatrix}
{{0,1},{1,0}}**x
"""

if __name__ == '__main__':
	import os.path
	import subprocess
	import sys

	if len (sys.argv) == 1:
		subprocess.run ([sys.executable, '-m', 'unittest', os.path.basename (sys.argv [0])])
		sys.exit (0)

	elif sys.argv [1] == '--print':
		exprs = [s.strip () for s in _EXPRESSIONS.strip ().split ('\n')]

		for func in (ast2tex, ast2simple, ast2py):
			print ()
			print (f'def test_{func.__name__} (self):')

			for expr in exprs:
				print (f'self.assertEqual ({func.__name__} (p ({expr!r})), {func (p (expr))!r})')
