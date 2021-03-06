#!/usr/bin/env python3
# python 3.6+

# Randomized CONSISTENCY testing of parsing vs. writing: text -> ast -> tex/nat/py -> ast -> tex/nat/py

from getopt import getopt
from random import random, randint, randrange, choice
import math
import string
import sys
import time

from sast import AST
import sast
import spatch
import sxlat
import sym
import sparser

_STATIC_TERMS = [
	'0',
	'1',
	'-1',
	'1.0',
	'-1.0',
	'.1',
	'-.1',
	'1.',
	'2',
	'1e-100',
	'1e100',
	'1e+100',
	'a',
	'b',
	'c',
	'x'
	'y'
	'z'
	'd',
	'dx',
	'dy',
	'dz',
	'x0',
	'y1',
	'z20',
	'w_{1}',
	'partial',
	'partialx',
	'\\partial ',
	'\\partialx',
	'\\partial x',
	'\\partialy',
	'oo',
	'\\infty '
	'zoo',
	'\\tilde\\infty ',
	"'s'",
	'"s"',
	'None',
	'True',
	'False',
	'\\emptyset',
]

# previously problematic static test expressions

_EXPRESSIONS = r"""
\sqrt[{{1} / {1.0}}]{({oo},{partial})}
sqrt{{-1.0}**{0}}
{{\frac{1.0}{dx}} \cdot {{partial} / {partialx}} \cdot {{d} >= {oo}}}
\frac{{partial}**{1}}{{{partialx}*{dx}*{1.0}}}
{{\frac{1.0}{partialx}} \cdot {\exp({0},{a})} \cdot {{{d}+{oo}}}}
{\arcsin({-1.0},{dx},{oo})}^{{d} <= {-1}}
({{d}**{1}},{\arcsech({partial},{partial})})
Limit ({d} > {-1.0}, x, {{1.0}*{partial}*{dx}})
{{d}^{1}} / {{{dx}  {oo}}}
{{{d}*{1}}} / {partial^{5} / partialy^{1} partialy^{2} partialz^{2} {oo}}
{{{0}!} \cdot {partial^{1} / partialx^{1} {dx}} \cdot {{d}**{d}}}
{{partial^{4} / partialy^{3} partialy^{1} {a}} \cdot {{'s'}^{d}}}
{\int {-1} dx} / {\int {1} dx}
{\int_{dx}^{a} {-1} dx}!
\int {partial^{3} / partialy^{3} {a}} dx
{{\int {partial} dx}  {partial^{4} / partialy^{1} partialz^{1} partialz^{2} {a}}}
\int_{[{-1.0}]}^{\int {partialx} dx} {{{oo}+{-1}}} dx
\int_{partial^{6} / partialy^{2} partialx^{2} partialz^{2} {partialx}}^{partial^{4} / partialz^{1} partialz^{2} partialx^{1} {0}} {{a} != {'s'}} dx
{{{oo}**{'s'}}+{\int {oo} dx}+{partial^{7} / partialz^{3} partialx^{2} partialx^{2} {0}}}
[{{{-1} \cdot {oo}}},{{{dx},{1.0},{oo}}},{partial^{8} / partialx^{3} partialx^{2} partialz^{3} {oo}}]
{{lambda x, y, z: {1}}+{{1.0} > {1.0}}+{{oo} / {'s'}}}
{{lambda: {-1}} \cdot {\frac{partialx}{oo}} \cdot {{1.0} if {1} else {a} if {0}}}
{{{a} / {-1}} {\lim_{x \to partial} {-1}} * [lambda x, y, z: {partialx}]}
\int_{\sqrt[{a}]{1.0}}^{[]} {lambda x: {partialx}} dx
lambda x: {{dx} = {dx}}
\int {{{{a} / {dx}}  {partial^{2} / partialz^{2} {partialx}}}} dx
\int \frac{d}{dx} x dx
\int d / dx x dx
\int_{{partial^{4} / partialx^{1} partialy^{3} {partial}}**{\sqrt[{oo}]{0}}}^{{{{-1} == {0}}*{({partial},{'s'},{a})}*{{1} / {1}}}} {-{partial^{6} / partialy^{3} partialx^{3} {0}}} dx
\int {-{partial^{6} / partialy^{3} partialx^{3} {0}}} dx
\lim_{x \to \frac{lambda x, y, z: {-{0}}}{partial^{5} / partialz^{2} partialz^{1} partialx^{2} {Limit (a, x, 1)}}} {\arctan()}
-{{{{{{partialx},{partial},{oo},},{{dx},{-1.0},{a},},}}**{StrictGreaterThan({1.0})}} > {partial^{4} / partialz^{1} partialx^{2} partialy^{1} {{1.0}^{1}}}}
-{{{{{\sum_{x = 0}^{-1.0} {oo}} \cdot {({0})}}},}}
\int {{{{d}+{partialx}+{1}}} if {lambda x, y, z: {a}} else {{1} / {partialx}}} dx
{|{\log_{partial^{1} / partialy^{1} {{{0}*{'s'}}}}{[{{-1.0} / {'s'}}]}}|}
{\lim_{x \to -1.0} {dx}} > {{oo} if {-1.0} else {d} if {d} else {1}}
\frac{{-1.0} > {oo}}{\ln{-1.0}}
{{|{d}|}{{({1.0},{1})},{[{oo}]},},}
1/2 * {a+b} [lambda: {d}]
{{{'s'} < {1.0}} \cdot {({a})} \cdot {{1} if {a}}}
-{1.0 if partial else d if 1 else oo if 1.0 else 's'}
{partial^{5} / partialy^{2} partialy^{2} partialy^{1} {partial}}^{{-1.0} > {d}}
{lambda x: {a}} if {{{'s'}*{a}*{1}}}
\int_{{-1.0} <= {1}}^{-{1}} {{-1.0} <= {1.0}} dx
{{({a1.0})}+{{a}!}+{{d} if {1} else {dx}}}
\int_{{{a}+{a}+{0}}}^{{'s'} / {a}} {\int {1} dx} dx
lambda x: {lambda x, y: {oo}}
\sqrt[3]{({oo},{a})}
Limit (\sum_{x = oo}^{partial} {-1.0}, x, \sec({-1.0},{-1},{partialx}))
{{a} = {partial}} if {{{oo}+{0}+{-1}}} else {\int {a} dx}
\sum_{x = {{1}*{d}*{oo}}}^{\exp({a},{1})} {\log_{1.0}{a}}
lambda x: {{a} = {dx}}
{{{d}^{oo}}*{{a}^{d}}}
{{oo} if {oo}} = {is_mersenne_prime({'s'})}
\lim_{x \to 0} {sqrt(dx) + [lambda x, y: -1.0]}
{{\frac{\int_{a}^{1} {dx} dx}{{{oo} \cdot {d} \cdot {dx}}}}}
# \int d/dx dx
(((-1)**partial)**({a_prime, oo, 's'}))**-{-{0}}
Limit ({{{0}^{'s'}}  {\left|{a}\right|}  {({a},{a})}}, x, lambda x: {{1}!})
\left(\left(\text{'s'} \right)! \le \left(\left(x, y \right) \mapsto -1.0 \right) \right) == \int_{\left[-1.0, \partial, -1 \right]}^{\log_{-1.0}\left(-1 \right)} \begin{cases} 1 & \text{for}\: \infty \\ 1.0 & \text{for}\: 1.0 \end{cases} \ dx
x^{-{{1} / {1.0}}}
cofactors( 1 , {lambda x: 1 = lambda: 2} )
({{{-{cse()}},{{{{partial} != {-1}}*{{{-1.0}  {1.0}}}}},{lambda: {{-1.0} == {dx}}},},{{\lim_{x \to \log_{0}{d}} {[{-1.0}]}},{partial^{7} / partialx^{3} partialy^{1} partialx^{3} {{partialx} if {a} else {-1.0} if {a} else {d} if {1.0} else {partialx}}},{{lambda x, y, z: {oo}} = {\tanh()}},},{{partial^{3} / partialz^{3} {{oo} / {'s'}}},{({{{\left|{dx}\right|},{{a} if {d}},},{{-{oo}},{({{-1.0},{oo},{-1.0},})},},})},{partial^{5} / partialx^{1} partialy^{1} partialz^{3} {{-1}!}},},})
{\left|{a}\right|} if {\int {'s'} dx} else {({-1},{-1},{a})} if {\left|{1.0}\right|}
{lambda x: {{1.0} if {oo} else {1.0} if {oo}}} = {{{{partial} \cdot {partialx}}}**{{a}!}}
{Sum (\int {1} dx, (x, 0, 1))} dx
{{\sum_{x = \left|{0}\right|}^{\tan({-1.0})} {\int_{partialx}^{oo} {d} dx}}+{{{\lim_{x \to 1} {d}} \cdot {{{a}+{-1}+{dx}}}}}+{{{{a} = {a}}+{({dx0d})}+{{{dx}*{dx}*{a}}}}}}
log(partialx*'s'*partialx) / log(Derivative(a, z, 3, y, 2))
dpartial
a, lambda: b = 1
\exp({a},{-1},{1})
x, y = lambda: 1, lambda: 2
doo
Sum(a*Integral(x, x), (x, 0, 1)) + 1*dx
(dx**p*artial)*Limit(sqrt(-1), x, 0**d)[(Matrix([[partialx]])), lcm_list()]
ln((a)**b)
a * \int dx + {\int dx dx}
1 if {a = x if z} else 0 if y
a, lambda: b = 1
a * [2]
sqrt(1, 2)
x*[][y]
lambda: x:
a*[x][y][z]
a*()**2
a*().t
a*()[2]
lambda*x:2
lambda*x, y:2
d**2e0/dx**2e0 x**3
y**z [w]
{y**z} [w]
x {y**z} [w]
{x y**z} [w]
\sqrt[{lambda x, y, z: {ConditionSet()}}]{x}
{1:2:3}[2]
{1:2:3}.x
None**-1.0**\[[\emptyset,],[0,],[\partial x,],] / {not \[None,\emptyset,]}
\int_{\lim_{x \to 1} oo^{not 1e100}}^\{{partialx+dx},{\partialx*.1},partialx!} \log_{\left|partialx\right|}{1 \cdot False} dx
{{\[[{{\emptyset} = {.1}},{\[[{\emptyset},],[{"s"},],]},],]} if {-{{\partial x}!}} else {{{{False}!} and {{{\partial x}||{oo}||{"s"}}}}}}
{\int {{{{{1e-100}  {1}  {partialx}}}*{{True}^{\tilde\infty }}}} dx}
{{{{-{"s"}} : {lambda x, y: {\partialx}}} \cdot {{not {{'s'} : {1.} : {.1}}}}}}
{-{-1}}^{{1} : {\partial x} : {0}}
{{{\sum_{x = {{a} : {"s"} : {True}}}^{({\partial x})} {[]}}||{{{1.0} : {False} : {\emptyset}} [{{-1} == {\partialx}}]}||{{{{oo} if {None} else {\partialx}}^^{{.1} [{oo}]}}}}}
{lambda x, y, z: {lambda x, y: {{{-1.0}&&{False}&&{d}}}}}
\int {{\partialx} : {d} : {1.0}} dx
{\lim_{x \to {{1} : {1e+100} : {.1}}} {({\partial x},{\partialx})}}
x + {-1 2}
x + {-1 * 2}
x - {{1 2} 3}
x - {{1 * 2} * 3}
{sqrt{{{{not {1.}}}+{\int_{a}^{-1.0} {s} dx}+{{{-1} \cdot {1e100} \cdot {\infty zoo}}}}}}
x - a b!
\int x * \frac{y}{z} \ dx
1+{{-1 * 2}+1}
-1 * a
x - y! ()
-x * a!
a * {-b} * c
a * {-b} c
--1 * x
---1 * x
a**{-1 [y]}
-{\int x dx} + y * dz
{z = x <= y} in [1, 2]
\int_a^b {d != c} dx
\int_a^b {d = c} dx
{a in b} not in c
a*()!
\frac12.and ()
lambda: a or lambda: b
{{a in b} * y} in z
\[]
\[[]]
\[[], []]
\{a:b}
{-x} y / z
d / dz {-1} a
1 / {-2} x
\sum_{x=0}^b {-x} y
\lim_{x\to0} {-x} y
\int a / -1 dx
\[[[x]]]
\[[[1, 2]], [[3]]]
\sqrt(a:b)
\sqrt[3](a:b)
{z : v,c : z,0 : u = {lambda x, y: a}}
a.inverse_mellin_transform()
a**b.c {x * y}!
\int x / --1 dx
\lim_{x \to a = {lambda: c}} b
?f (x, y, real = True)
Function ('f', real = True) (x, y)
a [b]'
a.b ()'
{x/y}'
1'['ac']
|x|'
| 's'|'
{x**y}'
{{-1}'}
{a [b]}''
1.'''
2y - 3/2 * x
2y + -3/2 * x
2y - -3/2 * x
2y + {-3/2} * x
2y + {-3/2 * x}
x - y z
x + -y z
x - -y z
x + {-y} z
x - {-y} z
x + {-y z}
x - {-y z}
1 / -2 x
-1''' {d/dx x}
x + -{1 + -1}
x + -1'
1 * -1'
x * [y]'
x * [y].a
x!' + ('s')
|x|' + ('s')
{x^y'}'
sin{x}!
sin{x}'
\sqrt{-\partial x  d^{5} / dx^{2} dy^{3} "s"  \{0}}'
\int a b - 1 dx
\int {a b - 1} dx
a * [b]!'
{\sum_{x=y}^z x} / -{d/dx x}
Sum (x, (x, y, z)) / -{a/b}
{-a / z}'
a * [b]' [c]
a * [a]!' [b]
a * [a]! [b]
a * [a].a [b]
a * [a].a' [b]
a * [a].a!' [b]
False * ()'
-{1!}
-{1'}
-{1 [b]}
-{1 [b] [c]}
-{a [b]}
-{a [b] [c]}
{x in y} {1 : 2 : 3}
x^{-{a and b}}
x^{-{a or b}}
x^{-{a || b}}
x^{-{a && b}}
x^{-{a ^^ b}}
{x if 2 else z} b^c
x^{a = b}
{{\sqrt[{?(x, y, reals = False, commutative = False)}]{{.1} = {\emptyset}}} \cdot {{{partialx}||{oo}}  {{dy}||{'s'}}} \cdot {{Derivative ({dx}, x, 1)} \cdot {{dy}^^{1.}^^{dx}} \cdot {Limit ({dy}, x, {None})}}}
{\frac{\sqrt{[{.1},{\partial },{1e100}]}}{{{\partialy} / {b}}  {{\partialx}+{\partialx}}  {{-1}**{True}}}}
{\frac{{not {1e-100}}  {{a}**{False}}}{{{partial}||{True}||{1.0}}&&{{b} / {a}}&&{{\partial x}!}}}
1 / {a in b}
{a * -1} {lambda: 2}
\frac{d\partial x}{dx}
partial / partialx \partial x
-{{1 [2]} c}
{{{?h(x, y, z)},{{{partialx}'''}^^{{1e100} or {1}}^^{{}}},{log{lambda x, y: {1.0}}}}}
sin (x) {a b / c}
{{{{-1.0}**{a}}^{{\partialy} [{c}, {partial}]}}*{{\sqrt{\tilde\infty }}*{\log_{'s'}{1.}}*{-{dz}}}}
Derivative ({partial}, x, 1)
Derivative ({\partial}, x, 1)
Derivative ({\partial x}, x, 1)
None {x = y}
{d / y} * a
{{-1.0} = {1.}} and {{True}+{False}} and {{\infty zoo} = {-1.0}}
a * \log_{2}{a} [x]
{a = b} * c^d
{lambda x: 1}**{-{x in b}}
{\[[{{{oo} : {\tilde\infty }}  not in  {Limit ({c}, x, {a})}},{\[{{\tilde\infty }||{\infty zoo}},]},],[{acoth()},{{{1} if {False} else {2} if {\partialy} else {0} if {-1.0}} \cdot {{xyzd}&&{1.0}&&{b}} \cdot {not {-1}}},],[{{{\partialx} if {"s"} else {0} if {\partialx} else {partial} if {1e100}}*{{xyzd}*{partial}}*{\int {False} dx}},{\int_{{2} [{\partialx}]}^{{"s"} and {1.} and {oo}} {[]} dx},],]}
{\int_{Derivative ({\[{0},{\emptyset},]}, z, 2, z, 2)}^{not {lambda: {-1.0}}} {{{dx} or {1}}**{{2}  not in  {None}}} dx}
{\{{{{1.}  in  {a}}  {{{1e-100}}}  {{a} = {-1.0}}},{{besselk({a},{\partialy},{1e-100})}''},{{Limit ({dx}, x, {False})}  {\frac{1e-100}{.1}}}}}
{\int_{{{-1.0}''}||{\int_{None}^{.1} {dz} dx}||{{\tilde\infty }+{None}}}^{{\lim_{x \to {oo}} {\partial }}**{{1.0}**{1e+100}}} {{-{-1}}^{{1.} == {\partialx} == {\emptyset} < {dx}}} dx}
{{?(x, y)} = {{\[{1e-100},]}||{{\tilde\infty }^{'s'}}}}
{{{{-1}^^{c}} [{{1e+100}+{1e+100}}, {{True}**{0}}]}**{-{not {1e-100}}}}
{{\gcd({\sum_{x = {-1.0}}^{\partial x} {\emptyset}})}**{-{{False}+{2}}}}
{{{d^{6} / dx^{3} dy^{3} {'s'}}+{{False}  {dz}}}**{-{{\partial x} = {\partial }}}}
{\sqrt[{-{\log_{partialx}{1e+100}}}]{{{.1} if {1e+100}}*{{b} \cdot {b}}}}
sqrt[log_2{x}]2
{{{?f()}**{{"s"} = {1e+100}}} = {{-1.0 : {Derivative ({1e100}, z, 1, x, 1, x, 2)},oo : {{}},1e-100 : {{1e100}^{\tilde\infty }}}}}
{{LeviCivita({?h(x, y, reals = False, commutative = False)},{{{partial},{\partial }}})}**{{Limit ({\emptyset}, x, {b})}+{{1.0}!}+{{"s"}'}}}
{partialx : {\partial x : \emptyset,-1 : 1e-100},\partial  : (oo,False)} : \lim_{x \to partialx = \emptyset} lambda x, y, z: "s" : \{}
{{-{{b} [{\tilde\infty }, {dx}]}}**{-{lambda x, y, z: {\partialy}}}}
{{\min({{None}*{0}},{{True : {1e100},0 : {None},\partial  : {2}}})}^{-{{b} : {.1} : {partialx}}}}
a in {-{b in c}}
-{{1'}!}
\ln(((a)))
\sqrt(((a)))
\ln{({(a, b, c)})}
Limit(x:1, a, b)
{-\partialx} / \partialy
Sum (x, (x, a, a : b))
-{Derivative (x, x) {a in b}}
\int dx dx / dx
b = dx [?h(x, y)]^lambda x, y, z: True!
dy / dx / 2
Sum ({2 \cdot {1 x} \cdot {\int_y^x {dy} dx}}, (x, 0, 1)) * 1
1 if True else 3 if True else 4
1 if True else 3 if True
1 if True else 3
1 if True
# |x, y|
# |lambda: 1|
# |lambda x: 1|
# |lambda x, y: 1|
x:None
1 and {-{a * b} + 2}
a in -(1)
:c:
x::
a {b : c : None}
\sqrt[-{2}]{a}
\int_0^1 {x:y:None} dx
a : b : (None)
log\left|None+xyzd\right| - (1e+100)
Limit (1, x, 1) || a in x if True
not lambda x, y, z: partialx! or -ln1.or lambda x: .1' or [Sum (1e+100, (x, 1, \infty zoo))&&\int 1e100 dx]
-v1.or lambda: 1
\sum_{x = a, b}^n 1
1+1. 1. [None]**2
0 1\left[x \right]**2
lambda x, y, z: ln lambda x: None
\int \gamma dx
gamma * x
x^{gamma} y
{d/dx y}.a
{y'}.a
a.b\_c
{a**b}.c
{a!}.b
a.b c.d
{\log_2 b}.c
a * \log_2 b
{\lambda: x}
{-\lambda: x}
{a = \lambda: x}
{a != \lambda: x}
{a, \lambda: x}
{a - \lambda: x}
{a + \lambda: x}
{a * \lambda: x}
{a / \lambda: x}
{a ^ \lambda: x}
{a || \lambda: x}
{a ^^ \lambda: x}
{a && \lambda: x}
{a or \lambda: x}
{a and \lambda: x}
{not \lambda: x}
N lambda: x
\int {2**gamma} dx
\ln\partialx[.1,z20,\Omega]/"s"!||z20>=oo>2.924745719942591e-14||2.B1Cxzr().sUCb()/{None:lambdax,y,z:(10900247533345.432:dy:),\tilde\infty:False+x0&&\int"s"dx,1:\{}/\partial**b}
sqrt\[Lambda[dx,0,b][:\lambda:1e-100,\alpha1,\{}],]
None:1:,c:a
-a.b{1:None,w:b,a:c}!
\sqrt[a]\sqrt a [x]
\sqrt[x]\{}**1[-1]
\sqrt[a](:)[b]**c
\left|a\right|**-1.00[a]**b
a**\sqrt[b]-1e+1[c]
|a|**[a][b].c
sin(b)tan(a)**1[c].d
{b,c}**2[d].a()
sin(a)^h(x)*sin()
\{}**'s'[b].c[d]
sin(a)^2 sin(c)
1 a**f(x)
a**?f(x)
a**?f(x).a
a**?f(x)[0]
f({x})'
-f({x})'
a^\frac{partialx}\partialx
a^\lambda*lambdax:1
x**?f(x,y).a^1
(LambertW(5.194664222299675e-09[1e100]=-4.904486369506518e-17*\lambda*a,lambdax,y,z:\emptyset'''))
x**?g(x)**x
a**?f(x)^a'
a**?f(x)^b^c
a**?f(x)'
a / c \int dx * d/dx a
d/dx a \lambda:
f(d/dx 1,x)
f(ln(2))
\sum_{x=0}^1 0.f()\int0dD + 1
a:b^\Lambda(True,1)
a**-\sqrt[b]1[c]
notassoc_legendre(Pi_{44},-1.0),z20=phi,1e+100*1e100*theta*variations()
a = {::b}, c
\partialx / \partial \partial
dx / dd
partial\theta
\.\.a|_{b=c}|_{d=e}
a**\.b[c]|_{x=1}
{d / dx (f(x))(0)} [1]
a*d/dx(h(x))(0)
\. {\. a |_{x = 1}} |_{c = d}
FiniteSet()**1[b].c
ln**2 lambda: 1
sin(v)**[a][b].c
a * d / dx (f(x,y))(0,1).c
a * d / dx (h(x))(0)''
a.b(((c)))
a[((()))]
a[(:)]
\[a]**b[c][d].e
\.x|_{x=(:)}
\.x|_{x=(sin x)}
\.x|_{(x)=sin x}
\.x|_{(1,2)=y}
\.x|_{(((1,2),))=y}
\.x|_{(((1,2)),)=y}
inverse_mell in_transform(())
1 e100a**2
?(),w_{1}=\psi*\sum_{x=1e+100}^partia lxNone/$ZDv()*oo\cdot"s"\cdot.1orTrue,c,dy\cdot{{{1e-100notin1.0,\sum_{x=1}^5530110.904839005c}}}
\. \int x dx |_{x=1}
a**{d/dx(f(x))(0)}
\int {\lim_{x \to 1} x} dy
\int {\sum_{x = 1}^2 x} dy
{d/dx (u(x))(0)}.a
x / {d / dx (f(x))(0)}
\int {dy}+{-1} dx
{{d/dx (f(real = True)(x))(0)}'} [a]
{\int_{Derivative ({\[{0},{\emptyset},]}, z, 2, z, 2)}^{not {lambda: {-1.0}}} {{{dx} or {1}}**{{2}  not in  {None}}} dx}
\int {dy**a}**c {dz} dx
\frac{a\int x dx}b
a**b[1]**(1/3)**c
{?(x)'(0)}'
\int {\frac{1}{a \lim_{x\to2} y}} dx
\int {dz < 3} dx
a**{-{d/dx (g(x))(0)}}
partialx/\partialy(x,real=True)(0)
{a \int -1 dx} / 2
{a / b \int x dx} c
{\sqrt{lambda: 1}}.a{\sqrt{lambda: 1}}.a
1 / {{d/dx (g(x))(0)} a}
Function('f', positive = True)(x, real = True)
\left. x \right|_{{f(x, commutative = True)} = 1}
{a \int x dx / c}*b
{( {\frac{ { { \tilde\infty  } or { a } or { c } }+{ d^{5} / dz^{2} dz^{1} dy^{2} { b } } }{ -{ not { \lambda } } } } :  :  )}
a / { -{d/dx (?f(x))(0)}}
{\int x dx a + b * c + d}
{\int x dx * a + b * c + d}
\int^{a dx b} x dx
\int {d**2 / dx dx (f(0))} dx
\int {d**2 / dy dx (?f(x, y))(0, 1)} dx
{\int { d^{1} / dz^{1} ({d**3 / dx dx dx g(commutative = True)(x, y)(0, 1)}) } dZ }
\int {{d / dy dy dx a} [dz]} dx
\frac{a}{b}*{{{{xx}'}^c}!}
\int a**N dx
{  : {\int { { {\[{ 's' },{ dy },{ \beta },]} \cdot { { -9.712711016258549e-12 }  { Gamma }  { -1.0 } } \cdot { { 0 } && { 6.222789060821971e-22 } } }*{ d^{4} / dz^{1} dz^{2} dy^{1} {\sum_{x = { x0 }}^{ .1 } { 2.040706058303616e-14 } } } } dz } }
sin (a b = c)
x.y (a b = c)
\. a, b |_{x = 1}
ln(1).or lambda: 1
\$()*{a**b}
""".strip ().split ('\n')

_LETTERS         = string.ascii_letters
_LETTERS_NUMBERS = _LETTERS + '_' + string.digits

def _randidentifier ():
	while 1:
		s = f'{choice (_LETTERS)}{"".join (choice (_LETTERS_NUMBERS) for _ in range (randint (0, 6)))}{choice (_LETTERS)}'

		if not (s in sparser.RESERVED_ALL or s [:2] == 'd_' or s [:8] == 'partial_' or (s [:1] == 'd' and s [1:] in sparser.RESERVED_ALL) or (s [:7] == 'partial' and s [7:] in sparser.RESERVED_ALL)):
			break

	return s

def term_num ():
	return f' {str (math.exp (random () * 100 - 50) * (-1 if random () >= 0.5 else 1))} '

_TERM_VARS = sast.AST_Var.GREEK + tuple ('\\' + g for g in sast.AST_Var.GREEK) + tuple (sast.AST_Var.PY2TEXMULTI.keys ())

def term_var ():
	return f' {choice (_TERM_VARS)}{f"_{{{randint (0, 100)}}}" if random () < 0.25 else ""} '

def expr_semicolon ():
	return '; '.join (expr () for _ in range (randrange (2, 5)))

def expr_ass ():
	return f'{expr ()} = {expr ()}'

def expr_in ():
	s = expr ()

	for _ in range (randrange (1, 4)):
		s = s + f' {choice (["in", "not in"])} {expr ()}'

	return s

def expr_cmp (): # this gets processed and possibly reordered in sxlat
	s = expr ()

	for _ in range (randrange (1, 4)):
		s = s + f' {choice (["==", "!=", "<", "<=", ">", ">="])} {expr ()}'

	return s

def expr_attr ():
	return f' {expr ()}{"".join (f".{_randidentifier ()}" + ("()" if random () >= 0.5 else "") for _ in range (randint (1, 3)))} '

def expr_comma ():
	return f" {','.join (f'{expr ()}' for _ in range (randint (2, 3)))} "

def expr_curly ():
	s = ','.join (f'{expr ()}' for _ in range (randint (1, 3))) if random () < 0.8 else ''

	for _ in range (randint (1, 3)):
		s = f'{{{s}}}'

	return s

def expr_paren ():
	s = ','.join (f'{expr ()}' for _ in range (randint (1, 3))) if random () < 0.8 else ''

	for _ in range (randint (1, 3)):
		s = f'({s})'

	return s

def expr_brack ():
	s = ','.join (f'{expr ()}' for _ in range (randint (1, 3))) if random () < 0.8 else ''

	for _ in range (randint (1, 3)):
		s = f'[{s}]'

	return s

def expr_abs ():
	return f'\\left|{expr ()}\\right|'

def expr_minus ():
	return f' -{expr ()} '

def expr_fact ():
	return f' {expr ()}! '

def expr_add ():
	return f" {'+'.join (f'{expr ()}' for i in range (randrange (2, 4)))} "

def expr_mul_imp ():
	return f" {'  '.join (f'{expr ()}' for i in range (randrange (2, 4)))} "

def expr_mul_exp ():
	return f" {'*'.join (f'{expr ()}' for i in range (randrange (2, 4)))} "

def expr_mul_cdot ():
	return ' ' + ' \\cdot '.join (f'{expr ()}' for i in range (randrange (2, 4))) + ' '

def expr_div ():
	return f' {expr ()} / {expr ()} '

def expr_frac ():
	return f'\\frac{expr ()}{expr ()} '

def expr_caret ():
	return f' {expr ()}^{expr ()} '

def expr_dblstar ():
	return f' {expr ()}**{expr ()} '

def expr_log ():
	return \
			choice ([' ', '\\']) + f'{choice (["ln", "log"])}{expr ()} ' \
			if random () >= 0.5 else \
			f'\\log_{expr ()}{expr ()} '

def expr_sqrt ():
	return \
			choice ([' ', '\\']) + f'sqrt{expr ()} ' \
			if random () >= 0.5 else \
			f'\\sqrt[{expr ()}]{expr ()} '

_FORBIDDEN_SXLAT_FUNCS = set (sxlat.XLAT_FUNC2AST_TEX) | set (sxlat.XLAT_FUNC2AST_NAT) | set (sxlat.XLAT_FUNC2AST_PY) | set (sxlat._XLAT_FUNC2TEX) | {'Gamma', 'digamma', 'idiff'}

def expr_func ():
	while 1:
		py = choice (list (AST.Func.PY))

		if py not in _FORBIDDEN_SXLAT_FUNCS:
			break

	while 1:
		tex = choice (list (AST.Func.TEX))

		if tex not in _FORBIDDEN_SXLAT_FUNCS:
			break

	return \
			'\\' + f'{tex}{expr_paren ()}' \
			if random () >= 0.5 else \
			f' {py}{expr_paren ()}' \

def expr_lim ():
	return \
			'\\lim_{x \\to ' + f'{expr ()}}} {expr ()} ' \
			# if random () >= 0.5 else \
			# f'Limit ({expr ()}, x, ({expr ()}))'

def expr_sum ():
	return \
			'\\sum_{x = ' + f'{expr ()}}}^{expr ()} {expr ()} ' \
			# if random () >= 0.5 else \
			# f'Sum ({expr ()}, (x, {expr ()}, {expr ()}))'

def expr_diff ():
	d  = choice (['d', 'partial'])
	p  = 0
	dv = []

	for _ in range (randrange (1, 4)):
		n  = randrange (1, 4)
		p += n

		dv.append ((choice (['x', 'y', 'z']), n))

	diff = expr () if random () < 0.5 else f'({expr ()})'

	return \
			f' {d}^{{{p}}} / {" ".join (f"{d + v}^{{{dp}}}" for v, dp in dv)} {diff} ' \
			# if random () >= 0.5 else \
			# f'Derivative ({expr ()}, {", ".join (f"{v}, {dp}" for v, dp in dv)})'

def expr_diffp ():
	return f"""{expr ()}{"'" * randrange (1, 4)}"""

def expr_intg ():
	dv = f'd{_randidentifier () if random () >= 0.5 else choice (_LETTERS)}'

	if random () >= 0.5:
		return f'\\int_{expr ()}^{expr ()} {expr ()} {dv} '
	else:
		return f'\\int {expr ()} {dv} '

def expr_vec ():
	return '\\[' + ','.join (f'{expr ()}' for i in range (randrange (1, 4))) + ',]'

def expr_mat ():
	cols = randrange (1, 4)

	return '\\[' + ','.join ('[' + ','.join (f'{expr ()}' for j in range (cols)) + ',]' for i in range (randrange (1, 4))) + ',]'

def expr_piece ():
	p = [f' {expr ()} if {expr ()} ']

	for _ in range (randrange (3)):
		p.append (f' else {expr ()} if {expr ()} ')

	if random () >= 0.5:
		p.append (f' else {expr ()} ')

	return ' '.join (p)

def expr_lamb ():
	return f' lambda{choice (["", " x", " x, y", " x, y, z"])}: {expr ()} '

def expr_idx ():
	if random () >= 0.5:
		return f' {expr ()} [{expr ()}]'
	elif random () >= 0.5:
		return f' {expr ()} [{expr ()}, {expr ()}]'
	else:
		return f' {expr ()} [{expr ()}, {expr ()}, {expr ()}]'

def expr_slice ():
	start, stop, step = expr ().replace ('None', 'C'), expr ().replace ('None', 'C'), expr ().replace ('None', 'C')

	if random () >= 0.5:
		ret = f' {choice ([start, ""])} : {choice ([stop, ""])} '
	else:
		ret = f' {choice ([start, ""])} : {choice ([stop, ""])} : {choice ([step, ""])} '

	return ret if random () >= 0.5 else f'{{{ret}}}' if random () >= 0.5 else f'({ret})'

def expr_set ():
	return '\\{' + ','.join (f'{expr ()}' for i in range (randrange (4))) + '}'

def expr_dict ():
	return f" {' {' + ','.join (f'{expr ()} : {expr ()}' for i in range (randrange (4))) + '}'} "

def expr_union ():
	return f" {' || '.join (f'{expr ()}' for i in range (randrange (2, 4)))} "

def expr_sdiff ():
	return f" {' ^^ '.join (f'{expr ()}' for i in range (randrange (2, 4)))} "

def expr_xsect ():
	return f" {' && '.join (f'{expr ()}' for i in range (randrange (2, 4)))} "

def expr_or ():
	return f" {' or '.join (f'{expr ()}' for i in range (randrange (2, 4)))} "

def expr_and ():
	return f" {' and '.join (f'{expr ()}' for i in range (randrange (2, 4)))} "

def expr_not ():
	return f' not {expr ()} '

def expr_ufunc ():
	name = choice (('', 'f', 'g', 'h', 'u'))
	vars = choice (((), ('x',), ('x', 'y'), ('x', 'y', 'z')))
	kw   = (() if random () < 0.8 else ('real = True',)) + (() if random () < 0.8 else ('commutative = True',))

	if random () < 0.25:
		s = f"Function({name!r}, {', '.join (kw)})({', '.join (vars)})"

	else:
		q = '?' if not name or random () < 0.25 else ''

		if random () < 0.5:
			s = f"{q}{name}({', '.join (kw)})({', '.join (vars)})"
		else:
			s = f"{q}{name}({', '.join (vars + kw)})"

	if len (vars) == 1 and random () < 0.2:
		s = s + choice (("'", "''", "'''"))

	elif vars and random () < 0.5:
		p = randint (1, 3)
		d = f"d{f'**{p}' if p > 1 else ''} / {' '.join (f'd{choice (vars)}' for _ in range (randint (1, 3)))}"
		s = f'{d} {s}' if random () < 0.25 else f'{d} ({s})'

	if vars and random () < 0.5:
		s = f"{s}({', '.join (str (i) for i in range (len (vars)))})"

	return s

def expr_subs ():
	t = [(expr (), expr ()) for _ in range (randint (1, 3))]
	r = randrange (3)

	if r == 0:
		s = ', '.join (f'{s} = {d}' for s, d in t)
	elif r == 1:
		s = f"{', '.join (s for s, d in t)} = {', '.join (d for s, d in t)}"
	else:
		s = '\\substack{' + ' \\\\ '.join (f'{s} = {d}' for s, d in t) + '}'

	if random () < 0.5:
		return f'\\. {expr ()} |_{{{s}}}'
	else:
		return f'\\left. {expr ()} \\right|_{{{s}}}'
	# else: Subs ()

def expr_sym ():
	name = _randidentifier () if random () < 0.95 else ''
	kw   = (() if random () < 0.5 else ('real = True',)) + (() if random () < 0.5 else ('commutative = True',))

	if random () < 0.25:
		return f"Symbol({name!r}, {', '.join (kw)})"
	else:
		return f"${name}({', '.join (kw)})"

#...............................................................................................
DEPTH  = 0 # pylint snack
EXPRS  = [va [1] for va in filter (lambda va: va [0] [:5] == 'expr_', globals ().items ())]
TERMS  = [va [1] for va in filter (lambda va: va [0] [:5] == 'term_', globals ().items ())]
CURLYS = True # if False then intentionally introduces grammatical ambiguity to test consistency in those cases

def expr_term ():
	ret = choice (TERMS) () if random () < 0.2 else f' {choice (_STATIC_TERMS)} '

	return f'{{{ret}}}' if CURLYS else ret

def expr ():
	global DEPTH

	if DEPTH <= 0:
		return expr_term ()

	else:
		DEPTH -= 1
		ret    = choice (EXPRS) ()
		DEPTH += 1

	return f'{{{ret}}}' if CURLYS else ret

#...............................................................................................
parser = sparser.Parser ()

sym.set_pyS (False)

def parse (text, retprepost = False):
	t0  = time.process_time ()
	ret = parser.parse (text)
	t   = time.process_time () - t0

	if t > 2:
		print ()
		print (f'Slow parse {t}s: \n{text}', file = sys.stderr)

	if not ret [0] or ret [1] or ret [2]:
		return None

	return (ret [0], ret [0].pre_parse_postprocess) if retprepost else ret [0]

def test (argv = None):
	global DEPTH, CURLYS

	funcs = {'N', 'O', 'S', 'beta', 'gamma', 'Gamma', 'Lambda', 'zeta'}

	sym.set_sym_user_funcs (funcs)
	sparser.set_sp_user_funcs (funcs)
	sym.set_strict (True)

	# sxlat._SX_XLAT_AND = False # turn off py And translation because it mangles things

	depth   = 3
	single  = None
	quick   = False
	topexpr = None
	opts, _ = getopt (sys.argv [1:] if argv is None else argv, 'tnpiqScd:e:E:', ['tex', 'nat', 'py', 'dump', 'show', 'se', 'showerr', 'inf', 'infinite', 'nc', 'nocurlys', 'ns', 'nospaces', 'rs', 'randomspaces', 'tp', 'transpose', 'quick', 'nopyS', 'cross', 'depth=', 'expr=', 'topexpr='])

	if ('-q', '') in opts or ('--quick', '') in opts:
		parser.set_quick (True)
		quick = True

	if ('-S', '') in opts or ('--nopyS', '') in opts:
		sym.set_pyS (False)

	for opt, arg in opts:
		if opt in ('-d', '--depth'):
			depth = int (arg)
		elif opt in ('-e', '--expr'):
			single = [arg]
		elif opt in ('-E', '--topexpr'):
			topexpr = globals ().get (f'expr_{arg}')

	if topexpr is None:
		topexpr = expr
	else:
		EXPRS.remove (topexpr)

	if ('--dump', '') in opts:
		DEPTH = 0

		for e in EXPRS:
			print (e ())

		sys.exit (0)

	dotex     = ('--tex', '') in opts or ('-t', '') in opts
	donat     = ('--nat', '') in opts or ('-n', '') in opts
	dopy      = ('--py', '') in opts or ('-p', '') in opts
	showerr   = ('--se', '') in opts or ('--showerr', '') in opts
	CURLYS    = not (('--nc', '') in opts or ('--nocurlys', '') in opts)
	spaces    = not (('--ns', '') in opts or ('--nospaces', '') in opts)
	rndspace  = ('--rs', '') in opts or ('--randomspaces', '') in opts
	transpose = ('--tp', '') in opts or ('--transpose', '') in opts
	show      = ('--show', '') in opts
	infinite  = (('-i', '') in opts or ('--inf', '') in opts or ('--infinite', '') in opts)
	docross   = ('--cross', '') in opts or ('-c', '') in opts

	if not (dotex or donat or dopy):
		dotex = donat = dopy = True

	if infinite and not single:
		expr_func = (lambda: topexpr ()) if spaces else (lambda: topexpr ().replace (' ', ''))
	else:
		expr_func = iter (single or filter (lambda s: s [0] != '#', _EXPRESSIONS)).__next__

	try:
		while 1:
			def validate (ast): # validate ast rules have not been broken by garbling functions
				if not isinstance (ast, AST):
					return ast

				if ast.is_var:
					if ast.var in sparser.RESERVED_ALL or ast.var_name.startswith ('_'):
						return AST ('@', 'C')

				if ast.is_func: # the slice function is evil
					if ast.func == 'slice' and ast.args.len == 2 and ast.args [0] == AST.None_: # :x gets written as slice(x) but may come from slice(None, x)
						ast = AST ('-slice', AST.None_, ast.args [1], None)
					elif ast.func in _FORBIDDEN_SXLAT_FUNCS: # random spaces can create forbidden functions
						ast = AST ('-func', 'print', *ast [2:])

				elif ast.is_diff: # reserved words can make it into diff via dif or partialelse
					if any (v [0] in sparser.RESERVED_ALL for v in ast.dvs):
						return AST ('@', 'C')

				elif ast.is_intg: # same
					if ast.dv.as_var.var in sparser.RESERVED_ALL:
						return AST ('@', 'C')

				elif ast.is_slice: # the slice object is evil
					if ast.start == AST.None_ or ast.stop == AST.None_ or ast.step == AST.None_:
						raise ValueError ('malformed slice')
						# ast = AST ('-slice', ast.start, ast.stop, None)

				elif ast.is_ufunc: # remove spaces inserted into ufunc name
					if ' ' in ast.ufunc:
						ast = AST ('-ufunc', ast.ufunc_full.replace (' ', ''), ast.vars, ast.kw)

				elif ast.is_subs:
					if ast.expr.is_comma:
						ast = AST ('-subs', ('(', ast.expr), ast.subs)

				elif ast.is_sym: # remove spaces inserted into ufunc name
					if ' ' in ast.sym:
						ast = AST ('-sym', ast.sym.replace (' ', ''), ast.kw)

				return AST (*(validate (a) for a in ast))

			def check_double_curlys (ast):
				if not isinstance (ast, AST):
					return False
				elif ast.is_curly and ast.curly.is_curly:
					return True

				return any (check_double_curlys (a) for a in ast)

			# start here
			status = []
			DEPTH  = depth
			text   = expr_func ()

			if text and infinite and not single and rndspace: # insert a random space to break shit
				i    = randrange (0, len (text))
				text = f'{text [:i]} {text [i:]}'

			if transpose: # transpose random block of text to another location overwriting that location
				s0, s1, d0, d1 = (randrange (len (text)) for _ in range (4))
				s0, s1         = sorted ((s0, s1))
				d0, d1         = sorted ((d0, d1))
				text           = text [:d0] + text [s0 : s1] + text [d1:]

			status.append (f'text: {text}')
			ast = parse (text) # fixstuff (parse (text))
			status.append (f'ast:  {ast}')

			err = None

			if not ast:
				if single or (not infinite and not quick) or showerr:
					err = ValueError ("error parsing")

			if ast and not err:
				try:
					ast2 = validate (ast)

				except Exception as e: # make sure garbling functions did not create an invalid ast
					if single or showerr:
						err = e
					else:
						ast = None

			if ast and not err:
				if ast2 != ast:
					status.append (f'astv: {ast2}')

					ast = ast2

				if dopy and any (a.is_ass for a in (ast.scolon if ast.is_scolon else (ast,))): # reject assignments at top level if doing py because all sorts of mangling goes on there, we just want expressions in that case
					if single or showerr:
						err = ValueError ("disallowed assignment")
					else:
						ast = None

			if err or not ast:
				if err and not showerr:
					raise err

				if showerr:
					print (f'\n{text} ... {err}')

				continue

			if show:
				print (f'{text}\n')

			sxlat._SX_XLAT_AND = False # turn off py And translation because it mangles things

			for rep in ('tex', 'nat', 'py'):
				if locals () [f'do{rep}']:
					symfunc     = getattr (sym, f'ast2{rep}')

					status.append (f'sym.ast2{rep} ()')

					text1       = symfunc (ast)
					status [-1] = f'{rep}1: {" " if rep == "py" else ""}{text1}'

					status.append ('parse ()')

					rast, rpre  = parse (text1, retprepost = True) # fixstuff (parse (text1))

					if not rast:
						raise ValueError (f"error parsing")

					if check_double_curlys (rpre):
						status [-1] = f'astd: {rpre}'

						raise ValueError ("doubled curlys")

					status [-1:] = [f'ast:  {rast}', f'sym.ast2{rep} ()']
					text2        = symfunc (rast)
					status [-1]  = f'{rep}2: {" " if rep == "py" else ""}{text2}'

					if text2 != text1:
						raise ValueError ("doesn't match")

					del status [-3:]

			if docross and dotex + donat + dopy > 1:
				def sanitize (ast): # prune or reformat information not encoded same across different representations and asts which are not possible from parsing
					if not isinstance (ast, AST):
						return ast

					# elif ast.is_ass:
					# 	return AST ('<>', sanitize (AST ('(', ast.lhs) if ast.lhs.is_comma else ast.lhs), (('==', sanitize (AST ('(', ast.rhs) if ast.rhs.is_comma else ast.rhs)),))

					elif ast.is_minus:
						if ast.minus.is_num_pos:
							return AST ('#', f'-{ast.minus.num}')

					elif ast.is_paren:
						if not ast.paren.is_comma:
							return sanitize (ast.paren)

					elif ast.is_mul:
						return AST ('*', tuple (sanitize (a) for a in ast.mul))

					elif ast.is_log:
						return AST ('-log', sanitize (ast.log))

					elif ast.is_sqrt:
						return AST ('-sqrt', sanitize (ast.rad))

					elif ast.is_func:
						if ast.func == 'And':
							args = sanitize (ast.args)
							ast2 = sxlat._xlat_f2a_And (*args, force = True)

							if ast2 is not None:
								ast = ast2
							else:
								return AST ('-and', args)

					elif ast.is_sum:
						if ast.from_.is_comma:
							return AST ('-sum', sanitize (ast.sum), ast.svar, sanitize (AST ('(', ast.from_) if ast.from_.is_comma else ast.from_), ast.to)

					elif ast.is_diff:
						if len (set (dv [0] for dv in ast.dvs)) == 1 and ast.is_diff_partial:
							return AST ('-diff', sanitize (ast.diff), 'd', ast.dvs)

					elif ast.is_intg:
						if ast.intg is None:
							return AST ('-intg', AST.One, *tuple (sanitize (a) for a in ast [2:]))

					elif ast.is_piece:
						if ast.piece [-1] [1] == AST.True_:
							ast = AST ('-piece', ast.piece [:-1] + ((ast.piece [-1] [0], True),))

						if ast.piece.len == 1 and ast.piece [0] [1] is True:
							ast = ast.piece [0] [0]

					elif ast.is_slice:
						ast = AST ('-slice', False if ast.start == AST.None_ else ast.start, False if ast.stop == AST.None_ else ast.stop, AST ('@', 'C') if ast.step == AST.None_ else False if ast.step is None else ast.step)

					elif ast.is_and:
						args = sanitize (ast.and_)
						ast2 = sxlat._xlat_f2a_And (*args, force = True)

						if ast2 is not None:
							ast = ast2

					elif ast.is_ufunc:
						if ast.is_ufunc_explicit:
							ast = AST ('-ufunc', ast.ufunc, *ast [2:])

					return AST (*tuple (sanitize (a) for a in ast))#, **ast._kw)

				sxlat._SX_XLAT_AND = True # turn on py And translation because it is needed here

				# start here
				ast = sanitize (ast)
				status.append (f'ast:  {ast}')

				if dotex:
					tex1 = sym.ast2tex (ast)
					status.append (f'tex1: {tex1}')
					ast2 = ast = sanitize (parse (tex1)).flat

					if donat:
						status.append (f'ast:  {ast2}')
						nat  = sym.ast2nat (ast2)
						status.append (f'nat:  {nat}')
						ast2 = parse (nat)

					if dopy:
						try:
							sym._SYM_MARK_PY_ASS_EQ = True # allow xlat of marked Eq functions which indicate assignment in python text

							status.append (f'ast:  {ast2}')
							py   = sym.ast2py (ast2, ass2cmp = False)
							status.append (f'py:   {py}')
							ast2 = parse (py)

						finally:
							sym._SYM_MARK_PY_ASS_EQ = False # allow xlat of marked Eq functions which indicate assignment in python text

					try:
						if dopy:
							sxlat._SX_READ_PY_ASS_EQ = True # allow xlat of marked Eq functions which indicate assignment in python text

						status.append (f'ast:  {ast2}')
						tex2 = sym.ast2tex (ast2)
						status.append (f'tex2: {tex2}')
						ast2 = sanitize (parse (tex2)).flat

					finally:
						sxlat._SX_READ_PY_ASS_EQ = False # allow xlat of marked Eq functions which indicate assignment in python text

				elif donat: # TODO: add more status updates for intermediate steps like above
					nat1 = sym.ast2nat (ast)
					status.append (f'nat1: {nat1}')
					ast2 = ast = sanitize (parse (nat1)).flat

					try:
						sym._SYM_MARK_PY_ASS_EQ = True # allow xlat of marked Eq functions which indicate assignment in python text

						status.append (f'ast:  {ast2}')
						py   = sym.ast2py (ast2, ass2cmp = False)
						status.append (f'py:   {py}')
						ast2 = parse (py)

					finally:
						sym._SYM_MARK_PY_ASS_EQ = False # allow xlat of marked Eq functions which indicate assignment in python text

					try:
						sxlat._SX_READ_PY_ASS_EQ = True # allow xlat of marked Eq functions which indicate assignment in python text

						status.append (f'ast:  {ast2}')
						nat2 = sym.ast2nat (ast2)
						status.append (f'nat2: {nat2}')
						ast2 = sanitize (parse (nat2)).flat

					finally:
						sxlat._SX_READ_PY_ASS_EQ = False # allow xlat of marked Eq functions which indicate assignment in python text

				if ast2 != ast:
					status.extend ([f'ast:  {ast2}', f'org:  {ast}'])

					raise ValueError ("doesn't match across representations")

	except (KeyboardInterrupt, StopIteration):
		pass

	except:
		print ('Exception!\n')
		print ('\n'.join (status))
		print ()

		raise

	finally:
		sxlat._SX_XLAT_AND = True

	return True

if __name__ == '__main__':
	# test ('-d4 --nc --ns --rs --tp --quick --showerr'.split ())
	# test (['-c', '-e', r"""{{\int { { log{ oo } }+{ { 1e+100 } \cdot { \Omega } }+{ { \infty zoo }^{ \zeta } } } dS }'}"""])
	# test (['--quick', '--showerr'])
	# test ([])
	test ()
