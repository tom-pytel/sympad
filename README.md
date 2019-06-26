# SymPad

SymPad is a simple symbolic math calculator using SymPy for the math and MathJax for the display in a web browser. It runs as a private web server on your machine and executes the system default browser pointing to itself on startup.
User input is intended to be quick, easy and intuitive. Sympad will accept LaTeX math formatting as well as Python-ish expressions and evaluate the result symbolically or numerically. The following are all valid inputs:
```
2*x**2
2x^2
sin (x) / cos (y)
\frac{\sin x}{\cos y}
sqrt[3] 27
\tan**{-1} x
\lim_{x \to 0^-} 1/x
\sum_{n=0}^\infty x**n / n!
d/dx x**2
\int_0^1 x dx
```

## Open-Source License

SymPad is made available under the BSD license, you may use it as you wish, as long as you copy the BSD statement if you redistribute it (see the LICENSE file for details).
