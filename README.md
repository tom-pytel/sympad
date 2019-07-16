# SymPad

SymPad is a simple single script symbolic calculator / scratchpad using SymPy for the math and MathJax for the display in a browser.
User input is intended to be quick, easy and intuitive and is displayed in symbolic form as it is being entered.
Sympad will accept Python expressions as well as LaTeX math formatting (or a mix) as input and evaluate those symbolically or numerically with the results being copy/pasteable in Python or LaTeX formats, so it acts as a translator as well.

The following are examples of valid inputs to SymPad:
```
cos**-1 x
\log_2{8}
\lim_{x\to\infty} 1/x
Limit (\frac1x, x, 0, dir='-')
\sum_{n=0}**oo x^n / n!
d**6 / dx dy**2 dz**3 x^3 y^3 z^3
Derivative (\int dx, x)
Integral (e^{-x^2}, (x, 0, \infty))
\int_0^\infty e^{-s t} dt
{{1,2},{3,4}}**-1
\begin{matrix} A & B \\ C & D \end{matrix} * {x, y}
{{1,2,3},{4,5,6}}.transpose ()
expand {x+1}**4
factor (x^3 + 3x^2 + 3x + 1)
series (e^x, x, 0, 5)
x if 1 < 2 else y
```

And they look like this while typing:

![SymPad image example](https://raw.githubusercontent.com/Pristine-Cat/SymPad/master/sympad.png)

## Installation

If you just want to use the program you only need the **sympad.py** file - along with the SymPy Python package installed on your system of course: [https://sympy.org/](https://sympy.org/).
This is an autogenerated Python script which contains all the modules and web resources in one handy easily copyable file.

Otherwise if you want to play with the code then download everything and run the program using **server.py**.

If you want to regenerate the parser tables you will need the PLY Python package: [https://www.dabeaz.com/ply/](https://www.dabeaz.com/ply/).

## Open-Source License

SymPad is made available under the BSD license, you may use it as you wish, as long as you copy the BSD statement if you redistribute it. See the LICENSE file for details.
