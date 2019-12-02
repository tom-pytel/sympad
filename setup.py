#!/usr/bin/env python3

import setuptools

setuptools.setup (
  name                          = "sympad",
  version                       = "1.1",
  author                        = "Tomasz Pytel",
  author_email                  = "tom_pytel@yahoo.com",
  license                       = 'BSD',
  keywords                      = "Math CAS SymPy GUI",
  description                   = "Graphical symbolic math calculator / scratchpad using SymPy",
  long_description              = "SymPad is a simple single script graphical symbolic calculator / scratchpad using SymPy for the math, MathJax for the display in a browser and matplotlib for plotting. "
    "User input is intended to be quick, easy and intuitive and is displayed in symbolic form as it is being entered. "
    "Sympad will accept Python expressions, LaTeX formatting, unicode math symbols and a native shorthand intended for quick entry, or a mix of all of these. "
    "The input will be evaluated symbolically or numerically with the results being copy/pasteable in Python or LaTeX formats, so it acts as a translator as well.",
  long_description_content_type = "text/plain",
  url                           = "https://github.com/Pristine-Cat/sympad",
  packages                      = ['sympad'],
  scripts                       = ['bin/sympad'],
  classifiers                   = [
    'Intended Audience :: Education',
    'Intended Audience :: Science/Research',
    'License :: OSI Approved :: BSD License',
    'Operating System :: OS Independent',
    'Programming Language :: Python',
    'Programming Language :: Python :: 3',
    'Programming Language :: Python :: 3 :: Only',
    'Topic :: Scientific/Engineering',
    'Topic :: Scientific/Engineering :: Mathematics',
  ],
  install_requires              = ['sympy>=1.4'],
  python_requires               = '>=3.6',
)