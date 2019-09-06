# Plot functions and expressions to image using matplotlib.

import base64
from io import BytesIO
import itertools as it
import math

import sympy as sp

_SPLOT = False

try:
	import matplotlib
	import matplotlib.pyplot as plt

	matplotlib.style.use ('bmh') # ('seaborn') # ('classic') # ('fivethirtyeight')

	_SPLOT       = True
	_FIGURE      = None
	_TRANSPARENT = True

except:
	pass

#...............................................................................................
def _cast_num (arg):
	try:
		return float (arg)
	except:
		return None

def _process_head (obj, args, fs, style = None, ret_xrng = False, ret_yrng = False, kw = {}):
	global _FIGURE, _TRANSPARENT

	if style is not None:
		if style [:1] == '-':
			style, _TRANSPARENT = style [1:], True
		else:
			_TRANSPARENT = False

		matplotlib.style.use (style)

	args = list (reversed (args))

	if args and args [-1] == '+': # continuing plot on previous figure?
		args.pop ()

	elif _FIGURE:
		plt.close (_FIGURE)

		_FIGURE = None

	if not _FIGURE:
		_FIGURE = plt.figure ()

	if fs is not None: # process figsize if present
		if isinstance (fs, (sp.Tuple, tuple)):
			fs = (_cast_num (fs [0]), _cast_num (fs [1]))

		else:
			fs = _cast_num (fs)

			if fs >= 0:
				fs = (fs, fs * 3 / 4)
			else:
				fs = (-fs, -fs)

		_FIGURE.set_figwidth (fs [0])
		_FIGURE.set_figheight (fs [1])

	xmax, ymin, ymax = None, None, None
	xmin             = _cast_num (args [-1]) if args else None

	if xmin is not None: # process xmin / xmax, ymin, ymax if present
		args = args [:-1]
		xmax = _cast_num (args [-1]) if args else None

		if xmax is not None:
			args = args [:-1]
			ymin = _cast_num (args [-1]) if args else None

			if ymin is not None:
				args = args [:-1]
				ymax = _cast_num (args [-1]) if args else None

				if ymax is not None:
					args = args [:-1]
				else:
					xmin, xmax, ymin, ymax = -xmin, xmin, xmax, ymin
		else:
			xmin, xmax = -xmin, xmin

	if xmin is not None:
		obj.xlim (xmin, xmax)
	elif ret_xrng:
		xmin, xmax = obj.xlim ()

	if ymin is not None:
		obj.ylim (ymin, ymax)
	elif ret_yrng:
		ymin, ymax = obj.ylim ()

	kw = dict ((k, # cast certain SymPy objects which don't play nice with matplotlib using numpy
		int (v) if isinstance (v, sp.Integer) else
		float (v) if isinstance (v, (sp.Float, sp.Rational)) else
		v) for k, v in kw.items ())

	return args, xmin, xmax, ymin, ymax, kw

def _process_fmt (args, kw = {}):
	kw    = kw.copy ()
	fargs = []

	if args and isinstance (args [-1], str):
		fmt, lbl = (args.pop ().split ('=', 1) + [None]) [:2]
		fmt, clr = (fmt.split ('#', 1) + [None]) [:2]

		if lbl:
			kw ['label'] = lbl.strip ()

		if clr:
			clr = clr.strip ()

			if len (clr) == 6:
				try:
					_   = int (clr, 16)
					clr = f'#{clr}'
				except:
					pass

			kw ['color'] = clr

		fargs = [fmt.strip ()]

	if args and isinstance (args [-1], dict):
		kw.update (args.pop ())

	return args, fargs, kw

def _figure_to_image ():
	data = BytesIO ()

	_FIGURE.savefig (data, format = 'png', bbox_inches = 'tight', facecolor = 'none', edgecolor = 'none', transparent = _TRANSPARENT)

	return base64.b64encode (data.getvalue ()).decode ()

#...............................................................................................
def plotf (*args, fs = None, res = 12, style = None, **kw):
	"""Plot function(s), point(s) and / or line(s).

plotf ([+,] [limits,] *args, fs = None, res = 12, **kw)

limits  = set absolute axis bounds: (default x is (0, 1), y is automatic)
  x              -> (-x, x, y auto)
  x0, x1         -> (x0, x1, y auto)
  x, y0, y1      -> (-x, x, y0, y1)
  x0, x1, y0, y1 -> (x0, x1, y0, y1)

fs      = set figure figsize if present: (default is (6.4, 4.8))
  x      -> (x, x * 3 / 4)
  -x     -> (x, x)
  (x, y) -> (x, y)

res     = minimum target resolution points per 50 x pixels (more or less 1 figsize x unit),
          may be raised a little to align with grid
style   = optional matplotlib plot style

*args   = functions and their formatting: (func, ['fmt',] [{kw},] func, ['fmt',] [{kw},] ...)
  func                      -> callable function takes x and returns y
	(x, y)                    -> point at x, y
	(x0, y0, x1, y1, ...)     -> connected lines from x0, y1 to x1, y1 to etc...
	((x0, y0), (x1, y1), ...) -> same thing

	fmt                       = 'fmt[#color][=label]'
	"""

	if not _SPLOT:
		return None

	obj    = plt
	legend = False

	args, xmin, xmax, ymin, ymax, kw = _process_head (obj, args, fs, style, ret_xrng = True, kw = kw)

	while args:
		arg = args.pop ()

		if isinstance (arg, (sp.Tuple, tuple, list)): # list of x, y coords
			if isinstance (arg [0], (sp.Tuple, tuple, list)):
				arg = list (it.chain.from_iterable (arg))

			pargs = [arg [0::2], arg [1::2]]

		else: # y = function (x)
			if not callable (arg):
				if len (arg.free_symbols) != 1:
					raise ValueError ('expression must have exactly one free variable')

				arg = sp.Lambda (arg.free_symbols.pop (), arg)

			win = _FIGURE.axes [-1].get_window_extent ()
			xrs = (win.x1 - win.x0) // 50 # scale resolution to roughly 'res' points every 50 pixels
			rng = res * xrs
			dx  = dx2 = xmax - xmin

			while dx2 < (res * xrs) / 2: # align sampling grid on integers and fractions of integers while rng stays small enough
				rng = int (rng + (dx2 - (rng % dx2)) % dx2)
				dx2 = dx2 * 2

			xs = [xmin + dx * i / rng for i in range (rng + 1)]
			ys = [None] * len (xs)

			for i in range (len (xs)):
				try:
					ys [i] = _cast_num (arg (xs [i]))
				except (ValueError, ZeroDivisionError, FloatingPointError):
					pass

			# remove lines crossing graph vertically due to poles (more or less)
			if ymin is not None:
				for i in range (1, len (xs)):
					if ys [i] is not None and ys [i-1] is not None:
						if ys [i] < ymin and ys [i-1] > ymax:
							ys [i] = None
						elif ys [i] > ymax and ys [i-1] < ymin:
							ys [i] = None

			pargs = [xs, ys]

		args, fargs, kwf = _process_fmt (args, kw)
		legend           = legend or ('label' in kwf)

		obj.plot (*(pargs + fargs), **kwf)

	if legend or 'label' in kw:
		obj.legend ()

	return _figure_to_image ()

#...............................................................................................
def __fxfy2fxy (f1, f2): # u = f1 (x, y), v = f2 (x, y) -> (u, v) = f' (x, y)
	return lambda x, y, f1 = f1, f2 = f2: (float (f1 (x, y)), float (f2 (x, y)))

def __fxy2fxy (f): # (u, v) = f (x, y) -> (u, v) = f' (x, y)
	return lambda x, y, f = f: tuple (float (v) for v in f (x, y))

def __fdy2fxy (f): # v/u = f (x, y) -> (u, v) = f' (x, y)
	return lambda x, y, f = f: tuple ((math.cos (t), math.sin (t)) for t in (math.atan2 (f (x, y), 1),)) [0]

def _process_funcxy (args, testx, testy):
	isdy = False
	f    = args.pop ()

	if isinstance (f, (sp.Tuple, tuple, list)): # if (f1 (x, y), f2 (x, y)) functions or expressions present in args they are individual u and v functions
		c1, c2 = callable (f [0]), callable (f [1])

		if c1 and c2: # two Lambdas
			f = __fxfy2fxy (f [0], f [1])

		elif not (c1 or c2): # two expressions
			vars = tuple (sorted (sp.Tuple (f [0], f [1]).free_symbols, key = lambda s: s.name))

			if len (vars) != 2:
				raise ValueError ('expression must have exactly two free variables')

			return args, __fxfy2fxy (sp.Lambda (vars, f [0]), sp.Lambda (vars, f [1])), False

		else:
			raise ValueError ('field must be specified by two lambdas or two expressions, not a mix')

	# one function or expression
	if not callable (f): # convert expression to function
		if len (f.free_symbols) != 2:
			raise ValueError ('expression must have exactly two free variables')

		f = sp.Lambda (tuple (sorted (f.free_symbols, key = lambda s: s.name)), f)

	for y in testy: # check if returns 1 dy or 2 u and v values
		for x in testx:
			try:
				v = f (x, y)
			except (ValueError, ZeroDivisionError, FloatingPointError):
				continue

			try:
				_, _ = v
				f    = __fxy2fxy (f)

				break

			except:
				f    = __fdy2fxy (f)
				isdy = True

				break

		else:
			continue

		break

	return args, f, isdy

_plotv_clr_mag  = lambda x, y, u, v: math.sqrt (u**2 + v**2)
_plotv_clr_dir  = lambda x, y, u, v: math.atan2 (v, u)

_plotv_clr_func = {'mag': _plotv_clr_mag, 'dir': _plotv_clr_dir}

#...............................................................................................
def plotv (*args, fs = None, res = 13, resw = 1, style = None, **kw):
	"""Plot vector field.

plotv (['+',] [limits,] func, [color,] [fmt,] [*walks,] res = 13, resw = 1, style = None, **kw)

limits  = set absolute axis bounds: (default x is (0, 1), y is automatic)
  x              -> (-x, x, y auto)
  x0, x1         -> (x0, x1, y auto)
  x, y0, y1      -> (-x, x, y0, y1)
  x0, x1, y0, y1 -> (x0, x1, y0, y1)

fs      = set figure figsize if present: (default is (6, 4))
  x      -> (x, x / 6 * 4)
  -x     -> (x, x)
  (x, y) -> (x, y)

res     = (w, h) number of arrows across x and y dimensions, if single digit then h will be w*3/4
resw    = resolution for optional walkq, see walkq for meaning
style   = optional matplotlib plot style

func    = function or two functions or expressions returning either (u, v) or v/u
	f (x, y)               -> returning (u, v)
	f (x, y)               -> returning v/u will be interpreted without direction
	(f1 (x, y), f2 (x, y)) -> returning u and v respectively

color   = followed optionally by individual arrow color selection function (can not be expression)
	'mag'               -> color by magnitude of (u, v) vector
	'dir'               -> color by direction of (u, v) vector
  f (x, y, u, v)      -> relative scalar, will be scaled according to whole field to select color

fmt     = followed optionally by color and label format string '[#color][=label]'

*walks  = followed optionally by arguments to walkq for individual x, y walks and formatting
	"""

	if not _SPLOT:
		return None

	obj = plt

	args, xmin, xmax, ymin, ymax, kw = _process_head (obj, args, fs, style, ret_xrng = True, ret_yrng = True, kw = kw)

	if not isinstance (res, (sp.Tuple, tuple, list)):
		win = _FIGURE.axes [-1].get_window_extent ()
		res = (int (res), int ((win.y1 - win.y0) // ((win.x1 - win.x0) / (res + 1))))
	else:
		res = (int (res [0]), int (res [1]))

	xs = (xmax - xmin) / (res [0] + 1)
	ys = (ymax - ymin) / (res [1] + 1)
	x0 = xmin + xs / 2
	y0 = ymin + ys / 2
	xd = (xmax - xs / 2) - x0
	yd = (ymax - ys / 2) - y0
	X  = [[x0 + xd * i / (res [0] - 1)] * res [1] for i in range (res [0])]
	Y  = [y0 + yd * i / (res [1] - 1) for i in range (res [1])]
	Y  = [Y [:] for _ in range (res [0])]
	U  = [[0] * res [1] for _ in range (res [0])]
	V  = [[0] * res [1] for _ in range (res [0])]

	args, f, isdy = _process_funcxy (args, [x [0] for x in X], Y [0])

	if isdy:
		d, kw = kw, {'headwidth': 0, 'headlength': 0, 'headaxislength': 0, 'pivot': 'middle'}
		kw.update (d)

	# populate U and Vs from X, Y grid
	for j in range (res [1]):
		for i in range (res [0]):
			try:
				U [i] [j], V [i] [j] = f (X [i] [j], Y [i] [j])
			except (ValueError, ZeroDivisionError, FloatingPointError):
				U [i] [j] = V [i] [j] = 0

	cfunc = None

	if args:
		if callable (args [-1]): # color function present? f (x, y, u, v)
			cfunc = args.pop ()

		elif isinstance (args [-1], str): # pre-defined color function string?
			cfunc = _plotv_clr_func.get (args [-1])

			if cfunc:
				args.pop ()

	args, _, kw = _process_fmt (args, kw)

	if cfunc:
		C = [[cfunc (X [i] [j], Y [i] [j], U [i] [j], V [i] [j]) for j in range (res [1])] for i in range (res [0])]

		obj.quiver (X, Y, U, V, C, **kw)

	else:
		obj.quiver (X, Y, U, V, **kw)

	if 'label' in kw:
		obj.legend ()

	# if args: # if arguments remain, pass them on to walkq to draw differential curves
	# 	walkq (res = resw, from_plotv = (args, xmin, xmax, ymin, ymax, f, isdy))

	return _figure_to_image ()

#...............................................................................................
class splot: # for single script
	plotf = plotf
	plotv = plotv
