import base64
from io import BytesIO
import itertools as it

SPLOT = False

try:
	import matplotlib.pyplot as plt
	from matplotlib import style

	style.use ('bmh') # ('seaborn') # ('classic') # ('fivethirtyeight')

	SPLOT = True

except:
	pass

def _cast_num (arg):
	try:
		return float (arg)
	except:
		return None

def _process_head (args, fs, obj, ret_xrng = False, ret_yrng = False):
	args = list (reversed (args))

	if fs is not None: # process figsize if present
		if isinstance (fs, tuple):
			fs = (_cast_num (fs [0]), _cast_num (fs [1]))

		else:
			fs = _cast_num (fs)

			if fs >= 0:
				fs = (fs, fs * 4 / 6)
			else:
				fs = (-fs, -fs)

		fig = plt.gcf ()

		fig.set_figwidth (fs [0])
		fig.set_figheight (fs [1])

	xmax, ymin, ymax = None, None, None

	xmin = _cast_num (args [-1])

	if xmin is not None: # process xmin / xmax, ymin, ymax if present
		args = args [:-1]
		xmax = _cast_num (args [-1])

		if xmax is not None:
			args = args [:-1]
			ymin = _cast_num (args [-1])

			if ymin is not None:
				args = args [:-1]
				ymax = _cast_num (args [-1])

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

	return args, xmin, xmax, ymin, ymax

def _process_fmt (args, kw = {}):
	kw    = kw.copy ()
	fargs = []

	if args and isinstance (args [-1], str):
		fmt, lbl = (args.pop ().split ('=', 1) + [None]) [:2]
		fmt, clr = (fmt.split ('#', 1) + [None]) [:2]

		if lbl:
			kw ['label'] = lbl.strip ()

		if clr:
			kw ['color'] = clr.strip ()

		fargs = [fmt.strip ()]

	if args and isinstance (args [-1], dict):
		kw.update (args.pop ())

	return args, fargs, kw

def plot (*args, fs = None, res = 12, **kw):
	"""Plot function(s), point(s) and / or line(s).

plotf ([limits,] *args, res = 16, **kw)

limits  = set absolute axis bounds: (default x is (0, 1), y is automatic)
  x              -> (-x, x, y auto)
  x0, x1         -> (x0, x1, y auto)
  x, y0, y1      -> (-x, x, y0, y1)
  x0, x1, y0, y1 -> (x0, x1, y0, y1)

fs      = set figure figsize if present: (default is (6, 4))
  x      -> (x, x / 6 * 4)
  -x     -> (x, x)
  (x, y) -> (x, y)

res     = minimum target resolution points per 50 x pixels (more or less 1 figsize x unit),
          may be raised a little to align with grid

*args   = functions and their formatting: (func, ['fmt',] [{kw},] func, ['fmt',] [{kw},] ...)
  func                      -> callable function takes x and returns y
	(x, y)                    -> point at x, y
	(x0, y0, x1, y1, ...)     -> connected lines from x0, y1 to x1, y1 to etc...
	((x0, y0), (x1, y1), ...) -> same thing

	fmt                       = 'fmt[#color][=label]'
	"""

	if not SPLOT:
		return None

	obj = plt
	fig = plt.figure ()

	args, xmin, xmax, ymin, ymax = _process_head (args, fs, obj, ret_xrng = True)
	leg                          = False

	while args:
		arg = args.pop ()

		if isinstance (arg, (tuple, list)): # list of x, y coords
			if isinstance (arg [0], (tuple, list)):
				arg = list (it.chain.from_iterable (arg))

			pargs = [arg [0::2], arg [1::2]]

		else: # y = function (x)
			win = plt.gcf ().axes [-1].get_window_extent ()
			xrs = (win.x1 - win.x0) // 50 # scale resolution to roughly 'res' points every 50 pixels
			rng = res * xrs
			dx  = dx2 = xmax - xmin

			while dx2 < (res * xrs) / 2: # align sampling grid on integers and fractions of integers while rng stays small enough
				rng = int (rng + (dx2 - (rng % dx2)) % dx2)
				dx2 = dx2 * 2

			xs  = [xmin + dx * i / rng for i in range (rng + 1)]
			ys  = [None] * len (xs)

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
		leg              = leg or ('label' in kwf)

		obj.plot (*(pargs + fargs), **kwf)

	if leg:
		obj.legend ()

	data = BytesIO ()

	fig.savefig (data, format = 'png', transparent = True, bbox_inches = 'tight')

	return base64.b64encode (data.getvalue ()).decode ()

class splot: # for single script
	SPLOT = SPLOT
	plot  = plot
