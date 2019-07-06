#!/usr/bin/env python
# python 3.6+

# Build parser tables for sparser.py using grammar dynamically generated from
# class methods in that file.

import sys

try:
	import ply
except ModuleNotFoundError:
	print ("This script requires the 'ply' python package to be installed.")
	sys.exit (-1)

import getopt
import importlib
import importlib.util
import os
import re
import types

from lalr1 import Parser

#...............................................................................................
def parse_rules (conflict_reduce_first = ()): # conflict_reduce_first = {'TOKEN', 'TOKEN', ...}
	def skipspace ():
		while lines and not lines [-1].strip ():
			lines.pop ()

		if not lines:
			return True

		return False

	lines   = list (reversed (open ('parser.out').readlines ()))
	rules   = [] # [('production', ('symbol', ...)), ...] - index by rule num
	strules = [] # [[(rule, pos) or rule with pos = 0 implied, ...], ...] - index by state
	terms   = {} # {'symbol': ([state, ...], [+shift or -reduce, ...], {state: conflict +shift or -reduce, ...} or not present if none), ...}
	nterms  = {} # {'symbol': ([state, ...], [+shift or -reduce, ...]), ...}
	state   = -1

	while lines [-1] [:5] != 'Rule ':
		lines.pop ()

	while lines [-1] [:5] == 'Rule ':
		_, num, prod, _, subs = lines.pop ().split (maxsplit = 4)

		assert int (num) == len (rules)

		rules.append ((prod, tuple (subs.split ()) if subs != '<empty>\n' else ()))

	for _ in range (2):
		skipspace ()
		lines.pop ()
		skipspace ()

		while lines [-1].strip ():
			t = lines.pop ().split ()

	while lines [-1] [:6] != 'state ':
		lines.pop ()

	while lines:
		if lines [-1] [:8] == 'WARNING:':
			break

		state += 1
		strules.append ([])

		assert int (lines.pop ().split () [1]) == state

		skipspace ()

		while lines [-1].strip (): # rules
			t     = lines.pop ().split ()
			rulei = int (t [0] [1 : -1])
			pos   = t.index ('.') - 3

			strules [-1].append ((rulei, pos) if pos else rulei)

		if skipspace ():
			break

		if lines [-1] [:6] == 'state ' or lines [-1] [:8] == 'WARNING:':
			continue

		while lines and lines [-1].strip (): # terminals
			t = lines.pop ().split ()

			if t [0] == '!':
				continue

			sts, acts, _ = terms.setdefault (t [0], ([], [], {}))

			if t [1] == 'shift':
				sts.append (state)
				acts.append (int (t [-1]))
			else: # t [1] == 'reduce'
				sts.append (state)
				acts.append (-int (t [4]))

		if skipspace ():
			break

		if lines [-1].split () [0] == '!':
			while lines and lines [-1].strip ():
				t   = lines.pop ().split ()
				act = int (t [-2]) if t [3] == 'shift' else -int (t [6])

				if t [1] in conflict_reduce_first:
					terms [t [1]] [2] [state] = terms [t [1]] [1] [-1]
					terms [t [1]] [1] [-1]    = act
				else:
					terms [t [1]] [2] [state] = act

			if skipspace ():
				break

		if lines [-1] [:6] == 'state ' or lines [-1] [:8] == 'WARNING:':
			continue

		while lines and lines [-1].strip (): # non-terminals
			t = lines.pop ().split ()

			assert t [1] == 'shift'

			sts, acts = nterms.setdefault (t [0], ([], []))

			sts.append (state)
			acts.append (int (t [-1]))

		if skipspace ():
			break

	lterms  = list (terms.keys ())
	lnterms = list (nterms.keys ())
	symbols = lterms + list (reversed (lnterms))
	rules   = [(-1 - lnterms.index (r [0]), tuple ((-1 - lnterms.index (s)) if s in nterms else lterms.index (s) \
			for s in r [1])) for r in rules [1:]]
	rules   = [r if len (r [1]) != 1 else (r [0], r [1] [0]) for r in rules]
	strules = [sr if len (sr) > 1 else sr [0] for sr in strules]
	terms   = [(lterms.index (s),) + t if t [2] else (lterms.index (s),) + t [:2] for s, t in terms.items ()]
	nterms  = [(-1 - lnterms.index (s),) + t for s, t in nterms.items ()]

	return symbols, rules, strules, terms, nterms

#...............................................................................................
def process (fnm, nodelete = False, compress = False, width = 512):
	parser_tables_rec      = re.compile (r'^(\s*)_PARSER_TABLES\s*=')
	parser_tables_cont_rec = re.compile (r'\\\s*$')

	spec = importlib.util.spec_from_file_location (fnm, fnm + '.py')
	mod  = importlib.util.module_from_spec (spec)

	spec.loader.exec_module (mod)

	# find and extract data from parser class
	for name, obj in mod.__dict__.items ():
		if isinstance (obj, object) and (hasattr (obj, '_PARSER_TABLES') and \
				hasattr (obj, 'TOKENS') and hasattr (obj, '_PARSER_TOP')):

			pc_name  = name
			pc_obj   = obj
			pc_start = Parser._rec_SYMBOL_NUMTAIL.match (obj._PARSER_TOP).group (1)
			pc_funcs = {} # {'prod': [('name', func, ('parm', ...)), ...], ...} - 'self' stripped from parms

			for name, obj in pc_obj.__dict__.items ():
				if name [0] != '_' and type (obj) is types.FunctionType and obj.__code__.co_argcount >= 1: # 2: allow empty productions
					name_sym = Parser._rec_SYMBOL_NUMTAIL.match (name).group (1)

					pc_funcs.setdefault (name_sym, []).append ((name, obj, obj.__code__.co_varnames [1 : obj.__code__.co_argcount]))

					if pc_start is None:
						pc_start = name_sym

			if pc_start is None:
				raise RuntimeError ('start production not found')

			break

	else:
		raise RuntimeError ('parser class not found')

	# build tokens, rules and context for ply
	ply_dict = {'__file__': __file__, 'tokens': list (filter (lambda s: s != 'ignore', pc_obj.TOKENS.keys ())), \
			'start': pc_start, 'p_error': lambda p: None, 't_error': lambda t: None}
	prods    = {} # {'prod': [('symbol', ...), ...], ...}
	stack    = [pc_start]

	for tok, text in pc_obj.TOKENS.items ():
		if tok != 'ignore':
			ply_dict [f't_{tok}'] = text

	while stack:
		prod = stack.pop ()

		if prod not in pc_funcs:
			raise NameError (f'production not found {prod!r}')

		rhss = prods.setdefault (prod, [])

		for name, func, parms in sorted (pc_funcs [prod]): # pc_funcs [prod]:
			parms = [p if p in pc_obj.TOKENS else Parser._rec_SYMBOL_NUMTAIL.match (p).group (1) for p in parms]

			rhss.append (parms)
			stack.extend (filter (lambda p: p not in pc_obj.TOKENS and p not in prods and p not in stack, parms))

	# add rule functions to context and build parse tables
	for prod, rhss in prods.items ():
		func         = lambda p: None
		func.__doc__ = f'{prod} : ' + '\n| '.join (' '.join (rhs) for rhs in rhss)

		ply_dict [f'p_{prod}'] = func

	exec ('import ply.lex as lex', ply_dict)
	exec ('import ply.yacc as yacc', ply_dict)
	exec ('lex.lex ()', ply_dict)
	exec (f'yacc.yacc (outputdir = {os.getcwd ()!r})', ply_dict)

	qpdata = parse_rules ({'BAR'}) # generalize BAR specification
	text   = repr (qpdata).replace (' ', '')

	if not nodelete:
		os.unlink ('parser.out')

	os.unlink ('parsetab.py')

	# write generated data into file
	class_rec = re.compile (fr'^\s*class\s+{pc_name}\s*[:(]')
	lines     = open (f'{fnm}.py').readlines ()

	for idx in range (len (lines)):
		if class_rec.match (lines [idx]):
			for idx in range (idx + 1, len (lines)):
				m = parser_tables_rec.match (lines [idx])

				if m:
					for end in range (idx, len (lines)):
						if not parser_tables_cont_rec.search (lines [end]):
							break

					end       += 1
					tab1       = m.group (1)
					tab2       = tab1 + '\t\t'
					lines_new  = [f'{tab1}_PARSER_TABLES = \\\n']

					if not compress:
						parser_tables_split_rec = re.compile (r'.{0,' + str (width) + r'}[,)}\]]')

						for line in parser_tables_split_rec.findall (text):
							lines_new.append (f'{tab2}{line} \\\n')

					else:
						import base64, zlib

						text = base64.b64encode (zlib.compress (text.encode ('utf8')))

						for i in range (0, len (text), width):
							lines_new.append (f'{tab2}{text [i : i + width]!r} \\\n')

					lines_new [-1]    = lines_new [-1] [:-2] + '\n'
					lines [idx : end] = lines_new

					open (f'{fnm}.py', 'w').writelines (lines)

					break

			break

#...............................................................................................
def cmdline ():
	nodelete   = False
	width      = 192
	compress   = True
	opts, argv = getopt.getopt (sys.argv [1:], 'w:', ['nd', 'nodelete', 'nc', 'nocompress', 'width='])

	for opt, arg in opts:
		if opt in ('--nd', '--nodelete'):
			nodelete = True
		elif opt in ('--nc', '--nocompress'):
			compress = False
		elif opt in ('-w', '--width'):
			width = int (arg)

	fnm = argv [0] if argv else 'sparser'

	process (fnm, nodelete = nodelete, compress = compress, width = width)

if __name__ == '__main__':
	cmdline ()
