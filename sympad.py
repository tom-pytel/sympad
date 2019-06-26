#!/usr/bin/env python
# python 3.6+

_RUNNING_AS_SINGLE_SCRIPT = True

import re
import types

#...............................................................................................
class Token (str):
	def __new__ (cls, str_, text = None, pos = None, grps = None):
		self      = str.__new__ (cls, str_)
		self.text = text or ''
		self.pos  = pos
		self.grp  = () if not grps else grps

		return self

class Parser:
	_PARSER_TABLES = '' # placeholders so pylint doesn't have a fit
	_PARSER_TOP    = ''
	TOKENS         = {}

	_SYMBOL_notail_rec = re.compile (r'(.*[^_\d])(_?\d+)?') # symbol names in code have extra digits at end for uniqueness which are discarded

	def __init__ (self):
		if isinstance (self._PARSER_TABLES, bytes):
			import ast, base64, zlib
			symbols, rules, strules, terms, nterms = ast.literal_eval (zlib.decompress (base64.b64decode (self._PARSER_TABLES)).decode ('utf8'))
		else:
			symbols, rules, strules, terms, nterms = self._PARSER_TABLES

		self.tokgrps = {} # {'token': (groups pos start, groups pos end), ...}
		tokpats      = list (self.TOKENS.items ())
		pos          = 0

		for tok, pat in tokpats:
			l                   = re.compile (pat).groups + 1
			self.tokgrps [tok]  = (pos, pos + l)
			pos                += l

		self.tokre   = '|'.join (f'(?P<{tok}>{pat})' for tok, pat in tokpats)
		self.tokrec  = re.compile (self.tokre)
		self.rules   = [(0, (symbols [-1]))] + [(symbols [r [0]], tuple (symbols [s] for s in (r [1] if isinstance (r [1], tuple) else (r [1],)))) for r in rules]
		self.strules = [[t if isinstance (t, tuple) else (t, 0) for t in (sr if isinstance (sr, list) else [sr])] for sr in strules]
		states       = max (max (max (t [1]) for t in terms), max (max (t [1]) for t in nterms)) + 1
		self.terms   = [{} for _ in range (states)] # [{'symbol': [+shift or -reduce, conflict +shift or -reduce or None], ...}] - index by state num then terminal
		self.nterms  = [{} for _ in range (states)] # [{'symbol': +shift or -reduce, ...}] - index by state num then non-terminal
		self.rfuncs  = [None] # first rule is always None

		for t in terms:
			sym, sts, acts, confs = t if len (t) == 4 else t + (None,)
			sym                   = symbols [sym]

			for st, act in zip (sts, acts):
				self.terms [st] [sym] = (act, None)

			if confs:
				for st, act in confs.items ():
					self.terms [st] [sym] = (self.terms [st] [sym] [0], act)

		for sym, sts, acts in nterms:
			for st, act in zip (sts, acts):
				self.nterms [st] [symbols [sym]] = act

		prods = {} # {('production', ('symbol', ...)): func, ...}

		for name in dir (self):
			obj = getattr (self, name)

			if name [0] != '_' and type (obj) is types.MethodType and obj.__code__.co_argcount >= 2:
				m = Parser._SYMBOL_notail_rec.match (name)

				if m:
					parms = tuple (p if p in self.TOKENS else Parser._SYMBOL_notail_rec.match (p).group (1) \
							for p in obj.__code__.co_varnames [1 : obj.__code__.co_argcount])
					prods [(m.group (1), parms)] = obj

		for irule in range (1, len (self.rules)):
			func = prods.get (self.rules [irule] [:2])

			if not func:
				raise NameError (f"no method for rule '{self.rules [irule] [0]} -> {''' '''.join (self.rules [irule] [1])}'")

			self.rfuncs.append (func)

	def tokenize (self, text):
		tokens = []
		end    = len (text)
		pos    = 0

		while pos < end:
			m = self.tokrec.match (text, pos)

			if m is None:
				tokens.append (Token ('$err', text [pos], pos))

				break

			else:
				if m.lastgroup != 'ignore':
					tok  = m.lastgroup
					s, e = self.tokgrps [tok]
					grps = m.groups () [s : e]

					tokens.append (Token (tok, grps [0], pos, grps [1:]))

				pos += len (m.group (0))

		tokens.append (Token ('$end', '', pos))

		return tokens

	#...............................................................................................
	def parse_getextrastate (self):
		return None

	def parse_setextrastate (self, state):
		pass

	def parse_error (self):
		return False # True if state fixed to continue parsing, False to fail

	def parse_success (self, reduct):
		'NO PARSE_SUCCESS'
		return None # True to contunue checking conflict backtracks, False to stop and return

	def parse (self, src):
		has_parse_success = (self.parse_success.__doc__ != 'NO PARSE_SUCCESS')

		rules, terms, nterms, rfuncs = self.rules, self.terms, self.nterms, self.rfuncs

		tokens = self.tokenize (src)
		tokidx = 0
		cstack = [] # [(action, tokidx, stack, stidx, extra state), ...] # conflict backtrack stack
		stack  = [(0, None, None)] # [(stidx, symbol, reduction) or (stidx, token), ...]
		stidx  = 0
		rederr = None # reduction function raised SyntaxError

		while 1:
			if not rederr:
				tok       = tokens [tokidx]
				act, conf = terms [stidx].get (tok, (None, None))

			if rederr or act is None:
				rederr = None

				self.tokens, self.tokidx, self.cstack, self.stack, self.stidx, self.tok = \
						tokens, tokidx, cstack, stack, stidx, tok

				if tok == '$end' and stidx == 1 and len (stack) == 2 and stack [1] [1] == rules [0] [1]:
					if not has_parse_success:
						return stack [1] [2]

					if not self.parse_success (stack [1] [2]) or not cstack:
						return None

				elif self.parse_error ():
					tokidx, stidx = self.tokidx, self.stidx
					continue

				elif not cstack:
					if has_parse_success: # do not raise SyntaxError if parser relies on parse_success
						return None

					raise SyntaxError ( \
						'unexpected end of input' if tok == '$end' else \
						f'invalid token {tok.text!r}' if tok == '$err' else \
						f'invalid syntax {src [tok.pos : tok.pos + 16]!r}')

			# if act is None:
				act, tokens, tokidx, stack, stidx, estate = cstack.pop ()
				tok                                       = tokens [tokidx]

				self.parse_setextrastate (estate)

			elif conf is not None:
				cstack.append ((conf, tokens [:], tokidx, stack [:], stidx, self.parse_getextrastate ()))

			if act > 0:
				tokidx += 1
				stidx   = act

				stack.append ((stidx, tok))

			else:
				rule  = rules [-act]
				rnlen = -len (rule [1])
				prod  = rule [0]

				try:
					reduct = rfuncs [-act] (*(t [-1] for t in stack [rnlen:]))

				except SyntaxError as e:
					rederr = e or True
					continue

				del stack [rnlen:]

				stidx = nterms [stack [-1] [0]] [prod]

				stack.append ((stidx, prod, reduct))

class lalr1: # for single script
	Token  = Token
	Parser = Parser
import re

# ('#', 'num')                  - numbers represented as strings to pass on maximum precision to sympy
# ('@', 'var')                  - variable name, can take forms: 'x', "x'", 'dx', '\partial x', 'x_2', '\partial x_{y_2}', "d\alpha_{x_{\beta''}'}'''"
# ('(', expr)                   - explicit parentheses
# ('|', expr)                   - absolute value
# ('-', expr)                   - negative of expression, negative numbers are represented with this at least initially
# ('!', expr)                   - factorial
# ('+', (expr1, expr2, ...))    - addition
# ('*', (expr1, expr2, ...))    - multiplication
# ('/', numer, denom)           - fraction numer(ator) / denom(inator)
# ('^', base, exp)              - power base ^ exp(onent)
# ('log', expr)                 - natural logarithm of expr
# ('log', expr, base)           - logarithm of expr in base
# ('sqrt', expr)                - square root of expr
# ('sqrt', expr, n)             - nth root of expr
# ('func', 'func', expr)        - sympy or regular python function 'func', will be called with sympy expression
# ('lim', expr, var, to)        - limit of expr when variable var approaches to from both positive and negative directions
# ('lim', expr, var, to, dir)   - limit of expr when variable var approaches to from direction dir which may be '+' or '-'
# ('sum', expr, var, from, to)  - summation of expr over variable var from from to to
# ('diff', expr, (var1, ...))   - differentiation of expr with respect to var1 and optional other vars
# ('intg', None, var)           - anti-derivative of 1 with respect to differential var ('dx', 'dy', etc ...)
# ('intg', expr, var)           - anti-derivative of expr with respect to differential var ('dx', 'dy', etc ...)
# ('intg', None, var, from, to) - definite integral of 1 with respect to differential var ('dx', 'dy', etc ...)
# ('intg', expr, var, from, to) - definite integral of expr with respect to differential var ('dx', 'dy', etc ...)

_rec_num_int                = re.compile (r'^-?\d+$')
_rec_num_pos_int            = re.compile (r'^\d+$')
_rec_var_diff_start         = re.compile (r'^d(?=[^_])')
_rec_var_part_start         = re.compile (r'^\\partial ')
_rec_var_not_single         = re.compile (r'^(?:d.|\\partial |.+_)')
_rec_func_trigh             = re.compile (r'^a?(?:sin|cos|tan|csc|sec|cot)h?$')
_rec_func_trigh_noninv_func = re.compile (r'^(?:sin|cos|tan|csc|sec|cot)h?$')

class AST (tuple):
	FUNCS_PY = list (reversed (sorted ('''
		abs
		expand
		factor
		factorial
		simplify
		'''.strip ().split ())))

	FUNCS_PY_AND_TEX = list (reversed (sorted ('''
		arg
		ln
		'''.strip ().split ())))

	def __new__ (cls, *args):
		op       = _AST_CLS2OP.get (cls)
		cls_args = tuple (AST (*arg) if arg.__class__ is tuple else arg for arg in args)

		if op:
			args = (op,) + cls_args

		elif args:
			args = cls_args
			cls2 = _AST_OP2CLS.get (args [0])

			if cls2:
				op       = args [0]
				cls      = cls2
				cls_args = cls_args [1:]

		self    = tuple.__new__ (cls, args)
		self.op = op

		if op:
			self._init (*cls_args)

		return self

	def __getattr__ (self, name): # calculate value for nonexistent self.name by calling self._name ()
		func                 = getattr (self, f'_{name}') if name [0] != '_' else None
		val                  = func and func ()
		self.__dict__ [name] = val

		return val

	def _is_neg (self):
		return \
				self.op == '-' or \
				self.op == '#' and self.num == '-' or \
				self.op == '*' and self.muls [0].is_neg

	def neg (self, stack = False): # stack means stack negatives ('-', ('-', ('#', '-1')))
		if stack:
			return \
					AST ('-', self)            if not self.is_pos_num else \
					AST ('#', f'-{self.num}')

		else:
			return \
					self.minus                 if self.is_minus else \
					AST ('-', self)            if not self.is_num else \
					AST ('#', self.num [1:])   if self.num [0] == '-' else \
					AST ('#', f'-{self.num}')

	def _is_single_unit (self): # is single positive digit or single non-differential non-subscripted variable?
		if self.op == '#':
			return len (self.num) == 1

		return self.op == '@' and not _rec_var_not_single.match (self.var)

	def strip_paren (self):
		while self.op == '(':
			self = self.arg

		return self

	@staticmethod
	def is_int_text (text): # >= 0
		return _rec_num_int.match (text)

	@staticmethod
	def flatcat (op, ast0, ast1): # ,,,/O.o\,,,~~
		if ast0.op == op:
			if ast1.op == op:
				return AST (op, ast0 [-1] + ast1 [-1])
			return AST (op, ast0 [-1] + (ast1,))
		elif ast1.op == op:
			return AST (op, (ast0,) + ast1 [-1])
		return AST (op, (ast0, ast1))

class AST_Num (AST):
	def _init (self, num):
		self.num = num

	def _is_num (self):
		return True

	def _is_pos_num (self):
		return self.num [0] != '-'

	def _is_neg_num (self):
		return self.num [0] == '-'

	def _is_pos_int (self):
		return _rec_num_pos_int.match (self.num)

class AST_Var (AST):
	def _init (self, var):
		self.var = var

	def _is_var (self):
		return True

	def _is_null_var (self):
		return not self.var

	def _is_diff_var (self):
		return _rec_var_diff_start.match (self.var)

	def _is_part_var (self):
		return _rec_var_part_start.match (self.var)

class AST_Paren (AST):
	def _init (self, paren):
		self.paren = paren

	def _is_paren (self):
		return True

class AST_Abs (AST):
	def _init (self, abs):
		self.abs = abs

	def _is_abs (self):
		return True

class AST_Minus (AST):
	def _init (self, minus):
		self.minus = minus

	def _is_minus (self):
		return True

class AST_Fact (AST):
	def _init (self, fact):
		self.fact = fact

	def _is_fact (self):
		return True

class AST_Add (AST):
	def _init (self, adds):
		self.adds = adds

	def _is_add (self):
		return True

class AST_Mul (AST):
	def _init (self, muls):
		self.muls = muls

	def _is_mul (self):
		return True

class AST_Div (AST):
	def _init (self, numer, denom):
		self.numer = numer
		self.denom = denom

	def _is_div (self):
		return True

class AST_Pow (AST):
	def _init (self, base, exp):
		self.base = base
		self.exp  = exp

	def _is_pow (self):
		return True

class AST_Log (AST):
	def _init (self, log, base = None):
		self.log  = log
		self.base = base

	def _is_log (self):
		return True

class AST_Sqrt (AST):
	def _init (self, rad, idx = None):
		self.rad = rad
		self.idx = idx

	def _is_sqrt (self):
		return True

class AST_Func (AST):
	def _init (self, func, arg):
		self.func = func
		self.arg  = arg

	def _is_func (self):
		return True

	def _is_trigh_func (self):
		return _rec_func_trigh.match (self.func)

	def _is_trigh_func_noninv_func (self):
		return _rec_func_trigh_noninv_func.match (self.func)

class AST_Lim (AST):
	def _init (self, lim, var, to, dir = None):
		self.lim = lim
		self.var = var
		self.to  = to
		self.dir = dir

	def _is_lim (self):
		return True

class AST_Sum (AST):
	def _init (self, sum, var, from_, to):
		self.sum   = sum
		self.var   = var
		self.from_ = from_
		self.to    = to

	def _is_sum (self):
		return True

class AST_Diff (AST):
	def _init (self, diff, vars):
		self.diff = diff
		self.vars = vars

	def _is_diff (self):
		return True

class AST_Intg (AST):
	def _init (self, intg, var, from_ = None, to = None):
		self.intg  = intg
		self.var   = var
		self.from_ = from_
		self.to    = to

	def _is_intg (self):
		return True

_AST_OP2CLS = {
	'#': AST_Num,
	'@': AST_Var,
	'(': AST_Paren,
	'|': AST_Abs,
	'-': AST_Minus,
	'!': AST_Fact,
	'+': AST_Add,
	'*': AST_Mul,
	'/': AST_Div,
	'^': AST_Pow,
	'log': AST_Log,
	'sqrt': AST_Sqrt,
	'func': AST_Func,
	'lim': AST_Lim,
	'sum': AST_Sum,
	'diff': AST_Diff,
	'intg': AST_Intg,
}

_AST_CLS2OP = dict ((b, a) for (a, b) in _AST_OP2CLS.items ())

for cls in _AST_CLS2OP:
	setattr (AST, cls.__name__ [4:], cls)

AST.Zero   = AST ('#', '0')
AST.One    = AST ('#', '1')
AST.NegOne = AST ('#', '-1')
AST.I      = AST ('@', 'i')
AST.E      = AST ('@', 'e')
AST.Pi     = AST ('@', '\\pi')
AST.Infty  = AST ('@', '\\infty')
# TODO: \int _
# TODO: redo _expr_diff d or \partial handling
# TODO: iterated integrals

# Builds expression tree from text, nodes are nested AST tuples.
#
# ) When parsing, explicit and implicit multiplication have different precedence, as well as latex
#   \frac and regular '/' division operators.
#
# ) Explicit multiplication and addition have higher precedence than integration, so they are included in the expression to be integrated,
#   but lower precedence than limits or sums, so they end those expressions.
#
# ) Differentiation and partially integration are dynamically extracted from the tree being built so they have
#   no specific complete grammar rules.

from collections import OrderedDict
import re


def _ast_from_tok_digit_or_var (tok, i = 0): # special-cased infinity 'oo' is super-special
	return AST ('#', tok.grp [i]) if tok.grp [i] else AST ('@', '\\infty' if tok.grp [i + 1] else tok.grp [i + 2])

def _expr_int (ast, from_to = ()): # construct indefinite integral ast
	if ast.is_diff_var or ast.is_null_var: # null_var is for autocomplete
		return AST ('intg', None, ast, *from_to)

	elif ast.is_div:
		if ast.numer.is_diff_var:
			return AST ('intg', ('/', ast.One, ast.denom), ast.numer, *from_to)
		elif ast.denom.is_mul and ast.denom.muls [-1].is_diff_var:
			return AST ('intg', ('/', ast.numer, ast.denom.muls [0] if len (ast.denom.muls) == 2 else AST ('*', ast.denom.muls [:-1])), ast.denom.muls [-1], *from_to)

	elif ast.is_mul and (ast.muls [-1].is_diff_var or ast.muls [-1].is_null_var): # null_var is for autocomplete
		return AST ('intg', ast.muls [0] if len (ast.muls) == 2 else AST ('*', ast.muls [:-1]), ast.muls [-1], *from_to)

	elif ast.is_add and ast.adds [-1].is_mul and ast.adds [-1].muls [-1].is_diff_var:
		return AST ('intg', \
				AST ('+', ast.adds [:-1] + (AST ('*', ast.adds [-1].muls [:-1]),))
				if len (ast.adds [-1]) > 3 else \
				AST ('+', ast.adds [:-1] + (ast.adds [-1].muls [0],)) \
				, ast.adds [-1].muls [-1], *from_to)

	raise SyntaxError ('integration expecting a differential')

_rec_var_d_or_partial = re.compile (r'^(?:d|\\partial)$')

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast.numer.is_var and _rec_var_d_or_partial.match (ast.numer.var):
			p = 1
			v = ast.numer.var

		elif ast.numer.is_pow and ast.numer.base.is_var and _rec_var_d_or_partial.match (ast.numer.base.var) and ast.numer.exp.is_pos_int:
			p = int (ast.numer.exp.num)
			v = ast.numer.base.var

		else:
			return None

		ast_dv_check = (lambda n: n.is_diff_var) if v [0] == 'd' else (lambda n: n.is_part_var)

		ns = ast.denom.muls if ast.denom.is_mul else (ast.denom,)
		ds = []
		cp = p

		for i in range (len (ns)):
			n = ns [i]

			if ast_dv_check (n):
				dec = 1
			elif n.is_pow and ast_dv_check (n.base) and n.exp.is_pos_int:
				dec = int (n.exp.num)
			else:
				return None

			cp -= dec

			if cp < 0:
				return None # raise SyntaxError?

			ds.append (n)

			if not cp:
				if i == len (ns) - 1:
					return AST ('diff', None, tuple (ds))
				elif i == len (ns) - 2:
					return AST ('diff', ns [-1], tuple (ds))
				else:
					return AST ('diff', AST ('*', ns [i + 1:]), tuple (ds))

		return None # raise SyntaxError?

	# start here
	if ast.is_div: # this part handles d/dx
		diff = _interpret_divide (ast)

		if diff and diff [1]:
			return diff

	elif ast.is_mul: # this part needed to handle \frac{d}{dx}
		tail = []
		end  = len (ast.muls)

		for i in range (end - 1, -1, -1):
			if ast.muls [i].is_div:
				diff = _interpret_divide (ast.muls [i])

				if diff:
					if diff.expr:
						if i < end - 1:
							tail [0 : 0] = ast.muls [i + 1 : end]

						tail.insert (0, diff)

					elif i < end - 1:
						tail.insert (0, AST ('diff', ast.muls [i + 1] if i == end - 2 else AST ('*', ast [i + 1 : end]), diff.vars))

					else:
						continue

					end = i

		if tail:
			tail = tail [0] if len (tail) == 1 else AST ('*', tuple (tail))

			return tail if end == 0 else AST.flatcat ('*', ast.muls [0], tail) if end == 1 else AST.flatcat ('*', AST ('*', ast.muls [:end]), tail)

	return ast

def _expr_func (iparm, *args): # rearrange ast tree for explicit parentheses like func (x)^y to give (func (x))^y instead of func((x)^y)
	if args [iparm].is_fact:
		if args [iparm].fact.is_paren:
			return AST ('!', AST (*(args [:iparm] + (args [iparm].fact.paren,) + args [iparm + 1:])))

	elif args [iparm].is_pow:
		if args [iparm].base.is_paren:
			return AST ('^', AST (*(args [:iparm] + (args [iparm].base.paren,) + args [iparm + 1:])), args [iparm].exp)

	return AST (*args)

#...............................................................................................
class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJztXXlvGzcW/zILRAIoYHjP5L8cbtfYNGldp8BCEIKkcRcBmjTI0V2g6Hffd5HDoWd02LJs1YXoIYfD4x0/PpLzKHm2fHD6/PyBevDs9Du4/vgSr9+dPn/5I979cEaPXnwL1/Oz02//CfE3L58/wcyTb/DZ40dncP3+0dnJ82eQOP32+Yuzk1dPXp49+zeW' \
			b'PXv0RCItsYGYHmPx59TdT9TGPy4+vE3PcpuYeAy1/nVyjkkkAXt9+uLl42cnP55TxSdQ8Jxof8xX7Or7Z8TBk6cv6FFRkgh59OT8xdnpI6Th6elPp09P+n4w7/uz0+9OsP75C7ic/PDy0TO8+/n1p4svr3779Ortb1/f/Hrx+cvrT5D7+eub3ylx8b+Pn159' \
			b'/vrxorh5A8ni6Yev71Pyy8WnnP7l0+ufU/ojdPIh3bx+8znn//bfXPz1z19y+uuHXPX9119fvXv/Md2+ffd7n/zll0zDxX96+jIJBZG/vntftgiJTM7btyn57kMi4cFKLWcL45Sxc8UJhwmtFoZir2at6hRkGKO6ecqjnHy70AFTlv5MVAs37+9tf7ugtrFu' \
			b'QzUbvlgDOXpeZdkyE5OYsnyx8gDLML1RzTQ20+LfPGfZ8jYXxTxMGTVzcGPm/Z21xKseZPv6rnoe6jtjBjmxvAOqSdRq1nBDWJifSp6kF1QOhA30eIViDsoiKUqDCP186ilpMW5RyA7KLCLGjv5Mm/LlvuvvIYGMaL5kxjgJqVbNQIaMjRYT+LRTDBEdgJaG' \
			b'RNzMU0arJMuUudCiFm5THuiOUo4vILm53AMKSWhAlfFUTm4NdQtQMIUEQhIiip75AhURJiBnZmxmS26rDNf3ADhlLAPbQ3KB95ASmqQQsAJgGym38yJngV24+aBM9Vxu4Y66tcQnsyMd9nl6PA/v+nwWDDQOnIARWEKfqHbQtG1UVDjoASkgKhthuNGARCKV' \
			b'18ob5RrlNKoNtWQUDslW2Q70h2MHFQmtORS5CQRGh0S4qFyroA0VlLPKOeUgMxDBUKZFnfiofKt8p0KjglbBqGBVgJKQ6FY4QNASWLwuZ0Aw3gHREDmo3BwDD8uZZS4iXZEHzOyYM89RkFxHRW9D0jaykEFyRJHhyAphnh4fB2g84wQowcgzQ54ZcprZ1KwT' \
			b'zQ+RPmJTW65KLRxA6J0gm6kx+iDdQn8sDGPX9ccjbJ+9skKMX9ert8pDP175sNe+w6FEy8McW2RE8Qh3lF0wB9p3LWufxeJSDX88Iy0IA/Z4SHaiDyFdU7ypkpZxquNWpdn+eKkUeHAHNjWBh15gQxNI9wEYCipEFVqkUEok2wBCrZEDUjYkeCqzk21suNWI' \
			b'DdxFBS1n7d0lDahC2u4USeGOkYRrGCMrCcMrCcMrCTNHABLycFamQpoLaSp0sLUOQQxnXaLBEA3HYb6MEZpRnIfoz0l//iD9wezHhtG7A83X3u9sQgMvYwIjlwSE8ztb5KOB0hJXHMdC7MyzlK1I2R8N5bTEMFssGgRAgYwSLhNMtTBY4hLC8NrB0Eox8Fom' \
			b'MCBDpAXkLLR54WDnxyAiXMYYXpTYkT1xO5KLt5Zvrcw1lucay3MNRFVnDKPI5b2eKEEzkj3cFnCJU5893NRnmDtjOWIpehlW3h1mUvEymqlzxxFT4pgux3eatItDwvICmnQXuHZg+xto3IzpGpDvBBuOseEYG47WIZqfask+lLoN9XsAGYt0iTsnkacoeBGk' \
			b'iJfGRGVqQGieheZZaP5o7K3XR0MsosGTljxrybN6HOPbsXYSigMrJLBCIALaGMmBC3opGO/UhmCJREcmGt8+z3gjbHiW8kTucHsLxLfMa8vVWinZ3j3GurtGkr1jJKHeOnmj3Mgr5YYm9kaRH6JDqnoCqHdcu7Bf0BUDty1wEocGn61XpyLACdAGSPMqBtUC' \
			b'dlrVdqprVAfK8qoLqgNzgJ2CLBpggmQCRCHH+LYOeUPmkDt88WMsEIteIasWwOgCXZ7oiwHBWHIwQRJ9TB07JEEQC6BoAewvAnqdkEd2+6E7DT0zWBpLRCXNopcyYHlskJoF/tBvs0D/lsd7jKEKFobqIOoF8L/w2IznRtC7iLfwF9BVhMXiCqfR3eVc6vp2' \
			b'ZA5/8AxBg4CxDnQAjar2kg7Q84aXNTpo5YO6aCd1IWUqXbS76oI7GtNFomNF1u+voRM0JRRqtWBWoOsaxeTaWA6dIGZSO325SkHU904aSv2N6qggaUWuR9ITWsDI2kL7acU8shm8gv6AITbLpSLRhG6hy9iqCJgGKGvSq9+gWr+betE9g94SnAPQ1dqrG/7g' \
			b'Ge7AbATVB5wTQHigUmAwMALQ3e1R6XhCAP38oALbDZCBcsbLGlwE+Sxg1mohsjx2Q0ZHpy8BRGpU6IAcdPZDE9A5HgVAqODxhS3gQshiyFDT44BBcWg+ZAE96EQHqHeBR12sXdECj2AUBELF7FnPv+shZIZWoIJQKObibYAUE35CASE9jaJwHUPRqhwQKRih' \
			b'+7PMLs0HmXW93q4v0JvRDtsQqGi28xS53G1lUnKl2qRgtx1hJVHWo4UaGgVM6kWsjNQctzI9ySva/N57eHQqB4JHx/Aos0t4dHwWZjM8qjYSPPg4EEUud1vBI1eq4dH18BDKCnh0k/CQXgQeUnMcHj3JCI9w7+GBfKaA8MBINi85u4AH3ga6boCHGYYED2rO' \
			b'cORyt0N49JUqeFC3DI/UVA8PamgUHqkXhkeqOQqPguQVHSy69/CgQ5wcCB6a4VFml/DQBA+9GR562EaCB5/jNHL6Urqt4JEr1fDQPTyEsgIeehIe0ovAQ2qOw6MneUUnzu49PLzKgeDhGR5ldgkPOmiJ103w8MM2Ejw8w8MzPKTbCh65Ug0P38NDKCvg4Sfh' \
			b'Ib0IPKTmODx6khEeHcLDyB4nTO9yxiHjN6GmqYEzsvVZj504Dp+RbdAWUDJDODXtDhujdZshVC0es4Vrg1siSkWKRrZF9JQK5TDYIZFUF5y/9t2S4LBsx0nzgkXeM1HkUpEai5Tbcac1HAPD8dImKlFdgDNM7qRMm7t2JGACqbQwDtJAm6merWI/pf7Q4SHu' \
			b'LFv/EPdyoFGIzZ9zOm2+rbHbiNwjtnetyoHsHe+1Btkl3ALl8HWTyWuHzSSY8XbL8HYr9VzBLFeqMdZvtxJxBaomt1upFzF5UnMcTT3JKz71e++nxE7lQBDh/dYgu5wSab9lNu+3TNVGwgfvtwzvt1K3FT5ypRof/X4rUVbgY3K/lXoRfEjNcXz0JK/4NNp+' \
			b'8KF3gUhz91CCbqQUECWW19WD7NIdQutqu35dTU01gzZsv7S2vLS28p2lvvPKb5If1K6TfnWd6OuxYidX16kXcadIzVGsFFQTVuzfWGGsWJUDYYXf/A6yS6yw72y984yaagZtULOCFfarUeTKzius5Ac1VmyPFaGvwMrke+HUi2BFao5jpad6xWcF/8YKYcWp' \
			b'HAgrjrFSZpdYcYQVtx4rjrHihs0krDjGimOs9J1XWMkPaqy4HitCX4EVN4kV6UWwIjXHsdKTRVjZ/Z0wn3YpXf/rQQOSBYFdBTpNgR53GwCCxumD4OGVS84pcEOLlg4pRuB0BJ1x8PDiJbXRGtU61a9eePHCa5fU7xA3ufcCNrrRBJ1+9cL09biZXLpwFwwa' \
			b'rjQKGel1xUflrmJatsbKdVGyO0T0PuxMVDmQnYlsZ8rs0s5EsjOR4IKR7jgasTaRrU0cNpasTWRrE9na9CRU1qasWhuc2BscIbQwOHHSyaBN7kyMjtQeNzp9IBRd7VXy4VFkCEjuoFhqVQ6EJd5UD7JLLNGO2vKO2raMpXYcSy1jqR02lrDEW2vLW+uChApL' \
			b'ZdUaS7zBtnyWpSC3QNTkNrvoUQAllccB1ZNBgGphqymnJzacnYjTLxBjQs2l8y4DaOx4LiK9CkyAmAJCV73qw5+24Jd8CzEr25x6WGzxKs/1HqipYzC1aq9+uoFexPQnHCb0uaBt0eAsA3CwF53i94v3pda4VrNsFsc1jIeO8ESkKbTd0JGOA2q9tTereE3k' \
			b'TSs/iWMEBP3r7zYDIr0Cr4AB1N/oYAeu9zTem+6Yxnx3+bX8XoY9sr3b0IeCt2nO4/216Lh2uVGrDtTdlZkaNkbufmm31iz5JZtuzxq2mzTcbFYySElculuqetRRe+1RrEXX7bX07VnlGG3WuO/9rVdS/KgXdX+LNW1Y8UhmpXv1h7EPAdfoIAVK/wbBAASB' \
			b'j45htBkEVPgugyASCLDGOhB4/EILHZ3HXSntTyMukA1IDnft9GIQEtER1/iOj15KAmtLO1bHIBqi59KgcDpZAsQsrzWh3My+b5s5pD4DX0IL1bLfueSg+77NcwdugPrz7PUsAjv6o1TpJTX629YhvhPzN6TDMc11fxXNhVvXXFBExIE0BwpZ6mbrqXm7GXnr' \
			b'r4RNqQW/J446CHwIAKMtJlD2/u88ae72Da+pr+rowTQIgl7qLWS6UZrXE2USo91+77GD8PYhOJSaeQhK/pO/x4tS295ybGM29mIqRJA4dq5gBnadgPc56Ff8veilxjHlaakFQlzKKoskNOQzyvcnm4aJqZryuW4ScJairSUWeI034C07k+ylpsN0026npisB' \
			b'0E9T07k8Phfboo8oe4HEXYNfFML3xvQzFfg+SN4VxPQSd0U/c5u+W3u5nRiKpuhL8WbwwY0HfKgZu2UzTo1+qA03bIN9YZMtwRCRD0+jvvxQe36sPfGtjbY64siCzVjx4al6mFdPuXP6NeLeMxiGPkEixdLBGNw8VP4+R26+7OMr/XpBPO3sxev00FM3yQBa' \
			b'gBsJlkGcM7SeKkkiiXtQBvkmrhaIhnYfNFh11UA0dD00rkOFwwWp41+e2DkQIeXp7+tQwr+hfcXAlOi1lOiamHYtPfx7GxOh9Zcym8tZgckyG0bxusFbktsP2I2DNaocBisBo8pHZcjLgKouJhpOoaTresyhPTiHuAA6RGD+3OH5s+oggfnzh+fPqYME5m/T' \
			b'PHoD/EV1kMD8xU38bb9C2IlL3HqsDTGue9qZDdWHgXltb2ZNtAPTRq0PfHpqY7EcYL+1RTHmvrt17r26jcB7jOburIct/ZOT2wssEM2uAaSnw59xm/M/TKGv7lt8L8VvjPBNh6P1l+AI3ZLQTPYlwKayo4M5/NThbwxp+qUhkPxq/n9Hh+Kn'

	_PARSER_TOP  = 'expr'

	_GREEK       = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\pi|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'

	_SPECIAL     = r'\\partial|\\infty'
	_CHAR        = fr'[a-zA-Z]'
	_ONEVAR      = fr'{_CHAR}|{_GREEK}'
	_ONEVARSP    = fr'{_CHAR}|{_GREEK}|{_SPECIAL}'
	_DIONEVARSP  = fr'(\d)|(oo)|({_ONEVARSP})'

	_FUNCPY      = '|'.join (AST.FUNCS_PY)
	_FUNCPYTEX   = '|'.join (AST.FUNCS_PY_AND_TEX)

	TOKENS       = OrderedDict ([ # order matters
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('TRIGH',         r'\\?(?:(a)(?:rc)?)?((?:sin|cos|tan|csc|sec|cot)h?)|\\operatorname\{(sech|csch)\}'),
		('FUNC',         fr'({_FUNCPY})|\\?({_FUNCPYTEX})|\\operatorname\{{({_CHAR}\w+)\}}|\$({_CHAR}\w+)|\?'),
		('SQRT',          r'\\?sqrt'),
		('LOG',           r'\\?log'),
		('LIM',           r'\\lim'),
		('SUM',           r'\\sum'),
		('INT',           r'\\int(?:\s*\\limits)?'),
		('LEFT',          r'\\left'),
		('RIGHT',         r'\\right'),
		('CDOT',          r'\\cdot'),
		('TO',            r'\\to'),
		('FRAC2',        fr'\\frac\s*(?:{_DIONEVARSP})\s*(?:{_DIONEVARSP})'),
		('FRAC1',        fr'\\frac\s*(?:{_DIONEVARSP})'),
		('FRAC',          r'\\frac'),
		('VAR',          fr'\b_|(oo)|(d|\\partial\s?)?({_ONEVAR})|{_SPECIAL}'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
		('SUB1',         fr'_(?:{_DIONEVARSP})'),
		('SUB',           r'_'),
		('CARET1',       fr'\^(?:{_DIONEVARSP})'),
		('CARET',         r'\^'),
		('DOUBLESTAR',    r'\*\*'),
		('PRIMES',        r"'+"),
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('CURLYL',        r'\{'),
		('CURLYR',        r'\}'),
		('BRACKETL',      r'\['),
		('BRACKETR',      r'\]'),
		('BAR',           r'\|'),
		('PLUS',          r'\+'),
		('MINUS',         r'\-'),
		('STAR',          r'\*'),
		('EQUALS',        r'='),
		('DIVIDE',        r'/'),
		('FACTORIAL',     r'!'),
		('ignore',        r'\\,|\\?\s+'),
	])

	_FUNC_AST_REMAP = {
		'abs'      : lambda expr: _expr_func (1, '|', expr.strip_paren ()),
		'factorial': lambda expr: _expr_func (1, '!', expr.strip_paren ()),
		'ln'       : lambda expr: _expr_func (1, 'log', expr),
	}

	def expr            (self, expr_int):                      	             return expr_int

	def expr_int_1      (self, INT, expr_sub, expr_super, expr_int):         return _expr_int (expr_int, (expr_sub, expr_super))
	def expr_int_2      (self, INT, expr_int):                               return _expr_int (expr_int)
	def expr_int_3      (self, expr_add):                                    return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_mul_exp):                return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2      (self, expr_add, MINUS, expr_mul_exp):               return AST.flatcat ('+', expr_add, expr_mul_exp.neg (True))
	def expr_add_3      (self, expr_mul_exp):                                return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_lim):                return AST.flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_2  (self, expr_mul_exp, STAR, expr_lim):                return AST.flatcat ('*', expr_mul_exp, expr_lim)
	def expr_mul_exp_3  (self, expr_lim):                                    return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_lim):                             return AST ('lim', expr_lim, expr_var, expr)
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_doublestar, PLUS, CURLYR, expr_lim):  return AST ('lim', expr_lim, expr_var, expr, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_doublestar, MINUS, CURLYR, expr_lim): return AST ('lim', expr_lim, expr_var, expr, '-')
	def expr_lim_6      (self, expr_sum):                                                                           return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQUALS, expr, CURLYR, expr_super, expr_lim):             return AST ('sum', expr_lim, expr_var, expr, expr_super)
	def expr_sum_2      (self, expr_neg):                                                                           return expr_neg

	def expr_neg_1      (self, MINUS, expr_diff):                            return expr_diff.neg (True) # _ast_neg_stack (expr_diff.neg (True) if expr_diff.is_pos_num else AST ('-', expr_diff)
	def expr_neg_2      (self, expr_diff):                                   return expr_diff

	def expr_diff       (self, expr_div):                                    return _expr_diff (expr_div)

	def expr_div_1      (self, expr_div, DIVIDE, expr_mul_imp):              return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2      (self, expr_div, DIVIDE, MINUS, expr_mul_imp):       return AST ('/', expr_div, expr_mul_imp.neg (True))
	def expr_div_3      (self, expr_mul_imp):                                return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_func):                     return AST.flatcat ('*', expr_mul_imp, expr_func)
	def expr_mul_imp_2  (self, expr_func):                                   return expr_func

	def expr_func_1     (self, SQRT, expr_func):                             return _expr_func (1, 'sqrt', expr_func)
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_func):   return _expr_func (1, 'sqrt', expr_func, expr)
	def expr_func_3     (self, LOG, expr_func):                              return _expr_func (1, 'log', expr_func)
	def expr_func_4     (self, LOG, expr_sub, expr_func):                    return _expr_func (1, 'log', expr_func, expr_sub)
	def expr_func_5     (self, TRIGH, expr_func):                            return _expr_func (2, 'func', f'{"a" if TRIGH.grp [0] else ""}{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func)
	def expr_func_6     (self, TRIGH, expr_super, expr_func):
		return \
				AST ('^', _expr_func (2, 'func', f'{TRIGH.grp [0] or ""}{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func), expr_super) \
				if expr_super != AST.NegOne else \
				_expr_func (2, 'func', TRIGH.grp [1] or TRIGH.grp [2], expr_func) \
				if TRIGH.grp [0] else \
				_expr_func (2, 'func', f'a{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func)

	def expr_func_7     (self, FUNC, expr_func):
		name = FUNC.grp [0] or FUNC.grp [1] or FUNC.grp [2] or FUNC.grp [3] or FUNC.text
		func = self._FUNC_AST_REMAP.get (name)

		return func (expr_func) if func else _expr_func (2, 'func', name, expr_func)

	def expr_func_8     (self, expr_fact):                                   return expr_fact

	def expr_fact_1     (self, expr_fact, FACTORIAL):                        return AST ('!', expr_fact)
	def expr_fact_2     (self, expr_pow):                                    return expr_pow

	def expr_pow_1      (self, expr_pow, expr_super):                        return AST ('^', expr_pow, expr_super)
	def expr_pow_2      (self, expr_abs):                                    return expr_abs

	def expr_abs_1      (self, LEFT, BAR1, expr, RIGHT, BAR2):               return AST ('|', expr)
	def expr_abs_2      (self, BAR1, expr, BAR2):                            return AST ('|', expr)
	def expr_abs_3      (self, expr_paren):                                  return expr_paren

	def expr_paren_1    (self, PARENL, expr, PARENR):                        return AST ('(', expr)
	def expr_paren_2    (self, LEFT, PARENL, expr, RIGHT, PARENR):           return AST ('(', expr)
	def expr_paren_3    (self, IGNORE_CURLY, CURLYL, expr, CURLYR):          return expr
	def expr_paren_4    (self, expr_frac):                                   return expr_frac

	def expr_frac_1     (self, FRAC, expr_term1, expr_term2):                return AST ('/', expr_term1, expr_term2)
	def expr_frac_2     (self, FRAC1, expr_term):                            return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_term)
	def expr_frac_3     (self, FRAC2):                                       return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 3))
	def expr_frac_4     (self, expr_term):                                   return expr_term

	def expr_term_1     (self, CURLYL, expr, CURLYR):                        return expr
	def expr_term_2     (self, expr_var):                                    return expr_var
	def expr_term_3     (self, expr_num):                                    return expr_num

	def expr_num        (self, NUM):                                         return AST ('#', NUM.text) if NUM.grp [0] or NUM.grp [2] else AST ('#', NUM.grp [1])

	def expr_var_1      (self, var, PRIMES, subvar):                         return AST ('@', f'{var}{subvar}{PRIMES.text}')
	def expr_var_2      (self, var, subvar, PRIMES):                         return AST ('@', f'{var}{subvar}{PRIMES.text}')
	def expr_var_3      (self, var, PRIMES):                                 return AST ('@', f'{var}{PRIMES.text}')
	def expr_var_4      (self, var, subvar):                                 return AST ('@', f'{var}{subvar}')
	def expr_var_5      (self, var):                                         return AST ('@', var)

	def var             (self, VAR):                                         return f'\\partial {VAR.grp [2]}' if VAR.grp [1] and VAR.grp [1] [0] == '\\' else '\\infty' if VAR.grp [0] else VAR.text
	def subvar_1        (self, SUB, CURLYL, expr_var, CURLYR):               return f'_{{{expr_var [1]}}}'
	def subvar_2        (self, SUB, CURLYL, NUM, CURLYR):                    return f'_{{{NUM.text}}}'
	def subvar_3        (self, SUB, CURLYL, NUM, subvar, CURLYR):            return f'_{{{NUM.text}{subvar}}}'
	def subvar_4        (self, SUB1):                                        return SUB1.text

	def expr_sub_1      (self, SUB, expr_frac):                              return expr_frac
	def expr_sub_2      (self, SUB1):                                        return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1    (self, DOUBLESTAR, expr_func):                       return expr_func
	def expr_super_2    (self, DOUBLESTAR, MINUS, expr_func):                return expr_func.neg (True)
	def expr_super_3    (self, CARET, expr_frac):                            return expr_frac
	def expr_super_4    (self, CARET1):                                      return _ast_from_tok_digit_or_var (CARET1)

	def caret_or_doublestar_1 (self, DOUBLESTAR):                            return '**'
	def caret_or_doublestar_2 (self, CARET):                                 return '^'

	#...............................................................................................
	_AUTOCOMPLETE_SUBSTITUTE = { # autocomplete means autocomplete AST tree so it can be rendered, not expression
		'CARET1': 'CARET',
		'SUB1'  : 'SUB',
		'FRAC2' : 'FRAC',
		'FRAC1' : 'FRAC',
	}

	_AUTOCOMPLETE_CLOSE = {
		'RIGHT'   : '\\right',
		'PARENR'  : ')',
		'CURLYR'  : '}',
		'BRACKETR': ']',
		'BAR'     : '|',
	}

	def _mark_error (self):
		self.autocompleting = False

		if self.erridx is None:
			self.erridx = self.tokens [self.tokidx - 1].pos

	def _parse_autocomplete_expr_int (self):
		s               = self.stack [-1]
		self.stack [-1] = (s [0], s [1], AST ('*', (s [2], ('@', ''))))
		expr_vars       = set ()

		if self.autocompleting:
			stack = [s [2]]

			while stack:
				ast = stack.pop ()

				if ast.is_var:
					expr_vars.add (ast.var)
				else:
					stack.extend (filter (lambda a: isinstance (a, tuple), ast))

		if len (expr_vars) == 1:
			self.autocomplete.append (f' d{expr_vars.pop ()}')
		else:
			self._mark_error ()

		return True

	def parse_getextrastate (self):
		return (self.autocomplete [:], self.autocompleting, self.erridx)

	def parse_setextrastate (self, state):
		self.autocomplete, self.autocompleting, self.erridx = state

	def parse_error (self): # add tokens to continue parsing for autocomplete if syntax allows
		if self.tok != '$end':
			self.parse_results.append ((None, self.tok.pos, []))

			return False

		if self.tokidx and self.tokens [self.tokidx - 1] == 'LEFT':
			for irule, pos in self.strules [self.stidx]:
				if self.rules [irule] [1] [pos] == 'PARENL':
					break
			else:
				raise RuntimeError ('could not find left parenthesis rule')

		else:
			irule, pos = self.strules [self.stidx] [0]

		rule = self.rules [irule]

		if pos >= len (rule [1]): # syntax error raised by rule reduction function?
			if rule [0] == 'expr_int': # special case error handling for integration
				return self._parse_autocomplete_expr_int ()

			return False

		sym = rule [1] [pos]

		if sym in self.TOKENS:
			self.tokens.insert (self.tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

			if self.autocompleting and sym in self._AUTOCOMPLETE_CLOSE:
				self.autocomplete.append (self._AUTOCOMPLETE_CLOSE [sym])
			else:
				self.autocompleting = False

		else:
			self.tokens.insert (self.tokidx, lalr1.Token ('VAR', '', self.tok.pos, (None, None, '')))
			self._mark_error ()

		return True

	def parse_success (self, reduct):
		self.parse_results.append ((reduct, self.erridx, self.autocomplete))

		return True # continue parsing if conflict branches remain to find best resolution

	def parse (self, text):
		self.parse_results  = [] # [(reduct, erridx, autocomplete), ...]
		self.autocomplete   = []
		self.autocompleting = True
		self.erridx         = None

		lalr1.Parser.parse (self, text)

		if not self.parse_results:
			return (None, 0, [])

		rated = sorted ((r is None, -e if e is not None else float ('-inf'), len (a), i, (r, e, a)) \
				for i, (r, e, a) in enumerate (self.parse_results))

		## DEBUG!
		rated = list (rated)
		print ()
		for res in rated:
			print ('parse:', res [-1])
		## DEBUG!

		return next (iter (rated)) [-1]

class sparser: # for single script
	Parser = Parser

## DEBUG!
# if __name__ == '__main__':
# 	p = Parser ()
# 	print (p.parse ('1') [0])
# 	print (p.parse ('x') [0])
# 	print (p.parse ('x!') [0])
# 	print (p.parse ('|x|') [0])
# 	print (p.parse ('x/y') [0])
# 	print (p.parse ('x/(y/z)') [0])
# 	print (p.parse ('sin x') [0])
# 	print (p.parse ('sin x**2') [0])
# 	print (p.parse ('sin (x**2)') [0])
# 	print (p.parse ('sin (x)**2') [0])
# 	print (p.parse ('x') [0])
# 	print (p.parse ('-x') [0])
# 	print (p.parse ('-{-x}') [0])
# 	print (p.parse ('\\int dx') [0])
# 	print (p.parse ('\\int dx/2') [0])
# 	print (p.parse ('\\int 2 dx') [0])
# 	print (p.parse ('\\int 3 / 2 dx') [0])
# 	print (p.parse ('\\int x + y dx') [0])
# 	print (p.parse ('\\int_0^1 dx') [0])
# 	print (p.parse ('\\int_0^1 dx/2') [0])
# 	print (p.parse ('\\int_0^1 2 dx') [0])
# 	print (p.parse ('\\int_0^1 3 / 2 dx') [0])
# 	print (p.parse ('\\int_0^1 x + y dx') [0])
# 	print (p.parse ('dx') [0])
# 	print (p.parse ('d / dx x') [0])
# 	print (p.parse ('d**2 / dx**2 x') [0])
# 	print (p.parse ('d**2 / dx dy x') [0])
# 	print (p.parse ('\\frac{d}{dx} x') [0])
# 	print (p.parse ('\\frac{d**2}{dx**2} x') [0])
# 	print (p.parse ('\\frac{d**2}{dxdy} x') [0])
# 	a = p.parse ('\\int_0^1x') [0]
# 	print (a)
# TODO: \int_0^\infty e^{-st} dt, sp.Piecewise

# Convert between internal AST and sympy expressions and write out LaTeX, simple and python code

import re
import sympy as sp
sp.numbers = sp.numbers # pylint medication


_FUNCS_PY_AND_TEX           = set (AST.FUNCS_PY_AND_TEX)
_FUNCS_ALL_PY               = set (AST.FUNCS_PY) | _FUNCS_PY_AND_TEX

_rec_var_diff_or_part_start = re.compile (r'^(?:d(?=[^_])|\\partial )')
_rec_num_deconstructed      = re.compile (r'^(-?)(\d*[^0.e])?(0*)(?:(\.)(0*)(\d*[^0e])?(0*))?(?:([eE])([+-]?\d+))?$') # -101000.000101000e+123 -> (-) (101) (000) (.) (000) (101) (000) (e) (+123)

_SYMPY_FLOAT_PRECISION      = None

#...............................................................................................
def set_precision (ast): # recurse through ast to set sympy float precision according to largest string of digits found
	global _SYMPY_FLOAT_PRECISION

	prec  = 15
	stack = [ast]

	while stack:
		ast = stack.pop ()

		if not isinstance (ast, AST):
			pass # do nothing
		elif ast.is_num:
			prec = max (prec, len (ast.num))
		else:
			stack.extend (ast [1:])

	_SYMPY_FLOAT_PRECISION = prec if prec > 15 else None

#...............................................................................................
def ast2tex (ast): # abstract syntax tree -> LaTeX text
	return _ast2tex_funcs [ast.op] (ast)

def _ast2tex_curly (ast):
	return f'{ast2tex (ast)}' if ast.is_single_unit else f'{{{ast2tex (ast)}}}'

def _ast2tex_paren (ast):
	return f'\\left({ast2tex (ast)} \\right)' if not ast.is_paren else ast2tex (ast)

def _ast2tex_paren_mul_exp (ast, ret_has = False, also = {'+'}):
	if ast.is_mul:
		s, has = _ast2tex_mul (ast, True)
	else:
		s, has = ast2tex (ast), ast.op in also

	s = f'\\left({s} \\right)' if has else s

	return (s, has) if ret_has else s

_rec_ast2tex_num = re.compile (r'^(-?\d*\.?\d*)[eE](?:(-\d+)|\+?(\d+))$')

def _ast2tex_num (ast):
	m = _rec_ast2tex_num.match (ast.num)

	return ast.num if not m else f'{m.group (1)} \\cdot 10^{_ast2tex_curly (AST ("#", m.group (2) or m.group (3)))}'

def _ast2tex_mul (ast, ret_has = False):
	t   = []
	p   = None
	has = False

	for n in ast.muls:
		s = f'{_ast2tex_paren (n) if n.is_add or (p and n.is_neg) else ast2tex (n)}'

		if p and (n.op in {'!', '#', 'lim', 'sum', 'intg'} or n.is_null_var or \
				(n.is_pow and n.base.is_pos_num) or (n.op in {'/', 'diff'} and p.op in {'#', '/', 'diff'})):
			t.append (f' \\cdot {s}')
			has = True

		elif p and (p in {('@', 'd'), ('@', '\\partial')} or p.is_sqrt or \
				(n.is_var and _rec_var_diff_or_part_start.match (n.var)) or \
				(p.is_var and _rec_var_diff_or_part_start.match (p.var))):
			t.append (f'\\ {s}')

		else:
			t.append (f'{"" if not p else " "}{s}')

		p = n

	return (''.join (t), has) if ret_has else ''.join (t)

def _ast2tex_pow (ast):
	b = ast2tex (ast.base)
	p = _ast2tex_curly (ast.exp)

	if ast.base.is_trigh_func_noninv_func and ast.exp.is_single_unit:
		i = len (ast.base.func) + (15 if ast.base.func in {'sech', 'csch'} else 1)

		return f'{b [:i]}^{p}{b [i:]}'

	if ast.base.op in {'(', '|', '@'} or ast.base.is_pos_num:
		return f'{b}^{p}'

	return f'\\left({b} \\right)^{p}'

def _ast2tex_log (ast):
	return \
			f'\\log{_ast2tex_paren (ast.log)}' \
			if ast.base is None else \
			f'\\log_{_ast2tex_curly (ast.base)}{_ast2tex_paren (ast.log)}'

def _ast2tex_func (ast):
	if ast.is_trigh_func:
		n = (f'\\operatorname{{{ast.func [1:]}}}^{{-1}}' \
				if ast.func in {'asech', 'acsch'} else \
				f'\\{ast.func [1:]}^{{-1}}') \
				if ast.func [0] == 'a' else \
				(f'\\operatorname{{{ast.func}}}' if ast.func in {'sech', 'csch'} else f'\\{ast.func}')

		return f'{n}{_ast2tex_paren (ast.arg)}'

	return \
			f'\\{ast.func}{_ast2tex_paren (ast.arg)}' \
			if ast.func in _FUNCS_PY_AND_TEX else \
			f'\\operatorname{{{ast.func}}}{_ast2tex_paren (ast.arg)}'

def _ast2tex_lim (ast):
	s = ast2tex (ast.to) if ast.dir is None else (ast2tex (AST ('^', ast.to, AST.Zero)) [:-1] + ast.dir)

	return f'\\lim_{{{ast2tex (ast.var)} \\to {s}}} {_ast2tex_paren_mul_exp (ast.lim)}'

def _ast2tex_sum (ast):
	return f'\\sum_{{{ast2tex (ast.var)} = {ast2tex (ast.from_)}}}^{_ast2tex_curly (ast.to)} {_ast2tex_paren_mul_exp (ast.sum)}' \

_rec_diff_var_single_start = re.compile (r'^d(?=[^_])')

def _ast2tex_diff (ast):
	ds = set ()
	p  = 0

	for n in ast.vars:
		if n.is_var:
			ds.add (n.var)
			p += 1
		else: # n = ('^', ('@', 'differential'), ('#', 'intg'))
			ds.add (n.base.var)
			p += int (n.exp.num)

	if len (ds) == 1 and ds.pop () [0] != '\\': # is not '\\partial'
		return f'\\frac{{d{"" if p == 1 else f"^{p}"}}}{{{"".join (ast2tex (n) for n in ast.vars)}}}{_ast2tex_paren (ast.diff)}'

	else:
		s = ''.join (_rec_diff_var_single_start.sub ('\\partial ', ast2tex (n)) for n in ast.vars)

		return f'\\frac{{\\partial{"" if p == 1 else f"^{p}"}}}{{{s}}}{_ast2tex_paren (ast.diff)}'

def _ast2tex_intg (ast):
	if ast.from_ is None:
		return \
				f'\\int \\ {ast2tex (ast.var)}' \
				if ast.intg is None else \
				f'\\int {ast2tex (ast.intg)} \\ {ast2tex (ast.var)}'
	else:
		return \
				f'\\int_{_ast2tex_curly (ast.from_)}^{_ast2tex_curly (ast.to)} \\ {ast2tex (ast.var)}' \
				if ast.intg is None else \
				f'\\int_{_ast2tex_curly (ast.from_)}^{_ast2tex_curly (ast.to)} {ast2tex (ast.intg)} \\ {ast2tex (ast.var)}'

_ast2tex_funcs = {
	'#': _ast2tex_num,
	'@': lambda ast: str (ast.var) if ast.var else '{}',
	'(': lambda ast: f'\\left({ast2tex (ast.paren)} \\right)',
	'|': lambda ast: f'\\left|{ast2tex (ast.abs)} \\right|',
	'-': lambda ast: f'-{_ast2tex_paren (ast.minus)}' if ast.minus.is_add else f'-{ast2tex (ast.minus)}',
	'!': lambda ast: f'{_ast2tex_paren (ast.fact)}!' if (ast.fact.op not in {'#', '@', '(', '|', '!', '^'} or ast.fact.is_neg_num) else f'{ast2tex (ast.fact)}!',
	'+': lambda ast: ' + '.join (ast2tex (n) for n in ast.adds).replace (' + -', ' - '),
	'*': _ast2tex_mul,
	'/': lambda ast: f'\\frac{{{ast2tex (ast.numer)}}}{{{ast2tex (ast.denom)}}}',
	'^': _ast2tex_pow,
	'log': _ast2tex_log,
	'sqrt': lambda ast: f'\\sqrt{{{ast2tex (ast.rad)}}}' if ast.idx is None else f'\\sqrt[{ast2tex (ast.idx)}]{{{ast2tex (ast.rad)}}}',
	'func': _ast2tex_func,
	'lim': _ast2tex_lim,
	'sum': _ast2tex_sum,
	'diff': _ast2tex_diff,
	'intg': _ast2tex_intg,
}

#...............................................................................................
def ast2simple (ast): # abstract syntax tree -> simple text
	return _ast2simple_funcs [ast.op] (ast)

def _ast2simple_curly (ast):
	return f'{ast2simple (ast)}' if ast.is_single_unit else f'{{{ast2simple (ast)}}}'

def _ast2simple_paren (ast):
	return f'({ast2simple (ast)})' if not ast.is_paren else ast2simple (ast)

def _ast2simple_paren_mul_exp (ast, ret_has = False, also = {'+'}):
	if ast.is_mul:
		s, has = _ast2simple_mul (ast, True)
	else:
		s, has = ast2simple (ast), ast.op in also

	s = f'({s})' if has else s

	return (s, has) if ret_has else s

def _ast2simple_mul (ast, ret_has = False):
	t   = []
	p   = None
	has = False

	for n in ast.muls:
		s = f'{_ast2simple_paren (n) if n.is_add or (p and n.is_neg) else ast2simple (n)}'

		if p and (n.op in {'!', '#', 'lim', 'sum', 'intg'} or n.is_null_var or \
				(n.is_pow and n.base.is_pos_num) or n.op in {'/', 'diff'} or p.op in {'/', 'diff'}):
			t.append (f' * {ast2simple (n)}')
			has = True

		elif p and (p in {('@', 'd'), ('@', '\\partial')} or \
				(n.op not in {'#', '@', '(', '|', '^'} or p.op not in {'#', '@', '(', '|', '^'}) or \
				(n.is_var and _rec_var_diff_or_part_start.match (n.var)) or \
				(p.is_var and _rec_var_diff_or_part_start.match (p.var))):
			t.append (f' {s}')

		else:
			t.append (s)

		p = n

	return (''.join (t), has) if ret_has else ''.join (t)

def _ast2simple_div (ast):
	n, ns = _ast2simple_paren_mul_exp (ast.numer, True, {'+', '/', 'lim', 'sum', 'diff'})
	d, ds = _ast2simple_paren_mul_exp (ast.denom, True, {'+', '/', 'lim', 'sum', 'diff'})

	return f'{n}{" / " if ns or ds else "/"}{d}'

def _ast2simple_pow (ast):
	b = ast2simple (ast.base)
	p = f'{ast2simple (ast.exp)}' if ast.exp.op in {'+', '*', '/', 'lim', 'sum', 'diff', 'intg'} else ast2simple (ast.exp)

	if ast.base.is_trigh_func_noninv_func and ast.exp.is_single_unit:
		i = len (ast.base.func)

		return f'{b [:i]}^{p}{b [i:]}'

	if ast.base.op in {'@', '(', '|'} or ast.base.is_pos_num:
		return f'{b}**{p}'

	return f'({b})**{p}'

def _ast2simple_log (ast):
	return \
			f'log{_ast2simple_paren (ast.log)}' \
			if ast.base is None else \
			f'log_{_ast2simple_curly (ast.base)}{_ast2simple_paren (ast.log)}'

def _ast2simple_func (ast):
	if ast.is_trigh_func:
		return f'{ast.func}{_ast2simple_paren (ast.arg)}'

	return \
			f'{ast.func}{_ast2simple_paren (ast.arg)}' \
			if ast.func in _FUNCS_ALL_PY else \
			f'${ast.func}{_ast2simple_paren (ast.arg)}'

def _ast2simple_lim (ast):
	s = ast2simple (ast.to) if ast.dir is None else ast2simple (AST ('^', ast [3], AST.Zero)) [:-1] + ast [4]

	return f'\\lim_{{{ast2simple (ast.var)} \\to {s}}} {_ast2simple_paren_mul_exp (ast.lim)}'

def _ast2simple_sum (ast):
	return f'\\sum_{{{ast2simple (ast.var)}={ast2simple (ast.from_)}}}^{_ast2simple_curly (ast.to)} {_ast2simple_paren_mul_exp (ast.sum)}' \

_ast2simple_diff_single_rec = re.compile ('^d')

def _ast2simple_diff (ast):
	ds = set ()
	p  = 0

	for n in ast.vars:
		if n.is_var:
			ds.add (n.var)
			p += 1
		else: # n = ('^', ('@', 'differential'), ('#', 'intg'))
			ds.add (n.base.var)
			p += int (n.exp.num)

	if len (ds) == 1 and ds.pop () [0] != '\\': # is not '\\partial'
		return f'd{"" if p == 1 else f"^{p}"}/{"".join (ast2simple (n) for n in ast.vars)}{_ast2simple_paren (ast.diff)}'

	else:
		s = ''.join (_ast2simple_diff_single_rec.sub ('\\partial ', ast2simple (n)) for n in ast.vars)

		return f'\\partial{"" if p == 1 else f"^{p}"}/{s}{_ast2simple_paren (ast.diff)}'

def _ast2simple_intg (ast):
	if ast.from_ is None:
		return \
				f'\\int {ast2simple (ast.var)}' \
				if ast.intg is None else \
				f'\\int {ast2simple (ast.intg)} {ast2simple (ast.var)}'
	else:
		return \
				f'\\int_{_ast2simple_curly (ast.from_)}^{_ast2simple_curly (ast.to)} {ast2simple (ast.var)}' \
				if ast.intg is None else \
				f'\\int_{_ast2simple_curly (ast.from_)}^{_ast2simple_curly (ast.to)} {ast2simple (ast.intg)} {ast2simple (ast.var)}'

_ast2simple_funcs = {
	'#': lambda ast: ast.num,
	'@': lambda ast: ast.var,
	'(': lambda ast: f'({ast2simple (ast.paren)})',
	'|': lambda ast: f'|{ast2simple (ast.abs)}|',
	'-': lambda ast: f'-{_ast2simple_paren (ast.minus)}' if ast.minus.is_add else f'-{ast2simple (ast.minus)}',
	'!': lambda ast: f'{_ast2simple_paren (ast.fact)}!' if (ast.fact.op not in {'#', '@', '(', '|', '!', '^'} or ast.fact.is_neg_num) else f'{ast2simple (ast.fact)}!',
	'+': lambda ast: ' + '.join (ast2simple (n) for n in ast.adds).replace (' + -', ' - '),
	'*': _ast2simple_mul,
	'/': _ast2simple_div,
	'^': _ast2simple_pow,
	'log': _ast2simple_log,
	'sqrt': lambda ast: f'\\sqrt{{{ast2simple (ast.rad)}}}' if ast.idx is None else f'\\sqrt[{ast2simple (ast.idx)}]{{{ast2simple (ast.rad)}}}',
	'func': _ast2simple_func,
	'lim': _ast2simple_lim,
	'sum': _ast2simple_sum,
	'diff': _ast2simple_diff,
	'intg': _ast2simple_intg,
}

#...............................................................................................
def ast2py (ast): # abstract syntax tree -> python code text
	return _ast2py_funcs [ast.op] (ast)

def _ast2py_curly (ast):
	return \
			_ast2py_paren (ast) \
			if ast.op in {'+', '*', '/'} or ast.is_neg_num or (ast.is_log and ast.base is not None) else \
			ast2py (ast)

def _ast2py_paren (ast):
	return f'({ast2py (ast)})' if not ast.is_paren else ast2py (ast)

def _ast2py_div (ast):
	n = _ast2py_curly (ast.numer)
	d = _ast2py_curly (ast.denom)

	return f'{n}{" / " if ast.numer.op not in {"#", "@", "-"} or ast.denom.op not in {"#", "@", "-"} else "/"}{d}'

def _ast2py_pow (ast):
	b = _ast2py_curly (ast.base)
	e = _ast2py_curly (ast.exp)

	return f'{b}**{e}'

def _ast2py_log (ast):
	return \
			f'log{_ast2py_paren (ast.log)}' \
			if ast.base is None else \
			f'log{_ast2py_paren (ast.log)} / log{_ast2py_paren (ast.base)}' \

def _ast2py_lim (ast):
	return \
		f'''Limit({ast2py (ast.lim)}, {ast2py (ast.var)}, {ast2py (ast.to)}''' \
		f'''{", dir='+-'" if ast.dir is None else ", dir='-'" if ast.dir == '-' else ""})'''

def _ast2py_diff (ast):
	args = sum ((
			(ast2py (AST ('@', _rec_var_diff_or_part_start.sub ('', n.var))),) \
			if n.is_var else \
			(ast2py (AST ('@', _rec_var_diff_or_part_start.sub ('', n.base.var))), str (n.exp.num)) \
			for n in ast.vars \
			), ())

	return f'Derivative({ast2py (ast.diff)}, {", ".join (args)})'

def _ast2py_intg (ast):
	if ast.from_ is None:
		return \
				f'Integral(1, {ast2py (AST ("@", _rec_var_diff_or_part_start.sub ("", ast.var.var)))})' \
				if ast.intg is None else \
				f'Integral({ast2py (ast.intg)}, {ast2py (AST ("@", _rec_var_diff_or_part_start.sub ("", ast.var.var)))})'
	else:
		return \
				f'Integral(1, ({ast2py (AST ("@", _rec_var_diff_or_part_start.sub ("", ast.var.var)))}, {ast2py (ast.from_)}, {ast2py (ast.to)}))' \
				if ast.intg is None else \
				f'Integral({ast2py (ast.intg)}, ({ast2py (AST ("@", _rec_var_diff_or_part_start.sub ("", ast.var.var)))}, {ast2py (ast.from_)}, {ast2py (ast.to)}))'

_rec_ast2py_varname_sanitize = re.compile (r'\{|\}')

_ast2py_funcs = {
	'#': lambda ast: ast.num,
	'@': lambda ast: _rec_ast2py_varname_sanitize.sub ('_', ast.var).replace ('\\infty', 'oo').replace ('\\', '').replace ("'", '_prime'),
	'(': lambda ast: f'({ast2py (ast.paren)})',
	'|': lambda ast: f'abs({ast2py (ast.abs)})',
	'-': lambda ast: f'-{_ast2py_paren (ast.minus)}' if ast.minus.is_add else f'-{ast2py (ast.minus)}',
	'!': lambda ast: f'factorial({ast2py (ast.fact)})',
	'+': lambda ast: ' + '.join (ast2py (n) for n in ast.adds).replace (' + -', ' - '),
	'*': lambda ast: '*'.join (_ast2py_paren (n) if n.is_add else ast2py (n) for n in ast.muls),
	'/': _ast2py_div,
	'^': _ast2py_pow,
	'log': _ast2py_log,
	'sqrt': lambda ast: f'sqrt{_ast2py_paren (ast.rad)}' if ast.base is None else ast2py (AST ('^', ast.rad, ('/', AST.One, ast.idx))),
	'func': lambda ast: f'{ast.func}({ast2py (ast.arg)})',
	'lim': _ast2py_lim,
	'sum': lambda ast: f'Sum({ast2py (ast.sum)}, ({ast2py (ast.var)}, {ast2py (ast.from_)}, {ast2py (ast.to)}))',
	'diff': _ast2py_diff,
	'intg': _ast2py_intg,
}

#...............................................................................................
def ast2spt (ast): # abstract syntax tree -> sympy tree (expression)
	return _ast2spt_funcs [ast.op] (ast)

def _ast2spt_diff (ast):
	args = sum ((
			(ast2spt (AST ('@', _rec_var_diff_or_part_start.sub ('', n [1]))),) \
			if n.is_var else \
			(ast2spt (AST ('@', _rec_var_diff_or_part_start.sub ('', n [1] [1]))), sp.Integer (n [2] [1])) \
			for n in ast.vars \
			), ())

	return sp.diff (ast2spt (ast [1]), *args)

def _ast2spt_intg (ast):
	if ast.from_ is None:
		return \
				sp.integrate (1, ast2spt (AST ('@', _rec_var_diff_or_part_start.sub ('', ast.var.var)))) \
				if ast.intg is None else \
				sp.integrate (ast2spt (ast.intg), ast2spt (AST ('@', _rec_var_diff_or_part_start.sub ('', ast.var.var))))
	else:
		return \
				sp.integrate (1, (ast2spt (AST ('@', _rec_var_diff_or_part_start.sub ('', ast.var.var))), ast2spt (ast.from_), ast2spt (ast.to))) \
				if ast.intg is None else \
				sp.integrate (ast2spt (ast [1]), (ast2spt (AST ('@', _rec_var_diff_or_part_start.sub ('', ast.var.var))), ast2spt (ast.from_), ast2spt (ast.to)))

_ast2spt_consts = {
	'i': sp.I,
	'\\pi': sp.pi,
	'e': sp.E,
	'\\infty': sp.oo,
}

_ast2spt_func_alias = {
	'?': 'N',
}

_ast2spt_funcs = {
	'#': lambda ast: sp.Integer (ast [1]) if ast.is_int_text (ast.num) else sp.Float (ast.num, _SYMPY_FLOAT_PRECISION),
	'@': lambda ast: _ast2spt_consts.get (ast.var, sp.Symbol (ast.var)),
	'(': lambda ast: ast2spt (ast.paren),
	'|': lambda ast: sp.Abs (ast2spt (ast.abs)),
	'-': lambda ast: -ast2spt (ast.minus),
	'!': lambda ast: sp.factorial (ast2spt (ast.fact)),
	'+': lambda ast: sp.Add (*(ast2spt (n) for n in ast.adds)),
	'*': lambda ast: sp.Mul (*(ast2spt (n) for n in ast.muls)),
	'/': lambda ast: sp.Mul (ast2spt (ast.numer), sp.Pow (ast2spt (ast.denom), -1)),
	'^': lambda ast: sp.Pow (ast2spt (ast.base), ast2spt (ast.exp)),
	'log': lambda ast: sp.log (ast2spt (ast.log)) if ast.base is None else sp.log (ast2spt (ast.log), ast2spt (ast.base)),
	'sqrt': lambda ast: sp.Pow (ast2spt (ast.rad), sp.Pow (2, -1)) if ast.idx is None else sp.Pow (ast2spt (ast.rad), sp.Pow (ast2spt (ast.idx), -1)),
	'func': lambda ast: getattr (sp, _ast2spt_func_alias.get (ast.func, ast.func)) (ast2spt (ast.arg)),
	'lim': lambda ast: sp.limit (ast2spt (ast.lim), ast2spt (ast.var), ast2spt (ast.to), dir = '+-' if ast.dir is None else ast [4]),
	'sum': lambda ast: sp.Sum (ast2spt (ast.sum), (ast2spt (ast.var), ast2spt (ast.from_), ast2spt (ast.to))).doit (),
	'diff': _ast2spt_diff,
	'intg': _ast2spt_intg,
}

#...............................................................................................
def spt2ast (spt): # sympy tree (expression) -> abstract syntax tree
	for cls in spt.__class__.__mro__:
		func = _spt2ast_funcs.get (cls)

		if func:
			return func (spt)

	raise RuntimeError (f'unexpected class {spt.__class__.__name__!r}')

def _spt2ast_nan (spt):
	raise ValueError ('undefined')

def _spt2ast_num (spt):
	m = _rec_num_deconstructed.match (str (spt))
	g = [g or '' for g in m.groups ()]

	if g [5]:
		return AST ('#', ''.join (g [:6] + g [7:]))

	e = len (g [2]) + (int (g [8]) if g [8] else 0)

	return AST ('#', \
			f'{g [0]}{g [1]}e+{e}'     if e >= 16 else \
			f'{g [0]}{g [1]}{"0" * e}' if e >= 0 else \
			f'{g [0]}{g [1]}e{e}')

def _spt2ast_mul (spt):
	if spt.args [0] == -1:
		return AST ('-', spt2ast (sp.Mul (*spt.args [1:])))

	if spt.args [0].is_negative:
		return AST ('-', spt2ast (sp.Mul (-spt.args [0], *spt.args [1:])))

	numer = []
	denom = []

	for arg in spt.args:
		if isinstance (arg, sp.Pow) and arg.args [1].is_negative:
			denom.append (spt2ast (sp.Pow (arg.args [0], -arg.args [1])))
		else:
			numer.append (spt2ast (arg))

	if not denom:
		return AST ('*', tuple (numer)) if len (numer) > 1 else numer [0]

	if not numer:
		return AST ('/', AST.One, AST ('*', tuple (denom)) if len (denom) > 1 else denom [0])

	return AST ('/', AST ('*', tuple (numer)) if len (numer) > 1 else numer [0], \
			AST ('*', tuple (denom)) if len (denom) > 1 else denom [0])

def _spt2ast_pow (spt):
	if spt.args [1].is_negative:
		return AST ('/', AST.One, spt2ast (sp.Pow (spt.args [0], -spt.args [1])))

	if spt.args [1] == 0.5:
		return AST ('sqrt', spt2ast (spt.args [0]))

	return AST ('^', spt2ast (spt.args [0]), spt2ast (spt.args [1]))

def _spt2ast_func (spt):
	return AST ('func', spt.__class__.__name__, spt2ast (spt.args [0]))

def _spt2ast_integral (spt):
	return \
			AST ('intg', spt2ast (spt.args [0]), AST ('@', f'd{spt2ast (spt.args [1] [0]) [1]}'), spt2ast (spt.args [1] [1]), spt2ast (spt.args [1] [2])) \
			if len (spt.args [1]) == 3 else \
			AST ('intg', spt2ast (spt.args [0]), AST ('@', f'd{spt2ast (spt.args [1] [0]) [1]}'))

_spt2ast_funcs = {
	sp.numbers.NaN: _spt2ast_nan,
	sp.Integer: _spt2ast_num,
	sp.Float: _spt2ast_num,
	sp.Rational: lambda spt: AST ('/', ('#', str (spt.p)), ('#', str (spt.q))) if spt.p >= 0 else AST ('-', ('/', ('#', str (-spt.p)), ('#', str (spt.q)))),
	sp.numbers.ImaginaryUnit: lambda ast: AST.I,
	sp.numbers.Pi: lambda spt: AST.Pi,
	sp.numbers.Exp1: lambda spt: AST.E,
	sp.exp: lambda spt: AST ('^', AST.E, spt2ast (spt.args [0])),
	sp.numbers.Infinity: lambda spt: AST.Infty,
	sp.numbers.NegativeInfinity: lambda spt: AST ('-', AST.Infty),
	sp.numbers.ComplexInfinity: lambda spt: AST.Infty, # not exactly but whatever
	sp.Symbol: lambda spt: AST ('@', spt.name),

	sp.Abs: lambda spt: AST ('|', spt2ast (spt.args [0])),
	sp.Add: lambda spt: AST ('+', tuple (spt2ast (arg) for arg in reversed (spt._sorted_args))),
	sp.arg: lambda spt: AST ('func', 'arg', spt2ast (spt.args [0])),
	sp.factorial: lambda spt: AST ('!', spt2ast (spt.args [0])),
	sp.log: lambda spt: AST ('log', spt2ast (spt.args [0])) if len (spt.args) == 1 else AST ('log', spt2ast (spt.args [0]), spt2ast (spt.args [1])),
	sp.Mul: _spt2ast_mul,
	sp.Pow: _spt2ast_pow,
	sp.functions.elementary.trigonometric.TrigonometricFunction: _spt2ast_func,
	sp.functions.elementary.hyperbolic.HyperbolicFunction: _spt2ast_func,
	sp.functions.elementary.trigonometric.InverseTrigonometricFunction: _spt2ast_func,
	sp.functions.elementary.hyperbolic.InverseHyperbolicFunction: _spt2ast_func,

	sp.Sum: lambda spt: AST ('sum', spt2ast (spt.args [0]), spt2ast (spt.args [1] [0]), spt2ast (spt.args [1] [1]), spt2ast (spt.args [1] [2])),
	sp.Integral: _spt2ast_integral,
}

class sym: # for single script
	set_precision = set_precision
	ast2tex       = ast2tex
	ast2simple    = ast2simple
	ast2py        = ast2py
	ast2spt       = ast2spt
	spt2ast       = spt2ast

## DEBUG!
# if __name__ == '__main__':
# 	print (_rec_num_deconstructed.match ('10100.0010100').groups ())
# 	t = ast2spt (('intg', ('@', 'dx')))
# 	print (t)
#!/usr/bin/env python
# python 3.6+

import json
import os
import re
import subprocess
import sys
import time
import threading
import traceback

from urllib.parse import parse_qs
from socketserver import ThreadingMixIn
from http.server import HTTPServer, SimpleHTTPRequestHandler


import sympy as sp ## DEBUG!


#...............................................................................................
_last_ast = AST.Zero # last evaluated expression for _ usage

def _ast_replace (ast, src, dst):
	return \
			ast if not isinstance (ast, AST) else \
			dst if ast == src else \
			AST (*(_ast_replace (s, src, dst) for s in ast))

class Handler (SimpleHTTPRequestHandler):
	def do_GET (self):
		if self.path == '/':
			self.path = '/index.html'

		return SimpleHTTPRequestHandler.do_GET (self)

	def do_POST (self):
		global _last_ast

		req    = parse_qs (self.rfile.read (int (self.headers ['Content-Length'])).decode ('utf8'), keep_blank_values = True)
		parser = sparser.Parser ()

		for key, val in list (req.items ()):
			if len (val) == 1:
				req [key] = val [0]

		if req ['mode'] == 'validate':
			ast, erridx, autocomplete = parser.parse (req ['text'])
			tex = simple = py         = None

			if ast is not None:
				ast    = _ast_replace (ast, ('@', '_'), _last_ast)
				tex    = sym.ast2tex (ast)
				simple = sym.ast2simple (ast)
				py     = sym.ast2py (ast)

				## DEBUG!
				print ()
				print ('ast:   ', ast)
				print ('tex:   ', tex)
				print ('simple:', simple)
				print ('py:    ', py)
				print ()
				## DEBUG!

			resp = {
				'tex'         : tex,
				'simple'      : simple,
				'py'          : py,
				'erridx'      : erridx,
				'autocomplete': autocomplete,
			}

		else: # mode = 'evaluate'
			try:
				ast, _, _ = parser.parse (req ['text'])
				ast       = _ast_replace (ast, ('@', '_'), _last_ast)

				sym.set_precision (ast)

				spt       = sym.ast2spt (ast)
				ast       = sym.spt2ast (spt)
				_last_ast = ast

				## DEBUG!
				print ()
				print ('spt:        ', repr (spt))
				print ('sympy latex:', sp.latex (spt))
				print ()
				## DEBUG!

				resp      = {
					'tex'   : sym.ast2tex (ast),
					'simple': sym.ast2simple (ast),
					'py'    : sym.ast2py (ast),
				}

			except Exception:
				resp = {'err': ''.join (traceback.format_exception (*sys.exc_info ())).replace ('  ', '&emsp;').strip ().split ('\n')}

		resp ['mode'] = req ['mode']
		resp ['idx']  = req ['idx']

		self.send_response (200)
		self.send_header ("Content-type", "application/json")
		self.end_headers ()
		self.wfile.write (json.dumps (resp).encode ('utf-8'))

class ThreadingHTTPServer (ThreadingMixIn, HTTPServer):
	pass

#...............................................................................................
_month_name = (None, 'Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec')

if __name__ == '__main__':
	try:
		if 'SYMPAD_RUNNED' not in os.environ:
			args = [sys.executable] + sys.argv

			while 1:
				subprocess.run (args, env = {**os.environ, 'SYMPAD_RUNNED': '1'})

		if len (sys.argv) < 2:
			host, port = 'localhost', 8000
		else:
			host, port = (re.split (r'(?<=\]):' if sys.argv [1].startswith ('[') else ':', sys.argv [1]) + ['8000']) [:2]
			host, port = host.strip ('[]'), int (port)

		watch   = ('lalr1.py', 'sparser.py', 'sym.py', 'server.py')
		tstamps = [os.stat (fnm).st_mtime for fnm in watch]
		httpd   = HTTPServer ((host, port), Handler) # ThreadingHTTPServer ((host, port), Handler)
		thread  = threading.Thread (target = httpd.serve_forever, daemon = True)

		thread.start ()

		def log_message (msg):
			y, m, d, hh, mm, ss, _, _, _ = time.localtime (time.time ())

			sys.stderr.write (f'{httpd.server_address [0]} - - ' \
					f'[{"%02d/%3s/%04d %02d:%02d:%02d" % (d, _month_name [m], y, hh, mm, ss)}] {msg}\n')

		log_message (f'Serving on {httpd.server_address [0]}:{httpd.server_address [1]}')

		while 1:
			time.sleep (0.5)

			if [os.stat (fnm).st_mtime for fnm in watch] != tstamps:
				log_message ('Files changed, restarting...')

				break

	except KeyboardInterrupt:
		pass

_FILES = {

	'style.css': # style.css

"""* {
	box-sizing: border-box;
	margin: 0;
	padding: 0;
}

body {
	margin-top: 1em;
	margin-bottom: 6em;
	cursor: default;
}

#Clipboard {
	position: fixed;
	bottom: 0;
	color: transparent;
	border: 0px;
}

#Background {
	position: fixed;
	z-index: -1;
	left: 0;
	top: 0;
}

#Greeting {
	position: fixed;
	left: 50%;
	top: 50%;
	transform: translate(-50%, -50%);
	color: #aaa;
}

#InputBG {
	position: fixed;
	z-index: 2;
	height: 4em;
	bottom: 0;
	left: 0;
	right: 0;
	background-color: white;
}

#Input {
	position: fixed;
	z-index: 3;
	bottom: 2em;
	left: 4em;
	right: 1em;
	border-color: transparent;
	outline-color: transparent;
	background-color: transparent;
}

#InputOverlay {
	z-index: 4;
}

#OverlayGood {
	-webkit-text-fill-color: transparent;
}

#OverlayError {
	-webkit-text-fill-color: #f44;
}

#OverlayAutocomplete {
	-webkit-text-fill-color: #999;
}

.LogEntry {
	width: 100%;
	margin-bottom: 1.5em;
}

.LogMargin {
	display: inline-block;
	height: 100%;
	width: 4em;
	vertical-align: top;
	text-align: right;
	padding-right: 0.5em;
}

.LogBody {
	display: inline-block;
	margin-right: -9999em;
}

.LogWait {
	vertical-align: top;
}

.LogInput {
	margin-bottom: 0.75em;
	width: fit-content;
	cursor: pointer;
}

.LogEval {
	position: relative;
	margin-bottom: 0.25em;
	cursor: pointer;
}

.LogError {
	margin-bottom: 0.25em;
	color: red;
}

.LogErrorTriange {
	position: absolute;
	left: -1.25em;
	top: 0.25em;
	font-size: 0.7em;
	/* left: -1em;
	top: 0; */
	color: red;
	font-weight: bold;
}




/* .blinking {
	animation: blinkingText 1s infinite;
}

@keyframes blinkingText {
	0%   { color: #000; }
	49%  { color: #000; }
	50%  { color: transparent; }
	100% { color: transparent; }
} */

/* .rotator {
	display: inline-block;
	animation: rotator 1s infinite;
}

@keyframes rotator {
	0%   { rotate: 0deg; }
	25%  { rotate: 90deg; }
	50%  { rotate: 180deg; }
	75%  { rotate: 270deg; }
	100% { rotate: 360deg; }
}
 */

/* .spinner1 {
	position: absolute;
	animation: spinner1 1s infinite;
}

@keyframes spinner1 {
	0%   { color: #000; }
	25%  { color: transparent; }
	75%  { color: transparent; }
	100% { color: #000; }
}

.spinner2 {
	position: absolute;
	animation: spinner2 1s infinite;
}

@keyframes spinner2 {
	0%   { color: transparent; }
	25%  { color: #000; }
	50%  { color: transparent; }
	100% { color: transparent; }
}

.spinner3 {
	position: absolute;
	animation: spinner3 1s infinite;
}

@keyframes spinner3 {
	0%   { color: transparent; }
	25%  { color: transparent; }
	50%  { color: #000; }
	75%  { color: transparent; }
	100% { color: transparent; }
}

.spinner4 {
	position: absolute;
	animation: spinner4 1s infinite;
}

@keyframes spinner4 {
	0%   { color: transparent; }
	50%  { color: transparent; }
	75%  { color: #000; }
	100% { color: transparent; }
} */
""",

	'script.js': # script.js

"""// TODO: Arrow keys in Edge?
// TODO: Change how error, auto and good text are displayed?

// TODO: Need to copyInputStyle when bottom scroll bar appears.

// Check if body height is higher than window height :)
// if ($(document).height() > $(window).height()) {
// 	alert("Vertical Scrollbar! D:");
// }

// // Check if body width is higher than window width :)
// if ($(document).width() > $(window).width()) {
// 	alert("Horizontal Scrollbar! D:<");
// }

var URL              = '/';
var MJQueue          = null;
var MarginTop        = Infinity;
var PreventFocusOut  = true;

var History          = [];
var HistIdx          = 0;
var LogIdx           = 0;
var UniqueID         = 1;

var Validations      = [undefined];
var Evaluations      = [undefined];
var ErrorIdx         = null;
var Autocomplete     = [];

var LastClickTime    = 0;
var NumClicks        = 0;

var GreetingFadedOut = false;

//...............................................................................................
function generateBG () {
	function writeRandomData (data, x0, y0, width, height) {
		let p, d;

		for (let y = y0; y < height; y ++) {
			p = (width * y + x0) * 4;

			for (let x = x0; x < width; x ++) {
				d            = 244 + Math.floor (Math.random () * 12);
				data [p]     = data [p + 1] = d;
				data [p + 2] = d - 8;
				data [p + 3] = 255;
				p            = p + 4;
			}
		}
	}

	let canv    = document.getElementById ('Background');
	canv.width  = window.innerWidth;
	canv.height = window.innerHeight;
	let ctx     = canv.getContext ('2d');
	let imgd    = ctx.getImageData (0, 0, canv.width, canv.height); // ctx.createImageData (width, height);

	writeRandomData (imgd.data, 0, 0, canv.width, canv.height);
	ctx.putImageData (imgd, 0, 0);

	canv        = $('#InputBG') [0];
	ctx         = canv.getContext ('2d');
	canv.width  = window.innerWidth;

	ctx.putImageData (imgd, 0, 0);
}

//...............................................................................................
function copyInputStyle () {
	JQInput.css ({left: $('#LogEntry1').position ().left})
	JQInput.width ($('#Log').width ());

	let style   = getComputedStyle (document.getElementById ('Input'));
	let overlay = document.getElementById ('InputOverlay');

  for (let prop of style) {
    overlay.style [prop] = style [prop];
	}

	overlay.style ['backgroundColor'] = 'transparent';
}

//...............................................................................................
function scrollToEnd () {
	window.scrollTo (0, document.body.scrollHeight);
}

//...............................................................................................
function resize () {
	console.log ('resize');
	copyInputStyle ();
	scrollToEnd ();
	generateBG ();
}

//...............................................................................................
function logResize () {
	let margin = Math.max (BodyMarginTop, Math.floor (window.innerHeight - $('body').height () - BodyMarginBottom + 2)); // 2 is fudge factor

	if (margin < MarginTop) {
		MarginTop = margin
		$('body').css ({'margin-top': margin});
	}
}

//...............................................................................................
function readyMathJax () {
	window.MJQueue = MathJax.Hub.queue;

	var TEX        = MathJax.InputJax.TeX;
	var PREFILTER  = TEX.prefilterMath;

	TEX.Augment ({
		prefilterMath: function (tex, displaymode, script) {
			return PREFILTER.call (TEX, '\\displaystyle{' + tex + '}', displaymode, script);
		}
	});
}

//...............................................................................................
function reprioritizeMJQueue () {
	let p = MJQueue.queue.pop ();

	if (p !== undefined) {
		MJQueue.queue.splice (0, 0, p);
	}
}

//...............................................................................................
function addLogEntry () {
	LogIdx += 1;

	$('#Log').append (`
			<div class="LogEntry"><div class="LogMargin">${LogIdx}.</div><div class="LogBody" id="LogEntry${LogIdx}"><div class="LogInput" id="LogInput${LogIdx}">
				<img class="LogWait" id="LogInputWait${LogIdx}" src="https://i.gifer.com/origin/3f/3face8da2a6c3dcd27cb4a1aaa32c926_w200.webp" width="16" style="visibility: hidden">
			</div></div></div>`)

	Validations.push (undefined);
	Evaluations.push (undefined);
}

//...............................................................................................
function writeToClipboard (text) {
	PreventFocusOut = false;

	$('#Clipboard').val (text);
	$('#Clipboard').focus ();
	$('#Clipboard').select ();
	document.execCommand ('copy');

	PreventFocusOut = true;

	JQInput.focus ();
}

//...............................................................................................
function copyToClipboard (e, val_or_eval, idx) {
	let t = performance.now ();

	if ((t - LastClickTime) > 500) {
		NumClicks = 1;
	} else{
		NumClicks += 1;
	}

	LastClickTime = t;
	let resp      = (val_or_eval ? Evaluations : Validations) [idx];

	writeToClipboard (NumClicks == 1 ? resp.simple : NumClicks == 2 ? resp.py : resp.tex);

	e.style.color      = 'transparent';
	e.style.background = 'black';

	setTimeout (function () {
		e.style.color      = 'black';
		e.style.background = 'transparent';
	}, 100);
}

//...............................................................................................
function updateOverlay (text, erridx, autocomplete) {
	ErrorIdx     = erridx;
	Autocomplete = autocomplete;

	if (ErrorIdx === null) {
		$('#OverlayGood').text (text);
		$('#OverlayError').text ('');

	} else {
		$('#OverlayGood').text (text.substr (0, ErrorIdx));
		$('#OverlayError').text (text.substr (ErrorIdx));
	}

	$('#OverlayAutocomplete').text (Autocomplete.join (''));
}

//...............................................................................................
function ajaxResponse (resp) {
	if (resp.mode == 'validate') {
		if (Validations [resp.idx] !== undefined && Validations [resp.idx].subidx >= resp.subidx) {
			return; // ignore out of order responses
		}

		if (resp.tex !== null) {
			Validations [resp.idx] = resp;

			let eLogInput = document.getElementById ('LogInput' + resp.idx);

			let queue              = [];
			[queue, MJQueue.queue] = [MJQueue.queue, queue];

			MJQueue.queue = queue.filter (function (obj, idx, arr) { // remove previous pending updates to same element
				return obj.data [0].parentElement !== eLogInput;
			})

			let eLogInputWait              = document.getElementById ('LogInputWait' + resp.idx);
			eLogInputWait.style.visibility = '';

			let idMath = 'LogInputMath' + UniqueID ++;
			$(eLogInput).append (`<span id="${idMath}" onclick="copyToClipboard (this, 0, ${resp.idx})" style="visibility: hidden">$${resp.tex}$</span>`);
			let eMath  = document.getElementById (idMath);

			MJQueue.Push (['Typeset', MathJax.Hub, eMath, function () {
				if (eMath === eLogInput.children [eLogInput.children.length - 1]) {
					eLogInput.appendChild (eLogInputWait);

					for (let i = eLogInput.children.length - 3; i >= 0; i --) {
						eLogInput.removeChild (eLogInput.children [i]);
					}

					eLogInputWait.style.visibility = 'hidden';
					eMath.style.visibility         = '';

					logResize ();
				}
			}]);

			reprioritizeMJQueue ();
		}

		updateOverlay (JQInput.val (), resp.erridx, resp.autocomplete);

	} else { // resp.mode == 'evaluate'
		Evaluations [resp.idx] = resp;

		let eLogEval = document.getElementById ('LogEval' + resp.idx);

		if (resp.err !== undefined) {
			eLogEval.removeChild (document.getElementById ('LogEvalWait' + resp.idx));

			if (resp.err.length > 1) {
				let idLogErrorHidden = 'LogErrorHidden' + resp.idx;
				$(eLogEval).append (`<div id="${idLogErrorHidden}" style="display: none"></div>`);
				var eLogErrorHidden  = document.getElementById (idLogErrorHidden);

				for (let i = 0; i < resp.err.length - 1; i ++) {
					$(eLogErrorHidden).append (`<div class="LogError">${resp.err [i]}</div>`);
				}
			}

			let idLogErrorTriangle = 'LogErrorTriangle' + resp.idx;
			$(eLogEval).append (`<div class="LogError">${resp.err [resp.err.length - 1]}</div><div class="LogErrorTriange" id="LogErrorTriangle${resp.idx}">\u25b7</div>`);
			var eLogErrorTriangle  = document.getElementById (idLogErrorTriangle);

			$(eLogEval).click (function () {
				if (eLogErrorHidden.style.display === 'none') {
					eLogErrorHidden.style.display = 'block';
					eLogErrorTriangle.innerText   = '\u25bd'; // '\u25bc'; // '-'; // '\u25bc';
				} else {
					eLogErrorHidden.style.display = 'none';
					eLogErrorTriangle.innerText   = '\u25b7'; // '\u25e2'; // '+'; // '\u25b6';
				}

				logResize ();
			});

			logResize ();
			scrollToEnd ();

		} else { // no error
			let idLogEvalMath = 'LogEvalMath' + resp.idx;
			$(eLogEval).append (`<span id="${idLogEvalMath}" style="visibility: hidden" onclick="copyToClipboard (this, 1, ${resp.idx})">$${resp.tex}$</span>`);
			let eLogEvalMath  = document.getElementById (idLogEvalMath);

			MJQueue.Push (['Typeset', MathJax.Hub, eLogEvalMath, function () {
				eLogEval.removeChild (document.getElementById ('LogEvalWait' + resp.idx));

				eLogEvalMath.style.visibility = '';

				logResize ();
				scrollToEnd ();
			}]);

			reprioritizeMJQueue ();
		}
	}
}

//...............................................................................................
function inputting (text, reset = false) {
	if (reset) {
		ErrorIdx     = null;
		Autocomplete = [];

		JQInput.val (text);
	}

	updateOverlay (text, ErrorIdx, Autocomplete);

	$.ajax ({
		url: URL,
		type: 'POST',
		cache: false,
		dataType: 'json',
		success: ajaxResponse,
		data: {
			mode: 'validate',
			idx: LogIdx,
			subidx: UniqueID ++,
			text: text,
		},
	});
}

//...............................................................................................
function inputted (text) {
	$.ajax ({
		url: URL,
		type: 'POST',
		cache: false,
		dataType: 'json',
		success: ajaxResponse,
		data: {
			mode: 'evaluate',
			idx: LogIdx,
			text: text,
		},
	});

	$('#LogEntry' + LogIdx).append (`
			<div class="LogEval" id="LogEval${LogIdx}">
				<img class="LogWait" id="LogEvalWait${LogIdx}" src="https://i.gifer.com/origin/3f/3face8da2a6c3dcd27cb4a1aaa32c926_w200.webp" width="16">
			</div>`);

	History.push (text);

	HistIdx = History.length;

	addLogEntry ();
	logResize ();
	scrollToEnd ();
}

//...............................................................................................
function inputKeypress (e) {
	if (e.which == 13) {
		s = JQInput.val ().trim ();

		if (s && ErrorIdx === null) {
			if (Autocomplete.length > 0) {
				s = s + Autocomplete.join ('');
				inputting (s);
			}

			JQInput.val ('');

			updateOverlay ('', null, []);
			inputted (s);

			return false;
		}

	} else if (e.which == 32) {
		if (!JQInput.val ()) {
			return false;
		}
	}

	return true;
}

//...............................................................................................
function inputKeydown (e) {
	if (!GreetingFadedOut) {
		GreetingFadedOut = true;
		$('#Greeting').fadeOut (3000);
	}

	if (e.code == 'Escape') {
		e.preventDefault ();

		if (JQInput.val ()) {
			HistIdx = History.length;
			inputting ('', true);

			return false;
		}

	} else if (e.code == 'Tab') {
		e.preventDefault ();
		$(this).focus ();

		return false;

	} else if (e.code == 'ArrowUp') {
		e.preventDefault ();

		if (HistIdx) {
			inputting (History [-- HistIdx], true);

			return false;
		}

	} else if (e.code == 'ArrowDown') {
		e.preventDefault ();

		if (HistIdx < History.length - 1) {
			inputting (History [++ HistIdx], true);

			return false;

		} else if (HistIdx != History.length) {
			HistIdx = History.length;
			inputting ('', true);

			return false;
		}

	} else if (e.code == 'ArrowRight') {
		if (JQInput.get (0).selectionStart === JQInput.val ().length && Autocomplete.length) {
			let text = JQInput.val ();

			if (Autocomplete [0] === '\\left' || Autocomplete [0] === '\\right') {
				text         = text + Autocomplete.slice (0, 2).join ('');
				Autocomplete = Autocomplete.slice (2);

			} else {
				text         = text + Autocomplete [0];
				Autocomplete = Autocomplete.slice (1);
			}

			JQInput.val (text);
			inputting (text);
			// updateOverlay (text, ErrorIdx, Autocomplete);
		}
	}
}

//...............................................................................................
// function inputFocusout (e) {
// 	if (PreventFocusOut) {
// 		e.preventDefault ();
// 		$(this).focus ();

// 		return false;
// 	}
// }

//...............................................................................................
function keepInputFocus () {
	if (PreventFocusOut) {
		JQInput.focus ();
	}

	setTimeout (keepInputFocus, 50);
}

//...............................................................................................
$(function () {
	window.JQInput = $('#Input');

	let margin       = $('body').css ('margin-top');
	BodyMarginTop    = Number (margin.slice (0, margin.length - 2));
	margin           = $('body').css ('margin-bottom');
	BodyMarginBottom = Number (margin.slice (0, margin.length - 2));

	$('#Clipboard').prop ('readonly', true);
	$('#InputBG') [0].height = $('#InputBG').height ();

	JQInput.keypress (inputKeypress);
	JQInput.keydown (inputKeydown);
	// JQInput.focusout (inputFocusout);
	// JQInput.blur (inputFocusout);

	addLogEntry ();
	logResize ();
	resize ();
	keepInputFocus ();
});


// $('#txtSearch').blur(function (event) {
// 	setTimeout(function () { $("#txtSearch").focus(); }, 20);
// });

// document.getElementById('txtSearch').addEventListener('blur', e => {
//   e.target.focus();
// });

// cursor_test = function (element) {
// 	if (!element.children.length && element.innerText == '∥') {
// 		console.log (element, element.classList);
// 		element.innerText = '|';
// 		element.classList.add ('blinking');
// 	}

// 	for (let e of element.children) {
// 		cursor_test (e);
// 	}
// }

// cursor_test (eLogInput.children [0]);
""",

	'index.html': # index.html

"""<!DOCTYPE html>
<html>
<head>

	<meta http-equiv="Content-Type" content="text/html; charset=utf-8" />
	<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1" />		<meta charset="utf-8">
	<meta http-equiv="X-UA-Compatible" content="IE=edge">
	<link rel="icon" href="https://www.sympy.org/static/SymPy-Favicon.ico">
	<title>SymPad</title>
	<meta name="viewport" content="width=device-width, initial-scale=1">
	<link rel="stylesheet" type="text/css" href="style.css">

	<script type="text/javascript" src="https://code.jquery.com/jquery-3.4.1.js" integrity="sha256-WpOohJOqMqqyKL9FccASB9O0KwACQJpFTUBLTYOVvVU=" crossorigin="anonymous"></script>
	<script type="text/javascript" src="script.js"></script>
	<script type="text/x-mathjax-config">
		MathJax.Hub.Config ({
			messageStyle: "none",
			tex2jax: {inlineMath: [["$","$"], ["\\(","\\)"]]}
		});

		MathJax.Hub.Register.StartupHook ("End", readyMathJax);
	</script>
	<script type="text/javascript" src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.5/latest.js?config=TeX-AMS_CHTML-full"></script>

</head>

<body onresize="resize ()">

	<input id="Clipboard">
	<canvas id="Background"></canvas>
	<div id="Greeting">
		simplify x, expand x, factor x, ? x
		<br><br>
		? x = N (x): numerically evaluate x
		<br><br>
		d/dx = \frac{d}{dx} = $ \frac{d}{dx} $
		<br>
		d^2/dxdy = \frac{\partial}{\partial x\partial y} = $ \frac{\partial}{\partial x\partial y} $
		<br><br>
		^ and ** are both the power operator but they bind differently, ^ follows latex rules and ** follows python rules
		<br><br>
		sin^{-1}(x) = $ \sin^{-1}(x) $: is interpreted as the inverse sin function arcsin,
		same goes for cos, tan, sec, csc, cot, sinh, cosh, tanh, sech, csch and coth

	</div>

	<div id="Log"></div>

	<canvas id="InputBG"></canvas>
	<input id="Input" oninput="inputting (this.value)" autofocus>
	<div id="InputOverlay"><span id="OverlayGood"></span><span id="OverlayError"></span><span id="OverlayAutocomplete"></span></div>

</body>
</html>""",
}
