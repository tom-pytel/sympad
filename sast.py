# Base classes for abstract math syntax tree, tuple based.
#
# (';', (expr1, ...))                                 - semicolon expression separator
# ('=', lhs, rhs)                                     - assignment to Left-Hand-Side of Right-Hand-Side
# ('<>', lhs, (('rel1', expr1), ...))                 - comparisons of type 'rel' relating two or more expressions, potentially x < y < z is x < y and y < z
# ('#', 'num')                                        - real numbers represented as strings to pass on maximum precision to sympy
# ('@', 'var')                                        - variable name, can take forms: 'x', "x'", 'dx', '\partial x', 'something'
# ('.', expr, 'name')                                 - data attribute reference
# ('.', expr, 'name', (a1, a2, ...))                  - method attribute call
# ('"', 'str')                                        - string
# (',', (expr1, expr2, ...))                          - comma expression (tuple)
# ('{', expr)                                         - invisible implicit parentheses for grouping and isolation during parsing
# ('(', expr)                                         - explicit parentheses (not tuple)
# ('[', (expr1, expr2, ...))                          - brackets (list, not index)
# ('|', expr)                                         - absolute value
# ('-', expr)                                         - negative of expression, negative numbers are represented with this at least initially
# ('!', expr)                                         - factorial
# ('+', (expr1, expr2, ...))                          - addition
# ('*', (expr1, expr2, ...)[, {i0, ...}])             - multiplication, with optional set of indices of explicit multiplications (indexes of rhs)
# ('*exp', (expr1, expr2, ...))                       - explicit multiplication, only used during parsing then converted to '*' with indexes of exps
# ('/', numer, denom)                                 - fraction numer(ator) / denom(inator)
# ('^', base, exp)                                    - power base ^ exp(onent)
# ('-log', expr[, base])                              - logarithm of expr in base, natural log if base not present
# ('-sqrt', expr[, n])                                - nth root of expr, square root if n not present
# ('-func', 'name', (a1, a2, ...))                    - sympy or regular Python function call to 'name()', will be called with expressions a1, a2, ...
# ('-lim', expr, var, to[, 'dir'])                    - limit of expr when var approaches to from both directions, otherwise only from specified '+' or '-' dir
# ('-sum', expr, var, from, to)                       - summation of expr over variable var from from to to
# ('-diff', expr, 'd', (('v1', p1), ...))             - differentiation of expr with respect to dv(s), d is 'd' or 'partial', dvs are ('var', power) - power is int
# ('-diffp', expr, count)                             - differentiation with respect to unspecified variable count times
# ('-intg', expr, dv[, from, to])                     - indefinite or definite integral of expr (or 1 if expr is None) with respect to differential dv (('@', 'dx'), ('@', 'dy'), etc ...)
# ('-mat', ((e11, e12, ...), (e21, e22, ...), ...))   - matrix
# ('-piece', ((v1, c1), ..., (vn, True?)))            - piecewise expression: v = AST, c = condition AST, last condition may be True to catch all other cases
# ('-lamb', expr, (v1, v2, ...))                      - lambda expression: v? = 'var'
# ('-idx', expr, (i0, i1, ...))                       - indexing: expr [i0, i1, ...]
# ('-slice', start, stop, step)                       - indexing slice object: obj [start : stop : step], None or False indicates not specified, None for step means no second colon
# ('-set', (expr1, expr2, ...))                       - set
# ('-dict', ((k1, v1), (k2, v2), ...))                - python dict
# ('||', (expr1, expr2, ...))                         - set union
# ('^^', (expr1, expr2, ...))                         - set symmetric difference
# ('&&', (expr1, expr2, ...))                         - set intersection
# ('-or', (expr1, expr2, ...))                        - pythonic or
# ('-and', (expr1, expr2, ...))                       - pythonic and
# ('-not', expr)                                      - pythonic not
# ('-ufunc', 'name', (a1, ...)[, (('kw1', a1), ...)]) - undefined function object with optional keyword arguments, no arguments means 'pure' unapplied undefined function
# ('-subs', expr, ((s1, d1), ...))                    - substitution - replace all s? with d? in expr

from collections import OrderedDict
import re
import types

import sympy as sp

#...............................................................................................
class AST (tuple):
	op      = None

	OPS     = set () # these will be filled in after all classes defined
	CONSTS  = set ()

	_OP2CLS = {}
	_CLS2OP = {}

	_rec_identifier = re.compile (r'^[a-zA-Z]\w*$')

	def __new__ (cls, *args, **kw):
		op       = AST._CLS2OP.get (cls)
		cls_args = tuple (AST (*arg) if arg.__class__ is tuple else arg for arg in args)

		if op:
			args = (op,) + cls_args

		elif args:
			args = cls_args

			try:
				cls2 = AST._OP2CLS.get (args [0])
			except TypeError: # for unhashable types
				cls2 = None

			if cls2:
				cls      = cls2
				cls_args = cls_args [1:]

		if cls is not AST and '__new__' in cls.__dict__:
			self = cls.__new__ (cls, *cls_args)

		else:
			self = tuple.__new__ (cls, args)

			if self.op:
				self._init (*cls_args)

		if kw:
			self.__dict__.update (kw)

		return self

	def __add__ (self, other):
		if not isinstance (other, tuple):
			raise TypeError (f'can only concatenate tuple (not "{type (other).__name__}") to AST')

		return self if not other else AST (*tuple.__add__ (self, other))

	def __getattr__ (self, name): # calculate value for nonexistent self.name by calling self._name () and store
		func                 = getattr (self, f'_{name}') if name [0] != '_' else None
		val                  = func and func ()
		self.__dict__ [name] = val

		return val

	def setkw (self, **kw):
		self.__dict__.update (kw)

		return self # convenience

	def _is_single_unit (self): # is single positive digit, fraction or single non-differential non-subscripted variable?
		if self.op == '/':
			return True
		elif self.op == '#':
			return len (self.num) == 1
		else:
			return self.is_var_single

	def _len (self):
		return len (self)

	@staticmethod
	def tuple2ast (args):
		return args [0] if len (args) == 1 else AST (',', args)

	@staticmethod
	def tuple2argskw (args):
		args, kw = AST.args2kwargs (args)
		args     = args + [AST ('=', ('@', kw), a) for kw, a in kw.items ()]

		return args [0] if len (args) == 1 else AST (',', tuple (args))

	def _no_curlys (self): # remove ALL curlys from entire tree, not just top level
		if self.is_curly:
			return self.curly.no_curlys
		else:
			return AST (*tuple (a.no_curlys if isinstance (a, AST) else a for a in self))#, **self._kw)

	def _flat (self, op = None, seq = None, exp = None): # flatten trees of '+', '*', '||', '^^', '&&', '-or' and '-and' into single ASTs
		def subflat (op, seq, exp):
			if self.is_mul:
				for i in range (self.mul.len):
					if i in self.exp:
						exp.add (len (seq))

					self.mul [i]._flat (self.op, seq, exp)

			else:
				for e in self [1]:
					e._flat (self.op, seq, exp)

		# start here
		if self.op in {'+', '*', '||', '^^', '&&', '-or', '-and'}: # specifically not '<>' because that would be different meaning
			if self.op == op:
				subflat (op, seq, exp)

				return

			seq2, exp2 = [], set ()

			subflat (self.op, seq2, exp2)

			ast = AST (self.op, tuple (seq2), exp2) if self.is_mul else AST (self.op, tuple (seq2))

		else:
			ast = AST (*tuple (a.flat if isinstance (a, AST) else a for a in self))

		if op:
			seq.append (ast)
		else:
			return ast

	def neg (self, stack = False): # stack means stack negatives ('-', ('-', ('#', '-1')))
		if stack:
			if not self.is_num_pos:
				return AST ('-', self)
			else:
				return AST ('#', f'-{self.num}')

		else:
			if self.is_minus:
				return self.minus
			elif not self.is_num:
				return AST ('-', self)
			elif self.num [0] == '-':
				return AST ('#', self.num [1:])
			else:
				return AST ('#', f'-{self.num}')

	def _strip (self, count = None, ops = {'{', '('}, idx = 1, keeptuple = False):
		count = -1 if count is None else count

		while count and self.op in ops and not (keeptuple and self [idx].is_comma):
			self   = self [idx]
			count -= 1

		return self

	_strip_attr     = lambda self, count = None: self._strip (count, {'.'})
	_strip_attrm    = lambda self, count = None: self._strip (count, {'.', '-'})
	_strip_attrdp   = lambda self, count = None: self._strip (count, {'.', '-diffp'})
	_strip_attrpdpi = lambda self, count = None: self._strip (count, {'.', '^', '-diffp', '-idx'})
	_strip_curly    = lambda self, count = None: self._strip (count, {'{'})
	_strip_paren    = lambda self, count = None, keeptuple = False: self._strip (count, ('(',), keeptuple = keeptuple)
	_strip_paren1   = lambda self: self._strip (1, {'('})
	_strip_minus    = lambda self: self._strip (None, {'-'})
	_strip_diffp    = lambda self: self._strip (None, {'-diffp'})
	_strip_fdpi     = lambda self, count = None: self._strip (count, {'!', '-diffp', '-idx'})
	_strip_pow      = lambda self, count = None: self._strip (count, {'^'})
	_strip_afpdpi   = lambda self, count = None: self._strip (count, ('.', '!', '^', '-diffp', '-idx')) # not currently used, possibly used in future in one place

	def _strip_pseudo (self):
		while self.is_func_pseudo:
			self = self.args [0]

		return self

	def _strip_minus_retneg (self):
		neg         = lambda ast: ast
		neg.has_neg = False
		neg.is_neg  = False

		while self.is_minus:
			self         = self.minus
			is_neg       = neg.is_neg
			neg          = lambda ast, neg = neg: neg (ast.neg (stack = True))
			neg.has_neg  = True
			neg.is_neg   = not is_neg

		return self, neg

	def _strip_mmls (self): # mmls = minus, mul, lim, sum
		while self.op in {'-', '*', '-lim', '-sum'}:
			self = self.mul [-1] if self.is_mul else self [1]

		return self

	def _as_identifier (self):
		def _as_identifier (ast, recursed = False):
			if ast.op in {'#', '@', '"'}:
				name = ast [1]
			elif not ast.is_mul:
				return None

			else:
				try:
					name = ''.join (_as_identifier (m, True) for m in ast.mul)
				except TypeError:
					return None

			return name if recursed or AST._rec_identifier.match (name) else None

		return _as_identifier (self)

	def _is_const (self):
		if self.is_num:
			return True
		elif self.is_var:
			return self.is_var_const
		elif self.op in {'{', '(', '-', '!'}:
			return self [1].is_const
		elif self.op in {'+', '*', '*exp'}:
			return all (a.is_const for a in self [1])
		elif self.is_div:
			return self.numer.is_const and self.denom.is_const
		elif self.is_pow:
			return self.base.is_const and self.exp.is_const
		elif self.is_log:
			return self.log.is_const if self.base is None else (self.log.is_const and self.base.is_const)
		elif self.is_sqrt:
			return self.rad.is_const if self.idx is None else (self.rad.is_const and self.idx.is_const)
		elif self.is_func:
			return all (a.is_const for a in self.args)

		return False

	def _tail_mul (self):
		tail = self

		while 1:
			if tail.is_mul:
				tail = tail.mul [-1]
			elif tail.is_pow:
				tail = tail.exp
			elif tail.is_minus:
				tail = tail.minus
			else:
				break

		return tail

	def _has_tail_lambda_solo (self):
		return self.tail_lambda_solo != (None, None)

	def _has_tail_lambda (self):
		return self.tail_lambda != (None, None)

	def _tail_lambda_solo (self):
		return self._tail_lambda (has_var = False)

	def _tail_lambda (self, has_var = None): # look for 'lambda' or 'lambda var' at the tail end of ast (to replace) - for use only during parsing (does not handle mul exp indexes)
		tail, wrap = self, lambda ast: ast

		while 1:
			if tail.is_var:
				if tail.is_var_lambda and has_var is not True:
					return None, wrap

				break

			elif tail.op in {',', '+', '*', '*exp', '||', '^^', '&&', '-or', '-and'}:
				if tail.is_mul and has_var is not False and tail.mul [-1].is_var_nonconst:
					_, wrapl = tail.mul [-2].tail_lambda_solo

					if wrapl:
						if tail.mul.len > 2:
							wrap = lambda ast, tail = tail, wrap = wrap, wrapl = wrapl: wrap (AST ('*', tail.mul [:-2] + (wrapl (ast),)))
						else:
							wrap = lambda ast, wrap = wrap, wrapl = wrapl: wrap (wrapl (ast))

						return tail.mul [-1], wrap

				wrap = lambda ast, tail = tail, wrap = wrap: wrap (AST (tail.op, tail [1] [:-1] + (ast,)))
				tail = tail [1] [-1]

			elif tail.op in {'=', '/', '^'}:
				wrap = lambda ast, tail = tail, wrap = wrap: wrap (AST (tail.op, tail [1], ast))
				tail = tail [2]

			elif tail.op in {'-', '-not'}:
				wrap = lambda ast, tail = tail, wrap = wrap: wrap (AST (tail.op, ast))
				tail = tail [1]

			elif tail.op in {'-lim', '-sum', '-lamb'}:
				wrap = lambda ast, tail = tail, wrap = wrap: wrap (AST (tail.op, ast, *tail [2:]))
				tail = tail [1]

			elif tail.is_diff:
				if (tail.src or not tail.diff.is_var) and not (tail.src and tail.src.is_div and (tail.src.numer.is_mul or tail.src.numer.is_diff_or_part)): # check src from sparser if present
					wrap = lambda ast, tail = tail, wrap = wrap: wrap (AST (tail.op, ast, tail.d, tail.dvs))
					tail = tail.diff

				else:
					break

			elif tail.is_cmp:
				wrap = lambda ast, tail = tail, wrap = wrap: wrap (AST ('<>', tail.lhs, tail.cmp [:-1] + ((tail.cmp [-1] [0], ast),)))
				tail = tail.cmp [-1] [1]

			elif tail.op in {'-sqrt', '-log'}:
				if tail.src: # check src from sparser if present
					wrap = lambda ast, tail = tail, wrap = wrap: wrap (AST (tail.op, ast, *tail [2:]))
					tail = tail.src.mul [1]

				else:
					break

			elif tail.is_func:
				if tail.src and tail.src.mul [0].is_var and tail.src.mul [0].var == tail.func: # check src from sparser if present
					wrap = lambda ast, tail = tail, wrap = wrap: wrap (AST ('-func', tail.func, (ast,)))
					tail = tail.src.mul [1]

				else:
					break

			elif tail.is_piece:
				if tail.piece [-1] [1] is True:
					wrap = lambda ast, tail = tail, wrap = wrap: wrap (AST ('-piece', tail.piece [:-1] + ((ast, True),)))
					tail = tail.piece [-1] [0]
				else:
					wrap = lambda ast, tail = tail, wrap = wrap: wrap (AST ('-piece', tail.piece [:-1] + ((tail.piece [-1] [0], ast),)))
					tail = tail.piece [-1] [1]

			elif tail.is_slice:
				if tail.step:
					wrap = lambda ast, tail = tail, wrap = wrap: wrap (AST ('-slice', tail.start, tail.stop, ast))
					tail = tail.step

				elif tail.step is False:
					break

				elif tail.stop:
					wrap = lambda ast, tail = tail, wrap = wrap: wrap (AST ('-slice', tail.start, ast, None))
					tail = tail.stop

				else:
					break

			else:
				break

		return None, None # var, wrap

	def _as_ufunc_argskw (self):
		args, kw = AST.args2kwargs (self.comma if self.is_comma else (self,) if self.op is not None else self)

		return tuple (args), tuple (sorted (kw.items ()))

	def _free_vars (self): # return set of unique unbound variables found in tree, not reliable especially if used before sxlat due to things like ('-func', 'Derivative', ...), '-subs' is particularly problematic
		def _free_vars (ast, vars):
			if isinstance (ast, AST):
				if ast.is_var:
					if ast.is_var_nonconst and ast.var:
						vars.add (ast)

				elif ast.is_lamb:
					_free_vars (ast.lamb, vars)
					vars.difference_update (('@', v) for v in ast.vars)

				elif ast.is_subs:
					_free_vars (ast.expr, vars)

					for src, dst in ast.subs:
						if not src.is_var_nonconst:
							present = False

						else:
							present = src in vars

							if present:
								vars.remove (src)

						if present:
							_free_vars (dst, vars)

				else:
					try:
						if ast.is_intg:
							_free_vars (ast.intg, vars)

							if ast.is_intg_definite:
								vars.remove (ast.dv.as_var)
							else:
								vars.add (ast.dv.as_var)

						else:
							for e in ast:
								_free_vars (e, vars)

							if ast.is_lim:
								vars.remove (ast.lvar)
							elif ast.is_sum:
								vars.remove (ast.svar)

					except KeyError:
						pass

		vars = set ()

		_free_vars (self, vars)

		return vars

	@staticmethod
	def args2kwargs (args, func = None, ass2cmp = False): # ass2cmp means convert assignment to comparison so it can be represented as Eq() in the py representation of argument list of functions
		func  = (lambda x: x) if func is None else func
		rargs = []
		kw    = []
		itr   = reversed (args)

		for arg in itr:
			if arg.is_ass and not arg.ass_is_not_kw: # ass_is_not_kw comes from sxlat of Eq during testing
				ident = arg.lhs.as_identifier

				if ident is not None:
					kw.append ((ident, func (arg.rhs)))

					continue

				elif ass2cmp: # rewrite assignment = as == for equations passed to functions
					arg = AST ('<>', arg.lhs, (('==', arg.rhs),))

			if ass2cmp:
				rargs = [func (arg)] + [func (AST ('<>', a.lhs, (('==', a.rhs),)) if a.is_ass else a) for a in itr]
			else:
				rargs = [func (arg)] + [func (a) for a in itr]

		return rargs [::-1], OrderedDict (reversed (kw))

	@staticmethod
	def flatcat (op, ast0, ast1): # ,,,/O.o\,,,~~
		if ast0.op == op:
			if ast1.op == op:
				if ast0.is_mul:
					return AST (op, ast0 [1] + ast1 [1], ast0.exp | frozenset (i + ast0.mul.len for i in ast1.exp))
				else:
					return AST (op, ast0 [1] + ast1 [1])

			else: # ast1.op != op:
				if ast0.is_mul:
					return AST (op, ast0 [1] + (ast1,), ast0.exp)
				else:
					return AST (op, ast0 [1] + (ast1,))

		else: # ast0.op != op
			if ast1.op == op:
				if ast1.is_mul:
					return AST (op, (ast0,) + ast1 [1], frozenset (i + 1 for i in ast1.exp))
				else:
					return AST (op, (ast0,) + ast1 [1])

			else:
				return AST (op, (ast0, ast1))

	@staticmethod
	def apply_vars (ast, vars, parent = None, mode = True): # remap vars to assigned expressions and 'execute' funcs which map to lambda vars
		# print ('/n'.join (f'{v} ... {a}' for v, a in vars.items ()) + f'\n{ast}')
		def push (vars, newvars): # create new frame and add new variables, this is really overkill
			frame       = vars.copy ()
			frame ['<'] = vars
			frame ['>'] = newvars

			frame.update (newvars)

			return frame

		def pop (vars, var): # find variable and return frame just below it
			prev = vars.get ('<')

			while prev:
				if var in prev.get ('>', {}):
					return prev

				vars = prev
				prev = vars.get ('<')

			return vars

		def scopeout (vars): # scope out one layer of variables (not frames) and create new frame
			count = vars.get ('#', 1)
			frame = {'<': vars.get ('<', {}), '>': vars.get ('>', vars), '#': count + 1}

			for v in vars:
				if v not in '<>#':
					f = vars

					for _ in range (count):
						while f:
							nvs = f.get ('>', f)
							f   = f.get ('<', {})

							if not f or v in nvs:
								break

					frame [v] = f.get (v)

			return frame

		def index_by_is (seq, obj):
			for i, o in enumerate (seq):
				if o is obj:
					return i

			return None

		# start here
		if not isinstance (ast, AST): # or (ast.is_func and ast.func == AST.Func.NOREMAP): # non-AST, ufunc definition or stop remap
			return ast

		if ast.is_ufunc: # possibly convert non-explicit ufunc to concrete function call if signature matches destination lambda
			if not ((mode is True and not ast.is_ufunc_explicit) or mode == 'lambexec'): # do not map ufuncs to func calls when mapping vars onto themselves, inside lambda definition or is explicit
				return ast

			lamb = vars.get (ast.ufunc)

			if not (lamb and lamb.is_lamb and ast.matches_lamb_sig (lamb)):
				if mode != 'lambexec':
					return ast
				else:
					return AST ('-ufunc', ast.ufunc_full, tuple (AST.apply_vars (a, vars, ast, mode) for a in ast.vars), ast.kw)

			ast = AST ('-func', ast.ufunc, ast.vars)

		if ast.is_num:
			return ast

		elif ast.is_var: # regular var substitution?
			expr = vars.get (ast.var)

			# if not expr:
			# 	if expr is not False and '#' in vars: # if scoped out and var is masked out then replace with dummy
			# 		return AST ('@', f'_{ast.var}')
			# 	else:
			# 		return ast

			if not expr:
				return ast
			elif not expr.is_lamb:
				return AST.apply_vars (expr, pop (vars, ast.var), ast, mode)

			if parent is None:
				parent = AST.Null

			i = index_by_is (parent.mul, ast) if parent.is_mul else None

			if (parent.op in {None, ';', '@', ',', '[', '-func', '-lamb', '-set', '-dict'} or
					(parent.is_piece and any (p [0] is ast for p in parent.piece)) or
					(i is not None and i < (parent.mul.len - 1) and parent.mul [i + 1].is_paren and (i + 1) not in parent.exp)): # if followed by implicit mul paren then is call not multiply
				return expr

			vars = push (vars, {v: False for v in expr.vars})

			return AST.apply_vars (expr.lamb, vars, ast, mode)

		elif ast.is_subs:
			return AST ('-subs', AST.apply_vars (ast.expr, vars, ast, mode), tuple ((src, AST.apply_vars (dst, vars, ast, mode)) for src, dst in ast.subs)) # without mapping src
			# return AST ('-subs', AST.apply_vars (ast.expr, vars, ast, mode), tuple ((AST.apply_vars (src, vars, ast, mode), AST.apply_vars (dst, vars, ast, mode)) for src, dst in ast.subs)) # mapping src

		elif ast.op in {'-lim', '-sum'}:
			vars = push (vars, {ast [2].var: False})

			return AST (ast.op, AST.apply_vars (ast [1], vars, ast, mode), ast [2], *(AST.apply_vars (a, vars, ast, mode) for a in ast [3:]))

		elif ast.is_diff:
			dvs = []

			for v, p in ast.dvs: # remap differentials if possible
				a = vars.get (v)

				if a:
					if a.is_var_nonconst:
						v = a.var

				dvs.append ((v, p))

			return AST ('-diff', AST.apply_vars (ast.diff, vars, ast, mode), ast.d, tuple (dvs))

		elif ast.is_intg:
			dv = ast.dv

			if ast.is_intg_definite: # don't map bound var
				v    = dv.var_name
				vars = push (vars, {dv.var_name: False})

			else: # remap differential if indefinite integral and possible
				a = vars.get (ast.dv.var_name)

				if a:
					if a.is_var_nonconst:
						dv = AST ('@', f'd{a.var}')
					else:
						dv = ast.dv

			return AST ('-intg', AST.apply_vars (ast.intg, vars, ast, mode), dv, *(AST.apply_vars (a, vars, ast, mode) for a in ast [3:]))

		elif ast.is_lamb: # lambda definition
			vars = push (vars, {v: False for v in ast.vars})

			return AST ('-lamb', AST.apply_vars (ast.lamb, vars, ast, mode and 'lambdef'), ast.vars)

		elif ast.is_func: # function, might be user lambda call
			if ast.func == AST.Func.NOREMAP:
				return AST.apply_vars (ast.args [0], scopeout (vars), ast, mode)
				# vars = scopeout (vars)

				# return AST ('-func', ast.func, tuple (AST.apply_vars (a, vars, ast, mode) for a in ast.args))

			else:
				lamb = vars.get (ast.func)

				if lamb and lamb.is_lamb: # 'execute' user lambda
					if ast.args.len == lamb.vars.len:
						vars = push (vars, dict (zip (lamb.vars, ast.args)))

						return AST.apply_vars (lamb.lamb, vars, ast, mode and 'lambexec') # remap lambda vars in body to func args and return body

					elif mode:
						raise TypeError (f"lambda function '{ast.func}' takes {lamb.vars.len} argument(s)")

					return AST ('-func', ast.func,
							tuple (('(', AST.apply_vars (a, vars, ast, mode))
							if (a.is_var and (vars.get (a.var) or AST.VarNull).is_ass)
							else AST.apply_vars (a, vars, ast, mode) for a in ast.args)) # wrap var assignment args in parens to avoid creating kwargs

		return AST (*(AST.apply_vars (a, vars, ast if ast.op else parent, mode) for a in ast))#, **ast._kw)

	@staticmethod
	def register_AST (cls):
		AST._CLS2OP [cls]    = cls.op
		AST._OP2CLS [cls.op] = cls

		AST.OPS.add (cls.op)

		setattr (AST, cls.__name__ [4:], cls)

	@staticmethod
	def EI (state = True):
		AST.CONSTS.difference_update ((AST.E, AST.I))

		AST.E, AST.I = (AST ('@', 'E'), AST ('@', 'I')) if state else (AST ('@', 'e'), AST ('@', 'i'))

		AST.CONSTS.update ((AST.E, AST.I))

#...............................................................................................
class AST_SColon (AST):
	op, is_scolon = ';', True

	def _init (self, scolon):
		self.scolon = scolon

class AST_Ass (AST):
	op, is_ass = '=', True

	def _init (self, lhs, rhs):
		self.lhs, self.rhs = lhs, rhs # should be py form

	@staticmethod
	def ufunc2lamb (ufunc, lamb):
		return AST ('-lamb', lamb, tuple (v.var or 'NONVARIABLE' for v in ufunc.vars))

	def _ass_valid (self):
		def verify (ast, lhs, multi = False):
			for lhs in (lhs if multi else (lhs,)):
				if lhs.is_var_const:
					ast.error = 'The only thing that is constant is change - Heraclitus; Except for constants, they never change - Math...'
				# elif lhs.is_ufunc_explicit:
				# 	ast.error = 'cannot define an undefined function, by definition'
				elif lhs.is_ufunc_impure:
					ast.error = 'cannot assign to a function containing non-variable parameters'
				# elif lhs.is_ufunc_anonymous:
				# 	ast.error = 'cannot assign to an anonymous function'
				else:
					continue

				break

			return ast # convenience

		if self.lhs.is_var:
			return verify (self, self.lhs)

		elif self.lhs.is_comma:
			rhs = self.rhs.strip_paren

			if rhs.op not in {',', '[', '-set'}:
				return verify (self, self.lhs.comma, multi = True)

			else:
				both = min (self.lhs.comma.len, rhs [1].len)
				lrs  = []

				for l, r in zip (self.lhs.comma, rhs [1]):
					if l.is_var:
						lrs.append ((l, r))
					elif l.is_ufunc_implicit:
						lrs.append ((('@', l.ufunc), self.ufunc2lamb (l, r)))
					else:
						return None

				rhs = (rhs.op, tuple (r for _, r in lrs) + rhs [1] [both:])

				return verify (AST ('=', (',', tuple (l for l, _ in lrs) + self.lhs.comma [both:]), ('(', rhs) if self.rhs.is_paren else rhs), self.lhs.comma, multi = True)

		elif self.lhs.is_ufunc_implicit:
			return verify (AST ('=', ('@', self.lhs.ufunc), self.ufunc2lamb (self.lhs, self.rhs)), self.lhs)

		return None

class AST_Cmp (AST):
	op, is_cmp = '<>', True

	TEX2PY = {'\\ne': '!=', '\\le': '<=', '\\ge': '>=', '\\lt': '<', '\\gt': '>', '\\neq': '!=', '\\in': 'in', '\\notin': 'notin'}
	UNI2PY = {'\u2260': '!=', '\u2264': '<=', '\u2265': '>=', '\u2208': 'in', '\u2209': 'notin'}
	ANY2PY = {**UNI2PY, **TEX2PY}
	PY2TEX = {'!=': '\\ne', '<=': '\\le', '>=': '\\ge', 'in': '\\in', 'notin': '\\notin'}
	PYFMT  = {'notin': 'not in'}

	def _init (self, lhs, cmp):
		self.lhs, self.cmp = lhs, cmp # should be py forms (('!=', expr), ('<=', expr), ...)

	_is_cmp_in = lambda self: self.cmp.len == 1 and self.cmp [0] [0] in {'in', 'notin'}

class AST_Num (AST):
	op, is_num = '#', True

	_rec_num   = re.compile (r'^(-?)(\d*[^0.e])?(0*)(?:(\.)(0*)(\d*[^0e])?(0*))?(?:([eE])([+-]?)(\d+))?$') # -101000.000101000e+123 -> (-) (101) (000) (.) (000) (101) (000) (e) (+) (123)

	def _init (self, num):
		self.num = str (num)

	_grp              = lambda self: [g or '' for g in AST_Num._rec_num.match (self.num).groups ()]
	_is_num_pos       = lambda self: not self.grp [0]
	_is_num_neg       = lambda self: bool (self.grp [0])
	_is_num_int       = lambda self: not self.grp [3] and not self.grp [7] # self.num_exp_val >= -len (self.grp [2])
	_is_num_pos_int   = lambda self: self.is_num_int and not self.is_num_neg
	_num_exp          = lambda self: self.grp [8] + self.grp [9]
	_num_mant_and_exp = lambda self: (''.join (self.grp [:7]), self.num_exp)
	_num_exp_val      = lambda self: int (self.num_exp) if self.num_exp else 0
	_as_int           = lambda self: int (self.num)

class AST_Var (AST):
	op, is_var  = '@', True

	GREEK       = ('alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta', 'eta', 'theta', 'iota', 'kappa', 'lambda', 'mu', 'nu', 'xi', 'pi', 'rho', 'sigma',
		'tau', 'upsilon', 'phi', 'chi', 'psi', 'omega', 'Gamma', 'Delta', 'Theta', 'Lambda', 'Xi', 'Pi', 'Sigma', 'Upsilon', 'Phi', 'Psi', 'Omega')
	GREEKUNI    = ('\u03b1', '\u03b2', '\u03b3', '\u03b4', '\u03b5', '\u03b6', '\u03b7', '\u03b8', '\u03b9', '\u03ba', '\u03bb', '\u03bc', '\u03bd', '\u03be', '\u03c0', '\u03c1', '\u03c3',
		'\u03c4', '\u03c5', '\u03c6', '\u03c7', '\u03c8', '\u03c9', '\u0393', '\u0394', '\u0398', '\u039b', '\u039e', '\u03a0', '\u03a3', '\u03a5', '\u03a6', '\u03a8', '\u03a9')

	PY2TEXMULTI = {
		'partial'  : ('\\partial',),
		'oo'       : ('\\infty',),
		'zoo'      : ('\\widetilde\\infty', '\\tilde\\infty', '\\overline\\infty', '\\bar\\infty'),
		'Reals'    : ('\\mathbb{R}',),
		'Complexes': ('\\mathbb{C}',),
		'Naturals' : ('\\mathbb{N}', '\\mathbb{N}^*', '\\mathbb{N}^+', '\\mathbb{N}_1', '\\mathbb{N}_{>0}', '\\mathbb{N}_{\\gt0}', '\\mathbb{Z}^+'),
		'Naturals0': ('\\mathbb{N}_0', '\\mathbb{Z}^{\\ge0}'), # , '\\mathbb{N}^0' - ambiguous
		'Integers' : ('\\mathbb{Z}',),
	}

	GREEK2TEX   = dict ((g, f'\\{g}') for g in GREEK)
	PY2TEX      = {**GREEK2TEX, **dict ((p, ts [0]) for p, ts in PY2TEXMULTI.items ())}
	TEX2PY      = {**dict ((f'\\{g}', g) for g in GREEK), **dict ((t, p) for p, ts in PY2TEXMULTI.items () for t in ts)}
	UNI2PY      = {**dict (zip (GREEKUNI, GREEK)), '\u2202': 'partial', '\u221e': 'oo'}
	ANY2PY      = {**UNI2PY, **TEX2PY}

	_rec_groups = re.compile (r"^(?:(?:(d(?!elta))|(partial))(?!_)(?!['\d]))?((.*)(?<!\d)(\d*))$")

	def _init (self, var):
		self.var = var

	_grp                  = lambda self: [g or '' for g in AST_Var._rec_groups.match (self.var).groups ()]
	_is_var_null          = lambda self: not self.var
	_is_var_long          = lambda self: len (self.var) > 1 and self.var not in AST_Var.PY2TEX
	_is_var_const         = lambda self: self in AST.CONSTS
	_is_var_nonconst      = lambda self: self not in AST.CONSTS
	_is_var_lambda        = lambda self: self.var == 'lambda' and self.text != '\\lambda'
	_is_var_single        = lambda self: len (self.var) == 1 or self.var in AST_Var.PY2TEX # is single atomic variable (non-differential, non-subscripted)?
	_is_differential      = lambda self: self.grp [0] and self.grp [2]
	_is_diff_solo         = lambda self: self.grp [0] and not self.grp [2]
	_is_diff_any          = lambda self: self.grp [0]
	_is_partial           = lambda self: self.grp [1] and self.grp [2]
	_is_part_solo         = lambda self: self.grp [1] and not self.grp [2]
	_is_part_any          = lambda self: self.grp [1]
	_is_diff_or_part      = lambda self: (self.grp [0] or self.grp [1]) and self.grp [2]
	_is_diff_or_part_solo = lambda self: (self.grp [0] or self.grp [1]) and not self.grp [2]
	_is_diff_or_part_any  = lambda self: self.grp [0] or self.grp [1]
	_diff_or_part_type    = lambda self: self.grp [0] or self.grp [1] or '' # 'dx' -> 'd', 'partialx' -> 'partial', else ''
	_var_name             = lambda self: self.grp [2]
	_as_var               = lambda self: AST ('@', self.grp [2]) if self.var else self # 'x', dx', 'partialx' -> 'x'
	_as_differential      = lambda self: AST ('@', f'd{self.grp [2]}') if self.var else self # 'x', 'dx', 'partialx' -> 'dx'
	_as_partial           = lambda self: AST ('@', f'partial{self.grp [2]}') if self.var else self # 'x', 'dx', 'partialx' -> 'partialx'
	_text_and_tail_num    = lambda self: (self.grp [3], self.grp [4]) if self.grp [3] and self.grp [3] [-1] != '_' else (self.grp [2], '')

class AST_Attr (AST):
	op, is_attr = '.', True

	def __new__ (cls, obj, attr, args = None):
		self                           = tuple.__new__ (cls, ('.', obj, attr) if args is None else ('.', obj, attr, args))
		self.obj, self.attr, self.args = obj, attr, args

		return self

	_is_attr_var  = lambda self: self.args is None
	_is_attr_func = lambda self: self.args is not None

class AST_Str (AST):
	op, is_str = '"', True

	def _init (self, str_):
		self.str_ = str_

class AST_Comma (AST):
	op, is_comma = ',', True

	def _init (self, comma):
		self.comma = comma

	_is_comma_empty = lambda self: not (self.comma.len)

class AST_Curly (AST):
	op, is_curly = '{', True

	def _init (self, curly):
		self.curly = curly

class AST_Paren (AST):
	op, is_paren = '(', True

	def _init (self, paren):
		self.paren = paren

	def _as_pvarlist (self):
		vars = self.paren.comma if self.paren.is_comma else (self.paren,)

		if all (v.is_var_nonconst for v in vars):
			return vars

		return None

class AST_Brack (AST):
	op, is_brack = '[', True

	def _init (self, brack):
		self.brack = brack

class AST_Abs (AST):
	op, is_abs = '|', True

	def _init (self, abs):
		self.abs = abs

class AST_Minus (AST):
	op, is_minus = '-', True

	def _init (self, minus):
		self.minus = minus

class AST_Fact (AST):
	op, is_fact = '!', True

	def _init (self, fact):
		self.fact = fact

class AST_Add (AST):
	op, is_add = '+', True

	def _init (self, add):
		self.add = add

class AST_Mul (AST):
	op, is_mul = '*', True

	def __new__ (cls, mul, exp = frozenset ()):
		exp                = frozenset (exp)
		self               = tuple.__new__ (cls, ('*', mul, exp) if exp else ('*', mul))
		self.mul, self.exp = mul, exp # exp is optional set of indices of rhses of explicitly specified multiplications

		return self

	def __repr__ (self):
		if not self.exp:
			return tuple.__repr__ (self)

		return tuple.__repr__ (('*', self.mul, set (self.exp)))

	def _is_mul_has_abs (self):
		for m in self.mul:
			if m.is_abs:
				return True

class AST_MulExp (AST): # temporary for isolating explicit multiplications from implicit mul grammar rewriting rules, used only during parsing
	op, is_mulexp = '*exp', True

	def _init (self, mul):
		self.mul = mul

class AST_Div (AST):
	op, is_div = '/', True

	def _init (self, numer, denom):
		self.numer, self.denom = numer, denom

class AST_Pow (AST):
	op, is_pow = '^', True

	def _init (self, base, exp):
		self.base, self.exp = base, exp

class AST_Log (AST):
	op, is_log = '-log', True

	def __new__ (cls, log, base = None):
		self               = tuple.__new__ (cls, ('-log', log) if base is None or base == AST.E else ('-log', log, base))
		self.log, self.base = log, base

		return self

	_is_log_with_base = lambda self: self.base is not None

class AST_Sqrt (AST):
	op, is_sqrt = '-sqrt', True

	def __new__ (cls, rad, idx = None):
		self               = tuple.__new__ (cls, ('-sqrt', rad) if idx is None or idx == AST.Two else ('-sqrt', rad, idx))
		self.rad, self.idx = rad, idx

		return self

	_is_sqrt_with_idx = lambda self: self.idx is not None

class AST_Func (AST):
	op, is_func = '-func', True

	_SYMPY_OBJECTS    = dict ((name, obj) for name, obj in filter (lambda no: no [0] [0] != '_', sp.__dict__.items ()))
	_SYMPY_FUNCS      = set (no [0] for no in filter (lambda no: len (no [0]) > 1 and callable (no [1]), _SYMPY_OBJECTS.items ()))

	NOREMAP           = '@'
	NOEVAL            = '%'

	ADMIN             = {'vars', 'del', 'delall', 'env', 'envreset'}
	PLOT              = {'plotf', 'plotv', 'plotw'}
	PSEUDO            = {NOREMAP, NOEVAL}
	TEXNATIVE         = {'max', 'min', 'arg', 'deg', 'exp', 'gcd', 'Re', 'Im'}
	TRIGH             = {'sin', 'cos', 'tan', 'cot', 'sec', 'csc', 'sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch'}
	BUILTINS          = {'abs', 'all', 'any', 'ascii', 'bin', 'callable', 'chr', 'dir', 'divmod', 'format', 'getattr', 'hasattr', 'hash', 'hex', 'id',
                       'isinstance', 'issubclass', 'iter', 'len', 'max', 'min', 'next', 'oct', 'pow', 'print', 'repr', 'round', 'sorted', 'sum', 'bool',
                       'bytearray', 'bytes', 'complex', 'dict', 'enumerate', 'filter', 'float', 'frozenset', 'property', 'int', 'list', 'map', 'range',
                       'reversed', 'set', 'slice', 'str', 'tuple', 'type', 'zip'}

	PY_TRIGH_INV      = {f'a{f}' for f in TRIGH}
	TEX_TRIGH_INV     = {f'arc{f}' for f in TRIGH}
	TEX2PY_TRIGH_INV  = {f'arc{f}': f'a{f}' for f in TRIGH}

	PY_TRIGH_ALL      = TRIGH | PY_TRIGH_INV
	PYALL             = ADMIN | PLOT | BUILTINS | PY_TRIGH_ALL | _SYMPY_FUNCS
	PY                = PYALL - {'sqrt', 'log', 'ln', 'beta', 'gamma', 'zeta', 'Lambda', 'Function', 'Symbol'} - {'init_printing', 'init_session', 'interactive_traversal'}
	TEX               = TEXNATIVE | TEX_TRIGH_INV | (TRIGH - {'sech', 'csch'})

	def _init (self, func, args):
		self.func, self.args = func, args

	_is_func_pseudo       = lambda self: self.func in {AST_Func.NOREMAP, AST_Func.NOEVAL}
	_is_func_trigh        = lambda self: self.func in AST_Func.PY_TRIGH_ALL
	_is_func_trigh_inv    = lambda self: self.func in AST_Func.PY_TRIGH_INV
	_is_func_trigh_noninv = lambda self: self.func in AST_Func.TRIGH

class AST_Lim (AST):
	op, is_lim = '-lim', True

	def __new__ (cls, lim, lvar, to, dir = None):
		self                                   = tuple.__new__ (cls, ('-lim', lim, lvar, to) if dir is None else ('-lim', lim, lvar, to, dir))
		self.lim, self.lvar, self.to, self.dir = lim, lvar, to, dir

		return self

class AST_Sum (AST):
	op, is_sum = '-sum', True

	def _init (self, sum, svar, from_, to):
		self.sum, self.svar, self.from_, self.to = sum, svar, from_, to

class AST_Diff (AST):
	op, is_diff = '-diff', True

	def _init (self, diff, d, dvs):
		self.diff, self.d, self.dvs = diff, d, dvs

	_is_diff_d         = lambda self: self.d == 'd'
	_is_diff_partial   = lambda self: self.d == 'partial'
	_is_diff_dvdv      = lambda self: self.d == 'd' and self.dvs.len == 1 # and self.diff.is_var and self.dvs [0] [1] == 1
	_is_diff_any_ufunc = lambda self: self.diff.strip_paren1.is_ufunc
	_diff_any          = lambda self: self.diff.strip_paren1

class AST_DiffP (AST):
	op, is_diffp = '-diffp', True

	def _init (self, diffp, count):
		self.diffp, self.count = diffp, count

	_is_diff_any_ufunc = lambda self: self.diffp.is_ufunc
	_diff_any          = lambda self: self.diffp

class AST_Intg (AST):
	op, is_intg = '-intg', True

	def __new__ (cls, intg, dv, from_ = None, to = None):
		self                                    = tuple.__new__ (cls, ('-intg', intg, dv) if from_ is None else ('-intg', intg, dv, from_, to))
		self.intg, self.dv, self.from_, self.to = intg, dv, from_, to

		return self

	_is_intg_definite = lambda self: self.from_ is not None

class AST_Mat (AST):
	op, is_mat = '-mat', True

	def _init (self, mat):
		self.mat = mat

	_rows          = lambda self: self.mat.len
	_cols          = lambda self: self.mat [0].len if self.mat else 0
	_is_mat_column = lambda self: self.rows and self.cols == 1

class AST_Piece (AST):
	op, is_piece = '-piece', True

	def _init (self, piece):
		self.piece = piece

class AST_Lamb (AST):
	op, is_lamb = '-lamb', True

	def _init (self, lamb, vars):
		self.lamb, self.vars = lamb, vars

class AST_Idx (AST):
	op, is_idx = '-idx', True

	def _init (self, obj, idx):
		self.obj, self.idx = obj, idx

class AST_Slice (AST):
	op, is_slice = '-slice', True

	def _init (self, start, stop, step):
		self.start, self.stop, self.step = start, stop, step

class AST_Set (AST):
	op, is_set = '-set', True

	def _init (self, set):
		self.set = set

class AST_Dict (AST):
	op, is_dict = '-dict', True

	def _init (self, dict):
		self.dict = dict

class AST_Union (AST):
	op, is_union = '||', True

	def _init (self, union):
		self.union = union

class AST_SDiff (AST): # symmetric difference
	op, is_sdiff = '^^', True

	def _init (self, sdiff):
		self.sdiff = sdiff

class AST_XSect (AST): # intersection
	op, is_xsect = '&&', True

	def _init (self, xsect):
		self.xsect = xsect

class AST_Or (AST):
	op, is_or = '-or', True

	def _init (self, or_):
		self.or_ = or_

class AST_And (AST):
	op, is_and = '-and', True

	def _init (self, and_):
		self.and_ = and_

class AST_Not (AST):
	op, is_not = '-not', True

	def _init (self, not_):
		self.not_ = not_

class AST_UFunc (AST):
	op, is_ufunc = '-ufunc', True

	def __new__ (cls, ufunc, vars, kw = ()):
		self                           = tuple.__new__ (cls, ('-ufunc', ufunc, vars, kw) if kw else ('-ufunc', ufunc, vars))
		self.ufunc, self.vars, self.kw = ufunc.lstrip ('?'), vars, kw
		self.ufunc_full                = ufunc

		return self

	_is_ufunc_explicit  = lambda self: self.ufunc_full.startswith ('?')
	_is_ufunc_implicit  = lambda self: not self.ufunc_full.startswith ('?')
	_is_ufunc_named     = lambda self: self.ufunc
	_is_ufunc_anonymous = lambda self: not self.ufunc
	_is_ufunc_applied   = lambda self: self.vars
	_is_ufunc_unapplied = lambda self: not self.vars
	_is_ufunc_pure      = lambda self: self.vars and all (v.is_var_nonconst for v in self.vars)
	_is_ufunc_impure    = lambda self: self.vars and any (not v.is_var_nonconst for v in self.vars)

	matches_lamb_sig    = lambda self, lamb: self.vars and self.vars.len == lamb.vars.len

	@staticmethod
	def valid_implicit_args (args):
		return not any (not a.is_var and not a.is_const for a in args)

	def apply_argskw (self, argskw):
		if not argskw or argskw [1]:
			return None

		args = argskw [0]
		subs = []

		if self.vars:
			if len (args) != self.vars.len:
				return None

			for v, a in zip (self.vars, args):
				if not v.is_var_nonconst: # or (a.is_var_nonconst and a.var != v.var):
					return None

				if a != v:
					subs.append ((v, a))

		return AST ('-ufunc', self.ufunc_full, args, self.kw, ufunc_subs = tuple (subs))

class AST_Subs (AST):
	op, is_subs = '-subs', True

	def _init (self, expr, subs):
		self.expr, self.subs = expr, subs

	_is_subs_diff_ufunc     = lambda self: self.expr.is_diff and self.expr.diff.strip_paren1.is_ufunc
	_is_subs_diffp_ufunc    = lambda self: self.expr.is_diffp and self.expr.diffp.is_ufunc
	_is_subs_diff_d_ufunc   = lambda self: self.expr.is_diff_d and self.expr.diff.strip_paren1.is_ufunc
	_is_subs_diff_any_ufunc = lambda self: (self.expr.is_diff and self.expr.diff.strip_paren1.is_ufunc) or (self.expr.is_diffp and self.expr.diffp.is_ufunc)

class AST_Sym (AST):
	op, is_sym = '-sym', True

	def __new__ (cls, sym, kw = ()):
		self              = tuple.__new__ (cls, ('-sym', sym, kw) if kw else ('-sym', sym))
		self.sym, self.kw = sym, kw

		return self

	_is_sym_anonymous   = lambda self: not self.sym
	_is_sym_unqualified = lambda self: not self.kw

#...............................................................................................
_AST_CLASSES = [AST_SColon, AST_Ass, AST_Cmp, AST_Num, AST_Var, AST_Attr, AST_Str, AST_Comma, AST_Curly, AST_Paren,
	AST_Brack, AST_Abs, AST_Minus, AST_Fact, AST_Add, AST_Mul, AST_MulExp, AST_Div, AST_Pow, AST_Log, AST_Sqrt, AST_Func,
	AST_Lim, AST_Sum, AST_Diff, AST_DiffP, AST_Intg, AST_Mat, AST_Piece, AST_Lamb, AST_Idx, AST_Slice, AST_Set, AST_Dict,
	AST_Union, AST_SDiff, AST_XSect, AST_Or, AST_And, AST_Not, AST_UFunc, AST_Subs, AST_Sym]

for _cls in _AST_CLASSES:
	AST.register_AST (_cls)

_AST_CONSTS = (('E', 'e'), ('I', 'i'), ('Pi', 'pi'), ('Infty', 'oo'), ('CInfty', 'zoo'), ('None_', 'None'), ('True_', 'True'), ('False_', 'False'), ('NaN', 'nan'),
	('Naturals', 'Naturals'), ('Naturals0', 'Naturals0'), ('Integers', 'Integers'), ('Reals', 'Reals'), ('Complexes', 'Complexes'))

for _vp, _vv in _AST_CONSTS:
	ast = AST ('@', _vv)

	AST.CONSTS.add (ast)
	setattr (AST, _vp, ast)

AST.Null       = AST ()
AST.Zero       = AST ('#', '0')
AST.One        = AST ('#', '1')
AST.Two        = AST ('#', '2')
AST.NegOne     = AST ('#', '-1')
AST.VarNull    = AST ('@', '')
AST.CommaEmpty = AST (',', ())
AST.MatEmpty   = AST ('-mat', ())
AST.SetEmpty   = AST ('-set', ())
AST.DictEmpty  = AST ('-dict', ())

# AUTO_REMOVE_IN_SINGLE_SCRIPT_BLOCK_START
if __name__ == '__main__': # DEBUG!
	vars = {'x': AST.Zero}
	expr = AST ('*', (('-lamb', ('*', (('-lamb', ('+', (('-func', '@', (('@', 'x'),)), ('#', '1'))), ('x',)), ('(', ('+', (('@', 'x'), ('#', '1')))))), ('x',)), ('(', ('#', '0'))))

	res  = AST.apply_vars (expr, vars)
	print (res)
