# Parser for PLY generated LALR1 grammar.

import re
import types

#...............................................................................................
class Token (str):
	__slots__ = ['text', 'pos', 'grp']

	def __new__ (cls, str_, text = None, pos = None, grps = None):
		self      = str.__new__ (cls, str_)
		self.text = text or ''
		self.pos  = pos
		self.grp  = () if not grps else grps

		return self

class State:
	__slots__ = ['idx', 'sym', 'pos', 'red']

	def __init__ (self, idx, sym, pos = None, red = None): # idx = state index, sym = symbol (TOKEN or 'expression')[, pos = position in text, red = reduction]
		self.idx  = idx
		self.sym  = sym
		self.pos  = sym.pos if pos is None else pos
		self.red  = red

	def __repr__ (self):
		return f'({self.idx}, {self.sym}, {self.pos}{"" if self.red is None else f", {self.red}"})'

class Conflict (tuple):
	def __new__ (cls, conf, pos, tokidx, stidx, tokens, stack, estate):#, keep = False):
		self      = tuple.__new__ (cls, (conf, pos, tokidx, stidx, tokens, stack, estate))
		self.conf = conf
		self.pos  = pos
		# self.keep = keep # do not remove when popping conflicts

		return self

	# def __repr__ (self):
	# 	r = tuple.__repr__ (self)

	# 	return f'{r [:-1]}, keep)' if self.keep else r

class Incomplete (Exception): # parse is head of good statement but incomplete
	__slots__ = ['red']

	def __init__ (self, red):
		self.red = red

# class KeepConf:
# 	__slots__ = ['red']

# 	def __init__ (self, red):
# 		self.red = red

class PopConfs:
	__slots__ = ['red']

	def __init__ (self, red):
		self.red = red

class Reduce: # returned instantiated will try conflicted reduction before rule, returned as uninstantiated class will discard results of rule and just continue with last conflict
	__slots__ = ['then', 'keep']

	def __init__ (self, then):#, keep = False):
		self.then = then
		# self.keep = keep

Reduce.red = Reduce

class LALR1:
	_rec_SYMBOL_NUMTAIL     = re.compile (r'(.*[^_\d])_?(\d+)?') # symbol names in code have extra digits at end for uniqueness which are discarded

	_PARSER_CONFLICT_REDUCE = {} # set of tokens for which a reduction will always be tried before a shift

	def set_tokens (self, tokens):
		self.tokgrps = {} # {'token': (groups pos start, groups pos end), ...}
		tokpats      = list (tokens.items ())
		pos          = 0

		for tok, pat in tokpats:
			l                   = re.compile (pat).groups + 1
			self.tokgrps [tok]  = (pos, pos + l)
			pos                += l

		self.tokre   = '|'.join (f'(?P<{tok}>{pat})' for tok, pat in tokpats)
		self.tokrec  = re.compile (self.tokre)

	def __init__ (self):
		if isinstance (self._PARSER_TABLES, bytes):
			import ast, base64, zlib
			symbols, rules, strules, terms, nterms = ast.literal_eval (zlib.decompress (base64.b64decode (self._PARSER_TABLES)).decode ('utf8'))
		else:
			symbols, rules, strules, terms, nterms = self._PARSER_TABLES

		self.set_tokens (self.TOKENS)

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

			if name [0] != '_' and type (obj) is types.MethodType and obj.__code__.co_argcount >= 1: # 2: allow empty productions
				m = LALR1._rec_SYMBOL_NUMTAIL.match (name)

				if m:
					parms = tuple (p if p in self.TOKENS else LALR1._rec_SYMBOL_NUMTAIL.match (p).group (1) \
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

	def parse_success (self, red):
		'NO PARSE_SUCCESS'
		return None # True to contunue checking conflict backtracks, False to stop and return

	def parse (self, src):
		has_parse_success = (self.parse_success.__doc__ != 'NO PARSE_SUCCESS')

		rules, terms, nterms, rfuncs = self.rules, self.terms, self.nterms, self.rfuncs

		tokens = self.tokenize (src)
		tokidx = 0
		confs  = [] # [(action, tokidx, stack, stidx, extra state), ...] # conflict backtrack stack
		stack  = self.stack = [State (0, None, 0, None)] # [(stidx, symbol, pos, reduction) or (stidx, token), ...]
		stidx  = 0
		rederr = None # reduction function raised exception (SyntaxError or Incomplete usually)
		act    = True
		pos    = 0

		if not hasattr (self, 'reds'): # DEBUG
			self.reds = {} # DEBUG

		while 1:
			if not rederr and act is not None:
				tok       = tokens [tokidx]
				act, conf = terms [stidx].get (tok, (None, None))

			if rederr or act is None:
				if rederr is Reduce:
					rederr = None

				else:
					self.tokens, self.tokidx, self.confs, self.stidx, self.tok, self.rederr, self.pos = \
							tokens, tokidx, confs, stidx, tok, rederr, pos

					rederr = None

					if tok == '$end' and stidx == 1 and len (stack) == 2 and stack [1].sym == rules [0] [1]:
						if not has_parse_success:
							return stack [1].red

						if not self.parse_success (stack [1].red) or not confs:
							return None

					elif self.parse_error ():
						tokidx, stidx = self.tokidx, self.stidx
						act           = True

						continue

				if not confs:
					if has_parse_success: # do not raise SyntaxError if parser relies on parse_success
						return None

					# if self.rederr is not None: # THIS IS COMMENTED OUT BECAUSE IS NOT USED HERE AND PYLINT DOESN'T LIKE IT!
					# 	raise self.rederr # re-raise exception from last reduction function if present

					raise SyntaxError ( \
						'unexpected end of input' if tok == '$end' else \
						f'invalid token {tok.text!r}' if tok == '$err' else \
						f'invalid syntax {src [tok.pos : tok.pos + 16]!r}')

				act, _, tokidx, stidx, tokens, stack, estate = confs.pop ()
				self.stack                                   = stack
				tok                                          = tokens [tokidx]
				conf                                         = None

				self.parse_setextrastate (estate)

				if act is None:
					continue

			if conf is not None:
				confs.append (Conflict (conf, tok.pos, tokidx, stidx, tokens [:], stack [:], self.parse_getextrastate ()))#, keep = act < 0 and tok in self._PARSER_CONFLICT_REDUCE))

				if conf < 0: # DEBUG
					k             = (act, rules [-conf])
					self.reds [k] = self.reds.get (k, 0) + 1

			if act > 0:
				tokidx += 1
				stidx   = act

				stack.append (State (stidx, tok))

			else:
				rule  = rules [-act]
				rnlen = -len (rule [1])
				prod  = rule [0]
				pos   = stack [rnlen].pos

				try:
					red = rfuncs [-act] (*((t.sym if t.red is None else t.red for t in stack [rnlen:]) if rnlen else ()))

					# if isinstance (red, KeepConf): # mark this conflict to not be removed by PopConf
					# 	red             = red.red
					# 	confs [-1].keep = True

					if isinstance (red, Reduce): # successful rule but request to follow conflicted reduction first putting results of rule on conf stack to be picked up later
						stidx     = nterms [stack [rnlen - 1].idx] [prod]
						stack     = stack [:rnlen] + [State (stidx, prod, pos, red.then)]
						tok       = tokens [tokidx]
						act, conf = terms [stidx].get (tok, (None, None))
						estate    = self.parse_getextrastate ()
						rederr    = Reduce

						if conf is not None:
							confs.insert (-1, Conflict (conf, tok.pos, tokidx, stidx, tokens [:], stack [:], estate))#, keep = red.keep))

						confs.insert (-1, Conflict (act, tok.pos, tokidx, stidx, tokens [:], stack [:], estate))#, keep = red.keep))

						continue

					if red is Reduce or isinstance (red, PopConfs): # pop all conflicts generated from parsing this rule because parse is guaranteed good
						red   = red.red
						start = stack [-1].pos if red is Reduce else pos
						i     = 0

						for i in range (len (confs) - 1, -1, -1):
							if confs [i].pos <= start:
								break

							# if not confs [i].keep: # dont remove conflicts which are marked for keeping
							# 	del confs [i]
							del confs [i]

						if red is Reduce: # if reduction only requested then don't store rule result and fall back to previous conflicted reduction
							rederr = red

							continue

				except SyntaxError as e:
					rederr = e # or True

					continue

				except Incomplete as e:
					rederr = e
					red    = e.red

				if rnlen:
					del stack [rnlen:]

				stidx = nterms [stack [-1].idx] [prod]

				stack.append (State (stidx, prod, pos, red))

class lalr1: # for single script
	Token      = Token
	State      = State
	Incomplete = Incomplete
	PopConfs   = PopConfs
	Reduce     = Reduce
	LALR1      = LALR1

# print ('\n'.join (str (s) for s in confs + stack + [rule, pos]))