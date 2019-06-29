# TODO: Fix variable naming for subscripted stuff and stuff with primes.
# TODO: 1+1j complex number parsing?
# TODO: Redo _expr_diff d or \partial handling???

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
#
# ) Future: vectors and matrices, assumptions, stateful variables, piecewise expressions

from collections import OrderedDict
import os
import re

import lalr1         # AUTO_REMOVE_IN_SINGLE_SCRIPT
from sast import AST # AUTO_REMOVE_IN_SINGLE_SCRIPT

def _ast_from_tok_digit_or_var (tok, i = 0):
	return AST ('#', tok.grp [i]) if tok.grp [i] else AST ('@', AST.Var.SHORT2LONG.get (tok.grp [i + 1] or tok.grp [i + 3], tok.grp [i + 2]))

def _expr_int (ast, from_to = ()): # find differential for integration if present in ast and return integral ast
	if ast.is_differential or ast.is_null_var: # null_var is for autocomplete
		return AST ('intg', None, ast, *from_to)

	elif ast.is_div:
		if ast.denom.is_mul and ast.denom.muls [-1].is_differential:
			return AST ('intg', ('/', ast.numer, ast.denom.muls [0] if len (ast.denom.muls) == 2 else \
					AST ('*', ast.denom.muls [:-1])), ast.denom.muls [-1], *from_to)

		if ast.numer.is_differential:
			return AST ('intg', ('/', ast.One, ast.denom), ast.numer, *from_to)

	elif ast.is_mul and (ast.muls [-1].is_differential or ast.muls [-1].is_null_var): # null_var is for autocomplete
		return AST ('intg', ast.muls [0] if len (ast.muls) == 2 else AST ('*', ast.muls [:-1]), ast.muls [-1], *from_to)

	elif ast.is_add:
		if ast.adds [-1].is_differential:
			return AST ('intg', \
					AST ('+', ast.adds [:-1])
					if len (ast.adds) > 2 else \
					ast.adds [0] \
					, ast.adds [-1], *from_to)

		if ast.adds [-1].is_mul and ast.adds [-1].muls [-1].is_differential:
			return AST ('intg', \
					AST ('+', ast.adds [:-1] + (AST ('*', ast.adds [-1].muls [:-1]),))
					if len (ast.adds [-1].muls) > 2 else \
					AST ('+', ast.adds [:-1] + (ast.adds [-1].muls [0],)) \
					, ast.adds [-1].muls [-1], *from_to)

	elif ast.is_intg and ast.intg is not None:
		return AST ('intg', _expr_int (ast.intg, () if ast.from_ is None else (ast.from_, ast.to)), ast.var, *from_to)

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

		ast_dv_check = (lambda n: n.is_differential) if v [0] == 'd' else (lambda n: n.is_partial)

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



# 	vars  = set ()
# 	stack = [ast]

# 	while stack:
# 		ast = stack.pop ()

# 		if ast.is_var:
# 			(diffs if ast.is_differential else vars).add (ast.var)
# 		else:
# 			stack.extend (filter (lambda a: isinstance (a, tuple), ast))

# 	vars  = vars - {'_', 'e', 'i'} - set (AST.Var.LONG2SHORT)
# 	vars -= set (var [1:] for var in diffs)

# 	return vars


def _expr_func_intg_remap (ast): # remap function 'Integral' to internal representation for rendering as pretty integral
	expr = _expr_func (1, '(', ast.strip_paren ())
	ast  = expr.paren if expr.is_paren else expr [1].paren

	if ast.is_comma:
		ast2 = ast.commas [1].strip_paren (1)

		if not ast2.is_comma:
			ast = AST ('intg', ast.commas [0], ('@', f'd{ast.commas [1].var}'))
		else:
			print ('ast2:', ast)
			ast  = AST ('intg', ast.commas [0], ('@', f'd{ast2.commas [0].var}'), ast2.commas [1], ast2.commas [2])


	if not expr.is_paren:
		ast = AST (expr.op, ast, *expr [2:])


	return ast



	print ()
	print ('expr:', expr)

	return expr



#...............................................................................................
class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJztXfuP2zYS/mcO6BqgAfEt9bc0TXvB5dFukgIHowjSJD0UaNJe2twdUPR/v5n5KJGUZVve2l67XZirB0VyhsNv+BiOtFerTx4/fPLi2Sfqk4dPntPx0cPHdHz2Qo5fX0vU0y/p+Pz64Zd/p/MXL57c58gHX/Czz+5d0/Gre9cPnjziMr588vT6wcv7L64f' \
			b'/ZPTXt+7n046nQ2d5TEnf/accz8RYt9ISX97+/5Nn2IomS/uP338+B4TpDL+8UDyMUPMw+dPX3z26MGz51LAfcrAkQ++lirJ6atHUsHPH37z8PMHnObzp8+FuuR49uIzHHWfXXi9d//50+uH9x5lmnz51fXDxw+4sOdP6fD61Ye3v7786cPLNz99/O7Ht7/8' \
			b'+uoDxf7y8bv/yMXb//384eXrn969e9Xf/PLx57fDk+8/vn/98v3bf+WH39FlkfX9x3f95a9vPwzX33949bq//pk4eN/fvPrulyH+p/8OyV+9/rUkmckNJRY0f/xhiP3h/ZDv3ccfX/7w7uf+9s0P/8mX338/8JvrwhnoYuDszZtc6tt/99fD1SffqtXV0rTK' \
			b'+IXCReALrZZGzlFdtapTFGGc6hZ9nMQMt0vd8pWTP0PP/CLfN/l2CSIBB2Mo4yLF0BVdUFFSUit/lrKCxnBfxNAFZ6U/qwxltCiKL5grj4MNi3S71KhZp640pTIN/y2GKFveapcuOI6vqCrEvnGLfGejSMVW0X7trn4e1u7qHLG8I66lSnzl0tVVIzcLqbaI' \
			b'myTR3y/BdkPVSZR9/zBFDjdLLQLXWl0ZZa0SAdEVmpqeJ7lNPhecdLOSNXWqpZbW8fJndf8k3Zt8v5TG6uSP+F0shiu6CCKGuMA1XbBstNJyoQksXEFGGODFMa3q41wZTSwJy6pve5KmFmDpgAPJcJHulyBAgr2iqnK6dGshd44vhGBiL0vjBxHYoS2pzhyf' \
			b'GjPdNnVEyFRIPEADN2TJMkUA2UxJm/7KoH1ZP0jRLNXLQGB9FN1T9KJONU7R39OtFByl6n0FEwNDJHUFU3F8l+MhLCqeOg3qfVaNonSB01lSKq+i4g7HWeWccl65VjlSSEpOyRyX6IJylDiwBlK9CGuuUU4rZ5TvVGikib3ito4KSKWeg8BGjUsq7b3yVILy' \
			b'KiivladcVnnHDUUYIr6oQQM9DCpEFVoVOhUbFbWKRkVKSdfttwxAFrDl4+qK+ac7qoPmOl1RTeSpl1OUY5uedXLnLE4uxTp+fIbVdKiC61JFDSoK7nXPvU6pRAy3znIErxaNYuXWR+XbS8GWbVMNElaANWID0g4i7YvUmgBdcICRR/1Cg+oaaI1B9WQ8OQVT' \
			b'K+5nhXDMhIGXE5FvQb7L5INWwahAF+5ETNjm1FLnArkT6TtGDTR4af5CAAQbH4AQAMSblOOC9QD18SICmpnQPOQi6+ExEHiXNFhANCOfSQOn0XMzoMcI0NSQOsgAyER0kBGAikgahUR0KpI0g4qR2U0J22HYpmnNJQlcphbE86VwG5nZ82ezvQw2iUPm82zZ' \
			b'c2fMHs+wjSi9CJHnrszsebAWwJqVczX0rXj+atYWEV5u9+2s87TSYFppMK00Cx6SvNx6PDQOLBmJvcixyZpUXRkITkLSpIY00manm0zxFBKEu9MSpiEYg24wpxIykbQ3AH9IS3KAXrcAu4fY3KWCfMWTYXPZU0g0gddomEZ6ODHMSbS93KYxgrU52qshg4C+' \
			b'N8ptNXNd8RzXYHJrZASIwHNMJqYAsUUMEyQtu8Bk0a6NHVHixgaodiKWby1ubRo67bmYeVY8gtszGcFl6LaXMi3n2YNJEwGLiYDFRIBOoyzoOz3a33ebUhhJwUOtgSHFwqDBp9CjW3qq0yyvwUeCLZVii64FrHqdMN1cagfDfaOIGc0XIO3YoF7Rob/ArC5i' \
			b'ZrnecqJG7nyUmhhwaz0WMwOcOuDUSTtKrExR3UknWwF4gtyoEAdwCaos2E/Ii8BaROdQd+hUKY9KeVTKXyYMpVu4UN4ZOyJ9OXIhaDwHzXFoO5f6yoDmCmguOhEh4DAgoU8J49mugldcgYgKRJlnwfScJlvCem16JT5b1LtFtjalbM+7kt05s6fPmD1u2y7t' \
			b'OjVp26mRbrhRq0aKh3JjzZH490n7dVeRywwP3BrpIabqmHsLkQPkQ1xxRRxvx0AIw8ZIqstaRWgSHAmfhFhCq1WtV21QLTHdqpbqRtgwqrOq86qjenBFuKpcTapIQ9VoqB4NiVRqSPFcR24hriWLmncq2ILN+0a8acQbOLx7w3so3BpseeDdR9565L083sdj' \
			b'cfK2F2+o8ljLu5S86csQ8A2JN3DN2ceBT66THXbxW6GUQS2pHDpSwy0du0k0oqZ9WLIrBburUPtzKj54l3xAODlHtmpJwll6dp3gwvJvSYx07B0CHjw7CzghasRnIsCXg5f6DZdGJbNvDjtLeN+XQW2+jPxHKagFuCB256FS2TGFfVissEWR1HBL9qBgDwl2' \
			b'F+LyA7NGQUtZ7DNCD6L4Q3BZkoRK9jZRY8HQLROjc2Rq/EALJSV+QF3PmmepUlFOf6t+8+bTJTeM9nQOv/PYzbjmeuzA9aGwXALZzcDvCLxa8Hsz8O4B3K1gZWxK31WiVW6jnBj1poJrCVF5JMcdIEWhZWCoyonRKd5SoAegMkrH8MxZRwit4ZmTbUdn7zuW' \
			b'4CnEw4DNntIkOjVAmSlVuNTNp6zuHZ8sNxmd3e8yON/Bc194OoGnq+HpAE8HeLrN8HQCT7cbnm4cBJ6uhqfbDs8h63Z4Dsl2wNPV8HQ1PBOlaXg6wHOgNA+e9g6ee8OzFXi2NTxbwLMFPNvN8GwFnu1ueK4FgWdbw7PdDs8h63Z4Dsl2wLOt4dnW8EyUpuHZ' \
			b'Ap4DpXnwdDPheexJq95/3jqJ3Ml5qznO3HUriLkZ4QNcgFhuo5xITtLSGcSmCCWgJZkcdwDaNOPAgJZTAnSaugoBcGNQsulzjwGei9oK8JxswwRWih5wDu/yAefCT6oooN7TnIS6JO9KmrOg7u+gfiSoa4G6rqGuAXUNqOsa6jqHCupaoK53Q12Pg0Bdr0Nd' \
			b'A+o6ebwD6sgxhvpQ1HaoD8k2Qb3q0qW8AuoaUM/rtZ7mNNQ1oJ5pzoJ6uIP6kaAuCztTL+wMFnYGCztTL+yMyaGCuizyzO5FXllAKsaByhjqWOgZzFbk1Odeg/pQ1HaoD8k2Qd1UUK/XfgZrP0mToJ5oTkMdy7+C5iyoxzuoHwnqVqBua6hbQN0C6raGus2h' \
			b'groVqNvdULfjIFC361C3gLoF1C2gjhxjqA9FbYf6kGwT1G0FdVtD3QLqNkM90ZyGugXUM81ZUG/voH4kqEeBeqyhHgH1CKjHGuoxhwrqUaAed0M9joNAPa5DPQLqEVCPgDpyjKE+FLUd6kOyTVCPFdRjDfUIqMcM9URzGuoRUM80Z0G9Y6gTUtN2zU0AH0+O' \
			b'ebcGeze1u3JA8DeHUgA2Hih5V9nKLoupjS8GxhcD44upjS+mzaHUhYh80vfsVIe1IOrQrqsD7DF8Qq+2zDnG6iCxLEwzYZ/hF1atG6vGUNYm1Wgr1ajNNQbmGkljpCVEPVDgBvWA1aagO0s9dPNHhoLTa8ZFjQbyXr28XV9ogIXlxsJyY2vLjS1CpQEWKeW4' \
			b'QwNsMw6sAXbdeGNhvLEw3lgYb1KOkQbkorYOCDnZBtTbynhja+ONhfHGZuNNT3MS8RbGm4LmPMTP3YW8m/zsC3ex3tjaemNhvbGw3tjaekO3QyjhLsnkuAvrehwE6+vWGwvrjYX1xsJ6k3KMsT4UtR3rQ7JNWK+sN7a23lhYb2y23vQ0p7EO601Bcx7W525p' \
			b'HgPrdhfcp3xjLgzxsrK19crWYmVrsbK19crW2hwqxMvK1u5e2ZYFpGIcqCTESxkJ9FjcWixuLRa3Od8Y98OD7bgfkm3CfbW+tfX61mJ9a/P6tqc5jXusbwua83A/d6/0Dvc3w71M7flY4h4uVHxiafka9z6HCvdecO93496Pg+DeZ9xnhyqhAYYMCjdFAWu4' \
			b'Hx5sx/2QbBPufYV7X+PeA/c+4z7RnMa9B+4zzXm4v81N2L8C7oPgPtS4D8A9fAdt7TzIUuxDhXvxHrS73QfLAlIxDlR63IeMe3gS8skgqSkKWMP98GA77odkm3AfKtzXXoXCUiKfcJ9oTuM+APeZ5jzcH2ZHVqeXG+BZf0MF8OmTJnurQVtogrkAZdAyCOh6' \
			b'EEh+tBqDgK4HAWahD5WjjQwCdIwwd2p8z01OGzxu/DiIx00eDTRGg86pLsD9BmOCxpigMSbk3GNvnLLkQj00f1ds3SlnSLpBRXQ1NOh6aNAYGnQeGnq60+45GBoKmvNU5GA7uX9QP/6gZpy9WljZArD1FoDFFoDFFoCttwBszKEaI2QLwEInxIvM4rRhpIjj' \
			b'ICNF3ggol8PYC7DYC7DYC8j5xiNFWeb2wWJItmmwqHYEbL0jYLEjYPOOQE9zerDAjkBBc54mHGyj90+kCfZI2uDEBOpqE6iDCdTBBOpqE6grQqkNkkyOJDs+EX9ymtYG14wDa4PLVlApCdrgYAh1MIQ6GEJzvpE2VGVu1YacbIM2uMoc6mpzqDYenKW6QyN6' \
			b'upMa4WASLejO04iD7QefrUY4UYpwPnohtlJX20odbKUOtlJX20pZhn2o9EJspQ62Uofv0cppg17ocRC9yBZTKSnpBYymDkZTB6NpzjfWi7LM7XoxJPOgFzxojbSjMqC62oDaCyIJIClHSjatHLChFsTnKUenVv3+caUedsrnvtu8em6zY/20V/3O/d6tzvRb' \
			b'Hek3wFQgWsKy3rudekOOkbnJYX65eznLYCu94re5xM/baZVP/W53hh+/5la6wm8ACyOlBAhe/z8wEMKxsNB0O/DgZHSZxgU958/q8jd1B4zwGy3uNrHS+dPBRY98ssaQ6UU1AZ3c+esBRv0AMIaTPlW/gm8hHKl3YXGZS+5luHryxfRj9zZaiDb79jrmImDi' \
			b'Z0DlwmHSHggmUtKOgWl/mNhzmqXEu4nKZkxoecHu2JMVdyo83LzPcH+FfuNAfYY4aOoj9Bt+Bk7MPlDR2dHphh3Iri+G7N2BuAQUfRCwBOzk8Wk/uITaJelAPcru73zs2aPwV1TkGx/rgFG/GU/r4k6+lhDukLMvcmDf59OeyImXgRyGSUzsbkFOVKtTz1QO' \
			b'sdyJN5incMufxzg0xsWhlja6eIFjj3GnJdmcFAEnt6U5e47Nfku2s+7UzX0C6+naF8eq1ndHbn0msGfjuwOoPOfa3vxsLcxfBtv1TTBid/Wn7gYKFAgQ/pJdgPqto9HfSIPrP3mDu3BMtb9Ji3NvEU7e4qTi1A7hU8JbGz9dttL45s/e+PHsGl/CWTS+le8Z' \
			b'avmKFXGJzdhWPB1IdOwDAOdJyw6QXG/2gzQ8fyAorPApmHEmxyvG1iI5ZbSS3FPyMHf5yQvPeavO/RaYu7CjeXSAY4MsC9u5cJCUN1gK7rng297moa0WdVQjEfkcec+R9IHEnEQsUJ6vbvsK9lBCZYk6mhnp3/H/NFeG+xTfCaZpxZTALxKqK9mCc5YIxvhc' \
			b'5kK+Lb0aFCdlH+QXxvKK0Ka6hr1PUqjLln9rLW9UanlPmqTEH7fu3XPEoQbOMuwxzFve/HJ74C0CNgDzdLFJNl5sOjO7SzOzQNLv9Z+UYKsS8F3nDYVYhV/rlC1/Uo68UAG/5qEo6krL0jozKtDx8OTSjxYi/SWPKHIlJfvpkuEhtbV8elz8MMbVcZBi2EYB' \
			b'Plib6aRt7MF/ieiSGo1+GFnHseNRcSH/cJx4CYfkpuWpwB4/YaM9OBs0sdjnJ1x0c7hg37iSEb2bF+4Wd4VuFMOj8XRSYRXfBwgSsxe7TckxE9nMNXdEPKnDxcxQpp/KC+718bm36ggB3Jsx96X/JV7Vl/fIpusjvRR7UhYfoy/9JrN/pLwkAV9Irm7v87gV' \
			b'akGdIshf7O/YbWk6JeRlj9/aUR0hgHu3s7U31aRs5KlaFTXb3qidKgNP0vowejQKXdsn45naeoqyyLXHqL2/9dob/AfokwbUPdx+3b06eUDd4+3XPaiTB9S9vf26d+rkAXXvblj3raPaDSTAi9T9Q2fHMbw+3bMULHXWJljHGeT3kIhT2wPeudiZbD3wun1e' \
			b'UohmbfZ266Jp1W0HSOaMZ4b8Rt65BAjLJtshL5250oh18mX1/P+aRBZUNU7V9tapbjBBmSR5L5/u5X9nppMJj7JF4Mgl60WQT39Fy2tmdnBL0VGEM5guWw0jjE0MtbyYcLKkIFrfLv4P/nTX8w=='

	_PARSER_TOP = 'expr'

	_GREEK      = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'

	_SPECIAL    =  r'\\partial|\\pi|\\infty'
	_CHAR       = fr'[a-zA-Z]'
	_SHORT      =  r'pi|oo|True|False|undefined'
	_TEXTVAR    =  r'\\text\s*\{\s*(True|False|undefined)\s*\}'
	_ONEVAR     = fr'{_CHAR}|{_GREEK}'
	_DSONEVARSP = fr'(?:(\d)|({_SHORT})|({_CHAR}|{_GREEK}|{_SPECIAL})|{_TEXTVAR})'
	_STR        =  r'(?:\'([^\']*)\'|"([^"]*)["])'

	_FUNCPYONLY = '|'.join (reversed (sorted ('\\?' if s == '?' else s for s in AST.Func.PY_ONLY))) # special cased function name '?' for regex
	_FUNCPYTEX  = '|'.join (reversed (sorted (AST.Func.PY_AND_TEX)))

	TOKENS      = OrderedDict ([ # order matters
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('TRIGH',         r'\\?(?:(a)(?:rc)?)?((?:sin|cos|tan|csc|sec|cot)h?)|\\operatorname\s*\{(sech|csch)\s*\}'),
		('FUNC',         fr'({_FUNCPYONLY})|\\?({_FUNCPYTEX})|\\operatorname\s*\{{\s*({_CHAR}\w*)\s*\}}|\$({_CHAR}\w*)'),
		('SQRT',          r'\\?sqrt'),
		('LOG',           r'\\?log'),
		('LIM',           r'\\lim'),
		('SUM',           r'\\sum'),
		('INT',           r'\\int(?:\s*\\limits)?'),
		('LEFT',          r'\\left'),
		('RIGHT',         r'\\right'),
		('CDOT',          r'\\cdot'),
		('TO',            r'\\to'),
		('FRAC2',        fr'\\frac\s*{_DSONEVARSP}\s*{_DSONEVARSP}'),
		('FRAC1',        fr'\\frac\s*{_DSONEVARSP}'),
		('FRAC',          r'\\frac'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
		('VAR',          fr"(?<!{_CHAR}|['])_|({_SHORT})|(d|\\partial\s?)?({_ONEVAR})|{_SPECIAL}|{_TEXTVAR}"),
		('STR',          fr"(?<!{_CHAR}|['}}]){_STR}|\\text\s*\{{\s*{_STR}\s*\}}"),
		('SUB1',         fr'_{_DSONEVARSP}'),
		('SUB',           r'_'),
		('CARET1',       fr'\^{_DSONEVARSP}'),
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
		('INEQ',          r'==|!=|\\neq?|<=|\\le|<|>=|\\ge|>'),
		('EQ',            r'='),
		('DIVIDE',        r'/'),
		('FACTORIAL',     r'!'),
		('COMMA',         r','),
		('ignore',        r'\\,|\\:|\\?\s+'),
	])

	_FUNC_AST_REMAP = {
		'Abs'      : lambda expr: _expr_func (1, '|', expr.strip_paren ()),
		'Integral' : _expr_func_intg_remap,
		'abs'      : lambda expr: _expr_func (1, '|', expr.strip_paren ()),
		'exp'      : lambda expr: _expr_func (2, '^', ('@', 'e'), expr.strip_paren ()),
		'factorial': lambda expr: _expr_func (1, '!', expr.strip_paren ()),
		'ln'       : lambda expr: _expr_func (1, 'log', expr.strip_paren ()),
	}

	def expr_comma_1    (self, expr_comma, COMMA, expr):                     return AST.flatcat (',', expr_comma, expr)
	def expr_comma_2    (self, expr):                                        return expr

	def expr            (self, expr_eq):                      	             return expr_eq

	def expr_eq_1       (self, expr_ineq1, EQ, expr_ineq2):                  return AST ('=', '=', expr_ineq1, expr_ineq2)
	def expr_eq_2       (self, expr_ineq):                                   return expr_ineq
	def expr_ineq_2     (self, expr_add1, INEQ, expr_add2):                  return AST ('=', AST.Eq.LONG2SHORT.get (INEQ.text, INEQ.text), expr_add1, expr_add2)
	def expr_ineq_3     (self, expr_add):                                    return expr_add

	def expr_add_1      (self, expr_add, PLUS, expr_mul_exp):                return AST.flatcat ('+', expr_add, expr_mul_exp)
	def expr_add_2      (self, expr_add, MINUS, expr_mul_exp):               return AST.flatcat ('+', expr_add, expr_mul_exp.neg (stack = True))
	def expr_add_3      (self, expr_mul_exp):                                return expr_mul_exp

	def expr_mul_exp_1  (self, expr_mul_exp, CDOT, expr_neg):                return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_2  (self, expr_mul_exp, STAR, expr_neg):                return AST.flatcat ('*', expr_mul_exp, expr_neg)
	def expr_mul_exp_3  (self, expr_neg):                                    return expr_neg

	def expr_neg_1      (self, MINUS, expr_diff):                            return expr_diff.neg (stack = True)
	def expr_neg_2      (self, expr_diff):                                   return expr_diff

	def expr_diff       (self, expr_div):                                    return _expr_diff (expr_div)

	def expr_div_1      (self, expr_div, DIVIDE, expr_mul_imp):              return AST ('/', expr_div, expr_mul_imp)
	def expr_div_2      (self, expr_div, DIVIDE, MINUS, expr_mul_imp):       return AST ('/', expr_div, expr_mul_imp.neg (stack = True))
	def expr_div_3      (self, expr_mul_imp):                                return expr_mul_imp

	def expr_mul_imp_1  (self, expr_mul_imp, expr_int):                      return AST.flatcat ('*', expr_mul_imp, expr_int)
	def expr_mul_imp_2  (self, expr_int):                                    return expr_int

	def expr_int_1      (self, INT, expr_sub, expr_super, expr_add):         return _expr_int (expr_add, (expr_sub, expr_super))
	def expr_int_2      (self, INT, expr_add):                               return _expr_int (expr_add)
	def expr_int_3      (self, expr_lim):                                    return expr_lim

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                              return AST ('lim', expr_neg, expr_var, expr)
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_doublestar, PLUS, CURLYR, expr_neg):   return AST ('lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_doublestar, MINUS, CURLYR, expr_neg):  return AST ('lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6      (self, expr_sum):                                                                            return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQ, expr, CURLYR, expr_super, expr_neg):                  return AST ('sum', expr_neg, expr_var, expr, expr_super)
	def expr_sum_2      (self, expr_func):                                                                           return expr_func

	def expr_func_1     (self, SQRT, expr_func_neg):                            return _expr_func (1, 'sqrt', expr_func_neg)
	def expr_func_2     (self, SQRT, BRACKETL, expr, BRACKETR, expr_func_neg):  return _expr_func (1, 'sqrt', expr_func_neg, expr)
	def expr_func_3     (self, LOG, expr_func_neg):                             return _expr_func (1, 'log', expr_func_neg)
	def expr_func_4     (self, LOG, expr_sub, expr_func_neg):                   return _expr_func (1, 'log', expr_func_neg, expr_sub)
	def expr_func_5     (self, TRIGH, expr_func_neg):                           return _expr_func (2, 'func', f'{"a" if TRIGH.grp [0] else ""}{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func_neg)
	def expr_func_6     (self, TRIGH, expr_super, expr_func_neg):
		return \
				AST ('^', _expr_func (2, 'func', f'{TRIGH.grp [0] or ""}{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func_neg), expr_super) \
				if expr_super != AST.NegOne else \
				_expr_func (2, 'func', TRIGH.grp [1] or TRIGH.grp [2], expr_func_neg) \
				if TRIGH.grp [0] else \
				_expr_func (2, 'func', f'a{TRIGH.grp [1] or TRIGH.grp [2]}', expr_func_neg)

	def expr_func_7     (self, FUNC, expr_func_neg):
		func  = FUNC.grp [0] or FUNC.grp [1] or FUNC.grp [2] or FUNC.grp [3] or FUNC.text
		remap = self._FUNC_AST_REMAP.get (func)

		return remap (expr_func_neg) if remap else _expr_func (2, 'func', func, expr_func_neg)

	def expr_func_8     (self, expr_fact):                                   return expr_fact

	def expr_func_neg_1 (self, expr_func):                                   return expr_func
	def expr_func_neg_2 (self, MINUS, expr_func):                            return expr_func.neg (stack = True)

	def expr_fact_1     (self, expr_fact, FACTORIAL):                        return AST ('!', expr_fact)
	def expr_fact_2     (self, expr_pow):                                    return expr_pow

	def expr_pow_1      (self, expr_pow, expr_super):                        return AST ('^', expr_pow, expr_super)
	def expr_pow_2      (self, expr_abs):                                    return expr_abs

	def expr_abs_1      (self, LEFT, BAR1, expr, RIGHT, BAR2):               return AST ('|', expr)
	def expr_abs_2      (self, BAR1, expr, BAR2):                            return AST ('|', expr)
	def expr_abs_3      (self, expr_paren):                                  return expr_paren

	def expr_paren_1    (self, PARENL, expr_comma, PARENR):                  return AST ('(', expr_comma)
	def expr_paren_2    (self, LEFT, PARENL, expr_comma, RIGHT, PARENR):     return AST ('(', expr_comma)
	def expr_paren_3    (self, IGNORE_CURLY, CURLYL, expr, CURLYR):          return expr
	def expr_paren_4    (self, expr_frac):                                   return expr_frac

	def expr_frac_1     (self, FRAC, expr_term1, expr_term2):                return AST ('/', expr_term1, expr_term2)
	def expr_frac_2     (self, FRAC1, expr_term):                            return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_term)
	def expr_frac_3     (self, FRAC2):                                       return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 4))
	def expr_frac_4     (self, expr_term):                                   return expr_term

	def expr_term_1     (self, CURLYL, expr, CURLYR):                        return expr
	def expr_term_2     (self, STR):                                         return AST ('"', STR.grp [0] or STR.grp [1] or STR.grp [2] or STR.grp [3] or '')
	def expr_term_3     (self, expr_var):                                    return expr_var
	def expr_term_4     (self, expr_num):                                    return expr_num

	def expr_num        (self, NUM):                                         return AST ('#', NUM.text) if NUM.grp [0] or NUM.grp [2] else AST ('#', NUM.grp [1])

	def expr_var_1      (self, var, PRIMES, subvar):                         return AST ('@', f'{var}{subvar}{PRIMES.text}')
	def expr_var_2      (self, var, subvar, PRIMES):                         return AST ('@', f'{var}{subvar}{PRIMES.text}')
	def expr_var_3      (self, var, PRIMES):                                 return AST ('@', f'{var}{PRIMES.text}')
	def expr_var_4      (self, var, subvar):                                 return AST ('@', f'{var}{subvar}')
	def expr_var_5      (self, var):                                         return AST ('@', var)

	def var             (self, VAR):
		return \
				f'\\partial {VAR.grp [2]}' \
				if VAR.grp [1] and VAR.grp [1] != 'd' else \
				AST.Var.SHORT2LONG.get (VAR.grp [0] or VAR.grp [3], VAR.text)

	def subvar_1        (self, SUB, CURLYL, expr_var, CURLYR):               return f'_{{{expr_var [1]}}}'
	def subvar_2        (self, SUB, CURLYL, NUM, CURLYR):                    return f'_{{{NUM.text}}}'
	def subvar_3        (self, SUB, CURLYL, NUM, subvar, CURLYR):            return f'_{{{NUM.text}{subvar}}}'
	def subvar_4        (self, SUB1):                                        return f'_{AST.Var.SHORT2LONG.get (SUB1.grp [1] or SUB1.grp [3], SUB1.text [1:])}'

	def expr_sub_1      (self, SUB, expr_frac):                              return expr_frac
	def expr_sub_2      (self, SUB1):                                        return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1    (self, DOUBLESTAR, expr_func):                       return expr_func
	def expr_super_2    (self, DOUBLESTAR, MINUS, expr_func):                return expr_func.neg (stack = True)
	def expr_super_3    (self, CARET, expr_frac):                            return expr_frac
	def expr_super_4    (self, CARET1):                                      return _ast_from_tok_digit_or_var (CARET1)

	def caret_or_doublestar_1 (self, DOUBLESTAR):                            return '**'
	def caret_or_doublestar_2 (self, CARET):                                 return '^'

	#...............................................................................................
	_AUTOCOMPLETE_SUBSTITUTE = { # autocomplete means autocomplete AST tree so it can be rendered, not expression
		'CARET1'             : 'CARET',
		'SUB1'               : 'SUB',
		'FRAC2'              : 'FRAC',
		'FRAC1'              : 'FRAC',
		'expr_sub'           : 'SUB',
		'expr_super'         : 'CARET',
		'caret_or_doublestar': 'CARET',
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

	def _insert_symbol (self, sym):
		if sym in self.TOKENS:
			self.tokens.insert (self.tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, sym), '', self.tok.pos))

			if self.autocompleting and sym in self._AUTOCOMPLETE_CLOSE:
				self.autocomplete.append (self._AUTOCOMPLETE_CLOSE [sym])
			else:
				self.autocompleting = False

		else:
			self.tokens.insert (self.tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, (None, None, '', None)))
			self._mark_error ()

		return True

	def _parse_autocomplete_expr_comma (self, rule):
		idx = -1 -len (rule [1])

		if self.stack [idx] [1] == 'CURLYL':
			return self._insert_symbol ('CURLYR')

		if self.stack [idx] [1] != 'PARENL':
			return False

		if self.stack [idx - 1] [1] == 'LEFT':
			return self._insert_symbol ('RIGHT')

		return self._insert_symbol ('PARENR')

	def _parse_autocomplete_expr_int (self):
		s               = self.stack [-1]
		self.stack [-1] = (s [0], s [1], AST ('*', (s [2], ('@', ''))))
		expr_vars       = set ()
		expr_diffs      = set ()

		if self.autocompleting:
			stack = [s [2]]

			while stack:
				ast = stack.pop ()

				if ast.is_var:
					(expr_diffs if ast.is_differential else expr_vars).add (ast.var)
				else:
					stack.extend (filter (lambda a: isinstance (a, tuple), ast))

		expr_vars  = expr_vars - {'_', 'e', 'i'} - set (AST.Var.LONG2SHORT)
		expr_vars -= set (var [1:] for var in expr_diffs)

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

		if pos >= len (rule [1]): # special error raised by rule reduction function or end of comma expression
			if rule [0] == 'expr_comma':
				return self._parse_autocomplete_expr_comma (rule)

			if rule [0] == 'expr_int':
				return self._parse_autocomplete_expr_int ()

			return False

		return self._insert_symbol (rule [1] [pos])

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

		if os.environ.get ('SYMPAD_DEBUG'):
			rated = list (rated)
			print ()
			for res in rated:
				print ('parse:', res [-1])

		return next (iter (rated)) [-1]

class sparser: # for single script
	Parser = Parser

# DEBUG!
if __name__ == '__main__':
	p = Parser ()
	a = p.parse ('\\left(1,2')
	print (a)

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
