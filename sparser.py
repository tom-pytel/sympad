# TODO: Merge trigh into func.
# TODO: Change vars to internal short representation?
# TODO: 1+1j complex number parsing?

# Builds expression tree from text, nodes are nested AST tuples.

# FUTURE: verify vars in expr func remaps
# FUTURE: vectors and matrices, Python long variable names, Python '.' members, assumptions / hints, stateful variables, piecewise expressions, plots

import ast as py_ast
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
		return AST ('intg', _expr_int (ast.intg, () if ast.from_ is None else (ast.from_, ast.to)), ast.dv, *from_to)

	raise SyntaxError ('integration expecting a differential')

def _expr_diff (ast): # convert possible cases of derivatives in ast: ('*', ('/', 'd', 'dx'), expr) -> ('diff', expr, 'dx')
	def _interpret_divide (ast):
		if ast.numer.is_diff_or_part_solo:
			p = 1
			v = ast.numer.var

		elif ast.numer.is_pow and ast.numer.base.is_diff_or_part_solo and ast.numer.exp.is_pos_int:
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
						tail.insert (0, AST ('diff', ast.muls [i + 1] if i == end - 2 else AST ('*', ast [i + 1 : end]), diff.dvs))

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

def _expr_func_remap (remap_func, ast): # rearrange ast tree for a given function remapping like 'Derivative' or 'Limit'
	expr = _expr_func (1, '(', ast)
	ast  = remap_func (expr.paren if expr.is_paren else expr [1].paren)

	return AST (expr.op, ast, *expr [2:]) if not expr.is_paren else ast

_remap_func_lim_dirs = {'+': '+', '-': '-', '+-': None}

def remap_func_lim (ast): # remap function 'Limit' to native ast representation for pretty rendering
	if ast.is_null_var:
		return AST ('lim', ast, AST.VarNull, AST.VarNull)
	elif not ast.is_comma:
		raise lalr1.Incomplete (AST ('lim', ast, AST.VarNull, AST.VarNull))

	commas = ast.commas
	l      = len (commas)

	if l == 1:
		ast = AST ('lim', commas [0], AST.VarNull, AST.VarNull)
	elif l == 2:
		ast = AST ('lim', commas [0], commas [1], AST.VarNull)
	elif l == 3:
		return AST ('lim', commas [0], commas [1], commas [2], '+')
	elif commas [3].is_str:
		return AST ('lim', commas [0], commas [1], commas [2], _remap_func_lim_dirs.get (commas [3].str_, '+'))
	elif commas [3].is_eq_eq and commas [3].lhs.as_identifier () == 'dir' and commas [3].rhs.is_str:
		return AST ('lim', commas [0], commas [1], commas [2], _remap_func_lim_dirs.get (commas [3].rhs.str_, '+'))
	else:
		ast = AST ('lim', commas [0], commas [1], commas [2])

	if commas [-1].is_null_var:
		return ast

	raise lalr1.Incomplete (ast)

def remap_func_sum (ast): # remap function 'Sum' to native ast representation for pretty rendering
	if ast.is_null_var:
		return AST ('sum', ast, AST.VarNull, AST.VarNull, AST.VarNull)
	elif not ast.is_comma:
		ast = AST ('sum', ast, AST.VarNull, AST.VarNull, AST.VarNull)

	else:
		commas = ast.commas

		if len (commas) == 1:
			ast = AST ('sum', commas [0], AST.VarNull, AST.VarNull, AST.VarNull)

		else:
			ast2 = commas [1].strip_paren (1)

			if not ast2.is_comma:
				ast = AST ('sum', commas [0], ast2, AST.VarNull, AST.VarNull)
			elif len (ast2.commas) == 3:
				return AST ('sum', commas [0], ast2.commas [0], ast2.commas [1], ast2.commas [2])

			else:
				commas = ast2.commas
				ast    = AST (*(('sum', ast.commas [0], *commas) + (AST.VarNull, AST.VarNull, AST.VarNull)) [:5])

		if commas [-1].is_null_var:
			return ast

	raise lalr1.Incomplete (ast)

def remap_func_diff (ast): # remap function 'Derivative' to native ast representation for pretty rendering
	if ast.is_null_var:
		return AST ('diff', ast, (AST.VarNull,))
	elif not ast.is_comma:
		raise lalr1.Incomplete (AST ('diff', ast, (AST.VarNull,)))
	elif len (ast.commas) == 1:
		raise lalr1.Incomplete (AST ('diff', ast.commas [0], (AST.VarNull,)))

	commas = list (ast.commas [:0:-1])
	ds     = []

	while commas:
		d = commas.pop ().as_differential ()

		if commas and commas [-1].is_num:
			ds.append (AST ('^', d, commas.pop ()))
		else:
			ds.append (d)

	return AST ('diff', ast.commas [0], AST (*ds))

def remap_func_intg (ast): # remap function 'Integral' to native ast representation for pretty rendering
	if not ast.is_comma:
		return AST ('intg', ast, ast.as_differential () if ast.is_var else AST.VarNull)
	elif len (ast.commas) == 1:
		ast = AST ('intg', ast.commas [0], AST.VarNull)

	else:
		ast2 = ast.commas [1].strip_paren (1)

		if not ast2.is_comma:
			return AST ('intg', ast.commas [0], ast2.as_differential ())
		elif len (ast2.commas) == 3:
			return AST ('intg', ast.commas [0], ast2.commas [0].as_differential (), ast2.commas [1], ast2.commas [2])
		else:
			ast = AST (*(('intg', ast.commas [0], ast2.commas [0].as_differential ()) + ast2.commas [1:] + (AST.VarNull, AST.VarNull)) [:5])

	raise lalr1.Incomplete (ast)

def _expr_curly (ast):
	if ast.op != ',':
		return ast

	c = sum (bool (c.is_vec) for c in ast.commas)

	if not c:
		return AST ('vec', ast.commas)

	if c != len (ast.commas) or len (set (len (c.vec) for c in ast.commas)) != 1:
		raise SyntaxError ('invalid matrix syntax')

	return AST ('mat', tuple (c.vec for c in ast.commas))

#...............................................................................................
class Parser (lalr1.Parser):
	_PARSER_TABLES = \
			b'eJztXftvHDeS/mcOiAT0AMM32785jjdrnO1kHSfYgxAYTuIcgou9OcfZu0Ow//tV1Uc2ye6e6RlpJM1Igqh+sPmoKtbHV5Gcs4vPXjx7+e03n3WfPXv5mq7Pn72g6zffyvVvr8Trqy/p+vrVsy//Sve/fPvyCXs+/Qt/+/zxK7p+/fjV05fPOY0vX3716umb' \
			b'J9++ev4fHPbV4yfpptJdc6SnX7558ZgS/Ht6+bx5+655+3p4k1Q5l88pnX9/+pofv3n9Ssj9nK4vhejvhKJ/e/fhpxyF35989eLF4xJ1IJofHr/4mq5PX35RiPri8+ffPH/8zV+Tf6GP375r3gp9LKDXKfJroeIJZcE+T/8m8pXb189F2l88++7ZF085zBdf' \
			b'vRZGHidOVI7ID0///oTZ/PrVsxdPOdrrr+jy49uP7z69+cfHNz/98Ovvn95+JK/f//jhn/Lw7n9/+/jm/dtPbz7+439Gr7/n99//+O3dEPbnPz78+ObDu//M7z/+4/37tyXkD/RYpfzhj/f58dO7j8PzDx/f/vhf7z4Nafzx8df/q3If8qJg+fk3YuJDfnn7' \
			b'w0Dcb4Xun9/++Kkms1A1ZFyR9usvg+8vH4Z47//49c0v73/Lrz/98s/y+PPPA1uFf45ADwNlP/1UUn333/l5ePrs++7ibGVMZ8J5h4fID6pbabmH7ix2fUcexnf9efYTn+F1pSSSlX9Lcd15eV+XV3qgu9acpiZ/HThVHc+zd/IsPitt5Cngojmv89Ynv9IH' \
			b'flCcuOqHxP159k6exYcy4CeKKuRH+beUKRgb3tfFhx44LouqM5SeQVr8wKJwuFgQRU8r5eWpp+yZG+ZvfT54mfpV2fTAfvxE8iOZJWHgjRNQJJ/G203efOMzfesbn1C/EdXCEmUBgujpbC0voiEoY/LI7yuQvSZ2Us59/pg8h5eVkjJSVBi6o9JlXkksVrSJ' \
			b'o6Jo5r+zctrdgq3bUCsFJVonveNyMevOqFr7mNTsX3w8fEzxCfCxxSfCx2UfUi2RjMLFrLPOGpWUlLzkYlhx0rfBK7/yF3py8m9N5ie92/K+EhXr5Z+kfH4+PNGDl8KDPnp+YBpJj6CvVLQqQS6BOQp8CjaLNwlSpYLKfqSs8uRxWeXQ9KiQE31hFCt8oFcr' \
			b'2kWKf2aqojODBrDypPTNoIHEmwmDCqbXdesRSy59Z0UkmrJQ+UGnB8ouP2loLqNZk0i5HCH97EXv5H3ehhqHyO/0KiWnheXEWJJV8WRSZvz4rfhDSJQ8UUgV9AWphUSUypUqpNBxnexV53XnTed954MkRIqvWKzedl6UhvTE0gPJPTCDBJEQuhBF90nsVIlZ' \
			b'0lwuaZIoyZDz9F0wXaCInesoZYqy7oLqgu6kaiadYJ125FTndOdM5yio66jYCR1K1IeVRXfRdNF20XXRd5GIjl3su37d9UQ5ceC/Z+XkEjJ8vTjTcj8jPhXzfUbc8jtxzLcg15i+9fLmEcLr5EuioPfTFIUH9z5AGAocakhIq8ShhjA8y+g02HLgx4I9K4QH' \
			b'1wV/l/TYZi49uISyWmjrWbSpTMWbajZqaKm1ubOojg7sQ4UDhBEihGCAWSOKTDW/XR8N4RfSyt2DEqJSAByNLaUAUB4RidAi4ysS+y6uu6i6qI+J0HCMqmwiWg6XWw5UTUEKvhIk4TWk+skiBJoch5tCNM5akpFCuau4OPMQhO/vRTVwFlAXB506YKLIB0rb' \
			b'rFOi8YCJ6h6JOiHcxc5RSVDSvnPhzhYTsavvF7vmfrFr7xG7Zw7NukLzpDCeieiOxFT/xjTYQ5iIfmSPBqkX6Pe6603X2653XG0jYO+HgSSN8u+a5GRATHzdJY4CM3Q3WIl3hxUvenbaLOgTZ4HnsrRUZmu+8wwQM3Q65FuQb6UubsYbFzwLpCdTegENAyZL' \
			b'rqOz64c5Go05Go05Gi3ZK7wrtEQKk5BsFEhzGPzRKDBlNMIqDIaGgcIdbbJN6nVbaYGPhSyZrZkpMmNSIYmSHdewnCc1QJw/PuIIguhpxSMr56iuqUqI6H0aoFs71EpJf6A+dxTTFzzNo+/BHMcFT2RpzGDdD36VvxeMnqWalHKZNgIXPLV1p+Grpc46IEam' \
			b'k708dafTbBuL2GGU7fpsbU0TxR6hXbJcOj0b2pl5bzvrHVElRyncZrB/wdMCGvMB6Ln1qMV7aECfugE9em5U/uYcY2cz7XKK39iKHGd8+dXg1aReuTklO+wFDyDMCQ0gZORg7tJsBw9wdBqAGAxADAYgdBtFkfAqQNcUkKPueockbBCEjLdYVAq2LB6HpOGX' \
			b'gQ3TwE4oAO8h5ChhjoU77sLKaBMlGlB7jNssB+97ZtxQ88JQfsabGn2pdnuUNRRAhyw2Ea5D8+BEEe668Jy/y5UC9yWkaA1uQHpEeceI8u7R3+hRS/ZSS87WIsS8Pa02m4mcdFqYYDQfFs2HlYkqiCiIr9SY9tjmF7hOlhYPTK1BqZP7fB+T6waLfqkF3m1C' \
			b'uKk7nqgp+tQ16yGJXpRl1HUk2TnIzkF27u6CR1rUO8wf67iUolwpI5fUyeXGAArkoEAOKmJRVVhoiE39MQ+l8FAKupEovhc0eSyF8QjvUvhw0raFC+Y1gNcgUsJQCeO3IN/aFUKUr4SnFCGpiNgxRYinL4/+1FmIJ84C61EP7ZLNC7x6di0t3rq7WAsJqLyG' \
			b'NLlvWOU1sIz6DvSDTjO0glYYjKlpRJ04K5wpU+hLpn75UIHGLBYRVFrZHJqlig3vvbRJzAWxsSYm1tQfWRMba+Jjzbwz3/SdeWQmuevLbLI0eVU4Lwnn9eC8FJzXyvOqLV5sxQtreVknr+nktZO8cJKXJvJCQLbgsPWGl9TzSmxehs3y5SW6Ulz0jSc8eLaD' \
			b'F6JzH4lXbvOCetYnXmDBi+J4pSDb6diWxut6eVEvWwt4hp4Nd7zylxdx8AIOXr0Reyo/z/LjPSmet7HwTg7egKTpmZVqRXJfUVx6otgr3sZDqZKSedE0cSve38H7Q4KE83wJWjbe8H4Pn/5WjrdcRdl6sSKhr4iUFSnYyvPWLd/VfytmjXe6EKtMHlGwCrzf' \
			b'hzNeyeYug6wd3xTv0oicJW+XomyouKvEeL8Uleyq581iThLkfWWUOueOrV9MM9MXhGnZDkXJUUjDXyhylKx5Rw+2qq2cSmxRAqSFK6GT02VpKM6FCYy8wyeF5C1FnPdaImPTFcuAd7VRAj2LT7FkeLMWheGNXAMTVKAry//x++5Prx6tREss3c2/uA1lFHKJ' \
			b'LaNQXz/yati5fdA2h7R1Qtt1Ie2SKFtEFus509lASwFZfEvQEjgUbPFrBSgJL9cKUlyu2S3Bqg6bYngkSAyyEgm4jELGQBbDaoyncSIjULWIKsFY7fRGRAn9DaQyU1NQSTJmQFQKuIwpVaBUyGrQpNaPuMYjbXvEVQFpBt3Vv6TT9YCqY0OVtFZ8rVFlgSpb' \
			b'UGVbVNkWVVZQZVtU2eIWUWXHTlBlp6iy21E1SmQ7qoZgrHZ2M6rsBFWJqRlU2RZVCLgDqmxB1UDWjqgyD6g6OlT1gqq2GyivTm4ZVX2Lqr5FVS+o6ltUVW4RVf3YCar6Kar67agaJbIdVUMwFcDrBlT1E1QlpmZQ1beoQsAdUNUXVA1k7YgquzuqbnEcpq4w' \
			b'FNsGuKWhmLm94dgi+Pi4i55LpQafvDq5JfDxYwU+LsXK1UCUuHKtgNgEXgDiKG1JDwnWQEwjMskcBPPqPozKUqwRMMeJbgVmCZZGZiKLKTgln8RWg8/M6xSfkhJoTRDNQlyEqKQIiFYE7gZR9wDRU4WoEYiaFqIGEDUFoqaFqGlcA1EjEDUtROvASxA1k+Q9' \
			b'EpyDqAFEDSCKVjPFGkN0lOh2iA7BMkTNPEQNIGomEE28zkDUAKKlFc1CXIaoKRAtBO4GUf8A0VOFqAwMdTsw1BgY6jIw1O3AUNvGNRCVQaJuB4lN4CWI2knyHgnOQRQDRbkZ3FyONYboKNHtEB2CZYjODxwlH5AxgmjidQaiGDtKzATRJMRliJbhY0XgbhAN' \
			b'DxA9VYg6gahrIeoAUVcg6lqIusY1EHUCUddCtA68BFE3Sd4jwTmIOkDUAaIOEEWsMURHiW6H6BAsQ9TNQ9QBom4C0cTrDEQdIOoKRJMQlyHqCkQLgbtBNB4WopXd8yaAGrdidX1/4CqTQrqdFNKYFNJlUki3k0K6b1wDV5kg0pggYhQaMTGvxlGWQNtPMvFI' \
			b'NoGWw2bMYqZIY7JIbi5F6mfGp22y/eIQdSAgI3d+/khjCklPppAywzPIxRSSxEzITWwsI7fMIlUEziDX60cyqzcFcM8AJvCltQWXhjGWIBxRYxvm2luzxc5/00BeXxOY5dRKPleRVEAMk+xR4VpendwSrvmxwjWXY+VqXJOEJbpcq5a4Cb8A6lHykh4SnGmJ' \
			b'JX/QbJC3cTnWCNJ1iioFGWNaxppqhO1CR8K2iGaKbckTJLXYznxPsS0pgW4uNy6FMIRfxrekCnxXRO7WMqv1lZvmo8P0/elAGyC3XVJgsKTAlCUFpl1SwOVUuQa5COzlWiO3Dr+EXD3JwSPBOeRilYHcDG4uxxojd5To1pa4BMtonV91IPmAjBFaE68zaMXC' \
			b'A4mJljjLcRmpZe1BReCOSN1jSc/DOPe4YCqzxaadLTaYLTZltti0s8WMh8rVMJW4cq0xWgdewqiZJO+R4BxGMVtsMFucbKzpaYzRUaLbMToEyxidny02mC02k9nizOsMRjFbbMpscaZ8GaNltrgicEeM7rFA6Kgwun2Ie19gKtNRpp2OMpiOMmU6yrTTUcY1' \
			b'roGpTEeZdjqqCbwEUzdJ3iPBBFNJO6EUs1EGs1EGs1El3hioo2S3A3UIloE6PyFlMCFlJhNSmdsZoGJCypQJqSzGZaCWCamKwL2GtWqPpUcPeD06vAbBa2jxGoDXUPAaWryGxjV4DYLX0OK1DryE1zBJ3iPBjNdQ8BqA1wC8BuB1iDfG6yjZ7XgdgmW8hnm8' \
			b'BuA1TPCauJ3BawBeQ8FrEuMyXkPBayFwP7ye6qKmB7wyXqPgNbZ4jcBrLHiNLV5b1+A1Cl5ji9c68BJep8l7JJjxGgteI/AagdcIvA7xxngdJbsdr0OwjNc4j9cIvMYJXhO3M3iNwGsseE1iXMZrLHgtBO6H1wOvcHow/NwOcMXwY1rDj4HhxxTDj2kNP6Zv' \
			b'XANcMfwYGH7k21puehRlCb79JBOPZDN8+wJfGH7SKmEDw0+JN4av+HJplCDbITwEyxCet/wYWH7MxPKTOZ6BMCw/plh+Mh/LEC6Wn4rA/SB84BVQDxC+FQizKoq4awhb2HhssfHY1sbDxVO5GsISV64EYfmGILpvoyxAeJSDhZnHFjOP5AAIW1h5LKw8Flae' \
			b'Em8E4ZmUtyK4BEsItvP2HQv7jp3YdzLDUwRb2HfsekBwlucigm2x7VQE7ofgAy+QekDw7SBYdgXYdleAxa4AW3YF2HZXAJdN5RoEy64Ai10BFqsvLFZfNFGWEKwmmXgkmxFcVl9YbA2wwy9ECoKHeGMET1PejuAhWEbw/AYBiw0CdrJBIDM8g2BsELBlg0CW' \
			b'5zKCywaBisD9EPywfupOIFistba11lpYa22x1trWWssFU7kGwWKqtTDVWgyB+ab7NsoSgvUkE49kM4J1QTDstRb2Wgt7bYk3RvA05e0IHoJlBM9bbS2stnZitc0MzyAYVltbrLZZnssILlbbisD9ENwfdpnF5PyXg+HY8pE0V0KzagCt7jioRVe4AJudsl5A' \
			b'rcqBKao9MYULvHLNEgz4yDVihJx+2hg/29tGXNpBO3Gyg9YP0OZHPh+G9VAB4gpHqsjN4Oaq+OO9tZMcYnvEipJqb4z0kl5Cupo/Z0VyBE0t0jP/U6RLSiA877dNQl5EuqQIpFcE7oV0ffgFVcfWXKt702JrabF122Knw5B0abF122J7CTO4BtyI5+Ua0mc5' \
			b'10AWPdexlhY967GTRc+l0dal0dZotDUabY1Gu8QbL3qepByXDMQlrbzueb7d1mi39aTdzjxP0azRbuvSbmepLqJZl3a7InA/NB940dWxQfme4NhKI23bRtqikbalkbZtI82FUbmm5y0tNF+5543m2aJ5bqIs9bwnTnrepXm2vvS80SxbNMsWzXKJN+55T1Pe' \
			b'3vMeguWe93x7bNEe20l7nBme6XmjPbalPc7yXO55l/a4InA/BG9bkmUbENcHMT7g+AA45oOBD9/hllVaql2lpbBKy6NN9li/qMpCLQ7G3W4mikPhoTmsRtZqKazVkm9ruek+BU5RZhDNg5yhw+3GTjrcZcWWKiu2FFZsKazYUlixVeKNO9rTlPnXejnv+XNs' \
			b'hmC5hz2/aEth0ZaaLNrKDM/0sLFoS5VFWzLOSzJd7mWXhVsVkTOotvER15YJ3D1hm39ddAbjB17G9YDuCbr1TbXUYmq2ranZwtRsi6nZtqZm2zeuaanF1GwxkLYwNVuYmpsoSy11P8nEI9ncUhdTs4Wp2cLUbGFqLvHGLfU05e0t9RAst9TzlmYLS7OdWJoz' \
			b'w3O4xicLqnNrnVhZbq2Ltbkicr/W+sALvE4cyaZCsz9RRDuxPLvW8uxgeXbF8uxay7NbN65GtMSVKyHawfLsYHluoiwgepSDg+XZFcuzK5ZnB8uzg+XZwfJc4o0QPZPyVkSXYAEiIR1PHjO4drA/u4n9ObM9xXVODKQnWGfBLsLaFRN0Rel+sHbdRd493AAb' \
			b'qB4gPWBYleWZG7EamkMbZ09s3Gdjr92ALzuDq23934yjGj8z2BlwU2Ol3ZE7dwR3hkuNlRocK98shlwCAav8+DDFbScp7rZVlkuflXjT0Ykjxd10ZHZ9ZGKtpzM6mhW01kvWO3/NeufkDP8Dad+mPlutgXpHLfRJE20aicU0GtumlZQGd+V5/NNoKL2T6hyZ' \
			b'pio599YdWmO3HKObtJbluZPmKmivkrGnGuS8RZPLif19o9W5YR1rd7hB7dZzB+LGS+l42KznRKviUS2Puveqdf2GmndDz+U4a18WT63TKk0NzJ5pq2Ym5Zd1e8MkgMwASOHgf58aWs3X0ht6E5tq6njNurxVkQ+sxZfSXLNDv8Ecs/a2mnvIGpkHKIfoSww1' \
			b'sl/qU7CIN2kr9XdVeETcSs+2vym9PVTte0idVSfd192h98AiOXgPYj9dtVfo/5Jkbm3cxb/id2ujL/61Qf6J6xPVzB36tDyxs3LhdkZjyNxfVivV7WmluU7FdDsop74/CsrZrK9LSednsGtF5c6/VJ0uXkVZ9REoq+/60PXxQWtvQGvdoLUQDf5vR4PNQTTY' \
			b'3HYnwN+e4t4LpS0Ke0tV7QGU1N62koYHJb0hJb0WE8KNKOktmrGgpLfYBbhnStqfrJJet83rRgxeVCb33Bhws8YtHDSt0jy0PYABgGerd1Xb7k8qnEeUkfwc5I5mLXspHV43K3murMb68HNXiyqrkqGwP6jqcnEY3C6vvFKmSX/T2pkD6W9a7HZNSwpmjFX8' \
			b'k+msr3ybVVkdHhHURWN3NF49aOxhNRb1Ld+uoLHxDmlshMbGZY3tu4vbX4513caAcIB+AMv5uLustTZe5+Q/Lwu9uqGf6Li4bb276eV/e+nbyejadRuZrqBj6vZ17DaWmW5apu2lM8PNwwadMzesc5zhJVSOo12H1rm9lI4XRK54WcCGVtarR7LRy1q6G/kp' \
			b'bk0yfqjxNnX+iurxxMdDbbdPbdf92T8iwIqWmQct29KuulNoVJ24Y1Qz94h33a7pxqXrH62i6Jx90LktOudPQud8J4SejM657kLJzj8rW5tYHRyLmydIjKiF7MQW9dDSH/SybRw/dryXRvLkyz4zLweZXdmnayczKtyIJn3iUjKyDfESmiRFfMl5kAPMduyu' \
			b'LpyoWzczGlRquYz3KuCda5qbLNamSFl6l6wZLtPRubFCTCVIsDbAdaRRmyB6kHmRCcmj74FrOQjV1UkJxvscuy60QfhulJiISURUsT4cILZuU6fwZys5CUjJUUK8xVg3G4op3dFuX7Fu6byIyHdpYy0fYCEmNPntUbqyVTc72VSgXfrOisH7vWwOJLZX7NBi' \
			b'jlf6UBRRZbrbn2RrtmVLZb1PzqYb//Hk9YY/yV02iCu9jQA3z73aQoflXoed/PEwvnm3zbsQ5HYiCHvK9yWLGufZv9zt2fTdCWV+D8qw230v+tL+b5u3pxG9odv8l7toW0KMOlDMg5xd7W+Wi8gd0Xi1PyE+3gLxfXflP6G9vwTtLs6Sv96TBY6wt+vnfLkn' \
			b'vxBPmMWv4HrxuTrD6y1Myzz6RsY5Ag+B8HAVN5vInCf4V8fBv+lu3IF/Pea/PVwkyQK/z7UoEWl++HQQW84FmZ4F0orJdMMpH3KiRy2yfFJH3Ca60N2asxjv25E37zmfjwKZm+PQOW5rbtiBf7uTzu0gi1rVFuUyVq4lxeI5nMqFfA35eUfHYyfE4VHTtoC2' \
			b'n8mxdRCgOw0B+u7IHKTnT0N6oTsyB+mF05Be7I7MQXrxJKTH80fH5SC9/jDS26GbcgAZ2u7qjqdVx176qqliCmXS8b/pjt+lhOq7RYfT5nYJueh4WnPPOBDuZFRxCsLlmeKjdpDtrY9YLiVb2x23g2wnI5OTkK3rjttBtruNeo5NtqE7bgfZ7jYgOuJZDDbL' \
			b'nYaDwH2yRLPxmUaqqfoI8qtAPJ0BQ0SSGAdyfP5UjHyttjchGm8iUKW0IHfFhvALNlGKfZKXGWTjo09WID6ByPLYhMUa2BBO8fjQPi6SCJr4IJi6yKloeK7YlKMFlEvWHTUJyYXIoW1XO+XQyvMBCTYWK7zY3tjuFjBM5+3nKojhK1CM78//H/nTN4s='

	_PARSER_TOP = 'expr'

	_GREEK      = r'\\alpha|\\beta|\\gamma|\\delta|\\epsilon|\\zeta|\\eta|\\theta|\\iota|\\kappa|\\lambda|\\mu|\\nu|\\xi|\\omnicron|\\rho|' \
			r'\\sigma|\\tau|\\upsilon|\\phi|\\chi|\\psi|\\omega|\\Gamma|\\Delta|\\Theta|\\Lambda|\\Upsilon|\\Xi|\\Phi|\\Pi|\\Psi|\\Sigma|\\Omega'

	_SPECIAL    =  r'\\partial|\\pi|\\infty'
	_CHAR       = fr'[a-zA-Z]'
	_PYVAR      = '|'.join (reversed (sorted (AST.Var.PY)))
	_TEXTVAR    =  r'\\text\s*\{\s*(' + _PYVAR + r')\s*\}'
	_ONEVAR     = fr'{_CHAR}|{_GREEK}'
	_DSONEVARSP = fr'(?:(\d)|({_PYVAR})|({_CHAR}|{_GREEK}|{_SPECIAL})|{_TEXTVAR})'
	_STR        =  r'\'(?:\\.|[^\'])*\'|"(?:\\.|[^"])*["]'

	_FUNCPYONLY = '|'.join (reversed (sorted (AST.Func.PY_ONLY)))
	_FUNCPYTEX  = '|'.join (reversed (sorted (AST.Func.PY_AND_TEX)))

	TOKENS      = OrderedDict ([ # order matters
		('IGNORE_CURLY',  r'\\underline|\\mathcal|\\mathbb|\\mathfrak|\\mathsf|\\mathbf|\\textbf'),
		('TRIGH',         r'\\?(?:(a)(?:rc)?)?((?:sin|cos|tan|csc|sec|cot)h?)|\\operatorname\s*\{(sech|csch)\s*\}'),
		('FUNC',         fr'({_FUNCPYONLY})|\\?({_FUNCPYTEX})|\$({_CHAR}\w*)|\\operatorname\s*\{{\s*({_CHAR}(?:\w|\\_)*)\s*\}}'),
		('SQRT',          r'\\?sqrt'),
		('LOG',           r'\\?log'),
		('LIM',           r'\\lim'),
		('SUM',           r'\\sum'),
		('INT',           r'\\int(?:\s*\\limits)?'),
		('LEFT',          r'\\left'),
		('RIGHT',         r'\\right'),
		('CDOT',          r'\\cdot'),
		('TO',            r'\\to'),
		('BEG_MATRIX',    r'\\begin\s*\{\s*matrix\s*\}'),
		('END_MATRIX',    r'\\end\s*\{\s*matrix\s*\}'),
		('BEG_BMATRIX',   r'\\begin\s*\{\s*bmatrix\s*\}'),
		('END_BMATRIX',   r'\\end\s*\{\s*bmatrix\s*\}'),
		('BEG_VMATRIX',   r'\\begin\s*\{\s*vmatrix\s*\}'),
		('END_VMATRIX',   r'\\end\s*\{\s*vmatrix\s*\}'),
		('BEG_PMATRIX',   r'\\begin\s*\{\s*pmatrix\s*\}'),
		('END_PMATRIX',   r'\\end\s*\{\s*pmatrix\s*\}'),
		('FRAC2',        fr'\\frac\s*{_DSONEVARSP}\s*{_DSONEVARSP}'),
		('FRAC1',        fr'\\frac\s*{_DSONEVARSP}'),
		('FRAC',          r'\\frac'),
		('NUM',           r'(?:(\d*\.\d+)|(\d+)\.?)([eE][+-]?\d+)?'),
		('VAR',          fr"({_PYVAR})|(d|\\partial\s?)?({_ONEVAR})|{_SPECIAL}|{_TEXTVAR}"),
		('STR',          fr"(?<!\d|{_CHAR}|['}}])({_STR})|\\text\s*\{{\s*({_STR})\s*\}}"),
		('SUB1',         fr'_{_DSONEVARSP}'),
		('SUB',           r'_'),
		('CARET1',       fr'\^{_DSONEVARSP}'),
		('CARET',         r'\^'),
		('DBLSTAR',       r'\*\*'),
		('PRIMES',        r"'+"),
		('PARENL',        r'\('),
		('PARENR',        r'\)'),
		('CURLYL',        r'{'),
		('CURLYR',        r'}'),
		('BRACKETL',      r'\['),
		('BRACKETR',      r'\]'),
		('BAR',           r'\|'),
		('PLUS',          r'\+'),
		('MINUS',         r'-'),
		('STAR',          r'\*'),
		('INEQ',          r'==|!=|\\neq?|<=|\\le|<|>=|\\ge|>'),
		('EQ',            r'='),
		('DIVIDE',        r'/'),
		('EXCL',          r'!'),
		('AMP',           r'&'),
		('DBLSLASH',      r'\\\\'),
		('COMMA',         r','),
		('ignore',        r'\\,|\\:|\\?\s+'),
	])

	_FUNC_AST_REMAP = {
		'Abs'       : lambda expr: _expr_func (1, '|', expr),
		'Derivative': lambda expr: _expr_func_remap (remap_func_diff, expr),
		'Integral'  : lambda expr: _expr_func_remap (remap_func_intg, expr),
		'Limit'     : lambda expr: _expr_func_remap (remap_func_lim, expr),
		'Sum'       : lambda expr: _expr_func_remap (remap_func_sum, expr),
		'abs'       : lambda expr: _expr_func (1, '|', expr),
		'exp'       : lambda expr: _expr_func (2, '^', ('@', 'e'), expr),
		'factorial' : lambda expr: _expr_func (1, '!', expr),
		'ln'        : lambda expr: _expr_func (1, 'log', expr),
	}

	def expr_comma_1    (self, expr_comma, COMMA, expr):                     return AST.flatcat (',', expr_comma, expr)
	def expr_comma_2    (self, expr_comma, COMMA):                           return expr_comma if expr_comma.is_comma else AST (',', (expr_comma,))
	def expr_comma_3    (self, expr):                                        return expr

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

	def expr_lim_1      (self, LIM, SUB, CURLYL, expr_var, TO, expr, CURLYR, expr_neg):                           return AST ('lim', expr_neg, expr_var, expr)
	def expr_lim_2      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, PLUS, CURLYR, expr_neg):   return AST ('lim', expr_neg, expr_var, expr, '+')
	def expr_lim_3      (self, LIM, SUB, CURLYL, expr_var, TO, expr, caret_or_dblstar, MINUS, CURLYR, expr_neg):  return AST ('lim', expr_neg, expr_var, expr, '-')
	def expr_lim_6      (self, expr_sum):                                                                         return expr_sum

	def expr_sum_1      (self, SUM, SUB, CURLYL, expr_var, EQ, expr, CURLYR, expr_super, expr_neg):               return AST ('sum', expr_neg, expr_var, expr, expr_super)
	def expr_sum_2      (self, expr_func):                                                                        return expr_func

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
		func  = FUNC.grp [0] or FUNC.grp [1] or FUNC.grp [2] or FUNC.grp [3].replace ('\\_', '_') or FUNC.text
		args  = expr_func_neg.strip_paren ()
		remap = self._FUNC_AST_REMAP.get (func)

		return remap (args) if remap else _expr_func (2, 'func', func, args)

	def expr_func_8     (self, expr_fact):                                   return expr_fact

	def expr_func_neg_1 (self, expr_func):                                   return expr_func
	def expr_func_neg_2 (self, MINUS, expr_func):                            return expr_func.neg (stack = True)

	def expr_fact_1     (self, expr_fact, EXCL):                             return AST ('!', expr_fact)
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

	def expr_frac_1     (self, FRAC, expr_mat1, expr_mat2):                  return AST ('/', expr_mat1, expr_mat2)
	def expr_frac_2     (self, FRAC1, expr_mat):                             return AST ('/', _ast_from_tok_digit_or_var (FRAC1), expr_mat)
	def expr_frac_3     (self, FRAC2):                                       return AST ('/', _ast_from_tok_digit_or_var (FRAC2), _ast_from_tok_digit_or_var (FRAC2, 4))
	def expr_frac_4     (self, expr_mat):                                    return expr_mat

	def expr_mat_1      (self, LEFT, BRACKETL, BEG_MATRIX, expr_mat_rows, END_MATRIX, RIGHT, BRACKETR):  return AST ('mat', expr_mat_rows)
	def expr_mat_2      (self, BEG_MATRIX, expr_mat_rows, END_MATRIX):                                   return AST ('mat', expr_mat_rows)
	def expr_mat_3      (self, BEG_BMATRIX, expr_mat_rows, END_BMATRIX):                                 return AST ('mat', expr_mat_rows)
	def expr_mat_4      (self, BEG_VMATRIX, expr_mat_rows, END_VMATRIX):                                 return AST ('mat', expr_mat_rows)
	def expr_mat_5      (self, BEG_PMATRIX, expr_mat_rows, END_PMATRIX):                                 return AST ('mat', expr_mat_rows)
	def expr_mat_6      (self, expr_curly):                                                              return expr_curly

	def expr_mat_rows_1 (self, expr_mat_rows, DBLSLASH, expr_mat_row):       return expr_mat_rows + (expr_mat_row,)
	def expr_mat_rows_2 (self, expr_mat_rows, DBLSLASH):                     return expr_mat_rows
	def expr_mat_rows_3 (self, expr_mat_row):                                return (expr_mat_row,)
	def expr_mat_row_1  (self, expr_mat_row, AMP, expr):                     return expr_mat_row + (expr,)
	def expr_mat_row_2  (self, expr):                                        return (expr,)

	def expr_curly_1    (self, LEFT, CURLYL, expr_comma, RIGHT, CURLYR):     return _expr_curly (expr_comma)
	def expr_curly_2    (self, CURLYL, expr_comma, CURLYR):                  return _expr_curly (expr_comma)
	def expr_curly_3    (self, expr_bracket):                                return expr_bracket

	def expr_bracket_1  (self, LEFT, BRACKETL, expr_comma, RIGHT, BRACKETR): return AST ('[', expr_comma.commas if expr_comma.is_comma else (expr_comma,))
	def expr_bracket_2  (self, BRACKETL, expr_comma, BRACKETR):              return AST ('[', expr_comma.commas if expr_comma.is_comma else (expr_comma,))
	def expr_bracket_3  (self, expr_term):                                   return expr_term

	def expr_term_1     (self, STR):                                         return AST ('"', py_ast.literal_eval (STR.grp [0] or STR.grp [1]))
	def expr_term_2     (self, SUB):                                         return AST ('@', '_')
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

	def subvar_1        (self, SUB, CURLYL, expr_var, CURLYR):               return f'_{expr_var.var}' if expr_var.var and expr_var.is_single_var else f'_{{{expr_var.var}}}'
	def subvar_2        (self, SUB, CURLYL, NUM, CURLYR):                    return f'_{{{NUM.text}}}'
	def subvar_3        (self, SUB, CURLYL, NUM, subvar, CURLYR):            return f'_{{{NUM.text}{subvar}}}'
	def subvar_4        (self, SUB1):                                        return f'_{AST.Var.SHORT2LONG.get (SUB1.grp [1] or SUB1.grp [3], SUB1.text [1:])}'

	def expr_sub_1      (self, SUB, expr_frac):                              return expr_frac
	def expr_sub_2      (self, SUB1):                                        return _ast_from_tok_digit_or_var (SUB1)

	def expr_super_1    (self, DBLSTAR, expr_func):                          return expr_func
	def expr_super_2    (self, DBLSTAR, MINUS, expr_func):                   return expr_func.neg (stack = True)
	def expr_super_3    (self, CARET, expr_frac):                            return expr_frac
	def expr_super_4    (self, CARET1):                                      return _ast_from_tok_digit_or_var (CARET1)

	def caret_or_dblstar_1 (self, DBLSTAR):                                  return '**'
	def caret_or_dblstar_2 (self, CARET):                                    return '^'

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
			self.tokens.insert (self.tokidx, lalr1.Token (self._AUTOCOMPLETE_SUBSTITUTE.get (sym, 'VAR'), '', self.tok.pos, ('', '', '', '')))
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
		self.stack [-1] = (s [0], s [1], AST ('*', (s [2], AST.VarNull)))
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

		# if rule [0] == 'expr_comma' and pos == 1: # force (expr . COMMA) to (expr .)
		# 	rule = self.rules [self.strules [self.stidx] [1] [0]]

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

if __name__ == '__main__':
	p = Parser ()
	a = p.parse ('{')
	print (a)
