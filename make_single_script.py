#!/usr/bin/env python
# python 3.6+

# Collect all source and data files into single sympad.py script file.

_PY_FILES    = ('lalr1.py', 'sast.py', 'sparser.py', 'sym.py', 'server.py')
_OTHER_FILES = ('style.css', 'script.js', 'index.html')

_HEADER = '''
#!/usr/bin/env python
# python 3.6+

_RUNNING_AS_SINGLE_SCRIPT = True

'''.lstrip ()

if __name__ == '__main__':
	fdout = open ('sympad.py', 'w')

	fdout.write (_HEADER)

	for fnm in _PY_FILES:
		for line in open (fnm):
			if not line.rstrip ().endswith ('# AUTO_REMOVE_IN_SINGLE_SCRIPT'):
				fdout.write (line)

	fdout.write ('\n_FILES = {\n')

	for fnm in _OTHER_FILES:
		fdout.write (f'''\n\t'{fnm}': # {fnm}\n\n"""''')

		for line in open (fnm):
			fdout.write (line)

		fdout.write ('""",\n')

	fdout.write ('}\n')
