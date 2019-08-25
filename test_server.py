#!/usr/bin/env python
# python 3.6+

# Testing of server state machine (vars, env, lambdas).

import os
import sys
import time

_OLDARGV = sys.argv [1:]
sys.argv = [os.path.abspath ('server.py'), '--child']

import server

if __name__ == '__main__':
	httpd = server.start_server ()

	while 1:
		time.sleep (1)