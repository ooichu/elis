#!/bin/sh
gcc -Wall -Wextra -pedantic -std=c89 -DELIS_TESTBED -O3 -oelis src/elis.c
