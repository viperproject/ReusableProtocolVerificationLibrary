#!/bin/bash -e

awk 'fname != FILENAME { printf "%s: %s\n", fname, count; fname = FILENAME; count = 0 } /.*\/\*@.*@\*\/.*/ { count++; total++ } END { print total }' $(find . -name '*.go' -or -name '*.gobra')
