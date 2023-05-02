#!/usr/bin/env -S scheme --libdirs src:. --script
(import (chezscheme) (vkanren) (sbral) (testrunner))
;(load "vkanren.ss")
(load "tests/test-sbral.ss")

(display "Testing Complete\n")
