#!/usr/bin/env -S scheme --optimize-level 3 --libdirs src:benchmarks:. --script
(compile-profile 'source)

(import (chezscheme) (aikanren))

(parameterize ([compile-profile 'source])
  
  
  (load "benchmarks/core-benchmarks.ss"))
(profile-dump-html "profiler/")

