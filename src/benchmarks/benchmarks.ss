(import (chezscheme) (aikanren) (benchmark-runner) (utils) (prefix (quine) quine-))


#;
  (bench "absento - tree2" 1
         ;; Tests that the solver can simplify absento into single variable constraints rather than entangling them in large disjunctions.
         (run* (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 x78 x79 x80 x81 x82 x83 x84 x85 x86 x87 x88 x89 x90 x91 x92 x93 x94 x95 x96 x97 x98 x99)
           (absento 100 x1) (absento 101 x1) (== x1 (cons x2 x3)) (== x2 (cons x4 x5)) (== x3 (cons x6 x7)) (== x4 (cons x8 x9)) (== x5 (cons x10 x11)) (== x6 (cons x12 x13)) (== x7 (cons x14 x15)) (== x8 (cons x16 x17))))


(include "src/benchmarks/core-benchmarks.ss")
(include "src/benchmarks/disequality-benchmarks.ss")
(include "src/benchmarks/absento-benchmarks.ss")
(include "src/benchmarks/relational-interpreter-benchmarks.ss")


