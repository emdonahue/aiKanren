(import (chezscheme) (aikanren) (benchmark-runner))

#;
(run* (x)
	   (let loop ([n 5]
		      [latest x])
	     (if (fx= n 0) (let lookup ([n 200])
			     (if (fx= n 0) (== 1 1) (conde [(== latest 1)] [(lookup (fx1- n))])))
		 (fresh (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 x78 x79 x80 x81 x82 x83 x84 x85 x86 x87 x88 x89 x90 x91 x92 x93 x94 x95 x96 x97 x98 x99 x100)
		   (conde [(== latest x1) (== x1 x2) (== x2 x3) (== x3 x4) (== x4 x5) (== x5 x6) (== x6 x7) (== x7 x8) (== x8 x9) (== x9 x10) (== x10 x11) (== x11 x12) (== x12 x13) (== x13 x14) (== x14 x15) (== x15 x16) (== x16 x17) (== x17 x18) (== x18 x19) (== x19 x20) (== x20 x21) (== x21 x22) (== x22 x23) (== x23 x24) (== x24 x25) (== x25 x26) (== x26 x27) (== x27 x28) (== x28 x29) (== x29 x30) (== x30 x31) (== x31 x32) (== x32 x33) (== x33 x34) (== x34 x35) (== x35 x36) (== x36 x37) (== x37 x38) (== x38 x39) (== x39 x40) (== x40 x41) (== x41 x42) (== x42 x43) (== x43 x44) (== x44 x45) (== x45 x46) (== x46 x47) (== x47 x48) (== x48 x49) (== x49 x50) (== x50 x51) (== x51 x52) (== x52 x53) (== x53 x54) (== x54 x55) (== x55 x56) (== x56 x57) (== x57 x58) (== x58 x59) (== x59 x60) (== x60 x61) (== x61 x62) (== x62 x63) (== x63 x64) (== x64 x65) (== x65 x66) (== x66 x67) (== x67 x68) (== x68 x69) (== x69 x70) (== x70 x71) (== x71 x72) (== x72 x73) (== x73 x74) (== x74 x75) (== x75 x76) (== x76 x77) (== x77 x78) (== x78 x79) (== x79 x80) (== x80 x81) (== x81 x82) (== x82 x83) (== x83 x84) (== x84 x85) (== x85 x86) (== x86 x87) (== x87 x88) (== x88 x89) (== x89 x90) (== x90 x91) (== x91 x92) (== x92 x93) (== x93 x94) (== x94 x95) (== x95 x96) (== x96 x97) (== x97 x98) (== x98 x99) (== x99 x100) (loop (fx- n 1) x100)]
			  [(== 1 2)])))))

(include "src/benchmarks/core-benchmarks.ss")
(include "src/benchmarks/disequality-benchmarks.ss")
(include "src/benchmarks/absento-benchmarks.ss")

