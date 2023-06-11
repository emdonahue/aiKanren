SHELL := /bin/bash
.PHONY: default clean profile bench

SRC = $(wildcard src/aikanren/*.ss)
PRE = $(SRC:src/aikanren/%=build/preprocessed/%)
OBJ = $(PRE:build/preprocessed/%.ss=build/object/%.so)

default: lib/aikanren.wpo lib/aikanren.so

clean:
	rm -rf lib build profile benchmarks

lib/aikanren.wpo lib/aikanren.so &: $(OBJ)
# Object file directory must come before source directory, but need both for wpo.
	mkdir -p lib
	echo '(generate-wpo-files #t) (compile-whole-library "build/object/aikanren.wpo" "lib/aikanren.so")' | scheme -q --libdirs build/preprocessed:build/object --compile-imported-libraries --optimize-level 3

build/preprocessed/%.ss: src/aikanren/%.ss
# Strip out the assertions and generate new source files as a preprocessing step. Assertions are assumed to be on their own lines.
	mkdir -p build/preprocessed
	sed '/(assert /d' $< > $@

build/object/%.so: $(PRE)
# Compile each library separately before compiling them all together as a whole library object file.
	mkdir -p build/object
	echo '(generate-wpo-files #t) (compile-library "'$(@:build/object/%.so=build/preprocessed/%.ss)'" "'$@'")' | scheme -q --libdirs build/preprocessed --compile-imported-libraries --optimize-level 3

profile: profile/profile.html
profile/profile.html: $(PRE)
	mkdir -p profile
	echo "(compile-profile 'source) "'(import (chezscheme) (aikanren)) (load "src/benchmarks/core-benchmarks.ss") (profile-dump-html "profile/")' | scheme -q --libdirs 'build/preprocessed:src/benchmarks' --optimize-level 3

bench: benchmarks/bench
	cat benchmarks/bench
benchmarks/bench: lib/aikanren.so
	mkdir -p benchmarks
	if [[ -f benchmarks/bench ]]; then mv benchmarks/bench benchmarks/bench-$$(($(ls -1 marks | { cut -c7-; echo 0 } | sort -nr | head -n1) + 1)); fi
	echo '(import (chezscheme) (aikanren)) (include "src/benchmarks/core-benchmarks.ss")' | scheme -q --optimize-level 3 --libdirs 'lib:src/benchmarks' > benchmarks/bench
