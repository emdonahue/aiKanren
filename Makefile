SHELL := /bin/bash
.PHONY: default clean profile bench repl rebench doc test debug

SRC = $(wildcard src/mk/*.ss)
PRE = $(SRC:src/mk/%=build/preprocessed/%)
PRO = $(SRC:src/mk/%=build/profiled/%)
OBJ = $(SRC:src/mk/%.ss=build/%.so)
OBJSRC = $(OBJ:.so=.ss)

default: lib/aikanren.wpo lib/aikanren.so

clean:
	rm -rf lib build profile

lib/aikanren.wpo lib/aikanren.so &: $(SRC)
# Source file directory must come before object directory, but need both for wpo.
	mkdir -p lib build/optimized
	cp -f src/mk/* build/optimized
	echo '(generate-wpo-files #t) (compile-library "build/optimized/aikanren.ss")' | scheme -q --libdirs build/optimized --compile-imported-libraries --optimize-level 3
	echo '(generate-wpo-files #t) (compile-whole-library "build/optimized/aikanren.wpo" "lib/aikanren.so")' | scheme -q --libdirs build/optimized --compile-imported-libraries --optimize-level 3

profile: profile/profile.html
# Builds an html heatmap of function calls for optimization purposes.
build/profiled/%.ss: build/preprocessed/%.ss
	mkdir -p build/profiled
	cp $< $@
profile/profile.html: $(PRE)
	mkdir -p profile
	echo "(compile-profile 'source) "'(import (chezscheme) (aikanren)) (load "src/benchmarks/benchmarks.ss") (profile-dump-html "profile/")' | scheme -q --libdirs 'build/preprocessed:src/benchmarks' --optimize-level 3

bench: benchmarks/bench
# Builds a set of benchmarks to test performance improvements.
	@if [[ 1 < $$(ls -1 benchmarks | wc -l) ]]; then BENCHMARK=$$(ls -1v benchmarks | tail -n1); LC_COLLATE=C join -e0 -oauto -a1 -a2 -t$$'\t' benchmarks/$$BENCHMARK benchmarks/bench | awk -vOFS='\t' -F'\t' -vBENCHMARK=$$BENCHMARK 'BEGIN {print "benchmark",BENCHMARK,"current","% improvement","% > prev","slower?"} {if ($$2==0||$$3==0) {$$4="-"; $$5="-"} else {$$4=-100*($$3-$$2)/$$2" %"; $$5=$$2/$$3; $$5=($$2/$$3-1)*100; if($$5<0) $$6="x"} print}' | column -ts$$'\t'; else cat benchmarks/bench | column -ts$$'\t'; fi
rebench:
# If you don't believe the numbers bench gave you, re-roll until your optimization wins!
	rm -f benchmarks/bench
	make bench
benchtest: build/benchmarks.so
	scheme --program build/benchmarks.so
benchmarks/bench: build/benchmarks.so
	mkdir -p benchmarks
	if [[ -f benchmarks/bench ]]; then mv benchmarks/bench benchmarks/bench-$$(ls -1 benchmarks | wc -l); fi
	scheme --program build/benchmarks.so | sed -E 's/#<time-duration ([[:digit:].]+)>/\1/g' | LC_COLLATE=C sort > benchmarks/bench
build/benchmarks.so: lib/aikanren.wpo $(wildcard src/benchmarks/*) $(wildcard src/mk/*)
	mkdir -p build/benchmarks
	cp -f src/benchmarks/* src/examples/* build/benchmarks
	echo '(generate-wpo-files #t) (compile-program "build/benchmarks/benchmarks.ss")' | scheme -q --libdirs 'build/optimized:build/benchmarks' --compile-imported-libraries --optimize-level 3
	echo '(compile-whole-program "build/benchmarks/benchmarks.wpo" "build/benchmarks.so")' | scheme -q --libdirs 'build/optimized:build/benchmarks' --compile-imported-libraries --optimize-level 3

repl: # Boot up a REPL preloaded with aiKanren
	REPLBOOT=$$(mktemp); \
	trap "rm -f $$REPLBOOT" EXIT; \
	echo '(import (aikanren))' > "$$REPLBOOT"; \
	scheme --libdirs src/mk "$$REPLBOOT"


doc:
	echo '# Documentation' > DOCUMENTATION.md
	grep -E '; \w+$$' src/mk/aikanren.ss | while read -a fns; do \
		echo '-  ['$${fns[-1]}'](#'$${fns[-1]}')' >> DOCUMENTATION.md; \
		for f in $${fns[@]::$${#fns[@]}-2}; do \
			echo -e '\t- ['$$f'](#'$$f')' >> DOCUMENTATION.md; \
		done \
	done
	grep -E '; \w+$$' src/mk/aikanren.ss | while read -a fns; do \
		echo '## '$${fns[-1]} >> DOCUMENTATION.md; \
		for f in $${fns[@]::$${#fns[@]}-2}; do \
			echo -e '### '$$f'\n```scheme' >> DOCUMENTATION.md; \
			sed -En "\%define(-syntax)? \(?$$f[ )]%,\%^[^;]*$$% p" src/mk/* | grep -e 'define' -e ';' >> DOCUMENTATION.md; \
			echo '```' >> DOCUMENTATION.md; \
		done \
	done
	echo '# Not Yet Implemented' > TODO.md
	grep -nr --exclude=utils.ss -e '(nyi' src | sed -E 's|^([^:]+):([^:]+):.*\(nyi([^)]*)\).*|- \3 ([\1:\2](https://github.com/emdonahue/aiKanren/blob/main/\1#L\2))|g' >> TODO.md
	echo '# TODO' >> TODO.md
	grep -nr -e 'TODO' src | sed -E 's|^([^:]+):([^:]+):.*TODO (.*)|- \3 ([\1:\2](https://github.com/emdonahue/aiKanren/blob/main/\1#L\2))|' >> TODO.md

test:
	@scheme --compile-imported-libraries --libdirs src/mk:src/tests:src/benchmarks:src/examples --script src/tests/all-tests.ss

debug:
	@TESTSUITE=$$(mktemp); \
	trap "rm -f $$TESTSUITE" EXIT; \
	echo '(import (chezscheme) (test-runner) (all-tests)) (run-all-tests) (tmessage)' > "$$TESTSUITE"; \
	scheme --libdirs src/mk:src/tests:src/benchmarks:src/examples --debug-on-exception --import-notify --script "$$TESTSUITE" || true

