SHELL := /bin/bash
.PHONY: default clean profile bench repl rebench doc test debug

SRC = $(wildcard src/mk/*.ss)
PRE = $(SRC:src/mk/%=build/preprocessed/%)
PRO = $(SRC:src/mk/%=build/profiled/%)
OBJ = $(PRE:build/preprocessed/%.ss=build/object/%.so)
OBJSRC = $(OBJ:.so=.ss)

default: lib/aikanren.wpo lib/aikanren.so

clean:
	rm -rf lib build profile benchmarks

lib/aikanren.wpo lib/aikanren.so &: $(OBJ)
# Source file directory must come before object directory, but need both for wpo.
	mkdir -p lib
	echo '(generate-wpo-files #t) (compile-whole-library "build/object/aikanren.wpo" "lib/aikanren.so")' | scheme -q --libdirs build/object --compile-imported-libraries --optimize-level 3

build/preprocessed/%.ss: src/mk/%.ss
# Strip out the assertions and generate new source files as a preprocessing step. Assertions are assumed to be on their own lines.
	mkdir -p build/preprocessed

build/object/%.so: $(OBJSRC)
# Compile each library separately before compiling them all together as a whole library object file.
	echo '(generate-wpo-files #t) (compile-library "'$(@:build/object/%.so=build/preprocessed/%.ss)'" "'$@'")' | scheme -q --libdirs build/object --compile-imported-libraries --optimize-level 3
build/object/%.ss: build/preprocessed/%.ss
# Chez likes to have src and obj in same directory, so we need to copy a set of src files specially for the compiler so it doesn't mix up the performance instrumented and non-performance-instrumented object files.
	mkdir -p build/object
	cp $< $@

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
benchmarks/bench: build/benchmarks.so
	mkdir -p benchmarks
	if [[ -f benchmarks/bench ]]; then mv benchmarks/bench benchmarks/bench-$$(ls -1 benchmarks | wc -l); fi
	scheme --program build/benchmarks.so | sed -E 's/#<time-duration ([[:digit:].]+)>/\1/g' | LC_COLLATE=C sort > benchmarks/bench
build/benchmarks.so: lib/aikanren.wpo $(wildcard src/benchmarks/*) $(OBJ)
	mkdir -p build/benchmarks
	cp -fr src/benchmarks/* src/examples/* build/benchmarks
	echo '(generate-wpo-files #t) (compile-program "build/benchmarks/benchmarks.ss")' | scheme -q --libdirs 'build/object:build/benchmarks' --compile-imported-libraries --optimize-level 3
	echo '(compile-whole-program "build/benchmarks/benchmarks.wpo" "build/benchmarks.so")' | scheme -q --libdirs 'build/object:build/benchmarks' --compile-imported-libraries --optimize-level 3

repl: # Boot up a REPL preloaded with aiKanren
	REPLBOOT=$$(mktemp); \
	trap "rm -f $$REPLBOOT" EXIT; \
	echo '(import (aikanren))' > "$$REPLBOOT"; \
	scheme --libdirs src/mk "$$REPLBOOT"


doc:
	sed -i -n '1,/^## Documentation/ p' README.md
	echo '## Not Yet Implemented' >> README.md
	grep -nr --exclude=utils.ss -e '(nyi' src | sed -E 's|^([^:]+):([^:]+):.*\(nyi([^)]*)\).*|- \3 ([\1:\2](https://github.com/emdonahue/aiKanren/blob/main/\1#L\2))|g' >> README.md
	echo '## TODO' >> README.md
	grep -nr -e 'TODO' src | sed -E 's|^([^:]+):([^:]+):.*TODO (.*)|- \3 ([\1:\2](https://github.com/emdonahue/aiKanren/blob/main/\1#L\2))|' >> README.md

test:
	@TESTSUITE=$$(mktemp); \
	trap "rm -f $$TESTSUITE" EXIT; \
	echo '(import (chezscheme) (test-runner) (all-tests)) (run-all-tests) (tmessage)' > "$$TESTSUITE"; \
	scheme --libdirs src/mk:src/tests:src/benchmarks:src/examples --script "$$TESTSUITE" || true

debug:
	@TESTSUITE=$$(mktemp); \
	trap "rm -f $$TESTSUITE" EXIT; \
	echo '(import (chezscheme) (test-runner) (all-tests)) (run-all-tests) (tmessage)' > "$$TESTSUITE"; \
	scheme --libdirs src/mk:src/tests:src/benchmarks:src/examples --debug-on-exception --script "$$TESTSUITE" || true

