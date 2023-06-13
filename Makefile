SHELL := /bin/bash
.PHONY: default clean profile bench repl rebench doc

SRC = $(wildcard src/aikanren/*.ss)
PRE = $(SRC:src/aikanren/%=build/preprocessed/%)
PRO = $(SRC:src/aikanren/%=build/profiled/%)
OBJ = $(PRE:build/preprocessed/%.ss=build/object/%.so)
OBJSRC = $(OBJ:.so=.ss)

default: lib/aikanren.wpo lib/aikanren.so

clean:
	rm -rf lib build profile benchmarks

lib/aikanren.wpo lib/aikanren.so &: $(OBJ)
# Source file directory must come before object directory, but need both for wpo.
	mkdir -p lib
	echo '(generate-wpo-files #t) (compile-whole-library "build/object/aikanren.wpo" "lib/aikanren.so")' | scheme -q --libdirs build/object --compile-imported-libraries --optimize-level 3 --import-notify

build/preprocessed/%.ss: src/aikanren/%.ss
# Strip out the assertions and generate new source files as a preprocessing step. Assertions are assumed to be on their own lines.
	mkdir -p build/preprocessed
	sed '/(assert /d' $< > $@

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
	echo "(compile-profile 'source) "'(import (chezscheme) (aikanren)) (load "src/benchmarks/core-benchmarks.ss") (profile-dump-html "profile/")' | scheme -q --libdirs 'build/preprocessed:src/benchmarks' --optimize-level 3

bench: benchmarks/bench
# Builds a set of benchmarks to test performance improvements.
	if [[ 1 < $$(ls -1 benchmarks | wc -l) ]]; then BENCHMARK=$$(ls -1 benchmarks | sort -nr | head -n1); join -t$$'\t' benchmarks/$$BENCHMARK benchmarks/bench | sed -E 's/#<time-duration ([[:digit:].]+)>/\1/g' | awk -vOFS='\t' -F'\t' -vBENCHMARK=$$BENCHMARK 'BEGIN {print "benchmark",BENCHMARK,"current","% improvement"} {$$4=-100*($$3-$$2)/$$2" %"; print}' | column -ts$$'\t'; else cat benchmarks/bench | sed -E 's/#<time-duration ([[:digit:].]+)>/\1/g' | column -ts$$'\t'; fi
rebench:
# If you don't believe the numbers bench gave you, re-roll until your optimization wins!
	rm -f benchmarks/bench
	make bench
benchmarks/bench: lib/aikanren.so $(wildcard src/benchmarks/*)
	mkdir -p benchmarks
	if [[ -f benchmarks/bench ]]; then mv benchmarks/bench benchmarks/bench-$$(ls -1 benchmarks | wc -l); fi
	echo '(import (chezscheme) (aikanren)) (include "src/benchmarks/core-benchmarks.ss")' | scheme -q --optimize-level 3 --libdirs 'lib:src/benchmarks' > benchmarks/bench

repl:
# Boot up a REPL preloaded with aiKanren
	REPLBOOT=$$(mktemp); \
	trap "rm -f $$REPLBOOT" EXIT; \
	echo '(import (aikanren))' > "$$REPLBOOT"; \
	scheme --libdirs src/aikanren "$$REPLBOOT"

doc:
	sed -i -n '1,/^## Documentation/ p' README.md
	echo '## TODO' >> README.md
	grep -nr 'TODO' * | sed -E 's/^([^:]+:[^:]+):.*TODO (.*)/- \2 (\1)/' >> README.md
