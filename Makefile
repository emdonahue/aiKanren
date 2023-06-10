.PHONY: default clean

SRC = $(wildcard src/*.ss)
PREPROCESSED = $(subst src/,object/,$(SRC))
OBJ = $(subst .ss,.so,$(PREPROCESSED))

default: lib/aikanren.wpo lib/aikanren.so

clean:
	rm -rf lib object

lib/aikanren.wpo lib/aikanren.so &: $(OBJ)
	mkdir -p lib
	echo '(compile-imported-libraries #t) (generate-wpo-files #t) (compile-whole-library "object/aikanren.wpo" "lib/aikanren.so")' | scheme -q --libdirs object --optimize-level 3

object/%.ss: src/%.ss
	mkdir -p object
	sed '/(assert /d' $< > $@

object/%.so: $(PREPROCESSED)
	echo '(compile-imported-libraries #t) (generate-wpo-files #t) (compile-library "'$(subst .so,.ss,$@)'" "'$@'")' | scheme -q --libdirs object --optimize-level 3
