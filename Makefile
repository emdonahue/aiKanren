.PHONY: default clean

SRC = $(wildcard src/*.ss)
PREPROCESSED = $(subst src/,object/,$(SRC))
OBJ = $(subst .ss,.so,$(PREPROCESSED))

default: lib/aikanren.wpo lib/aikanren.so

clean:
	rm -rf lib object

lib/aikanren.wpo lib/aikanren.so: $(OBJ)
	mkdir -p lib
#	echo '(generate-wpo-files #t) (compile-whole-library "object/aikanren.wpo" "lib/aikanren.so")' | scheme --libdirs object --optimize-level 3 -q

object/%.ss: src/%.ss
	mkdir -p object
	sed '/(assert /d' $< > $@

object/%.so: $(PREPROCESSED)
	echo '(generate-wpo-files #t) (compile-library "'$(subst .ss,.so,$@)'" "'$@'")' | scheme --libdirs object --optimize-level 3 -q

#object/aikanren.ss: src/aikanren.ss
#	mkdir -p object
#	find src -type f -execdir sed -ne '/(assert /d' -e 'w ../object/'{} {} \;
#	find src -execdir sed '/(assert /d' {} > ../object \;
