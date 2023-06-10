.PHONY: all clean

all: lib/aikanren.wpo lib/aikanren.so
clean:
	rm -f lib/aikanren.wpo lib/aikanren.so
	rmdir lib
	rm -f precompilation/*.ss
	rmdir precompilation
lib/aikanren.wpo lib/aikanren.so: precompilation/aikanren.ss
	mkdir -p lib
	echo '(generate-wpo-files #t) (compile-library "precompilation/aikanren.ss" "lib/aikanren.so")' | scheme --libdirs precompilation --optimize-level 3 -q 
precompilation/aikanren.ss: src/aikanren.ss
	mkdir -p precompilation
	find src -type f -execdir sed -ne '/(assert /d' -e 'w ../precompilation/'{} {} \;
	find src -execdir sed '/(assert /d' {} > ../precompilation \;
