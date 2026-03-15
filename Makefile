run: build/
	cp src/* build/ && cd build && dafny run main.dfy

build/:
	mkdir -p build

clean:
	rm -rf build/*

.PHONY: run clean