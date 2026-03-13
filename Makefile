run:
	cp src/* build/ && cd build && dafny run main.dfy

clean:
	rm -rf build/*

.PHONY: run clean