ROOT = $(shell dune exec ./get_cwd.exe)

TESTS = $(wildcard tests/*)
DEPS = $(wildcard *.opam.locked)

all: build
	"$(ROOT)/proving.exe"

build:
	dune build

install:
	opam switch create . ocaml-base-compiler.4.14.2

install_test:
	@for deps in $(DEPS); do \
		opam install ./$$deps --deps-only; \
	done

test: build
	@for p in $(TESTS); do \
		echo; \
	  echo ">>>>>>>>>> Running on $$p <<<<<<<<<<"; \
	  cat "$$p" | "$(ROOT)/proving.exe"; \
	done

# you can provide various arguments :
# 	- clean=1 : the proof you are trying to make is overwritten
# 	- lib=<libraries> : scripts in <libraries> are imported
%:
ifdef clean
	rm -f proofs/$@
endif
	touch proofs/$@
ifdef lib
	cat lib/start $(lib) lib/end proofs/$@ - | "$(ROOT)/proving.exe" proofs/$@
else
	cat proofs/$@ - | "$(ROOT)/proving.exe" proofs/$@
endif
	sed -i '' "/# start/,/# end/d" proofs/$@
	sed -i '' "/env/d" proofs/$@
	sed -i '' "/context/d" proofs/$@
	sed -i '' "/exit/d" proofs/$@
