ROOT = $(shell dune exec ./get_cwd.exe)

PROOFS = $(wildcard proofs/*.proof)

all: build
	"$(ROOT)/proving.exe"

build:
	dune build
test:
	$(foreach p, $(PROOFS), cat $(p) | dune exec ./proving.exe)
