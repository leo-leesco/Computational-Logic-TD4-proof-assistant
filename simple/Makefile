ROOT = $(shell dune exec ./get_cwd.exe)

PROOFS = $(wildcard proofs/*.proof)

all: build
	"$(ROOT)/proving.exe"

build:
	dune build

test: build
	$(foreach p, $(PROOFS), cat $(p) | "$(ROOT)/proving.exe")
