ROOT = $(shell dune exec ./get_cwd.exe)

PROOFS = $(wildcard proofs/*.proof)

all: build
	"$(ROOT)/proving.exe"

build:
	dune build

test: build
	@for p in $(PROOFS); do \
	  echo ">> Running on $$p"; \
	  cat "$$p" | "$(ROOT)/proving.exe"; \
	done
