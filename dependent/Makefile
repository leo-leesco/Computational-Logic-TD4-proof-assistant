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

%:
	touch proofs/$@.proof
ifdef lib
	cat lib/$(lib)/* proofs/$@.proof - | "$(ROOT)/proving.exe" proofs/$@.proof
else
	cat proofs/$@.proof - | "$(ROOT)/proving.exe" proofs/$@.proof
endif
	sed -i '' "/hide/,/show/d" proofs/$@.proof
