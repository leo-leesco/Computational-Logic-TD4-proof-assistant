ROOT = $(shell dune exec ./get_cwd.exe)

PROOFS = $(wildcard proofs/*)

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
ifdef clean
	rm -f proofs/$@
endif
	touch proofs/$@
ifdef lib
	cat lib/$(lib)/* proofs/$@ - | "$(ROOT)/proving.exe" proofs/$@
else
	cat proofs/$@ - | "$(ROOT)/proving.exe" proofs/$@
endif
	sed -i '' "/hide/,/show/d" proofs/$@
