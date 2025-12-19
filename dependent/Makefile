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

# you can provide various arguments :
# 	- clean=1 : the proof you are trying to make is overwritten
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
