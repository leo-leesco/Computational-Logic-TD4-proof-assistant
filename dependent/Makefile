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
# 	- lib=<list of library folders, stored inside the subfolder `lib/` >
# 	- clean=1 : the proof you are trying to make is overwritten
#	- library=<folder>/<filename> : you are defining a library file, to be stored in `lib/<folder>/<filename>`
%:
ifdef clean
	rm -f proofs/$@
endif
	touch proofs/$@
ifdef lib
	echo (echo "#start
	hide";
	cat lib/$(lib)/* proofs/$@;
	echo "show
	#end"
	) - | "$(ROOT)/proving.exe" proofs/$@
else
	cat proofs/$@ - | "$(ROOT)/proving.exe" proofs/$@
endif
	sed -i '' "/#start/,/#end/d" proofs/$@
	sed -i '' "/exit/d" proofs/$@
