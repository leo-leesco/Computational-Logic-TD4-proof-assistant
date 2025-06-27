all:
	dune exec ./proving.exe

PROOFS = $(wildcard proofs/*.proof)

test:
	$(foreach p, $(PROOFS), cat $(p) | dune exec ./prover.exe)
