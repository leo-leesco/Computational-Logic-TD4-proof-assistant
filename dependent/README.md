# Dependent prover

The aim of this project is to provide a simple environment to define dependent functions, and prove various theorems.

**NOTE** : Universes are not implemented, meaning it is currently unsound (`Type : Type`).

It follows quite closely the outline of [Samuel MIMRAM's proof assistant project](https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/pp/TD/4.prover.html#dependent-types). The [repository](https://github.com/leo-leesco/Computational-Logic-TD4-proof-assistant.git) is public.

## Usage

We use `make` for this project, in various ways :
- `make build` is `dune build`
- `make` alone enters in interactive mode and writes to `proofs/interactive`
- `make test` runs all files in `tests/` independently

## Installation


