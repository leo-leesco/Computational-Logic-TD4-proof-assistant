# Dependent prover

The aim of this project is to provide a simple environment to define dependent functions, and prove various theorems.

**NOTE** : Universes are not implemented, meaning it is currently unsound (`Type : Type`).

It follows quite closely the outline of [Samuel MIMRAM's proof assistant project](https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/pp/TD/4.prover.html#dependent-types). The [repository](https://github.com/leo-leesco/Computational-Logic-TD4-proof-assistant.git) is public.

## Usage

### `make` commands

We use `make` for this project, in various ways :
- `make build` is `dune build`
- `make` alone enters in interactive mode and writes to `proofs/interactive`
- `make test` runs all files in `tests/` independently
- `make <file> [<OPTIONS>]` will :
    - write to `proofs/<file>`
    - if `clean=1` is given, the file is first erased before being written to, otherwise (meaning `clean` is not set, the value of `clean` is not compared against) the script is first executed and subsequent commands are appended to it 
    - if `lib=<libraries>` is given, the scripts described by `<libraries>` are first run before you can input more commands. `<libraries>` is an arbitrary string that `ls` (`cat` actually) can read.
    > eg : `make addassoc lib={lib/dnat/*,proofs/Seq} clean=1`

### Inside the interaction loop

You can execute the following commands :
- `context` prints the current context
- `assume <ident> : <type>` adds `<ident>` of type `<type>` to the global context
- `define <ident> = <expr>` adds `<ident>` defined as `<expr>` to the global context, the type is automatically inferred
- `type <expr>` returns the type of `<expr>`
- `check <expr> = <type>` prints `Ok.` if `<expr>` is indeed of type `<type>`, or prints at which point in the type evaluation a subexpression diverged from what was expected
- `eval <expr>` returns a normalized version of `<expr>`
- `prove <ident> = <type>` enters proof mode, and upon success adds the term built (to prove the `<type>`) to the context

### Inside the prover

When in proof mode (see the [previous paragraph](#inside-the-interaction-loop))

## Installation

You will need :
- `OCaML` (tested with `ocaml@4.14.2`)
- `opam`
- `dune`
- `ppx_expect`

Here is a proposed install script (there is no guarantee anything will work if other versions are used) :
```bash
opam switch create . ocaml-base-compiler.4.14.2
opam install . --locked
opam install dune
```

## Tests

To run inline tests :
```bash
dune test
```
