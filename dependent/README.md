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
- `environment` prints the global context
- `assume <ident> : <type>` adds `<ident>` of type `<type>` to the global context
- `define <ident> = <expr>` adds `<ident>` defined as `<expr>` to the global context, the type is automatically inferred
- `type <expr>` returns the type of `<expr>`
- `check <expr> = <type>` prints `Ok.` if `<expr>` is indeed of type `<type>`, or prints at which point in the type evaluation a subexpression diverged from what was expected
- `eval <expr>` returns a normalized version of `<expr>`
- `prove <ident> = <type>` enters proof mode, and upon success adds the term built (to prove the `<type>`) to the context
- `exit` gracefully stops the prover (it is useful as `make <file>` has clean-up commands running after the execution of the prover)

### Inside the prover

When in proof mode (see the [previous paragraph](#inside-the-interaction-loop)), you can run [`Rocq`-like tactics](https://rocq-prover.org/doc/V8.0/doc/Reference-Manual010.html) :
- `context` prints the local context
- `environment` prints the global context
- `exact <expr>` concludes the proof _iff_ `<expr>` type matches (in the local context of the function) the current goal
- `elim <ident> <args>` applies elimination tactics to `<ident>` in the local context, depending on the type of `<ident>` :
    - `A -> B` : if `B` is the goal, `A` is left to prove
    - `Nat` : starts a proof by induction on `<ident>`. If `<args>` is provided, its type is the induction hypothesis.
    - `x = y` : starts a proof by (structural) induction on `<ident>`. If `<args>` is provided, it is split (on whitespaces) up to two times, and represent :
        - `<arg1>` represents `x`
        - `<arg2>` represents `y`
    <!-- If `<args>` is provided, and `p <ident>` is the predicate we are trying to prove over induction on `<ident>`, `<args>` is the induction -->
- `intro [<ident>]`
    - `(x : A) -> B` or `A -> B` : introduces `x` if no `<ident>` is provided, or `<ident> : A`, in the context
- `cut <type>` requires to first prove the lemma `<type>` and then asks to prove `<type> -> goal` (which basically amounts to adding `<type>` to the context)
- `abort` returns to the [interaction loop](#inside-the-interaction-loop)

## Installation

You will need :
- `OCaML` (tested with `ocaml@4.14.2`)
- `opam`
- `dune`
- `ppx_expect` (relies on `sexplib`)

```bash
make install
```

## Tests

To run inline tests :
```bash
dune test
```
