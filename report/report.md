---
title: Report for the _proof assistant project_
author: Léo LEESCO
---

The project is divided into two parts :

- using the Curry-Howard equivalence to prove propositional formulas, which equate to typing $\lambda$-terms

- similarly, but implementing dependent types this time to get closer to modern provers such as Agda

# What was implemented in the project

## Simple types

The part implementing simple types relies on a type checker that handles the following types :

- Implications i.e. function signatures

- Conjunctions i.e. product types

- Disjunctions i.e. union types

- Truth i.e. unit type

- False i.e. empty type

- Natural numbers

- and of course basic typing (naming types)

To produce such types, we introduce terms that have the corresponding types (functions, products, etc.), and match the type inference rules with the term introduction rules for the prover.

The design (which is the same for the dependent part) is that we start with a goal, which is a type, and enter commands that progressively construct a $\lambda$-term that matches what is need.

### Implementation choices

#### Visual choices

In order to facilitate debugging and avoid having types that look like a compound type (e.g. `A /\ B` as type name instead of the product type composed of `A` and `B`), I added a function `raw_of_ty` that follows the same logic as `string_of_ty` and helps with debugging, especially when doing type inference on Natural numbers.

Following the same idea, I added two commands to the interpreter in order to see what is going on : `type` which asks for a variable present in the context, and `show` which (should, but does not work as intended) show the current $\lambda$-term.

A second design choice I made was to try and reduce successor to a more human-readable format (`Succ(Succ(n))` should be pretty-printed as `n + 2`).

Lastly, about the interpreter loop, I decided to offer the possibility to directly write to a file (all handled by the program). It allows to either load a proof and check that it is correct, or write a new one.

#### Logical choices

For `Case` and `Rec`, my first intention was to have return branches to be functions. In order to make the type system compliant with the parser, I decided to go back on this decision for `Case` so as to have it of the form `case (t, x, u, y, v)` instead of `case (t, x -> u, y -> v)`. However, after becoming more familiar with the parser's syntax, I went for parsing `Rec` as `Rec (t, u, Abs(x, Abs(y, v)))` (where `t` is the rank of the recursor, `u` is the return value when `t=0` ; when `t>0`, `x` is `pred t`, `y` is the computed value for `pred t` and `v` is the computed expression for `t`).

For `elim`, a general rule is to use it with exactly one argument present in the context. However, in the case of `Rec`, the argument is expected to be of the form `x|y` (whitespaces are allowed : `x | y` and variations are equally valid, the arguments are parsed based on `|`) which are the variable names for the `Abs(x, Abs(y, v))` as previously mentioned.

### Difficulties encountered

The first problem I faced was quite unexpected : some terms were not properly parsed by the lexer. When a type was passed as a command argument, it was interpreted as a type name, instead of first being parsed then interpreted as a complete type. For instance, when doing `cut A /\ B`, before adding proper parsing, the prover interpreted the command as `cut` for the type `A /\ B` instead of `cut` for the conjunction of the types `A` and `B`.

### Extensions

Everything that was required from this part has been done, except loading a partially done proof : the expected behaviour is to be able to load an incomplete proof, and give back control to the user if need be. I did not try to do that as it was not the goal of the project.

## Dependent types

The subtlety in this case is that functions (among others) can have a return type dependent on the variable provided, and since the system is more flexible in this case, types and terms can be unified.

### Implementation choices

This part is not fully implemented yet. To make things simpler, not all inference rules are implemented yet (Natural numbers and Equality).

Contrary to the simple implementation which starts from an empty context (in the prover), since the types are considered as regular terms, we have to provide a way to see the context at all times. In debug mode, we print the term and the context it lives in for each evaluation of `infer`.

Lastly, we can no longer rely on a simple type-checking as we can benefit from both $\alpha\beta$-reduction and due to the way we perform substitution (aggressive renaming of bound variables, which makes $\alpha$-reduction central).

# Conclusion

This project was extremely interesting and I am going to see it through in the upcoming weeks : there are some features left to be implemented (such as Natural numbers and Equality in the dependent part).

You can follow the evolution of the project at https://github.com/leo-leesco/proof-assistant-project !

Please note this project is part of the Computational Logic class given by Professor Samuel MIMRAM at École Polytechnique, who has my wholehearted thanks for both the class and projects throughout the quarter.
