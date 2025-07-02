# Simply typed theorem prover

## Usage

Run `dune exec ./proving.exe`. This will prompt you for a proposition you would like to prove and to input a series of tactics to prove it. This results in a proof term written as a $\lambda$-term.

The prover will summarize the commands inputted at the end of the proof, which can then be loaded again (as is) :
```shell
cat <proof> | dune exec ./proving.exe
```

## Tactics

### `exact`

Requires an element of the context whose type matches the current goal.

This is the *axiom* rule in case you provide an identifier, and plugs the expression provided in the hole in case a fully well-formed expression is provided.

In case the goal is `true` or `⊤`, ends the proof.

This is the *truth introduction* rule.

In case the goal is a natural number, ends the proof with `Zero`. Note that providing an identifier here uses the regular tactic.

### `intro`

In presence of a connector, we can prove it as the result of an introduction rule (which "creates" it).

#### `intro x`

In case the goal is an arrow, introduces a new identifier which matches its domain, leaving the codomain to be proven from the context.

This is the *arrow introduction* rule.

#### Conjunction

In case the goal is a conjunction type, divides the proof into two subproofs of both types of the pair.

This is the *conjunction introduction* rule.

#### `left` and `right`

In case the goal is a disjunction, allows to prove only the left or right goal.

This are the *disjunction introduction* rules.

#### `Succ(n)`

In case the goal is a natural number, asks to prove the predecessor of the current goal.

This is the *successor introduction* rule.

### `elim`

Tries to prove the goal by using connectors that could have led to the current goal (basically backtracking).

#### `elim f`

Provide an identifier whose type is an arrow whose codomain matches the current goal, leaving the domain to be proven.

This is the *arrow elimination* rule.

#### `cut A`

Divides the proof into two subproofs, one of the lemma `A`, the other that `A` is indeed sufficient to prove the current goal.

This is the *full arrow elimination* rule.

#### `fst p` and `snd p`

Provide an identifier whose type is a conjunction type and either its first or second component matches the current goal.

This are the *left* and *right elimination* rules.

#### False

In case an identifier is of type `False`, prove the current goal.

This is the *false elimination* rule.

#### `Rec`

In case the provided identifier's type matches the current goal but no other rule above, proves the recurrence principle on natural numbers.

This is the *natural recurrence principle elimination* rule.
