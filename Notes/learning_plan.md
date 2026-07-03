# Lean Learning Plan

This plan is for learning Lean slowly and concretely. Do not rush.

## Stage 1: Read Lean Expressions

Goal: understand what Lean code says before trying to prove hard things.

Practice files:

- `Playground/Scratch.lean`
- `Sandbox/Basic/Syntax.lean`

Things to learn:

- `#eval`
- `def`
- function application
- namespaces and imports

Checkpoint:

- You can explain `#eval Sandbox.Basic.Syntax.double 12`.

## Stage 2: Read Propositions As Types

Goal: understand theorem statements.

Practice files:

- `Sandbox/Basic/Propositions.lean`
- `Sandbox/Exercises/Logic.lean`

Things to learn:

- `P : Prop`
- `h : P`
- `P -> Q`
- `P ∧ Q`
- `P ∨ Q`

Checkpoint:

- You can explain `example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q`.

## Stage 3: Learn Tiny Tactics

Goal: know what each proof step does to the goal.

Practice files:

- `Sandbox/Basic/Tactics.lean`
- `Playground/Scratch.lean`

Things to learn:

- `by`
- `exact`
- `constructor`
- `intro`
- `cases`

Checkpoint:

- You can prove `P ∧ Q` from `hp : P` and `hq : Q`.

## Stage 4: Solve Exercises With `sorry`

Goal: replace one `sorry` at a time.

Practice files:

- `Sandbox/Exercises/Logic.lean`
- `Sandbox/Exercises/NaturalNumbers.lean`

Rules:

- Solve only one theorem at a time.
- Read the InfoView after every line.
- When stuck, write the error in `Notes/mistakes.md`.

Checkpoint:

- `lake build` has fewer `sorry` warnings than before.

## Stage 5: Add Mathlib Later

Goal: use the larger mathematics library only after basic Lean feels familiar.

Do this later, not now.

Things to learn later:

- importing Mathlib
- theorem search
- algebraic structures
- real-number proofs

Checkpoint:

- You can read simple proofs before using a large library.
