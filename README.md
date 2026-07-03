# Lean Learning Sandbox

This project is a personal sandbox for learning Lean 4.

The goal is not to keep everything polished. The goal is to make a place where
you can try small ideas, break proofs, repair them, and keep the useful patterns.

## Layout

- `Sandbox/Basic/`: small examples for syntax, propositions, and tactics.
- `Sandbox/Exercises/`: practice files with `sorry` placeholders.
- `Playground/Scratch.lean`: a loose scratchpad for experiments.
- `Notes/learning_plan.md`: the staged learning path.
- `Notes/proof_patterns.md`: proof moves worth remembering.
- `Notes/mistakes.md`: errors and fixes you want future-you to remember.

## First Commands

After the Lean toolchain is installed, run:

```sh
lake build
```

Open `Playground/Scratch.lean` in VS Code and edit it while watching Lean's
infoview.

## Learning Rhythm

1. Read one file in `Sandbox/Basic/`.
2. Change an example and observe the error.
3. Solve one theorem in `Sandbox/Exercises/`.
4. Write down one useful pattern or mistake in `Notes/`.

Small daily contact beats rare heroic sessions.
