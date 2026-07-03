import Sandbox

/-!
This file is your loose experiment space.

You can break things here freely. The Lean InfoView will update as you type.
-/

-- `#eval` asks Lean to compute an expression and print the result.
-- `Sandbox.Basic.Syntax.double` is the full name of the function `double`
-- that we defined in `Sandbox/Basic/Syntax.lean`.
#eval Sandbox.Basic.Syntax.double 12

/-!
Read the next example as:

Assume:
- `P` and `Q` are propositions.
- `hp` is a proof of `P`.
- `hq` is a proof of `Q`.

Then prove:
- `P ∧ Q`, meaning "`P` and `Q`".
-/
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  -- To prove an `and` statement, use `constructor`.
  -- Lean changes one goal, `P ∧ Q`, into two goals: first `P`, then `Q`.
  constructor

  -- The first goal is `P`.
  -- `hp` already has type `P`, so `exact hp` finishes this goal.
  · exact hp

  -- The second goal is `Q`.
  -- `hq` already has type `Q`, so `exact hq` finishes this goal.
  · exact hq

/-!
Tiny exercise:

Try replacing the final `exact hq` above with `exact hp`.
Lean should complain, because the goal is `Q` but `hp` proves `P`.
-/

/-!
Next grammar: implication.

`P -> Q` means:

If `P` is true, then `Q` is true.

In Lean, a proof of `P -> Q` behaves like a function:
give it a proof of `P`, and it returns a proof of `Q`.
-/
example (P Q : Prop) (hp : P) (hpq : P -> Q) : Q := by
  -- Goal: prove `Q`.
  -- `hpq` can turn a proof of `P` into a proof of `Q`.
  -- `hp` is a proof of `P`.
  exact hpq hp

/-!
The same proof, written in smaller tactic steps:
-/
example (P Q : Prop) (hp : P) (hpq : P -> Q) : Q := by
  -- `apply hpq` says:
  -- "I can prove `Q` if I first prove the input needed by `hpq`."
  apply hpq

  -- Now the goal has changed from `Q` to `P`.
  -- `hp` proves `P`, so we are done.
  exact hp

/-!
Now the opposite situation:

If your goal is `P -> P`, Lean asks you to prove an implication.
To prove an implication, use `intro`.

`intro hp` means:
"Assume `P` is true, and call that proof `hp`."
-/
example (P : Prop) : P -> P := by
  -- Goal: prove `P -> P`.
  intro hp

  -- After `intro hp`, the goal is `P`,
  -- and the context now contains `hp : P`.
  exact hp

/-!
Tiny exercise:

Move your cursor after each line in the examples above.
Watch how the InfoView goal changes after `apply hpq` and after `intro hp`.
-/

/-!
Next grammar: disjunction.

`P ∨ Q` means "`P` or `Q`".

To prove `P ∨ Q`, you only need one side:

- `Or.inl hp` proves `P ∨ Q` using a proof of the left side, `P`.
- `Or.inr hq` proves `P ∨ Q` using a proof of the right side, `Q`.
-/
example (P Q : Prop) (hp : P) : P ∨ Q := by
  -- We have a proof of `P`, so we choose the left side of `P ∨ Q`.
  exact Or.inl hp

example (P Q : Prop) (hq : Q) : P ∨ Q := by
  -- We have a proof of `Q`, so we choose the right side of `P ∨ Q`.
  exact Or.inr hq

/-!
Using an `or` proof is different.

If you have `h : P ∨ Q`, you do not know which side is true.
So Lean makes you handle both cases.
-/
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  -- Split the proof `h` into two possible cases.
  cases h with
  | inl hp =>
      -- Case 1: `h` was a proof of the left side, so now `hp : P`.
      -- Goal: prove `Q ∨ P`.
      -- Since we have `P`, choose the right side.
      exact Or.inr hp
  | inr hq =>
      -- Case 2: `h` was a proof of the right side, so now `hq : Q`.
      -- Goal: prove `Q ∨ P`.
      -- Since we have `Q`, choose the left side.
      exact Or.inl hq

/-!
Tiny exercise:

In the case split above, move the cursor inside each branch.
Notice that Lean gives you different assumptions:

- in the `inl` branch, you have `hp : P`
- in the `inr` branch, you have `hq : Q`
-/

/-!
Next grammar: using an `and` proof.

If you have:

`h : P ∧ Q`

then `h` contains two proofs:

- `h.left` is a proof of `P`
- `h.right` is a proof of `Q`
-/
example (P Q : Prop) (h : P ∧ Q) : P := by
  -- Goal: prove `P`.
  -- Since `h : P ∧ Q`, the left part of `h` proves `P`.
  exact h.left

example (P Q : Prop) (h : P ∧ Q) : Q := by
  -- Goal: prove `Q`.
  -- Since `h : P ∧ Q`, the right part of `h` proves `Q`.
  exact h.right

/-!
You can also take an `and` proof apart with `cases`.

This is useful when you want to give names to the two pieces.
-/
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  -- Split `h : P ∧ Q` into two assumptions:
  -- `hp : P` and `hq : Q`.
  cases h with
  | intro hp hq =>
      -- Goal: prove `Q ∧ P`.
      constructor
      · exact hq
      · exact hp

/-!
Tiny exercise:

In the proof above, change `Q ∧ P` to `P ∧ Q`.
Then repair the two `exact` lines.
-/

/-!
Next grammar: false and not.

`False` is the proposition that has no proof.

`¬ P` means "not P".
In Lean, `¬ P` is really shorthand for:

`P -> False`

So a proof of `¬ P` is a function:
give it a proof of `P`, and it produces a contradiction.
-/
example (P : Prop) (hp : P) (hnp : ¬ P) : False := by
  -- `hnp` means `P -> False`.
  -- Since `hp : P`, applying `hnp` to `hp` gives `False`.
  exact hnp hp

/-!
From `False`, Lean can prove anything.

This is the logical rule:
from contradiction, anything follows.

In Lean, use `False.elim`.
-/
example (P Q : Prop) (hp : P) (hnp : ¬ P) : Q := by
  -- First make the contradiction.
  have impossible : False := hnp hp

  -- Then use the contradiction to prove the current goal `Q`.
  exact False.elim impossible

/-!
How do you prove a negation?

Since `¬ P` means `P -> False`, use `intro`.

To prove `¬ P`, assume `P`, then prove `False`.
-/
example (P Q : Prop) (hp : P) (hnq : ¬ Q) : ¬ (P -> Q) := by
  -- Goal: prove `¬ (P -> Q)`.
  -- This means prove `(P -> Q) -> False`.
  intro hpq

  -- Now `hpq : P -> Q`.
  -- Since `hp : P`, we can get `hq : Q`.
  have hq : Q := hpq hp

  -- But `hnq : ¬ Q`, so `hnq hq : False`.
  exact hnq hq

/-!
Tiny exercise:

In the last proof, move your cursor after `intro hpq`.
Notice that Lean changes the goal from `¬ (P -> Q)` to `False`,
and adds `hpq : P -> Q` to the context.
-/
