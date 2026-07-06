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

/-!
Next tactic: `have`.

`have` creates a new intermediate fact inside a proof.

Read:

`have hq : Q := hpq hp`

as:

"Let `hq` be a proof of `Q`, obtained by applying `hpq` to `hp`."
-/
example (P Q R : Prop) (hp : P) (hpq : P -> Q) (hqr : Q -> R) : R := by
  -- First create a proof of `Q`.
  have hq : Q := hpq hp

  -- Now use that proof of `Q` to create a proof of `R`.
  have hr : R := hqr hq

  -- The goal is `R`, and `hr` already proves it.
  exact hr

/-!
You can use `have` to make an `and` proof step by step.
-/
example (P Q R : Prop) (hp : P) (hq : Q) (hqr : Q -> R) : P ∧ R := by
  -- Build the right side first.
  have hr : R := hqr hq

  -- Now prove `P ∧ R`.
  constructor
  · exact hp
  · exact hr

/-!
You can also use `have` to name a contradiction.
-/
example (P Q : Prop) (hp : P) (hnp : ¬ P) : Q := by
  -- Name the contradiction.
  have contradiction : False := hnp hp

  -- Use the contradiction to prove `Q`.
  exact False.elim contradiction

/-!
Tiny exercise:

In the first `have` example, delete the line:

`have hr : R := hqr hq`

Then try to finish the proof directly with:

`exact hqr hq`
-/

/-!
Next grammar: equality.

`a = b` is a proposition.

So a proof of:

`a = b`

means:

"Lean accepts that `a` and `b` are equal."
-/
example : 2 + 3 = 5 := by
  -- `rfl` means "both sides are the same after Lean computes/simplifies them."
  rfl

example : Sandbox.Basic.Syntax.double 4 = 8 := by
  -- `double 4` unfolds to `4 + 4`, and Lean can compute that to `8`.
  rfl

/-!
Equality can also be an assumption.

Read:

`h : a = b`

as:

"`h` is a proof that `a` equals `b`."
-/
example (a b : Nat) (h : a = b) : a = b := by
  -- The goal is exactly what `h` already proves.
  exact h

/-!
If you have `h : a = b`, you can also prove `b = a`.

The theorem `Eq.symm` turns equality around.
-/
example (a b : Nat) (h : a = b) : b = a := by
  exact Eq.symm h

/-!
A common beginner pattern:

Use `have` to name an equality, then use it with `exact`.
-/
example : Sandbox.Basic.Syntax.double 5 = 10 := by
  have h : Sandbox.Basic.Syntax.double 5 = 10 := by
    rfl
  exact h

/-!
Tiny exercise:

Change `double 5 = 10` to `double 6 = 12`.
Then check whether `rfl` still closes the proof.
-/

/-!
Next tool: `#check` versus `#eval`.

`#eval` runs a computable expression and prints a value.
-/
#eval Sandbox.Basic.Syntax.double 7

/-!
`#check` does not run a program.
It asks Lean:

"What is the type of this expression?"

This is very useful for proofs.
-/
#check Sandbox.Basic.Syntax.double
#check And.intro
#check Or.inl
#check False.elim
#check Eq.symm

/-!
You can also `#check` a proof expression.

The expression below is an anonymous function.
Read `fun ... => ...` as:

"Given these inputs, return this result."
-/
#check fun (P Q : Prop) (hp : P) (hpq : P -> Q) => hpq hp

/-!
The type that Lean prints is the theorem shape:

`(P Q : Prop) -> P -> (P -> Q) -> Q`

Meaning:

For any propositions `P` and `Q`,
if you have `P`,
and you have `P -> Q`,
then you can get `Q`.
-/

/-!
Tiny exercise:

Put your cursor on each `#check` line and read what Lean prints.
Do not try to memorize it. Just notice the shape.
-/

#eval Sandbox.Basic.Syntax.double 7

#check False.elim

#check fun (P Q : Prop) (hp : P) (hpq : P → Q) => hpq hp

#check fun (x : Nat) => x + 1

/-!
Next grammar: anonymous functions.

`fun x => x + 1`

means:

"Make a function. It takes input `x`, and returns `x + 1`."

This is like writing:

`x ↦ x + 1`

in ordinary math.
-/
#eval (fun (x : Nat) => x + 1) 5

/-!
You can give the function a name with `def`.
-/
def addOne (x : Nat) : Nat :=
  x + 1

#eval addOne 5



def addThree (x: Nat) : Nat :=
x + 3

#eval addThree 9
/-!
Proofs can also be written as functions.

This proof:
-/
example (P : Prop) : P -> P := by
  intro hp
  exact hp

/-!
can be written more directly as:
-/
example (P : Prop) : P -> P :=
  fun hp => hp

/-!
Read:

`fun hp => hp`

as:

"Given a proof `hp` of `P`, return that same proof `hp`."

So it proves:

`P -> P`

because it turns any proof of `P` into a proof of `P`.
-/

/-!
Another example:
-/
example (P Q : Prop) : P -> Q -> P :=
  fun hp _hq => hp

/-!
Read:

`fun hp _hq => hp`

as:

"Given a proof `hp : P`, and given a proof `_hq : Q`,
return `hp`."

The underscore in `_hq` means:

"This argument exists, but I will not use it."
-/

/-!
Tiny exercise:

Put your cursor on:

`fun hp _hq => hp`

and use the InfoView / hover to see the types of `hp` and `_hq`.
-/

/-!
Next idea: named theorems.

`example` checks a proof, but it does not give the proof a name.

`theorem` is like `example`, but reusable.
-/
theorem proofFromImplication (P Q : Prop) (hp : P) (hpq : P -> Q) : Q := by
  exact hpq hp

/-!
Now Lean remembers the theorem name:
-/
#check proofFromImplication

/-!
You can use the named theorem inside another proof.
-/
example (A B : Prop) (ha : A) (hab : A -> B) : B := by
  exact proofFromImplication A B ha hab

/-!
Notice the order:

`proofFromImplication A B ha hab`

means:

- use `A` as `P`
- use `B` as `Q`
- use `ha` as the proof of `A`
- use `hab` as the proof of `A -> B`
-/

/-!
You can also let Lean infer some arguments by writing `_`.
-/
example (A B : Prop) (ha : A) (hab : A -> B) : B := by
  exact proofFromImplication _ _ ha hab

/-!
Tiny exercise:

Change the theorem name `proofFromImplication` to your own name.
Then update the two examples that use it.
-/

/-!
Next grammar: `variable` and `section`.

Sometimes several examples use the same assumptions.
Instead of writing `(P Q : Prop)` every time, you can declare them once.

`section` starts a local area.
`end` closes that local area.
-/
section VariablePractice

variable (P Q R : Prop)

/-!
Inside this section, Lean knows:

`P : Prop`
`Q : Prop`
`R : Prop`

So we can write shorter examples.
-/
example (hp : P) : P := by
  exact hp

example (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

/-!
You can also declare proof variables.
-/
variable (hp : P)
variable (hpq : P -> Q)
variable (hqr : Q -> R)

/-!
Now Lean knows:

`hp : P`
`hpq : P -> Q`
`hqr : Q -> R`

for the rest of this section.
-/
example : Q := by
  exact hpq hp

example : R := by
  have hq : Q := hpq hp
  exact hqr hq

end VariablePractice

/-!
After `end VariablePractice`, those local variables are gone.

This keeps the scratch file organized: assumptions live only where they are
needed.
-/

/-!
Tiny exercise:

Inside the section above, add this example and try to complete it:

`example : P ∧ R := by`

Hint:

First prove `R`, then use `constructor`.
-/

/-!
Next tactic: `rw`.

`rw` means "rewrite".

If you have:

`h : a = b`

then:

`rw [h]`

replaces `a` with `b` in the current goal.
-/
example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  -- Goal starts as:
  -- `a + 1 = b + 1`
  --
  -- `rw [h]` replaces `a` with `b`.
  rw [h]

  -- Now the goal is:
  -- `b + 1 = b + 1`
  --
  -- Lean notices both sides are the same, so `rw [h]` finishes the proof.
  -- If you write `rfl` after this, Lean says there are no goals left.

/-!
Often `rw` leaves a goal that `rfl` can solve automatically.
Sometimes `rw` finishes the proof by itself.
-/
example (a b : Nat) (h : a = b) : a = b := by
  rw [h]

/-!
You can rewrite backwards with:

`rw [← h]`

Type `\l` or `\leftarrow` then Space/Tab to get `←`.
-/
example (a b : Nat) (h : a = b) : b + 1 = a + 1 := by
  -- Replace `b` with `a` by using `h` backwards.
  rw [← h]

example: 2 + 3 = 5 := by
  rfl
  -- rfl works when both sides are already the same after Lean computes.
  -- rw changes the goal using an equality.
  -- If rw already finishes the proof, do not write rfl after it.

/-!
You can rewrite inside larger expressions too.
-/
example (a b : Nat) (h : a = b) : Sandbox.Basic.Syntax.double a = Sandbox.Basic.Syntax.double b := by
  rw [h]

/-!
Tiny exercise:

Change the first rewrite example from:

`a + 1 = b + 1`

to:

`a + 3 = b + 3`

and see whether `rw [h]` still works.
-/

/-!
Next tactic: `simp`.

`simp` means "simplify".

It tries many obvious simplifications automatically:

- compute simple arithmetic
- remove unnecessary `True`
- simplify expressions like `x + 0`
- use known simplification rules

You can think of `simp` as:

"Lean, clean up the goal using obvious facts."
-/
example : 2 + 3 = 5 := by
  simp

example (n : Nat) : n + 0 = n := by
  simp

example (n : Nat) : 0 + n = n := by
  simp

/-!
You can also give `simp` a fact to use.

This is like `rw [h]`, but `simp [h]` may also simplify after rewriting.
-/
example (a b : Nat) (h : a = b) : a + 0 = b := by
  -- Use `h` to replace `a` with `b`, then simplify `b + 0`.
  simp [h]

/-!
Compare these two proofs.

With `rw`, we may need to think about the remaining goal:
-/
example (a b : Nat) (h : a = b) : a + 0 = b := by
  rw [h]
  simp

/-!
With `simp [h]`, Lean does both parts:

1. use `h`
2. simplify `b + 0`
-/
example (a b : Nat) (h : a = b) : a + 0 = b := by
  simp [h]

example (a b : Nat)(h : a = b) : a + 0 = b := by
  simp [h]



/-!
Tiny exercise:

Change:

`a + 0 = b`

to:

`0 + a = b`

and test whether `simp [h]` still solves it.
-/

/-!
Next skill: choose the tactic from the goal shape.

This is one of the most useful habits in Lean.

Look first at the goal, then choose the tactic.
-/

/-!
Goal shape: exactly something in the context.

Use `exact`.
-/
example (P : Prop) (hp : P) : P := by
  exact hp

/-!
Goal shape: `P -> Q`.

Use `intro` to assume `P`.
-/
example (P Q : Prop) (hpq : P -> Q) : P -> Q := by
  intro hp
  exact hpq hp

/-!
Goal shape: `P ∧ Q`.

Use `constructor` to split it into two goals.
-/
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

/-!
Context shape: `h : P ∧ Q`.

Use `h.left`, `h.right`, or `cases h`.
-/
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  · exact h.right
  · exact h.left

/-!
Context shape: `h : P ∨ Q`.

Use `cases h`, because either side may be true.
-/
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>
      exact Or.inr hp
  | inr hq =>
      exact Or.inl hq

/-!
Goal shape: equality with an equality hypothesis.

Use `rw [h]`.
-/
example (a b : Nat) (h : a = b) : a + 2 = b + 2 := by
  rw [h]

/-!
Goal shape: boring arithmetic or cleanup.

Try `simp`.
-/
example (a b : Nat) (h : a = b) : 0 + a + 0 = b := by
  simp [h]

/-!
Tiny exercise:

Before writing a tactic, ask:

- Is the goal an implication? Try `intro`.
- Is the goal an `and`? Try `constructor`.
- Do I have an `or` assumption? Try `cases`.
- Do I have an equality? Try `rw`.
- Does the goal look like cleanup? Try `simp`.
- Is the exact proof already in the context? Try `exact`.
-/

/-!
Next idea: tactic mode versus term mode.

Lean has two common ways to write proofs.

1. Tactic mode:

`:= by`

Then you write tactics like `intro`, `exact`, `constructor`.

2. Term mode:

No `by`.
You write the proof expression directly.
-/

/-!
Same theorem, tactic mode:
-/
example (P : Prop) : P -> P := by
  intro hp
  exact hp

/-!
Same theorem, term mode:
-/
example (P : Prop) : P -> P :=
  fun hp => hp

/-!
These two proofs mean the same thing.

Tactic mode is like telling Lean:

"Step 1, assume `hp`.
 Step 2, use `hp`."

Term mode is like directly giving Lean the finished proof object:

"Here is the function: `fun hp => hp`."
-/

/-!
Another pair: prove `P ∧ Q`.

Tactic mode:
-/
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

/-!
Term mode:
-/
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
  And.intro hp hq

/-!
Another pair: use an implication.

Tactic mode:
-/
example (P Q : Prop) (hp : P) (hpq : P -> Q) : Q := by
  exact hpq hp

/-!
Term mode:
-/
example (P Q : Prop) (hp : P) (hpq : P -> Q) : Q :=
  hpq hp

/-!
Practical advice:

Use tactic mode while learning, because the InfoView shows the goal after
each step.

Read term mode slowly, because it reveals that proofs are also expressions.
-/

/-!
Tiny exercise:

For each pair above, put your cursor on the tactic proof and then on the term
proof. Notice that Lean accepts both, even though they look different.
-/
