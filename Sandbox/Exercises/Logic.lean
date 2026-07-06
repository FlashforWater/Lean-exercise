namespace Sandbox.Exercises.Logic

-- Replace each `sorry` with a proof when you practice.
-- It is fine to leave `sorry` in this sandbox while learning.
--
-- Practice rule:
-- 1. Read the goal after `:= by`.
-- 2. Look at the hypotheses.
-- 3. Choose a tactic from the goal shape.

theorem exercise_identity (P : Prop) (h : P) : P := by
  -- Goal: prove `P`.
  -- Hypothesis: `h : P`.
  -- The exact proof is already in the context.
  exact h

theorem exercise_swap_and (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  -- Goal shape: `Q ∧ P`.
  -- Hint: an `and` goal asks for `constructor`.
  -- After that, use `h.right` and `h.left`.
  constructor
  · exact h.right
  · exact h.left


theorem exercise_swap_or (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  -- Context shape: `h : P ∨ Q`.
  -- Hint: an `or` hypothesis asks for `cases h`.
  -- In the left case, prove the right side with `Or.inr`.
  -- In the right case, prove the left side with `Or.inl`.
  cases h with
  | inl hp =>
    exact Or.inr hp
  | inr hp =>
    exact Or.inl hp



theorem exercise_chain (P Q R : Prop) (hp : P) (hpq : P -> Q) (hqr : Q -> R) : R := by
  -- Goal: prove `R`.
  -- Hint: first create `hq : Q` using `hpq hp`.
  -- Then use `hqr hq`.

  have hq : Q := hpq hp
  exact hqr hq




end Sandbox.Exercises.Logic
