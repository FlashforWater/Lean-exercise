namespace Sandbox.Exercises.LogicLevel2

/-!
Second logic practice set.

These are still small, but they combine tactics more often.

Suggested workflow:

1. Replace one `sorry` at a time.
2. Watch the InfoView after every tactic.
3. If the goal is an implication, use `intro`.
4. If the goal is an `and`, use `constructor`.
5. If you have an `or` hypothesis, use `cases`.
6. If you reach `False`, use `False.elim` only when the goal is not already `False`.
-/

theorem exercise_and_assoc_forward (P Q R : Prop) (h : (P ∧ Q) ∧ R) : P ∧ (Q ∧ R) := by
  -- Goal shape: `P ∧ (Q ∧ R)`.
  -- Hint: split with `constructor`.
  -- From `h`, you can use:
  -- `h.left.left  : P`
  -- `h.left.right : Q`
  -- `h.right      : R`
  constructor
  · exact h.left.left
  · constructor
    · exact h.left.right
    · exact h.right



theorem exercise_or_distribute_left (P Q R : Prop) (h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) := by
  -- Context contains an `or` inside `h.right`.
  -- Hint: use `cases h.right with`.
  -- In the `Q` case, prove the left side with `Or.inl`.
  -- In the `R` case, prove the right side with `Or.inr`.
  cases h.right with
  | inl hq =>
    apply Or.inl
    constructor
    · exact h.left
    · exact hq
  | inr hr =>
    apply Or.inr
    constructor
    · exact h.left
    · exact hr



theorem exercise_contrapositive_small (P Q : Prop) (hpq : P -> Q) (hnq : ¬ Q) : ¬ P := by
  -- Goal shape: `¬ P`, which means `P -> False`.
  -- Hint: use `intro hp`.
  -- Then get `hq : Q` from `hpq hp`.
  -- Then use `hnq hq`.
  intro hp
  have hq : Q := hpq hp
  exact hnq hq


theorem exercise_or_elim_to_goal (P Q R : Prop) (h : P ∨ Q) (hpr : P -> R) (hqr : Q -> R) : R := by
  -- Context shape: `h : P ∨ Q`.
  -- Hint: split into cases.
  -- In the `P` case, use `hpr`.
  -- In the `Q` case, use `hqr`.
  cases h with
  | inl hp =>
    exact hpr hp
  | inr hq =>
    exact hqr hq





theorem exercise_chain_and_package (P Q R : Prop) (hp : P) (hpq : P -> Q) (hqr : Q -> R) : Q ∧ R := by
  -- Goal shape: `Q ∧ R`.
  -- Hint: first create `hq : Q`.
  -- Then create `hr : R`.
  -- Then use `constructor`.
  have hq: Q := hpq hp
  constructor
  · exact hq
  · exact hqr hq

end Sandbox.Exercises.LogicLevel2
