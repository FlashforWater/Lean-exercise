namespace Sandbox.Exercises.LogicLevel3

/-!
Third logic practice set.

Theme:

- negation as `P -> False`
- contradiction
- equality and rewriting

Suggested workflow:

1. Replace one `sorry` at a time.
2. If the goal is `¬ P`, start with `intro hp`.
3. If you have both `hp : P` and `hnp : ¬ P`, use `hnp hp`.
4. If the goal is equality and you have `h : a = b`, try `rw [h]`.
5. If the goal looks like simple cleanup, try `simp`.
-/

theorem exercise_not_not_intro (P : Prop) (hp : P) : ¬ ¬ P := by
  -- Goal shape: `¬ ¬ P`.
  -- This means `(¬ P) -> False`.
  -- Hint: use `intro hnp`, then use `hnp hp`.
  intro hnp
  exact hnp hp



theorem exercise_false_elim_pair (P Q : Prop) (hp : P) (hnp : ¬ P) : Q ∧ ¬ Q := by
  -- You can first make `bad : False` using `hnp hp`.
  -- Then use `False.elim bad` for each side of the `and`.
  have bad: False := hnp hp
  constructor
  · exact False.elim bad
  · exact False.elim bad

theorem exercise_eq_substitute_left (a b : Nat) (h : a = b) : a + 2 = b + 2 := by
  -- Equality/rewrite practice.
  -- Hint: use `rw [h]`.
  rw[h]

theorem exercise_eq_substitute_backward (a b : Nat) (h : a = b) : b + 2 = a + 2 := by
  -- Backward rewrite practice.
  -- Hint: use `rw [← h]`.
  rw[← h]

theorem exercise_simp_with_eq (a b : Nat) (h : a = b) : 0 + a + 0 = b := by
  -- Simplification practice.
  -- Hint: use `simp [h]`.
  simp [h]

theorem exercise_not_or_from_not_both (P Q : Prop) (hnp : ¬ P) (hnq : ¬ Q) : ¬ (P ∨ Q) := by
  -- Goal shape: `¬ (P ∨ Q)`, so start with `intro h`.
  -- Then split `h : P ∨ Q` with `cases h`.
  -- In the `P` case, use `hnp`.
  -- In the `Q` case, use `hnq`.
  intro h
  cases h with
  | inl hp =>
    exact hnp hp
  | inr hq =>
    exact hnq hq

end Sandbox.Exercises.LogicLevel3
