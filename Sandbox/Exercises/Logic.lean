namespace Sandbox.Exercises.Logic

-- Replace each `sorry` with a proof when you practice.
-- It is fine to leave `sorry` in this sandbox while learning.

theorem exercise_identity (P : Prop) (h : P) : P := by
  sorry

theorem exercise_swap_and (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  sorry

theorem exercise_swap_or (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  sorry

theorem exercise_chain (P Q R : Prop) (hp : P) (hpq : P -> Q) (hqr : Q -> R) : R := by
  sorry

end Sandbox.Exercises.Logic
