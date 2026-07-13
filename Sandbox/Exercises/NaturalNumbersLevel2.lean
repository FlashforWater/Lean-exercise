import Sandbox.Basic.Syntax
import Sandbox.Exercises.NaturalNumbers

namespace Sandbox.Exercises.NaturalNumbersLevel2

/-!
Natural number practice, level 2.

Theme:

- use `rfl` when both sides compute to the same value
- use `rw [h]` when you have an equality hypothesis
- use `simp` for cleanup like `n + 0`
- use your own definitions inside proofs
-/

def quadruple (n : Nat) : Nat :=
  n + n + n + n

#eval quadruple 3

theorem exercise_quadruple_two : quadruple 2 = 8 := by
  -- Hint: both sides compute to the same number.
  rfl

theorem exercise_double_eq (a b : Nat) (h : a = b) :
    Sandbox.Basic.Syntax.double a = Sandbox.Basic.Syntax.double b := by
  -- Hint: rewrite using `h`.
  rw [h]

theorem exercise_triple_eq (a b : Nat) (h : a = b) :
    Sandbox.Exercises.NaturalNumbers.triple a = Sandbox.Exercises.NaturalNumbers.triple b := by
  -- Hint: rewrite using `h`.
  rw [h]

theorem exercise_add_zero_after_rewrite (a b : Nat) (h : a = b) :
    a + 0 = b := by
  -- Hint: `simp [h]` can rewrite and simplify.
  simp [h]

theorem exercise_zero_add_after_rewrite (a b : Nat) (h : a = b) :
    0 + a = b := by
  -- Hint: `simp [h]`.
  simp [h]

theorem exercise_package_equalities (a b : Nat) (h : a = b) :
    a + 0 = b ∧ Sandbox.Basic.Syntax.double a = Sandbox.Basic.Syntax.double b := by
  -- Goal shape: an `and`.
  -- Hint: use `constructor`.
  -- First side: `simp [h]`.
  -- Second side: `rw [h]`.
  constructor
  · simp [h]
  · rw [h]

end Sandbox.Exercises.NaturalNumbersLevel2
