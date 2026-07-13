import Sandbox.Basic.Syntax

namespace Sandbox.Exercises.CalculationLevel1

/-!
Calculation practice, level 1.

This is a bridge toward Mathematics in Lean.

New tools:

- `calc` for readable equality chains
- `show` for telling Lean the exact goal you want to prove now
- `rw` for a specific equality rewrite
- `simp` for simple cleanup
-/

/-!
Example: `calc` lets you prove equality step by step.
-/
example : Sandbox.Basic.Syntax.double 3 = 6 := by
  calc
    Sandbox.Basic.Syntax.double 3 = 3 + 3 := by rfl
    _ = 6 := by rfl

/-!
Example: `show` can make the current goal explicit.
-/
example (a b : Nat) (h : a = b) : a + 0 = b := by
  show a + 0 = b
  simp [h]

/-!
Exercise 1.
-/
theorem exercise_calc_double_four : Sandbox.Basic.Syntax.double 4 = 8 := by
  -- Hint: copy the shape of the `calc` example above.
  calc
    Sandbox.Basic.Syntax.double 4 = 4 + 4 := by rfl
    _ = 8 := by rfl

/-!
Exercise 2.
-/
theorem exercise_calc_add_zero (a b : Nat) (h : a = b) : a + 0 = b := by
  -- Hint: try a two-line `calc`:
  -- `a + 0 = b + 0 := by rw [h]`
  -- `_ = b := by simp`
  calc
    a + 0 = b + 0:= by rw [h]
    _ = b := by simp

/-!
Exercise 3.
-/
theorem exercise_calc_double_eq (a b : Nat) (h : a = b) :
    Sandbox.Basic.Syntax.double a = Sandbox.Basic.Syntax.double b := by
  -- Hint: use `calc` and one `rw [h]` step.
  calc
    Sandbox.Basic.Syntax.double a = Sandbox.Basic.Syntax.double b := by rw [h]

/-!
Exercise 4.
-/
theorem exercise_show_then_constructor (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  -- Hint: first write `show P ∧ Q`.
  -- Then solve the `and` goal.
  show P ∧ Q
  constructor
  · exact hp
  · exact hq

/-!
Exercise 5.
-/
theorem exercise_calc_with_named_fact (a b : Nat) (h : a = b) :
    0 + Sandbox.Basic.Syntax.double a = Sandbox.Basic.Syntax.double b := by
  -- Hint:
  -- First make a fact:
  -- `have hd : Sandbox.Basic.Syntax.double a = Sandbox.Basic.Syntax.double b := by rw [h]`
  -- Then use `calc` or `simp [hd]`.
  have hd: Sandbox.Basic.Syntax.double a = Sandbox.Basic.Syntax.double b := by rw [h]
  calc
    0 + Sandbox.Basic.Syntax.double a = Sandbox.Basic.Syntax.double a := by simp
    _ = Sandbox.Basic.Syntax.double b := by exact hd


end Sandbox.Exercises.CalculationLevel1
