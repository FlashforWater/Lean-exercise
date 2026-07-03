import Sandbox.Basic.Syntax

namespace Sandbox.Exercises.NaturalNumbers

def triple (n : Nat) : Nat :=
  n + n + n

#eval triple 4

-- Some simple computation proofs close with `rfl`, because both sides reduce
-- to the same normal form.
theorem zero_add_by_reduction : 0 + 3 = 3 := by
  rfl

theorem exercise_double_zero : Sandbox.Basic.Syntax.double 0 = 0 := by
  sorry

theorem exercise_triple_two : triple 2 = 6 := by
  sorry

end Sandbox.Exercises.NaturalNumbers
