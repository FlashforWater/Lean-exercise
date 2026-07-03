namespace Sandbox.Basic.Tactics

-- Tactics build proof terms interactively.

theorem exact_example (P : Prop) (h : P) : P := by
  exact h

theorem apply_example (P Q : Prop) (h : P) (hpq : P -> Q) : Q := by
  apply hpq
  exact h

theorem constructor_example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

theorem cases_and_example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases h with
  | intro hp hq =>
      constructor
      · exact hq
      · exact hp

theorem cases_or_example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>
      exact Or.inr hp
  | inr hq =>
      exact Or.inl hq

end Sandbox.Basic.Tactics
