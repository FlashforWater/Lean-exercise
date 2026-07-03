namespace Sandbox.Basic.Propositions

-- In Lean, propositions are types, and proofs are values of those types.

theorem identity_example (P : Prop) (h : P) : P :=
  h

theorem implication_example (P Q : Prop) (hp : P) (hpq : P -> Q) : Q :=
  hpq hp

theorem and_intro_example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
  And.intro hp hq

theorem and_left_example (P Q : Prop) (h : P ∧ Q) : P :=
  h.left

theorem and_right_example (P Q : Prop) (h : P ∧ Q) : Q :=
  h.right

theorem or_left_example (P Q : Prop) (hp : P) : P ∨ Q :=
  Or.inl hp

theorem or_elim_example (P Q R : Prop) (h : P ∨ Q) (hp : P -> R) (hq : Q -> R) : R :=
  Or.elim h hp hq

end Sandbox.Basic.Propositions
