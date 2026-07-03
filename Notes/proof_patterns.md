# Lean Proof Patterns

## When The Goal Is Already In The Context

Use `exact`.

```lean
example (P : Prop) (h : P) : P := by
  exact h
```

## When The Goal Is An Implication

Introduce the assumption.

```lean
example (P Q : Prop) : P -> Q -> P := by
  intro hp
  intro _hq
  exact hp
```

## When The Goal Is `P ∧ Q`

Use `constructor`.

```lean
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq
```

## When You Have `P ∧ Q`

Use `.left`, `.right`, or `cases`.

```lean
example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.right
```

## When You Have `P ∨ Q`

Use `cases`, because either side could be true.

```lean
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq
```
