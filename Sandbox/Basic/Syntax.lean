namespace Sandbox.Basic.Syntax

-- Evaluate expressions with `#eval`.
#eval 1 + 2
#eval "Lean " ++ "sandbox"

-- Define values with `def`.
def double (n : Nat) : Nat :=
  n + n

#eval double 5

-- Functions can be written with pattern matching.
def isZero : Nat -> Bool
  | 0 => true
  | _ + 1 => false

#eval isZero 0
#eval isZero 7

-- Structures are records with named fields.
structure Learner where
  name : String
  lessonsFinished : Nat
deriving Repr

def you : Learner :=
  { name := "sfffpanda", lessonsFinished := 0 }

#eval you

end Sandbox.Basic.Syntax
