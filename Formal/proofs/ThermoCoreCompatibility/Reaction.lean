import Mathlib

/-! Literal reversible reactions and the fixed-barrier thermodynamic current. -/

namespace ThermoCoreCompatibility

open scoped BigOperators

abbrev Complex (Species : Type*) := Species → ℕ

structure ReversibleCRN (Species Reaction : Type*) where
  reactant : Reaction → Complex Species
  product : Reaction → Complex Species
  barrier : Reaction → ℝ
  barrier_pos : ∀ r, 0 < barrier r

namespace ReversibleCRN

variable {Species Reaction : Type*}

def stoich (Q : ReversibleCRN Species Reaction) (s : Species) (r : Reaction) : ℤ :=
  (Q.product r s : ℤ) - (Q.reactant r s : ℤ)

def complexActivity [Fintype Species] (z : Species → ℝ) (c : Complex Species) : ℝ :=
  ∏ s, z s ^ c s

def current [Fintype Species] (Q : ReversibleCRN Species Reaction)
    (z : Species → ℝ) (r : Reaction) : ℝ :=
  Q.barrier r * (complexActivity z (Q.reactant r) - complexActivity z (Q.product r))

end ReversibleCRN

end ThermoCoreCompatibility
