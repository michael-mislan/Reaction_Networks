import Mathlib

namespace CoreCriticalSiphon

/-- A finite, literal source representation of a chemical reaction network.
Reactant and product complexes are retained separately; `catalyst` records
explicit source incidence even when net stoichiometry cancels it. -/
structure SourceCRN where
  Species : Type
  Reaction : Type
  [speciesFintype : Fintype Species]
  [reactionFintype : Fintype Reaction]
  [speciesDecidableEq : DecidableEq Species]
  [reactionDecidableEq : DecidableEq Reaction]
  reactant : Reaction → Species → ℕ
  product : Reaction → Species → ℕ
  catalyst : Reaction → Species → Bool

attribute [instance] SourceCRN.speciesFintype SourceCRN.reactionFintype
  SourceCRN.speciesDecidableEq SourceCRN.reactionDecidableEq

namespace SourceCRN

variable (Q : SourceCRN)

/-- The literal mass-action monomial of one reaction. -/
def monomial (r : Q.Reaction) (x : Q.Species → ℝ) : ℝ :=
  ∏ i, x i ^ Q.reactant r i

/-- The contribution of one literal reaction to one species coordinate. -/
def reactionField (r : Q.Reaction) (k : ℝ) (x : Q.Species → ℝ)
    (i : Q.Species) : ℝ :=
  k * Q.monomial r x * ((Q.product r i : ℝ) - Q.reactant r i)

/-- The full mass-action vector field. -/
def massAction (k : Q.Reaction → ℝ) (x : Q.Species → ℝ) (i : Q.Species) : ℝ :=
  ∑ r, Q.reactionField r (k r) x i

end SourceCRN

end CoreCriticalSiphon
