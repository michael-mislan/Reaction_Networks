import proofs.CoreCriticalSiphon.Source

namespace CoreCriticalSiphon

variable (Q : SourceCRN)

/-- A literal reaction consumes at least one member of `Σ`. -/
def Consumes (sigma : Finset Q.Species) (r : Q.Reaction) : Prop :=
  ∃ i ∈ sigma, 0 < Q.reactant r i

/-- A literal reaction produces at least one member of `Σ`. -/
def Produces (sigma : Finset Q.Species) (r : Q.Reaction) : Prop :=
  ∃ i ∈ sigma, 0 < Q.product r i

/-- Source-faithful siphon predicate. -/
def IsSiphon (sigma : Finset Q.Species) : Prop :=
  ∀ r, Produces Q sigma r → Consumes Q sigma r

end CoreCriticalSiphon
