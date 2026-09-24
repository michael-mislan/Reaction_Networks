import proofs.RAFReactionQuotient.ORDistribution
import proofs.RAFReactionQuotient.SplitAdapter

namespace RAFReactionQuotient
open Classical MeasureTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

def coordinateProjection {n : ℕ} (z : Molecule n × Reaction n) :
    Molecule n × RepositoryChannel n := (z.1,splitToQuotient z.2)

theorem coordinateProjection_OR {n : ℕ} (ω : (Molecule n × Reaction n) → Prop)
    (x : Molecule n) (j : RepositoryChannel n) :
    fieldOR coordinateProjection ω (x,j) ↔
      orCatalysis splitToQuotient (fun y r => ω (y,r)) x j := by
  constructor
  · rintro ⟨⟨y,r⟩,he,ho⟩
    have hy : y = x := congrArg Prod.fst he
    have hr : splitToQuotient r = j := congrArg Prod.snd he
    subst y
    exact ⟨r,hr,ho⟩
  · rintro ⟨r,hr,ho⟩
    exact ⟨(x,r),Prod.ext rfl hr,ho⟩

/-- The iid molecule-by-split-channel law maps to an independent, generally
inhomogeneous molecule-by-quotient-channel law. -/
theorem catalytic_OR_distribution (n : ℕ) (p : I) :
    (RAFEmergenceApprox.Generic.colLaw (Molecule n × Reaction n) p).map
      (fieldOR coordinateProjection) =
      Measure.pi (fun z : Molecule n × RepositoryChannel n =>
        ambientCoordLaw (fibreParameter coordinateProjection p z)) :=
  fieldOR_map coordinateProjection p

end RAFReactionQuotient
