import proofs.ThermoCoreCompatibility.Examples.PaperIncompatiblePair
import proofs.ThermoCoreCompatibility.Examples.MagnitudeObstructionPair
import proofs.ThermoCoreCompatibility.Examples.TrianglePhaseDiagram
import proofs.ThermoCoreCompatibility.Examples.ToricObstructionPair
import proofs.ThermoCoreCompatibility.InterfaceProfile

namespace ThermoCoreCompatibility

theorem paperPair_source_equations_incompatible
    {barrier : PaperPair.Reaction → ℝ} {hbarrier : ∀ r, 0 < barrier r}
    (z : PaperPair.Species → ℝ) (hz : ∀ s, 0 < z s)
    (hL : (PaperPair.leftMotif (barrier := barrier) (hbarrier := hbarrier)).Productive
      ((PaperPair.network barrier hbarrier).current z))
    (hR : (PaperPair.rightMotif (barrier := barrier) (hbarrier := hbarrier)).Productive
      ((PaperPair.network barrier hbarrier).current z)) : False :=
  PaperPair.no_common_thermodynamic_witness z hz hL hR

theorem source_valid_multiPAC_not_multiCAC
    {barrier : PaperPair.Reaction → ℝ} {hbarrier : ∀ r, 0 < barrier r} :
    (PaperPair.paperFamily (barrier := barrier) (hbarrier := hbarrier)).MultiPAC ∧
      ¬ (PaperPair.paperFamily (barrier := barrier) (hbarrier := hbarrier)).MultiCAC :=
  PaperPair.paperPair_multiPAC_not_multiCAC

theorem source_valid_strongCompatibility_counterexample :
    MagnitudePair.family.MultiPAC ∧
      MagnitudePair.family.DirectionCompatible ∧
      ¬ MagnitudePair.family.MultiCAC :=
  MagnitudePair.strongCompatibility_counterexample

/-- Existential, science-facing form of the magnitude-only counterexample. -/
theorem exists_sourceValid_magnitudeIncompatible_pair :
    ∃ F : CoreFamily (Core := MagnitudePair.Core) MagnitudePair.network,
      F.MultiPAC ∧ F.DirectionCompatible ∧ ¬ F.MultiCAC :=
  ⟨MagnitudePair.family, MagnitudePair.strongCompatibility_counterexample⟩

/-- The fixed magnitude obstruction already fails before the toric monomial
realization constraint is imposed. -/
theorem sourceValid_nonToric_magnitudeObstruction :
    MagnitudePair.family.MultiPAC ∧
      MagnitudePair.family.DirectionCompatible ∧
      ¬ MagnitudePair.family.LinearComplexCompatible :=
  MagnitudePair.magnitudeObstruction_is_nonToric

/-- Exact barrier phase diagram for the two-triangle assembly. -/
theorem magnitudePair_multiCAC_iff (k : ℝ) (hk : 0 < k) :
    TrianglePhaseDiagram.PairMultiCAC k hk ↔ 1 / 2 < k ∧ k < 2 :=
  TrianglePhaseDiagram.pairMultiCAC_iff_window k hk

/-- Publication-facing literal form: PAC minimality, common productive flow,
direction compatibility, and the exact CAC window are stated on the same
parameterized source family. -/
theorem triangleFamily_complete_phaseDiagram (k : ℝ) (hk : 0 < k) :
    (TrianglePhaseDiagram.familyAt k hk).MultiPAC ∧
      (TrianglePhaseDiagram.familyAt k hk).DirectionCompatible ∧
      ((TrianglePhaseDiagram.familyAt k hk).MultiCAC ↔
        1 / 2 < k ∧ k < 2) :=
  TrianglePhaseDiagram.familyAt_complete_phaseDiagram k hk

/-- Publication-facing source adapter: the scalar interval is exactly the
projection of the literal barrier-weighted productive-current equations. -/
theorem literalTriangle_interfaceProjection {m b₀ b₁ b₂ q : ℝ}
    (hm : 1 < m) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) :
    InterfaceProfile.LiteralBarrierTriangleResponse m b₀ b₁ b₂ q ↔
      b₀ * (1 / b₁ + 1 / b₂) / m < q ∧
        q < b₀ * (1 / b₁ + 1 / b₂) :=
  InterfaceProfile.literalBarrierTriangleResponse_iff_interval hm hb₀ hb₁ hb₂

/-- A smaller source-minimal pair reaches the genuinely toric obstruction
layer: independent complex activities work, but common species activities do
not. -/
theorem exists_sourceValid_genuineToricIncompatible_pair :
    ∃ F : CoreFamily (Core := ToricPair.Core) ToricPair.network,
      F.MultiPAC ∧ F.DirectionCompatible ∧
        F.LinearComplexCompatible ∧ ¬ F.MultiCAC :=
  ⟨ToricPair.family, ToricPair.genuineToricObstruction⟩

/-- Strong Compatibility is false already on the fixed five-reaction network:
not every source-valid family with a common productive oriented flow and a
strict direction potential has a common thermodynamic activity realization. -/
theorem strongCompatibility_refuted :
    ¬ (∀ F : CoreFamily (Core := MagnitudePair.Core) MagnitudePair.network,
      F.MultiPAC → F.DirectionCompatible → F.MultiCAC) := by
  intro h
  exact MagnitudePair.family_not_multiCAC
    (h MagnitudePair.family MagnitudePair.family_multiPAC
      MagnitudePair.family_directionCompatible)

end ThermoCoreCompatibility
