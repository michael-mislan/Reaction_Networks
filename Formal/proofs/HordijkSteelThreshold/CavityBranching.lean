import proofs.HordijkSteelThreshold.FamilyOpenProbability
import proofs.HordijkSteelThreshold.FactorCone

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- At least one target in a fixed finite family has every retained reaction
closed against the catalyst pool.  This is the one-generation bad event in
the cavity exploration. -/
def someCatalystPoolFamilyClosed {n : Nat} {ι : Type*}
    (ω : AmbientCoord n → Prop) (C : Finset (Molecule n))
    (T : Finset ι) (R : ι → Finset (Reaction n)) : Prop :=
  ∃ i ∈ T, ¬catalystPoolFamilyOpen ω C (R i)

/-- A dependence-safe union bound for one cavity generation.  The reaction
families may overlap arbitrarily: only the individual lower cardinality bound
is used. -/
theorem measure_someCatalystPoolFamilyClosed_le {n d : Nat} {ι : Type*}
    [DecidableEq ι] (lambda : ℝ) (C : Finset (Molecule n))
    (T : Finset ι) (R : ι → Finset (Reaction n))
    (hcard : ∀ i ∈ T, d ≤ (R i).card) :
    ambientPiMeasure n lambda
        {ω | someCatalystPoolFamilyClosed ω C T R} ≤
      (T.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (C.card * d) := by
  classical
  rw [show {ω | someCatalystPoolFamilyClosed ω C T R} =
      ⋃ i ∈ T, {ω | ¬catalystPoolFamilyOpen ω C (R i)} by
        ext ω
        simp [someCatalystPoolFamilyClosed]]
  calc
    ambientPiMeasure n lambda
          (⋃ i ∈ T, {ω | ¬catalystPoolFamilyOpen ω C (R i)}) ≤
        ∑ i ∈ T, ambientPiMeasure n lambda
          {ω | ¬catalystPoolFamilyOpen ω C (R i)} :=
      measure_biUnion_finset_le T _
    _ ≤ ∑ _i ∈ T,
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (C.card * d) := by
      exact Finset.sum_le_sum fun i hi =>
        measure_catalystPoolFamilyClosed_le lambda C (R i) (hcard i hi)
    _ = (T.card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (C.card * d) := by simp

/-- The one-generation bad-event bound specialized to descendants in the raw
factor cone of one deleted word.  No descendant independence is used. -/
theorem measure_fixedFactorConeFamilyClosed_le {n i j d : Nat}
    (lambda : ℝ) (C : Finset (Molecule n)) (u : Word i)
    (R : Word (i + j) → Finset (Reaction n))
    (hcard : ∀ x ∈ fixedFactorCone (j := j) u, d ≤ (R x).card) :
    ambientPiMeasure n lambda
        {ω | someCatalystPoolFamilyClosed ω C
          (fixedFactorCone (j := j) u) R} ≤
      ((2 * 2 ^ j : Nat) : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (C.card * d) := by
  calc
    ambientPiMeasure n lambda
        {ω | someCatalystPoolFamilyClosed ω C
          (fixedFactorCone (j := j) u) R} ≤
      ((fixedFactorCone (j := j) u).card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (C.card * d) :=
      measure_someCatalystPoolFamilyClosed_le lambda C
        (fixedFactorCone (j := j) u) R hcard
    _ ≤ ((2 * 2 ^ j : Nat) : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (C.card * d) := by
      gcongr
      exact_mod_cast card_fixedFactorCone_le (j := j) u

/-- One-generation bound for an arbitrary deleted set in one factor layer.
After division by the target-layer cardinality, the deterministic prefactor is
at most twice the deleted-layer density, uniformly in the later gap `j`. -/
theorem measure_deletedFactorConeFamilyClosed_le {n i j d : Nat}
    (lambda : ℝ) (C : Finset (Molecule n)) (D : Finset (Word i))
    (R : Word (i + j) → Finset (Reaction n))
    (hcard : ∀ x ∈ D.biUnion (fun u => fixedFactorCone (j := j) u),
      d ≤ (R x).card) :
    ambientPiMeasure n lambda
        {ω | someCatalystPoolFamilyClosed ω C
          (D.biUnion fun u => fixedFactorCone (j := j) u) R} ≤
      ((D.card * (2 * 2 ^ j) : Nat) : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (C.card * d) := by
  calc
    ambientPiMeasure n lambda
        {ω | someCatalystPoolFamilyClosed ω C
          (D.biUnion fun u => fixedFactorCone (j := j) u) R} ≤
      ((D.biUnion fun u => fixedFactorCone (j := j) u).card : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (C.card * d) :=
      measure_someCatalystPoolFamilyClosed_le lambda C
        (D.biUnion fun u => fixedFactorCone (j := j) u) R hcard
    _ ≤ ((D.card * (2 * 2 ^ j) : Nat) : ENNReal) *
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
          (C.card * d) := by
      gcongr
      exact_mod_cast card_biUnion_fixedFactorCone_le (j := j) D

end HordijkSteelThreshold
