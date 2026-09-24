import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

namespace MemoryPrediction
noncomputable section
open MeasureTheory

/-- One latent draw per family, marginalized before combining founders. -/
def familyMixture {Ω : Type*} [MeasurableSpace Ω] (slow fast : Measure Ω) : Measure Ω :=
  (1/2 : NNReal) • slow + (1/2 : NNReal) • fast

instance familyMixture_probability {Ω : Type*} [MeasurableSpace Ω]
    (slow fast : Measure Ω) [IsProbabilityMeasure slow] [IsProbabilityMeasure fast] :
    IsProbabilityMeasure (familyMixture slow fast) := by
  constructor
  simp [familyMixture, Measure.add_apply, Measure.smul_apply]
  exact ENNReal.inv_two_add_inv_two

/-- The sample space Ω can be the full family trajectory/tree space. -/
def independentFamilies {Ω : Type*} [MeasurableSpace Ω] (slow fast : Measure Ω) :=
  (familyMixture slow fast).prod (familyMixture slow fast)

/-- Draw a common well state, then independently draw the two conditional families. -/
def sharedFamilies {Ω : Type*} [MeasurableSpace Ω] (slow fast : Measure Ω) :=
  (1/2 : NNReal) • slow.prod slow + (1/2 : NNReal) • fast.prod fast

theorem single_founder_law_equal {Ω : Type*} [MeasurableSpace Ω]
    (slow fast : Measure Ω) [IsProbabilityMeasure slow] [IsProbabilityMeasure fast] :
    (independentFamilies slow fast).map Prod.fst =
      (sharedFamilies slow fast).map Prod.fst := by
  have hI : (independentFamilies slow fast).map Prod.fst = familyMixture slow fast := by
    simp [independentFamilies]
  rw [hI]
  simp [sharedFamilies, Measure.map_add, Measure.map_smul, measurable_fst,
    familyMixture]

/-- Every measurable refinement of a single family has the same law, not only
finitely many summaries. The equality holds even for arbitrary maps, since map
is defined for them; applications use the actual measurable observation map. -/
theorem single_observation_law_equal {Ω O : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
    (slow fast : Measure Ω) [IsProbabilityMeasure slow] [IsProbabilityMeasure fast]
    (observe : Ω → O) :
    ((independentFamilies slow fast).map Prod.fst).map observe =
      ((sharedFamilies slow fast).map Prod.fst).map observe := by
  rw [single_founder_law_equal]

theorem shared_minus_independent_rectangle {Ω : Type*} [MeasurableSpace Ω]
    (slow fast : Measure Ω) [IsProbabilityMeasure slow] [IsProbabilityMeasure fast]
    (s : Set Ω) :
    (sharedFamilies slow fast).real (s ×ˢ s) -
      (independentFamilies slow fast).real (s ×ˢ s) =
        (slow.real s - fast.real s)^2/4 := by
  have hp (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
      (μ.prod ν).real (s ×ˢ s) = μ.real s * ν.real s := by
    simp [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  unfold sharedFamilies independentFamilies
  rw [measureReal_add_apply]
  simp only [measureReal_nnreal_smul_apply, hp]
  unfold familyMixture
  rw [measureReal_add_apply]
  simp only [measureReal_nnreal_smul_apply]
  norm_num
  ring

end
end MemoryPrediction
