import proofs.MemoryPrediction.SourceLower
import proofs.MemoryPrediction.ScalarCertificate
import proofs.LowFounderPrediction.ProbabilityBudget

namespace MemoryPrediction
noncomputable section
open LowFounderPrediction MeasureTheory CompositionalMemory

def demographicBox (a : Rates) : Prop :=
  (1/10 ≤ a.bS ∧ a.bS ≤ 501/5000) ∧ (1/10 ≤ a.bR ∧ a.bR ≤ 501/5000) ∧
  (1/20 ≤ a.dS ∧ a.dS ≤ 501/10000) ∧ (1/20 ≤ a.dR ∧ a.dR ≤ 501/10000)

def endpointFour : Set State := {x | totalCount x ≤ 4}

/-- A source-connected nonzero-contrast safe class. The bound is conservative:
we retain only histories through count five and sixteen Poisson terms. -/
theorem one_founder_four (a : Rates) (ha : demographicBox a) (x : State)
    (hx : totalCount x = 1) : (963/1000 : ℝ) ≤ (law a x 7).real endpointFour := by
  have h := source_scalar_lower a ha.1.2 ha.2.1.2 ha.2.2.1.1 ha.2.2.2.1 7 x
  have hp : countProjection x = 1 := by simp [countProjection, hx, capCount]
  rw [hp] at h
  have hr := (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mp h
  exact finite_scalar_certificate.trans hr

def preparedSingle (a : Rates) (p : ℝ) : Measure State :=
  Real.toNNReal (1-p) • law a (1,0) 7 + Real.toNNReal p • law a (0,1) 7

instance preparedSingle_finite (a : Rates) (p : ℝ) : IsFiniteMeasure (preparedSingle a p) := by
  unfold preparedSingle
  infer_instance

theorem preparedSingle_lower (a : Rates) (ha : demographicBox a) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (963/1000 : ℝ) ≤ (preparedSingle a p).real endpointFour := by
  have hS := one_founder_four a ha (1,0) (by rfl)
  have hR := one_founder_four a ha (0,1) (by rfl)
  have hp : 0 ≤ 1-p := by linarith
  have hmS := mul_le_mul_of_nonneg_left hS hp
  have hmR := mul_le_mul_of_nonneg_left hR hp0
  unfold preparedSingle
  rw [measureReal_add_apply]
  simp only [measureReal_nnreal_smul_apply, Real.coe_toNNReal p hp0,
    Real.coe_toNNReal (1-p) hp]
  nlinarith

/-- The preparation contract specifies a full source law, not a CDF premise.
Detection may delete arbitrarily; only false objects have a probability budget. -/
theorem observed_four {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → State) (hX : Measurable X)
    (D A : Ω → ℕ) (hD : ∀ ω, D ω ≤ totalCount (X ω))
    (hfalse : μ.real {ω | 0 < A ω} ≤ 1/100)
    (a : Rates) (ha : demographicBox a) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (empty single multiple : NNReal) (hsum : empty+single+multiple=1)
    (hm : (multiple : ℝ) ≤ 1/1000) (bad : Measure State) [IsProbabilityMeasure bad]
    (hprep : μ.map X = empty • Measure.dirac (0,0) +
      single • preparedSingle a p + multiple • bad) :
    (952037/1000000 : ℝ) ≤ μ.real {ω | D ω+A ω ≤ 4} := by
  have hs := preparedSingle_lower a ha p hp0 hp1
  have hsumR : (empty : ℝ)+(single : ℝ)+(multiple : ℝ)=1 := by exact_mod_cast hsum
  have hb := preparation_budget (empty : ℝ) single multiple (963/1000) (1/1000)
    empty.property (by norm_num) (by norm_num) hsumR hm
  have he : (Measure.dirac (0,0) : Measure State).real endpointFour=1 := by
    simp [Measure.real, endpointFour, totalCount]
  have hmap := map_measureReal_apply (μ := μ) hX (Set.to_countable endpointFour).measurableSet
  rw [hprep, measureReal_add_apply, measureReal_add_apply] at hmap
  simp only [measureReal_nnreal_smul_apply, he, mul_one] at hmap
  have hsingle := mul_le_mul_of_nonneg_left hs single.property
  have hbad : 0 ≤ (multiple : ℝ)*bad.real endpointFour :=
    mul_nonneg multiple.property measureReal_nonneg
  have hobs := observed_budget μ (fun ω => totalCount (X ω)) D A 4 hD
  have hlatent : (1-1/1000 : ℝ)*(963/1000) ≤ μ.real {ω | totalCount (X ω) ≤ 4} := by
    have heq : (empty : ℝ)+(single : ℝ)*(preparedSingle a p).real endpointFour+
        (multiple : ℝ)*bad.real endpointFour = μ.real {ω | totalCount (X ω) ≤ 4} := hmap
    calc
      _ ≤ (empty : ℝ)+(single : ℝ)*(963/1000) := hb
      _ ≤ (empty : ℝ)+(single : ℝ)*(preparedSingle a p).real endpointFour :=
        add_le_add (le_refl _) hsingle
      _ ≤ (empty : ℝ)+(single : ℝ)*(preparedSingle a p).real endpointFour+
          (multiple : ℝ)*bad.real endpointFour := le_add_of_nonneg_right hbad
      _ = _ := heq
  linarith

theorem observed_four_margin : (19/20 : ℝ) < 952037/1000000 := by norm_num

end
end MemoryPrediction
