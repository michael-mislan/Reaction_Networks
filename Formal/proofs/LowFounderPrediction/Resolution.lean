import proofs.LowFounderPrediction.ChronologicalBridge
import proofs.LowFounderPrediction.RobustConstants
import proofs.LowFounderPrediction.ProbabilityBudget

namespace LowFounderPrediction
noncomputable section
open Classical MeasureTheory
open scoped ENNReal

def good : Set State := {x | x.1+x.2 ≤ 3}

def oneFounder (a : Rates) (p : ℝ) : Measure State :=
  Real.toNNReal (1-p) • law a (1,0) horizon +
  Real.toNNReal p • law a (0,1) horizon

instance oneFounder_finite (a : Rates) (p : ℝ) : IsFiniteMeasure (oneFounder a p) := by
  unfold oneFounder
  infer_instance

theorem one_founder_history_lower (a : Rates) (ha : RateBall a) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1-p)*sensitiveLower+p*resistantLower ≤ (oneFounder a p).real good := by
  have hS := source_lower a (rate_ball_admissible a ha) horizon (1,0)
  have hR := source_lower a (rate_ball_admissible a ha) horizon (0,1)
  have hSr : sensitiveLower ≤ (law a (1,0) horizon).real good := by
    have hh := (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mp hS
    simpa [observe, value, good] using hh
  have hRr : resistantLower ≤ (law a (0,1) horizon).real good := by
    have hh := (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mp hR
    have hh' : value horizon 2 ≤ (law a (0,1) horizon).real good := by
      simpa [observe, good] using hh
    exact resistant_value_lower.trans hh'
  have hm := add_le_add (mul_le_mul_of_nonneg_left hSr (by linarith : 0 ≤ 1-p))
    (mul_le_mul_of_nonneg_left hRr hp0)
  calc
    _ ≤ (1-p)*(law a (1,0) horizon).real good+p*(law a (0,1) horizon).real good := hm
    _ = (oneFounder a p).real good := by
      unfold oneFounder
      rw [measureReal_add_apply]
      simp [Real.toNNReal_of_nonneg hp0, Real.toNNReal_of_nonneg (by linarith : 0 ≤ 1-p)]

theorem one_founder_lower (a : Rates) (ha : RateBall a) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : p ≤ 5/24+1/1000) :
    (57461421889141/60212040602000 : ℝ)+11/1000 ≤ (oneFounder a p).real good :=
  (history_mixture_constant p hp0 hp).trans (one_founder_history_lower a ha p hp0 hp1)

def singleLower : ℝ := (1-(5/24+1/1000))*sensitiveLower+(5/24+1/1000)*resistantLower

theorem singleLower_bounds : 0 ≤ singleLower ∧ singleLower ≤ 1 := by
  norm_num [singleLower, sensitiveLower, resistantLower, c]

theorem one_founder_sharp (a : Rates) (ha : RateBall a) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : p ≤ 5/24+1/1000) :
    singleLower ≤ (oneFounder a p).real good := by
  have h := one_founder_history_lower a ha p hp0 hp1
  norm_num [singleLower, sensitiveLower, resistantLower, c] at *
  linarith

/-- Unrestricted bad-founder outcome law; only its mixture mass is controlled. -/
def assay (a : Rates) (p : ℝ) (empty single multiple : NNReal) (bad : Measure State) :
    Measure State :=
  empty • Measure.dirac (0,0) + single • oneFounder a p + multiple • bad

theorem assay_lower (a : Rates) (ha : RateBall a) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : p ≤ 5/24+1/1000)
    (empty single multiple : NNReal) (hsum : empty+single+multiple = 1)
    (hmulti : (multiple : ℝ) ≤ 1/1000) (bad : Measure State) [IsProbabilityMeasure bad] :
    (57461421889141/60212040602000 : ℝ)+1/100 ≤
      (assay a p empty single multiple bad).real good := by
  have hsumR : (empty : ℝ)+(single : ℝ)+(multiple : ℝ) = 1 := by exact_mod_cast hsum
  have h0 := empty.property
  have h1 := single.property
  have hb := multiple.property
  have hsingle : (single : ℝ) ≤ 1 := by linarith
  have hl := one_founder_lower a ha p hp0 hp1 hp
  have hm := mul_le_mul_of_nonneg_left hl h1
  have hbad : 0 ≤ (multiple : ℝ)*bad.real good := mul_nonneg hb measureReal_nonneg
  have he : (Measure.dirac (0,0) : Measure State).real good = 1 := by
    simp [Measure.real, good]
  have heval : (assay a p empty single multiple bad).real good =
      (empty : ℝ)+(single : ℝ)*(oneFounder a p).real good+(multiple : ℝ)*bad.real good := by
    unfold assay
    rw [measureReal_add_apply, measureReal_add_apply]
    simp [he]
  rw [heval]
  nlinarith

/-- Complete source-derived observed-count robustness for fixed admitted rates.
`hprep` specifies the full latent endpoint law, not a coverage bound.
Deletions and false objects may depend on the entire outcome. -/
theorem robust_endpoint_three {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → State) (hX : Measurable X)
    (D A : Ω → ℕ) (hD : ∀ ω, D ω ≤ (X ω).1+(X ω).2)
    (hfalse : μ.real {ω | 0 < A ω} ≤ 1/100)
    (a : Rates) (ha : RateBall a) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : |p-5/24| ≤ 1/1000)
    (empty single multiple : NNReal) (hsum : empty+single+multiple = 1)
    (hmulti : (multiple : ℝ) ≤ 1/1000) (bad : Measure State) [IsProbabilityMeasure bad]
    (hprep : μ.map X = assay a p empty single multiple bad) :
    57461421889141/60212040602000 ≤ μ.real {ω | D ω+A ω ≤ 3} := by
  have hpU : p ≤ 5/24+1/1000 := by have := (abs_le.mp hp).2; linarith
  have hl := assay_lower a ha p hp0 hp1 hpU empty single multiple hsum hmulti bad
  rw [← hprep, map_measureReal_apply hX (Set.to_countable good).measurableSet] at hl
  have hb := observed_budget μ (fun ω => (X ω).1+(X ω).2) D A 3 hD
  change (57461421889141/60212040602000 : ℝ)+1/100 ≤
    μ.real {ω | (X ω).1+(X ω).2 ≤ 3} at hl
  linarith

theorem assay_sharp (a : Rates) (ha : RateBall a) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : p ≤ 5/24+1/1000)
    (empty single multiple : NNReal) (hsum : empty+single+multiple = 1)
    (γ : ℝ) (hmulti : (multiple : ℝ) ≤ γ) (bad : Measure State) [IsProbabilityMeasure bad] :
    (1-γ)*singleLower ≤ (assay a p empty single multiple bad).real good := by
  have hsumR : (empty : ℝ)+(single : ℝ)+(multiple : ℝ) = 1 := by exact_mod_cast hsum
  have hm := mul_le_mul_of_nonneg_left (one_founder_sharp a ha p hp0 hp1 hp) single.property
  have hbad : 0 ≤ (multiple : ℝ)*bad.real good := mul_nonneg multiple.property measureReal_nonneg
  have he : (Measure.dirac (0,0) : Measure State).real good = 1 := by simp [Measure.real, good]
  have hb := preparation_budget (empty : ℝ) single multiple singleLower γ empty.property
    singleLower_bounds.1 singleLower_bounds.2 hsumR hmulti
  unfold assay
  rw [measureReal_add_apply, measureReal_add_apply]
  simp only [measureReal_nnreal_smul_apply, he, mul_one]
  exact hb.trans ((add_le_add (le_refl (empty : ℝ)) hm).trans (le_add_of_nonneg_right hbad))

theorem robust_endpoint_three_budget {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → State) (hX : Measurable X)
    (D A : Ω → ℕ) (hD : ∀ ω, D ω ≤ (X ω).1+(X ω).2)
    (γ η : ℝ) (hfalse : μ.real {ω | 0 < A ω} ≤ η)
    (a : Rates) (ha : RateBall a) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : |p-5/24| ≤ 1/1000)
    (empty single multiple : NNReal) (hsum : empty+single+multiple = 1)
    (hmulti : (multiple : ℝ) ≤ γ) (bad : Measure State) [IsProbabilityMeasure bad]
    (hprep : μ.map X = assay a p empty single multiple bad) :
    max 0 ((1-γ)*singleLower-η) ≤ μ.real {ω | D ω+A ω ≤ 3} := by
  have hpU : p ≤ 5/24+1/1000 := by have := (abs_le.mp hp).2; linarith
  have hl := assay_sharp a ha p hp0 hp1 hpU empty single multiple hsum γ hmulti bad
  rw [← hprep, map_measureReal_apply hX (Set.to_countable good).measurableSet] at hl
  have hb := observed_budget μ (fun ω => (X ω).1+(X ω).2) D A 3 hD
  change (1-γ)*singleLower ≤ μ.real {ω | (X ω).1+(X ω).2 ≤ 3} at hl
  exact max_le measureReal_nonneg (by linarith)

theorem sharp_constant :
    (1-(1/1000 : ℝ))*singleLower-1/100 =
      6470259728405606661/6768514267000000000 := by
  norm_num [singleLower, sensitiveLower, resistantLower, c]

end
end LowFounderPrediction
