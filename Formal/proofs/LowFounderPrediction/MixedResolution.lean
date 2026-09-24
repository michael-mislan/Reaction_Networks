import proofs.LowFounderPrediction.Resolution
import Mathlib.Probability.Kernel.Composition.MeasureComp

namespace LowFounderPrediction
noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Mixing happens after the conditional one-founder source law is constructed.
No independence between the shared condition and the founder type is asserted. -/
theorem mixed_one_founder_lower {U : Type*} [MeasurableSpace U]
    (ν : Measure U) [IsProbabilityMeasure ν] (κ : Kernel U State) [IsMarkovKernel κ]
    (a : U → Rates) (p : U → ℝ) (ha : ∀ u, RateBall (a u))
    (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hp : ∀ u, |p u-5/24| ≤ 1/1000)
    (hκ : ∀ u, κ u = oneFounder (a u) (p u)) :
    (57461421889141/60212040602000 : ℝ)+11/1000 ≤ (κ ∘ₘ ν).real good := by
  have hpoint (u : U) :
      ENNReal.ofReal ((57461421889141/60212040602000 : ℝ)+11/1000) ≤ κ u good := by
    have hpU : p u ≤ 5/24+1/1000 := by have := (abs_le.mp (hp u)).2; linarith
    have h := one_founder_lower (a u) (ha u) (p u) (hp0 u) (hp1 u) hpU
    rw [← hκ u] at h
    exact (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mpr h
  have h := lintegral_mono hpoint (μ := ν)
  have he : (κ ∘ₘ ν) good = ∫⁻ u, κ u good ∂ν :=
    Measure.bind_apply (Set.to_countable good).measurableSet κ.aemeasurable
  simp only [lintegral_const, measure_univ, mul_one] at h
  rw [← he] at h
  exact (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mp h

/-- The guide's optional shared-condition extension, with global bad-founder and
false-object budgets. The mixing law is the condition law among single founders. -/
theorem robust_endpoint_three_mixed {Ω U : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → State) (hX : Measurable X)
    (D A : Ω → ℕ) (hD : ∀ ω, D ω ≤ (X ω).1+(X ω).2)
    (hfalse : μ.real {ω | 0 < A ω} ≤ 1/100)
    (ν : Measure U) [IsProbabilityMeasure ν] (κ : Kernel U State) [IsMarkovKernel κ]
    (a : U → Rates) (p : U → ℝ) (ha : ∀ u, RateBall (a u))
    (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hp : ∀ u, |p u-5/24| ≤ 1/1000)
    (hκ : ∀ u, κ u = oneFounder (a u) (p u))
    (empty single multiple : NNReal) (hsum : empty+single+multiple = 1)
    (hmulti : (multiple : ℝ) ≤ 1/1000) (bad : Measure State) [IsProbabilityMeasure bad]
    (hprep : μ.map X = empty • Measure.dirac (0,0) + single • (κ ∘ₘ ν) + multiple • bad) :
    57461421889141/60212040602000 ≤ μ.real {ω | D ω+A ω ≤ 3} := by
  have hl := mixed_one_founder_lower ν κ a p ha hp0 hp1 hp hκ
  have hsumR : (empty : ℝ)+(single : ℝ)+(multiple : ℝ) = 1 := by exact_mod_cast hsum
  have h0 := empty.property
  have h1 := single.property
  have hb := multiple.property
  have hm := mul_le_mul_of_nonneg_left hl h1
  have hbad : 0 ≤ (multiple : ℝ)*bad.real good := mul_nonneg hb measureReal_nonneg
  have he : (Measure.dirac (0,0) : Measure State).real good = 1 := by
    simp [Measure.real, good]
  have heval : μ.real {ω | (X ω).1+(X ω).2 ≤ 3} =
      (empty : ℝ)+(single : ℝ)*(κ ∘ₘ ν).real good+(multiple : ℝ)*bad.real good := by
    have hmap := map_measureReal_apply (μ := μ) hX (Set.to_countable good).measurableSet
    rw [hprep, measureReal_add_apply, measureReal_add_apply] at hmap
    simp only [measureReal_nnreal_smul_apply, he, mul_one] at hmap
    simpa only [good, Set.preimage_setOf_eq] using hmap.symm
  have hbgt := observed_budget μ (fun ω => (X ω).1+(X ω).2) D A 3 hD
  rw [heval] at hbgt
  nlinarith

theorem mixed_one_founder_sharp {U : Type*} [MeasurableSpace U]
    (ν : Measure U) [IsProbabilityMeasure ν] (κ : Kernel U State) [IsMarkovKernel κ]
    (a : U → Rates) (p : U → ℝ) (ha : ∀ u, RateBall (a u))
    (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hp : ∀ u, |p u-5/24| ≤ 1/1000)
    (hκ : ∀ u, κ u = oneFounder (a u) (p u)) :
    singleLower ≤ (κ ∘ₘ ν).real good := by
  have hpoint (u : U) :
      ENNReal.ofReal (singleLower) ≤ κ u good := by
    have hpU : p u ≤ 5/24+1/1000 := by have := (abs_le.mp (hp u)).2; linarith
    have h := one_founder_sharp (a u) (ha u) (p u) (hp0 u) (hp1 u) hpU
    rw [← hκ u] at h
    exact (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mpr h
  have h := lintegral_mono hpoint (μ := ν)
  have he : (κ ∘ₘ ν) good = ∫⁻ u, κ u good ∂ν :=
    Measure.bind_apply (Set.to_countable good).measurableSet κ.aemeasurable
  simp only [lintegral_const, measure_univ, mul_one] at h
  rw [← he] at h
  exact (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).mp h


theorem robust_endpoint_three_mixed_budget {Ω U : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → State) (hX : Measurable X)
    (D A : Ω → ℕ) (hD : ∀ ω, D ω ≤ (X ω).1+(X ω).2)
    (γ η : ℝ) (hfalse : μ.real {ω | 0 < A ω} ≤ η)
    (ν : Measure U) [IsProbabilityMeasure ν] (κ : Kernel U State) [IsMarkovKernel κ]
    (a : U → Rates) (p : U → ℝ) (ha : ∀ u, RateBall (a u))
    (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hp : ∀ u, |p u-5/24| ≤ 1/1000)
    (hκ : ∀ u, κ u = oneFounder (a u) (p u))
    (empty single multiple : NNReal) (hsum : empty+single+multiple = 1)
    (hmulti : (multiple : ℝ) ≤ γ) (bad : Measure State) [IsProbabilityMeasure bad]
    (hprep : μ.map X = empty • Measure.dirac (0,0) + single • (κ ∘ₘ ν) + multiple • bad) :
    max 0 ((1-γ)*singleLower-η) ≤ μ.real {ω | D ω+A ω ≤ 3} := by
  have hl := mixed_one_founder_sharp ν κ a p ha hp0 hp1 hp hκ
  have hsumR : (empty : ℝ)+(single : ℝ)+(multiple : ℝ) = 1 := by exact_mod_cast hsum
  have h0 := empty.property
  have h1 := single.property
  have hb := multiple.property
  have hm := mul_le_mul_of_nonneg_left hl h1
  have hbad : 0 ≤ (multiple : ℝ)*bad.real good := mul_nonneg hb measureReal_nonneg
  have he : (Measure.dirac (0,0) : Measure State).real good = 1 := by
    simp [Measure.real, good]
  have heval : μ.real {ω | (X ω).1+(X ω).2 ≤ 3} =
      (empty : ℝ)+(single : ℝ)*(κ ∘ₘ ν).real good+(multiple : ℝ)*bad.real good := by
    have hmap := map_measureReal_apply (μ := μ) hX (Set.to_countable good).measurableSet
    rw [hprep, measureReal_add_apply, measureReal_add_apply] at hmap
    simp only [measureReal_nnreal_smul_apply, he, mul_one] at hmap
    simpa only [good, Set.preimage_setOf_eq] using hmap.symm
  have hbgt := observed_budget μ (fun ω => (X ω).1+(X ω).2) D A 3 hD
  rw [heval] at hbgt
  have hpgt := preparation_budget (empty : ℝ) single multiple singleLower γ h0
    singleLower_bounds.1 singleLower_bounds.2 hsumR hmulti
  have hsource := hpgt.trans ((add_le_add (le_refl (empty : ℝ)) hm).trans
    (le_add_of_nonneg_right hbad))
  exact max_le measureReal_nonneg (sub_le_iff_le_add.mpr
    (hsource.trans (hbgt.trans (add_le_add (le_refl _) hfalse))))

end
end LowFounderPrediction
