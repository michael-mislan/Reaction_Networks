import proofs.CompositionalMemory.SixthCapTaylor
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace CompositionalMemory
open MeasureTheory Set

/-- Initial recovery cost from centered allocation noise and its first two
quadratic moments. This applies to a countable raw offspring law as well as a
finite one; concrete binomial/Poisson moments are separate obligations. -/
theorem sixth_cap_initial_expectation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (s q : α → ℝ) (u m1 m2 : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) (hs : Integrable s μ) (hq : Integrable q μ)
    (hq2 : Integrable (fun z => q z^2) μ)
    (hcenter : ∫ z,s z ∂μ=0) (hfirst : ∫ z,q z ∂μ ≤ m1)
    (hsecond : ∫ z,q z^2 ∂μ ≤ m2) (hm1 : 0 ≤ m1)
    (hD : ∀ z,0 ≤ u+2*s z+q z) (hcross : ∀ z,s z^2 ≤ u*q z) :
    (∫ z,smoothQuadraticCap ((u+2*s z+q z)^6) ∂μ) ≤
      smoothQuadraticCap (u^6)+(4+48*u)*m1+12*m2 := by
  let a : ℝ := 2*(12*u^5-12*u^11)
  let b : ℝ := 12*u^5-12*u^11+48*u
  let c : ℝ := smoothQuadraticCap (u^6)
  have hb : 0 ≤ b := by
    dsimp [b]
    linarith only [sixth_cap_slope_nonneg u hu.1 hu.2,hu.1]
  have hcb : b ≤ 4+48*u := by
    dsimp [b]
    linarith only [sixth_cap_slope_le_four u hu.1 hu.2]
  have hi : Integrable (fun z => c+a*s z+b*q z+12*q z^2) μ :=
    (((integrable_const c).add (hs.const_mul a)).add (hq.const_mul b)).add (hq2.const_mul 12)
  have hm : (∫ z,smoothQuadraticCap ((u+2*s z+q z)^6) ∂μ) ≤
      ∫ z,c+a*s z+b*q z+12*q z^2 ∂μ := by
    exact integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z => smoothQuadraticCap_nonneg _ (pow_nonneg (hD z) 6))) hi
      (Filter.Eventually.of_forall (fun z => sixth_cap_noise_upper u (s z) (q z) hu (hD z) (hcross z)))
  have heq : (∫ z,c+a*s z+b*q z+12*q z^2 ∂μ)=
      c+b*(∫ z,q z ∂μ)+12*(∫ z,q z^2 ∂μ) := by
    have h1 := integral_add (((integrable_const c).add (hs.const_mul a)).add (hq.const_mul b)) (hq2.const_mul 12)
    have h2 := integral_add ((integrable_const c).add (hs.const_mul a)) (hq.const_mul b)
    have h3 := integral_add (integrable_const c) (hs.const_mul a)
    simp only [Pi.add_apply] at h1 h2 h3
    rw [h1,h2,h3]
    simp [integral_const_mul,hcenter]
  rw [heq] at hm
  have h1 := mul_le_mul_of_nonneg_left hfirst hb
  have h2 := mul_le_mul_of_nonneg_left hsecond (show (0 : ℝ) ≤ 12 by norm_num)
  have h3 := mul_le_mul_of_nonneg_right hcb hm1
  change _ ≤ c+(4+48*u)*m1+12*m2
  linarith only [hm,h1,h2,h3]

end CompositionalMemory
