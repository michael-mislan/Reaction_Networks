import proofs.CoreCouplingGlobal.QuadraticCoordinates
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace CoreCouplingGlobal
open Set MeasureTheory intervalIntegral

theorem past_exponential_kernel_mass (ν t : ℝ) (hν : 0 < ν) :
    (∫ s in (0:ℝ)..t, Real.exp (-ν*(t-s))) = (1-Real.exp (-ν*t))/ν := by
  have heq : (fun s : ℝ => Real.exp (-ν*(t-s))) =
      (fun s => Real.exp (-ν*t)*Real.exp (ν*s)) := by
    ext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq,intervalIntegral.integral_const_mul,integral_comp_mul_left _ hν.ne',integral_exp]
  simp only [mul_zero,Real.exp_zero,smul_eq_mul]
  have hprod : Real.exp (-ν*t)*Real.exp (ν*t) = 1 := by
    rw [← Real.exp_add,show -ν*t+ν*t = 0 by ring,Real.exp_zero]
  field_simp
  simp only [neg_mul] at hprod ⊢
  nlinarith only [hprod]

theorem past_exponential_kernel_mass_bound (ν t : ℝ) (hν : 0 < ν) :
    (∫ s in (0:ℝ)..t, Real.exp (-ν*(t-s))) ≤ 1/ν := by
  rw [past_exponential_kernel_mass ν t hν]
  exact (div_le_div_iff_of_pos_right hν).2 (by linarith [Real.exp_pos (-ν*t)])

theorem future_exponential_kernel_mass (ν t : ℝ) (hν : 0 < ν) :
    (∫ s in Ioi t, Real.exp (-ν*(s-t))) = 1/ν := by
  have heq : (fun s : ℝ => Real.exp (-ν*(s-t))) =
      (fun s => Real.exp (ν*t)*Real.exp ((-ν)*s)) := by
    ext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq,MeasureTheory.integral_const_mul,integral_exp_mul_Ioi (neg_neg_of_pos hν)]
  have hprod : Real.exp (ν*t)*Real.exp ((-ν)*t) = 1 := by
    rw [← Real.exp_add,show ν*t+(-ν)*t = 0 by ring,Real.exp_zero]
  field_simp
  simp only [neg_mul] at hprod ⊢
  nlinarith only [hprod]

theorem weighted_past_kernel_mass (a β t : ℝ) (hgap : β < a) :
    Real.exp (β*t)*(∫ s in (0:ℝ)..t, Real.exp (-a*(t-s))*Real.exp (-β*s)) =
      (1-Real.exp (-(a-β)*t))/(a-β) := by
  rw [← intervalIntegral.integral_const_mul]
  calc
    (∫ s in (0:ℝ)..t, Real.exp (β*t)*(Real.exp (-a*(t-s))*Real.exp (-β*s))) =
        ∫ s in (0:ℝ)..t, Real.exp (-(a-β)*(t-s)) := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      rw [← mul_assoc,← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    _ = _ := past_exponential_kernel_mass (a-β) t (sub_pos.mpr hgap)

theorem weighted_future_kernel_mass (a β t : ℝ) (hgap : 0 < a+β) :
    Real.exp (β*t)*(∫ s in Ioi t, Real.exp (a*(t-s))*Real.exp (-β*s)) = 1/(a+β) := by
  rw [← MeasureTheory.integral_const_mul]
  calc
    (∫ s in Ioi t, Real.exp (β*t)*(Real.exp (a*(t-s))*Real.exp (-β*s))) =
        ∫ s in Ioi t, Real.exp (-(a+β)*(s-t)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with s
      rw [← mul_assoc,← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    _ = _ := future_exponential_kernel_mass (a+β) t hgap

/-- The fixed decay weight 1/4 yields a common Green-kernel bound of four for
the three stable coordinates and the future unstable coordinate. -/
theorem middle_perron_kernel_bounds (μ : Fin 4 → ℝ)
    (hs : ∀ i : Fin 3, μ i.castSucc < -(1/2:ℝ)) (hu : 0 < μ 3) (t : ℝ) :
    (∀ i : Fin 3, Real.exp ((1/4:ℝ)*t)*
      (∫ s in (0:ℝ)..t, Real.exp (μ i.castSucc*(t-s))*Real.exp (-(1/4:ℝ)*s)) ≤ 4) ∧
    Real.exp ((1/4:ℝ)*t)*
      (∫ s in Ioi t, Real.exp (μ 3*(t-s))*Real.exp (-(1/4:ℝ)*s)) ≤ 4 := by
  obtain ⟨hstable,hunstable⟩ := middle_weighted_gaps μ hs hu
  constructor
  · intro i
    have heq := weighted_past_kernel_mass (-μ i.castSucc) (1/4) t (by linarith [hs i])
    simp only [neg_neg] at heq
    rw [heq]
    apply (div_le_iff₀ (by linarith [hstable i] : 0 < -μ i.castSucc-1/4)).2
    linarith [Real.exp_pos (-(-μ i.castSucc-1/4)*t),hstable i]
  · rw [weighted_future_kernel_mass (μ 3) (1/4) t (by linarith)]
    apply (div_le_iff₀ (by linarith : 0 < μ 3+1/4)).2
    linarith

end CoreCouplingGlobal
