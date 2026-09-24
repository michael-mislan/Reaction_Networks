import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

namespace InheritedCellAssay.ScalarCount

noncomputable def denominator (x : ℝ) : ℝ := (5*(1+x)^4+19)^2
noncomputable def numerator (x : ℝ) : ℝ := 120*(1+x)^6+1368*(1+x)^2
noncomputable def majorant (x : ℝ) : ℝ :=
  25897/10000 + (3457/2000)*x^1 - (32099/5000)*x^2 + (179/50)*x^3
noncomputable def integrand (x : ℝ) : ℝ := numerator x / denominator x

theorem denominator_pos (x : ℝ) : 0 < denominator x := by
  unfold denominator
  positivity

theorem pointwise_bounds (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    1 ≤ integrand x ∧ integrand x ≤ majorant x := by
  have hx0 : 0 ≤ x := hx.1
  have hx1 : 0 ≤ 1-x := sub_nonneg.mpr hx.2
  have lower : numerator x - denominator x =
      (912/1 : ℝ) * x^0 * (1-x)^8 +
      (9792/1 : ℝ) * x^1 * (1-x)^7 +
      (44336/1 : ℝ) * x^2 * (1-x)^6 +
      (111696/1 : ℝ) * x^3 * (1-x)^5 +
      (172180/1 : ℝ) * x^4 * (1-x)^4 +
      (166152/1 : ℝ) * x^5 * (1-x)^3 +
      (96812/1 : ℝ) * x^6 * (1-x)^2 +
      (29976/1 : ℝ) * x^7 * (1-x)^1 +
      (3351/1 : ℝ) * x^8 * (1-x)^0 := by unfold numerator denominator; ring
  have upper : majorant x * denominator x - numerator x =
      (2292/625 : ℝ) * x^0 * (1-x)^11 +
      (41292/625 : ℝ) * x^1 * (1-x)^10 +
      (10987/625 : ℝ) * x^2 * (1-x)^9 +
      (39713/625 : ℝ) * x^3 * (1-x)^8 +
      (12938273/2500 : ℝ) * x^4 * (1-x)^7 +
      (28405139/1250 : ℝ) * x^5 * (1-x)^6 +
      (54190307/1250 : ℝ) * x^6 * (1-x)^5 +
      (26139962/625 : ℝ) * x^7 * (1-x)^4 +
      (174528933/10000 : ℝ) * x^8 * (1-x)^3 +
      (131199/1250 : ℝ) * x^9 * (1-x)^2 +
      (58443/2000 : ℝ) * x^10 * (1-x)^1 +
      (836124/625 : ℝ) * x^11 * (1-x)^0 := by unfold majorant numerator denominator; ring
  have hl : 0 ≤ numerator x - denominator x := by rw [lower]; positivity
  have hu : 0 ≤ majorant x * denominator x - numerator x := by rw [upper]; positivity
  constructor
  · apply (le_div_iff₀ (denominator_pos x)).mpr
    linarith
  · apply (div_le_iff₀ (denominator_pos x)).mpr
    linarith

theorem integrand_continuous : Continuous integrand := by
  unfold integrand numerator denominator
  fun_prop (disch := intro x; exact ne_of_gt (denominator_pos x))

noncomputable def varianceIntegral : ℝ := ∫ x in (0 : ℝ)..1, integrand x

theorem majorant_integral : (∫ x in (0 : ℝ)..1, majorant x) = 132541/60000 := by
  unfold majorant
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_add]
  · simp only [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_pow]
    norm_num
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

theorem varianceIntegral_bounds : 1 ≤ varianceIntegral ∧ varianceIntegral ≤ 9/4 := by
  have hl := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) (μ := MeasureTheory.volume)
    (f := fun _ => (1 : ℝ)) (g := integrand) (by norm_num)
    (continuous_const.intervalIntegrable _ _) (integrand_continuous.intervalIntegrable _ _)
    (fun x hx => (pointwise_bounds x hx).1)
  have hu := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) (μ := MeasureTheory.volume)
    (f := integrand) (g := majorant) (by norm_num)
    (integrand_continuous.intervalIntegrable _ _)
    ((by unfold majorant; fun_prop : Continuous majorant).intervalIntegrable _ _)
    (fun x hx => (pointwise_bounds x hx).2)
  rw [majorant_integral] at hu
  norm_num at hl
  exact ⟨hl, le_trans hu (by norm_num)⟩

end InheritedCellAssay.ScalarCount
