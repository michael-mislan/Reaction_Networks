import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace CompositionalMemory
open MeasureTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 60000

def renewalConv (f g : ℝ → ℝ≥0∞) (T : ℝ) : ℝ≥0∞ := ∫⁻ u,f u*g (T-u)

theorem renewalConv_measurable {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    Measurable (renewalConv f g) := by
  exact (hf.comp measurable_snd |>.mul (hg.comp (measurable_fst.sub measurable_snd))).lintegral_prod_right

theorem renewalConv_assoc {f g h : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (T : ℝ) :
    renewalConv f (renewalConv g h) T = renewalConv (renewalConv f g) h T := by
  unfold renewalConv
  calc
    _ = ∫⁻ u,∫⁻ v,f u*(g v*h (T-u-v)) := by
      apply lintegral_congr
      intro u
      exact (lintegral_const_mul _ (hg.mul (hh.comp (measurable_const.sub measurable_id)))).symm
    _ = ∫⁻ u,∫⁻ s,f u*(g (s-u)*h (T-s)) := by
      apply lintegral_congr
      intro u
      have he := lintegral_sub_right_eq_self
        (fun v : ℝ => f u*(g v*h (T-u-v))) u (μ := volume)
      convert he.symm using 1
      congr 1
      funext s
      congr 3
      ring
    _ = ∫⁻ s,∫⁻ u,f u*(g (s-u)*h (T-s)) := by
      apply lintegral_lintegral_swap
      exact ((hf.comp measurable_fst).mul
        ((hg.comp (measurable_snd.sub measurable_fst)).mul
          (hh.comp (measurable_const.sub measurable_snd)))).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro s
      simp_rw [← mul_assoc]
      exact lintegral_mul_const _ (hf.mul (hg.comp (measurable_const.sub measurable_id)))

theorem renewalConv_add_right {f g h : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (T : ℝ) :
    renewalConv f (fun t => g t+h t) T = renewalConv f g T+renewalConv f h T := by
  unfold renewalConv
  simp_rw [mul_add]
  exact lintegral_add_left (hf.mul (hg.comp (measurable_const.sub measurable_id))) _

theorem renewalConv_add_left {f g h : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hh : Measurable h) (T : ℝ) :
    renewalConv (fun t => f t+g t) h T = renewalConv f h T+renewalConv g h T := by
  unfold renewalConv
  simp_rw [add_mul]
  exact lintegral_add_left (hf.mul (hh.comp (measurable_const.sub measurable_id))) _

end
end CompositionalMemory
