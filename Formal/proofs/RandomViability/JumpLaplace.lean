import proofs.RandomViability.ExponentialLaplace
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 30000

variable {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem jumpLabel_weight_integral (rate : β → ℝ) (hr : ∀ b, 0 ≤ rate b)
    (ht : 0 < ∑ b, rate b) (w : β → ℝ) (hw : ∀ b, 0 ≤ w b) :
    ∫⁻ b, ENNReal.ofReal (w b) ∂(jumpLabelPMF rate hr ht).toMeasure =
      ENNReal.ofReal ((∑ b, rate b*w b)/(∑ b, rate b)) := by
  rw [lintegral_fintype]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), jumpLabelPMF, PMF.ofFintype_apply]
  simp_rw [← ENNReal.ofReal_mul (hw _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => mul_nonneg (hw b) (div_nonneg (hr b) ht.le))]
  congr 1
  simp only [← mul_div_assoc, ← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem jumpClock_weight_laplace (rate : β → ℝ) (hr : ∀ b, 0 ≤ rate b)
    (ht : 0 < ∑ b, rate b) (w : β → ℝ) (hw : ∀ b, 0 ≤ w b)
    (s : ℝ) (hs : 0 < (∑ b, rate b)+s) :
    ∫⁻ y, ENNReal.ofReal (w y.1)*ENNReal.ofReal (Real.exp (-s*y.2)) ∂jumpClockMeasure rate hr ht =
      ENNReal.ofReal ((∑ b, rate b*w b)/((∑ b, rate b)+s)) := by
  letI := isProbabilityMeasure_expMeasure ht
  unfold jumpClockMeasure
  rw [lintegral_prod_mul (f := fun b => ENNReal.ofReal (w b))
    (g := fun x => ENNReal.ofReal (Real.exp (-s*x))) (measurable_of_countable _).aemeasurable (by fun_prop),
    jumpLabel_weight_integral rate hr ht w hw, exponential_laplace_lintegral _ s ht hs]
  rw [← ENNReal.ofReal_mul (div_nonneg (Finset.sum_nonneg (fun b _ => mul_nonneg (hr b) (hw b))) ht.le)]
  congr 1
  field_simp

end
end RandomViability
