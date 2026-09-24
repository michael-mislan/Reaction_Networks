import proofs.RandomViability.ExactFirstChannel
import proofs.RandomViability.JumpClockKernel
import Mathlib.MeasureTheory.Measure.WithDensity

namespace RandomViability
open Classical FiniteCopy MeasureTheory ProbabilityTheory
noncomputable section

theorem exponential_Iic (r T : ℝ) (hr : 0 < r) (hT : 0 ≤ T) :
    expMeasure r (Set.Iic T) = ENNReal.ofReal (1-Real.exp (-r*T)) := by
  change volume.withDensity (exponentialPDF r) (Set.Iic T) = _
  rw [withDensity_apply _ measurableSet_Iic, lintegral_exponentialPDF_eq_antiDeriv hr]
  simp only [if_pos hT, neg_mul]

variable {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem jumpClock_first_channel_CDF (rate : β → ℝ) (hr : ∀ b, 0 ≤ rate b)
    (ht : 0 < ∑ b, rate b) (b : β) (T : ℝ) (hT : 0 ≤ T) :
    jumpClockMeasure rate hr ht ({b} ×ˢ Set.Iic T) =
      ENNReal.ofReal (rate b / (∑ c, rate c) * (1-Real.exp (-(∑ c, rate c)*T))) := by
  letI := isProbabilityMeasure_expMeasure ht
  rw [jumpClockMeasure, Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ b (measurableSet_singleton b), exponential_Iic _ T ht hT]
  change ENNReal.ofReal (rate b / (∑ c, rate c)) * _ = _
  exact (ENNReal.ofReal_mul (div_nonneg (hr b) ht.le)).symm

/-- Equality with an event under the actual marked exponential holding-time measure. -/
theorem poisson_first_channel_law {α : Type*} [Fintype α]
    (M : FiniteJumpModel α β) (q t : NNReal) (hq : 0 < (q : ℝ))
    (hb : ∀ x, M.total x ≤ q) (x : α) (hx : 0 < M.total x) (b : β) :
    ENNReal.ofReal ((labeledUniformize M q hq hb).poissonEventMass (q*t) x
      (FiniteLabeledKernel.firstRace (markedLabel (fun _ => True))
        (markedLabel (fun c => c = b)))) =
      jumpClockMeasure (M.rate x) (M.nonneg x) hx ({b} ×ˢ Set.Iic (t : ℝ)) := by
  rw [first_channel_poisson M q t hq hb x hx b,
    jumpClock_first_channel_CDF (M.rate x) (M.nonneg x) hx b t t.coe_nonneg]
  rfl

end
end RandomViability
