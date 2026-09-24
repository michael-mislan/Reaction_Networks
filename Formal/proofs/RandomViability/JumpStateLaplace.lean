import proofs.RandomViability.JumpLaplace
import proofs.RandomViability.JumpTrajectory

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 30000

def jumpMultiplier {α β : Type*} (w : β → ℝ) (s : ℝ) (y : JumpState α β) : ℝ≥0∞ :=
  ENNReal.ofReal (y.2.1.elim (fun _ => 1) w) * ENNReal.ofReal (Real.exp (-s*y.2.2))

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

omit [Countable α] [MeasurableSingletonClass α] in
theorem jumpMultiplier_measurable (w : β → ℝ) (s : ℝ) :
    Measurable (jumpMultiplier (α := α) w s) := by
  unfold jumpMultiplier
  exact (((measurable_const.sumElim (measurable_of_countable w)).comp measurable_snd.fst).ennreal_ofReal).mul
    (by fun_prop)

theorem jumpState_weight_laplace (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (w : β → ℝ) (hw : ∀ b, 0 ≤ w b) (s : ℝ) (x : α) (hs : 0 < (∑ b, rate x b)+s) :
    ∫⁻ y, jumpMultiplier w s y ∂jumpStateKernel next rate hr ht x =
      ENNReal.ofReal ((∑ b, rate x b*w b)/((∑ b, rate x b)+s)) := by
  change ∫⁻ y, jumpMultiplier w s y ∂(jumpClockMeasure (rate x) (hr x) (ht x)).map (jumpStateUpdate next x) = _
  rw [lintegral_map (jumpMultiplier_measurable w s) (jumpStateUpdate_measurable next x)]
  exact jumpClock_weight_laplace (rate x) (hr x) (ht x) w hw s hs

theorem jumpState_wait_contraction (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (x : α) (q : ℝ) (hq : (∑ b, rate x b) ≤ q) :
    (∫⁻ y, jumpMultiplier (fun _ => 1) 1 y ∂jumpStateKernel next rate hr ht x) ≤
      ENNReal.ofReal (q/(q+1)) ∧ ENNReal.ofReal (q/(q+1)) < 1 := by
  have hqp : 0 < q := (ht x).trans_le hq
  rw [jumpState_weight_laplace next rate hr ht (fun _ => 1) (fun _ => zero_le_one) 1 x (by linarith [ht x])]
  simp only [mul_one]
  constructor
  · apply ENNReal.ofReal_le_ofReal
    apply (div_le_div_iff₀ (by linarith [ht x]) (by linarith)).mpr
    nlinarith
  · rw [ENNReal.ofReal_lt_one]
    exact (div_lt_one (by linarith)).mpr (by linarith)

end
end RandomViability
