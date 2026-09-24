import proofs.CompositionalMemory.JumpClockConvolution
import proofs.CompositionalMemory.JumpDeadlineRenewal
import proofs.CompositionalMemory.RenewalSelfLoop

namespace CompositionalMemory
open Classical RandomViability MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 60000
variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem physicalSafeDeadline_measurable (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (D : Set α) (f : α → ℝ≥0∞) :
    Measurable (fun p : α × ℝ => physicalSafeDeadline next rate hr ht D f p.1 p.2) := by
  apply measurable_from_prod_countable_right
  intro x
  exact Measurable.lintegral_prod_right (ν := jumpTrajectoryLaw x next rate hr ht)
    (f := fun T z => safeDeadlinePayoff D f T z) (safeDeadlinePayoff_measurable D f)

theorem physicalSafeDeadline_outside (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (D : Set α) (f : α → ℝ≥0∞) (x : α) (T : ℝ) (h : ¬(x ∈ D ∧ 0 ≤ T)) :
    physicalSafeDeadline next rate hr ht D f x T=0 := by
  rw [physicalSafeDeadline_renewal,if_neg h]

omit [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
theorem jumpClock_deadline_tail (rate : β → ℝ) (hr : ∀ b,0 ≤ rate b)
    (ht : 0 < ∑ b,rate b) (a : ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ y,(if T < y.2 then a else 0) ∂jumpClockMeasure rate hr ht) =
      causalExp (∑ b,rate b) T*a := by
  letI := isProbabilityMeasure_expMeasure ht
  have he : (∫⁻ u,(if T < u then a else 0) ∂expMeasure (∑ b,rate b)) =
      a*ENNReal.ofReal (Real.exp (-(∑ b,rate b)*T)) := by
    change (∫⁻ u,(Set.Ioi T).indicator (fun _ => a) u ∂expMeasure (∑ b,rate b))=_
    rw [lintegral_indicator measurableSet_Ioi,lintegral_const,Measure.restrict_apply_univ,
      exponential_Ioi _ T ht hT]
  have hg : Measurable (fun u : ℝ => if T < u then a else (0 : ℝ≥0∞)) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const
  have hh := lintegral_prod_mul (μ := (jumpLabelPMF rate hr ht).toMeasure)
    (ν := expMeasure (∑ b,rate b)) (f := fun _ : β => (1 : ℝ≥0∞))
    (g := fun u : ℝ => if T < u then a else 0) measurable_const.aemeasurable hg.aemeasurable
  simp only [one_mul,lintegral_const,measure_univ,mul_one] at hh
  rw [he] at hh
  exact hh.trans (by simp only [causalExp,if_pos hT]; exact mul_comm _ _)

attribute [local irreducible] physicalSafeDeadline

/-- The actual safe-history event satisfies the physical-rate convolution equation. -/
theorem physicalSafeDeadline_causal (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (D : Set α) (f : α → ℝ≥0∞) (x : α) (hx : x ∈ D) (T : ℝ) (hT : 0 ≤ T) :
    physicalSafeDeadline next rate hr ht D f x T =
      causalExp (∑ b,rate x b) T*f x + renewalConv (causalExp (∑ b,rate x b))
        (fun t => ∑ b,ENNReal.ofReal (rate x b)*physicalSafeDeadline next rate hr ht D f (next x b) t) T := by
  rw [physicalSafeDeadline_renewal,if_pos ⟨hx,hT⟩,
    lintegral_add_left (Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const measurable_const),
    jumpClock_deadline_tail (rate x) (hr x) (ht x) (f x) T hT]
  have hm (b : β) : Measurable (fun t : ℝ => physicalSafeDeadline next rate hr ht D f (next x b) t) :=
    (physicalSafeDeadline_measurable next rate hr ht D f).comp
      (measurable_const.prodMk measurable_id)
  exact congrArg (fun v => causalExp (∑ b,rate x b) T*f x+v)
    (jumpClock_future_convolution (rate x) (hr x) (ht x)
      (fun b t => physicalSafeDeadline next rate hr ht D f (next x b) t) hm T)

end
end CompositionalMemory
