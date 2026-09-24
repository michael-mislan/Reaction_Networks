import proofs.CompositionalMemory.PhysicalDeadlineCausal

namespace CompositionalMemory
open Classical RandomViability MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 60000
attribute [local irreducible] physicalSafeDeadline
variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem physicalSafeDeadline_causal_all (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (D : Set α) (f : α → ℝ≥0∞) (x : α) (hx : x ∈ D) (T : ℝ) :
    physicalSafeDeadline next rate hr ht D f x T =
      causalExp (∑ b,rate x b) T*f x + renewalConv (causalExp (∑ b,rate x b))
        (fun t => ∑ b,ENNReal.ofReal (rate x b)*physicalSafeDeadline next rate hr ht D f (next x b) t) T := by
  by_cases hT : 0 ≤ T
  · exact physicalSafeDeadline_causal next rate hr ht D f x hx T hT
  · rw [physicalSafeDeadline_outside next rate hr ht D f x T (fun h => hT h.2)]
    simp only [causalExp,if_neg hT,zero_mul,zero_add]
    symm
    apply lintegral_eq_zero_of_ae_eq_zero
    apply Filter.Eventually.of_forall
    intro u
    by_cases hu : 0 ≤ u
    · have htu : ¬0 ≤ T-u := by linarith
      have hh (b : β) : physicalSafeDeadline next rate hr ht D f (next x b) (T-u)=0 :=
        physicalSafeDeadline_outside next rate hr ht D f (next x b) (T-u) (fun h => htu h.2)
      simp only [hh,mul_zero,Finset.sum_const_zero,Pi.zero_apply]
    · simp [causalExp,hu]

/-- The actual trajectory payoff now obeys a chosen dominating clock's self-loop equation. -/
theorem physicalSafeDeadline_common_clock (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (D : Set α) (f : α → ℝ≥0∞) (x : α) (hx : x ∈ D)
    (q : ℝ) (hq : (∑ b,rate x b) ≤ q) (T : ℝ) :
    physicalSafeDeadline next rate hr ht D f x T =
      causalExp q T*f x+renewalConv (causalExp q)
        (fun t => (∑ b,ENNReal.ofReal (rate x b)*physicalSafeDeadline next rate hr ht D f (next x b) t)+
          ENNReal.ofReal (q-(∑ b,rate x b))*physicalSafeDeadline next rate hr ht D f x t) T := by
  let H : ℝ → ℝ≥0∞ := fun t => ∑ b,ENNReal.ofReal (rate x b)*physicalSafeDeadline next rate hr ht D f (next x b) t
  have hH : Measurable H := by
    apply Finset.measurable_sum
    intro b _
    exact measurable_const.mul ((physicalSafeDeadline_measurable next rate hr ht D f).comp
      (measurable_const.prodMk measurable_id))
  have he (t : ℝ) : physicalSafeDeadline next rate hr ht D f x t=
      causalExp (∑ b,rate x b) t*f x+renewalConv (causalExp (∑ b,rate x b)) H t :=
    physicalSafeDeadline_causal_all next rate hr ht D f x hx t
  have hh := causal_renewal_self_loop q (∑ b,rate x b) hq H hH (f x) T
  simp_rw [← he] at hh
  exact hh

end
end CompositionalMemory
