import proofs.RandomViability.JumpStateLaplace

namespace CompositionalMemory
open RandomViability MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A generator Lyapunov inequality becomes an exact discounted one-jump
multiplicative budget under state-dependent exponential holding times. -/
theorem jump_lyapunov_step {α β : Type*}
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (V : α → ℝ) (hV : ∀ x, 0 < V x) (c : ℝ) (hc : 0 ≤ c)
    (hgen : ∀ x, (∑ b, rate x b*(V (next x b)-V x)) ≤ c*V x)
    (x : α) :
    (∫⁻ y, jumpMultiplier (fun b => V (next x b)/V x) c y
      ∂jumpStateKernel next rate hr ht x) ≤ 1 := by
  rw [jumpState_weight_laplace next rate hr ht _
    (fun b => (div_pos (hV (next x b)) (hV x)).le) c x (add_pos_of_pos_of_nonneg (ht x) hc)]
  apply ENNReal.ofReal_le_one.mpr
  apply (div_le_one (add_pos_of_pos_of_nonneg (ht x) hc)).mpr
  have hs : (∑ b, rate x b*(V (next x b)/V x)) = (∑ b, rate x b*V (next x b))/V x := by
    simp only [mul_div_assoc,Finset.sum_div]
  rw [hs]
  apply (div_le_iff₀ (hV x)).mpr
  have hg := hgen x
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul] at hg
  nlinarith only [hg]

end CompositionalMemory
