import proofs.CompositionalMemory.CountJumpLyapunov
import proofs.CompositionalMemory.JumpNonexplosion

namespace CompositionalMemory
open RandomViability MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- The literal source jump law is nonexplosive, without a tube or small-rate assumption. -/
theorem count_jump_nonexplosive {k : ℕ} (hk : 1 ≤ k) (γ : ℝ)
    (w : Fin k → Fin k → ℝ) (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j)
    (s : PositiveCountState k) :
    ∀ᵐ z ∂countJumpTrajectory hk γ w hγ hw s,
      Tendsto (waitingSum (fun i => (z (i+1)).2.2)) atTop atTop := by
  apply jump_times_diverge s positiveCountNext (fun x r => modularRate γ w x.val r)
    (fun x r => modular_rate_nonnegative γ w hγ hw x.val r)
    (modular_total_positive hk γ w hγ hw) positiveCountMass positive_count_mass_pos 33
    (by norm_num) (positive_count_generator hk γ w)
  intro B
  obtain ⟨q,hq,hbound⟩ := count_jump_rates_locally_bounded γ w hγ hw B
  exact ⟨q,lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hq,hbound⟩

end CompositionalMemory
