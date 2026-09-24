import proofs.SerialTransferSelection.RecoveryReturn

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy

def wrongRecoverySize (D : Finset Compartment) (m : ℕ) : Set (StoppedCompartment D) :=
  {x | match x with | none => False | some c => c.val.2 ≠ m}

theorem zero_growth_size_generator (N : ℕ) (D : Finset Compartment) (m : ℕ)
    (x : StoppedCompartment D) :
    (stoppedGrowthModel 0 (by norm_num) N D).generator
      (FiniteKernel.eventIndicator (wrongRecoverySize D m)) x ≤ 0 := by
  classical
  cases x with
  | none => simp [stoppedGrowthModel, FiniteJumpModel.generator]
  | some c =>
    by_cases hc : c.val.2 < 2*N
    · unfold FiniteJumpModel.generator
      apply Finset.sum_nonpos
      intro r _
      cases r with
      | inr r => simp [stoppedGrowthModel, hc, propensity]
      | inl r =>
        have hr := propensity_nonneg 0 (by norm_num) c.val (.inl r)
        by_cases hd : nextCompartment c.val (.inl r) ∈ D
        · have hd' : (nextCounts c.val.1 r, c.val.2) ∈ D := hd
          simp [stoppedGrowthModel, hc, hd', FiniteKernel.eventIndicator,
            wrongRecoverySize, nextCompartment]
          split_ifs <;> norm_num
        · have hi : 0 ≤ FiniteKernel.eventIndicator (wrongRecoverySize D m) (some c) := by
            unfold FiniteKernel.eventIndicator
            split_ifs <;> norm_num
          simpa [stoppedGrowthModel, hc, hd, FiniteKernel.eventIndicator,
            wrongRecoverySize] using mul_nonpos_of_nonneg_of_nonpos hr (neg_nonpos.mpr hi)
    · simp [stoppedGrowthModel, FiniteJumpModel.generator, hc]

/-- Surviving states have exactly the transferred size under the Poissonized law. -/
theorem zero_growth_size_probability (N : ℕ) (D : Finset Compartment)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x, (stoppedGrowthModel 0 (by norm_num) N D).total x ≤ q)
    (c : {c : Compartment // c ∈ D}) :
    ((stoppedGrowthModel 0 (by norm_num) N D).uniformize q hq hclock).poissonized
      (q*t) (FiniteKernel.eventIndicator (wrongRecoverySize D c.val.2)) (some c) ≤ 0 := by
  classical
  have h := (stoppedGrowthModel 0 (by norm_num) N D).uniformized_event_bound
    q t hq hclock (wrongRecoverySize D c.val.2)
    (FiniteKernel.eventIndicator (wrongRecoverySize D c.val.2)) 1 0
    (by intro y; unfold FiniteKernel.eventIndicator; split_ifs <;> norm_num)
    (by intro y hy; simp only [FiniteKernel.eventIndicator, if_pos hy, le_refl])
    (zero_growth_size_generator N D c.val.2) (some c)
  simpa [FiniteKernel.eventIndicator, wrongRecoverySize] using h

end SerialTransferSelection
