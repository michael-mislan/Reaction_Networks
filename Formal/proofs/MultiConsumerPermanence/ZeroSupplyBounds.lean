import proofs.MultiConsumerPermanence.ReservoirFlowBounds

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence

theorem reservoir_extension_zero_supply_bound {n : ℕ} (e Q : ℝ)
    (b : ReservoirVector n → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → ReservoirVector n) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (h0 : X 0 (.inl 4)+total (fun i => X 0 (.inr i)) ≤ Q)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • reservoirField e 0 0 (X t)) t) :
    ∀ t, 0 ≤ t → X t (.inl 4)+total (fun i => X t (.inr i)) ≤ Q := by
  apply scalar_upper_barrier _ (fun t => b (X t)*(-(1/2)*total (fun i => X t (.inr i))-
    (n:ℝ)*squares (fun i => X t (.inr i)))) Q ?_ h0 ?_
  · intro t ht
    convert ((hasDerivAt_pi.1 (hd t ht)) (.inl 4)).add
      (reservoir_extension_aggregate_deriv e 0 0 b X t (hd t ht)) using 1
    simp [reservoirField]
    ring
  · intro t ht _
    apply mul_nonpos_of_nonneg_of_nonpos (hb _)
    have hs := total_nonneg (fun i => X t (.inr i)) (fun i => hX t ht (.inr i))
    have hq : 0 ≤ (n:ℝ)*squares (fun i => X t (.inr i)) :=
      mul_nonneg (Nat.cast_nonneg n) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    linarith only [hs,hq]

end MultiConsumerPermanence
