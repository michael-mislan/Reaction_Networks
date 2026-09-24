import proofs.RAF1519.Refinement.HoldingPrimitive

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

/-- The continuous primitive at a jump time depends only on earlier holding
    intervals, including when several zero waits share that time. -/
theorem holdingPrimitive_at_clock (h v : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i)
    (K j : ℕ) (hj : j ≤ K) :
    holdingPrimitive h v K (holdingClock h j) = ∑ i ∈ Finset.range j, v i*h i := by
  induction K with
  | zero =>
    have hj0 : j=0 := by omega
    subst j
    simp [holdingPrimitive]
  | succ K ih =>
    by_cases hjK : j=K+1
    · subst j
      exact holdingPrimitive_completed h v hh (K+1) _ le_rfl
    · have hj' : j ≤ K := by omega
      have he : holdingPrimitive h v (K+1) (holdingClock h j) =
          holdingPrimitive h v K (holdingClock h j)+
          v K*holdingRamp (holdingClock h K) (h K) (holdingClock h j) := by
        unfold holdingPrimitive
        rw [Finset.sum_range_succ]
      rw [he,ih hj',holdingRamp_not_started _ _ _ (holdingClock_monotone h hh hj')]
      simp

end
end RAF1519.Refinement
