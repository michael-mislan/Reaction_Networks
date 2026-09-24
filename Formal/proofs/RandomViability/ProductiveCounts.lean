import proofs.RandomViability.ProductiveRates

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 40000

/-- Population after L productive ligations and E exports of their product.
Other species retain their initial counts. -/
def productiveCounts {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (L E : ℕ) (y : Molecule n) : ℕ :=
  if y = reactionLeft r then N y-L else
  if y = reactionRight r then N y-L else
  if y = reactionProduct r then L-E else N y

theorem productive_counts_initial {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (hp : N (reactionProduct r) = 0) : productiveCounts N r 0 0 = N := by
  funext y
  unfold productiveCounts
  split_ifs with hu hw hz
  · omega
  · omega
  · subst y; exact hp.symm
  · rfl

theorem productive_basal_enabled {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (huw : reactionLeft r ≠ reactionRight r)
    (L E : ℕ) (hu : L < N (reactionLeft r)) (hw : L < N (reactionRight r)) :
    ∀ y, physicalChannelInput (.inr (.inl (r,true))) y ≤ productiveCounts N r L E y := by
  intro y
  by_cases hyu : y = reactionLeft r
  · subst y
    simp [physicalChannelInput, singleCount, productiveCounts, huw]
    omega
  · by_cases hyw : y = reactionRight r
    · subst y
      simp [physicalChannelInput, singleCount, productiveCounts, Ne.symm huw]
      omega
    · simp [physicalChannelInput, singleCount, hyu, hyw]

theorem productive_catalytic_enabled {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (huw : reactionLeft r ≠ reactionRight r)
    (hup : reactionLeft r ≠ reactionProduct r) (hwp : reactionRight r ≠ reactionProduct r)
    (L E : ℕ) (hu : L < N (reactionLeft r)) (hw : L < N (reactionRight r)) (he : E < L) :
    ∀ y, physicalChannelInput (.inr (.inr (r,reactionProduct r,true))) y ≤ productiveCounts N r L E y := by
  intro y
  by_cases hyu : y = reactionLeft r
  · subst y
    simp [physicalChannelInput, singleCount, productiveCounts, huw, hup]
    omega
  · by_cases hyw : y = reactionRight r
    · subst y
      simp [physicalChannelInput, singleCount, productiveCounts, Ne.symm huw, hwp]
      omega
    · by_cases hyp : y = reactionProduct r
      · subst y
        simp [physicalChannelInput, singleCount, productiveCounts, Ne.symm hup, Ne.symm hwp]
        omega
      · simp [physicalChannelInput, singleCount, hyu, hyw, hyp]

theorem productive_basal_next {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (huw : reactionLeft r ≠ reactionRight r)
    (hup : reactionLeft r ≠ reactionProduct r) (hwp : reactionRight r ≠ reactionProduct r)
    (L E : ℕ) (hu : L < N (reactionLeft r)) (hw : L < N (reactionRight r)) (he : E ≤ L) :
    unboundedPhysicalNext (productiveCounts N r L E) (.inr (.inl (r,true))) =
      productiveCounts N r (L+1) E := by
  rw [unboundedPhysicalNext, if_pos (productive_basal_enabled N r huw L E hu hw)]
  funext y
  by_cases hyu : y = reactionLeft r
  · subst y
    simp [applyCountChannel, physicalChannelInput, physicalChannelOutput, singleCount,
      productiveCounts, huw, hup]
    omega
  · by_cases hyw : y = reactionRight r
    · subst y
      simp [applyCountChannel, physicalChannelInput, physicalChannelOutput, singleCount,
        productiveCounts, Ne.symm huw, hwp]
      omega
    · by_cases hyp : y = reactionProduct r
      · subst y
        simp [applyCountChannel, physicalChannelInput, physicalChannelOutput, singleCount,
          productiveCounts, Ne.symm hup, Ne.symm hwp]
        omega
      · simp [applyCountChannel, physicalChannelInput, physicalChannelOutput, singleCount,
          productiveCounts, hyu, hyw, hyp]

theorem productive_catalytic_next {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (huw : reactionLeft r ≠ reactionRight r)
    (hup : reactionLeft r ≠ reactionProduct r) (hwp : reactionRight r ≠ reactionProduct r)
    (L E : ℕ) (hu : L < N (reactionLeft r)) (hw : L < N (reactionRight r)) (he : E < L) :
    unboundedPhysicalNext (productiveCounts N r L E) (.inr (.inr (r,reactionProduct r,true))) =
      productiveCounts N r (L+1) E := by
  rw [unboundedPhysicalNext, if_pos (productive_catalytic_enabled N r huw hup hwp L E hu hw he)]
  funext y
  by_cases hyu : y = reactionLeft r
  · subst y
    simp [applyCountChannel, physicalChannelInput, physicalChannelOutput, singleCount,
      productiveCounts, huw, hup]
    omega
  · by_cases hyw : y = reactionRight r
    · subst y
      simp [applyCountChannel, physicalChannelInput, physicalChannelOutput, singleCount,
        productiveCounts, Ne.symm huw, hwp]
      omega
    · by_cases hyp : y = reactionProduct r
      · subst y
        simp [applyCountChannel, physicalChannelInput, physicalChannelOutput, singleCount,
          productiveCounts, Ne.symm hup, Ne.symm hwp]
        omega
      · simp [applyCountChannel, physicalChannelInput, physicalChannelOutput, singleCount,
          productiveCounts, hyu, hyw, hyp]

theorem productive_export_next {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (hup : reactionLeft r ≠ reactionProduct r) (hwp : reactionRight r ≠ reactionProduct r)
    (L E : ℕ) (he : E < L) :
    unboundedPhysicalNext (productiveCounts N r L E) (.inl (.inr (reactionProduct r))) =
      productiveCounts N r L (E+1) := by
  have hen : ∀ y, physicalChannelInput (.inl (.inr (reactionProduct r))) y ≤ productiveCounts N r L E y := by
    intro y
    by_cases hyp : y = reactionProduct r
    · subst y
      simp [physicalChannelInput, singleCount, productiveCounts, Ne.symm hup, Ne.symm hwp]
      omega
    · simp [physicalChannelInput, singleCount, hyp]
  rw [unboundedPhysicalNext, if_pos hen]
  funext y
  by_cases hyp : y = reactionProduct r
  · subst y
    simp [applyCountChannel, physicalChannelInput, physicalChannelOutput, singleCount,
      productiveCounts, Ne.symm hup, Ne.symm hwp]
    omega
  · simp only [applyCountChannel, physicalChannelInput, physicalChannelOutput,
      singleCount, if_neg hyp, Nat.sub_zero, Nat.add_zero]
    unfold productiveCounts
    split_ifs <;> rfl

end
end RandomViability
