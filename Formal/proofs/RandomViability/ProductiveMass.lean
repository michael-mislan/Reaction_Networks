import proofs.RandomViability.ProductiveCounts

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 30000

theorem countMass_const_mul {n : ℕ} (a : ℕ) (N : Molecule n → ℕ) :
    countMass (fun y => a*N y) = a*countMass N := by
  unfold countMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Exact material accounting: every ligation preserves mass, and each
prescribed export removes one product molecule's mass. -/
theorem productive_count_mass {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (huw : reactionLeft r ≠ reactionRight r)
    (hup : reactionLeft r ≠ reactionProduct r) (hwp : reactionRight r ≠ reactionProduct r)
    (hp : N (reactionProduct r) = 0) (L E : ℕ)
    (hu : L ≤ N (reactionLeft r)) (hw : L ≤ N (reactionRight r)) (he : E ≤ L) :
    countMass (productiveCounts N r L E)+E*molLength (reactionProduct r) = countMass N := by
  have hpoint : (fun y => productiveCounts N r L E y + L*singleCount (reactionLeft r) y +
      L*singleCount (reactionRight r) y + E*singleCount (reactionProduct r) y) =
      (fun y => N y+L*singleCount (reactionProduct r) y) := by
    funext y
    by_cases hyu : y = reactionLeft r
    · subst y
      simp [productiveCounts, singleCount, huw, hup]
      omega
    · by_cases hyw : y = reactionRight r
      · subst y
        simp [productiveCounts, singleCount, Ne.symm huw, hwp]
        omega
      · by_cases hyp : y = reactionProduct r
        · subst y
          simp [productiveCounts, singleCount, Ne.symm hup, Ne.symm hwp, hp]
          omega
        · simp [productiveCounts, singleCount, hyu, hyw, hyp]
  have hh := congrArg countMass hpoint
  simp only [countMass_add, countMass_const_mul, countMass_single] at hh
  have hlen : molLength (reactionLeft r)+molLength (reactionRight r) = molLength (reactionProduct r) := by
    simpa only [molLength_reactionLeft, molLength_reactionRight, molLength_reactionProduct]
      using reaction_length_add r
  nlinarith only [hh, hlen]

theorem productive_count_mass_le {n : ℕ} (N : Molecule n → ℕ) (r : Reaction n)
    (huw : reactionLeft r ≠ reactionRight r)
    (hup : reactionLeft r ≠ reactionProduct r) (hwp : reactionRight r ≠ reactionProduct r)
    (hp : N (reactionProduct r) = 0) (L E : ℕ)
    (hu : L ≤ N (reactionLeft r)) (hw : L ≤ N (reactionRight r)) (he : E ≤ L) :
    countMass (productiveCounts N r L E) ≤ countMass N := by
  have hh := productive_count_mass N r huw hup hwp hp L E hu hw he
  omega

end
end RandomViability
