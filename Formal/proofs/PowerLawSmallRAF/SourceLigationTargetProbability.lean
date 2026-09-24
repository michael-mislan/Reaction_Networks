import proofs.PowerLawSmallRAF.SourceLigationIIDLaw

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 100000

/-- A joint event: the supplied nucleus is genuinely generated, but the
target fails. T may include other support channels and may depend on H. -/
def sourceLigationTargetFailureMass (p : ℝ) (n L : Nat) (w : LigationWord)
    (T : Finset (Reaction n) → Finset (Reaction n)) : ℝ :=
  ∑ H : Finset (Reaction n),
    if (∀ u ∈ ligationTargetNucleus L w, SourceLigationGenerated n (T H) u) ∧
      ¬ SourceLigationGenerated n (T H) w then bernoulliSubsetRowWeight p H else 0

theorem sourceLigationTargetFailureMass_le_raw {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (n L : Nat) (w : LigationWord) (hn : w.length ≤ n)
    (T : Finset (Reaction n) → Finset (Reaction n)) (hT : ∀ H, H ⊆ T H) :
    sourceLigationTargetFailureMass p n L w T ≤ ligationTargetFailureProbability p L w := by
  calc
    _ ≤ ∑ H : Finset (Reaction n), bernoulliSubsetRowWeight p H *
        (if w ∉ ligationRawKnown (ligationSubstringSchedule w)
          (sourceLigationTargetConfiguration n w hn H) (ligationTargetNucleus L w) then 1 else 0) := by
      apply Finset.sum_le_sum
      intro H _
      have hw := bernoulliSubsetRowWeight_nonneg hp hp1 H
      by_cases hbad : (∀ u ∈ ligationTargetNucleus L w, SourceLigationGenerated n (T H) u) ∧
          ¬ SourceLigationGenerated n (T H) w
      · have hr := sourceLigationTarget_failure_inclusion n L w hn H (T H) (hT H) hbad.1 hbad.2
        simp only [if_pos hbad, if_pos hr, mul_one, le_refl]
      · rw [if_neg hbad]
        exact mul_nonneg hw (by split_ifs <;> norm_num)
    _ = ligationTargetFailureProbability p L w := by
      rw [sourceLigationTargetConfiguration_expectation p n w hn
        (fun cfg => if w ∉ ligationRawKnown (ligationSubstringSchedule w) cfg
          (ligationTargetNucleus L w) then 1 else 0)]
      simp only [mul_ite, mul_one, mul_zero]
      rfl

/-- Concrete source target bound, valid even when nucleus generation and
the additional production support depend on the high channel field.
It bounds the joint bad event, not a conditional probability quotient. -/
theorem source_ligation_target_failure_bound {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (n L : Nat) (w : LigationWord) (hn : w.length ≤ n)
    (T : Finset (Reaction n) → Finset (Reaction n)) (hT : ∀ H, H ⊆ T H)
    (hL : 4 ≤ L) (hLw : L ≤ w.length) (hlarge : 32*Real.log 2 ≤ p*(L : ℝ)) :
    sourceLigationTargetFailureMass p n L w T ≤
      Real.exp (-p*(w.length : ℝ)/2) + 2*(w.length : ℝ)^2*Real.exp (-p*(L : ℝ)^2/32) :=
  (sourceLigationTargetFailureMass_le_raw hp hp1 n L w hn T hT).trans
    (finite_ligation_target_failure_bound hp hp1 L w hL hLw hlarge)

end
end PowerLawSmallRAF
