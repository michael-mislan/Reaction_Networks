import proofs.PowerLawSmallRAF.BoundedRawLigationWitness
import proofs.PowerLawSmallRAF.SourceLigationIIDLaw

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def sourceBoundedTargetFailureMass (p : ℝ) (n L : Nat) (w : LigationWord)
    (B : Finset (Reaction n) → Finset (Reaction n)) : ℝ :=
  ∑ H : Finset (Reaction n), if
    (∀ u ∈ ligationTargetNucleus L w, SourceLigationGenerated n (B H) u) ∧
      ¬ (∃ S : Finset (Reaction n), S ⊆ H ∧ S.card ≤ w.length-1 ∧
        SourceLigationGenerated n (B H ∪ S) w)
    then bernoulliSubsetRowWeight p H else 0

theorem sourceBoundedTargetFailureMass_le_raw {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (n L : Nat) (w : LigationWord) (hn : w.length ≤ n)
    (B : Finset (Reaction n) → Finset (Reaction n)) :
    sourceBoundedTargetFailureMass p n L w B ≤ ligationTargetFailureProbability p L w := by
  calc
    _ ≤ ∑ H : Finset (Reaction n), bernoulliSubsetRowWeight p H *
        (if w ∉ ligationRawKnown (ligationSubstringSchedule w)
          (sourceLigationTargetConfiguration n w hn H) (ligationTargetNucleus L w) then 1 else 0) := by
      apply Finset.sum_le_sum
      intro H _
      have hw := bernoulliSubsetRowWeight_nonneg hp hp1 H
      by_cases hbad : (∀ u ∈ ligationTargetNucleus L w, SourceLigationGenerated n (B H) u) ∧
          ¬ (∃ S : Finset (Reaction n), S ⊆ H ∧ S.card ≤ w.length-1 ∧
            SourceLigationGenerated n (B H ∪ S) w)
      · have hf : w ∉ ligationRawKnown (ligationSubstringSchedule w)
            (sourceLigationTargetConfiguration n w hn H) (ligationTargetNucleus L w) := by
          intro hh
          exact hbad.2 (sourceRawTarget_bounded_witness n L (B H) H w hn hbad.1 hh)
        simp only [if_pos hbad,if_pos hf,mul_one,le_refl]
      · rw [if_neg hbad]
        exact mul_nonneg hw (by split_ifs <;> norm_num)
    _ = ligationTargetFailureProbability p L w := by
      rw [sourceLigationTargetConfiguration_expectation p n w hn
        (fun cfg => if w ∉ ligationRawKnown (ligationSubstringSchedule w) cfg
          (ligationTargetNucleus L w) then 1 else 0)]
      simp only [mul_ite,mul_one,mul_zero]
      rfl

/-- Same target error, now retaining an explicit bounded additional support.
The base support may depend on the field; no conditional iid claim is used. -/
theorem source_bounded_target_failure_bound {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (n L : Nat) (w : LigationWord) (hn : w.length ≤ n)
    (B : Finset (Reaction n) → Finset (Reaction n))
    (hL : 4 ≤ L) (hLw : L ≤ w.length) (hlarge : 32*Real.log 2 ≤ p*(L : ℝ)) :
    sourceBoundedTargetFailureMass p n L w B ≤
      Real.exp (-p*(w.length : ℝ)/2) + 2*(w.length : ℝ)^2*Real.exp (-p*(L : ℝ)^2/32) :=
  (sourceBoundedTargetFailureMass_le_raw hp hp1 n L w hn B).trans
    (finite_ligation_target_failure_bound hp hp1 L w hL hLw hlarge)

end
end PowerLawSmallRAF
