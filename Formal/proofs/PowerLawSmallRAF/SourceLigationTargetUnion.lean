import proofs.PowerLawSmallRAF.SourceLigationTargetProbability

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 100000

def sourceLigationTargetsFailureMass (p : ℝ) (n L : Nat) (W : Finset LigationWord)
    (T : Finset (Reaction n) → Finset (Reaction n)) : ℝ :=
  ∑ H : Finset (Reaction n), if ∃ w ∈ W,
    (∀ u ∈ ligationTargetNucleus L w, SourceLigationGenerated n (T H) u) ∧
      ¬ SourceLigationGenerated n (T H) w then bernoulliSubsetRowWeight p H else 0

theorem sourceLigationTargetsFailureMass_le_sum {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (n L : Nat) (W : Finset LigationWord)
    (T : Finset (Reaction n) → Finset (Reaction n)) :
    sourceLigationTargetsFailureMass p n L W T ≤
      ∑ w ∈ W, sourceLigationTargetFailureMass p n L w T := by
  unfold sourceLigationTargetsFailureMass sourceLigationTargetFailureMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro H _
  have hw := bernoulliSubsetRowWeight_nonneg hp hp1 H
  by_cases he : ∃ w ∈ W,
      (∀ u ∈ ligationTargetNucleus L w, SourceLigationGenerated n (T H) u) ∧
        ¬ SourceLigationGenerated n (T H) w
  · rw [if_pos he]
    obtain ⟨w, hwW, hbad⟩ := he
    calc
      _ = (if (∀ u ∈ ligationTargetNucleus L w, SourceLigationGenerated n (T H) u) ∧
          ¬ SourceLigationGenerated n (T H) w then bernoulliSubsetRowWeight p H else 0) :=
        (if_pos hbad).symm
      _ ≤ _ := Finset.single_le_sum (s := W) (a := w)
        (f := fun v : LigationWord => if
          (∀ u ∈ ligationTargetNucleus L v, SourceLigationGenerated n (T H) u) ∧
            ¬ SourceLigationGenerated n (T H) v then bernoulliSubsetRowWeight p H else 0)
        (fun v _ => by dsimp only; split_ifs <;> linarith only [hw]) hwW
  · rw [if_neg he]
    exact Finset.sum_nonneg (fun v _ => by split_ifs <;> linarith only [hw])

/-- No independence between target-generation events is required. The set W
is fixed for the high-field experiment (and may be chosen from low rows). -/
theorem source_ligation_targets_failure_bound {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (n L m : Nat) (W : Finset LigationWord)
    (hW : ∀ w ∈ W, m ≤ w.length ∧ w.length ≤ n)
    (T : Finset (Reaction n) → Finset (Reaction n)) (hT : ∀ H, H ⊆ T H)
    (hL : 4 ≤ L) (hLm : L ≤ m) (hlarge : 32*Real.log 2 ≤ p*(L : ℝ)) :
    sourceLigationTargetsFailureMass p n L W T ≤
      (W.card : ℝ)*(Real.exp (-p*(m : ℝ)/2) +
        2*(n : ℝ)^2*Real.exp (-p*(L : ℝ)^2/32)) := by
  apply (sourceLigationTargetsFailureMass_le_sum hp hp1 n L W T).trans
  calc
    _ ≤ ∑ _w ∈ W, (Real.exp (-p*(m : ℝ)/2) +
        2*(n : ℝ)^2*Real.exp (-p*(L : ℝ)^2/32)) := by
      apply Finset.sum_le_sum
      intro w hw
      obtain ⟨hmin,hmax⟩ := hW w hw
      apply (source_ligation_target_failure_bound hp hp1 n L w hmax T hT hL (hLm.trans hmin) hlarge).trans
      have hm : (m : ℝ) ≤ w.length := by exact_mod_cast hmin
      have hn : (w.length : ℝ) ≤ n := by exact_mod_cast hmax
      apply add_le_add
      · apply Real.exp_le_exp.mpr
        nlinarith only [mul_nonneg hp (sub_nonneg.mpr hm)]
      · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        have hs : (w.length : ℝ)^2 ≤ (n : ℝ)^2 :=
          pow_le_pow_left₀ (by positivity) hn 2
        nlinarith only [hs]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

end
end PowerLawSmallRAF
