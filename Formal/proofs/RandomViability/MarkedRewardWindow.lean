import proofs.RandomViability.MarkedRewardInterval
import proofs.RandomViability.PhysicalWindowPotential

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

/-- The literal marked jumps after index J through index J+K. -/
def markedWindowReward {n : ℕ}
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (J K : ℕ) : ℝ :=
  ∑ i : Fin K,(z (J+i+1)).2.1.elim (fun _ => 0) (reward (z (J+i)).1)

theorem marked_reward_prefix_shift {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (J K : ℕ) :
    censoredMarkedRewardPrefix c V basal cat reward T (massExitStop V) z (J+K) =
      censoredMarkedRewardPrefix c V basal cat reward T (massExitStop V) z J+
        ∑ i : Fin K,censoredMarkedRewardCompensation c V basal cat reward T (massExitStop V)
          (J+i) (Preorder.frestrictLe (J+i) z) (z (J+i+1)) := by
  induction K with
  | zero => simp only [Fin.sum_univ_zero,add_zero]
  | succ K ih =>
    have hsucc (L : ℕ) : censoredMarkedRewardPrefix c V basal cat reward T (massExitStop V) z (L+1) =
        censoredMarkedRewardPrefix c V basal cat reward T (massExitStop V) z L+
          censoredMarkedRewardCompensation c V basal cat reward T (massExitStop V)
            L (Preorder.frestrictLe L z) (z (L+1)) := by
      unfold censoredMarkedRewardPrefix
      rw [Fin.sum_univ_castSucc]
      rfl
    rw [Nat.add_succ,hsucc,ih,Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    ring

/-- Exact reward-minus-compensator identity, including both partial endpoints. -/
theorem marked_reward_window_identity {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ) (T A B : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (J K : ℕ)
    (hs : ∀ i ≤ K,¬censoredNonfoodStop V T (massExitStop V) (J+i) (Preorder.frestrictLe (J+i) z))
    (ht : ∀ i < K,(z (J+i+1)).2.2 ≤ T-prefixElapsed (J+i) (Preorder.frestrictLe (J+i) z)) :
    markedWindowReward reward z J K =
      windowMassIntegral (fun i => markedRewardDrift c V basal cat reward (z (J+i)).1)
        (fun i => (z (J+i+1)).2.2) A B K+
      markedRewardWithinInterval c V basal cat reward T (massExitStop V) z (J+K) B-
      markedRewardWithinInterval c V basal cat reward T (massExitStop V) z J A := by
  have hs0 : ¬censoredNonfoodStop V T (massExitStop V) J (Preorder.frestrictLe J z) := by
    simpa only [Nat.add_zero] using hs 0 (Nat.zero_le K)
  have he (i : Fin K) : censoredMarkedRewardCompensation c V basal cat reward T (massExitStop V)
      (J+i) (Preorder.frestrictLe (J+i) z) (z (J+i+1)) =
      (z (J+i+1)).2.1.elim (fun _ => 0) (reward (z (J+i)).1)-
        markedRewardDrift c V basal cat reward (z (J+i)).1*(z (J+i+1)).2.2 := by
    unfold censoredMarkedRewardCompensation
    dsimp only
    rw [if_neg (hs i i.isLt.le),if_pos (ht i i.isLt),min_eq_left (ht i i.isLt)]
    rfl
  simp only [markedRewardWithinInterval,if_neg hs0,if_neg (hs K le_rfl)]
  rw [marked_reward_prefix_shift]
  simp_rw [he]
  simp only [Finset.sum_sub_distrib,windowMassIntegral,markedWindowReward,Nat.add_zero]
  ring

theorem export_window_compensator {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (J K : ℕ) :
    windowMassIntegral (fun i => markedRewardDrift c V basal cat (fun _ => exportReward V) (z (J+i)).1)
      (fun i => (z (J+i+1)).2.2)
      (1-prefixElapsed J (Preorder.frestrictLe J z))
      (100-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z)) K =
        physicalWindowNonfoodIntegral V z J K := by
  have he (N : Molecule n → ℕ) : markedRewardDrift c V basal cat (fun _ => exportReward V) N =
      nonfoodMass (fun q => (N q : ℝ)/V) :=
    (export_reward_drift c V hV basal cat N).trans (count_nonfood_normalized N V)
  simp only [he,physicalWindowNonfoodIntegral]

end
end RandomViability
