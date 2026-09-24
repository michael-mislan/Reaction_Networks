import proofs.RandomViability.MarkedRewardWindow
import proofs.StartupMarked.RetainedReward

namespace StartupMarked
open Classical RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

theorem window_integral_mono (f g w : ℕ → ℝ) (A B : ℝ) (K : ℕ)
    (hfg : ∀ i ≤ K,f i ≤ g i) (hw : ∀ i,0 ≤ w i)
    (hAw : A ≤ w 0) (hB : 0 ≤ B) (hAB : K=0 → A ≤ B) :
    windowMassIntegral f w A B K ≤ windowMassIntegral g w A B K := by
  induction K generalizing B with
  | zero =>
    have hh := mul_le_mul_of_nonneg_right (hfg 0 le_rfl) (sub_nonneg.mpr (hAB rfl))
    simp only [windowMassIntegral,Fin.sum_univ_zero,zero_add]
    nlinarith only [hh]
  | succ K ih =>
    have hs := mul_le_mul_of_nonneg_right (hfg (K+1) le_rfl) hB
    have hind : windowMassIntegral f w A (w K) K ≤ windowMassIntegral g w A (w K) K := by
      exact ih (w K) (fun i hi => hfg i (by omega)) (hw K)
        (by intro hk; subst K; exact hAw)
    simp only [windowMassIntegral,Fin.sum_univ_castSucc] at hind ⊢
    change (∑ i : Fin K,f i*w i)+f K*w K+f (K+1)*B-f 0*A ≤
      (∑ i : Fin K,g i*w i)+g K*w K+g (K+1)*B-g 0*A
    linarith only [hind,hs]

theorem retained_window_sum_le {n : ℕ} (V : NNReal) (r : Reaction n) (k₀ : ℕ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (J K : ℕ)
    (hk₀ : 0 < k₀) (hfloor : ∀ i < K,k₀ ≤ (z (J+i)).1 (reactionProduct r))
    (hc : ∀ i < K,jumpConsistent unboundedPhysicalNext (z (J+i)).1 (z (J+i+1))) :
    markedWindowReward (cutoffReward V r k₀) z J K ≤
      countPotential V r (z (J+K)).1-countPotential V r (z J).1 := by
  have hstep (i : ℕ) (hi : i < K) :
      (z (J+i+1)).2.1.elim (fun _ => (0 : ℝ)) (cutoffReward V r k₀ (z (J+i)).1) ≤
        countPotential V r (z (J+i+1)).1-countPotential V r (z (J+i)).1 := by
    obtain ⟨ch,hmark,hnext⟩ := hc i hi
    rw [hmark,Sum.elim_inr,cutoff_agrees_above_floor V r k₀ _ ch (hfloor i hi),hnext]
    exact retained_reward_le_potential_increment V r _ ch (hk₀.trans_le (hfloor i hi))
  have htel (L : ℕ) : (∑ i : Fin L,(countPotential V r (z (J+i+1)).1-
      countPotential V r (z (J+i)).1)) = countPotential V r (z (J+L)).1-countPotential V r (z J).1 := by
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last]
      rw [ih]
      simp only [Nat.add_succ]
      ring
  rw [← htel K]
  exact Finset.sum_le_sum (fun i _ => hstep i i.isLt)

end
end StartupMarked
