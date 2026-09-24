import proofs.StartupMarked.WindowAlgebra
import proofs.StartupMarked.PotentialBounds

namespace StartupMarked
open Classical RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 80000

theorem source_window_occupation_quota {n : ℕ} (hn : 2 ≤ n) (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 1000000000000000000000000 ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (r : Reaction n)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16) (hfood : ∀ z,molLength z ≤ 2 → cfg z = ∅)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hlen : molLength (reactionProduct r) = 4) (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hsel : r ∈ cfg (reactionProduct r)) (hcat : 4 ≤ (cat r (reactionProduct r) : ℝ))
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (J K : ℕ)
    (a b : ℝ) (hab : a ≤ b) (hbT : b ≤ 200)
    (hfirstNext : a < prefixElapsed (J+1) (Preorder.frestrictLe (J+1) z))
    (hlast : prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤ b)
    (hh : ∀ i,0 ≤ (z (i+1)).2.2)
    (hconsistent : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hactive : ∀ i ≤ K,¬censoredNonfoodStop V 200 (massExitStop V) (J+i) (Preorder.frestrictLe (J+i) z))
    (hfloor : ∀ i ≤ K,(1/3000000000000000000 : ℝ) ≤ ((z (J+i)).1 (reactionProduct r) : ℝ)/V)
    (hnoiseA : |markedRewardWithinInterval cfg V basal cat (cutoffReward V r stockCutoff)
      200 (massExitStop V) z J (a-prefixElapsed J (Preorder.frestrictLe J z))| ≤ 15)
    (hnoiseB : |markedRewardWithinInterval cfg V basal cat (cutoffReward V r stockCutoff)
      200 (massExitStop V) z (J+K) (b-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z))| ≤ 15) :
    ((19/10)*(b-a)-82)/624 < windowMassIntegral
      (fun i => nonfoodMass (fun q => ((z (J+i)).1 q : ℝ)/V))
      (fun i => (z (J+i+1)).2.2)
      (a-prefixElapsed J (Preorder.frestrictLe J z))
      (b-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z)) K := by
  have hv : 0 < (V : ℝ) := by linarith
  let A := a-prefixElapsed J (Preorder.frestrictLe J z)
  let B := b-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z)
  let w := fun i => (z (J+i+1)).2.2
  let M := fun i => nonfoodMass (fun q => ((z (J+i)).1 q : ℝ)/V)
  let D := fun i => markedRewardDrift cfg V basal cat (cutoffReward V r stockCutoff) (z (J+i)).1
  have hk (i : ℕ) (hi : i ≤ K) : stockCutoff ≤ (z (J+i)).1 (reactionProduct r) := by
    have hf := (le_div_iff₀ hv).mp (hfloor i hi)
    have hx : (333333 : ℝ) < (z (J+i)).1 (reactionProduct r) := by nlinarith only [hf,hV]
    have hn' : 333333 < (z (J+i)).1 (reactionProduct r) := by exact_mod_cast hx
    exact hn'
  have hmass (i : ℕ) (hi : i ≤ K) : (countMass (z (J+i)).1 : ℝ) ≤ 11*V := by
    by_contra h
    exact hactive i hi (Or.inr (Or.inl h))
  have hd (i : ℕ) (hi : i ≤ K) : 19/10-624*M i ≤ D i :=
    source_cutoff_drift hn cfg V hV basal cat _ r hb hc hfood (hmass i hi)
      hl hr hlen huw huz hwz hsel hcat (hk i hi)
  have hAw : A ≤ w 0 := by
    have he := hfirstNext
    rw [prefixElapsed_restrict_succ] at he
    dsimp [A,w]
    simpa only [Nat.add_zero] using (show a-prefixElapsed J (Preorder.frestrictLe J z) ≤ (z (J+1)).2.2 by linarith)
  have hB : 0 ≤ B := sub_nonneg.mpr hlast
  have hAB : K=0 → A ≤ B := by intro he; subst K; dsimp [A,B]; linarith
  have hi := window_integral_mono (fun i => 19/10-624*M i) D w A B K hd (fun i => hh (J+i)) hAw hB hAB
  have he : windowMassIntegral (fun i => 19/10-624*M i) w A B K =
      (19/10)*windowDuration w A B K-624*windowMassIntegral M w A B K := by
    simp only [windowMassIntegral,windowDuration,sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum,mul_assoc]
    ring
  have htime : windowDuration w A B K = b-a := physical_window_duration z J K a b
  rw [he,htime] at hi
  have ht : ∀ i < K,(z (J+i+1)).2.2 ≤ 200-prefixElapsed (J+i) (Preorder.frestrictLe (J+i) z) := by
    intro i hil
    have hm := prefix_elapsed_monotone z hh (show J+i+1 ≤ J+K by omega)
    dsimp only at hm
    rw [prefixElapsed_restrict_succ] at hm
    linarith only [hm,hlast,hbT]
  have hid := marked_reward_window_identity cfg V basal cat (cutoffReward V r stockCutoff)
    200 A B z J K hactive ht
  have hpath := retained_window_sum_le V r stockCutoff z J K (by decide)
    (fun i hi => hk i hi.le) (fun i _ => hconsistent (J+i))
  have hcap : ((z (J+K)).1 (reactionProduct r) : ℝ)/V ≤ 11/4 := by
    have hs : molLength (reactionProduct r)*(z (J+K)).1 (reactionProduct r) ≤ countMass (z (J+K)).1 :=
      Finset.single_le_sum (fun q _ => Nat.zero_le (molLength q*(z (J+K)).1 q)) (Finset.mem_univ _)
    rw [hlen] at hs
    have hs' : 4*((z (J+K)).1 (reactionProduct r) : ℝ) ≤ countMass (z (J+K)).1 := by exact_mod_cast hs
    apply (div_le_iff₀ hv).mpr
    linarith only [hs',hmass K le_rfl]
  have hpen := count_potential_endpoint V hv r (z J).1 (z (J+K)).1
    (by simpa only [Nat.add_zero] using hfloor 0 (Nat.zero_le K))
    (lt_of_lt_of_le (by decide : 0 < stockCutoff) (hk K le_rfl)) hcap
  have hna := (abs_le.mp hnoiseA).2
  have hnb := (abs_le.mp hnoiseB).1
  change _ < windowMassIntegral M w A B K
  change _ = windowMassIntegral D w A B K+_-_ at hid
  dsimp only [A,B] at hid
  dsimp only [A,B] at hi ⊢
  linarith only [hi,hid,hpath,hpen,hna,hnb]

end
end StartupMarked
