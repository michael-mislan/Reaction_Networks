import proofs.RandomViability.PhysicalWindowEndpoint

namespace RandomViability
open Classical Set RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 150000

/-- Actual occupation integral between arbitrary clock endpoints, without restart. -/
def physicalIntervalNonfoodIntegral {n : ℕ} (V : NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (J K : ℕ) (a b : ℝ) : ℝ :=
  windowMassIntegral (fun i => nonfoodMass (fun q => ((z (J+i)).1 q : ℝ)/V))
    (fun i => (z (J+i+1)).2.2)
    (a-prefixElapsed J (Preorder.frestrictLe J z))
    (b-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z)) K

theorem physical_interval_potential_gain {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ)) (hcatCap : ∀ r q,(cat r q : ℝ) ≤ 16)
    (hfood : ∀ q,molLength q ≤ 2 → c q = ∅) (r : Reaction n)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hsel : r ∈ c (reactionProduct r))
    (hbas : (1/500000000 : ℝ) ≤ basal r) (hcat : 4 ≤ (cat r (reactionProduct r) : ℝ))
    (A0 B0 T : ℝ) (hAB0 : A0 ≤ B0) (hT : B0 < T)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (J K : ℕ)
    (hfirst : prefixElapsed J (Preorder.frestrictLe J z) ≤ A0)
    (hfirstNext : A0 < prefixElapsed (J+1) (Preorder.frestrictLe (J+1) z))
    (hlast : prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤ B0)
    (hlastNext : B0 < prefixElapsed (J+K+1) (Preorder.frestrictLe (J+K+1) z))
    (hh : ∀ i,0 ≤ (z (i+1)).2.2)
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hactive : ∀ i ≤ J+K,¬censoredNonfoodStop V T (massExitStop V) i (Preorder.frestrictLe i z))
    (hfloor : ∀ i ≤ K,(1/3000000000000000000 : ℝ) ≤ ((z (J+i)).1 (reactionProduct r) : ℝ)/V)
    (hnoiseL : coordinateNoiseBound c V basal cat (reactionLeft r) T (1/100000) z)
    (hnoiseR : coordinateNoiseBound c V basal cat (reactionRight r) T (1/100000) z)
    (hnoiseP : coordinateNoiseBound c V basal cat (reactionProduct r) T (1/300000000000000000000) z) :
    (B0-A0)*((19/10 : ℝ)-480*(1/500000000 : ℝ))-640*physicalIntervalNonfoodIntegral V z J K A0 B0 ≤
      correctedPotential c V basal cat r T z (J+K)
        (B0-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z))-
      correctedPotential c V basal cat r T z J (A0-prefixElapsed J (Preorder.frestrictLe J z)) := by
  let A := A0-prefixElapsed J (Preorder.frestrictLe J z)
  let B := B0-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z)
  let w := fun i => (z (J+i+1)).2.2
  let h := fun i => if i=K then B else w i
  let M := fun i => nonfoodMass (fun q => ((z (J+i)).1 q : ℝ)/V)
  let P := fun i => correctedPotential c V basal cat r T z (J+i)
  have hm := prefix_elapsed_monotone z hh
  have hA0 : 0 ≤ A := sub_nonneg.mpr hfirst
  have hB0 : 0 ≤ B := sub_nonneg.mpr hlast
  have hAw : A ≤ w 0 := by
    have he := hfirstNext
    rw [prefixElapsed_restrict_succ] at he
    dsimp [A,w]
    linarith only [he]
  have hBw : B ≤ w K := by
    have he := hlastNext
    rw [prefixElapsed_restrict_succ] at he
    dsimp [B,w]
    linarith only [he]
  have hAB : K=0 → A ≤ B := by
    intro hk
    subst K
    dsimp [A,B]
    linarith
  have hA : A ≤ h 0 := by
    dsimp [h]
    split_ifs with hk
    · exact hAB hk.symm
    · exact hAw
  have hh' : ∀ i,0 ≤ h i := by
    intro i
    dsimp [h]
    split_ifs
    · exact hB0
    · exact hh (J+i)
  have hfull : ∀ i < K,h i = w i := by
    intro i hi
    exact if_neg (ne_of_lt hi)
  have hlimit : ∀ i ≤ K,h i ≤ min (z (J+i+1)).2.2
      (T-prefixElapsed (J+i) (Preorder.frestrictLe (J+i) z)) := by
    intro i hi
    by_cases hik : i=K
    · subst i
      simp only [h,if_pos rfl]
      apply le_min hBw
      dsimp [B]
      linarith only [hT]
    · have hil : i < K := by omega
      rw [hfull i hil]
      apply le_min le_rfl
      have he := (hm (show J+i+1 ≤ J+K by omega)).trans hlast
      dsimp only at he
      rw [prefixElapsed_restrict_succ] at he
      dsimp [w]
      linarith only [he,hT]
  have hmass : ∀ i ≤ K,(countMass (z (J+i)).1 : ℝ) ≤ 11*V := by
    intro i hi
    by_contra hm'
    exact hactive (J+i) (by omega) (Or.inr (Or.inl hm'))
  have hgain : ∀ i ≤ K,∀ a b,(if i=0 then A else 0) ≤ a → a ≤ b → b ≤ h i →
      (b-a)*((19/10 : ℝ)-480*(1/500000000 : ℝ)-640*M i) ≤ P i b-P i a := by
    intro i hi a b ha hab hbh
    have ha0 : 0 ≤ a := by
      by_cases hi0 : i=0
      · rw [if_pos hi0] at ha
        exact hA0.trans ha
      · simpa only [if_neg hi0] using ha
    exact physical_holding_potential_gain c V hV basal cat (1/500000000) (by norm_num)
      hb hcatCap hfood r hl hr hlen huw huz hwz hsel hbas hcat T z (J+i) a b ha0 hab
      (hbh.trans (hlimit i hi)) (hactive _ (by omega)) (hmass i hi) (hfloor i hi)
      hnoiseL hnoiseR hnoiseP
  have hlink : ∀ i < K,P i (h i) = P (i+1) 0 := by
    intro i hi
    have he := hlimit i hi.le
    rw [hfull i hi] at he
    have hp := corrected_potential_link c V basal cat r T z (J+i) (hc _) (hactive _ (by omega))
      (le_trans he (min_le_right _ _))
    simpa only [P,hfull i hi,w,Nat.add_assoc] using hp
  have hg := finite_window_growth P M h A ((19/10 : ℝ)-480*(1/500000000 : ℝ)) 640 K B
    hA hh' hgain hlink hB0 (by simp [h]) hAB
  have hs : (∑ i : Fin K,h i) = ∑ i : Fin K,w i := by
    apply Finset.sum_congr rfl
    intro i _
    exact hfull i i.isLt
  have hsM : (∑ i : Fin K,M i*h i) = ∑ i : Fin K,M i*w i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hfull i i.isLt]
  have hd : windowDuration h A B K = B0-A0 := by
    unfold windowDuration
    rw [hs]
    simpa only [windowDuration] using
      physical_window_duration z J K A0 B0
  rw [hd] at hg
  simp only [windowMassIntegral,hsM] at hg
  change ((19/10 : ℝ)-480*(1/500000000 : ℝ))*(B0-A0)-
    640*physicalIntervalNonfoodIntegral V z J K A0 B0 ≤ P K B-P 0 A at hg
  simpa only [P,Nat.add_zero,mul_comm] using hg


end
end RandomViability
