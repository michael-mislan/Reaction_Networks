import proofs.RandomViability.MarkedRewardWindow
import proofs.RandomViability.PhysicalWindowProbability

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 150000

def markedRewardNoiseBound {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ) (T eta : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  ∀ k s,0 ≤ s → s ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z)) →
    |markedRewardWithinInterval c V basal cat reward T (massExitStop V) z k s| ≤ eta

theorem marked_reward_budget {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ) (T H eta b : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (K : ℕ)
    (hs : ∀ i ≤ K,¬censoredNonfoodStop V T (massExitStop V) i (Preorder.frestrictLe i z))
    (ht : ∀ i < K,(z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z))
    (hh : ∀ i,0 ≤ (z (i+1)).2.2)
    (hB : 0 ≤ H-prefixElapsed K (Preorder.frestrictLe K z))
    (hBcap : H-prefixElapsed K (Preorder.frestrictLe K z) ≤
      min (z (K+1)).2.2 (T-prefixElapsed K (Preorder.frestrictLe K z)))
    (hbound : ∀ i ≤ K,markedRewardDrift c V basal cat reward (z i).1 ≤ b)
    (hnoise : markedRewardNoiseBound c V basal cat reward T eta z) :
    markedWindowReward reward z 0 K ≤ b*H+eta := by
  let B := H-prefixElapsed K (Preorder.frestrictLe K z)
  have hid := marked_reward_window_identity c V basal cat reward T 0 B z 0 K
    (fun i hi => hs (0+i) (by omega)) (fun i hi => ht (0+i) (by omega))
  have hzero : markedRewardWithinInterval c V basal cat reward T (massExitStop V) z 0 0 = 0 := by
    simp [markedRewardWithinInterval,censoredMarkedRewardPrefix]
  simp only [Nat.zero_add,hzero,sub_zero] at hid
  have hsum : (∑ i : Fin K,markedRewardDrift c V basal cat reward (z i).1*(z (i+1)).2.2) ≤
      b*(∑ i : Fin K,(z (i+1)).2.2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hbound i i.isLt.le) (hh i))
  have hlast := mul_le_mul_of_nonneg_right (hbound K le_rfl) hB
  have htime : (∑ i : Fin K,(z (i+1)).2.2)+B = H := by
    change (∑ i : Fin K,(z (i+1)).2.2)+(H-∑ i : Fin K,(z (i+1)).2.2) = H
    ring
  have hi : windowMassIntegral (fun i => markedRewardDrift c V basal cat reward (z i).1)
      (fun i => (z (i+1)).2.2) 0 B K ≤ b*H := by
    simp only [windowMassIntegral,mul_zero,sub_zero]
    calc
      _ ≤ b*(∑ i : Fin K,(z (i+1)).2.2)+b*B := add_le_add hsum hlast
      _ = _ := by rw [← mul_add,htime]
  have he := (abs_le.mp (hnoise K B hB hBcap)).2
  linarith only [hid,hi,he]

/-- The collective certificate plus six noise bounds yields literal marked output. -/
theorem marked_productive_output_from_noise {n : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ)) (T : ℝ) (hT : 100 < T)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hinitM : (countMass (z 0).1 : ℝ)/V ≤ 10)
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hh : ∀ i,0 ≤ (z (i+1)).2.2)
    (hnoiseM : massNoiseBound c V basal cat T (1/4) z)
    (hcert : windowMassCertificate V z)
    (hnoiseE : markedRewardNoiseBound c V basal cat (fun _ => exportReward V) T (1/40) z)
    (hnoiseB : markedRewardNoiseBound c V basal cat (positiveBasalReward V) T (1/100) z) :
    ∃ J K,prefixElapsed J (Preorder.frestrictLe J z) ≤ 1 ∧
      1 < prefixElapsed (J+1) (Preorder.frestrictLe (J+1) z) ∧
      prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤ 100 ∧
      100 < prefixElapsed (J+K+1) (Preorder.frestrictLe (J+K+1) z) ∧
      (1/10 : ℝ) < markedWindowReward (fun _ => exportReward V) z J K ∧
      markedWindowReward (positiveBasalReward V) z 0 (J+K) <
        markedWindowReward (fun _ => exportReward V) z J K/4 := by
  obtain ⟨J,K,hfirst,hfirstNext,hlast,hlastNext,hI⟩ := hcert
  have hm := prefix_elapsed_monotone z hh
  have hmass : ∀ i ≤ J+K,(countMass (z i).1 : ℝ) ≤ 11*V := by
    intro i hi
    have hg := physical_mass_localization hn c V hV basal cat T z hinitM hc hh hnoiseM i
      ((hm hi).trans_lt (hlast.trans_lt hT))
    have he := (div_le_iff₀ hV).mp hg
    nlinarith only [he,hV]
  have hactive : ∀ i ≤ J+K,¬censoredNonfoodStop V T (massExitStop V) i (Preorder.frestrictLe i z) := by
    intro i hi
    exact mass_exit_active_before_first_exit V T z (by omega : i < J+K+1)
      (fun j hj => hmass j (by omega)) ((hm hi).trans_lt (hlast.trans_lt hT))
  have hcomplete : ∀ i < J+K,(z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z) := by
    intro i hi
    have he := (hm (show i+1 ≤ J+K by omega)).trans_lt (hlast.trans_lt hT)
    dsimp only at he
    rw [prefixElapsed_restrict_succ] at he
    linarith only [he]
  have ha0 : 0 ≤ 1-prefixElapsed J (Preorder.frestrictLe J z) := sub_nonneg.mpr hfirst
  have hb0 : 0 ≤ 100-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) := sub_nonneg.mpr hlast
  have ha : 1-prefixElapsed J (Preorder.frestrictLe J z) ≤
      min (z (J+1)).2.2 (T-prefixElapsed J (Preorder.frestrictLe J z)) := by
    apply le_min
    · rw [prefixElapsed_restrict_succ] at hfirstNext
      linarith only [hfirstNext]
    · linarith only [hT]
  have hb' : 100-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤
      min (z (J+K+1)).2.2 (T-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z)) := by
    apply le_min
    · rw [prefixElapsed_restrict_succ] at hlastNext
      linarith only [hlastNext]
    · linarith only [hT]
  have hE := marked_reward_window_identity c V basal cat (fun _ => exportReward V) T
    (1-prefixElapsed J (Preorder.frestrictLe J z))
    (100-prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z)) z J K
    (fun i hi => hactive (J+i) (by omega)) (fun i hi => hcomplete (J+i) (by omega))
  rw [export_window_compensator c V hV basal cat z J K] at hE
  have he0 := abs_le.mp (hnoiseE J _ ha0 ha)
  have he1 := abs_le.mp (hnoiseE (J+K) _ hb0 hb')
  have hEbound : physicalWindowNonfoodIntegral V z J K-(1/20 : ℝ) ≤
      markedWindowReward (fun _ => exportReward V) z J K := by linarith only [hE,he0.2,he1.1]
  have hB := marked_reward_budget c V basal cat (positiveBasalReward V) T 100 (1/100)
    (1936*(1/500000000 : ℝ)) z (J+K) hactive hcomplete hh hb0 hb'
    (fun i hi => positive_basal_reward_drift c V hV basal cat (z i).1 _ (by norm_num) hb (hmass i hi)) hnoiseB
  exact ⟨J,K,hfirst,hfirstNext,hlast,hlastNext,
    compensated_productive_margin _ _ _ hI hEbound hB⟩

end
end RandomViability
