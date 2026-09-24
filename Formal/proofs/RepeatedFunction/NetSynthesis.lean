import proofs.RepeatedFunction.Mission

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

/-- Net internal creation of nonfood monomer mass, including reverse reactions. -/
def signedSynthesisReward {n : ℕ} (V : NNReal) (N : Molecule n → ℕ)
    (ch : PhysicalCountChannel n) : ℝ :=
  match ch with
  | .inr _ => (countNonfoodMass (unboundedPhysicalNext N ch)-countNonfoodMass N)/V
  | _ => 0

theorem enabled_synthesis_identity {n : ℕ} (V : NNReal)
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n)
    (he : ∀ q,physicalChannelInput ch q ≤ N q) :
    (countNonfoodMass (unboundedPhysicalNext N ch)-countNonfoodMass N)/V+exportReward V ch =
      signedSynthesisReward V N ch := by
  rcases ch with (f|q)|ch
  · simp [unbounded_feed_nonfood_jump,exportReward,signedSynthesisReward]
  · rw [enabled_outflow_nonfood_change N q he]
    simp only [exportReward,signedSynthesisReward]
    ring
  · simp only [exportReward,signedSynthesisReward,add_zero]

theorem actual_net_synthesis_identity {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hp : ∀ i,jumpPositiveRate (unboundedPhysicalRate c V 1 basal cat) (z i).1 (z (i+1))) (K : ℕ) :
    countNonfoodMass (z K).1/V+markedWindowReward (fun _ => exportReward V) z 0 K =
      countNonfoodMass (z 0).1/V+markedWindowReward (signedSynthesisReward V) z 0 K := by
  induction K with
  | zero => simp [markedWindowReward]
  | succ K ih =>
    obtain ⟨ch,hch,hr⟩ := hp K
    obtain ⟨b,hb,hn⟩ := hc K
    have heq : b = ch := Sum.inr.inj (hb.symm.trans hch)
    subst b
    have hen : ∀ q,physicalChannelInput ch q ≤ (z K).1 q := by
      by_contra h
      simp [unboundedPhysicalRate,h] at hr
    have hs := enabled_synthesis_identity V (z K).1 ch hen
    rw [← hn] at hs
    simp only [marked_window_reward_succ,Nat.zero_add,hch,Sum.elim_inr]
    rw [sub_div] at hs
    linarith only [ih,hs]

theorem two_window_export_total {n : ℕ} (V : NNReal) (hV : 0 < (V : ℝ))
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hh : ∀ i,0 ≤ (z (i+1)).2.2) (hz : twoWindowMission V z) :
    ∃ L,prefixElapsed L (Preorder.frestrictLe L z) ≤ 199 ∧
      199 < prefixElapsed (L+1) (Preorder.frestrictLe (L+1) z) ∧
      (1/5 : ℝ) < markedWindowReward (fun _ => exportReward V) z 0 L := by
  obtain ⟨J,K,_,_,hk,hk',he1,_⟩ := hz.2.1
  obtain ⟨J2,K2,hj2,hj2',hl,hl',he2,_⟩ := hz.2.2.1
  have hj := holding_index_unique z hh J2 (J+K) 100 hj2 hj2' hk hk'
  subst J2
  have hpre : 0 ≤ markedWindowReward (fun _ => exportReward V) z 0 J := by
    apply Finset.sum_nonneg
    intro i _
    cases (z (0+i+1)).2.1 with
    | inl u => exact le_rfl
    | inr ch => exact (export_reward_bounds V hV ch).1
  refine ⟨J+K+K2,hl,hl',?_⟩
  rw [marked_window_reward_prefix_shift (fun _ => exportReward V) z (J+K) K2,
    marked_window_reward_prefix_shift (fun _ => exportReward V) z J K]
  linarith only [hpre,he1,he2]

theorem food_only_mission_net_synthesis {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hinit : countNonfoodMass (z 0).1 = 0)
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hp : ∀ i,jumpPositiveRate (unboundedPhysicalRate c V 1 basal cat) (z i).1 (z (i+1)))
    (hh : ∀ i,0 ≤ (z (i+1)).2.2) (hz : twoWindowMission V z) :
    ∃ L,prefixElapsed L (Preorder.frestrictLe L z) ≤ 199 ∧
      199 < prefixElapsed (L+1) (Preorder.frestrictLe (L+1) z) ∧
      (1/5 : ℝ) < markedWindowReward (signedSynthesisReward V) z 0 L := by
  obtain ⟨L,hl,hl',he⟩ := two_window_export_total V hV z hh hz
  have hb := actual_net_synthesis_identity c V basal cat z hc hp L
  rw [hinit,zero_div,zero_add] at hb
  have hn := div_nonneg (count_nonfood_nonneg (z L).1) hV.le
  exact ⟨L,hl,hl',by linarith only [he,hb,hn]⟩

end
end RandomViability
