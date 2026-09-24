import proofs.StartupMarked.EnhancedPath
import proofs.RepeatedFunction.NetSynthesis
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
theorem enhanced_export_total {n : ℕ} (V : NNReal) (hV : 0 < (V : ℝ))
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hh : ∀ i,0 ≤ (z (i+1)).2.2) (hz : StartupMarked.enhancedMission V z) :
    ∃ L,prefixElapsed L (Preorder.frestrictLe L z) ≤ 199 ∧
      199 < prefixElapsed (L+1) (Preorder.frestrictLe (L+1) z) ∧
      (6/25 : ℝ) < markedWindowReward (fun _ => exportReward V) z 0 L := by
  obtain ⟨J,K,_,_,hk,hk',he1⟩ := hz.2 1 100 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨J2,K2,hj2,hj2',hl,hl',he2⟩ := hz.2 100 199 (by norm_num) (by norm_num) (by norm_num)
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

theorem food_only_enhanced_net_synthesis {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hinit : countNonfoodMass (z 0).1 = 0)
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hp : ∀ i,jumpPositiveRate (unboundedPhysicalRate c V 1 basal cat) (z i).1 (z (i+1)))
    (hh : ∀ i,0 ≤ (z (i+1)).2.2) (hz : StartupMarked.enhancedMission V z) :
    ∃ L,prefixElapsed L (Preorder.frestrictLe L z) ≤ 199 ∧
      199 < prefixElapsed (L+1) (Preorder.frestrictLe (L+1) z) ∧
      (6/25 : ℝ) < markedWindowReward (signedSynthesisReward V) z 0 L := by
  obtain ⟨L,hl,hl',he⟩ := enhanced_export_total V hV z hh hz
  have hb := actual_net_synthesis_identity c V basal cat z hc hp L
  rw [hinit,zero_div,zero_add] at hb
  have hn := div_nonneg (count_nonfood_nonneg (z L).1) hV.le
  exact ⟨L,hl,hl',by linarith only [he,hb,hn]⟩

end
end RandomViability
