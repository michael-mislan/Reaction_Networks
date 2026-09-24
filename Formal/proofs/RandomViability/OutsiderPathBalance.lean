import proofs.RandomViability.OutsiderSignedReward
import proofs.RandomViability.PhysicalOutputEvent
import proofs.RandomViability.CoordinateObservedPath

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 80000

theorem outsider_signed_prefix_identity {n : ℕ} (q : Molecule n) (V : NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1))) (K : ℕ) :
    1001*markedWindowReward (outsiderSignedReward q V) z 0 K =
      markedWindowReward (positiveBasalReward V) z 0 K+
      markedWindowReward (normalizedPositiveCatalyticReward V) z 0 K+
      2000*(((z K).1 q : ℝ)-((z 0).1 q : ℝ))/V := by
  induction K with
  | zero => simp [markedWindowReward]
  | succ K ih =>
    have hi := consistent_coordinate_increment V q _ _ (hc K)
    obtain ⟨ch,hch,hn⟩ := hc K
    simp only [marked_window_reward_succ,Nat.zero_add,hch,Sum.elim_inr]
    simp only [hch,Sum.elim_inr] at hi
    have hstep : 2000*(((z (K+1)).1 q : ℝ)-((z 0).1 q : ℝ))/V =
        2000*(((z K).1 q : ℝ)-((z 0).1 q : ℝ))/V+
        2000*coordinateConcentrationJump V q (z K).1 ch := by
      rw [hi]
      ring
    rw [show outsiderSignedReward q V (z K).1 ch =
      (positiveBasalReward V (z K).1 ch+normalizedPositiveCatalyticReward V (z K).1 ch+
        2000*coordinateConcentrationJump V q (z K).1 ch)/1001 from rfl]
    linarith only [ih,hstep]

theorem output_forces_outsider_reward {n : ℕ} (q : Molecule n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hinit : countNonfoodMass (z 0).1 = 0) (hq0 : (z 0).1 q = 0)
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hp : ∀ i,jumpPositiveRate (unboundedPhysicalRate c V 1 basal cat) (z i).1 (z (i+1)))
    (hz : physicalOutputEvent V z) :
    ∃ L,prefixElapsed L (Preorder.frestrictLe L z) ≤ 100 ∧
      100 < prefixElapsed (L+1) (Preorder.frestrictLe (L+1) z) ∧
      (1/10010 : ℝ) < markedWindowReward (outsiderSignedReward q V) z 0 L := by
  obtain ⟨J,K,_,_,hl,hl',he⟩ := hz.2
  have hbalance := marked_nonfood_prefix_balance c V hV basal cat z hc hp (J+K)
  have hidentity := outsider_signed_prefix_identity q V z hc (J+K)
  rw [hinit,zero_div,zero_add,marked_window_reward_prefix_shift (fun _ => exportReward V) z J K] at hbalance
  rw [hq0,Nat.cast_zero,sub_zero] at hidentity
  have hpre : 0 ≤ markedWindowReward (fun _ => exportReward V) z 0 J := by
    apply Finset.sum_nonneg
    intro i _
    cases (z (0+i+1)).2.1 with
    | inl u => exact le_rfl
    | inr ch => exact (export_reward_bounds V hV ch).1
  have hlast := div_nonneg (count_nonfood_nonneg (z (J+K)).1) hV.le
  have hq : 0 ≤ 2000*((z (J+K)).1 q : ℝ)/V := by positivity
  exact ⟨J+K,hl,hl',by linarith only [hbalance,hidentity,hpre,hlast,hq,he]⟩

theorem output_forces_outsider_noise {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (q : Molecule n) (r : Reaction n) (hiso : SingleLocalIncidence singleIncidenceCutoff c q r)
    (hout : OutsiderFoodIncidence r q) (hsmall : molLength q ≤ singleIncidenceCutoff+2)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hcat : ∀ r q,(cat r q : ℝ) ≤ 16)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hinit : countNonfoodMass (z 0).1 = 0) (hq0 : (z 0).1 q = 0)
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hp : ∀ i,jumpPositiveRate (unboundedPhysicalRate c V 1 basal cat) (z i).1 (z (i+1)))
    (hh : ∀ i,0 ≤ (z (i+1)).2.2) (hz : physicalOutputEvent V z) :
    ¬markedRewardNoiseBound c V basal cat (outsiderSignedReward q V) 101 (1/100000) z := by
  intro hnoise
  obtain ⟨L,hl,hl',he⟩ := output_forces_outsider_reward q c V hV basal cat z hinit hq0 hc hp hz
  have hbound := localized_reward_budget c V basal cat (outsiderSignedReward q V)
    ((37282993/46875000000)/1001) (1/100000) z L hz.1 hh hl hl'
    (fun N hM => isolated_outsider_signed_drift_bound c q r hiso hout hsmall V hV basal cat hb hcat N hM) hnoise
  linarith only [hbound,he]

end
end RandomViability
