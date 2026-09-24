import proofs.RandomViability.MarkedMassBalance
import proofs.RandomViability.ProductiveControl

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 150000

/-- Signed catalytic nonfood input, retaining reverse firings. -/
def normalizedSignedCatalyticReward {n : ℕ} (V : NNReal) (N : Molecule n → ℕ)
    (ch : PhysicalCountChannel n) : ℝ :=
  match ch with
  | .inr (.inr _) => (countNonfoodMass (unboundedPhysicalNext N ch)-countNonfoodMass N)/V
  | _ => 0

theorem enabled_nonfood_signed_budget {n : ℕ} (V : NNReal) (hV : 0 < (V : ℝ))
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n)
    (he : ∀ q,physicalChannelInput ch q ≤ N q) :
    (countNonfoodMass (unboundedPhysicalNext N ch)-countNonfoodMass N)/V+exportReward V ch ≤
      positiveBasalReward V N ch+normalizedSignedCatalyticReward V N ch := by
  rcases ch with (f|q)|(b|d)
  · simp [unbounded_feed_nonfood_jump,exportReward,positiveBasalReward,normalizedSignedCatalyticReward]
  · rw [enabled_outflow_nonfood_change N q he]
    simp only [exportReward,positiveBasalReward,normalizedSignedCatalyticReward]
    ring_nf
    exact le_rfl
  · simp only [exportReward,positiveBasalReward,normalizedSignedCatalyticReward,add_zero]
    exact div_le_div_of_nonneg_right (le_max_right _ _) hV.le
  · simp only [exportReward,positiveBasalReward,normalizedSignedCatalyticReward,add_zero,zero_add]
    exact le_rfl

theorem marked_nonfood_signed_prefix_balance {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hp : ∀ i,jumpPositiveRate (unboundedPhysicalRate c V 1 basal cat) (z i).1 (z (i+1))) (K : ℕ) :
    countNonfoodMass (z K).1/V+markedWindowReward (fun _ => exportReward V) z 0 K ≤
      countNonfoodMass (z 0).1/V+markedWindowReward (positiveBasalReward V) z 0 K+
        markedWindowReward (normalizedSignedCatalyticReward V) z 0 K := by
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
    have hstep := enabled_nonfood_signed_budget V hV (z K).1 ch hen
    rw [← hn] at hstep
    simp only [marked_window_reward_succ,Nat.zero_add,hch,Sum.elim_inr]
    rw [sub_div] at hstep
    linarith only [ih,hstep]

theorem marked_success_forces_signed_catalytic {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (r : Reaction n)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hinit : countNonfoodMass (z 0).1 = 0)
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hp : ∀ i,jumpPositiveRate (unboundedPhysicalRate c V 1 basal cat) (z i).1 (z (i+1)))
    (hz : finiteMarkedSuccess V r z) :
    ∃ L,prefixElapsed L (Preorder.frestrictLe L z) ≤ 100 ∧
      100 < prefixElapsed (L+1) (Preorder.frestrictLe (L+1) z) ∧
      (3/40 : ℝ) < markedWindowReward (normalizedSignedCatalyticReward V) z 0 L := by
  obtain ⟨J,K,_,_,hl,hl',he,hb⟩ := hz.2.2
  have hbalance := marked_nonfood_signed_prefix_balance c V hV basal cat z hc hp (J+K)
  rw [hinit,zero_div,zero_add,marked_window_reward_prefix_shift (fun _ => exportReward V) z J K] at hbalance
  have hpre : 0 ≤ markedWindowReward (fun _ => exportReward V) z 0 J := by
    apply Finset.sum_nonneg
    intro i _
    cases hm : (z (0+i+1)).2.1 with
    | inl u => exact le_rfl
    | inr ch => exact (export_reward_bounds V hV ch).1
  have hlast : 0 ≤ countNonfoodMass (z (J+K)).1/V := div_nonneg (count_nonfood_nonneg _) hV.le
  refine ⟨J+K,hl,hl',?_⟩
  linarith only [hbalance,hpre,hlast,he,hb]


theorem disabled_signed_reward_prefix_zero {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (basal : Reaction n → NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hp : ∀ i,jumpPositiveRate (unboundedPhysicalRate c V 1 basal (fun _ _ => 0))
      (z i).1 (z (i+1))) (K : ℕ) :
    markedWindowReward (normalizedSignedCatalyticReward V) z 0 K = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  obtain ⟨ch,hch,hr⟩ := hp (0+i)
  simp only [hch,Sum.elim_inr]
  rcases ch with (f|q)|(b|⟨r,x,d⟩)
  · rfl
  · rfl
  · rfl
  · rw [disabled_catalytic_rate_zero] at hr
    exact (lt_irrefl (0 : ℝ) hr).elim

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- The same collective success event is impossible in the catalyst-disabled
control, with unchanged basal chemistry and food-only nonfood initialization. -/
theorem catalyst_disabled_collective_zero (hn : 2 ≤ n) (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (N : Molecule n → ℕ) (hinit : countNonfoodMass N = 0) (r : Reaction n) :
    physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal (fun _ _ => 0) N
      {z | finiteMarkedSuccess V r z} = 0 := by
  have hi := jumpTrajectory_initial_population N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal (fun _ _ => 0))
    (unboundedPhysicalRate_nonneg c V 1 basal (fun _ _ => 0))
    (unbounded_total_pos hn c V 1 hV (by norm_num) basal (fun _ _ => 0))
  have hc := jumpTrajectory_consistent N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal (fun _ _ => 0))
    (unboundedPhysicalRate_nonneg c V 1 basal (fun _ _ => 0))
    (unbounded_total_pos hn c V 1 hV (by norm_num) basal (fun _ _ => 0))
  have hp := jumpTrajectory_positive_rate N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal (fun _ _ => 0))
    (unboundedPhysicalRate_nonneg c V 1 basal (fun _ _ => 0))
    (unbounded_total_pos hn c V 1 hV (by norm_num) basal (fun _ _ => 0))
  have hnone : ∀ᵐ z ∂physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal (fun _ _ => 0) N,
      ¬finiteMarkedSuccess V r z := by
    filter_upwards [hi,hc,hp] with z hzi hzc hzp hz
    obtain ⟨L,_,_,hout⟩ := marked_success_forces_signed_catalytic c V hV basal (fun _ _ => 0) r z
      (by simpa only [hzi] using hinit) hzc hzp hz
    rw [disabled_signed_reward_prefix_zero c V basal z hzp L] at hout
    norm_num at hout
  simpa only [not_not] using ae_iff.mp hnone

end
end RandomViability
