import proofs.RandomViability.MarkedCatalyticInput
import proofs.RandomViability.MarkedFiniteEvent
import proofs.RandomViability.JumpPositiveRate

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 150000

theorem count_nonfood_nonneg {n : ℕ} (N : Molecule n → ℕ) : 0 ≤ countNonfoodMass N := by
  apply Finset.sum_nonneg
  intro q _
  dsimp only
  unfold foodMassWeight
  split_ifs <;> simp only [sub_self,zero_mul,sub_zero] <;> positivity

theorem enabled_outflow_nonfood_change {n : ℕ} (N : Molecule n → ℕ) (q : Molecule n)
    (he : ∀ z,physicalChannelInput (.inl (.inr q)) z ≤ N z) :
    countNonfoodMass (unboundedPhysicalNext N (.inl (.inr q)))-countNonfoodMass N =
      -((molLength q : ℝ)-foodMassWeight q) := by
  rw [unboundedPhysicalNext,if_pos he]
  unfold countNonfoodMass
  rw [weightedCountMass_change _ _ _ _ he]
  simp [weightedCountMass,physicalChannelInput,physicalChannelOutput,singleCount,mul_ite]

theorem enabled_nonfood_reward_budget {n : ℕ} (V : NNReal) (hV : 0 < (V : ℝ))
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n)
    (he : ∀ q,physicalChannelInput ch q ≤ N q) :
    (countNonfoodMass (unboundedPhysicalNext N ch)-countNonfoodMass N)/V+exportReward V ch ≤
      positiveBasalReward V N ch+normalizedPositiveCatalyticReward V N ch := by
  rcases ch with (f|q)|(b|d)
  · simp [unbounded_feed_nonfood_jump,exportReward,positiveBasalReward,normalizedPositiveCatalyticReward]
  · rw [enabled_outflow_nonfood_change N q he]
    simp only [exportReward,positiveBasalReward,normalizedPositiveCatalyticReward]
    ring_nf
    exact le_rfl
  · simp only [exportReward,positiveBasalReward,normalizedPositiveCatalyticReward,add_zero]
    exact div_le_div_of_nonneg_right (le_max_right _ _) hV.le
  · simp only [exportReward,positiveBasalReward,normalizedPositiveCatalyticReward,add_zero,zero_add]
    exact div_le_div_of_nonneg_right (le_max_right _ _) hV.le

theorem marked_window_reward_succ {n : ℕ}
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (J K : ℕ) :
    markedWindowReward reward z J (K+1) = markedWindowReward reward z J K+
      (z (J+K+1)).2.1.elim (fun _ => 0) (reward (z (J+K)).1) := by
  unfold markedWindowReward
  rw [Fin.sum_univ_castSucc]
  rfl

theorem marked_window_reward_prefix_shift {n : ℕ}
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (J K : ℕ) :
    markedWindowReward reward z 0 (J+K) =
      markedWindowReward reward z 0 J+markedWindowReward reward z J K := by
  induction K with
  | zero => simp [markedWindowReward]
  | succ K ih =>
    rw [Nat.add_succ,marked_window_reward_succ,ih,marked_window_reward_succ]
    simp only [Nat.zero_add]
    ring

theorem marked_nonfood_prefix_balance {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hp : ∀ i,jumpPositiveRate (unboundedPhysicalRate c V 1 basal cat) (z i).1 (z (i+1))) (K : ℕ) :
    countNonfoodMass (z K).1/V+markedWindowReward (fun _ => exportReward V) z 0 K ≤
      countNonfoodMass (z 0).1/V+markedWindowReward (positiveBasalReward V) z 0 K+
        markedWindowReward (normalizedPositiveCatalyticReward V) z 0 K := by
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
    have hstep := enabled_nonfood_reward_budget V hV (z K).1 ch hen
    rw [← hn] at hstep
    simp only [marked_window_reward_succ,Nat.zero_add,hch,Sum.elim_inr]
    rw [sub_div] at hstep
    linarith only [ih,hstep]

theorem marked_success_forces_catalytic {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (r : Reaction n)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hinit : countNonfoodMass (z 0).1 = 0)
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hp : ∀ i,jumpPositiveRate (unboundedPhysicalRate c V 1 basal cat) (z i).1 (z (i+1)))
    (hz : finiteMarkedSuccess V r z) :
    ∃ L,prefixElapsed L (Preorder.frestrictLe L z) ≤ 100 ∧
      100 < prefixElapsed (L+1) (Preorder.frestrictLe (L+1) z) ∧
      (3/40 : ℝ) < markedWindowReward (normalizedPositiveCatalyticReward V) z 0 L := by
  obtain ⟨J,K,_,_,hl,hl',he,hb⟩ := hz.2.2
  have hbalance := marked_nonfood_prefix_balance c V hV basal cat z hc hp (J+K)
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

end
end RandomViability
