import proofs.RandomViability.CollectiveSourceUpper
import proofs.RandomViability.MarkedSignedCurrent

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 150000

/-- Observable mass localization and nonfood export only. No RAF, product
floor, or catalytic/basal label condition is part of this event. -/
def physicalOutputEvent {n : ℕ} (V : NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  (∀ k,prefixElapsed k (Preorder.frestrictLe k z) ≤ 100 → (countMass (z k).1 : ℝ) ≤ 11*V) ∧
  ∃ J K,prefixElapsed J (Preorder.frestrictLe J z) ≤ 1 ∧
    1 < prefixElapsed (J+1) (Preorder.frestrictLe (J+1) z) ∧
    prefixElapsed (J+K) (Preorder.frestrictLe (J+K) z) ≤ 100 ∧
    100 < prefixElapsed (J+K+1) (Preorder.frestrictLe (J+K+1) z) ∧
    (1/10 : ℝ) < markedWindowReward (fun _ => exportReward V) z J K

theorem finite_success_implies_output {n : ℕ} (V : NNReal) (r : Reaction n)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hz : finiteMarkedSuccess V r z) : physicalOutputEvent V z := by
  obtain ⟨J,K,hj,hj',hk,hk',he,_⟩ := hz.2.2
  exact ⟨hz.1,J,K,hj,hj',hk,hk',he⟩

theorem localized_reward_budget {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (reward : (Molecule n → ℕ) → PhysicalCountChannel n → ℝ) (b eta : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (L : ℕ)
    (hmass : ∀ i,prefixElapsed i (Preorder.frestrictLe i z) ≤ 100 → (countMass (z i).1 : ℝ) ≤ 11*V)
    (hh : ∀ i,0 ≤ (z (i+1)).2.2)
    (hl : prefixElapsed L (Preorder.frestrictLe L z) ≤ 100)
    (hl' : 100 < prefixElapsed (L+1) (Preorder.frestrictLe (L+1) z))
    (hbound : ∀ N,(countMass N : ℝ) ≤ 11*V → markedRewardDrift c V basal cat reward N ≤ b)
    (hnoise : markedRewardNoiseBound c V basal cat reward 101 eta z) :
    markedWindowReward reward z 0 L ≤ b*100+eta := by
  have hm := prefix_elapsed_monotone z hh
  have hM : ∀ i ≤ L,(countMass (z i).1 : ℝ) ≤ 11*V := fun i hi => hmass i ((hm hi).trans hl)
  have ha : ∀ i ≤ L,¬censoredNonfoodStop V 101 (massExitStop V) i (Preorder.frestrictLe i z) := by
    intro i hi
    exact mass_exit_active_before_first_exit V 101 z (by omega : i < L+1)
      (fun j hj => hM j (by omega)) ((hm hi).trans_lt (hl.trans_lt (by norm_num)))
  have ht : ∀ i < L,(z (i+1)).2.2 ≤ 101-prefixElapsed i (Preorder.frestrictLe i z) := by
    intro i hi
    have he := (hm (show i+1 ≤ L by omega)).trans hl
    dsimp only at he
    rw [prefixElapsed_restrict_succ] at he
    linarith only [he]
  have hcap : 100-prefixElapsed L (Preorder.frestrictLe L z) ≤
      min (z (L+1)).2.2 (101-prefixElapsed L (Preorder.frestrictLe L z)) := by
    apply le_min
    · rw [prefixElapsed_restrict_succ] at hl'
      linarith only [hl']
    · linarith
  exact marked_reward_budget c V basal cat reward 101 100 eta b z L ha ht hh
    (sub_nonneg.mpr hl) hcap (fun i hi => hbound _ (hM i hi)) hnoise

theorem output_requires_noise {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (hgood : ¬ShortIncidence collectiveUpperCutoff c) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ)) (hcat : ∀ r q,(cat r q : ℝ) ≤ 16)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hinit : countNonfoodMass (z 0).1 = 0)
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hp : ∀ i,jumpPositiveRate (unboundedPhysicalRate c V 1 basal cat) (z i).1 (z (i+1)))
    (hh : ∀ i,0 ≤ (z (i+1)).2.2) (hz : physicalOutputEvent V z) :
    ¬markedRewardNoiseBound c V basal cat (positiveBasalReward V) 101 (1/100) z ∨
    ¬markedRewardNoiseBound c V basal cat (normalizedPositiveCatalyticReward V) 101 (1/40) z := by
  by_contra h
  push Not at h
  obtain ⟨J,K,_,_,hl,hl',he⟩ := hz.2
  have hB := localized_reward_budget c V basal cat (positiveBasalReward V) (1936*(1/500000000))
    (1/100) z (J+K) hz.1 hh hl hl'
    (fun N hM => positive_basal_reward_drift c V hV basal cat N _ (by norm_num) hb hM) h.1
  have hC := localized_reward_budget c V basal cat (normalizedPositiveCatalyticReward V) (1/4000)
    (1/40) z (J+K) hz.1 hh hl hl'
    (fun N hM => positive_catalytic_drift_small c hgood V hV basal cat N hM hcat) h.2
  have hbal := marked_nonfood_prefix_balance c V hV basal cat z hc hp (J+K)
  rw [hinit,zero_div,zero_add,marked_window_reward_prefix_shift (fun _ => exportReward V) z J K] at hbal
  have hpre : 0 ≤ markedWindowReward (fun _ => exportReward V) z 0 J := by
    apply Finset.sum_nonneg
    intro i _
    cases (z (0+i+1)).2.1 with
    | inl u => exact le_rfl
    | inr ch => exact (export_reward_bounds V hV ch).1
  have hlast := div_nonneg (count_nonfood_nonneg (z (J+K)).1) hV.le
  linarith only [hB,hC,hbal,hpre,hlast,he]

theorem disabled_output_requires_basal_noise {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hinit : countNonfoodMass (z 0).1 = 0)
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hp : ∀ i,jumpPositiveRate (unboundedPhysicalRate c V 1 basal (fun _ _ => 0)) (z i).1 (z (i+1)))
    (hh : ∀ i,0 ≤ (z (i+1)).2.2) (hz : physicalOutputEvent V z) :
    ¬markedRewardNoiseBound c V basal (fun _ _ => 0) (positiveBasalReward V) 101 (1/100) z := by
  intro h
  obtain ⟨J,K,_,_,hl,hl',he⟩ := hz.2
  have hB := localized_reward_budget c V basal (fun _ _ => 0) (positiveBasalReward V) (1936*(1/500000000))
    (1/100) z (J+K) hz.1 hh hl hl'
    (fun N hM => positive_basal_reward_drift c V hV basal (fun _ _ => 0) N _ (by norm_num) hb hM) h
  have hbal := marked_nonfood_signed_prefix_balance c V hV basal (fun _ _ => 0) z hc hp (J+K)
  rw [hinit,zero_div,zero_add,disabled_signed_reward_prefix_zero c V basal z hp (J+K),add_zero,
    marked_window_reward_prefix_shift (fun _ => exportReward V) z J K] at hbal
  have hpre : 0 ≤ markedWindowReward (fun _ => exportReward V) z 0 J := by
    apply Finset.sum_nonneg
    intro i _
    cases (z (0+i+1)).2.1 with
    | inl u => exact le_rfl
    | inr ch => exact (export_reward_bounds V hV ch).1
  have hlast := div_nonneg (count_nonfood_nonneg (z (J+K)).1) hV.le
  linarith only [hB,hbal,hpre,hlast,he]

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)] [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_output_measurable (V : NNReal) : MeasurableSet {z | physicalOutputEvent (n := n) V z} := by
  have hclock (i : ℕ) : Measurable (fun z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) =>
      prefixElapsed i (Preorder.frestrictLe i z)) :=
    (prefixElapsed_measurable i).comp (Preorder.measurable_frestrictLe i)
  have hmass (i : ℕ) : Measurable (fun z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) =>
      (countMass (z i).1 : ℝ)) := (measurable_of_countable (fun N : Molecule n → ℕ => (countMass N : ℝ))).comp
        (measurable_pi_apply i).fst
  have he := marked_window_reward_measurable (fun _ => exportReward (n := n) V)
  unfold physicalOutputEvent
  measurability

end
end RandomViability
