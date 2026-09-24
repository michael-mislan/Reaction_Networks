import proofs.RandomViability.SingleIncidencePathBalance
import proofs.RandomViability.PhysicalOutputEvent

set_option Elab.async false
namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 70000

theorem output_forces_half_modified_reward {n : ℕ}
    (p : Molecule n) (a : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2)
    (hp : a+3 ≤ (molLength p : ℝ)) (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hinit : countNonfoodMass (z 0).1 = 0)
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hr : ∀ i,jumpPositiveRate (unboundedPhysicalRate c V 1 basal cat) (z i).1 (z (i+1)))
    (hz : physicalOutputEvent V z) :
    ∃ L,prefixElapsed L (Preorder.frestrictLe L z) ≤ 100 ∧
      100 < prefixElapsed (L+1) (Preorder.frestrictLe (L+1) z) ∧
      (3/100 : ℝ) < markedWindowReward (halfModifiedInputReward p a V) z 0 L := by
  have hp' : 2 < molLength p := by
    have hh : (3 : ℝ) ≤ molLength p := by linarith
    exact_mod_cast hh
  obtain ⟨J,K,_,_,hl,hl',he⟩ := hz.2
  have hbalance := marked_modified_prefix_balance p a hp' c V hV basal cat z hc hr (J+K)
  rw [marked_window_reward_prefix_shift (fun _ => modifiedExportReward p a V) z J K] at hbalance
  have hinitP : weightedCountMass (singleIncidenceWeight p a) (z 0).1/V ≤ 0 := by
    rw [singleIncidence_count_eq, hinit]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_nonneg ha (Nat.cast_nonneg ((z 0).1 p))]) hV.le
  have hlast : 0 ≤ weightedCountMass (singleIncidenceWeight p a) (z (J+K)).1/V :=
    div_nonneg ((mul_nonneg (by norm_num : (0 : ℝ) ≤ 3/5) (count_nonfood_nonneg _)).trans
      (singleIncidence_count_lower p a ha2 hp _)) hV.le
  have hpre0 : 0 ≤ markedWindowReward (fun _ => exportReward V) z 0 J := by
    apply Finset.sum_nonneg
    intro i _
    cases hm : (z (0+i+1)).2.1 with
    | inl u => exact le_rfl
    | inr ch => exact (export_reward_bounds V hV ch).1
  have hpre := marked_modified_export_lower p a ha2 hp V hV z 0 J
  have hwin := marked_modified_export_lower p a ha2 hp V hV z J K
  refine ⟨J+K,hl,hl',?_⟩
  linarith only [hbalance,hinitP,hlast,hpre0,hpre,hwin,he]

/-- This isolates the remaining kinetic obligation as an explicit drift bound.
It is not a proof that isolated catalytic hosts satisfy that bound. -/
theorem output_forces_half_modified_noise {n : ℕ}
    (p : Molecule n) (a : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2)
    (hp : a+3 ≤ (molLength p : ℝ)) (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal)
    (hbound : ∀ N,(countMass N : ℝ) ≤ 11*V →
      markedRewardDrift c V basal cat (halfModifiedInputReward p a V) N ≤ 1/200000)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hinit : countNonfoodMass (z 0).1 = 0)
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hr : ∀ i,jumpPositiveRate (unboundedPhysicalRate c V 1 basal cat) (z i).1 (z (i+1)))
    (hh : ∀ i,0 ≤ (z (i+1)).2.2) (hz : physicalOutputEvent V z) :
    ¬markedRewardNoiseBound c V basal cat (halfModifiedInputReward p a V) 101 (1/100) z := by
  intro hnoise
  obtain ⟨L,hl,hl',hout⟩ := output_forces_half_modified_reward p a ha ha2 hp c V hV basal cat z hinit hc hr hz
  have hm := prefix_elapsed_monotone z hh
  have hmass : ∀ i ≤ L,(countMass (z i).1 : ℝ) ≤ 11*V :=
    fun i hi => hz.1 i ((hm hi).trans hl)
  have hactive : ∀ i ≤ L,¬censoredNonfoodStop V 101 (massExitStop V) i (Preorder.frestrictLe i z) := by
    intro i hi
    exact mass_exit_active_before_first_exit V 101 z (by omega : i < L+1)
      (fun j hj => hmass j (by omega)) ((hm hi).trans_lt (hl.trans_lt (by norm_num)))
  have hcomplete : ∀ i < L,(z (i+1)).2.2 ≤ 101-prefixElapsed i (Preorder.frestrictLe i z) := by
    intro i hi
    have he := (hm (show i+1 ≤ L by omega)).trans hl
    dsimp only at he
    rw [prefixElapsed_restrict_succ] at he
    linarith only [he]
  have hb0 : 0 ≤ 100-prefixElapsed L (Preorder.frestrictLe L z) := sub_nonneg.mpr hl
  have hbcap : 100-prefixElapsed L (Preorder.frestrictLe L z) ≤
      min (z (L+1)).2.2 (101-prefixElapsed L (Preorder.frestrictLe L z)) := by
    apply le_min
    · rw [prefixElapsed_restrict_succ] at hl'
      linarith only [hl']
    · linarith
  have hb := marked_reward_budget c V basal cat (halfModifiedInputReward p a V) 101 100 (1/100)
    (1/200000) z L hactive hcomplete hh hb0 hbcap
    (fun i hi => hbound (z i).1 (hmass i hi)) hnoise
  linarith only [hb,hout]

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- Literal reactor-law upper bound conditional only on the displayed uniform
drift estimate. Proving that estimate from local isolation is still required. -/
theorem physical_mixed_exclusion_of_drift (hn : 4 ≤ n)
    (p : Molecule n) (a : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2)
    (hp : a+3 ≤ (molLength p : ℝ)) (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (hscale : (n : ℝ)/V ≤ 1/200)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hbound : ∀ N,(countMass N : ℝ) ≤ 11*V →
      markedRewardDrift c V basal cat (halfModifiedInputReward p a V) N ≤ 1/200000)
    (N : Molecule n → ℕ) (hinit : countNonfoodMass N = 0) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | physicalOutputEvent V z} ≤
      2*ENNReal.ofReal (Real.exp (-((1/200 : ℝ)^2*(V : ℝ)/(4*(n : ℝ)*(96011*101+1/200))))) := by
  let μ := physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
  have hi := jumpTrajectory_initial_population N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hc := jumpTrajectory_consistent N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hr := jumpTrajectory_positive_rate N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hw := jumpTrajectory_wait_nonneg N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hsub : ∀ᵐ z ∂μ,z ∈ {z | physicalOutputEvent V z} →
      z ∈ {z | ¬markedRewardNoiseBound c V basal cat (halfModifiedInputReward p a V) 101 (1/100) z} := by
    filter_upwards [hi,hc,hr,hw] with z hzi hzc hzr hzw
    intro hz
    exact output_forces_half_modified_noise p a ha ha2 hp c V hV basal cat hbound z
      (by simpa only [hzi] using hinit) hzc hzr hzw hz
  apply (measure_mono_ae hsub).trans
  exact physical_half_modified_reward_noise_failure hn p a ha ha2 c V hV basal cat hb hcat N
    (1/200) 101 (1/100) (by norm_num) (by norm_num) (by linarith only [hscale])

end
end RandomViability
