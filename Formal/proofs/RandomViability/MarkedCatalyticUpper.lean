import proofs.RandomViability.MarkedMassBalance

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 150000

theorem marked_success_forces_catalytic_noise {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (hgood : ¬ShortIncidence collectiveUpperCutoff c) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hcat : ∀ r q,(cat r q : ℝ) ≤ 16) (r : Reaction n)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hinit : countNonfoodMass (z 0).1 = 0)
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hp : ∀ i,jumpPositiveRate (unboundedPhysicalRate c V 1 basal cat) (z i).1 (z (i+1)))
    (hh : ∀ i,0 ≤ (z (i+1)).2.2)
    (hz : finiteMarkedSuccess V r z) :
    ¬markedRewardNoiseBound c V basal cat (normalizedPositiveCatalyticReward V) 101 (1/40) z := by
  intro hnoise
  obtain ⟨L,hl,hl',hout⟩ := marked_success_forces_catalytic c V hV basal cat r z hinit hc hp hz
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
  have hb := marked_reward_budget c V basal cat (normalizedPositiveCatalyticReward V) 101 100 (1/40)
    (1/4000) z L hactive hcomplete hh hb0 hbcap
    (fun i hi => positive_catalytic_drift_small c hgood V hV basal cat (z i).1 (hmass i hi) hcat) hnoise
  linarith only [hb,hout]

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- Fixed-source upper bound outside a fixed short-incidence event. The success
event itself supplies mass localization, so no separate mass-exit error is paid. -/
theorem physical_collective_upper_without_short_incidence (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (hgood : ¬ShortIncidence collectiveUpperCutoff c)
    (V : NNReal) (hV : 0 < (V : ℝ)) (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r q,(cat r q : ℝ) ≤ 16)
    (N : Molecule n → ℕ) (hinit : countNonfoodMass N = 0) (r : Reaction n) :
    (physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | finiteMarkedSuccess V r z}).toReal ≤
      2*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) := by
  let μ := physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
  have hi := jumpTrajectory_initial_population N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hc := jumpTrajectory_consistent N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hp := jumpTrajectory_positive_rate N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hw := jumpTrajectory_wait_nonneg N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hsub : ∀ᵐ z ∂μ,z ∈ {z | finiteMarkedSuccess V r z} →
      z ∈ {z | ¬markedRewardNoiseBound c V basal cat (normalizedPositiveCatalyticReward V) 101 (1/40) z} := by
    filter_upwards [hi,hc,hp,hw] with z hzi hzc hzp hzw
    intro hz
    exact marked_success_forces_catalytic_noise c hgood V hV basal cat hcat r z
      (by simpa only [hzi] using hinit) hzc hzp hzw hz
  have hm := marked_noise_margins (n : ℝ) V (by exact_mod_cast hn) hV hscale
  have ht := physical_marked_reward_noise_failure hn c V hV basal cat N (normalizedPositiveCatalyticReward V)
    (fun N ch => by
      rw [abs_of_nonneg (positive_catalytic_reward_bounds V hV N ch).1]
      exact (positive_catalytic_reward_bounds V hV N ch).2.trans
        (div_le_div_of_nonneg_right (by exact_mod_cast hn) hV.le))
    (fun N hM => positive_catalytic_reward_common_variance (by omega) c V hV basal cat N hM hb hcat)
    markedNoiseDelta 101 (1/40) (by norm_num [markedNoiseDelta]) (by norm_num) hm.2.2.2.2.1
  have he := (marked_noise_exponents (n : ℝ) V (by exact_mod_cast hn) hV).1
  have ht' := (measure_mono_ae hsub).trans (ht.trans
    (mul_le_mul_right (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg he))) 2))
  have hr := ENNReal.toReal_mono (by finiteness) ht'
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal (Real.exp_pos _).le] using hr

end
end RandomViability
