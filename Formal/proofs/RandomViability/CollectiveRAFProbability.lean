import proofs.RandomViability.CollectiveJointProbability
import proofs.RandomViability.ProductiveRAF
import proofs.RandomViability.ProductiveOperationProbability

namespace RandomViability
open Classical Filter Topology MeasureTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 150000

local instance collectiveRAFChannelSpace (n : ℕ) : MeasurableSpace (PhysicalCountChannel n) := ⊤
local instance collectiveRAFChannelSingleton (n : ℕ) : MeasurableSingletonClass (PhysicalCountChannel n) := ⟨fun _ => trivial⟩

/-- Actual source/mark/clock probability of collective operation with the
selected reaction a genuine RAF. Output remains a collective-host observable. -/
def fullyAveragedCollectiveRAFProbability {n : ℕ} (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V) (a : ℝ) : ℝ :=
  uniformFiniteAverage (fun u : KineticMarkConfig n => sourceAverage a n (fun c =>
    if IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig c) {productiveReaction hn} then
      (physicalTrajectoryLaw (by omega : 2 ≤ n) c (V : NNReal) 1
        (by exact_mod_cast hV) (by norm_num) (kineticBasal u) (kineticCatalytic u) (foodOnlyCounts n V)
        {z | finiteMarkedSuccess (V : NNReal) (productiveReaction hn) z}).toReal else 0))

theorem fully_averaged_collective_raf_lower {n : ℕ} (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ)) (a : ℝ) (ha : 1 < a) :
    (sourceEmptyRowMass a n ^ 6*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1)*
      (1-24*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ)))) ≤
      fullyAveragedCollectiveRAFProbability hn V hV a := by
  have hcard : (0 : ℝ) < Fintype.card (KineticMarkConfig n) := by exact_mod_cast Fintype.card_pos
  unfold fullyAveragedCollectiveRAFProbability uniformFiniteAverage
  rw [le_div_iff₀ hcard]
  calc
    _ = ∑ _u : KineticMarkConfig n,
        (sourceEmptyRowMass a n ^ 6*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1)*
          (1-24*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ)))) := by simp [mul_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro u _
      apply sourceAverage_food_silent_seed_lower hn a ha (reactionProduct (productiveReaction hn))
        (productive_reaction_food hn).2.2 (productiveReaction hn)
      · intro c
        split_ifs
        · exact ENNReal.toReal_nonneg
        · exact le_rfl
      · intro c hseed
        rw [if_pos (productive_singleton_isRAF hn c hseed.2)]
        exact concrete_collective_success_lower hn V hV hscale c (kineticBasal u) (kineticCatalytic u)
          (kinetic_basal_bounds u) (kinetic_catalytic_bounds u) hseed

theorem fully_averaged_collective_raf_le {n : ℕ} (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (a : ℝ) (ha : 1 < a) :
    fullyAveragedCollectiveRAFProbability hn V hV a ≤ fullyAveragedCollectiveProbability hn V hV a := by
  unfold fullyAveragedCollectiveRAFProbability fullyAveragedCollectiveProbability uniformFiniteAverage
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro u _
  apply sourceAverage_mono a ha
  intro c
  split_ifs
  · exact le_rfl
  · exact ENNReal.toReal_nonneg

def collectiveRAFJointProbability (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) (n : ℕ) : ℝ :=
  if hn : 4 ≤ n then fullyAveragedCollectiveRAFProbability hn (volume n)
    ((collective_minimal_volume_pos n).trans_le (hvolume n)) (2-2/(n : ℝ)) else 1

theorem collective_raf_joint_probability_bounds (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) (n : ℕ) (hn : 4 ≤ n) :
    sourceEmptyRowMass (2-2/(n : ℝ)) n ^ 6*productiveSourceIncidence n*
      (1-24*Real.exp (-(markedNoiseRate*(volume n : ℝ)/(n : ℝ)))) ≤
        collectiveRAFJointProbability volume hvolume n ∧
    collectiveRAFJointProbability volume hvolume n ≤
      collectiveSourceUpperConstant*productiveSourceIncidence n+
        2*Real.exp (-(markedNoiseRate*(volume n : ℝ)/(n : ℝ))) := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 1 < 2-2/(n : ℝ) := by
    have hd : 2/(n : ℝ) ≤ 1/2 := (div_le_iff₀ (by linarith)).2 (by linarith)
    linarith
  have hR : 2 ≤ sourceReactionCount n := by unfold sourceReactionCount; omega
  have hv : (10^60 : ℝ)*((n : ℝ)+1)^2 ≤ (volume n : ℝ) := by exact_mod_cast hvolume n
  have hs := (collective_quadratic_volume_scale (n : ℝ) (volume n) (by linarith only [hnR]) hv).1
  have hl := fully_averaged_collective_raf_lower hn (volume n)
    ((collective_minimal_volume_pos n).trans_le (hvolume n)) hs (2-2/(n : ℝ)) ha
  rw [powerLawMoleculeGatewayHit_one_eq_mean_div _ _ ha hR] at hl
  constructor
  · simpa only [collectiveRAFJointProbability,dif_pos hn,productiveSourceIncidence,productiveSourceMean] using hl
  · have hu := fully_averaged_collective_raf_le hn (volume n)
      ((collective_minimal_volume_pos n).trans_le (hvolume n)) (2-2/(n : ℝ)) ha
    have hu' : collectiveRAFJointProbability volume hvolume n ≤ collectiveJointProbability volume hvolume n := by
      simpa only [collectiveRAFJointProbability,collectiveJointProbability,dif_pos hn] using hu
    exact hu'.trans (collective_joint_probability_bounds volume hvolume n hn).2

/-- Uniform positive constant-factor comparison with the exact source incidence.
It holds for every volume sequence above the same explicit quadratic envelope. -/
theorem collective_raf_joint_probability_theta (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    ∃ L U : ℝ,0 < L ∧ 0 < U ∧ ∀ᶠ n in atTop,
      L*productiveSourceIncidence n ≤ collectiveRAFJointProbability volume hvolume n ∧
      collectiveRAFJointProbability volume hvolume n ≤ U*productiveSourceIncidence n := by
  let L : ℝ := (1/(Real.pi^2/6))^6/2
  let U : ℝ := collectiveSourceUpperConstant+1
  have hq : 0 < (1/(Real.pi^2/6) : ℝ)^6 := by positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hU : 0 < U := by
    have hc : 0 ≤ collectiveSourceUpperConstant := by unfold collectiveSourceUpperConstant; positivity
    dsimp [U]
    linarith only [hc]
  have hl := (collective_empty_row_limit.pow 6).mul
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      ((collective_noise_tendsto_zero volume hvolume).const_mul 24))
  simp only [mul_zero,sub_zero,mul_one] at hl
  have hle := hl.eventually (eventually_gt_nhds (show L < (1/(Real.pi^2/6) : ℝ)^6 by dsimp [L]; linarith only [hq]))
  have hu := (collective_noise_relative_tendsto_zero volume hvolume).const_mul 2
  simp only [mul_zero] at hu
  have hue := hu.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  refine ⟨L,U,hL,hU,?_⟩
  filter_upwards [hle,hue,source_incidence_ge_exp_eventually,eventually_ge_atTop 4] with n hl hu hp hn
  have hb := collective_raf_joint_probability_bounds volume hvolume n hn
  constructor
  · have hh := mul_le_mul_of_nonneg_right hl.le hp.1.le
    nlinarith only [hh,hb.1]
  · have hh := (div_le_iff₀ hp.1).1 (show
        (2*Real.exp (-(markedNoiseRate*(volume n : ℝ)/(n : ℝ))))/productiveSourceIncidence n ≤ 1 by
      simpa only [mul_div_assoc] using hu.le)
    dsimp only [U]
    nlinarith only [hh,hb.2]

theorem collective_raf_joint_logarithmic_limit (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    Tendsto (fun n => Real.log (collectiveRAFJointProbability volume hvolume n)/(n : ℝ))
      atTop (𝓝 (-Real.log 2)) := by
  obtain ⟨L,U,hL,hU,hbounds⟩ := collective_raf_joint_probability_theta volume hvolume
  have hl := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log L) atTop (𝓝 (Real.log L))).div_atTop
    (tendsto_natCast_atTop_atTop (R := ℝ))).add productive_source_incidence_log_rate
  have hu := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log U) atTop (𝓝 (Real.log U))).div_atTop
    (tendsto_natCast_atTop_atTop (R := ℝ))).add productive_source_incidence_log_rate
  simp only [zero_add] at hl hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [hbounds,source_incidence_ge_exp_eventually] with n hb hp
    have hh := Real.log_le_log (mul_pos hL hp.1) hb.1
    rw [Real.log_mul hL.ne' hp.1.ne'] at hh
    simpa only [add_div] using div_le_div_of_nonneg_right hh (show (0 : ℝ) ≤ n by positivity)
  · filter_upwards [hbounds,source_incidence_ge_exp_eventually] with n hb hp
    have hpos := (mul_pos hL hp.1).trans_le hb.1
    have hh := Real.log_le_log hpos hb.2
    rw [Real.log_mul hU.ne' hp.1.ne'] at hh
    simpa only [add_div] using div_le_div_of_nonneg_right hh (show (0 : ℝ) ≤ n by positivity)

end
end RandomViability
