import proofs.RandomViability.LocalMultiplicity
import proofs.RandomViability.SingletonDominanceNoise
import proofs.RandomViability.OutputJointLimit

set_option Elab.async false
namespace RandomViability
open Classical Filter Topology MeasureTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 80000
local instance singletonChannelSpace (n : ℕ) : MeasurableSpace (PhysicalCountChannel n) := ⊤
local instance singletonChannelSingleton (n : ℕ) : MeasurableSingletonClass (PhysicalCountChannel n) := ⟨fun _ => trivial⟩

def noProductiveSingleton {n : ℕ} (c : SourceMoleculeFibreConfig n) : Prop :=
  ∀ z r,r ∈ c z → ¬ProductiveSingletonIncidence r z

theorem averaged_output_nonneg {n : ℕ} (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (a : ℝ) (ha : 1 < a) (A : SourceMoleculeFibreConfig n → Prop) :
    0 ≤ averagedOutputProbability hn V hV a A := by
  unfold averagedOutputProbability uniformFiniteAverage
  simp only [if_true]
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro u _
  unfold sourceAverage
  apply Finset.sum_nonneg
  intro c _
  apply mul_nonneg (sourcePowerLawConfigWeight_nonneg a n ha c)
  dsimp only
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

theorem averaged_output_without_singleton_upper {n : ℕ} (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ)) (hsmall : (n : ℝ)/(V : ℝ) ≤ 1/200000)
    (a : ℝ) (ha : 1 < a) :
    averagedOutputProbability hn V hV a noProductiveSingleton ≤
      eventMass a n (fun c => ¬AtMostOneLocalIncidence singleIncidenceCutoff c)+
        localOutputNoiseUpper n (V : NNReal) := by
  have hcard : (0 : ℝ) < Fintype.card (KineticMarkConfig n) := by exact_mod_cast Fintype.card_pos
  have hnoise : 0 ≤ localOutputNoiseUpper n (V : NNReal) := by unfold localOutputNoiseUpper; positivity
  unfold averagedOutputProbability uniformFiniteAverage
  simp only [if_true]
  rw [div_le_iff₀ hcard]
  calc
    _ ≤ ∑ _u : KineticMarkConfig n,(eventMass a n (fun c => ¬AtMostOneLocalIncidence singleIncidenceCutoff c)+
        localOutputNoiseUpper n (V : NNReal)) := by
      apply Finset.sum_le_sum
      intro u _
      apply sourceAverage_le_bad_add a n ha hn (fun c => ¬AtMostOneLocalIncidence singleIncidenceCutoff c) _ _ hnoise
      · intro c
        split_ifs
        · exact measureReal_le_one
        · norm_num
      · intro c hc
        have hone : AtMostOneLocalIncidence singleIncidenceCutoff c := not_not.mp hc
        split_ifs with hno
        · exact physical_output_upper_at_most_one_local hn c hone hno (V : NNReal)
            (by exact_mod_cast hV) hscale hsmall (kineticBasal u) (kineticCatalytic u)
            (fun r => (kinetic_basal_bounds u r).2) (fun r z => (kinetic_catalytic_bounds u r z).2)
            (foodOnlyCounts n V) (food_only_nonfood_zero n V)
        · exact hnoise
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

/-- T1: under the exact capped-Zipf source and the literal marked reactor,
productive output without a productive food-food singleton is o(p_n). -/
theorem output_without_productive_singleton_relative_tendsto_zero (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    Tendsto (fun n => outputJointProbability volume hvolume (fun _ => noProductiveSingleton) n/
      productiveSourceIncidence n) atTop (𝓝 0) := by
  have hsource : Tendsto (fun n : ℕ => eventMass (2-2/(n : ℝ)) n
      (fun c => ¬AtMostOneLocalIncidence singleIncidenceCutoff c)/productiveSourceIncidence n) atTop (𝓝 0) := by
    simpa only [productiveSourceIncidence,productiveSourceMean] using
      two_local_incidence_mass_div_incidence_tendsto_zero singleIncidenceCutoff
  have hupper := hsource.add (local_output_noise_relative_tendsto_zero volume hvolume)
  simp only [add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_ge_atTop 4,source_incidence_ge_exp_eventually,
      sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n hn hp ha
    unfold outputJointProbability
    rw [dif_pos hn]
    exact div_nonneg (averaged_output_nonneg hn _ _ _ ha _) hp.1.le
  · filter_upwards [eventually_ge_atTop 4,source_incidence_ge_exp_eventually,
      sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n hn hp ha
    have hscale := singleton_volume_scales n (volume n) hn (hvolume n)
    have hh := averaged_output_without_singleton_upper hn (volume n)
      ((collective_minimal_volume_pos n).trans_le (hvolume n)) hscale.1 hscale.2 _ ha
    unfold outputJointProbability
    rw [dif_pos hn]
    simpa only [add_div] using div_le_div_of_nonneg_right hh hp.1.le

end
end RandomViability
