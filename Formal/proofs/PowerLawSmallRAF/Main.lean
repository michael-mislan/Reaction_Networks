import proofs.PowerLawSmallRAF.SourceCriticalEndpoint
import proofs.PowerLawSmallRAF.SourceRAFSurvivalUpper
import proofs.PowerLawSmallRAF.SourceSubexponentialRAF
import proofs.PowerLawSmallRAF.SourceSplitCoreRAFProbability

namespace PowerLawSmallRAF
open Classical Filter Topology MeasureTheory HordijkSteelThreshold RAF.Polymer RAF.Concrete
noncomputable section

theorem sourceBoundedRevRAFProbability_le_full (a : ℝ) (ha : 1<a) (n m : Nat) :
    sourceBoundedRevRAFProbability a n m ≤ sourceFullRAFProbability a n := by
  unfold sourceFullRAFProbability sourceBoundedRevRAFProbability
  apply Finset.sum_le_sum
  intro config _
  by_cases h : ∃ S : Finset (Reaction n), S.card ≤ m ∧
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) S
  · obtain ⟨S,hS,hraf⟩ := h
    have hm : ∃ S : Finset (Reaction n), S.card ≤ m ∧
        IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) S := ⟨S,hS,hraf⟩
    have hf : ∃ S : Finset (Reaction n), S.card ≤ Fintype.card (Reaction n) ∧
        IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) S :=
      ⟨S,Finset.card_le_univ S,hraf⟩
    rw [if_pos hm,if_pos hf]
  · rw [if_neg h]
    split_ifs
    · exact sourcePowerLawConfigWeight_nonneg a n ha config
    · exact le_rfl

theorem sourceCriticalSurvival_pos : 0 < (staticSurvival sourceCriticalOpenness).toReal :=
  ENNReal.toReal_pos (ne_of_gt (staticSurvival_pos sourceCriticalOpenness
    (by linarith [sourceCriticalOpenness_gt_half]))) (measure_ne_top _ _)

theorem source_RAF_probability_tendsto :
    Tendsto (fun n : Nat => sourceFullRAFProbability (2-2/(n : ℝ)) n) atTop
      (𝓝 (staticSurvival sourceCriticalOpenness).toReal) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    obtain ⟨N,_,hp⟩ := source_subexponential_RAF_endpoint_lower r hr
    filter_upwards [hp,sourceExactCriticalExponent_tendsto.eventually
      (Ioi_mem_nhds one_lt_two)] with n hn ha
    exact hn.trans_le (sourceBoundedRevRAFProbability_le_full _ ha n _)
  · exact fun r hr => source_RAF_survival_upper r hr

theorem source_subexponential_cutoff_probability_tendsto (b : ℝ) (hb : 0<b) :
    Tendsto (fun n : Nat => sourceBoundedRevRAFProbability (2-2/(n : ℝ)) n
      ⌊(2 : ℝ)^(b*(n : ℝ))⌋₊) atTop
      (𝓝 (staticSurvival sourceCriticalOpenness).toReal) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    obtain ⟨N,hsize,hprob⟩ := source_subexponential_RAF_endpoint_lower r hr
    filter_upwards [hsize b hb,hprob,sourceExactCriticalExponent_tendsto.eventually
      (Ioi_mem_nhds one_lt_two)] with n hs hp ha
    exact hp.trans_le (sourceBoundedRevRAFProbability_mono_size _ n _ _ ha (Nat.le_floor hs.le))
  · intro r hr
    filter_upwards [source_RAF_survival_upper r hr,sourceExactCriticalExponent_tendsto.eventually
      (Ioi_mem_nhds one_lt_two)] with n hn ha
    exact (sourceBoundedRevRAFProbability_le_full _ ha n _).trans_lt hn

theorem source_RAF_probability_eventually_pos :
    ∀ᶠ n : Nat in atTop, 0 < sourceFullRAFProbability (2-2/(n : ℝ)) n :=
  source_RAF_probability_tendsto.eventually (Ioi_mem_nhds sourceCriticalSurvival_pos)

/-- In the literal capped-Zipf reversible binary-polymer source, at a_n=2-2/n,
the minimum nonempty RAF is subexponential in conditional probability:
for every positive exponential cutoff, conditional small-RAF probability tends
to one. Food horizon is two and channels retain their split-position identity. -/
theorem source_conditional_minimum_subexponential (b : ℝ) (hb : 0<b) :
    Tendsto (fun n : Nat => sourceConditionalBoundedRevRAFProbability
      (2-2/(n : ℝ)) n ⌊(2 : ℝ)^(b*(n : ℝ))⌋₊) atTop (𝓝 1) := by
  have ht := (source_subexponential_cutoff_probability_tendsto b hb).div
    source_RAF_probability_tendsto (ne_of_gt sourceCriticalSurvival_pos)
  simpa only [sourceConditionalBoundedRevRAFProbability,
    div_self (ne_of_gt sourceCriticalSurvival_pos)] using ht

end
end PowerLawSmallRAF
