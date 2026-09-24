import proofs.PowerLawSmallRAF.SourceEscapeLimit

namespace PowerLawSmallRAF
open Classical Filter Topology MeasureTheory HordijkSteelThreshold RAF.Polymer RAF.Concrete
noncomputable section

/-- The actual source RAF probability has upper limit at most the iid
survival probability at the exact critical openness. -/
theorem source_RAF_survival_upper (r : ℝ)
    (hr : (staticSurvival sourceCriticalOpenness).toReal < r) :
    ∀ᶠ n : Nat in atTop, sourceFullRAFProbability (2-2/(n : ℝ)) n < r := by
  obtain ⟨s,hs,hsr⟩ := exists_between hr
  have hK := (ENNReal.tendsto_toReal
    (show staticSurvival sourceCriticalOpenness ≠ ⊤ from measure_ne_top _ _)).comp
    (finite_static_escape_probability_tendsto sourceCriticalOpenness)
  obtain ⟨K,hKs⟩ := (hK.eventually (Iio_mem_nhds hs)).exists
  have hn := (sourceEscapeProbability_tendsto K).add
    (sourceExactCriticalBoundedSeedError_tendsto_zero (K+2))
  simp only [add_zero] at hn
  have hnr := hn.eventually (Iio_mem_nhds (hKs.trans hsr))
  filter_upwards [hnr,eventually_ge_atTop 4,
    sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n hh hn4 ha
  exact (sourceFullRAFProbability_le_escape_add_seed _ ha n (K+2) hn4).trans_lt hh

end
end PowerLawSmallRAF
