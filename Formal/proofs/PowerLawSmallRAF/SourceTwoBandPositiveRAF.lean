import proofs.PowerLawSmallRAF.SourceTwoBandGoodMass

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section

/-- A genuine source-law bounded RAF has probability uniformly bounded
away from zero. The separate size asymptotic and conditional classification
are not premises or conclusions of this statement. -/
theorem sourceTwoBand_boundedRAF_eventually_positive :
    ∀ᶠ n : Nat in atTop, sourceNucleusProbabilityFloor/4 ≤
      sourceBoundedRevRAFProbability (2-2/(n : ℝ)) n (sourceTwoBandConstructionBudget n) := by
  let E := fun n => sourceHighTargetInvalidMass n +
    sourceActualBoundedHighTargetFailureMass n (sourceNucleusBase n) +
    sourceActualBoundedLowTargetFailureMass n (sourceNucleusBase n) + sourceActiveRowErrorEnvelope n
  have he : Tendsto E atTop (𝓝 0) := by
    have hh := ((sourceHighTargetInvalidMass_tendsto_zero.add
      (sourceActualBoundedHighTargetFailureMass_tendsto_zero sourceNucleusBase)).add
      (sourceActualBoundedLowTargetFailureMass_tendsto_zero sourceNucleusBase)).add
      sourceActiveRowErrorEnvelope_tendsto_zero
    simpa only [add_zero] using hh
  have hevent : ∀ᶠ n in atTop, E n < sourceNucleusProbabilityFloor/4 :=
    he.eventually (gt_mem_nhds (div_pos sourceNucleusProbabilityFloor_pos (by norm_num)))
  filter_upwards [hevent,sourceLowRows_actualNucleus_eventually_lower,
    targetUnion_eventual_conditions,eventually_ge_atTop 4] with n hE hN hc hn
  have hLn : targetNucleusLength n ≤ n := hc.2.2.2.1.trans (Nat.div_le_self _ _)
  have hL : 3 ≤ targetNucleusLength n := by have hh := hc.2.2.1; omega
  have hgood := sourceLowNucleusMass_le_good_add_errors n hn
  have haux := sourceTwoBandGoodMass_le_auxiliary n hn hL hLn
  have hsource := sourceTwoBandAuxiliaryRAFMass_le_source n (sourceTwoBandConstructionBudget n) hn
  dsimp only [E] at hE
  linarith

end
end PowerLawSmallRAF
