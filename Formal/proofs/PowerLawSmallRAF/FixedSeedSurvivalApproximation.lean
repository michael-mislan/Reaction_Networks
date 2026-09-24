import proofs.PowerLawSmallRAF.FixedSeedGeometricTail
import proofs.PowerLawSmallRAF.FixedSeedNucleusGrowth
import proofs.HordijkSteelThreshold.InfiniteClosureDichotomy
import proofs.HordijkSteelThreshold.StaticSurvivalContinuity

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete Filter Topology MeasureTheory unitInterval HordijkSteelThreshold
open scoped ENNReal
noncomputable section

/-- First choose a fixed seed to make the uniform extension error small;
then choose a finite witness cap capturing any prescribed mass below survival.
No quantitative growth rate of the infinite closure is required. -/
theorem fixed_seed_captures_survival_with_small_extension_error
    (a : I) (ha : 1/2 < (a : ℝ)) (ε : ℝ) (hε : 0<ε)
    (c : ENNReal) (hc : c < staticSurvival a) :
    ∃ m N : Nat, 2 ≤ m ∧ m ≤ N ∧
      2*(2*(1-(a : ℝ)))^m/(1-2*(1-(a : ℝ))) < ε ∧
      c < staticReactionMeasure N a {ω | ∀ w ∈ actualBinaryWords m,
        ∃ x ∈ temporaryReactionClosure 2 (staticOpenReactions ω), moleculeWord x = w} := by
  have htail := fixedSeedTail_tendsto_zero (1-(a : ℝ)) (by linarith [a.property.2]) (by linarith)
  obtain ⟨m,hmerror,hm⟩ := ((htail.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop 2)).exists
  have hseed := staticSurvival_le_same_parameter_seed a (by linarith) (actualBinaryWords m)
    (fun w hw => List.length_pos_iff.mpr ((mem_actualBinaryWords w m).mp hw).1)
  have hfinite := (finite_static_seed_probability_tendsto 2 a (actualBinaryWords m)).eventually_const_lt
    (hc.trans_le hseed)
  obtain ⟨N,hN,hNm⟩ := (hfinite.and (eventually_ge_atTop m)).exists
  exact ⟨m,N,hm,hNm,hmerror,hN⟩

end
end PowerLawSmallRAF
