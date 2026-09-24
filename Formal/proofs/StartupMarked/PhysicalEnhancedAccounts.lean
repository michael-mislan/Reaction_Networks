import proofs.StartupMarked.EnhancedAccounts
import proofs.RepeatedFunction.EnsembleBounds

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy Filter
noncomputable section
set_option maxHeartbeats 100000

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- The accounting conclusion holds on the literal law, with path consistency,
positive enabled jumps and the zero initial inventory discharged. -/
theorem physical_enhanced_accounts (hn : 2 ≤ n) (c : SourceMoleculeFibreConfig n)
    (V : ℕ) (hV : 0 < V) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) :
    ∀ᵐ z ∂physicalTrajectoryLaw hn c (V : NNReal) 1 (by exact_mod_cast hV) (by norm_num)
      basal cat (foodOnlyCounts n V), StartupMarked.enhancedMission (V : NNReal) z →
      ∃ L,prefixElapsed L (Preorder.frestrictLe L z) ≤ 199 ∧
        199 < prefixElapsed (L+1) (Preorder.frestrictLe (L+1) z) ∧
        (6/25 : ℝ) < markedWindowReward (signedSynthesisReward (V : NNReal)) z 0 L := by
  let N := foodOnlyCounts n V
  have hv : 0 < ((V : NNReal) : ℝ) := by exact_mod_cast hV
  have hi := jumpTrajectory_initial_population N unboundedPhysicalNext
    (unboundedPhysicalRate c (V : NNReal) 1 basal cat)
    (unboundedPhysicalRate_nonneg c (V : NNReal) 1 basal cat)
    (unbounded_total_pos hn c (V : NNReal) 1 hv (by norm_num) basal cat)
  have hc := jumpTrajectory_consistent N unboundedPhysicalNext
    (unboundedPhysicalRate c (V : NNReal) 1 basal cat)
    (unboundedPhysicalRate_nonneg c (V : NNReal) 1 basal cat)
    (unbounded_total_pos hn c (V : NNReal) 1 hv (by norm_num) basal cat)
  have hp := jumpTrajectory_positive_rate N unboundedPhysicalNext
    (unboundedPhysicalRate c (V : NNReal) 1 basal cat)
    (unboundedPhysicalRate_nonneg c (V : NNReal) 1 basal cat)
    (unbounded_total_pos hn c (V : NNReal) 1 hv (by norm_num) basal cat)
  have hh := jumpTrajectory_wait_nonneg N unboundedPhysicalNext
    (unboundedPhysicalRate c (V : NNReal) 1 basal cat)
    (unboundedPhysicalRate_nonneg c (V : NNReal) 1 basal cat)
    (unbounded_total_pos hn c (V : NNReal) 1 hv (by norm_num) basal cat)
  filter_upwards [hi,hc,hp,hh] with z hzi hzc hzp hzh hz
  exact food_only_enhanced_net_synthesis c (V : NNReal) hv basal cat z
    (by simpa only [hzi] using food_only_nonfood_zero n V) hzc hzp hzh hz

end
end RandomViability
