import proofs.RandomViability.MarkedSignedCurrent
import proofs.RandomViability.PhysicalTimeCoverage

namespace RandomViability
open Classical Filter MeasureTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- The measurable finite event gives residence at every physical time,
and a strictly positive signed catalytic current including reverse firings.
The current is over the whole history through time100, so no initial stock
is silently discarded in a later-window balance. -/
theorem physical_collective_success_meaning (hn : 2 ≤ n) (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ)
    (hinit : countNonfoodMass N = 0) (r : Reaction n) :
    ∀ᵐ z ∂physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N,
      finiteMarkedSuccess V r z →
      (∀ t : ℝ,0 ≤ t → t ≤ 100 → ∃ K,
        prefixElapsed K (Preorder.frestrictLe K z) ≤ t ∧
        t < prefixElapsed (K+1) (Preorder.frestrictLe (K+1) z) ∧
        (countMass (z K).1 : ℝ) ≤ 11*V ∧
        (1 ≤ t → (1/3000000000000000000 : ℝ) ≤ ((z K).1 (reactionProduct r) : ℝ)/V)) ∧
      (∃ L,prefixElapsed L (Preorder.frestrictLe L z) ≤ 100 ∧
        100 < prefixElapsed (L+1) (Preorder.frestrictLe (L+1) z) ∧
        (3/40 : ℝ) < markedWindowReward (normalizedSignedCatalyticReward V) z 0 L) := by
  have hi := jumpTrajectory_initial_population N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos hn c V 1 hV (by norm_num) basal cat)
  have hc := jumpTrajectory_consistent N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos hn c V 1 hV (by norm_num) basal cat)
  have hp := jumpTrajectory_positive_rate N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos hn c V 1 hV (by norm_num) basal cat)
  filter_upwards [hi,hc,hp,physical_time_coverage hn c V hV basal cat N] with z hzi hzc hzp hzt
  intro hz
  constructor
  · intro t ht ht100
    obtain ⟨K,hK,hK'⟩ := hzt t ht
    refine ⟨K,hK,hK',hz.1 K (hK.trans ht100),?_⟩
    intro ht1
    exact hz.2.1 K (hK.trans ht100) ((max_le ht1 hK).trans_lt hK')
  · exact marked_success_forces_signed_catalytic c V hV basal cat r z
      (by simpa only [hzi] using hinit) hzc hzp hz

end
end RandomViability
