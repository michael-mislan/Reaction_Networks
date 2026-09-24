import proofs.StartupCount.AllTimeCrossing
import proofs.StartupCount.SourceCountLaw
import proofs.RandomViability.PhysicalTimeCoverage

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000
variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- The two-boundary-state compensator on the literal physical source law.
No restart, comparison chain, or assumed compensator identity is required. -/
theorem source_count_crossing_bound (hn : 2 ≤ n) (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (r : Reaction n) (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → cfg z = ∅)
    (hlen : molLength (reactionProduct r) = 4)
    (N₀ : Molecule n → ℕ) (h : ℕ) (hh : 0 < h) (a b : ℝ) (ha : 0 ≤ a) :
    physicalTrajectoryLaw hn cfg V 1 hV (by norm_num) basal cat N₀
      (lowDuring (countGuard V r) (fun N => N (reactionProduct r)) h a b) ≤
    physicalTrajectoryLaw hn cfg V 1 hV (by norm_num) basal cat N₀
      (guardedLowEvent (countGuard V r) (fun N => N (reactionProduct r)) (h-1) a) +
    ∫⁻ t : ℝ,if a < t ∧ t ≤ b then ENNReal.ofReal (1476*(h+1 : ℕ)) *
      physicalTrajectoryLaw hn cfg V 1 hV (by norm_num) basal cat N₀
        (guardedLowEvent (countGuard V r) (fun N => N (reactionProduct r)) (h+1) t) else 0 := by
  apply lowDuring_probability_le unboundedPhysicalNext (unboundedPhysicalRate cfg V 1 basal cat)
    (unboundedPhysicalRate_nonneg cfg V 1 basal cat)
    (unbounded_total_pos hn cfg V 1 hV (by norm_num) basal cat)
    N₀ (countGuard V r) (fun N => N (reactionProduct r)) h (h+1) hh (1476*(h+1 : ℕ)) a b
  · filter_upwards [physical_prefix_times_diverge hn cfg V hV basal cat N₀] with z hz
    obtain ⟨J,hpre,hpost⟩ := unbounded_elapsed_covers_time z hz a ha
    simp only [prefixElapsed_eq_jumpElapsed] at hpre hpost
    exact ⟨J,hpre,hpost⟩
  · intro N hN
    exact physical_crossing_rate_le cfg V hV basal cat N hb hc hfood hN.1
      (reactionProduct r) hlen h

end
end StartupCount
