import proofs.StartupMarked.MissionPath
import proofs.StartupMarked.PositiveWaiting

namespace StartupMarked
open Classical RandomViability StartupCount MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy Filter
open scoped Topology ENNReal
noncomputable section
set_option maxHeartbeats 150000

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem startup_two_window_ae (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 1000000000000000000000000 ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ)) (hcatCap : ∀ r q,(cat r q : ℝ) ≤ 16)
    (hfood : ∀ q,molLength q ≤ 2 → c q = ∅) (r : Reaction n)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hsel : r ∈ c (reactionProduct r))
    (hcat : 4 ≤ (cat r (reactionProduct r) : ℝ))
    (N : Molecule n → ℕ)
    (hinitM : (countMass N : ℝ)/V ≤ 10)
    (hinitL : (N (reactionLeft r) : ℝ)/V = 1)
    (hinitR : (N (reactionRight r) : ℝ)/V = 1)
    : ∀ᵐ z ∂physicalTrajectoryLaw hn c V 1 (by linarith) (by norm_num) basal cat N,
      massNoiseBound c V basal cat 200 (1/4) z →
      coordinateNoiseBound c V basal cat (reactionLeft r) 200 (1/100000) z →
      coordinateNoiseBound c V basal cat (reactionRight r) 200 (1/100000) z →
      z ∉ lowDuring (countGuard V r) (fun N => N (reactionProduct r)) (stockThreshold V) 1 199 →
      markedRewardNoiseBound c V basal cat (cutoffReward V r stockCutoff) 200 15 z →
      markedRewardNoiseBound c V basal cat (fun _ => exportReward V) 200 (1/40) z →
      markedRewardNoiseBound c V basal cat (fun _ => grossFeedReward V) 200 1 z →
      twoWindowMission V z := by
  have hv : 0 < (V : ℝ) := by linarith
  have hi := jumpTrajectory_initial_population N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos hn c V 1 hv (by norm_num) basal cat)
  have hc := jumpTrajectory_consistent N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos hn c V 1 hv (by norm_num) basal cat)
  have hw := jumpTrajectory_wait_pos N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos hn c V 1 hv (by norm_num) basal cat)
  filter_upwards [hi,hc,hw,physical_prefix_times_diverge hn c V hv basal cat N]
    with z hzi hzc hzw hzd
  intro hM hL hR hgood hmarked hE hB
  exact startup_two_window_mission hn c V hV basal cat hb hcatCap hfood r
    hl hr hlen huw huz hwz hsel hcat z
    (by simpa only [hzi] using hinitM) (by simpa only [hzi] using hinitL)
    (by simpa only [hzi] using hinitR) hzc hzw hzd hM hL hR hgood hmarked hE hB

end
end StartupMarked
