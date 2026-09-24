import proofs.StartupMarked.MissionFailure

namespace StartupMarked
open Classical RandomViability StartupCount MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000
variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)] [MeasurableSingletonClass (PhysicalCountChannel n)]
theorem startup_mission_success (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 1000000000000000000000000 ≤ (V : ℝ))
    (hVn : 10000000000000*(n : ℝ) ≤ V)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ)) (hcatCap : ∀ r q,(cat r q : ℝ) ≤ 16)
    (hfood : ∀ q,molLength q ≤ 2 → c q = ∅) (r : Reaction n)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hsel : r ∈ c (reactionProduct r))
    (hbas : (1/500000000 : ℝ) ≤ basal r)
    (hcat : 4 ≤ (cat r (reactionProduct r) : ℝ))
    (N : Molecule n → ℕ)
    (hinitM : (countMass N : ℝ)/V ≤ 10)
    (hinitL : (N (reactionLeft r) : ℝ)/V = 1)
    (hinitR : (N (reactionRight r) : ℝ)/V = 1)
    : (9989/10000 : ℝ) ≤
      (physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 (by linarith) (by norm_num) basal cat N
        {z | twoWindowMission V z}).toReal := by
  have hv : 0 < (V : ℝ) := by linarith
  let μ := physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hv (by norm_num) basal cat N
  have ht := startup_mission_failure hn c V hV hVn basal cat hb hcatCap hfood r
    hl hr hlen huw huz hwz hsel hbas hcat N hinitM hinitL hinitR
  have hb' : (μ {z | ¬twoWindowMission V z}).toReal ≤ (11/10000 : ℝ) := by
    have hh := ENNReal.toReal_mono (by finiteness) ht.le
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 11/10000)] using hh
  have he := probReal_add_probReal_compl (μ := μ) (two_window_mission_measurable V)
  change (μ {z | twoWindowMission V z}).toReal+(μ {z | ¬twoWindowMission V z}).toReal = 1 at he
  change (9989/10000 : ℝ) ≤ (μ {z | twoWindowMission V z}).toReal
  linarith only [he,hb']

end
end StartupMarked

