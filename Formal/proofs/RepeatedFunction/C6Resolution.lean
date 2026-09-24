import proofs.RepeatedFunction.MissionPosterior
import proofs.RepeatedFunction.MissionAccounts

namespace RandomViability
open Classical Filter Topology MeasureTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

local instance rootChannelSpace (n : ℕ) : MeasurableSpace (PhysicalCountChannel n) := ⊤
local instance rootChannelSingleton (n : ℕ) : MeasurableSingletonClass (PhysicalCountChannel n) := ⟨fun _ => trivial⟩

/-- C6 finite-horizon resolution on the literal polymer source. The event
contains readiness at 1, two consecutive export/ready windows, and gross
feed/mass bounds. The actual-law account rules out preloaded nonfood output.
No arbitrary-state restart or infinite-horizon claim is made. -/
theorem c6_two_window_resolution (volume : ℕ → ℕ)
    (hvolume : ∀ n,collectiveMinimalVolume n ≤ volume n) :
    (∀ n (hn : 4 ≤ n) (a : ℝ),1 < a →
      let hV := (collective_minimal_volume_pos n).trans_le (hvolume n)
      let S := averagedMissionProbability hn (volume n) hV a (fun _ => True)
      0 < missionLowerBound a n (volume n) ∧ missionLowerBound a n (volume n) ≤ S ∧
        S ≤ missionUpperBound a n (volume n)) ∧
    (∀ᶠ n in atTop,
      missionAsymptoticLower*productiveSourceIncidence n ≤ missionJointProbability volume hvolume (fun _ _ => True) n ∧
      missionJointProbability volume hvolume (fun _ _ => True) n ≤ 15481*productiveSourceIncidence n) ∧
    (∀ᶠ n in atTop,missionAsymptoticLower/15481 ≤
      missionJointProbability volume hvolume missionSeedEvent n/
        missionJointProbability volume hvolume (fun _ _ => True) n) ∧
    Tendsto (fun n => missionJointProbability volume hvolume (fun _ => noProductiveSingleton) n/
      missionJointProbability volume hvolume (fun _ _ => True) n) atTop (𝓝 0) ∧
    (∀ n (hn : 4 ≤ n) (c : SourceMoleculeFibreConfig n) (u : KineticMarkConfig n),
      ∀ᵐ z ∂physicalTrajectoryLaw (by omega : 2 ≤ n) c (volume n : NNReal) 1
        (by exact_mod_cast (collective_minimal_volume_pos n).trans_le (hvolume n)) (by norm_num)
        (kineticBasal u) (kineticCatalytic u) (foodOnlyCounts n (volume n)),
        twoWindowMission (volume n : NNReal) z →
          ∃ L,prefixElapsed L (Preorder.frestrictLe L z) ≤ 199 ∧
            199 < prefixElapsed (L+1) (Preorder.frestrictLe (L+1) z) ∧
            (1/5 : ℝ) < markedWindowReward (signedSynthesisReward (volume n : NNReal)) z 0 L) := by
  refine ⟨?_,mission_joint_eventual_bounds volume hvolume (fun _ _ => True) (fun _ _ _ _ => trivial),
    seed_given_mission_eventually_positive volume hvolume,
    no_singleton_given_mission_tendsto_zero volume hvolume,?_⟩
  · intro n hn a ha
    have hh := two_window_finite_source_resolution hn (volume n) (hvolume n) a ha
    exact ⟨hh.1,hh.2.1,hh.2.2.1⟩
  · intro n hn c u
    exact physical_mission_accounts (by omega) c (volume n)
      ((collective_minimal_volume_pos n).trans_le (hvolume n)) (kineticBasal u) (kineticCatalytic u)

end
end RandomViability
