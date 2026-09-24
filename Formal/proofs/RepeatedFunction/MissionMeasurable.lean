import proofs.RepeatedFunction.Mission

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 400000

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem two_window_mission_measurable (V : NNReal) :
    MeasurableSet {z | twoWindowMission (n := n) V z} := by
  have hclock (i : ℕ) : Measurable (fun z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) =>
      prefixElapsed i (Preorder.frestrictLe i z)) :=
    (prefixElapsed_measurable i).comp (Preorder.measurable_frestrictLe i)
  have hmass (i : ℕ) : Measurable (fun z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) =>
      (countMass (z i).1 : ℝ)) := (measurable_of_countable (fun N : Molecule n → ℕ => (countMass N : ℝ))).comp
        (measurable_pi_apply i).fst
  have hcount (i : ℕ) (q : Molecule n) :
      Measurable (fun z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) =>
        ((z i).1 q : ℝ)/V) :=
    (measurable_of_countable (fun N : Molecule n → ℕ => (N q : ℝ)/V)).comp (measurable_pi_apply i).fst
  have hexport := marked_window_reward_measurable (fun _ => exportReward (n := n) V)
  have hfeed := marked_window_reward_measurable (fun _ => grossFeedReward (n := n) V)
  unfold twoWindowMission windowOutputReady observedReady
  measurability

end
end RandomViability
