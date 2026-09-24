import proofs.RandomViability.BindingOperatingFailures

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy

theorem missedEntry_fixed (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (X : OutputState) :
    (operatingOutputKernel true k r hk hk1 hr hr1).step
      (FiniteKernel.eventIndicator {X | missedEntry X}) X =
      FiniteKernel.eventIndicator {X | missedEntry X} X := by
  have hg : (outputModel true (1/500000000) k r (by norm_num) hk (by linarith)).generator
      (FiniteKernel.eventIndicator {X | missedEntry X}) X=0 := by
    by_cases hp : trackedPhase X.1=0
    · exact output_generator_deadline_failure _ _ _ _ _ _ _ X hp
    · have hn (j : Fin 18) : FiniteKernel.eventIndicator {X | missedEntry X} (outputNext true X j)=0 := by
        have hh := trackedNext_nezero X.1 j hp
        simp [FiniteKernel.eventIndicator,missedEntry,outputNext,hh]
      simp only [FiniteJumpModel.generator,outputModel,hn]
      simp [FiniteKernel.eventIndicator,missedEntry,hp]
  rw [operatingOutputKernel,FiniteJumpModel.uniformize_step,hg]
  simp

theorem operating_missed_entry (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) :
    operatingExpectation k r hk hk1 hr hr1 (FiniteKernel.eventIndicator {X | missedEntry X}) <
      1/12+1/600000000 := by
  unfold operatingExpectation twoPeriod
  simp only [poissonized_fixed _ _ (missedEntry_fixed k r hk hk1 hr hr1)]
  change (operatingOutputKernel false k r hk hk1 hr hr1).poissonized 150000000000000
    (fun X=>FiniteKernel.eventIndicator {Z | trackedPhase Z=0 ∧ resourceGood (boxCounts (trackedCounts Z)) 100000000} X.1)
    outputInitial < _
  rw [output_poisson_project]
  exact tracked_entry_deadline k r hk hk1 hr hr1

end
end RandomViability.Binding
