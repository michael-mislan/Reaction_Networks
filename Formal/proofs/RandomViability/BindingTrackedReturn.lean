import proofs.RandomViability.BindingTrackedModel

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal

def trackedReturnPotential (X : TrackedCounts) : ℝ :=
  if trackedPhase X=0 then Real.exp (-1600) else returnPotential (boxCounts (trackedCounts X))

theorem tracked_return_nonneg (X : TrackedCounts) : 0 ≤ trackedReturnPotential X := by
  unfold trackedReturnPotential returnPotential
  split_ifs <;> positivity

theorem tracked_return_exit (X : TrackedCounts) (h : trackedPhase X=2) :
    1 ≤ trackedReturnPotential X := by
  have hv := X.property.2.2 h
  have hp : trackedPhase X≠0 := by omega
  simp only [trackedReturnPotential,if_neg hp]
  exact returnPotential_exit (boxCounts (trackedCounts X)) hv

theorem return_before_entry (X : TrackedCounts) (j : Fin 18) (hp : trackedPhase X=0) :
    trackedReturnPotential (trackedNext X j) ≤ trackedReturnPotential X := by
  have hp2 : trackedPhase X≠2 := by omega
  simp only [trackedReturnPotential,trackedNext_phase X j hp2,trackedNext_counts X j hp2,
    phaseStep,hp,if_true]
  by_cases hY : 40000 ≤ weightedCount (boxCounts (boxNext 100000000 (trackedCounts X) j))
  · simp only [if_pos hY]
    norm_num
    exact returnPotential_small _ hY
  · simp [hY]

theorem return_after_entry (X : TrackedCounts) (j : Fin 18) (hp : trackedPhase X=1) :
    trackedReturnPotential (trackedNext X j) =
      returnPotential (boxCounts (boxNext 100000000 (trackedCounts X) j)) := by
  have hp2 : trackedPhase X≠2 := by omega
  simp only [trackedReturnPotential,trackedNext_phase X j hp2,trackedNext_counts X j hp2,
    phaseStep,hp]
  split_ifs <;> norm_num at *
  omega

theorem tracked_return_foster (eps k r : ℝ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22) (X : TrackedCounts) :
    (trackedModel eps k r heps hk (by linarith)).generator trackedReturnPotential X ≤ returnSource := by
  by_cases h : trackingEnabled X
  · by_cases hp : trackedPhase X=0
    · have hh : (trackedModel eps k r heps hk (by linarith)).generator trackedReturnPotential X ≤ 0 := by
        unfold FiniteJumpModel.generator
        apply Finset.sum_nonpos
        intro j _
        exact mul_nonpos_of_nonneg_of_nonpos ((trackedModel eps k r heps hk (by linarith)).nonneg X j)
          (sub_nonpos.mpr (return_before_entry X j hp))
      exact hh.trans (by unfold returnSource; positivity)
    · have hp1 : trackedPhase X=1 := by have hh := h.1; omega
      have he : (trackedModel eps k r heps hk (by linarith)).generator trackedReturnPotential X =
          literalGenerator (boxCounts (trackedCounts X)) 100000000 eps k r returnPotential := by
        simp only [FiniteJumpModel.generator,trackedModel,if_pos h,literalGenerator]
        apply Finset.sum_congr rfl
        intro j _
        rw [return_after_entry X j hp1,boxNext_exact 100000000 (trackedCounts X) j h.2]
        simp only [trackedReturnPotential,if_neg hp]
      rw [he]
      exact return_foster _ eps k r heps heps1 hk hk1 hr hr1 h.2
  · rw [tracked_generator_outside eps k r heps hk (by linarith) X _ h]
    unfold returnSource
    positivity

theorem tracked_initial_return : trackedReturnPotential trackedInitial = Real.exp (-1600) := by
  simp [trackedReturnPotential,trackedPhase,trackedInitial]

theorem tracked_return_probability (eps k r : ℝ) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (q : ℝ≥0) (hq : 0 < (q:ℝ))
    (hbound : ∀ X, (trackedModel eps k r heps hk (by linarith)).total X ≤ q) :
    ((trackedModel eps k r heps hk (by linarith)).uniformize q hq hbound).poissonized (q*1000)
      (FiniteKernel.eventIndicator {X | trackedPhase X=2}) trackedInitial < 1/10000 := by
  have h := (trackedModel eps k r heps hk (by linarith)).uniformized_event_bound q 1000 hq hbound
    {X | trackedPhase X=2} trackedReturnPotential 1 returnSource tracked_return_nonneg
    (fun X hX => tracked_return_exit X hX) (tracked_return_foster eps k r heps heps1 hk hk1 hr hr1) trackedInitial
  rw [tracked_initial_return] at h
  norm_num only [one_mul,NNReal.coe_ofNat] at h
  exact h.trans_lt evaluated_return_budget

end
end RandomViability.Binding
