import proofs.FiniteCopyReactor.PreparedCycle

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

theorem marked_poisson_const {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (t : NNReal) (c : ℝ) (x : α) (z : ℝ) : P.poissonized t (fun _ _ => c) x z=c := by
  unfold MarkedKernel.poissonized
  simp_rw [P.law_const]
  simpa only [one_mul] using ((poissonWeight_sum t).mul_right c).tsum_eq

theorem joint_cycle_const (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (c : ℝ) (N : BoxCounts V) (z : ReactorCounters) :
    jointCycle V r d hV hr hr' hd hd' (fun _ => c) N z=c := by
  unfold jointCycle threeStage
  simp_rw [marked_poisson_const]

theorem joint_cycle_event_bounds (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (A : Set (BoxCounts V × ReactorCounters)) (N : BoxCounts V) (z : ReactorCounters) :
    0 ≤ jointCycle V r d hV hr hr' hd hd' (FiniteKernel.eventIndicator A) N z ∧
      jointCycle V r d hV hr hr' hd hd' (FiniteKernel.eventIndicator A) N z ≤ 1 :=
  three_stage_bounds _ _ _ _ _ _ _ 1 (fun X _ => FiniteKernel.eventIndicator_bounds A X) _ _

theorem joint_cycle_event_mono (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (A B : Set (BoxCounts V × ReactorCounters)) (hAB : A ⊆ B) (N : BoxCounts V) (z : ReactorCounters) :
    jointCycle V r d hV hr hr' hd hd' (FiniteKernel.eventIndicator A) N z ≤
      jointCycle V r d hV hr hr' hd hd' (FiniteKernel.eventIndicator B) N z := by
  apply three_stage_mono _ _ _ _ _ _ _ _ 1 1
    (fun X _ => FiniteKernel.eventIndicator_bounds A X) (fun X _ => FiniteKernel.eventIndicator_bounds B X)
  intro X _
  by_cases h : X ∈ A
  · simp only [FiniteKernel.eventIndicator,if_pos h,if_pos (hAB h),le_refl]
  · simp only [FiniteKernel.eventIndicator,if_neg h]
    split_ifs <;> norm_num

theorem prepared_success_failure_bound (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V)
    (hstock : (3/250)*(V:ℝ) ≤ weightedCount (boxCounts N))
    (hprep : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N) ∧ unitObs side (boxCounts N) ≤ (51/50)*(V:ℝ))
    (doseU doseW : ℝ) (hu : doseU ≤ (151/200)*(V:ℝ)) (hw : doseW ≤ (151/200)*(V:ℝ)) :
    jointCycle V r d hV (by linarith) hr' hd hd'
      (FiniteKernel.eventIndicator {X | ¬CycleSuccess V X}) N (initialCounters doseU doseW) ≤ preparedCycleError V := by
  have hsub : {X | ¬CycleSuccess V X} ⊆ PreparedCycleFailure V := by
    intro X hX
    by_contra hn
    exact hX (outside_prepared_cycle_failure V X hn)
  exact (joint_cycle_event_mono V r d hV (by linarith) hr' hd hd' _ _ hsub N (initialCounters doseU doseW)).trans
    (prepared_cycle_failure_bound V r d hV hlarge hr hr' hd hd' N hstock hprep doseU doseW hu hw)

end
end FiniteCopyReactor
