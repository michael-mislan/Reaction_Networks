import proofs.FiniteCopyReactor.JointProbability
import proofs.FiniteReservoir.PreparedCycle

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical

theorem joint_cycle_const (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (c : ℝ) (N : BoxState V M) (z : ReactorCounters) :
    jointCycle V M p hV (fun _ => c) N z=c := by
  unfold jointCycle threeStage
  simp_rw [marked_poisson_const]

theorem joint_cycle_event_bounds (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (A : Set (BoxState V M × ReactorCounters)) (N : BoxState V M) (z : ReactorCounters) :
    0 ≤ jointCycle V M p hV (FiniteKernel.eventIndicator A) N z ∧
      jointCycle V M p hV (FiniteKernel.eventIndicator A) N z ≤ 1 :=
  three_stage_bounds _ _ _ _ _ _ _ 1 (fun X _ => FiniteKernel.eventIndicator_bounds A X) _ _

theorem joint_cycle_event_mono (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (A B : Set (BoxState V M × ReactorCounters)) (hAB : A ⊆ B) (N : BoxState V M) (z : ReactorCounters) :
    jointCycle V M p hV (FiniteKernel.eventIndicator A) N z ≤
      jointCycle V M p hV (FiniteKernel.eventIndicator B) N z := by
  apply three_stage_mono _ _ _ _ _ _ _ _ 1 1
    (fun X _ => FiniteKernel.eventIndicator_bounds A X) (fun X _ => FiniteKernel.eventIndicator_bounds B X)
  intro X _
  by_cases h : X ∈ A
  · simp only [FiniteKernel.eventIndicator,if_pos h,if_pos (hAB h),le_refl]
  · simp only [FiniteKernel.eventIndicator,if_neg h]
    split_ifs <;> norm_num

theorem prepared_success_failure_bound (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
     (N : BoxState V M)
    (hstock : (3/250)*(V:ℝ) ≤ weightedCount (boxCounts N.1))
    (hprep : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N.1) ∧ unitObs side (boxCounts N.1) ≤ (51/50)*(V:ℝ))
    (doseU doseW : ℝ) (hu : doseU ≤ (151/200)*(V:ℝ)) (hw : doseW ≤ (151/200)*(V:ℝ)) :
    jointCycle V M p hV
      (FiniteKernel.eventIndicator {X | ¬CycleSuccess V M X}) N (initialCounters doseU doseW) ≤ preparedCycleError V := by
  have hsub : {X | ¬CycleSuccess V M X} ⊆ PreparedCycleFailure V M := by
    intro X hX
    by_contra hn
    exact hX (outside_prepared_cycle_failure V M X hn)
  exact (joint_cycle_event_mono V M p hV _ _ hsub N (initialCounters doseU doseW)).trans
    (prepared_cycle_failure_bound V M p hV hlarge N hstock hprep doseU doseW hu hw)

end
end FiniteReservoir
