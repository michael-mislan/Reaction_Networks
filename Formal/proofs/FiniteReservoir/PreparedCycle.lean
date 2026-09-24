import proofs.FiniteReservoir.StateRestart

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical

def PreparedCycleFailure (V M : ℕ) : Set (BoxState V M × ReactorCounters) :=
  JointCounterFailure V M ∪ {X | X.1 ∈ StateRestartFailure V M}

def preparedCycleError (V : ℝ) : ℝ := jointCounterError V+stateRestartError V

def CycleSuccess (V M : ℕ) (X : BoxState V M × ReactorCounters) : Prop :=
  Restart V (boxCounts X.1.1) ∧
    (Nat.ceil ((V:ℝ)/56):ℝ) ≤ X.2 1 ∧ (Nat.ceil ((V:ℝ)/1080):ℝ) ≤ X.2 0 ∧
    X.2 2 ≤ 5*(V:ℝ) ∧ X.2 3 ≤ 5*(V:ℝ) ∧ X.2 4 ≤ (Nat.floor ((V:ℝ)/5):ℝ)

theorem prepared_cycle_failure_bound (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
     (N : BoxState V M)
    (hstock : (3/250)*(V:ℝ) ≤ weightedCount (boxCounts N.1))
    (hprep : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N.1) ∧ unitObs side (boxCounts N.1) ≤ (51/50)*(V:ℝ))
    (doseU doseW : ℝ) (hu : doseU ≤ (151/200)*(V:ℝ)) (hw : doseW ≤ (151/200)*(V:ℝ)) :
    jointCycle V M p hV
      (FiniteKernel.eventIndicator (PreparedCycleFailure V M)) N (initialCounters doseU doseW) ≤ preparedCycleError V := by
  have hU := joint_cycle_event_union V M p hV
    (JointCounterFailure V M) {X | X.1 ∈ StateRestartFailure V M} N (initialCounters doseU doseW)
  have hC := joint_counter_budget V M p hV hlarge N doseU doseW hu hw
  have hS := state_restart_failure_bound V M p hV N hstock hprep
  have hM := joint_state_marginal V M p hV
    (FiniteKernel.eventIndicator (StateRestartFailure V M)) N doseU doseW
  have hS' : jointCycle V M p hV
      (FiniteKernel.eventIndicator {X | X.1 ∈ StateRestartFailure V M}) N (initialCounters doseU doseW) ≤ stateRestartError V := hM.le.trans hS
  exact hU.trans (add_le_add hC hS')

theorem outside_prepared_cycle_failure (V M : ℕ) (X : BoxState V M × ReactorCounters)
    (h : X ∉ PreparedCycleFailure V M) : CycleSuccess V M X := by
  have hS : X.1 ∉ StateRestartFailure V M := fun hn => h (Or.inr hn)
  have hC : X ∉ JointCounterFailure V M := fun hn => h (Or.inl hn)
  have ha := (outside_state_restart_failure V M X.1 hS).1
  have hR := (outside_state_restart_failure V M X.1 hS).2
  have h0 : (V:ℝ)/1080+1 < X.2 0 := by
    by_contra hn
    exact hC (Or.inl (Or.inl ⟨ha,le_of_not_gt hn⟩))
  have h1 : (V:ℝ)/56+1 < X.2 1 := by
    by_contra hn
    exact hC (Or.inl (Or.inr ⟨ha,le_of_not_gt hn⟩))
  have h2 : X.2 2 < 5*(V:ℝ) := by
    by_contra hn
    exact hC (Or.inr (Or.inl (Or.inl (le_of_not_gt hn))))
  have h3 : X.2 3 < 5*(V:ℝ) := by
    by_contra hn
    exact hC (Or.inr (Or.inl (Or.inr (le_of_not_gt hn))))
  have h4 : X.2 4 < (V:ℝ)/5-1 := by
    by_contra hn
    exact hC (Or.inr (Or.inr (le_of_not_gt hn)))
  refine ⟨hR,?_,?_,h2.le,h3.le,?_⟩
  · exact ((Nat.ceil_lt_add_one (show 0 ≤ (V:ℝ)/56 by positivity)).trans h1).le
  · exact ((Nat.ceil_lt_add_one (show 0 ≤ (V:ℝ)/1080 by positivity)).trans h0).le
  · exact (h4.trans (Nat.sub_one_lt_floor ((V:ℝ)/5))).le

end
end FiniteReservoir
