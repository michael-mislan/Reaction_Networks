import proofs.FiniteCopyReactor.StateRestart

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

def PreparedCycleFailure (V : ℕ) : Set (BoxCounts V × ReactorCounters) :=
  JointCounterFailure V ∪ {X | X.1 ∈ StateRestartFailure V}

def preparedCycleError (V : ℝ) : ℝ := jointCounterError V+stateRestartError V

def CycleSuccess (V : ℕ) (X : BoxCounts V × ReactorCounters) : Prop :=
  Restart V (boxCounts X.1) ∧
    (Nat.ceil ((V:ℝ)/56):ℝ) ≤ X.2 1 ∧ (Nat.ceil ((V:ℝ)/1080):ℝ) ≤ X.2 0 ∧
    X.2 2 ≤ 5*(V:ℝ) ∧ X.2 3 ≤ 5*(V:ℝ) ∧ X.2 4 ≤ (Nat.floor ((V:ℝ)/5):ℝ)

theorem prepared_cycle_failure_bound (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V)
    (hstock : (3/250)*(V:ℝ) ≤ weightedCount (boxCounts N))
    (hprep : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N) ∧ unitObs side (boxCounts N) ≤ (51/50)*(V:ℝ))
    (doseU doseW : ℝ) (hu : doseU ≤ (151/200)*(V:ℝ)) (hw : doseW ≤ (151/200)*(V:ℝ)) :
    jointCycle V r d hV (by linarith) hr' hd hd'
      (FiniteKernel.eventIndicator (PreparedCycleFailure V)) N (initialCounters doseU doseW) ≤ preparedCycleError V := by
  have hU := joint_cycle_event_union V r d hV (by linarith) hr' hd hd'
    (JointCounterFailure V) {X | X.1 ∈ StateRestartFailure V} N (initialCounters doseU doseW)
  have hC := joint_counter_budget V r d hV hlarge hr hr' hd hd' N doseU doseW hu hw
  have hS := state_restart_failure_bound V r d hV hr hr' hd hd' N hstock hprep
  have hM := joint_state_marginal V r d hV (by linarith) hr' hd hd'
    (FiniteKernel.eventIndicator (StateRestartFailure V)) N doseU doseW
  have hS' : jointCycle V r d hV (by linarith) hr' hd hd'
      (FiniteKernel.eventIndicator {X | X.1 ∈ StateRestartFailure V}) N (initialCounters doseU doseW) ≤ stateRestartError V := hM.le.trans hS
  exact hU.trans (add_le_add hC hS')

theorem outside_prepared_cycle_failure (V : ℕ) (X : BoxCounts V × ReactorCounters)
    (h : X ∉ PreparedCycleFailure V) : CycleSuccess V X := by
  have hS : X.1 ∉ StateRestartFailure V := fun hn => h (Or.inr hn)
  have hC : X ∉ JointCounterFailure V := fun hn => h (Or.inl hn)
  have ha := (outside_state_restart_failure V X.1 hS).1
  have hR := (outside_state_restart_failure V X.1 hS).2
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
end FiniteCopyReactor
