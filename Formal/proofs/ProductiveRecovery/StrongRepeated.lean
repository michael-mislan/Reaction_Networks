import proofs.ProductiveRecovery.StrongOutput

namespace ProductiveRecovery
noncomputable section
open scoped BigOperators

structure RoutineCycle (r d : ℝ) (p : Intervention) (c : State) where
  trajectory : ℝ → State
  initial : trajectory 0 = pulse p c
  nonnegative : ∀ t, 0 ≤ t → Nonneg (trajectory t)
  derivative : ∀ t, 0 ≤ t → HasDerivAt trajectory (field r d (trajectory t)) t
  recovered : StrongReturned (trajectory 3)
  terminal : StrongReturned (trajectory 4)
  output : 1/28 ≤ routineExport trajectory
  routineFoodU_bound : routineFoodU p ≤ 951/200
  routineFoodW_bound : routineFoodW p ≤ 951/200
  service : routineService d trajectory ≤ 9/50

def chooseRoutine (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 1/50 ≤ d) (hd' : d ≤ 1/25) (p : Intervention) (c : State) (hc : StrongReturned c) :
    RoutineCycle r d p c := by
  have he := exists_routine_cycle r d hr hr' hd hd' p c hc
  let X := Classical.choose he
  have h := Classical.choose_spec he
  exact ⟨X,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2⟩

def routineStates (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 1/50 ≤ d) (hd' : d ≤ 1/25) (protocol : ℕ → State → Intervention)
    (initial : {c : State // StrongReturned c}) : ℕ → {c : State // StrongReturned c}
  | 0 => initial
  | n+1 =>
    let c := routineStates r d hr hr' hd hd' protocol initial n
    let q := chooseRoutine r d hr hr' hd hd' (protocol n c.val) c.val c.property
    ⟨q.trajectory 4,q.terminal⟩

theorem arbitrary_routine_operation (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 1/50 ≤ d) (hd' : d ≤ 1/25) (protocol : ℕ → State → Intervention)
    (c : State) (hc : StrongReturned c) :
    ∃ states : ℕ → State, ∃ X : ℕ → ℝ → State,
      states 0 = c ∧ (∀ n, StrongReturned (states n)) ∧
      (∀ n, X n 0 = pulse (protocol n (states n)) (states n) ∧
        X n 4 = states (n+1) ∧
        (∀ t, 0 ≤ t → Nonneg (X n t)) ∧
        (∀ t, 0 ≤ t → HasDerivAt (X n) (field r d (X n t)) t) ∧
        StrongReturned (X n 3) ∧ StrongReturned (X n 4)) ∧
      ∀ m : ℕ, (m:ℝ)/28 ≤ ∑ n ∈ Finset.range m, routineExport (X n) ∧
        (∑ n ∈ Finset.range m, routineFoodU (protocol n (states n))) ≤ 951*(m:ℝ)/200 ∧
        (∑ n ∈ Finset.range m, routineFoodW (protocol n (states n))) ≤ 951*(m:ℝ)/200 ∧
        (∑ n ∈ Finset.range m, routineService d (X n)) ≤ 9*(m:ℝ)/50 := by
  let s := routineStates r d hr hr' hd hd' protocol ⟨c,hc⟩
  let q := fun n => chooseRoutine r d hr hr' hd hd' (protocol n (s n).val) (s n).val (s n).property
  refine ⟨fun n => (s n).val,fun n => (q n).trajectory,rfl,
    fun n => (s n).property,?_,?_⟩
  · intro n
    exact ⟨(q n).initial,rfl,(q n).nonnegative,(q n).derivative,(q n).recovered,(q n).terminal⟩
  · intro m
    have ho := Finset.sum_le_sum (s := Finset.range m) (fun n _ => (q n).output)
    have hu := Finset.sum_le_sum (s := Finset.range m) (fun n _ => (q n).routineFoodU_bound)
    have hw := Finset.sum_le_sum (s := Finset.range m) (fun n _ => (q n).routineFoodW_bound)
    have hg := Finset.sum_le_sum (s := Finset.range m) (fun n _ => (q n).service)
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at ho hu hw hg
    refine ⟨?_,?_,?_,?_⟩
    · convert ho using 1
      ring
    · convert hu using 1
      ring
    · convert hw using 1
      ring
    · convert hg using 1
      ring

end
end ProductiveRecovery
