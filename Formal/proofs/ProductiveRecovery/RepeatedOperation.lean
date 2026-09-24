import proofs.ProductiveRecovery.OutputSupplies

namespace ProductiveRecovery
noncomputable section
open scoped BigOperators

structure RealizedCycle (r d : ℝ) (p : Intervention) (c : State) where
  trajectory : ℝ → State
  initial : trajectory 0 = pulse p c
  nonnegative : ∀ t, 0 ≤ t → Nonneg (trajectory t)
  derivative : ∀ t, 0 ≤ t → HasDerivAt trajectory (field r d (trajectory t)) t
  recovered : Returned (trajectory 4)
  terminal : Returned (trajectory 5)
  output : 1/3500 ≤ measuredExport trajectory
  foodU_bound : foodU p ≤ 1151/200
  foodW_bound : foodW p ≤ 1151/200
  service : grossService d trajectory ≤ 9/40

def chooseCycle (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 1/50 ≤ d) (hd' : d ≤ 1/25) (p : Intervention) (c : State) (hc : Admitted c) :
    RealizedCycle r d p c := by
  have he := exists_productive_cycle r d hr hr' hd hd' p c hc
  let X := Classical.choose he
  have h := Classical.choose_spec he
  exact ⟨X,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2⟩

def cycleStates (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 1/50 ≤ d) (hd' : d ≤ 1/25) (protocol : ℕ → State → Intervention)
    (initial : {c : State // Admitted c}) : ℕ → {c : State // Admitted c}
  | 0 => initial
  | n+1 =>
    let c := cycleStates r d hr hr' hd hd' protocol initial n
    let q := chooseCycle r d hr hr' hd hd' (protocol n c.val) c.val c.property
    ⟨q.trajectory 5,returned_admitted _ q.terminal⟩

theorem arbitrary_finite_operation (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 1/50 ≤ d) (hd' : d ≤ 1/25) (protocol : ℕ → State → Intervention)
    (c : State) (hc : Admitted c) :
    ∃ states : ℕ → State, ∃ X : ℕ → ℝ → State,
      states 0 = c ∧ (∀ n, Admitted (states n)) ∧
      (∀ n, X n 0 = pulse (protocol n (states n)) (states n) ∧
        X n 5 = states (n+1) ∧
        (∀ t, 0 ≤ t → Nonneg (X n t)) ∧
        (∀ t, 0 ≤ t → HasDerivAt (X n) (field r d (X n t)) t) ∧
        Returned (X n 4) ∧ Returned (X n 5)) ∧
      ∀ m : ℕ, (m:ℝ)/3500 ≤ ∑ n ∈ Finset.range m, measuredExport (X n) ∧
        (∑ n ∈ Finset.range m, foodU (protocol n (states n))) ≤ 1151*(m:ℝ)/200 ∧
        (∑ n ∈ Finset.range m, foodW (protocol n (states n))) ≤ 1151*(m:ℝ)/200 ∧
        (∑ n ∈ Finset.range m, grossService d (X n)) ≤ 9*(m:ℝ)/40 := by
  let s := cycleStates r d hr hr' hd hd' protocol ⟨c,hc⟩
  let q := fun n => chooseCycle r d hr hr' hd hd' (protocol n (s n).val) (s n).val (s n).property
  refine ⟨fun n => (s n).val,fun n => (q n).trajectory,rfl,
    fun n => (s n).property,?_,?_⟩
  · intro n
    exact ⟨(q n).initial,rfl,(q n).nonnegative,(q n).derivative,(q n).recovered,(q n).terminal⟩
  · intro m
    have ho := Finset.sum_le_sum (s := Finset.range m) (fun n _ => (q n).output)
    have hu := Finset.sum_le_sum (s := Finset.range m) (fun n _ => (q n).foodU_bound)
    have hw := Finset.sum_le_sum (s := Finset.range m) (fun n _ => (q n).foodW_bound)
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
