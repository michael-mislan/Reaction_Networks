import proofs.RAF1519.Refinement.Output

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

def seed : State := ![19/20,19/20,1/20,0,0,0,0]

theorem seed_ready (theta : ℝ) (ht : 0 ≤ theta) : Ready theta seed := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    fin_cases i
    · change (0:ℝ) ≤ 19/20; norm_num
    · change (0:ℝ) ≤ 19/20; norm_num
    · change (0:ℝ) ≤ 1/20; norm_num
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
  · change (159/160:ℝ) ≤ 19/20+1/20+2*0+2*0+2*0+0 ∧
      (19/20+1/20+2*0+2*0+2*0+0:ℝ) ≤ 161/160
    norm_num
  · change (159/160:ℝ) ≤ 19/20+1/20+0+2*0+2*0+0 ∧
      (19/20+1/20+0+2*0+2*0+0:ℝ) ≤ 161/160
    norm_num
  · change (1/20:ℝ) ≤ 1/20+(9/8)*0+(7/5)*0+(9/5)*0
    norm_num
  · change (0:ℝ) ≤ (1101/1000)*theta
    positivity

structure Cycle (r d theta : ℝ) (p : Intervention) (c : State) where
  trajectory : ℝ → State
  initial : trajectory 0 = pulse p c
  nonnegative : ∀ t, 0 ≤ t → ∀ i, 0 ≤ trajectory t i
  derivative : ∀ t, 0 ≤ t → HasDerivAt trajectory (field r d (1/100) theta (trajectory t)) t
  recovered : ∀ t, 5/2 ≤ t → 1/20 ≤ stock (trajectory t)
  terminal : Ready theta (trajectory 4)
  product : 1/28 ≤ outputI trajectory
  freeProduct : 1/540 ≤ outputX trajectory
  service_bound : totalService d theta trajectory ≤ 112201/625000

def chooseCycle (r d theta : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (ht : 0 < theta) (ht' : theta ≤ 1/100)
    (p : Intervention) (c : State) (hc : Ready theta c) : Cycle r d theta p c := by
  let he := exists_returning_cycle r d theta hr hr' hd hd' ht ht' p c hc
  let X := Classical.choose he
  obtain ⟨h0,hn,hX,hy,hend⟩ := Classical.choose_spec he
  have hout := trajectory_output r d theta hr hr' hd hd' ht ht' p c hc X h0 hn hX
  exact ⟨X,h0,hn,hX,hy,hend,hout.1,hout.2.1,hout.2.2⟩

def cycleStates (r d theta : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (ht : 0 < theta) (ht' : theta ≤ 1/100)
    (protocol : ℕ → State → Intervention) (initial : {c : State // Ready theta c}) :
    ℕ → {c : State // Ready theta c}
  | 0 => initial
  | n+1 =>
    let c := cycleStates r d theta hr hr' hd hd' ht ht' protocol initial n
    let q := chooseCycle r d theta hr hr' hd hd' ht ht' (protocol n c.val) c.val c.property
    ⟨q.trajectory 4,q.terminal⟩

/-- Deterministic root: literal pulses and actual returned seven-species endpoints,
    useful outputs, both food accounts, and gross service on every finite prefix. -/
theorem R15_D (r d theta : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 1/50 ≤ d) (hd' : d ≤ 1/25) (ht : 0 < theta) (ht' : theta ≤ 1/100)
    (protocol : ℕ → State → Intervention) (c : State) (hc : Ready theta c) :
    ∃ states : ℕ → State, ∃ X : ℕ → ℝ → State,
      states 0 = c ∧ (∀ n, Ready theta (states n)) ∧
      (∀ n, X n 0 = pulse (protocol n (states n)) (states n) ∧
        X n 4 = states (n+1) ∧
        (∀ t, 0 ≤ t → ∀ i, 0 ≤ X n t i) ∧
        (∀ t, 0 ≤ t → HasDerivAt (X n) (field r d (1/100) theta (X n t)) t) ∧
        (∀ t, 5/2 ≤ t → 1/20 ≤ stock (X n t)) ∧
        1/28 ≤ outputI (X n) ∧ 1/540 ≤ outputX (X n) ∧
        totalService d theta (X n) ≤ 112201/625000) ∧
      ∀ m : ℕ, (m:ℝ)/28 ≤ ∑ n ∈ Finset.range m, outputI (X n) ∧
        (m:ℝ)/540 ≤ ∑ n ∈ Finset.range m, outputX (X n) ∧
        (∑ n ∈ Finset.range m, foodU (protocol n (states n))) ≤ 951*(m:ℝ)/200 ∧
        (∑ n ∈ Finset.range m, foodW (protocol n (states n))) ≤ 951*(m:ℝ)/200 ∧
        (∑ n ∈ Finset.range m, totalService d theta (X n)) ≤ 112201*(m:ℝ)/625000 := by
  have hd0 : 0 ≤ d := by linarith
  let s := cycleStates r d theta hr hr' hd0 hd' ht ht' protocol ⟨c,hc⟩
  let q := fun n => chooseCycle r d theta hr hr' hd0 hd' ht ht' (protocol n (s n).val) (s n).val (s n).property
  refine ⟨fun n => (s n).val,fun n => (q n).trajectory,rfl,
    fun n => (s n).property,?_,?_⟩
  · intro n
    exact ⟨(q n).initial,rfl,(q n).nonnegative,(q n).derivative,(q n).recovered,
      (q n).product,(q n).freeProduct,(q n).service_bound⟩
  · intro m
    have ho := Finset.sum_le_sum (s := Finset.range m) (fun n _ => (q n).product)
    have hx := Finset.sum_le_sum (s := Finset.range m) (fun n _ => (q n).freeProduct)
    have hu := Finset.sum_le_sum (s := Finset.range m) (fun n _ => (food_bounds (protocol n (s n).val)).1)
    have hw := Finset.sum_le_sum (s := Finset.range m) (fun n _ => (food_bounds (protocol n (s n).val)).2)
    have hg := Finset.sum_le_sum (s := Finset.range m) (fun n _ => (q n).service_bound)
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at ho hx hu hw hg
    refine ⟨?_,?_,?_,?_,?_⟩
    · convert ho using 1; ring
    · convert hx using 1; ring
    · convert hu using 1; ring
    · convert hw using 1; ring
    · convert hg using 1; ring
end
end RAF1519.Refinement

#print axioms RAF1519.Refinement.R15_D
