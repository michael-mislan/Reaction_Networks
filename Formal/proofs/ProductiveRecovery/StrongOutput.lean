import proofs.ProductiveRecovery.StrongReturn
import proofs.ProductiveRecovery.OutputSupplies

namespace ProductiveRecovery
noncomputable section
open MeasureTheory Set

def routineExport (X : ℝ → State) : ℝ := ∫ t in (3:ℝ)..4, inventory (X t)
def routineService (d : ℝ) (X : ℝ → State) : ℝ :=
  ∫ t in (0:ℝ)..4, d*X t 2+d*(1/8000000000)*X t 0*X t 1
def routineFoodU (p : Intervention) : ℝ := 4+(1-p.q+p.eU)
def routineFoodW (p : Intervention) : ℝ := 4+(1-p.q+p.eW)

theorem routine_output_supplies (r d : ℝ) (hd' : d ≤ 1/25) (p : Intervention)
    (X : ℝ → State) (hn : ∀ t, 0 ≤ t → Nonneg (X t))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t)
    (hcor : ∀ t, 0 ≤ t → (9/10 ≤ A (X t) ∧ A (X t) ≤ 11/10) ∧
      (9/10 ≤ B (X t) ∧ B (X t) ≤ 11/10))
    (hret : ∀ t, 3 ≤ t → StrongReturned (X t)) :
    1/28 ≤ routineExport X ∧ routineFoodU p ≤ 951/200 ∧ routineFoodW p ≤ 951/200 ∧
      routineService d X ≤ 9/50 ∧ StrongReturned (X 4) := by
  have hcont (a b : ℝ) (ha : 0 ≤ a) : ContinuousOn X (Icc a b) :=
    fun t ht => (hX t (ha.trans ht.1)).continuousAt.continuousWithinAt
  have hi : Continuous inventory := by unfold inventory; fun_prop
  have hi45 : IntervalIntegrable (fun t => inventory (X t)) volume 3 4 :=
    (hi.comp_continuousOn (hcont 3 4 (by norm_num))).intervalIntegrable_of_Icc (by norm_num)
  have houtput := intervalIntegral.integral_mono_on (a := (3:ℝ)) (b := 4)
    (by norm_num) (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1/28:ℝ)) volume 3 4)
    hi45 (fun t ht => by
      have hh := inventory_lower (X t) (hn t (by linarith [ht.1]))
      have hy := (hret t ht.1).2.2.2
      linarith)
  have hg : Continuous (fun c : State => d*c 2+d*(1/8000000000)*c 0*c 1) := by fun_prop
  have hg05 : IntervalIntegrable (fun t => d*X t 2+d*(1/8000000000)*X t 0*X t 1) volume 0 4 :=
    (hg.comp_continuousOn (hcont 0 4 le_rfl)).intervalIntegrable_of_Icc (by norm_num)
  have hservice := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 4)
    (by norm_num) hg05
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (9/200:ℝ)) volume 0 4)
    (fun t ht => gross_service_bound d (X t) (hn t ht.1) hd'
      (hcor t ht.1).1.2 (hcor t ht.1).2.2)
  obtain ⟨_,hu,_,hw⟩ := food_feasible p
  refine ⟨?_,?_,?_,?_,hret 4 (by norm_num)⟩
  · norm_num [intervalIntegral.integral_const] at houtput
    exact houtput
  · dsimp [routineFoodU]; linarith
  · dsimp [routineFoodW]; linarith
  · norm_num [intervalIntegral.integral_const] at hservice
    exact hservice

theorem exists_routine_cycle (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 1/50 ≤ d) (hd' : d ≤ 1/25) (p : Intervention) (c : State) (hc : StrongReturned c) :
    ∃ X : ℝ → State, X 0 = pulse p c ∧
      (∀ t, 0 ≤ t → Nonneg (X t)) ∧
      (∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t) ∧
      StrongReturned (X 3) ∧ StrongReturned (X 4) ∧
      1/28 ≤ routineExport X ∧ routineFoodU p ≤ 951/200 ∧ routineFoodW p ≤ 951/200 ∧
      routineService d X ≤ 9/50 := by
  obtain ⟨X,h0,hn,hX,hcor,_⟩ := exists_actual_return r d hr hr' (by linarith) hd' p c (strong_admitted c hc)
  have hret := (routine_return r d hr hr' (by linarith) hd' p c hc X h0 hn hX).2
  obtain ⟨hq,hu,hw,hg,h5⟩ := routine_output_supplies r d hd' p X hn hX hcor hret
  exact ⟨X,h0,hn,hX,hret 3 le_rfl,h5,hq,hu,hw,hg⟩

end
end ProductiveRecovery
