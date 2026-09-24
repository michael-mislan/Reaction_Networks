import proofs.ProductiveRecovery.ProductiveReturn

namespace ProductiveRecovery
noncomputable section
open MeasureTheory Set

def measuredExport (X : ℝ → State) : ℝ := ∫ t in (4:ℝ)..5, inventory (X t)
def grossService (d : ℝ) (X : ℝ → State) : ℝ :=
  ∫ t in (0:ℝ)..5, d*X t 2+d*(1/8000000000)*X t 0*X t 1
def foodU (p : Intervention) : ℝ := 5+(1-p.q+p.eU)
def foodW (p : Intervention) : ℝ := 5+(1-p.q+p.eW)

theorem cycle_output_supplies (r d : ℝ) (hd' : d ≤ 1/25) (p : Intervention)
    (X : ℝ → State) (hn : ∀ t, 0 ≤ t → Nonneg (X t))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t)
    (hcor : ∀ t, 0 ≤ t → (9/10 ≤ A (X t) ∧ A (X t) ≤ 11/10) ∧
      (9/10 ≤ B (X t) ∧ B (X t) ≤ 11/10))
    (hret : ∀ t, 4 ≤ t → Returned (X t)) :
    1/3500 ≤ measuredExport X ∧ foodU p ≤ 1151/200 ∧ foodW p ≤ 1151/200 ∧
      grossService d X ≤ 9/40 ∧ Returned (X 5) := by
  have hcont (a b : ℝ) (ha : 0 ≤ a) : ContinuousOn X (Icc a b) :=
    fun t ht => (hX t (ha.trans ht.1)).continuousAt.continuousWithinAt
  have hi : Continuous inventory := by unfold inventory; fun_prop
  have hi45 : IntervalIntegrable (fun t => inventory (X t)) volume 4 5 :=
    (hi.comp_continuousOn (hcont 4 5 (by norm_num))).intervalIntegrable_of_Icc (by norm_num)
  have houtput := intervalIntegral.integral_mono_on (a := (4:ℝ)) (b := 5)
    (by norm_num) (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1/3500:ℝ)) volume 4 5)
    hi45 (fun t ht => by
      have hh := inventory_lower (X t) (hn t (by linarith [ht.1]))
      have hy := (hret t ht.1).2.2.2
      linarith)
  have hg : Continuous (fun c : State => d*c 2+d*(1/8000000000)*c 0*c 1) := by fun_prop
  have hg05 : IntervalIntegrable (fun t => d*X t 2+d*(1/8000000000)*X t 0*X t 1) volume 0 5 :=
    (hg.comp_continuousOn (hcont 0 5 le_rfl)).intervalIntegrable_of_Icc (by norm_num)
  have hservice := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 5)
    (by norm_num) hg05
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (9/200:ℝ)) volume 0 5)
    (fun t ht => gross_service_bound d (X t) (hn t ht.1) hd'
      (hcor t ht.1).1.2 (hcor t ht.1).2.2)
  obtain ⟨_,hu,_,hw⟩ := food_feasible p
  refine ⟨?_,?_,?_,?_,hret 5 (by norm_num)⟩
  · norm_num [intervalIntegral.integral_const] at houtput
    exact houtput
  · dsimp [foodU]; linarith
  · dsimp [foodW]; linarith
  · norm_num [intervalIntegral.integral_const] at hservice
    exact hservice

theorem exists_productive_cycle (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 1/50 ≤ d) (hd' : d ≤ 1/25) (p : Intervention) (c : State) (hc : Admitted c) :
    ∃ X : ℝ → State, X 0 = pulse p c ∧
      (∀ t, 0 ≤ t → Nonneg (X t)) ∧
      (∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t) ∧
      Returned (X 4) ∧ Returned (X 5) ∧
      1/3500 ≤ measuredExport X ∧ foodU p ≤ 1151/200 ∧ foodW p ≤ 1151/200 ∧
      grossService d X ≤ 9/40 := by
  obtain ⟨X,h0,hn,hX,hcor,hret⟩ := exists_actual_return r d hr hr' (by linarith) hd' p c hc
  obtain ⟨hq,hu,hw,hg,h5⟩ := cycle_output_supplies r d hd' p X hn hX hcor hret
  exact ⟨X,h0,hn,hX,hret 4 le_rfl,h5,hq,hu,hw,hg⟩

end
end ProductiveRecovery
