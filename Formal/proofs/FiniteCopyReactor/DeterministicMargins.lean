import proofs.FiniteCopyReactor.Margins
import proofs.ProductiveRecovery.StrongOutput
import proofs.ProductiveRecovery.FreeProduct

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery MeasureTheory

/-- Deterministic diagnostic: the strengthened stock target has strict room above restart. -/
theorem deterministic_interior_return (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (p : Intervention) (c : State) (hc : StrongReturned c)
    (X : ℝ → State) (h0 : X 0=pulse p c) (hn : ∀ t,0 ≤ t → Nonneg (X t))
    (hX : ∀ t,0 ≤ t → HasDerivAt X (field r d (X t)) t) :
    ∀ t,11/4 ≤ t → 3/50 ≤ Y (X t) := by
  have hcor := (trajectory_return r d hr hr' hd hd' p c (strong_admitted c hc) X h0 hn hX).1
  have hy0 : 49/4800 ≤ (5/6:ℝ)*Y (X 0) := by
    rw [h0]
    have hp := pulse_catalyst p c hc.1
    linarith [hc.2.2.2]
  have he : (1/20:ℝ)/(49/4800) ≤ Real.exp ((3/5)*(11/4)) := by
    have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 33/20) 6
    norm_num [Finset.sum_range_succ] at hh ⊢
    linarith
  have hg := strong_scheduled_recovery (fun t => (5/6:ℝ)*Y (X t))
    (fun t => (5/6:ℝ)*Y (field r d (X t)))
    (fun t ht => (deriv_Y X _ t (hX t ht)).const_mul (5/6))
    (49/4800) (11/4) (by norm_num) hy0 (by norm_num) he
    (fun t ht _ hlow => by
      have hh := interior_guarded_growth r d (X t) (hn t ht) hr hr' hd hd'
        (hcor t ht).1.1 (hcor t ht).2.1 (by linarith)
      linarith)
  intro t ht
  have hh := hg t ht
  linarith

/-- Source-derived deterministic collection and expenditure margins used to select the count targets. -/
theorem deterministic_collection_margins (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (p : Intervention) (c : State) (hc : StrongReturned c)
    (X : ℝ → State) (h0 : X 0=pulse p c) (hn : ∀ t,0 ≤ t → Nonneg (X t))
    (hX : ∀ t,0 ≤ t → HasDerivAt X (field r d (X t)) t) :
    (∀ t,11/4 ≤ t → 3/50 ≤ Y (X t)) ∧ StrongReturned (X 4) ∧
    1/28 ≤ routineExport X ∧ (1/540:ℝ) ≤ ∫ t in (3:ℝ)..4,X t 2 ∧
    routineFoodU p ≤ 951/200 ∧ routineFoodW p ≤ 951/200 ∧ routineService d X ≤ 9/50 := by
  have hcor := (trajectory_return r d hr hr' hd hd' p c (strong_admitted c hc) X h0 hn hX).1
  have hret := (routine_return r d hr hr' hd hd' p c hc X h0 hn hX).2
  obtain ⟨ht,hu,hw,hg,hend⟩ := routine_output_supplies r d hd' p X hn hX hcor hret
  have hf := (routine_free_export r d hr hr' hd hd' p c hc X h0 hn hX).2
  exact ⟨deterministic_interior_return r d hr hr' hd hd' p c hc X h0 hn hX,hend,ht,hf,hu,hw,hg⟩

end
end FiniteCopyReactor
