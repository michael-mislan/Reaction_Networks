import proofs.FiniteCopyReactor.SwitchedExit

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal

theorem switched_stock_exit (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V)
    (hstock : (3/250)*(V:ℝ) ≤ weightedCount (boxCounts N))
    (hprep : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N) ∧ unitObs side (boxCounts N) ≤ (51/50)*(V:ℝ)) :
    switchedState V r d hV (by linarith) hr' hd hd'
      (FiniteKernel.eventIndicator {X | weightedCount (boxCounts X) ≤ (V:ℝ)/20}) N ≤ collectionResidenceError V := by
  let P := materialKernel V r d hV (by linarith) hr' hd hd'
  let Q := residenceKernel V r d hV (by linarith) hr' hd hd'
  let E : Set (BoxCounts V) := {X | weightedCount (boxCounts X) ≤ (V:ℝ)/20}
  let F := fun X : BoxCounts V => clampedResidence V (boxCounts X)
  let b := Real.exp (-(V:ℝ)/10000+9/500)
  have hF (X) : 0 ≤ F X := (clamped_residence_bounds V (boxCounts X)).1
  have hi (X) : FiniteKernel.eventIndicator E X ≤ F X := by
    by_cases h : X ∈ E
    · rw [FiniteKernel.eventIndicator,if_pos h,show F X=1 from clamped_residence_low V (boxCounts X) h]
    · rw [FiniteKernel.eventIndicator,if_neg h]
      exact hF X
  have hinner (X) : Q.poissonized ((750:ℝ≥0)*V)
      (fun Y => Q.poissonized ((3000:ℝ≥0)*V) (FiniteKernel.eventIndicator E) Y) X ≤
      F X+(3750*(V:ℝ))*b := by
    have hm := Q.poissonized_mono ((750:ℝ≥0)*V) _ _
      (fun Y => (Q.poissonized_event_bounds _ E Y).1) (Q.poissonized_nonneg _ F hF)
      (Q.poissonized_mono ((3000:ℝ≥0)*V) _ F (fun Y => (FiniteKernel.eventIndicator_bounds E Y).1) hF hi) X
    have hdri := finite_two_clock_drift Q Q ((750:ℝ≥0)*V) ((3000:ℝ≥0)*V) F hF b b
      (Real.exp_pos _).le (residence_clamped_step V r d hV hr hr' hd hd')
      (residence_clamped_step V r d hV hr hr' hd hd') X
    have hb := hm.trans hdri
    norm_num only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat] at hb
    convert hb using 1
    ring
  have hm := P.poissonized_mono ((8250:ℝ≥0)*V) _ (fun X => F X+(3750*(V:ℝ))*b)
    (Q.poissonized_nonneg _ _ (fun Y => (Q.poissonized_event_bounds _ E Y).1))
    (fun X => add_nonneg (hF X) (by dsimp [b]; positivity)) hinner N
  rw [P.poissonized_add _ F (fun _ => (3750*(V:ℝ))*b) hF (fun _ => by dsimp [b]; positivity),P.poissonized_const] at hm
  have hdline := actual_deadline_stock V r d hV hr hr' hd hd' N hstock hprep
  have hb := hm.trans (add_le_add hdline le_rfl)
  change _ ≤ collectionResidenceError V
  unfold collectionResidenceError deadlineStockError at *
  dsimp [b] at hb
  convert hb using 1
  ring

end
end FiniteCopyReactor
