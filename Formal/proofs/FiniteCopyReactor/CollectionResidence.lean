import proofs.FiniteCopyReactor.DeadlineStock

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal

theorem residence_clamped_step (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V) :
    (residenceKernel V r d hV (by linarith) hr' hd hd').step
      (fun X => clampedResidence V (boxCounts X)) N ≤
      clampedResidence V (boxCounts N)+Real.exp (-(V:ℝ)/10000+9/500) := by
  unfold residenceKernel
  rw [FiniteJumpModel.uniformize_step,residence_model_generator]
  split_ifs with h
  · have hm := material_clamped_step V r d hV hr hr' hd hd' N
    unfold materialKernel at hm
    rw [FiniteJumpModel.uniformize_step,material_model_inside V r d hV _ hd N _ h.1] at hm
    exact hm
  · simp only [zero_div,add_zero]
    exact le_add_of_nonneg_right (Real.exp_pos _).le

theorem residence_from_clamped (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (t : ℝ≥0) (N : BoxCounts V) :
    (residenceKernel V r d hV (by linarith) hr' hd hd').poissonized t
      (FiniteKernel.eventIndicator {X | weightedCount (boxCounts X) ≤ (V:ℝ)/20}) N ≤
      clampedResidence V (boxCounts N)+(t:ℝ)*Real.exp (-(V:ℝ)/10000+9/500) := by
  let R := residenceKernel V r d hV (by linarith) hr' hd hd'
  let E : Set (BoxCounts V) := {X | weightedCount (boxCounts X) ≤ (V:ℝ)/20}
  have hi (X) : FiniteKernel.eventIndicator E X ≤ clampedResidence V (boxCounts X) := by
    by_cases h : X ∈ E
    · rw [FiniteKernel.eventIndicator,if_pos h,clamped_residence_low V (boxCounts X) h]
    · rw [FiniteKernel.eventIndicator,if_neg h]
      exact (clamped_residence_bounds V (boxCounts X)).1
  exact (R.poissonized_mono t _ _ (fun X => (FiniteKernel.eventIndicator_bounds E X).1)
    (fun X => (clamped_residence_bounds V (boxCounts X)).1) hi N).trans
    (R.poissonized_drift_bound t _ _ (fun X => (clamped_residence_bounds V (boxCounts X)).1)
      (residence_clamped_step V r d hV hr hr' hd hd') N)

def collectionResidenceError (V : ℝ) : ℝ :=
  Real.exp (-(3/5000000)*V)+Real.exp (-V/2)+materialExitError V+
    Real.exp (-V/10000)+12000*V*Real.exp (-V/10000+9/500)

/-- Continue the actual deadline state for another5/4 units. No state is reset
to the recovery threshold. The second kernel records lower or material exit. -/
theorem recovery_collection_residence (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V)
    (hstock : (3/250)*(V:ℝ) ≤ weightedCount (boxCounts N))
    (hprep : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N) ∧
      unitObs side (boxCounts N) ≤ (51/50)*(V:ℝ)) :
    (materialKernel V r d hV (by linarith) hr' hd hd').poissonized ((8250:ℝ≥0)*V)
      (fun X => (residenceKernel V r d hV (by linarith) hr' hd hd').poissonized ((3750:ℝ≥0)*V)
        (FiniteKernel.eventIndicator {Y | weightedCount (boxCounts Y) ≤ (V:ℝ)/20}) X) N ≤
      collectionResidenceError V := by
  let P := materialKernel V r d hV (by linarith) hr' hd hd'
  let R := residenceKernel V r d hV (by linarith) hr' hd hd'
  let E : Set (BoxCounts V) := {Y | weightedCount (boxCounts Y) ≤ (V:ℝ)/20}
  have hh := P.poissonized_mono ((8250:ℝ≥0)*V) _ _
    (fun X => (R.poissonized_event_bounds ((3750:ℝ≥0)*V) E X).1)
    (fun X => add_nonneg (clamped_residence_bounds V (boxCounts X)).1 (by positivity))
    (residence_from_clamped V r d hV hr hr' hd hd' ((3750:ℝ≥0)*V)) N
  rw [P.poissonized_add _ _ _ (fun X => (clamped_residence_bounds V (boxCounts X)).1)
    (fun _ => by positivity),P.poissonized_const] at hh
  have hdline := actual_deadline_stock V r d hV hr hr' hd hd' N hstock hprep
  have hb := hh.trans (add_le_add hdline le_rfl)
  norm_num only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat] at hb
  unfold collectionResidenceError deadlineStockError at *
  convert hb using 1
  ring

end
end FiniteCopyReactor
