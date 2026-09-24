import proofs.FiniteReservoir.DeadlineStock

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal
open FiniteCopyReactor (clampedResidence clamped_residence_low clamped_residence_bounds materialExitError)

theorem residence_clamped_step (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) (N : BoxState V M) :
    (residenceKernel V M p hV).step
      (fun X => clampedResidence V (boxCounts X.1)) N ≤
      clampedResidence V (boxCounts N.1)+Real.exp (-(V:ℝ)/10000+9/500) := by
  unfold residenceKernel
  rw [FiniteJumpModel.uniformize_step]
  by_cases h : resourceGood (boxCounts N.1) V ∧ (V:ℝ)/20 < weightedCount (boxCounts N.1)
  · rw [show (residenceModel V M p hV).generator _ N = _ from
      model_inside V M p hV (fun X => resourceGood X V ∧ (V:ℝ)/20 < weightedCount X)
        N h h.1 (clampedResidence V)]
    have hm := material_clamped_step V M p hV N
    unfold materialKernel at hm
    rw [FiniteJumpModel.uniformize_step] at hm
    rw [show (materialModel V M p hV).generator _ N = _ from
      model_inside V M p hV (fun X => resourceGood X V) N h.1 h.1 (clampedResidence V)] at hm
    exact hm
  · rw [show (residenceModel V M p hV).generator _ N=0 from
      model_outside V M p hV _ N h _]
    simp only [zero_div,add_zero]
    exact le_add_of_nonneg_right (Real.exp_pos _).le

theorem residence_from_clamped (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (t : ℝ≥0) (N : BoxState V M) :
    (residenceKernel V M p hV).poissonized t
      (FiniteKernel.eventIndicator {X | weightedCount (boxCounts X.1) ≤ (V:ℝ)/20}) N ≤
      clampedResidence V (boxCounts N.1)+(t:ℝ)*Real.exp (-(V:ℝ)/10000+9/500) := by
  let R := residenceKernel V M p hV
  let E : Set (BoxState V M) := {X | weightedCount (boxCounts X.1) ≤ (V:ℝ)/20}
  have hi (X) : FiniteKernel.eventIndicator E X ≤ clampedResidence V (boxCounts X.1) := by
    by_cases h : X ∈ E
    · rw [FiniteKernel.eventIndicator,if_pos h,clamped_residence_low V (boxCounts X.1) h]
    · rw [FiniteKernel.eventIndicator,if_neg h]
      exact (clamped_residence_bounds V (boxCounts X.1)).1
  exact (R.poissonized_mono t _ _ (fun X => (FiniteKernel.eventIndicator_bounds E X).1)
    (fun X => (clamped_residence_bounds V (boxCounts X.1)).1) hi N).trans
    (R.poissonized_drift_bound t _ _ (fun X => (clamped_residence_bounds V (boxCounts X.1)).1)
      (residence_clamped_step V M p hV) N)

def collectionResidenceError (V : ℝ) : ℝ :=
  Real.exp (-(3/5000000)*V)+Real.exp (-V/2)+materialExitError V+
    Real.exp (-V/10000)+12000*V*Real.exp (-V/10000+9/500)

/-- Continue the actual deadline state for another5/4 units. No state is reset
to the recovery threshold. The second kernel records lower or material exit. -/
theorem recovery_collection_residence (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) (N : BoxState V M)
    (hstock : (3/250)*(V:ℝ) ≤ weightedCount (boxCounts N.1))
    (hprep : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N.1) ∧
      unitObs side (boxCounts N.1) ≤ (51/50)*(V:ℝ)) :
    (materialKernel V M p hV).poissonized ((8250:ℝ≥0)*V)
      (fun X => (residenceKernel V M p hV).poissonized ((3750:ℝ≥0)*V)
        (FiniteKernel.eventIndicator {Y | weightedCount (boxCounts Y.1) ≤ (V:ℝ)/20}) X) N ≤
      collectionResidenceError V := by
  let P := materialKernel V M p hV
  let R := residenceKernel V M p hV
  let E : Set (BoxState V M) := {Y | weightedCount (boxCounts Y.1) ≤ (V:ℝ)/20}
  have hh := P.poissonized_mono ((8250:ℝ≥0)*V) _ _
    (fun X => (R.poissonized_event_bounds ((3750:ℝ≥0)*V) E X).1)
    (fun X => add_nonneg (clamped_residence_bounds V (boxCounts X.1)).1 (by positivity))
    (residence_from_clamped V M p hV ((3750:ℝ≥0)*V)) N
  rw [P.poissonized_add _ _ _ (fun X => (clamped_residence_bounds V (boxCounts X.1)).1)
    (fun _ => by positivity),P.poissonized_const] at hh
  have hdline := actual_deadline_stock V M p hV N hstock hprep
  have hb := hh.trans (add_le_add hdline le_rfl)
  norm_num only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat] at hb
  unfold collectionResidenceError deadlineStockError at *
  convert hb using 1
  ring

end
end FiniteReservoir
