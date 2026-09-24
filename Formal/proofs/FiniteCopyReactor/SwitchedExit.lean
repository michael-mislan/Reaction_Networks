import proofs.FiniteCopyReactor.JointState
import proofs.FiniteCopyReactor.ThreeClockDrift

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal

theorem material_resource_step (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V) :
    (materialKernel V r d hV hr hr' hd hd').step (fun X => resourcePotential V (boxCounts X)) N ≤
      resourcePotential V (boxCounts N)+4*Real.exp (-(V:ℝ)/2000+1/50) := by
  unfold materialKernel
  rw [FiniteJumpModel.uniformize_step]
  have h := div_le_div_of_nonneg_right (material_resource_foster V r d hV hr hr' hd N)
    (show 0 ≤ 3000*(V:ℝ) by positivity)
  have he : 4*resourceSource V/(3000*(V:ℝ))=4*Real.exp (-(V:ℝ)/2000+1/50) := by
    unfold resourceSource
    field_simp
  rw [he] at h
  exact add_le_add le_rfl h

theorem residence_resource_step (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V) :
    (residenceKernel V r d hV (by linarith) hr' hd hd').step (fun X => resourcePotential V (boxCounts X)) N ≤
      resourcePotential V (boxCounts N)+4*Real.exp (-(V:ℝ)/2000+1/50) := by
  rw [residence_step_eq V r d hV hr hr' hd hd']
  split_ifs
  · exact material_resource_step V r d hV (by linarith) hr' hd hd' N
  · exact le_add_of_nonneg_right (by positivity)

theorem switched_material_exit (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V)
    (hprep : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N) ∧ unitObs side (boxCounts N) ≤ (51/50)*(V:ℝ)) :
    switchedState V r d hV (by linarith) hr' hd hd'
      (FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X) V}) N ≤ materialExitError V := by
  let P := materialKernel V r d hV (by linarith) hr' hd hd'
  let Q := residenceKernel V r d hV (by linarith) hr' hd hd'
  let F := fun X : BoxCounts V => resourcePotential V (boxCounts X)
  have hF (X) : 0 ≤ F X := resourcePotential_nonneg V (boxCounts X)
  have hi (X) : FiniteKernel.eventIndicator {Y | ¬resourceGood (boxCounts Y) V} X ≤ F X := by
    by_cases h : resourceGood (boxCounts X) V
    · simp only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,not_true_eq_false,if_false,h]
      exact hF X
    · simpa only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,if_pos h] using resourcePotential_exit V (boxCounts X) h
  have hm := finite_three_clock_mono P Q Q ((8250:ℝ≥0)*V) ((750:ℝ≥0)*V) ((3000:ℝ≥0)*V)
    _ F (fun X => (FiniteKernel.eventIndicator_bounds _ X).1) hF hi N
  have hh := finite_three_clock_drift P Q Q ((8250:ℝ≥0)*V) ((750:ℝ≥0)*V) ((3000:ℝ≥0)*V) F hF
    (4*Real.exp (-(V:ℝ)/2000+1/50)) (4*Real.exp (-(V:ℝ)/2000+1/50)) (4*Real.exp (-(V:ℝ)/2000+1/50))
    (by positivity) (by positivity) (material_resource_step V r d hV (by linarith) hr' hd hd')
    (residence_resource_step V r d hV hr hr' hd hd') (residence_resource_step V r d hV hr hr' hd hd') N
  have hp := prepared_resource_potential (boxCounts N) V hprep
  have hb := hm.trans hh
  norm_num only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat] at hb
  dsimp [F] at hb
  apply hb.trans
  unfold materialExitError
  linarith

end
end FiniteCopyReactor
