import proofs.FiniteReservoir.JointState
import proofs.FiniteCopyReactor.ThreeClockDrift

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped NNReal

theorem material_resource_step (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     (N : BoxState V M) :
    (materialKernel V M p hV).step (fun X => resourcePotential V (boxCounts X.1)) N ≤
      resourcePotential V (boxCounts N.1)+4*Real.exp (-(V:ℝ)/2000+1/50) := by
  unfold materialKernel
  rw [FiniteJumpModel.uniformize_step]
  have h := div_le_div_of_nonneg_right (material_foster V M p hV N)
    (show 0 ≤ 3000*(V:ℝ) by positivity)
  have he : 4*resourceSource V/(3000*(V:ℝ))=4*Real.exp (-(V:ℝ)/2000+1/50) := by
    unfold resourceSource
    field_simp
  rw [he] at h
  exact add_le_add le_rfl h

theorem residence_resource_step (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     (N : BoxState V M) :
    (residenceKernel V M p hV).step (fun X => resourcePotential V (boxCounts X.1)) N ≤
      resourcePotential V (boxCounts N.1)+4*Real.exp (-(V:ℝ)/2000+1/50) := by
  rw [residence_step_eq V M p hV]
  split_ifs
  · exact material_resource_step V M p hV N
  · exact le_add_of_nonneg_right (by positivity)

theorem switched_material_exit (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     (N : BoxState V M)
    (hprep : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N.1) ∧ unitObs side (boxCounts N.1) ≤ (51/50)*(V:ℝ)) :
    switchedState V M p hV
      (FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X.1) V}) N ≤ materialExitError V := by
  let P := materialKernel V M p hV
  let Q := residenceKernel V M p hV
  let F := fun X : BoxState V M => resourcePotential V (boxCounts X.1)
  have hF (X) : 0 ≤ F X := resourcePotential_nonneg V (boxCounts X.1)
  have hi (X) : FiniteKernel.eventIndicator {Y | ¬resourceGood (boxCounts Y.1) V} X ≤ F X := by
    by_cases h : resourceGood (boxCounts X.1) V
    · simp only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,not_true_eq_false,if_false,h]
      exact hF X
    · simpa only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,if_pos h] using resourcePotential_exit V (boxCounts X.1) h
  have hm := finite_three_clock_mono P Q Q ((8250:ℝ≥0)*V) ((750:ℝ≥0)*V) ((3000:ℝ≥0)*V)
    _ F (fun X => (FiniteKernel.eventIndicator_bounds _ X).1) hF hi N
  have hh := finite_three_clock_drift P Q Q ((8250:ℝ≥0)*V) ((750:ℝ≥0)*V) ((3000:ℝ≥0)*V) F hF
    (4*Real.exp (-(V:ℝ)/2000+1/50)) (4*Real.exp (-(V:ℝ)/2000+1/50)) (4*Real.exp (-(V:ℝ)/2000+1/50))
    (by positivity) (by positivity) (material_resource_step V M p hV)
    (residence_resource_step V M p hV) (residence_resource_step V M p hV) N
  have hp := prepared_resource_potential (boxCounts N.1) V hprep
  have hb := hm.trans hh
  norm_num only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat] at hb
  dsimp [F] at hb
  apply hb.trans
  unfold materialExitError
  linarith

end
end FiniteReservoir
