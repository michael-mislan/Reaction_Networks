import proofs.FiniteCopyReactor.ClampedResidence
import proofs.FiniteCopyReactor.StoppedComparison
import proofs.FiniteCopyReactor.EntryProbability
import proofs.FiniteCopyReactor.MaterialPulse

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal

theorem routine_entry_step (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : BoxCounts V → ℝ) (N : BoxCounts V) :
    (routineEntryKernel V r d hV hr hr' hd hd').step f N =
      if entryActive V ((3/50)*(V:ℝ)) N then
        (materialKernel V r d hV (by linarith) hr' hd hd').step f N else f N := by
  unfold routineEntryKernel materialKernel
  rw [FiniteJumpModel.uniformize_step,FiniteJumpModel.uniformize_step]
  by_cases h : entryActive V ((3/50)*(V:ℝ)) N
  · simp only [if_pos h,FiniteJumpModel.generator,competitionEntryModel,materialModel,if_pos h.1]
  · simp only [if_neg h,FiniteJumpModel.generator,competitionEntryModel,zero_mul,
      Finset.sum_const_zero,zero_div,add_zero]

theorem material_clamped_step (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V) :
    (materialKernel V r d hV (by linarith) hr' hd hd').step
      (fun X => clampedResidence V (boxCounts X)) N ≤
      clampedResidence V (boxCounts N)+Real.exp (-(V:ℝ)/10000+9/500) := by
  have hg : (materialModel V r d hV (by linarith) hd).generator
      (fun X => clampedResidence V (boxCounts X)) N ≤
      (3000*(V:ℝ))*Real.exp (-(V:ℝ)/10000+9/500) := by
    by_cases hc : resourceGood (boxCounts N) V
    · rw [material_model_inside V r d hV _ hd N _ hc]
      exact clamped_residence_generator (boxCounts N) V r d hV hr hr' hd hd' hc
    · rw [material_model_outside V r d hV _ hd N _ hc]
      positivity
  have hh := (materialModel V r d hV (by linarith) hd).uniformize_drift
    (3000*(V:ℝ)) (by positivity) (material_total_bound V r d hV (by linarith) hr' hd hd')
    (fun X => clampedResidence V (boxCounts X))
    ((3000*(V:ℝ))*Real.exp (-(V:ℝ)/10000+9/500))
  unfold materialKernel
  rw [FiniteJumpModel.uniformize_step]
  have hdv := div_le_div_of_nonneg_right hg (show 0 ≤ 3000*(V:ℝ) by positivity)
  have he : (3000*(V:ℝ)*Real.exp (-(V:ℝ)/10000+9/500))/(3000*(V:ℝ)) =
      Real.exp (-(V:ℝ)/10000+9/500) := by field_simp
  rw [he] at hdv
  exact add_le_add le_rfl hdv

theorem entry_material_exit (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V)
    (hprep : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N) ∧
      unitObs side (boxCounts N) ≤ (51/50)*(V:ℝ)) :
    (routineEntryKernel V r d hV hr hr' hd hd').poissonized ((8250:ℝ≥0)*V)
      (FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X) V}) N ≤ materialExitError V := by
  let Q := routineEntryKernel V r d hV hr hr' hd hd'
  let F := fun X : BoxCounts V => resourcePotential V (boxCounts X)
  have hs (X) : Q.step F X ≤ F X+4*resourceSource V/(3000*(V:ℝ)) := by
    rw [routine_entry_step]
    split_ifs
    · exact (materialModel V r d hV (by linarith) hd).uniformize_drift
        (3000*(V:ℝ)) (by positivity) (material_total_bound V r d hV (by linarith) hr' hd hd') F
        (4*resourceSource V) (material_resource_foster V r d hV (by linarith) hr' hd) X
    · exact le_add_of_nonneg_right (by unfold resourceSource; positivity)
  have hi (X) : FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X) V} X ≤ F X := by
    by_cases hx : resourceGood (boxCounts X) V
    · simp only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,not_true_eq_false,hx,if_false]
      exact resourcePotential_nonneg V (boxCounts X)
    · simpa only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,hx,not_false_eq_true,if_true]
        using resourcePotential_exit V (boxCounts X) hx
  have hh := Q.poissonized_mono ((8250:ℝ≥0)*V) _ F
    (fun X => by unfold FiniteKernel.eventIndicator; split_ifs <;> norm_num)
    (fun X => resourcePotential_nonneg V (boxCounts X)) hi N
  have hg := Q.poissonized_drift_bound ((8250:ℝ≥0)*V) F (4*resourceSource V/(3000*(V:ℝ)))
    (fun X => resourcePotential_nonneg V (boxCounts X)) hs N
  have he : (((8250:ℝ≥0)*V:ℝ≥0):ℝ)*(4*resourceSource V/(3000*(V:ℝ))) = 11*resourceSource V := by
    push_cast
    field_simp
    ring
  rw [he] at hg
  have hp := prepared_resource_potential (boxCounts N) V hprep
  have hb := hh.trans hg
  dsimp [F] at hb
  unfold materialExitError resourceSource at *
  nlinarith [Real.exp_pos (-(V:ℝ)/2000+1/50),Nat.cast_nonneg (α := ℝ) V]

end
end FiniteCopyReactor
