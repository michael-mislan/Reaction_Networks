import proofs.FiniteReservoir.ClampedResidence
import proofs.FiniteReservoir.RecoveryProbability
import proofs.FiniteReservoir.MaterialControl
import proofs.FiniteCopyReactor.StoppedComparison
import proofs.FiniteCopyReactor.EntryProbability
import proofs.FiniteCopyReactor.MaterialPulse

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal
open FiniteCopyReactor (clampedResidence materialExitError prepared_resource_potential)

theorem routine_entry_step (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (f : BoxState V M → ℝ) (N : BoxState V M) :
    (entryKernel V M p hV).step f N =
      if entryActive V ((3/50)*(V:ℝ)) N.1 then
        (materialKernel V M p hV).step f N else f N := by
  unfold entryKernel materialKernel
  rw [FiniteJumpModel.uniformize_step,FiniteJumpModel.uniformize_step]
  by_cases h : entryActive V ((3/50)*(V:ℝ)) N.1
  · rw [if_pos h]
    change resourceGood (boxCounts N.1) V ∧ weightedCount (boxCounts N.1)<(3/50)*(V:ℝ) at h
    simp only [FiniteJumpModel.generator,entryModel,materialModel,model,if_pos h,if_pos h.1]
  · rw [if_neg h]
    change ¬(resourceGood (boxCounts N.1) V ∧ weightedCount (boxCounts N.1)<(3/50)*(V:ℝ)) at h
    simp only [FiniteJumpModel.generator,entryModel,model,if_neg h,zero_mul,
      Finset.sum_const_zero,zero_div,add_zero]

theorem material_clamped_step (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) (N : BoxState V M) :
    (materialKernel V M p hV).step
      (fun X => clampedResidence V (boxCounts X.1)) N ≤
      clampedResidence V (boxCounts N.1)+Real.exp (-(V:ℝ)/10000+9/500) := by
  have hg : (materialModel V M p hV).generator
      (fun X => clampedResidence V (boxCounts X.1)) N ≤
      (3000*(V:ℝ))*Real.exp (-(V:ℝ)/10000+9/500) := by
    by_cases hc : resourceGood (boxCounts N.1) V
    · rw [show (materialModel V M p hV).generator _ N = _ from
        model_inside V M p hV (fun X => resourceGood X V) N hc hc (clampedResidence V)]
      exact clamped_residence_generator (boxCounts N.1) V p.release _ _ hV p.release_lower p.release_upper (parameters_box p N.2) hc
    · rw [show (materialModel V M p hV).generator _ N=0 from
        model_outside V M p hV _ N hc _]
      positivity
  unfold materialKernel
  rw [FiniteJumpModel.uniformize_step]
  have hdv := div_le_div_of_nonneg_right hg (show 0 ≤ 3000*(V:ℝ) by positivity)
  have he : (3000*(V:ℝ)*Real.exp (-(V:ℝ)/10000+9/500))/(3000*(V:ℝ)) =
      Real.exp (-(V:ℝ)/10000+9/500) := by field_simp
  rw [he] at hdv
  exact add_le_add le_rfl hdv

theorem entry_material_exit (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) (N : BoxState V M)
    (hprep : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N.1) ∧
      unitObs side (boxCounts N.1) ≤ (51/50)*(V:ℝ)) :
    (entryKernel V M p hV).poissonized ((8250:ℝ≥0)*V)
      (FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X.1) V}) N ≤ materialExitError V := by
  let Q := entryKernel V M p hV
  let F := fun X : BoxState V M => resourcePotential V (boxCounts X.1)
  have hs (X) : Q.step F X ≤ F X+4*resourceSource V/(3000*(V:ℝ)) := by
    rw [routine_entry_step]
    split_ifs
    · exact (materialModel V M p hV).uniformize_drift
        (3000*(V:ℝ)) (by positivity) (material_total V M p hV) F
        (4*resourceSource V) (material_foster V M p hV) X
    · exact le_add_of_nonneg_right (by unfold resourceSource; positivity)
  have hi (X) : FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X.1) V} X ≤ F X := by
    by_cases hx : resourceGood (boxCounts X.1) V
    · simp only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,not_true_eq_false,hx,if_false]
      exact resourcePotential_nonneg V (boxCounts X.1)
    · simpa only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,hx,not_false_eq_true,if_true]
        using resourcePotential_exit V (boxCounts X.1) hx
  have hh := Q.poissonized_mono ((8250:ℝ≥0)*V) _ F
    (fun X => by unfold FiniteKernel.eventIndicator; split_ifs <;> norm_num)
    (fun X => resourcePotential_nonneg V (boxCounts X.1)) hi N
  have hg := Q.poissonized_drift_bound ((8250:ℝ≥0)*V) F (4*resourceSource V/(3000*(V:ℝ)))
    (fun X => resourcePotential_nonneg V (boxCounts X.1)) hs N
  have he : (((8250:ℝ≥0)*V:ℝ≥0):ℝ)*(4*resourceSource V/(3000*(V:ℝ))) = 11*resourceSource V := by
    push_cast
    field_simp
    ring
  rw [he] at hg
  have hp := prepared_resource_potential (boxCounts N.1) V hprep
  have hb := hh.trans hg
  dsimp [F] at hb
  unfold materialExitError resourceSource at *
  nlinarith [Real.exp_pos (-(V:ℝ)/2000+1/50),Nat.cast_nonneg (α := ℝ) V]

end
end FiniteReservoir
