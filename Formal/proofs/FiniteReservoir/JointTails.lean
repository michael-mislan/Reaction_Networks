import proofs.FiniteCopyReactor.JointTails
import proofs.FiniteReservoir.JointOutputMarginal
import proofs.FiniteCopyReactor.FinitePoissonInterchange

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped NNReal

theorem free_collection_nested (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     (N : BoxState V M) :
    (residenceKernel V M p hV).poissonized ((750:ℝ≥0)*V)
      (fun X => (residenceMarked V M p hV).poissonized ((3000:ℝ≥0)*V)
        (MarkedKernel.eventIndicator (FreeShortfall V M ((V:ℝ)/1080+1))) X 0) N =
    freeCollectionFailure V M p hV N := by
  unfold MarkedKernel.poissonized
  rw [finite_poisson_tsum _ _ (fun X => (residenceMarked V M p hV).event_summable _ _ X 0)]
  simp only [FiniteKernel.poissonized_scale,freeCollectionFailure]

theorem joint_template_tail (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
    
    (N : BoxState V M) (doseU doseW : ℝ) :
    jointCycle V M p hV
      (fun X => if residenceActive V X.1.1 ∧ X.2 1 ≤ (V:ℝ)/56+1 then 1 else 0)
      N (initialCounters doseU doseW) ≤ Real.exp (-(V:ℝ)/100000) := by
  have he := joint_output_marginal true V M p hV
    (MarkedKernel.eventIndicator {s | residenceActive V s.1.1 ∧ s.2 ≤ (V:ℝ)/56+1}) N doseU doseW
  dsimp [MarkedKernel.eventIndicator] at he
  convert he.le.trans ?_ using 1
  · congr 1
    funext X
    split_ifs <;> rfl
  change (materialKernel V M p hV).poissonized _
    (fun X => (residenceKernel V M p hV).poissonized _
      (fun Y => (templateKernel V M p hV).poissonized _
        (MarkedKernel.eventIndicator {s | residenceActive V s.1.1 ∧ s.2 ≤ (V:ℝ)/56+1}) Y 0) X) N ≤ _
  let P := templateKernel V M p hV
  have hnon (Y) : 0 ≤ P.poissonized ((3000:ℝ≥0)*V)
      (MarkedKernel.eventIndicator {s | residenceActive V s.1.1 ∧ s.2 ≤ (V:ℝ)/56+1}) Y 0 :=
    (marked_bounded_poisson P _ (fun y z => P.event_bounds _ 0 y z) _ Y 0).1
  apply finite_poisson_upper_const
  · intro X
    exact FiniteKernel.poissonized_nonneg _ _ _ hnon X
  · positivity
  · intro X
    exact finite_poisson_upper_const _ _ _ hnon (Real.exp_pos _).le
      (template_collection_probability V M p hV hlarge) _ X

theorem joint_free_tail (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
    
    (N : BoxState V M) (doseU doseW : ℝ) :
    jointCycle V M p hV
      (fun X => if residenceActive V X.1.1 ∧ X.2 0 ≤ (V:ℝ)/1080+1 then 1 else 0)
      N (initialCounters doseU doseW) ≤ freeCollectionError V := by
  have he := joint_output_marginal false V M p hV
    (MarkedKernel.eventIndicator (FreeShortfall V M ((V:ℝ)/1080+1))) N doseU doseW
  dsimp [MarkedKernel.eventIndicator,FreeShortfall] at he
  convert he.le.trans ?_ using 1
  · congr 1
    funext X
    split_ifs <;> rfl
  change (materialKernel V M p hV).poissonized _
    (fun X => (residenceKernel V M p hV).poissonized _
      (fun Y => (residenceMarked V M p hV).poissonized _
        (MarkedKernel.eventIndicator (FreeShortfall V M ((V:ℝ)/1080+1))) Y 0) X) N ≤ _
  simp_rw [free_collection_nested]
  apply finite_poisson_upper_const
  · intro X
    unfold freeCollectionFailure
    apply tsum_nonneg
    intro n
    apply mul_nonneg (poissonWeight_nonneg _ _)
    exact FiniteKernel.poissonized_nonneg _ _ _
      (fun Y => ((residenceMarked V M p hV).event_bounds _ n Y 0).1) X
  · unfold freeCollectionError freeDiscreteError
    positivity
  · exact free_collection_probability V M p hV hlarge

end
end FiniteReservoir
