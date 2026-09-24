import proofs.FiniteCopyReactor.JointOutputMarginal
import proofs.FiniteCopyReactor.FinitePoissonInterchange

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal

theorem finite_poisson_upper_const {α : Type*} [Fintype α] (P : FiniteKernel α)
    (f : α → ℝ) (c : ℝ) (hf : ∀ x, 0 ≤ f x) (hc : 0 ≤ c) (h : ∀ x, f x ≤ c)
    (t : NNReal) (x : α) : P.poissonized t f x ≤ c := by
  have hh := P.poissonized_mono t f (fun _ => c) hf (fun _ => hc) h x
  simpa only [P.poissonized_const] using hh

theorem free_collection_nested (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V) :
    (residenceKernel V r d hV (by linarith) hr' hd hd').poissonized ((750:ℝ≥0)*V)
      (fun X => (residenceMarked V r d hV hr hr' hd hd').poissonized ((3000:ℝ≥0)*V)
        (MarkedKernel.eventIndicator (FreeShortfall V ((V:ℝ)/1080+1))) X 0) N =
    freeCollectionFailure V r d hV hr hr' hd hd' N := by
  unfold MarkedKernel.poissonized
  rw [finite_poisson_tsum _ _ (fun X => (residenceMarked V r d hV hr hr' hd hd').event_summable _ _ X 0)]
  simp only [FiniteKernel.poissonized_scale,freeCollectionFailure]

theorem joint_template_tail (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (N : BoxCounts V) (doseU doseW : ℝ) :
    jointCycle V r d hV (by linarith) hr' hd hd'
      (fun X => if residenceActive V X.1 ∧ X.2 1 ≤ (V:ℝ)/56+1 then 1 else 0)
      N (initialCounters doseU doseW) ≤ Real.exp (-(V:ℝ)/100000) := by
  have he := joint_output_marginal true V r d hV (by linarith) hr' hd hd'
    (MarkedKernel.eventIndicator {s | residenceActive V s.1 ∧ s.2 ≤ (V:ℝ)/56+1}) N doseU doseW
  dsimp [MarkedKernel.eventIndicator] at he
  convert he.le.trans ?_ using 1
  · congr 1
    funext X
    split_ifs <;> rfl
  change (materialKernel V r d hV (by linarith) hr' hd hd').poissonized _
    (fun X => (residenceKernel V r d hV (by linarith) hr' hd hd').poissonized _
      (fun Y => (templateKernel V r d hV hr hr' hd hd').poissonized _
        (MarkedKernel.eventIndicator {s | residenceActive V s.1 ∧ s.2 ≤ (V:ℝ)/56+1}) Y 0) X) N ≤ _
  let P := templateKernel V r d hV hr hr' hd hd'
  have hnon (Y) : 0 ≤ P.poissonized ((3000:ℝ≥0)*V)
      (MarkedKernel.eventIndicator {s | residenceActive V s.1 ∧ s.2 ≤ (V:ℝ)/56+1}) Y 0 :=
    (marked_bounded_poisson P _ (fun y z => P.event_bounds _ 0 y z) _ Y 0).1
  apply finite_poisson_upper_const
  · intro X
    exact FiniteKernel.poissonized_nonneg _ _ _ hnon X
  · positivity
  · intro X
    exact finite_poisson_upper_const _ _ _ hnon (Real.exp_pos _).le
      (template_collection_probability V r d hV hlarge hr hr' hd hd') _ X

theorem joint_free_tail (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (N : BoxCounts V) (doseU doseW : ℝ) :
    jointCycle V r d hV (by linarith) hr' hd hd'
      (fun X => if residenceActive V X.1 ∧ X.2 0 ≤ (V:ℝ)/1080+1 then 1 else 0)
      N (initialCounters doseU doseW) ≤ freeCollectionError V := by
  have he := joint_output_marginal false V r d hV (by linarith) hr' hd hd'
    (MarkedKernel.eventIndicator (FreeShortfall V ((V:ℝ)/1080+1))) N doseU doseW
  dsimp [MarkedKernel.eventIndicator,FreeShortfall] at he
  convert he.le.trans ?_ using 1
  · congr 1
    funext X
    split_ifs <;> rfl
  change (materialKernel V r d hV (by linarith) hr' hd hd').poissonized _
    (fun X => (residenceKernel V r d hV (by linarith) hr' hd hd').poissonized _
      (fun Y => (residenceMarked V r d hV hr hr' hd hd').poissonized _
        (MarkedKernel.eventIndicator (FreeShortfall V ((V:ℝ)/1080+1))) Y 0) X) N ≤ _
  simp_rw [free_collection_nested]
  apply finite_poisson_upper_const
  · intro X
    unfold freeCollectionFailure
    apply tsum_nonneg
    intro n
    apply mul_nonneg (poissonWeight_nonneg _ _)
    exact FiniteKernel.poissonized_nonneg _ _ _
      (fun Y => ((residenceMarked V r d hV hr hr' hd hd').event_bounds _ n Y 0).1) X
  · unfold freeCollectionError freeDiscreteError
    positivity
  · exact free_collection_probability V r d hV hlarge hr hr' hd hd'

end
end FiniteCopyReactor
