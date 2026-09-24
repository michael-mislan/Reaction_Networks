import proofs.FiniteReservoir.FreeMarked
import proofs.FiniteCopyReactor.CountRow

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped BigOperators

theorem free_mark_bounds (j : CompetitionChannel) : 0 ≤ freeWashoutMark j ∧ freeWashoutMark j ≤ 1 := by
  cases j with
  | inl j => dsimp [freeWashoutMark]; split_ifs <;> norm_num
  | inr j => norm_num [freeWashoutMark]

theorem residence_mark_bounds (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     (j : Option CompetitionChannel) :
    0 ≤ (residenceMarked V M p hV).mark j ∧
      (residenceMarked V M p hV).mark j ≤ 1 := by
  cases j with
  | none => norm_num [residenceMarked,FiniteJumpModel.withMarks]
  | some j => exact free_mark_bounds j

theorem residence_mark_mean (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (N : BoxState V M) (hc : residenceActive V N.1) :
    (∑ j,(residenceMarked V M p hV).prob N j*
      (residenceMarked V M p hV).mark j)=(boxCounts N.1 2:ℝ)/(3000*(V:ℝ)) := by
  simp only [Fintype.sum_option,residenceMarked,FiniteJumpModel.withMarks,mul_zero,zero_add]
  change resourceGood (boxCounts N.1) V ∧ (V:ℝ)/20 < weightedCount (boxCounts N.1) at hc
  simp only [residenceModel,model,if_pos hc,rate_binding,div_mul_eq_mul_div,
    ← Finset.sum_div,boxState,free_washout_intensity]


theorem corrected_free_row (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (N : BoxState V M) (hc : residenceActive V N.1) :
    (∑ j,(residenceMarked V M p hV).prob N j*
      Real.exp (-(1/1000)*((residenceMarked V M p hV).mark j+
        (1/3000000)*FiniteKernel.eventIndicator (LowFreeActive V M) N))) ≤
      Real.exp (-(33/100000000000:ℝ)) := by
  let P := residenceMarked V M p hV
  let b := FiniteKernel.eventIndicator (LowFreeActive V M) N
  have hb := FiniteKernel.eventIndicator_bounds (LowFreeActive V M) N
  have hg (j) : 0 ≤ P.mark j+(1/3000000)*b ∧ P.mark j+(1/3000000)*b ≤ 2 := by
    have hm := residence_mark_bounds V M p hV j
    dsimp [P,b] at *
    constructor <;> linarith
  have hmean : (1/3000000:ℝ) ≤ ∑ j,P.prob N j*(P.mark j+(1/3000000)*b) := by
    simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,P.row_sum,one_mul]
    rw [residence_mark_mean V M p hV N hc]
    by_cases hbad : N ∈ LowFreeActive V M
    · have he : b=1 := by simp only [b,FiniteKernel.eventIndicator,if_pos hbad]
      rw [he]
      have hnon : 0 ≤ (boxCounts N.1 2:ℝ)/(3000*(V:ℝ)) := by positivity
      linarith
    · have he : b=0 := by simp only [b,FiniteKernel.eventIndicator,if_neg hbad]
      rw [he,mul_zero,add_zero]
      have hx : (V:ℝ)/1000 < (boxCounts N.1 2:ℝ) := lt_of_not_ge (fun hh => hbad ⟨hc,hh⟩)
      apply (le_div_iff₀ (show 0 < 3000*(V:ℝ) by positivity)).mpr
      linarith
  have hh := small_nonnegative_mark_row P (fun j => P.mark j+(1/3000000)*b) hg N
    (1/1000) (1/3000000) (by norm_num) le_rfl hmean
  norm_num only at hh
  exact hh

end
end FiniteReservoir
