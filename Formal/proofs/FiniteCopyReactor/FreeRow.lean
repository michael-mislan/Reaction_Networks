import proofs.FiniteCopyReactor.FreeMarked
import proofs.FiniteCopyReactor.CountRow

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators

theorem free_mark_bounds (j : CompetitionChannel) : 0 ≤ freeWashoutMark j ∧ freeWashoutMark j ≤ 1 := by
  cases j with
  | inl j => dsimp [freeWashoutMark]; split_ifs <;> norm_num
  | inr j => norm_num [freeWashoutMark]

theorem residence_mark_bounds (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (j : Option CompetitionChannel) :
    0 ≤ (residenceMarked V r d hV hr hr' hd hd').mark j ∧
      (residenceMarked V r d hV hr hr' hd hd').mark j ≤ 1 := by
  cases j with
  | none => norm_num [residenceMarked,FiniteJumpModel.withMarks]
  | some j => exact free_mark_bounds j

theorem residence_mark_mean (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (N : BoxCounts V) (hc : residenceActive V N) :
    (∑ j,(residenceMarked V r d hV hr hr' hd hd').prob N j*
      (residenceMarked V r d hV hr hr' hd hd').mark j)=(boxCounts N 2:ℝ)/(3000*(V:ℝ)) := by
  simp only [Fintype.sum_option,residenceMarked,FiniteJumpModel.withMarks,mul_zero,zero_add]
  change (∑ j, (if residenceActive V N then competitionRate (boxCounts N) V
    (1/500000000) (1/10) r d j else 0)/(3000*(V:ℝ))*freeWashoutMark j)=_
  simp only [if_pos hc,div_mul_eq_mul_div,← Finset.sum_div,free_washout_intensity]

theorem corrected_free_row (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (N : BoxCounts V) (hc : residenceActive V N) :
    (∑ j,(residenceMarked V r d hV hr hr' hd hd').prob N j*
      Real.exp (-(1/1000)*((residenceMarked V r d hV hr hr' hd hd').mark j+
        (1/3000000)*FiniteKernel.eventIndicator (LowFreeActive V) N))) ≤
      Real.exp (-(33/100000000000:ℝ)) := by
  let P := residenceMarked V r d hV hr hr' hd hd'
  let b := FiniteKernel.eventIndicator (LowFreeActive V) N
  have hb := FiniteKernel.eventIndicator_bounds (LowFreeActive V) N
  have hg (j) : 0 ≤ P.mark j+(1/3000000)*b ∧ P.mark j+(1/3000000)*b ≤ 2 := by
    have hm := residence_mark_bounds V r d hV hr hr' hd hd' j
    dsimp [P,b] at *
    constructor <;> linarith
  have hmean : (1/3000000:ℝ) ≤ ∑ j,P.prob N j*(P.mark j+(1/3000000)*b) := by
    simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,P.row_sum,one_mul]
    rw [residence_mark_mean V r d hV hr hr' hd hd' N hc]
    by_cases hbad : N ∈ LowFreeActive V
    · have he : b=1 := by simp only [b,FiniteKernel.eventIndicator,if_pos hbad]
      rw [he]
      have hnon : 0 ≤ (boxCounts N 2:ℝ)/(3000*(V:ℝ)) := by positivity
      linarith
    · have he : b=0 := by simp only [b,FiniteKernel.eventIndicator,if_neg hbad]
      rw [he,mul_zero,add_zero]
      have hx : (V:ℝ)/1000 < (boxCounts N 2:ℝ) := lt_of_not_ge (fun hh => hbad ⟨hc,hh⟩)
      apply (le_div_iff₀ (show 0 < 3000*(V:ℝ) by positivity)).mpr
      linarith
  have hh := small_nonnegative_mark_row P (fun j => P.mark j+(1/3000000)*b) hg N
    (1/1000) (1/3000000) (by norm_num) le_rfl hmean
  norm_num only at hh
  exact hh

end
end FiniteCopyReactor
