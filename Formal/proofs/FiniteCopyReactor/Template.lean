import proofs.FiniteCopyReactor.FreeRow

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators NNReal
set_option maxHeartbeats 30000

def templateMark : CompetitionChannel → ℝ
  | .inl j => ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,2] j
  | .inr _ => 0

theorem template_mark_bounds (j : CompetitionChannel) : 0 ≤ templateMark j ∧ templateMark j ≤ 2 := by
  cases j with
  | inl j => fin_cases j <;> norm_num [templateMark]
  | inr j => norm_num [templateMark]

theorem template_intensity (N : Counts) (V r d : ℝ) :
    (∑ j,competitionRate N V (1/500000000) (1/10) r d j*templateMark j)=
      (N 2:ℝ)+(N 3)+(N 4)+2*(N 5) := by
  norm_num [Fintype.sum_sum_type,competitionRate,templateMark,countRate,Fin.sum_univ_succ]
  ring

theorem template_stock_lower (N : Counts) :
    (5/7)*weightedCount N ≤ (N 2:ℝ)+(N 3)+(N 4)+2*(N 5) := by
  dsimp [weightedCount,weighted]
  nlinarith [Nat.cast_nonneg (α := ℝ) (N 2),Nat.cast_nonneg (α := ℝ) (N 3),Nat.cast_nonneg (α := ℝ) (N 5)]

def templateKernel (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :=
  (residenceModel V r d hV (by linarith) hd).withMarks templateMark
    (3000*(V:ℝ)) (by positivity) (residence_total_bound V r d hV (by linarith) hr' hd hd')

def templateTest (V : ℕ) (N : BoxCounts V) (z : ℝ) : ℝ :=
  if residenceActive V N then Real.exp (-z/1000) else 0

theorem template_step (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V) (z : ℝ) :
    (templateKernel V r d hV hr hr' hd hd').step (templateTest V) N z ≤
      Real.exp (-(33/2800000000:ℝ))*templateTest V N z := by
  let P := templateKernel V r d hV hr hr' hd hd'
  by_cases hc : residenceActive V N
  · have hmark (j) : 0 ≤ P.mark j ∧ P.mark j ≤ 2 := by
      cases j with
      | none => norm_num [P,templateKernel,FiniteJumpModel.withMarks]
      | some j => exact template_mark_bounds j
    have hmean : (1/84000:ℝ) ≤ ∑ j,P.prob N j*P.mark j := by
      simp only [P,templateKernel,FiniteJumpModel.withMarks,Fintype.sum_option,mul_zero,zero_add]
      change _ ≤ ∑ j,(if residenceActive V N then competitionRate (boxCounts N) V
        (1/500000000) (1/10) r d j else 0)/(3000*(V:ℝ))*templateMark j
      simp only [if_pos hc,div_mul_eq_mul_div,← Finset.sum_div,template_intensity]
      apply (le_div_iff₀ (show 0 < 3000*(V:ℝ) by positivity)).mpr
      nlinarith [template_stock_lower (boxCounts N),hc.2]
    have hrow := small_nonnegative_mark_row P P.mark hmark N (1/1000) (1/84000)
      (by norm_num) le_rfl hmean
    norm_num only at hrow
    have hp (j) : templateTest V (P.next N j) (z+P.mark j) ≤
        Real.exp (-z/1000)*Real.exp (-(1/1000)*P.mark j) := by
      unfold templateTest
      split_ifs
      · rw [← Real.exp_add]
        apply le_of_eq
        congr 1
        ring
      · positivity
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hp j) (P.nonneg N j))
    have he : (∑ j,P.prob N j*(Real.exp (-z/1000)*Real.exp (-(1/1000)*P.mark j))) =
        Real.exp (-z/1000)*(∑ j,P.prob N j*Real.exp (-(1/1000)*P.mark j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he] at hh
    have hb := hh.trans (mul_le_mul_of_nonneg_left hrow (Real.exp_pos _).le)
    simpa only [templateTest,if_pos hc,mul_comm] using hb
  · unfold MarkedKernel.step templateKernel
    rw [Fintype.sum_option]
    simp only [FiniteJumpModel.withMarks,residenceModel,if_neg hc,zero_div,zero_mul,
      Finset.sum_const_zero,add_zero]
    simp only [templateTest,if_neg hc,mul_zero,le_refl]

theorem template_collection_probability (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V) :
    (templateKernel V r d hV hr hr' hd hd').poissonized ((3000:ℝ≥0)*V)
      (MarkedKernel.eventIndicator {s | residenceActive V s.1 ∧ s.2 ≤ (V:ℝ)/56+1}) N 0 ≤
      Real.exp (-(V:ℝ)/100000) := by
  let P := templateKernel V r d hV hr hr' hd hd'
  have hi (X) (z : ℝ) : MarkedKernel.eventIndicator {s | residenceActive V s.1 ∧ s.2 ≤ (V:ℝ)/56+1} X z ≤
      Real.exp (((V:ℝ)/56+1)/1000)*templateTest V X z := by
    by_cases h : residenceActive V X ∧ z ≤ (V:ℝ)/56+1
    · simp only [MarkedKernel.eventIndicator,Set.mem_setOf_eq,if_pos h,templateTest,if_pos h.1]
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      linarith [h.2]
    · simp only [MarkedKernel.eventIndicator,Set.mem_setOf_eq,if_neg h]
      unfold templateTest
      split_ifs <;> positivity
  have hh := P.poissonized_event_decay ((3000:ℝ≥0)*V) _ (templateTest V)
    (Real.exp (((V:ℝ)/56+1)/1000)) (Real.exp (-(33/2800000000:ℝ)))
    (Real.exp_pos _).le (Real.exp_pos _).le hi (template_step V r d hV hr hr' hd hd') N 0
  have hz : templateTest V N 0 ≤ 1 := by unfold templateTest; split_ifs <;> norm_num
  have hb := hh.trans (mul_le_mul_of_nonneg_left hz (by positivity))
  rw [mul_one,← Real.exp_add] at hb
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have he := exp_small_quadratic (-(33/2800000000:ℝ)) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left he hV.le
  have hv : (1000000:ℝ) ≤ V := by exact_mod_cast hlarge
  norm_num only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat]
  nlinarith

end
end FiniteCopyReactor
