import proofs.FiniteReservoir.CountSource

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding
open scoped BigOperators

def variance (N : Counts) (V r alpha beta : ℝ) : ℝ :=
  ∑ j, internalRate N V r alpha beta j*(weightedJump (competitionBase j))^2

theorem variance_expansion (N : Counts) (V r alpha beta : ℝ) :
    variance N V r alpha beta=countVariance N V (1/500000000) (1/10) r+
      alpha*(N 2)+beta*(N 0)*(N 1)/V := by
  simp only [variance,Fintype.sum_sum_type]
  change countVariance N V (1/500000000) (1/10) r+_= _
  simp [Fin.sum_univ_succ,internalRate_forward,internalRate_reverse,competitionBase,drivenBase,weightedJump]
  ring

theorem stock_variance (N : Counts) (V r alpha beta : ℝ) (hV : 0 < V)
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hbox : RateBox alpha beta)
    (hu : (N 0:ℝ)/V ≤ 11/10) (hw : (N 1:ℝ)/V ≤ 11/10)
    (hx : (N 2:ℝ)/V ≤ 11/10) :
    variance N V r alpha beta ≤ 6*weightedCount N+V/100000000 := by
  have huw : ((N 0:ℝ)/V)*((N 1:ℝ)/V) ≤ 121/100 := by
    have h := mul_le_mul hu hw (by positivity : 0 ≤ (N 1:ℝ)/V)
      (by norm_num : (0:ℝ) ≤ 11/10)
    nlinarith
  have hb := actual_count_variance_bound N V (1/500000000) (1/10) r hV
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hy := weightedCount_nonneg N
  have hxw := freeCount_le_weighted N
  have hdr : alpha*(N 2:ℝ) ≤ weightedCount N := by
    have h := mul_le_mul hbox.alpha_upper hxw (Nat.cast_nonneg _)
      (by norm_num : (0:ℝ) ≤ 1/25)
    linarith
  have hi := mul_le_mul hbox.beta_upper huw
    (by positivity : 0 ≤ ((N 0:ℝ)/V)*((N 1:ℝ)/V))
    (by norm_num : (0:ℝ) ≤ 1/200000000000)
  have hi' := mul_le_mul_of_nonneg_right hi hV.le
  have he : beta*((N 0:ℝ)/V*((N 1:ℝ)/V))*V=beta*(N 0)*(N 1)/V := by
    field_simp
  rw [he] at hi'
  rw [variance_expansion]
  linarith

end
end FiniteReservoir
