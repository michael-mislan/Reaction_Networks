import proofs.FiniteCopyReactor.Source
import proofs.RandomViability.BindingCountExponential

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding

/-- A variance estimate valid at C2 stock levels, rather than C0's tiny-stock guard. -/
theorem stock_variance (N : Counts) (V r d : ℝ) (hV : 0 < V)
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd' : d ≤ 1/25)
    (hu : (N 0:ℝ)/V ≤ 11/10) (hw : (N 1:ℝ)/V ≤ 11/10)
    (hx : (N 2:ℝ)/V ≤ 11/10) :
    competitionVariance N V (1/500000000) (1/10) r d ≤
      6*weightedCount N+V/100000000 := by
  have huw : ((N 0:ℝ)/V)*((N 1:ℝ)/V) ≤ 121/100 := by
    have h := mul_le_mul hu hw (by positivity : 0 ≤ (N 1:ℝ)/V)
      (by norm_num : (0:ℝ) ≤ 11/10)
    nlinarith
  have hb := actual_count_variance_bound N V (1/500000000) (1/10) r hV
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hy := weightedCount_nonneg N
  have hxw := freeCount_le_weighted N
  have hdr : d*(N 2:ℝ) ≤ weightedCount N := by
    have h := mul_le_mul hd' hxw (Nat.cast_nonneg _) (by norm_num : (0:ℝ) ≤ 1/25)
    linarith
  have hi := mul_le_mul hd' huw (by positivity : 0 ≤ ((N 0:ℝ)/V)*((N 1:ℝ)/V))
    (by norm_num : (0:ℝ) ≤ 1/25)
  have hi' := mul_le_mul_of_nonneg_right hi (show 0 ≤ V/8000000000 by positivity)
  have he : d*((N 0:ℝ)/V*((N 1:ℝ)/V))*(V/8000000000) =
      d*(1/500000000)/16*(N 0)*(N 1)/V := by
    field_simp
    ring
  rw [he] at hi'
  rw [competition_variance_expansion]
  linarith

end
end FiniteCopyReactor
