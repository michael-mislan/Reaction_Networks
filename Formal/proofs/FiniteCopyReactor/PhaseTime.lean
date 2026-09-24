import proofs.FiniteCopyReactor.PhaseProbability
import proofs.FiniteCopyReactor.PoissonWindow

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal

/-- A physical window of3/100 time units, with material exits paid separately.
This controls the actual free-X count, not merely weighted catalytic stock. -/
theorem short_window_free_probability (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (N : BoxCounts V) (hstock : (V:ℝ)/20 ≤ weightedCount (boxCounts N)) :
    (materialKernel V r d hV (by linarith) hr' hd hd').poissonized ((90:ℝ≥0)*V)
      (FiniteKernel.eventIndicator (LowFree V)) N ≤
      Real.exp (-(V:ℝ)/10000000000)+2*Real.exp (-(V:ℝ)/400) := by
  have hh := poissonized_in_window (materialKernel V r d hV (by linarith) hr' hd hd')
    (LowFree V) N ((90:ℝ≥0)*V) (89*V) (91*V) (Real.exp (-(V:ℝ)/10000000000))
    (199/200) (201/200) (Real.exp_pos _).le (by norm_num) (by norm_num) (by norm_num)
    (fun n hn hn' => phase_discrete_probability V r d hV hr hr' hd hd' n hn hn' N hstock)
  have hlo := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 199/200 by norm_num)
  have hhi := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 201/200 by norm_num)
  norm_num at hlo hhi
  have hml := mul_le_mul_of_nonneg_left hlo hV.le
  have hmh := mul_le_mul_of_nonneg_left hhi hV.le
  have hel : Real.exp (-((89*V:ℕ):ℝ)*Real.log (199/200)+(((90:ℝ≥0)*V:ℝ≥0):ℝ)*((199/200)-1)) ≤
      Real.exp (-(V:ℝ)/400) := by
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have heu : Real.exp (-((91*V:ℕ):ℝ)*Real.log (201/200)+(((90:ℝ≥0)*V:ℝ≥0):ℝ)*((201/200)-1)) ≤
      Real.exp (-(V:ℝ)/400) := by
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  linarith

end
end FiniteCopyReactor
