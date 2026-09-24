import proofs.FiniteCopyReactor.StateMarks
import proofs.RandomViability.BindingEntryExponential

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy RandomViability.Binding Classical
open scoped BigOperators

theorem small_nonnegative_mark_row {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (g : β → ℝ) (hg : ∀ j, 0 ≤ g j ∧ g j ≤ 2) (x : α) (s p : ℝ)
    (hs : 0 ≤ s) (hs' : s ≤ 1/1000) (hmean : p ≤ ∑ j,P.prob x j*g j) :
    (∑ j,P.prob x j*Real.exp (-s*g j)) ≤ Real.exp (-(99/100)*s*p) := by
  have hpoint (j) : Real.exp (-s*g j) ≤ 1-(99/100)*s*g j := by
    have ha : |-s*g j| ≤ 9/50 := by
      rw [abs_mul,abs_neg,abs_of_nonneg hs,abs_of_nonneg (hg j).1]
      nlinarith [mul_le_mul hs' (hg j).2 (hg j).1 (by norm_num : (0:ℝ) ≤ 1/1000)]
    have hsq : (g j)^2 ≤ 2*g j := by nlinarith [(hg j).1,(hg j).2]
    have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg s)
    have hss : s^2*g j ≤ (1/1000)*s*g j := by
      exact mul_le_mul_of_nonneg_right (by nlinarith : s^2 ≤ (1/1000)*s) (hg j).1
    nlinarith [exp_small_quadratic (-s*g j) ha,mul_nonneg hs (hg j).1]
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint j) (P.nonneg x j))
  have he : (∑ j,P.prob x j*(1-(99/100)*s*g j)) =
      1-(99/100)*s*(∑ j,P.prob x j*g j) := by
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib]
    rw [P.row_sum,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at hh
  have hm := mul_le_mul_of_nonneg_left hmean (show 0 ≤ (99/100)*s by positivity)
  exact hh.trans ((by linarith : 1-(99/100)*s*(∑ j,P.prob x j*g j) ≤ 1-(99/100)*s*p).trans
    (by linarith [Real.add_one_le_exp (-(99/100)*s*p)]))

end
end FiniteCopyReactor
