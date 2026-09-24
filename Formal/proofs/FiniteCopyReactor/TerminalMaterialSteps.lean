import proofs.FiniteCopyReactor.TerminalMaterial

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

theorem material_compensated_steps (V : ℕ) (side : Bool) (r d s q : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hd : 0 ≤ d) (hs : |s| ≤ 1/100) (hq : 0 < q) (hq1 : 1 ≤ q)
    (hbound : ∀ N, (materialModel V r d hV hr hd).total N ≤ q) (n : ℕ) (N : BoxCounts V) :
    ((materialModel V r d hV hr hd).uniformize q hq hbound).steps n (materialCompensated V side s) N ≤
      materialCompensated V side ((1-1/q)^n*s) N := by
  let P := (materialModel V r d hV hr hd).uniformize q hq hbound
  have ha : 0 ≤ 1-1/q := sub_nonneg.mpr ((div_le_one hq).mpr hq1)
  have ha1 : 1-1/q ≤ 1 := by
    have h : 0 ≤ 1/q := by positivity
    linarith
  induction n generalizing N with
  | zero => simp only [FiniteKernel.steps,pow_zero,one_mul,le_refl]
  | succ n ih =>
    have hm := P.step_mono ih N
    have hsn : |(1-1/q)^n*s| ≤ 1/100 := by
      rw [abs_mul,abs_of_nonneg (pow_nonneg ha _)]
      have hp : (1-1/q)^n ≤ 1 := pow_le_one₀ ha ha1
      exact (mul_le_mul_of_nonneg_right hp (abs_nonneg s)).trans (by simpa only [one_mul] using hs)
    have hh := material_compensated_step V side r d ((1-1/q)^n*s) q hV hr hd hsn hq hq1 hbound N
    have he : (1-1/q)*((1-1/q)^n*s) = (1-1/q)^(n+1)*s := by rw [pow_succ]; ring
    rw [he] at hh
    exact hm.trans hh

theorem material_test_steps (V : ℕ) (side : Bool) (r d s q : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hd : 0 ≤ d) (hs : |s| ≤ 1/100) (hq : 0 < q) (hq1 : 1 ≤ q)
    (hbound : ∀ N, (materialModel V r d hV hr hd).total N ≤ q) (n : ℕ) (N : BoxCounts V) :
    ((materialModel V r d hV hr hd).uniformize q hq hbound).steps n (materialTest V side s) N ≤
      Real.exp (2*s^2*(V:ℝ))*materialTest V side ((1-1/q)^n*s) N := by
  have h := material_compensated_steps V side r d s q hV hr hd hs hq hq1 hbound n N
  unfold materialCompensated at h
  rw [FiniteKernel.steps_scale] at h
  have he : Real.exp (-2*((1-1/q)^n*s)^2*(V:ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg (sq_nonneg ((1-1/q)^n*s)) hV.le])
  have ht : 0 ≤ materialTest V side ((1-1/q)^n*s) N := by
    unfold materialTest
    split_ifs
    · positivity
    · exact le_rfl
  have hb := h.trans ((mul_le_mul_of_nonneg_right he ht).trans_eq (one_mul _))
  have hh := mul_le_mul_of_nonneg_left hb (Real.exp_pos (2*s^2*(V:ℝ))).le
  have hc : Real.exp (2*s^2*(V:ℝ))*Real.exp (-2*s^2*(V:ℝ)) = 1 := by
    rw [← Real.exp_add,show 2*s^2*(V:ℝ)+ -2*s^2*(V:ℝ)=0 by ring,Real.exp_zero]
  rwa [← mul_assoc,hc,one_mul] at hh

end
end FiniteCopyReactor
