import proofs.FiniteCopyReactor.MaterialModel

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators

def materialTest (V : ℕ) (side : Bool) (s : ℝ) (N : BoxCounts V) : ℝ :=
  if resourceGood (boxCounts N) V then Real.exp (s*(unitObs side (boxCounts N)-(V:ℝ))) else 0

def materialCompensated (V : ℕ) (side : Bool) (s : ℝ) (N : BoxCounts V) : ℝ :=
  Real.exp (-2*s^2*(V:ℝ))*materialTest V side s N

theorem material_test_generator (V : ℕ) (side : Bool) (r d s : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hd : 0 ≤ d) (hs : |s| ≤ 1/100) (N : BoxCounts V)
    (hcor : resourceGood (boxCounts N) V) :
    (materialModel V r d hV hr hd).generator (materialTest V side s) N ≤
      Real.exp (s*(unitObs side (boxCounts N)-(V:ℝ))) *
        (-s*(unitObs side (boxCounts N)-(V:ℝ))+2*s^2*(V:ℝ)) := by
  have hkill : (materialModel V r d hV hr hd).generator (materialTest V side s) N ≤
      (materialModel V r d hV hr hd).generator
        (fun X => Real.exp (s*(unitObs side (boxCounts X)-(V:ℝ)))) N := by
    unfold FiniteJumpModel.generator
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ ((materialModel V r d hV hr hd).nonneg N j)
    simp only [materialTest,if_pos hcor]
    apply sub_le_sub_right
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  rw [material_model_inside V r d hV hr hd N
    (fun X => Real.exp (s*(unitObs side X-(V:ℝ)))) hcor] at hkill
  have he := competition_resource_generator (boxCounts N) V (1/500000000) (1/10) r d
    (fun u w => Real.exp (s*((if side then u else w)-(V:ℝ))))
  change competitionGenerator (boxCounts N) V (1/500000000) (1/10) r d
      (fun X => Real.exp (s*(unitObs side X-(V:ℝ)))) = _ at he
  rw [he] at hkill
  change (materialModel V r d hV hr hd).generator (materialTest V side s) N ≤
    literalGenerator (boxCounts N) V (1/500000000) (1/10) r
      (fun X => Real.exp (s*(unitObs side X-(V:ℝ)))) at hkill
  rw [unit_exponential_generator side (boxCounts N) V (1/500000000) (1/10) r s V] at hkill
  have ht := unit_exponential_tilt side (boxCounts N) V (1/500000000) (1/10) r s hV
    (by norm_num) (by norm_num) hr hs
  have hu : unitObs side (boxCounts N) ≤ (11/10)*(V:ℝ) := by
    cases side
    · exact hcor.2.2.2
    · exact hcor.2.1
  have hsq := mul_le_mul_of_nonneg_left hu (sq_nonneg s)
  apply hkill.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  nlinarith [mul_nonneg (sq_nonneg s) hV.le]

theorem material_step_transform (V : ℕ) (side : Bool) (r d s q : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hd : 0 ≤ d) (hs : |s| ≤ 1/100) (hq : 0 < q)
    (hbound : ∀ N, (materialModel V r d hV hr hd).total N ≤ q) (N : BoxCounts V) :
    ((materialModel V r d hV hr hd).uniformize q hq hbound).step (materialTest V side s) N ≤
      Real.exp (2*s^2*(V:ℝ)/q)*materialTest V side ((1-1/q)*s) N := by
  rw [FiniteJumpModel.uniformize_step]
  by_cases hcor : resourceGood (boxCounts N) V
  · have hg := div_le_div_of_nonneg_right (material_test_generator V side r d s hV hr hd hs N hcor) hq.le
    simp only [materialTest,if_pos hcor]
    calc
      _ ≤ Real.exp (s*(unitObs side (boxCounts N)-(V:ℝ))) +
          Real.exp (s*(unitObs side (boxCounts N)-(V:ℝ))) *
            (-s*(unitObs side (boxCounts N)-(V:ℝ))+2*s^2*(V:ℝ))/q := add_le_add le_rfl hg
      _ = Real.exp (s*(unitObs side (boxCounts N)-(V:ℝ))) *
          (1+(-s*(unitObs side (boxCounts N)-(V:ℝ))+2*s^2*(V:ℝ))/q) := by ring
      _ ≤ Real.exp (s*(unitObs side (boxCounts N)-(V:ℝ))) *
          Real.exp ((-s*(unitObs side (boxCounts N)-(V:ℝ))+2*s^2*(V:ℝ))/q) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp ((-s*(unitObs side (boxCounts N)-(V:ℝ))+2*s^2*(V:ℝ))/q)]
      _ = _ := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
  · rw [material_model_outside V r d hV hr hd N _ hcor]
    simp only [materialTest,if_neg hcor,zero_div,add_zero,mul_zero,le_refl]

theorem material_compensated_step (V : ℕ) (side : Bool) (r d s q : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hd : 0 ≤ d) (hs : |s| ≤ 1/100) (hq : 0 < q) (hq1 : 1 ≤ q)
    (hbound : ∀ N, (materialModel V r d hV hr hd).total N ≤ q) (N : BoxCounts V) :
    ((materialModel V r d hV hr hd).uniformize q hq hbound).step (materialCompensated V side s) N ≤
      materialCompensated V side ((1-1/q)*s) N := by
  unfold materialCompensated
  rw [FiniteKernel.step_scale]
  have h := mul_le_mul_of_nonneg_left (material_step_transform V side r d s q hV hr hd hs hq hbound N)
    (Real.exp_pos (-2*s^2*(V:ℝ))).le
  apply h.trans
  rw [← mul_assoc,← Real.exp_add]
  have ht : 0 ≤ materialTest V side ((1-1/q)*s) N := by
    unfold materialTest
    split_ifs
    · positivity
    · exact le_rfl
  apply mul_le_mul_of_nonneg_right _ ht
  apply Real.exp_le_exp.mpr
  have hi : 0 < 1/q := by positivity
  have hi1 : 1/q ≤ 1 := (div_le_one hq).mpr hq1
  have hb : (1-1/q)^2 ≤ 1-1/q := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*s^2*(V:ℝ) by positivity)
  convert neg_le_neg hm using 1 <;> ring

end
end FiniteCopyReactor
