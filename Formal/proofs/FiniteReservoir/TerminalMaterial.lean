import proofs.FiniteReservoir.MaterialControl

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators

def materialTest (V M : ℕ) (side : Bool) (s : ℝ) (N : BoxState V M) : ℝ :=
  if resourceGood (boxCounts N.1) V then Real.exp (s*(unitObs side (boxCounts N.1)-(V:ℝ))) else 0

def materialCompensated (V M : ℕ) (side : Bool) (s : ℝ) (N : BoxState V M) : ℝ :=
  Real.exp (-2*s^2*(V:ℝ))*materialTest V M side s N

theorem material_test_generator (V M : ℕ) (side : Bool) (p : Parameters M) (s : ℝ) (hV : 0 < (V:ℝ)) (hs : |s| ≤ 1/100) (N : BoxState V M)
    (hcor : resourceGood (boxCounts N.1) V) :
    (materialModel V M p hV).generator (materialTest V M side s) N ≤
      Real.exp (s*(unitObs side (boxCounts N.1)-(V:ℝ))) *
        (-s*(unitObs side (boxCounts N.1)-(V:ℝ))+2*s^2*(V:ℝ)) := by
  have hkill : (materialModel V M p hV).generator (materialTest V M side s) N ≤
      (materialModel V M p hV).generator
        (fun X => Real.exp (s*(unitObs side (boxCounts X.1)-(V:ℝ)))) N := by
    unfold FiniteJumpModel.generator
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ ((materialModel V M p hV).nonneg N j)
    simp only [materialTest,if_pos hcor]
    apply sub_le_sub_right
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  rw [show (materialModel V M p hV).generator
      (fun X => Real.exp (s*(unitObs side (boxCounts X.1)-(V:ℝ)))) N = _ from
    model_inside V M p hV (fun X => resourceGood X V) N hcor hcor
      (fun X => Real.exp (s*(unitObs side X-(V:ℝ))))] at hkill
  have he := resource_generator (boxCounts N.1) V p.release
    (alpha (bathOf N.2) p.cleavage p.capacity) (beta (bathOf N.2) p.cleavage p.capacity)
    (fun u w => Real.exp (s*((if side then u else w)-(V:ℝ))))
  change generator (boxCounts N.1) V p.release _ _
    (fun X => Real.exp (s*(unitObs side X-(V:ℝ)))) = _ at he
  rw [he] at hkill
  change (materialModel V M p hV).generator (materialTest V M side s) N ≤
    literalGenerator (boxCounts N.1) V (1/500000000) (1/10) p.release
      (fun X => Real.exp (s*(unitObs side X-(V:ℝ)))) at hkill
  rw [unit_exponential_generator side (boxCounts N.1) V (1/500000000) (1/10) p.release s V] at hkill
  have ht := unit_exponential_tilt side (boxCounts N.1) V (1/500000000) (1/10) p.release s hV
    (by norm_num) (by norm_num) (by linarith [p.release_lower]) hs
  have hu : unitObs side (boxCounts N.1) ≤ (11/10)*(V:ℝ) := by
    cases side
    · exact hcor.2.2.2
    · exact hcor.2.1
  have hsq := mul_le_mul_of_nonneg_left hu (sq_nonneg s)
  apply hkill.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  nlinarith [mul_nonneg (sq_nonneg s) hV.le]

theorem material_step_transform (V M : ℕ) (side : Bool) (p : Parameters M) (s q : ℝ) (hV : 0 < (V:ℝ)) (hs : |s| ≤ 1/100) (hq : 0 < q)
    (hbound : ∀ N, (materialModel V M p hV).total N ≤ q) (N : BoxState V M) :
    ((materialModel V M p hV).uniformize q hq hbound).step (materialTest V M side s) N ≤
      Real.exp (2*s^2*(V:ℝ)/q)*materialTest V M side ((1-1/q)*s) N := by
  rw [FiniteJumpModel.uniformize_step]
  by_cases hcor : resourceGood (boxCounts N.1) V
  · have hg := div_le_div_of_nonneg_right (material_test_generator V M side p s hV hs N hcor) hq.le
    simp only [materialTest,if_pos hcor]
    calc
      _ ≤ Real.exp (s*(unitObs side (boxCounts N.1)-(V:ℝ))) +
          Real.exp (s*(unitObs side (boxCounts N.1)-(V:ℝ))) *
            (-s*(unitObs side (boxCounts N.1)-(V:ℝ))+2*s^2*(V:ℝ))/q := add_le_add le_rfl hg
      _ = Real.exp (s*(unitObs side (boxCounts N.1)-(V:ℝ))) *
          (1+(-s*(unitObs side (boxCounts N.1)-(V:ℝ))+2*s^2*(V:ℝ))/q) := by ring
      _ ≤ Real.exp (s*(unitObs side (boxCounts N.1)-(V:ℝ))) *
          Real.exp ((-s*(unitObs side (boxCounts N.1)-(V:ℝ))+2*s^2*(V:ℝ))/q) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp ((-s*(unitObs side (boxCounts N.1)-(V:ℝ))+2*s^2*(V:ℝ))/q)]
      _ = _ := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
  · rw [show (materialModel V M p hV).generator _ N=0 from
      model_outside V M p hV _ N hcor _]
    simp only [materialTest,if_neg hcor,zero_div,add_zero,mul_zero,le_refl]

theorem material_compensated_step (V M : ℕ) (side : Bool) (p : Parameters M) (s q : ℝ) (hV : 0 < (V:ℝ)) (hs : |s| ≤ 1/100) (hq : 0 < q) (hq1 : 1 ≤ q)
    (hbound : ∀ N, (materialModel V M p hV).total N ≤ q) (N : BoxState V M) :
    ((materialModel V M p hV).uniformize q hq hbound).step (materialCompensated V M side s) N ≤
      materialCompensated V M side ((1-1/q)*s) N := by
  unfold materialCompensated
  rw [FiniteKernel.step_scale]
  have h := mul_le_mul_of_nonneg_left (material_step_transform V M side p s q hV hs hq hbound N)
    (Real.exp_pos (-2*s^2*(V:ℝ))).le
  apply h.trans
  rw [← mul_assoc,← Real.exp_add]
  have ht : 0 ≤ materialTest V M side ((1-1/q)*s) N := by
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
end FiniteReservoir
