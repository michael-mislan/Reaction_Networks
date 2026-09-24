import proofs.DUnstableCores.Elementary.QuarticSpectral
namespace DUnstableCores
theorem elementary_root_real_part_ge_two :
    ∃ z : ℂ, 2 ≤ z.re ∧ elementaryQuartic 10908 185600 1280000 64000000 z = 0 := by
  have hcont : Continuous elementaryShiftH := by
    unfold elementaryShiftH elementaryDelta elementaryShiftA elementaryShiftB
      elementaryShiftC elementaryShiftD
    fun_prop
  have hlo : elementaryShiftH 2 ≤ 0 := by
    norm_num [elementaryShiftH, elementaryDelta, elementaryShiftA,
      elementaryShiftB, elementaryShiftC, elementaryShiftD]
  have hhi : 0 ≤ elementaryShiftH 4 := by
    norm_num [elementaryShiftH, elementaryDelta, elementaryShiftA,
      elementaryShiftB, elementaryShiftC, elementaryShiftD]
  obtain ⟨x,hx,hzero⟩ := intermediate_value_Icc (show (2:ℝ) ≤ 4 by norm_num)
    hcont.continuousOn ⟨hlo,hhi⟩
  have hxpos : 0 < x := by linarith [hx.1]
  have hA : 0 < elementaryShiftA x := by unfold elementaryShiftA; positivity
  have hC : 0 < elementaryShiftC x := by unfold elementaryShiftC; positivity
  let w : ℝ := Real.sqrt (elementaryShiftC x / elementaryShiftA x)
  have hw2 : w^2 = elementaryShiftC x / elementaryShiftA x :=
    Real.sq_sqrt (le_of_lt (div_pos hC hA))
  have hCeq : elementaryShiftC x = elementaryShiftA x*w^2 := by
    rw [hw2]; field_simp
  have hDeq : elementaryShiftD x = elementaryShiftB x*w^2-w^4 := by
    have hdelt : elementaryDelta (elementaryShiftA x) (elementaryShiftB x)
        (elementaryShiftC x) (elementaryShiftD x) = 0 := hzero
    rw [hCeq] at hdelt
    have hfac : (elementaryShiftA x)^2 *
        (elementaryShiftB x*w^2-w^4-elementaryShiftD x) = 0 := by
      dsimp [elementaryDelta] at hdelt
      nlinarith [hdelt]
    have hn : (elementaryShiftA x)^2 ≠ 0 := pow_ne_zero _ (ne_of_gt hA)
    have := (mul_eq_zero.mp hfac).resolve_left hn
    linarith
  have hroot : elementaryQuartic (elementaryShiftA x) (elementaryShiftB x)
      (elementaryShiftC x) (elementaryShiftD x) ((w:ℂ)*Complex.I) = 0 := by
    rw [hCeq,hDeq]
    apply Complex.ext <;>
      simp [elementaryQuartic, pow_succ, Complex.mul_re, Complex.mul_im] <;>
      ring
  refine ⟨(x:ℂ)+(w:ℂ)*Complex.I, by simpa using hx.1, ?_⟩
  calc
    elementaryQuartic 10908 185600 1280000 64000000 ((x:ℂ)+(w:ℂ)*Complex.I) =
        elementaryQuartic (elementaryShiftA x) (elementaryShiftB x)
          (elementaryShiftC x) (elementaryShiftD x) ((w:ℂ)*Complex.I) := by
      simp only [elementaryQuartic, elementaryShiftA, elementaryShiftB,
        elementaryShiftC, elementaryShiftD, Complex.ofReal_add, Complex.ofReal_mul,
        Complex.ofReal_pow, Complex.ofReal_ofNat]
      ring
    _ = 0 := hroot

end DUnstableCores
