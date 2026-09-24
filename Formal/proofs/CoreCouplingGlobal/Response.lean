import proofs.CoreCouplingGlobal.Absorbing

namespace CoreCouplingGlobal
open CoreCouplingCAC

noncomputable def responseA (e B : ℝ) : ℝ :=
  2*(33-B+e*B)/(1+Real.sqrt (1+4*e*(33-B+e*B)))

noncomputable def responseTotal (e B : ℝ) : ℝ := B+responseA e B

theorem response_discriminant_pos (e B : ℝ) (he : 0 ≤ e)
    (he' : e ≤ 1/50000) (hB : 2 ≤ B) (hB' : B ≤ 34) :
    0 < 1+4*e*(33-B+e*B) := by
  have heB := mul_nonneg he (by linarith : 0 ≤ B)
  have hq : -1 ≤ 33-B+e*B := by linarith
  have := mul_le_mul_of_nonneg_left hq he
  nlinarith

theorem response_quadratic (e B : ℝ) (he : 0 ≤ e)
    (he' : e ≤ 1/50000) (hB : 2 ≤ B) (hB' : B ≤ 34) :
    e*(responseA e B)^2+responseA e B = 33-B+e*B := by
  have hd := response_discriminant_pos e B he he' hB hB'
  have hs := Real.sq_sqrt (le_of_lt hd)
  have hn : 1+Real.sqrt (1+4*e*(33-B+e*B)) ≠ 0 := by positivity
  dsimp [responseA]
  generalize Real.sqrt (1+4*e*(33-B+e*B)) = t at hs hn ⊢
  field_simp
  linear_combination -(33-B+e*B)*hs

theorem response_bounds (e B : ℝ) (he : 0 ≤ e)
    (he' : e ≤ 1/50000) (hB : 2 ≤ B) (hB' : B ≤ 34) :
    -1 ≤ responseA e B ∧ responseA e B ≤ 33 := by
  have hq := response_quadratic e B he he' hB hB'
  have heB := mul_nonneg he (by linarith : 0 ≤ B)
  have hden : 1 ≤ 1+Real.sqrt (1+4*e*(33-B+e*B)) := by
    linarith [Real.sqrt_nonneg (1+4*e*(33-B+e*B))]
  have hrough : -2 ≤ responseA e B := by
    dsimp [responseA]
    apply (le_div_iff₀ (by positivity)).2
    nlinarith
  have heA := mul_le_mul_of_nonneg_left hrough he
  have hfactor : 0 < 1+e*(responseA e B-1) := by nlinarith
  have hlow : -1 ≤ responseA e B := by
    by_contra hh
    have hneg := mul_neg_of_neg_of_pos (by linarith : responseA e B+1 < 0) hfactor
    have hEB : e ≤ e*B := by nlinarith
    nlinarith
  have hupper : responseA e B ≤ 33 := by
    have he1 : e ≤ 1 := by linarith
    have hQB := mul_le_mul_of_nonneg_right he1 (by linarith : 0 ≤ B)
    have heAA := mul_nonneg he (sq_nonneg (responseA e B))
    nlinarith
  exact ⟨hlow,hupper⟩

noncomputable def responseSlope (e B : ℝ) : ℝ :=
  e*(1+2*responseA e B)/(1+2*e*responseA e B)

theorem response_coefficient_bounds (e A B : ℝ) (he : 0 ≤ e)
    (he' : e ≤ 1/50000) (hA : 0 ≤ A) (hA' : A ≤ 34)
    (hB : 2 ≤ B) (hB' : B ≤ 34) :
    99/100 ≤ 1+e*(A+responseA e B) ∧
    1+e*(A+responseA e B) ≤ 101/100 ∧
    -(1/500) ≤ responseSlope e B ∧ responseSlope e B ≤ 1/500 := by
  obtain ⟨hl,hu⟩ := response_bounds e B he he' hB hB'
  have hel := mul_le_mul_of_nonneg_left hl he
  have heu := mul_le_mul_of_nonneg_left hu he
  have heA := mul_nonneg he hA
  have heA' := mul_le_mul_of_nonneg_left hA' he
  have hd : 0 < 1+2*e*responseA e B := by nlinarith
  refine ⟨by nlinarith, by nlinarith, ?_, ?_⟩
  · dsimp [responseSlope]
    apply (le_div_iff₀ hd).2
    nlinarith
  · dsimp [responseSlope]
    apply (div_le_iff₀ hd).2
    nlinarith

theorem responseTotal_hasDerivAt (e B : ℝ) (he : 0 ≤ e)
    (he' : e ≤ 1/50000) (hB : 2 ≤ B) (hB' : B ≤ 34) :
    HasDerivAt (responseTotal e) (responseSlope e B) B := by
  have hd := response_discriminant_pos e B he he' hB hB'
  have hs := Real.sq_sqrt (le_of_lt hd)
  have hs0 : 0 < Real.sqrt (1+4*e*(33-B+e*B)) := Real.sqrt_pos.2 hd
  have hn : 1+Real.sqrt (1+4*e*(33-B+e*B)) ≠ 0 := by positivity
  have hq : HasDerivAt (fun x : ℝ => 33-x+e*x) (-1+e) B := by
    convert ((hasDerivAt_const B (33:ℝ)).sub (hasDerivAt_id B)).add
      ((hasDerivAt_id B).const_mul e) using 1
    ring
  have hdv := (hq.const_mul (4*e)).const_add 1
  have hsq := hdv.sqrt (ne_of_gt hd)
  have hv := (hasDerivAt_id B).add ((hq.const_mul 2).div (hsq.const_add 1) hn)
  have hresponse : 1+2*e*responseA e B = Real.sqrt (1+4*e*(33-B+e*B)) := by
    dsimp [responseA]
    generalize Real.sqrt (1+4*e*(33-B+e*B)) = t at hs hn ⊢
    field_simp
    nlinarith only [hs]
  convert hv using 1
  dsimp [responseSlope]
  rw [hresponse]
  dsimp [responseA]
  generalize Real.sqrt (1+4*e*(33-B+e*B)) = t at hs hn hs0 ⊢
  field_simp
  linear_combination -(t+e)*hs

/-- Exact response residuals for the literal four-species ODE. -/
theorem response_residual_identities (e A B z H h : ℝ)
    (hq : h+e*(h-B)^2 = 33+e*B) :
    fA (flagshipRates e) A B z + fB (flagshipRates e) A B z =
      -(1+e*(A+h-B))*(A+B-h) ∧
    fB (flagshipRates e) A B z =
      60-(2+z)*B+(1+e*(A+h-B))*(A+B-h) ∧
    fZ (flagshipRates e) A B z H =
      h-(1+z)*B-16*z-4*z^2+3*H+(A+B-h) := by
  dsimp [fA,fB,fZ,flagshipRates]
  constructor
  · nlinarith only [hq]
  constructor
  · nlinarith only [hq]
  · ring

end CoreCouplingGlobal
