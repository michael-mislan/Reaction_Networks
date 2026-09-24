import proofs.CoreCouplingGlobal.PositiveExtension
import proofs.CoreCouplingGlobal.ScalarBarrier

namespace CoreCouplingGlobal
open CoreCouplingCAC

theorem response_boundary_nonneg (e : ℝ) (he : 0 ≤ e) (y : ResponseVector)
    (hy : ∀ i, 0 ≤ y i) (i : Fin 4) (hi : y i = 0) : 0 ≤ responseVectorField e y i := by
  have h₀ := hy 0
  have h₁ := hy 1
  have h₂ := hy 2
  have h₃ := hy 3
  fin_cases i
  · change y 0 = 0 at hi
    change 0 ≤ 6-2*y 0+y 2*y 1+2*e*(y 1-(y 0)^2)
    rw [hi]
    nlinarith [mul_nonneg h₂ h₁,mul_nonneg he h₁]
  · change y 1 = 0 at hi
    change 0 ≤ 27+y 0-(1+y 2)*y 1-e*(y 1-(y 0)^2)
    rw [hi]
    nlinarith [mul_nonneg he (sq_nonneg (y 0))]
  · change y 2 = 0 at hi
    change 0 ≤ y 0-y 1*y 2-16*y 2-2*2*(y 2)^2+3*y 3
    rw [hi]
    linarith
  · change y 3 = 0 at hi
    change 0 ≤ 16*y 2+2*(y 2)^2-(2+1/10000)*y 3
    rw [hi]
    nlinarith

theorem extension_nonnegative (e : ℝ) (he : 0 ≤ e) (b : ResponseVector → ℝ)
    (hb : ∀ x, 0 ≤ b x) (X : ℝ → ResponseVector) (h0 : ∀ i, 0 ≤ X 0 i)
    (hd : ∀ t, HasDerivAt X (b (positivePart (X t)) • responseVectorField e (positivePart (X t))) t) :
    ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i := by
  intro t ht i
  apply scalar_lower_barrier (fun t => X t i)
    (fun t => b (positivePart (X t))*responseVectorField e (positivePart (X t)) i) 0
    (fun t _ => (hasDerivAt_pi.1 (hd t)) i) (h0 i) ?_ t ht
  intro s _ hs
  apply mul_nonneg (hb _)
  apply response_boundary_nonneg e he _ (fun j => le_max_left 0 (X s j)) i
  exact max_eq_left hs

theorem weighted_upper_comparison_general (A B z H e S : ℝ)
    (hA : A ≤ S) (hB : 0 ≤ B) (hz : 0 ≤ z) (hH : 0 ≤ H) :
    fZ (flagshipRates e) A B z H+(7/4:ℝ)*fH (flagshipRates e) z H ≤
      S+76-(2/7:ℝ)*(z+(7/4:ℝ)*H) := by
  have hBZ := mul_nonneg hB hz
  have hs := sq_nonneg (z-86/7)
  dsimp [fZ,fH,flagshipRates]
  nlinarith only [hA,hBZ,hH,hs]

theorem extension_total_bound (e S : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (hS : 34 ≤ S) (b : ResponseVector → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → ResponseVector) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (h0 : X 0 0+X 0 1 ≤ S)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • responseVectorField e (X t)) t) :
    ∀ t, 0 ≤ t → X t 0+X t 1 ≤ S := by
  apply scalar_upper_barrier _ (fun t => b (X t)*
    (fA (flagshipRates e) (X t 0) (X t 1) (X t 2)+fB (flagshipRates e) (X t 0) (X t 1) (X t 2))) S
    ?_ h0 ?_
  · intro t ht
    convert ((hasDerivAt_pi.1 (hd t ht)) 0).add ((hasDerivAt_pi.1 (hd t ht)) 1) using 1
    dsimp [responseVectorField]
    ring
  · intro t ht hs
    apply mul_nonpos_of_nonneg_of_nonpos (hb _)
    have hh := total_upper_comparison (X t 0) (X t 1) (X t 2) e (hX t ht 0) he
    have hprod : (49999/50000:ℝ)*34 ≤ (1-e)*(X t 0+X t 1) :=
      mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
    linarith

theorem extension_weighted_bound (e S W : ℝ) (hW : (7/2)*(S+76) ≤ W)
    (b : ResponseVector → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → ResponseVector) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (hS : ∀ t, 0 ≤ t → X t 0+X t 1 ≤ S)
    (h0 : X 0 2+(7/4:ℝ)*X 0 3 ≤ W)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • responseVectorField e (X t)) t) :
    ∀ t, 0 ≤ t → X t 2+(7/4:ℝ)*X t 3 ≤ W := by
  apply scalar_upper_barrier _ (fun t => b (X t)*
    (fZ (flagshipRates e) (X t 0) (X t 1) (X t 2) (X t 3)+(7/4:ℝ)*fH (flagshipRates e) (X t 2) (X t 3))) W
    ?_ h0 ?_
  · intro t ht
    convert ((hasDerivAt_pi.1 (hd t ht)) 2).add (((hasDerivAt_pi.1 (hd t ht)) 3).const_mul (7/4:ℝ)) using 1
    dsimp [responseVectorField]
    ring
  · intro t ht hw
    apply mul_nonpos_of_nonneg_of_nonpos (hb _)
    have hh := weighted_upper_comparison_general (X t 0) (X t 1) (X t 2) (X t 3) e S
      (by have hh := hS t ht; have hh' := hX t ht 1; linarith)
      (hX t ht 1) (hX t ht 2) (hX t ht 3)
    linarith

theorem response_linear_lower (e R : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (hR : 1 ≤ R) (y : ResponseVector) (hy : ∀ i, 0 ≤ y i) (hy' : ∀ i, y i ≤ R)
    (i : Fin 4) : -(20+6*R)*y i ≤ responseVectorField e y i := by
  have hA := hy 0
  have hB := hy 1
  have hz := hy 2
  have hH := hy 3
  have hA' := hy' 0
  have hB' := hy' 1
  have hz' := hy' 2
  have he1 : e ≤ 1 := by linarith
  have heAA := mul_nonneg he (sq_nonneg (y 0))
  have heB := mul_nonneg he hB
  have hzB := mul_nonneg hz hB
  have hAA : e*(y 0)^2 ≤ R*y 0 := by
    have hh := mul_le_mul_of_nonneg_right he1 (sq_nonneg (y 0))
    have hh' := mul_nonneg hA (sub_nonneg.2 hA')
    nlinarith
  have heB' := mul_le_mul_of_nonneg_right he1 hB
  have hzB' := mul_le_mul_of_nonneg_right hz' hB
  have hBz' := mul_le_mul_of_nonneg_right hB' hz
  have hzz := mul_nonneg hz (sub_nonneg.2 hz')
  have hRA := mul_nonneg (by linarith : 0 ≤ R) hA
  have hRB := mul_nonneg (by linarith : 0 ≤ R) hB
  have hRz := mul_nonneg (by linarith : 0 ≤ R) hz
  have hRH := mul_nonneg (by linarith : 0 ≤ R) hH
  fin_cases i
  · change -(20+6*R)*y 0 ≤ 6-2*y 0+y 2*y 1+2*e*(y 1-(y 0)^2)
    nlinarith
  · change -(20+6*R)*y 1 ≤ 27+y 0-(1+y 2)*y 1-e*(y 1-(y 0)^2)
    nlinarith
  · change -(20+6*R)*y 2 ≤ y 0-y 1*y 2-16*y 2-2*2*(y 2)^2+3*y 3
    nlinarith
  · change -(20+6*R)*y 3 ≤ 16*y 2+2*(y 2)^2-(2+1/10000)*y 3
    nlinarith

end CoreCouplingGlobal
