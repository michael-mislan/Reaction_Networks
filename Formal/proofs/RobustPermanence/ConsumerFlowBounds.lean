import proofs.RobustPermanence.ConsumerFlow

namespace RobustPermanence
open CoreCouplingCAC CoreCouplingGlobal

theorem weighted_upper_comparison_general (A B z H e S : ℝ)
    (hA : A ≤ S) (hB : 0 ≤ B) (hz : 0 ≤ z) (hH : 0 ≤ H) :
    fZ (flagshipRates e) A B z H+(7/4:ℝ)*fH (flagshipRates e) z H ≤
      S+76-(2/7:ℝ)*(z+(7/4:ℝ)*H) := by
  have hBZ := mul_nonneg hB hz
  have hs := sq_nonneg (z-86/7)
  dsimp [fZ,fH,flagshipRates]
  nlinarith only [hA,hBZ,hH,hs]

theorem consumer_extension_total_bound (e S : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (hS : 34 ≤ S) (b : ConsumerVector → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → ConsumerVector) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (h0 : X 0 0+X 0 1 ≤ S)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • consumerField e (X t)) t) :
    ∀ t, 0 ≤ t → X t 0+X t 1 ≤ S := by
  apply scalar_upper_barrier _ (fun t => b (X t)*
    (fA (flagshipRates e) (X t 0) (X t 1) (X t 2)+fB (flagshipRates e) (X t 0) (X t 1) (X t 2))) S
    ?_ h0 ?_
  · intro t ht
    convert ((hasDerivAt_pi.1 (hd t ht)) 0).add ((hasDerivAt_pi.1 (hd t ht)) 1) using 1
    dsimp [consumerField]
    ring
  · intro t ht hs
    apply mul_nonpos_of_nonneg_of_nonpos (hb _)
    have hh := total_upper_comparison (X t 0) (X t 1) (X t 2) e (hX t ht 0) he
    have hprod : (49999/50000:ℝ)*34 ≤ (1-e)*(X t 0+X t 1) :=
      mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
    linarith

theorem consumer_extension_weighted_bound (e S W : ℝ) (hW : (7/2)*(S+76) ≤ W)
    (b : ConsumerVector → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → ConsumerVector) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (hS : ∀ t, 0 ≤ t → X t 0+X t 1 ≤ S)
    (h0 : X 0 2+(7/4:ℝ)*X 0 3 ≤ W)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • consumerField e (X t)) t) :
    ∀ t, 0 ≤ t → X t 2+(7/4:ℝ)*X t 3 ≤ W := by
  apply scalar_upper_barrier _ (fun t => b (X t)*
    (fZ (flagshipRates e) (X t 0) (X t 1) (X t 2) (X t 3)-(X t 2)*(X t 4)+(7/4:ℝ)*fH (flagshipRates e) (X t 2) (X t 3))) W
    ?_ h0 ?_
  · intro t ht
    convert ((hasDerivAt_pi.1 (hd t ht)) 2).add (((hasDerivAt_pi.1 (hd t ht)) 3).const_mul (7/4:ℝ)) using 1
    dsimp [consumerField]
    ring
  · intro t ht hw
    apply mul_nonpos_of_nonneg_of_nonpos (hb _)
    have hh := weighted_upper_comparison_general (X t 0) (X t 1) (X t 2) (X t 3) e S
      (by have hh := hS t ht; have hh' := hX t ht 1; linarith)
      (hX t ht 1) (hX t ht 2) (hX t ht 3)
    have hfeed := mul_nonneg (hX t ht 2) (hX t ht 4)
    linarith

theorem consumer_linear_lower (e R : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (hR : 1 ≤ R) (y : ConsumerVector) (hy : ∀ i, 0 ≤ y i) (hy' : ∀ i, y i ≤ R)
    (i : Fin 5) : -(20+7*R)*y i ≤ consumerField e y i := by
  have hx := hy 4
  have hx' := hy' 4
  have hxz := mul_le_mul_of_nonneg_left hx' (hy 2)
  have hxx := mul_le_mul_of_nonneg_left hx' hx
  have hzx := mul_nonneg (hy 2) hx
  have hRx := mul_nonneg (by linarith : 0 ≤ R) hx
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
  · change -(20+7*R)*y 0 ≤ 6-2*y 0+y 2*y 1+2*e*(y 1-(y 0)^2)
    nlinarith
  · change -(20+7*R)*y 1 ≤ 27+y 0-(1+y 2)*y 1-e*(y 1-(y 0)^2)
    nlinarith
  · change -(20+7*R)*y 2 ≤ y 0-y 1*y 2-16*y 2-2*2*(y 2)^2+3*y 3-y 2*y 4
    nlinarith
  · change -(20+7*R)*y 3 ≤ 16*y 2+2*(y 2)^2-(2+1/10000)*y 3
    nlinarith

  · change -(20+7*R)*y 4 ≤ y 4*(y 2-1/2-y 4)
    nlinarith

end RobustPermanence

