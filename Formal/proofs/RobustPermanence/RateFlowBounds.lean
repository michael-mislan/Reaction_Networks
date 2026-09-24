import proofs.RobustPermanence.RateFlow

namespace RobustPermanence
open CoreCouplingGlobal CoreCouplingCAC

theorem rate_extension_total_bound (r : AssemblyRates) (hr : RateBox r) (S : ℝ)
    (hS : 34 ≤ S) (b : ConsumerVector → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → ConsumerVector) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (h0 : X 0 0+X 0 1 ≤ S)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • rateField r (X t)) t) :
    ∀ t, 0 ≤ t → X t 0+X t 1 ≤ S := by
  apply scalar_upper_barrier _ (fun t => b (X t)*
    (rateA r (X t 0) (X t 1) (X t 2)+rateB r (X t 0) (X t 1) (X t 2))) S ?_ h0 ?_
  · intro t ht
    convert ((hasDerivAt_pi.1 (hd t ht)) 0).add ((hasDerivAt_pi.1 (hd t ht)) 1) using 1
    dsimp [rateField]
    ring
  · intro t ht hs
    apply mul_nonpos_of_nonneg_of_nonpos (hb _)
    have hh := rate_total_upper r hr (X t 0) (X t 1) (X t 2) (hX t ht 0) (hX t ht 1)
    linarith only [hh,hs,hS]

theorem rate_weighted_general (r : AssemblyRates) (hr : RateBox r) (A B z H X S : ℝ)
    (hA : 0 ≤ A) (hAS : A ≤ S) (hB : 0 ≤ B) (hz : 0 ≤ z) (hH : 0 ≤ H) (hX : 0 ≤ X) :
    rateZ r A B z H X+(7/4:ℝ)*rateH r z H ≤ 2*S+200-(2/7)*(z+(7/4)*H) := by
  rw [rate_weighted_identity]
  have hp := mul_le_mul_of_nonneg_right (show r.p ≤ 2 by linarith [hr.p.2]) hA
  have hq := mul_nonneg (mul_nonneg (by linarith [hr.q.1] : 0 ≤ r.q) hB) hz
  have hk := mul_nonneg (mul_nonneg (by linarith [hr.k.1] : 0 ≤ r.k) hz) hX
  have hu := mul_le_mul_of_nonneg_right (show r.u ≤ 17 by linarith [hr.u.2]) hz
  have hv := mul_le_mul_of_nonneg_right (show 1 ≤ r.v by linarith [hr.v.1]) (sq_nonneg z)
  have hc : (-3*r.h1+r.h2-7*r.d)/4 ≤ -(1/2:ℝ) := by linarith [hr.h1.1,hr.h2.2,hr.d.1]
  have hcH := mul_le_mul_of_nonneg_right hc hH
  have hquad := quadratic_ceiling ((3/4)*17+2/7) (1/4) 200 z (by norm_num) (by norm_num)
  nlinarith only [hp,hAS,hq,hk,hu,hv,hcH,hquad]

theorem rate_extension_weighted_bound (r : AssemblyRates) (hr : RateBox r) (S W : ℝ)
    (hW : (7/2)*(2*S+200) ≤ W) (b : ConsumerVector → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → ConsumerVector) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (hS : ∀ t, 0 ≤ t → X t 0+X t 1 ≤ S) (h0 : X 0 2+(7/4:ℝ)*X 0 3 ≤ W)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • rateField r (X t)) t) :
    ∀ t, 0 ≤ t → X t 2+(7/4:ℝ)*X t 3 ≤ W := by
  apply scalar_upper_barrier _ (fun t => b (X t)*
    (rateZ r (X t 0) (X t 1) (X t 2) (X t 3) (X t 4)+(7/4:ℝ)*rateH r (X t 2) (X t 3))) W ?_ h0 ?_
  · intro t ht
    convert ((hasDerivAt_pi.1 (hd t ht)) 2).add (((hasDerivAt_pi.1 (hd t ht)) 3).const_mul (7/4:ℝ)) using 1
    dsimp [rateField]
    ring
  · intro t ht hw
    apply mul_nonpos_of_nonneg_of_nonpos (hb _)
    have hh := rate_weighted_general r hr (X t 0) (X t 1) (X t 2) (X t 3) (X t 4) S
      (hX t ht 0) (by have hh := hS t ht; have hn := hX t ht 1; linarith)
      (hX t ht 1) (hX t ht 2) (hX t ht 3) (hX t ht 4)
    linarith only [hh,hw,hW]

theorem rate_extension_abundance_bound (r : AssemblyRates) (hr : RateBox r) (Q : ℝ)
    (b : ConsumerVector → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → ConsumerVector) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (hz : ∀ t, 0 ≤ t → 4*X t 2 ≤ Q) (h0 : X 0 4 ≤ Q)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • rateField r (X t)) t) :
    ∀ t, 0 ≤ t → X t 4 ≤ Q := by
  apply scalar_upper_barrier (fun t => X t 4) (fun t => b (X t)*rateX r (X t 2) (X t 4)) Q
    (fun t ht => hasDerivAt_pi.1 (hd t ht) 4) h0
  intro t ht hq
  apply mul_nonpos_of_nonneg_of_nonpos (hb _)
  apply mul_nonpos_of_nonneg_of_nonpos (hX t ht 4)
  have hk := mul_le_mul_of_nonneg_right (show r.k ≤ 2 by linarith [hr.k.2]) (hX t ht 2)
  have hrho := mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ r.rho by linarith [hr.rho.1]) (hX t ht 4)
  linarith [hz t ht,hr.mu.1]

end RobustPermanence
