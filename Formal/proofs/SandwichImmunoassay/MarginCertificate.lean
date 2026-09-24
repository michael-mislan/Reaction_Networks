import proofs.SandwichImmunoassay.Robust

namespace SandwichImmunoassay

noncomputable def marginPolynomial (u d r m : ℝ) : ℝ := 
  81*r*d*u^2-(81+100*m*u)*(u+11/5*d)^2

theorem bernstein_nonneg {t b0 b1 b2 b3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (h0 : 0 ≤ b0) (h1 : 0 ≤ b1)
    (h2 : 0 ≤ b2) (h3 : 0 ≤ b3) :
    0  ≤  b0*(1-t)^3+3*b1*t*(1-t)^2+3*b2*t^2*(1-t)+b3*t^3 :=  by
  have : 0 ≤ 1-t :=  by linarith
  positivity

theorem dilution_endpoints {u d r m lo hi : ℝ}
    (hu : 0 ≤ u) (hm : 0 ≤ m) (hwidth : lo < hi) (hlo : lo ≤ d) (hhi : d ≤ hi)
    (h0 : 0 ≤ marginPolynomial u lo r m) (h1 : 0 ≤ marginPolynomial u hi r m) :
    0 ≤ marginPolynomial u d r m :=  by
  have identity : (hi-lo)*marginPolynomial u d r m  = 
      (hi-d)*marginPolynomial u lo r m+(d-lo)*marginPolynomial u hi r m+
      (hi-lo)*(121/25)*(81+100*m*u)*(d-lo)*(hi-d) :=  by
    unfold marginPolynomial
    ring
  have a :=  mul_nonneg (sub_nonneg.mpr hhi) h0
  have b :=  mul_nonneg (sub_nonneg.mpr hlo) h1
  have c : 0 ≤ (hi-lo)*(121/25)*(81+100*m*u)*(d-lo)*(hi-d) :=  by
    have : 0 ≤ hi-lo :=  sub_nonneg.mpr hwidth.le
    have : 0 ≤ d-lo :=  sub_nonneg.mpr hlo
    have : 0 ≤ hi-d :=  sub_nonneg.mpr hhi
    positivity
  nlinarith only [identity,a,b,c,hwidth]

theorem shared_source_bounds {u C D K J p q : ℝ}
    (h : Reaction u C D K J p q)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J) :
    C*D*u  ≤  (u+11/5)^2*signal u p q ∧ u*signal u p q  ≤  C*D :=  by
  have u0 :=  h.capture.x_nonneg
  have cp :=  h.capture.total_pos
  have dp :=  h.detector.total_pos
  have pp :=  h.capture.pos
  have qp :=  h.detector.pos
  have lp :=  (div_le_iff₀ (by linarith [h.capture.kd_pos] : 0 < u+K+C)).mp h.capture.bounds.1
  have lq :=  (div_le_iff₀ (by linarith [h.detector.kd_pos] : 0 < u+J+D)).mp h.detector.bounds.1
  have bp : C  ≤  (u+11/5)*p :=  by
    nlinarith [mul_nonneg pp.le (show 0 ≤ 11/5-K-C by linarith [hk.2,hc.2])]
  have bq : D  ≤  (u+11/5)*q :=  by
    nlinarith [mul_nonneg qp.le (show 0 ≤ 11/5-J-D by linarith [hj.2,hd.2])]
  have low :=  mul_le_mul_of_nonneg_left (mul_le_mul bp bq dp.le (by positivity)) u0
  have high :=  mul_le_mul h.capture.total_bound h.detector.total_bound
    (mul_nonneg u0 qp.le) cp.le
  dsimp [signal]
  constructor  <;>  nlinarith only [low,high]

theorem algebra_margin {u v d c r m bd bn : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hr : 0 ≤ r) (hm : 0 ≤ m) (hc : 81/100 ≤ c)
    (hl : c*d*u  ≤  v*bd) (hn : u*bn ≤ c)
    (hp : 0 ≤ 81*r*d*u^2-(81+100*m*u)*v) : m ≤ r*bd-bn :=  by
  have mw : 0 ≤ m*u*v :=  by positivity
  have a : 0 ≤ r*d*u^2-v :=  by nlinarith only [hp,mw]
  have b :=  mul_nonneg (show 0 ≤ c-81/100 by linarith) a
  have l :=  mul_le_mul_of_nonneg_right hl (mul_nonneg hr hu.le)
  have n :=  mul_le_mul_of_nonneg_right hn hv.le
  have final : m*(u*v)  ≤  (r*bd-bn)*(u*v) :=  by nlinarith only [hp,b,l,n]
  exact (mul_le_mul_iff_left₀ (mul_pos hu hv)).mp final

theorem source_certificate {u d C D K J p q pd qd r r0 m : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hu : 0 < u) (hdil : 0 < d) (hr0 : 0 ≤ r0) (hr : r0 ≤ r) (hm : 0 ≤ m)
    (cert : 0 ≤ marginPolynomial u d r0 m) :
    m  ≤  r*signal (u/d) pd qd-signal u p q :=  by
  have low :=  (shared_source_bounds j hc hd hk hj).1
  have scaled :=  mul_le_mul_of_nonneg_right low (sq_nonneg d)
  have eq1 : C*D*(u/d)*d^2 = C*D*d*u :=  by field_simp
  have eq2 : ((u/d+11/5)^2*signal (u/d) pd qd)*d^2 = 
      (u+11/5*d)^2*signal (u/d) pd qd :=  by field_simp
  rw [eq1,eq2] at scaled
  have prod : (81/100:ℝ)  ≤  C*D :=  by
    have :=  mul_le_mul hc.1 hd.1 (by norm_num : (0:ℝ) ≤ 9/10) h.capture.total_pos.le
    norm_num at this ⊢
    exact this
  have margin :=  algebra_margin hu (sq_pos_of_pos (by positivity : 0 < u+11/5*d)) hr0 hm prod
    scaled (shared_source_bounds h hc hd hk hj).2 cert
  have drift :=  mul_le_mul_of_nonneg_right hr j.signal_nonneg
  linarith only [margin,drift]

theorem noisy_margin {bn bd r g e1 ed eps m gmin : ℝ}
    (hg : gmin ≤ g) (hg0 : 0 ≤ gmin) (hm : 0 ≤ m) (h : m ≤ r*bd-bn)
    (he1 : |e1| ≤ eps) (hed : |ed| ≤ eps) :
    gmin*m-2*eps  ≤  (g*r*bd+ed)-(g*bn+e1) :=  by
  have b :=  mul_le_mul hg h hm (by linarith only [hg,hg0])
  have ee1 :=  abs_le.mp he1
  have eed :=  abs_le.mp hed
  nlinarith only [b,ee1.2,eed.1]

end SandwichImmunoassay
