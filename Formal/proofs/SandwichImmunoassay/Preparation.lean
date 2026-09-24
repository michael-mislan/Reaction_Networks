import proofs.SandwichImmunoassay.OperatingRanges

namespace SandwichImmunoassay

theorem effective_dilution {d k dlo dhi klo khi : ℝ}
    (hdlo : 0 ≤ dlo) (hkl : 0 < klo) (hk0 : klo ≤ k) (hk1 : k ≤ khi)
    (hd0 : dlo ≤ d) (hd1 : d ≤ dhi) : dlo/khi ≤ d/k ∧ d/k ≤ dhi/klo :=  by
  have kp : 0 < k :=  lt_of_lt_of_le hkl hk0
  have khp : 0 < khi :=  lt_of_lt_of_le kp hk1
  have dp : 0 ≤ d :=  le_trans hdlo hd0
  constructor
  · apply (div_le_div_iff₀ khp kp).2
    nlinarith [mul_nonneg hdlo (sub_nonneg.mpr hk1),
      mul_nonneg (sub_nonneg.mpr hd0) khp.le]
  · apply (div_le_div_iff₀ kp hkl).2
    nlinarith [mul_nonneg dp (sub_nonneg.mpr hk0),
      mul_nonneg (sub_nonneg.mpr hd1) kp.le]

theorem effective_identity {u d k : ℝ} (hd : d≠0) (hk : k≠0) : u/(d/k) = k*u/d :=  by
  field_simp

theorem availability_overlap {L H rmin rmax : ℝ}
    (hr : 0 < rmax) (ho : rmin*H ≤ rmax*L) :
    rmin*H/rmax ≤ L ∧ rmax*(rmin*H/rmax) = rmin*H :=  by
  constructor
  · exact (div_le_iff₀ hr).2 (by nlinarith only [ho])
  · field_simp

theorem transient_high {u d C D K J p q pd qd r t1 td : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hl : 20 ≤ u) (hu : u ≤ 100) (hd0 : 9 ≤ d) (hd1 : d ≤ 11) (hr : 19/20 ≤ r)
    (ht1 : t1 ≤ signal u p q) (htd : (9/10)*signal (u/d) pd qd ≤ td) :
    3/100 ≤ r*td-t1 :=  by
  have mr : (171/200:ℝ) ≤ r*(9/10) :=  by linarith only [hr]
  have margin :=  attenuation_90pct_source h j hc hd hk hj hl hu hd0 hd1 mr
  have mult :=  mul_le_mul_of_nonneg_left htd (by linarith : 0 ≤ r)
  nlinarith only [margin,mult,ht1]

theorem transient_low {u d C D K J p q pd qd r t1 td : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hu : u ≤ 1/10) (hd0 : 9 ≤ d) (hr0 : 0 ≤ r) (hr : r ≤ 21/20)
    (ht1 : (9/10)*signal u p q ≤ t1) (htd : td ≤ signal (u/d) pd qd) :
    r*td-t1 ≤ 0 :=  by
  have u0 :=  h.capture.x_nonneg
  have b0 :=  h.signal_nonneg
  have lower :=  (h.box_bounds hc hd hk hj).1
  have sq : (u+11/5)^2 ≤ 529/100 :=  by nlinarith only [hu,u0]
  have mult :=  mul_le_mul_of_nonneg_right sq b0
  have b1 : (3/20)*u ≤ signal u p q :=  by nlinarith only [lower,mult,u0]
  have ub :=  j.signal_le_x
  have du : u/d ≤ u/9 :=  (div_le_div_iff₀ (by linarith) (by norm_num)).2 (by nlinarith)
  have rb :=  mul_le_mul hr (le_trans ub du) j.signal_nonneg (by norm_num : (0:ℝ) ≤ 21/20)
  have tb :=  mul_le_mul_of_nonneg_left htd hr0
  nlinarith only [ht1,b1,rb,tb,u0]

theorem transient_noisy_high {u d C D K J p q pd qd r t1 td g gmin e1 ed eps : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hl : 20 ≤ u) (hu : u ≤ 100) (hd0 : 9 ≤ d) (hd1 : d ≤ 11) (hr : 19/20 ≤ r)
    (ht1 : t1 ≤ signal u p q) (htd : (9/10)*signal (u/d) pd qd ≤ td)
    (hg : gmin ≤ g) (hg0 : 0 ≤ gmin) (he1 : |e1| ≤ eps) (hed : |ed| ≤ eps) :
    gmin*(3/100)-2*eps ≤ (g*r*td+ed)-(g*t1+e1) := by
  exact noisy_margin hg hg0 (by norm_num)
    (transient_high h j hc hd hk hj hl hu hd0 hd1 hr ht1 htd) he1 hed

end SandwichImmunoassay
