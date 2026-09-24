import proofs.SandwichImmunoassay.Preparation
import proofs.SandwichImmunoassay.Controls

namespace SandwichImmunoassay

/-- Margin polynomial for an arbitrary reagent box: `A` and `H` bound `K+C` and `J+D`
from above, `c` bounds the capacity product `C*D` from below. -/
noncomputable def generalPolynomial (u d r m A H c : ℝ) : ℝ :=
  c*r*d*u^2-(c+m*u)*(u+A*d)*(u+H*d)

theorem general_dilution_endpoints {u d r m A H c lo hi : ℝ}
    (hu : 0 ≤ u) (hm : 0 ≤ m) (hA : 0 ≤ A) (hH : 0 ≤ H) (hc : 0 ≤ c)
    (hwidth : lo < hi) (hlo : lo ≤ d) (hhi : d ≤ hi)
    (h0 : 0 ≤ generalPolynomial u lo r m A H c)
    (h1 : 0 ≤ generalPolynomial u hi r m A H c) :
    0 ≤ generalPolynomial u d r m A H c := by
  have identity : (hi-lo)*generalPolynomial u d r m A H c =
      (hi-d)*generalPolynomial u lo r m A H c+(d-lo)*generalPolynomial u hi r m A H c+
      (hi-lo)*A*H*(c+m*u)*(d-lo)*(hi-d) := by
    unfold generalPolynomial
    ring
  have a := mul_nonneg (sub_nonneg.mpr hhi) h0
  have b := mul_nonneg (sub_nonneg.mpr hlo) h1
  have e : 0 ≤ (hi-lo)*A*H*(c+m*u)*(d-lo)*(hi-d) := by
    have : 0 ≤ hi-lo := sub_nonneg.mpr hwidth.le
    have : 0 ≤ d-lo := sub_nonneg.mpr hlo
    have : 0 ≤ hi-d := sub_nonneg.mpr hhi
    positivity
  nlinarith only [identity,a,b,e,hwidth]

theorem general_shared_bounds {u C D K J p q A H : ℝ}
    (h : Reaction u C D K J p q) (hA : K+C ≤ A) (hH : J+D ≤ H) :
    C*D*u ≤ (u+A)*(u+H)*signal u p q ∧ u*signal u p q ≤ C*D := by
  have u0 := h.capture.x_nonneg
  have cp := h.capture.total_pos
  have dp := h.detector.total_pos
  have pp := h.capture.pos
  have qp := h.detector.pos
  have A0 : 0 ≤ A := by linarith only [hA,cp,h.capture.kd_pos]
  have H0 : 0 ≤ H := by linarith only [hH,dp,h.detector.kd_pos]
  have lp := (div_le_iff₀ (by linarith [h.capture.kd_pos] : 0 < u+K+C)).mp h.capture.bounds.1
  have lq := (div_le_iff₀ (by linarith [h.detector.kd_pos] : 0 < u+J+D)).mp h.detector.bounds.1
  have bp : C ≤ (u+A)*p := by
    nlinarith only [lp,mul_nonneg pp.le (show 0 ≤ A-K-C by linarith only [hA])]
  have bq : D ≤ (u+H)*q := by
    nlinarith only [lq,mul_nonneg qp.le (show 0 ≤ H-J-D by linarith only [hH])]
  have low := mul_le_mul_of_nonneg_left (mul_le_mul bp bq dp.le (by positivity)) u0
  have high := mul_le_mul h.capture.total_bound h.detector.total_bound
    (mul_nonneg u0 qp.le) cp.le
  dsimp [signal]
  constructor <;> nlinarith only [low,high]

theorem general_algebra_margin {u v d c c0 r m bd bn : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hr : 0 ≤ r) (hm : 0 ≤ m) (hc0 : 0 < c0) (hc : c0 ≤ c)
    (hl : c*d*u ≤ v*bd) (hn : u*bn ≤ c)
    (hp : 0 ≤ c0*r*d*u^2-(c0+m*u)*v) : m ≤ r*bd-bn := by
  have mw : 0 ≤ m*u*v := by positivity
  have a : 0 ≤ r*d*u^2-v := by
    by_contra hneg
    have neg := mul_pos hc0 (neg_pos.mpr (not_le.mp hneg))
    nlinarith only [hp,mw,neg]
  have b := mul_nonneg (sub_nonneg.mpr hc) a
  have l := mul_le_mul_of_nonneg_right hl (mul_nonneg hr hu.le)
  have n := mul_le_mul_of_nonneg_right hn hv.le
  have final : m*(u*v) ≤ (r*bd-bn)*(u*v) := by nlinarith only [hp,b,l,n]
  exact (mul_le_mul_iff_left₀ (mul_pos hu hv)).mp final

theorem general_source_certificate {u d C D K J p q pd qd r r0 m A H c : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hA : K+C ≤ A) (hH : J+D ≤ H) (hc0 : 0 < c) (hc : c ≤ C*D)
    (hu : 0 < u) (hdil : 0 < d) (hr0 : 0 ≤ r0) (hr : r0 ≤ r) (hm : 0 ≤ m)
    (cert : 0 ≤ generalPolynomial u d r0 m A H c) :
    m ≤ r*signal (u/d) pd qd-signal u p q := by
  have A0 : 0 < A := by linarith only [hA,h.capture.total_pos,h.capture.kd_pos]
  have H0 : 0 < H := by linarith only [hH,h.detector.total_pos,h.detector.kd_pos]
  have low := (general_shared_bounds j hA hH).1
  have scaled := mul_le_mul_of_nonneg_right low (sq_nonneg d)
  have eq1 : C*D*(u/d)*d^2 = C*D*d*u := by field_simp
  have eq2 : ((u/d+A)*(u/d+H)*signal (u/d) pd qd)*d^2 =
      ((u+A*d)*(u+H*d))*signal (u/d) pd qd := by field_simp
  rw [eq1,eq2] at scaled
  have cert' : 0 ≤ c*r0*d*u^2-(c+m*u)*((u+A*d)*(u+H*d)) := by
    unfold generalPolynomial at cert
    linarith only [cert]
  have margin := general_algebra_margin hu (by positivity : 0 < (u+A*d)*(u+H*d)) hr0 hm hc0 hc
    scaled (general_shared_bounds h hA hH).2 cert'
  have drift := mul_le_mul_of_nonneg_right hr j.signal_nonneg
  linarith only [margin,drift]

theorem general_low_sign {u d C D K J p q pd qd r A H c uL dmin rmax : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hA : K+C ≤ A) (hH : J+D ≤ H) (hc : c ≤ C*D)
    (hu : u ≤ uL) (hdmin : 0 < dmin) (hd : dmin ≤ d) (hr0 : 0 ≤ r) (hr : r ≤ rmax)
    (cert : rmax*((uL+A)*(uL+H)) ≤ c*dmin) :
    r*signal (u/d) pd qd-signal u p q ≤ 0 := by
  have u0 := h.capture.x_nonneg
  have A0 : 0 < A := by linarith only [hA,h.capture.total_pos,h.capture.kd_pos]
  have H0 : 0 < H := by linarith only [hH,h.detector.total_pos,h.detector.kd_pos]
  have uL0 : 0 ≤ uL := le_trans u0 hu
  have rmax0 : 0 ≤ rmax := le_trans hr0 hr
  have bs := h.signal_nonneg
  have bt := j.signal_nonneg
  have low := (general_shared_bounds h hA hH).1
  have W : (u+A)*(u+H) ≤ (uL+A)*(uL+H) :=
    mul_le_mul (by linarith only [hu]) (by linarith only [hu]) (by positivity) (by positivity)
  have Wpos : 0 < (uL+A)*(uL+H) := by positivity
  have s1 := mul_le_mul_of_nonneg_right W bs
  have s2 := mul_le_mul_of_nonneg_right hc u0
  have cs : c*u ≤ (uL+A)*(uL+H)*signal u p q := by linarith only [low,s1,s2]
  have dpos : 0 < d := lt_of_lt_of_le hdmin hd
  have tb := (le_div_iff₀ dpos).mp j.signal_le_x
  have tb2 := mul_le_mul_of_nonneg_left hd bt
  have tb3 : dmin*signal (u/d) pd qd ≤ u := by linarith only [tb,tb2]
  have step1 := mul_le_mul_of_nonneg_left tb3 (mul_nonneg rmax0 Wpos.le)
  have step2 := mul_le_mul_of_nonneg_right cert u0
  have step3 := mul_le_mul_of_nonneg_left cs hdmin.le
  have key : ((uL+A)*(uL+H)*dmin)*(rmax*signal (u/d) pd qd) ≤
      ((uL+A)*(uL+H)*dmin)*signal u p q := by nlinarith only [step1,step2,step3]
  have key2 := le_of_mul_le_mul_left key (mul_pos Wpos hdmin)
  have rt := mul_le_mul_of_nonneg_right hr bt
  linarith only [key2,rt]

/-! ### Example A: capacities in `[9,11]`, dissociation constants at most `11/100`. -/

theorem capacity_high_lo {u : ℝ} (hl : 100 ≤ u) (hu : u ≤ 1000) :
    0 ≤ generalPolynomial u 9 (19/20) (2/5) (1111/100) (1111/100) 81 := by
  let t : ℝ := (u-100)/900
  have h0 : 0 ≤ t := by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 := by dsimp [t]; linarith only [hu]
  have identity : generalPolynomial u 9 (19/20) (2/5) (1111/100) (1111/100) 81 =
      (20859839879/10000)*(1-t)^3+3*(243201899759/10000)*t*(1-t)^2+3*(1576750559639/10000)*t^2*(1-t)+(1105505819519/10000)*t^3 := by
    dsimp [generalPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem capacity_high_hi {u : ℝ} (hl : 100 ≤ u) (hu : u ≤ 1000) :
    0 ≤ generalPolynomial u 11 (19/20) (2/5) (1111/100) (1111/100) 81 := by
  let t : ℝ := (u-100)/900
  have h0 : 0 ≤ t := by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 := by dsimp [t]; linarith only [hu]
  have identity : generalPolynomial u 11 (19/20) (2/5) (1111/100) (1111/100) 81 =
      (24898486239/10000)*(1-t)^3+3*(312191285319/10000)*t*(1-t)^2+3*(2078225484399/10000)*t^2*(1-t)+(2407001083479/10000)*t^3 := by
    dsimp [generalPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem capacity_high_polynomial {u d : ℝ} (hl : 100 ≤ u) (hu : u ≤ 1000)
    (hd0 : 9 ≤ d) (hd1 : d ≤ 11) :
    0 ≤ generalPolynomial u d (19/20) (2/5) (1111/100) (1111/100) 81 := by
  exact general_dilution_endpoints (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hd0 hd1 (capacity_high_lo hl hu) (capacity_high_hi hl hu)

theorem capacity_product {C D : ℝ} (hc : 9 ≤ C) (hd : 9 ≤ D) : 81 ≤ C*D := by
  nlinarith only [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hd),hc,hd]

theorem capacity_high {u d C D K J p q pd qd r : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc0 : 9 ≤ C) (hc1 : C ≤ 11) (hd0 : 9 ≤ D) (hd1 : D ≤ 11)
    (hk : K ≤ 11/100) (hj : J ≤ 11/100)
    (hl : 100 ≤ u) (hu : u ≤ 1000) (hdl : 9 ≤ d) (hdh : d ≤ 11) (hr : 19/20 ≤ r) :
    2/5 ≤ r*signal (u/d) pd qd-signal u p q := by
  exact general_source_certificate h j (by linarith only [hc1,hk]) (by linarith only [hd1,hj])
    (by norm_num) (capacity_product hc0 hd0) (by linarith) (by linarith)
    (by norm_num) hr (by norm_num) (capacity_high_polynomial hl hu hdl hdh)

theorem capacity_guard60_lo {u : ℝ} (hl : 60 ≤ u) (hu : u ≤ 1000) :
    0 ≤ generalPolynomial u 9 (19/20) (3/20) (1111/100) (1111/100) 81 := by
  let t : ℝ := (u-60)/940
  have h0 : 0 ≤ t := by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 := by dsimp [t]; linarith only [hu]
  have identity : generalPolynomial u 9 (19/20) (3/20) (1111/100) (1111/100) 81 =
      (189467991/1000)*(1-t)^3+3*(160028623863/10000)*t*(1-t)^2+3*(243938250477/1250)*t^2*(1-t)+(4130450819769/10000)*t^3 := by
    dsimp [generalPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem capacity_guard60_hi {u : ℝ} (hl : 60 ≤ u) (hu : u ≤ 1000) :
    0 ≤ generalPolynomial u 11 (19/20) (3/20) (1111/100) (1111/100) 81 := by
  let t : ℝ := (u-60)/940
  have h0 : 0 ≤ t := by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 := by dsimp [t]; linarith only [hu]
  have identity : generalPolynomial u 11 (19/20) (3/20) (1111/100) (1111/100) 81 =
      (59176431/1000)*(1-t)^3+3*(200486296783/10000)*t*(1-t)^2+3*(308422184157/1250)*t^2*(1-t)+(5555389293729/10000)*t^3 := by
    dsimp [generalPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem capacity_guard60_polynomial {u d : ℝ} (hl : 60 ≤ u) (hu : u ≤ 1000)
    (hd0 : 9 ≤ d) (hd1 : d ≤ 11) :
    0 ≤ generalPolynomial u d (19/20) (3/20) (1111/100) (1111/100) 81 := by
  exact general_dilution_endpoints (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hd0 hd1 (capacity_guard60_lo hl hu) (capacity_guard60_hi hl hu)

theorem capacity_guard60 {u d C D K J p q pd qd r : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc0 : 9 ≤ C) (hc1 : C ≤ 11) (hd0 : 9 ≤ D) (hd1 : D ≤ 11)
    (hk : K ≤ 11/100) (hj : J ≤ 11/100)
    (hl : 60 ≤ u) (hu : u ≤ 1000) (hdl : 9 ≤ d) (hdh : d ≤ 11) (hr : 19/20 ≤ r) :
    3/20 ≤ r*signal (u/d) pd qd-signal u p q := by
  exact general_source_certificate h j (by linarith only [hc1,hk]) (by linarith only [hd1,hj])
    (by norm_num) (capacity_product hc0 hd0) (by linarith) (by linarith)
    (by norm_num) hr (by norm_num) (capacity_guard60_polynomial hl hu hdl hdh)

theorem capacity_low_wide {u d C D K J p q pd qd r : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc0 : 9 ≤ C) (hc1 : C ≤ 11) (hd0 : 9 ≤ D) (hd1 : D ≤ 11)
    (hk : K ≤ 11/100) (hj : J ≤ 11/100)
    (hu : u ≤ 15) (hdl : 9 ≤ d) (hr0 : 0 ≤ r) (hr : r ≤ 21/20) :
    r*signal (u/d) pd qd-signal u p q ≤ 0 := by
  exact general_low_sign (A := 1111/100) (H := 1111/100) (c := 81) h j
    (by linarith only [hc1,hk]) (by linarith only [hd1,hj])
    (capacity_product hc0 hd0) hu (by norm_num) hdl hr0 hr (by norm_num)

theorem capacity_low {u d C D K J p q pd qd r : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc0 : 9 ≤ C) (hc1 : C ≤ 11) (hd0 : 9 ≤ D) (hd1 : D ≤ 11)
    (hk : K ≤ 11/100) (hj : J ≤ 11/100)
    (hu : u ≤ 1) (hdl : 9 ≤ d) (hr0 : 0 ≤ r) (hr : r ≤ 21/20) :
    r*signal (u/d) pd qd-signal u p q ≤ 0 := by
  exact capacity_low_wide h j hc0 hc1 hd0 hd1 hk hj (le_trans hu (by norm_num)) hdl hr0 hr

/-! ### Example B: unequal capacities `C ∈ [9,11]`, `D ∈ [18,22]`. -/

theorem unequal_high_lo {u : ℝ} (hl : 200 ≤ u) (hu : u ≤ 1000) :
    0 ≤ generalPolynomial u 9 (19/20) (4/5) (1111/100) (1111/50) 162 := by
  let t : ℝ := (u-200)/800
  have h0 : 0 ≤ t := by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 := by dsimp [t]; linarith only [hu]
  have identity : generalPolynomial u 9 (19/20) (4/5) (1111/100) (1111/50) 162 =
      (41918049839/2500)*(1-t)^3+3*(197023156399/2500)*t*(1-t)^2+3*(620461062959/2500)*t^2*(1-t)+(288231769519/2500)*t^3 := by
    dsimp [generalPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem unequal_high_hi {u : ℝ} (hl : 200 ≤ u) (hu : u ≤ 1000) :
    0 ≤ generalPolynomial u 11 (19/20) (4/5) (1111/100) (1111/50) 162 := by
  let t : ℝ := (u-200)/800
  have h0 : 0 ≤ t := by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 := by dsimp [t]; linarith only [hu]
  have identity : generalPolynomial u 11 (19/20) (4/5) (1111/100) (1111/50) 162 =
      (54016762599/2500)*(1-t)^3+3*(793546058677/7500)*t*(1-t)^2+3*(2637195429557/7500)*t^2*(1-t)+(873666133479/2500)*t^3 := by
    dsimp [generalPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem unequal_high_polynomial {u d : ℝ} (hl : 200 ≤ u) (hu : u ≤ 1000)
    (hd0 : 9 ≤ d) (hd1 : d ≤ 11) :
    0 ≤ generalPolynomial u d (19/20) (4/5) (1111/100) (1111/50) 162 := by
  exact general_dilution_endpoints (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hd0 hd1 (unequal_high_lo hl hu) (unequal_high_hi hl hu)

theorem unequal_product {C D : ℝ} (hc : 9 ≤ C) (hd : 18 ≤ D) : 162 ≤ C*D := by
  nlinarith only [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hd),hc,hd]

theorem unequal_high {u d C D K J p q pd qd r : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc0 : 9 ≤ C) (hc1 : C ≤ 11) (hd0 : 18 ≤ D) (hd1 : D ≤ 22)
    (hk : K ≤ 11/100) (hj : J ≤ 22/100)
    (hl : 200 ≤ u) (hu : u ≤ 1000) (hdl : 9 ≤ d) (hdh : d ≤ 11) (hr : 19/20 ≤ r) :
    4/5 ≤ r*signal (u/d) pd qd-signal u p q := by
  exact general_source_certificate h j (by linarith only [hc1,hk]) (by linarith only [hd1,hj])
    (by norm_num) (unequal_product hc0 hd0) (by linarith) (by linarith)
    (by norm_num) hr (by norm_num) (unequal_high_polynomial hl hu hdl hdh)

theorem unequal_low_wide {u d C D K J p q pd qd r : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc0 : 9 ≤ C) (hc1 : C ≤ 11) (hd0 : 18 ≤ D) (hd1 : D ≤ 22)
    (hk : K ≤ 11/100) (hj : J ≤ 22/100)
    (hu : u ≤ 20) (hdl : 9 ≤ d) (hr0 : 0 ≤ r) (hr : r ≤ 21/20) :
    r*signal (u/d) pd qd-signal u p q ≤ 0 := by
  exact general_low_sign (A := 1111/100) (H := 1111/50) (c := 162) h j
    (by linarith only [hc1,hk]) (by linarith only [hd1,hj])
    (unequal_product hc0 hd0) hu (by norm_num) hdl hr0 hr (by norm_num)

theorem unequal_low {u d C D K J p q pd qd r : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc0 : 9 ≤ C) (hc1 : C ≤ 11) (hd0 : 18 ≤ D) (hd1 : D ≤ 22)
    (hk : K ≤ 11/100) (hj : J ≤ 22/100)
    (hu : u ≤ 1) (hdl : 9 ≤ d) (hr0 : 0 ≤ r) (hr : r ≤ 21/20) :
    r*signal (u/d) pd qd-signal u p q ≤ 0 := by
  exact unequal_low_wide h j hc0 hc1 hd0 hd1 hk hj (le_trans hu (by norm_num)) hdl hr0 hr

/-! ### Relative (multiplicative) read-out error on the original unit box. -/

theorem relative_error_high_lo {u : ℝ} (hl : 20 ≤ u) (hu : u ≤ 100) :
    0 ≤ marginPolynomial u 9 (1843/2060) (3/100) := by
  let t : ℝ := (u-20)/80
  have h0 : 0 ≤ t := by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 := by dsimp [t]; linarith only [hu]
  have identity : marginPolynomial u 9 (1843/2060) (3/100) =
      (96648177/2575)*(1-t)^3+3*(791044737/2575)*t*(1-t)^2+3*(2981865297/2575)*t^2*(1-t)+(2713909857/2575)*t^3 := by
    dsimp [marginPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem relative_error_high_hi {u : ℝ} (hl : 20 ≤ u) (hu : u ≤ 100) :
    0 ≤ marginPolynomial u 11 (1843/2060) (3/100) := by
  let t : ℝ := (u-20)/80
  have h0 : 0 ≤ t := by dsimp [t]; linarith only [hl]
  have h1 : t ≤ 1 := by dsimp [t]; linarith only [hu]
  have identity : marginPolynomial u 11 (1843/2060) (3/100) =
      (111738657/2575)*(1-t)^3+3*(1042884017/2575)*t*(1-t)^2+3*(4121605377/2575)*t^2*(1-t)+(5392702737/2575)*t^3 := by
    dsimp [marginPolynomial,t]; ring
  rw [identity]
  exact bernstein_nonneg h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem relative_error_high_polynomial {u d : ℝ} (hl : 20 ≤ u) (hu : u ≤ 100)
    (hd0 : 9 ≤ d) (hd1 : d ≤ 11) :
    0 ≤ marginPolynomial u d (1843/2060) (3/100) := by
  exact dilution_endpoints (by linarith) (by norm_num) (by norm_num) hd0 hd1
    (relative_error_high_lo hl hu) (relative_error_high_hi hl hu)

theorem relative_error_high {u d C D K J p q pd qd r : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hl : 20 ≤ u) (hu : u ≤ 100) (hd0 : 9 ≤ d) (hd1 : d ≤ 11)
    (hr : 1843/2060 ≤ r) : 3/100 ≤ r*signal (u/d) pd qd-signal u p q := by
  exact source_certificate h j hc hd hk hj (by linarith) (by linarith)
    (by norm_num) hr (by norm_num) (relative_error_high_polynomial hl hu hd0 hd1)

theorem relative_error_low {u d C D K J p q pd qd r : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hu : u ≤ 1/10) (hd0 : 9 ≤ d) (hr0 : 0 ≤ r) (hr : r ≤ 2163/1940) :
    r*signal (u/d) pd qd-signal u p q ≤ 0 := by
  have prod : (81/100:ℝ) ≤ C*D := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hc.1) (sub_nonneg.mpr hd.1),hc.1,hd.1]
  exact general_low_sign (A := 11/5) (H := 11/5) (c := 81/100) h j
    (by linarith only [hc.2,hk.2]) (by linarith only [hd.2,hj.2])
    prod hu (by norm_num) hd0 hr0 hr (by norm_num)

theorem near_unit_low_wide {u d C D K J p q pd qd r : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hu : u ≤ 2/5) (hd0 : 9 ≤ d) (hr0 : 0 ≤ r) (hr : r ≤ 21/20) :
    r*signal (u/d) pd qd-signal u p q ≤ 0 := by
  have prod : (81/100:ℝ) ≤ C*D := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hc.1) (sub_nonneg.mpr hd.1),hc.1,hd.1]
  exact general_low_sign (A := 11/5) (H := 11/5) (c := 81/100) h j
    (by linarith only [hc.2,hk.2]) (by linarith only [hd.2,hj.2])
    prod hu (by norm_num) hd0 hr0 hr (by norm_num)

theorem uniform_tail_margin {u d C D K J p q pd qd r : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hl : 20 ≤ u) (hd0 : 9 ≤ d) (hd1 : d ≤ 11) (hr : 19/20 ≤ r) :
    7371/8000 ≤ u*(r*signal (u/d) pd qd-signal u p q) := by
  have u0 : 0 < u := by linarith only [hl]
  have dpos : 0 < d := by linarith only [hd0]
  have bt := j.signal_nonneg
  have low := (shared_source_bounds j hc hd hk hj).1
  have scaled := mul_le_mul_of_nonneg_right low (sq_nonneg d)
  have eq1 : C*D*(u/d)*d^2 = C*D*d*u := by field_simp
  have eq2 : ((u/d+11/5)^2*signal (u/d) pd qd)*d^2 =
      (u+11/5*d)^2*signal (u/d) pd qd := by field_simp
  rw [eq1,eq2] at scaled
  have p9 : 0 ≤ 4*9*u^2-9*(u+11/5*9)^2 := by
    nlinarith only [hl,sq_nonneg (u-20)]
  have p11 : 0 ≤ 4*11*u^2-9*(u+11/5*11)^2 := by
    nlinarith only [hl,sq_nonneg (u-20)]
  have quad : 9*(u+11/5*d)^2 ≤ 4*d*u^2 := by
    have a := mul_nonneg (sub_nonneg.mpr hd1) p9
    have b := mul_nonneg (sub_nonneg.mpr hd0) p11
    have e := mul_nonneg (sub_nonneg.mpr hd0) (sub_nonneg.mpr hd1)
    nlinarith only [a,b,e]
  have k1 := mul_le_mul_of_nonneg_right quad bt
  have k2 : (d*u)*(9*(C*D)) ≤ (d*u)*(4*(u*signal (u/d) pd qd)) := by
    nlinarith only [k1,scaled]
  have k3 := le_of_mul_le_mul_left k2 (mul_pos dpos u0)
  have prod : (81/100:ℝ) ≤ C*D := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hc.1) (sub_nonneg.mpr hd.1),hc.1,hd.1]
  have up := (shared_source_bounds h hc hd hk hj).2
  have rb := mul_le_mul_of_nonneg_right hr (mul_nonneg u0.le bt)
  nlinarith only [k3,prod,up,rb]

theorem relative_error_reduction {g r b ξ1 ξd η rlo rhi : ℝ}
    (h1 : |ξ1| ≤ η) (hd : |ξd| ≤ η) (hη : η < 1)
    (hrlo : 0 ≤ rlo) (hr0 : rlo ≤ r) (hr1 : r ≤ rhi) :
    g*r*b*(1+ξd) = (g*(1+ξ1))*(r*(1+ξd)/(1+ξ1))*b ∧
    rlo*(1-η)/(1+η) ≤ r*(1+ξd)/(1+ξ1) ∧
    r*(1+ξd)/(1+ξ1) ≤ rhi*(1+η)/(1-η) := by
  have a1 := abs_le.mp h1
  have ad := abs_le.mp hd
  have pos1 : 0 < 1+ξ1 := by linarith only [a1.1,hη]
  have posd : 0 ≤ 1+ξd := by linarith only [ad.1,hη]
  have eta0 : 0 < 1-η := by linarith only [hη]
  have eta1 : 0 < 1+η := by linarith only [a1.1,a1.2]
  have r0 : 0 ≤ r := le_trans hrlo hr0
  have rhi0 : 0 ≤ rhi := le_trans r0 hr1
  refine ⟨?_, ?_, ?_⟩
  · field_simp
  · apply (div_le_div_iff₀ eta1 pos1).2
    exact mul_le_mul (mul_le_mul hr0 (by linarith only [ad.1]) eta0.le r0)
      (by linarith only [a1.2]) pos1.le (mul_nonneg r0 posd)
  · apply (div_le_div_iff₀ pos1 eta0).2
    exact mul_le_mul (mul_le_mul hr1 (by linarith only [ad.2]) posd rhi0)
      (by linarith only [a1.1]) eta0.le (mul_nonneg rhi0 eta1.le)

theorem relative_error_gain {g gmin ξ1 η : ℝ}
    (hg : gmin ≤ g) (hg0 : 0 ≤ gmin) (h1 : |ξ1| ≤ η) (hη : η ≤ 1) :
    gmin*(1-η) ≤ g*(1+ξ1) := by
  have a1 := abs_le.mp h1
  exact mul_le_mul hg (by linarith only [a1.1]) (by linarith only [hη]) (le_trans hg0 hg)

theorem relative_error_noisy_high {u d C D K J p q pd qd r g gmin ξ1 ξd a1 ad eps : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hl : 20 ≤ u) (hu : u ≤ 100) (hd0 : 9 ≤ d) (hd1 : d ≤ 11) (hr : 19/20 ≤ r)
    (hg : gmin ≤ g) (hg0 : 0 ≤ gmin) (hξ1 : |ξ1| ≤ 3/100) (hξd : |ξd| ≤ 3/100)
    (ha1 : |a1| ≤ eps) (had : |ad| ≤ eps) :
    gmin*(97/100)*(3/100)-2*eps ≤
      (g*r*signal (u/d) pd qd*(1+ξd)+ad)-(g*signal u p q*(1+ξ1)+a1) := by
  obtain ⟨eqn,lo,_⟩ := relative_error_reduction (g := g) (b := signal (u/d) pd qd)
    hξ1 hξd (by norm_num) (by norm_num : (0:ℝ) ≤ 19/20) hr (le_refl r)
  have lo' : (1843/2060:ℝ) ≤ r*(1+ξd)/(1+ξ1) := le_trans (by norm_num) lo
  have margin := relative_error_high h j hc hd hk hj hl hu hd0 hd1 lo'
  have gain := relative_error_gain hg hg0 hξ1 (by norm_num)
  have gain' : gmin*(97/100) ≤ g*(1+ξ1) := by linarith only [gain]
  have nm := noisy_margin gain' (by positivity : 0 ≤ gmin*(97/100)) (by norm_num)
    margin ha1 had
  linarith only [nm,eqn]

theorem relative_error_noisy_low {u d C D K J p q pd qd r g ξ1 ξd a1 ad eps : ℝ}
    (h : Reaction u C D K J p q) (j : Reaction (u/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hu : u ≤ 1/10) (hd0 : 9 ≤ d) (hr0 : 0 ≤ r) (hr : r ≤ 21/20)
    (hg : 0 ≤ g) (hξ1 : |ξ1| ≤ 3/100) (hξd : |ξd| ≤ 3/100)
    (ha1 : |a1| ≤ eps) (had : |ad| ≤ eps) :
    (g*r*signal (u/d) pd qd*(1+ξd)+ad)-(g*signal u p q*(1+ξ1)+a1) ≤ 2*eps := by
  obtain ⟨eqn,lo,hi⟩ := relative_error_reduction (g := g) (b := signal (u/d) pd qd)
    hξ1 hξd (by norm_num) (le_refl (0:ℝ)) hr0 hr
  have lo' : 0 ≤ r*(1+ξd)/(1+ξ1) := le_trans (by norm_num) lo
  have hi' : r*(1+ξd)/(1+ξ1) ≤ 2163/1940 := le_trans hi (by norm_num)
  have sign := relative_error_low h j hc hd hk hj hu hd0 lo' hi'
  have g' : 0 ≤ g*(1+ξ1) := mul_nonneg hg (by linarith only [(abs_le.mp hξ1).1])
  have m := mul_nonneg g' (neg_nonneg.mpr sign)
  have e1 := abs_le.mp ha1
  have ed := abs_le.mp had
  nlinarith only [m,eqn,e1.1,ed.2]

/-! ### Native-sample windows and the end-to-end Example A contrast. -/

theorem native_window {x rho Hn U rmin : ℝ}
    (hx0 : Hn ≤ x) (hx1 : x ≤ U) (hH : 0 ≤ Hn)
    (hr0 : rmin ≤ rho) (hr1 : rho ≤ 1) (hrmin : 0 ≤ rmin) :
    rmin*Hn ≤ rho*x ∧ rho*x ≤ U := by
  have xp : 0 ≤ x := le_trans hH hx0
  constructor
  · exact mul_le_mul hr0 hx0 hH (le_trans hrmin hr0)
  · nlinarith only [mul_le_mul_of_nonneg_right hr1 xp,hx1]

theorem capacity_noisy_high {x rho d C D K J p q pd qd r g gmin e1 ed eps : ℝ}
    (h : Reaction (rho*x) C D K J p q) (j : Reaction (rho*x/d) C D K J pd qd)
    (hc0 : 9 ≤ C) (hc1 : C ≤ 11) (hd0 : 9 ≤ D) (hd1 : D ≤ 11)
    (hk : K ≤ 11/100) (hj : J ≤ 11/100)
    (hx0 : 125 ≤ x) (hx1 : x ≤ 1000) (hrho0 : 4/5 ≤ rho) (hrho1 : rho ≤ 1)
    (hdl : 9 ≤ d) (hdh : d ≤ 11) (hr : 19/20 ≤ r)
    (hg : gmin ≤ g) (hg0 : 0 ≤ gmin) (he1 : |e1| ≤ eps) (hed : |ed| ≤ eps) :
    gmin*(2/5)-2*eps ≤
      (g*r*signal (rho*x/d) pd qd+ed)-(g*signal (rho*x) p q+e1) := by
  have w := native_window hx0 hx1 (by norm_num) hrho0 hrho1 (by norm_num)
  have wl : 100 ≤ rho*x := le_trans (by norm_num) w.1
  exact noisy_margin hg hg0 (by norm_num)
    (capacity_high h j hc0 hc1 hd0 hd1 hk hj wl w.2 hdl hdh hr) he1 hed

theorem capacity_noisy_low {x rho d C D K J p q pd qd r g e1 ed eps : ℝ}
    (h : Reaction (rho*x) C D K J p q) (j : Reaction (rho*x/d) C D K J pd qd)
    (hc0 : 9 ≤ C) (hc1 : C ≤ 11) (hd0 : 9 ≤ D) (hd1 : D ≤ 11)
    (hk : K ≤ 11/100) (hj : J ≤ 11/100)
    (hx1 : x ≤ 15) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hdl : 9 ≤ d) (hr0 : 0 ≤ r) (hr : r ≤ 21/20)
    (hg : 0 ≤ g) (he1 : |e1| ≤ eps) (hed : |ed| ≤ eps) :
    (g*r*signal (rho*x/d) pd qd+ed)-(g*signal (rho*x) p q+e1) ≤ 2*eps := by
  have wu : rho*x ≤ 15 := by
    nlinarith only [mul_le_mul_of_nonneg_left hx1 hrho0,hrho1]
  have sign := capacity_low_wide h j hc0 hc1 hd0 hd1 hk hj wu hdl hr0 hr
  have m := mul_nonneg hg (neg_nonneg.mpr sign)
  have a1 := abs_le.mp he1
  have ad := abs_le.mp hed
  nlinarith only [m,a1.1,ad.2]

end SandwichImmunoassay
