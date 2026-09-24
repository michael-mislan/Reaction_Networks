import proofs.SandwichImmunoassay.Source

namespace SandwichImmunoassay

def InBox (a : ℝ) : Prop := 9/10 ≤ a ∧ a ≤ 11/10

theorem Occupancy.box_lower {x C K p : ℝ} (h : Occupancy x C K p)
    (hc : InBox C) (hk : InBox K) : 9/10 ≤ (x+11/5)*p := by
  have hh := (div_le_iff₀ (by linarith [h.x_nonneg,h.kd_pos,h.total_pos] : 0<x+K+C)).1 h.bounds.1
  have hp := h.pos
  rcases hc with ⟨hc0,hc1⟩
  rcases hk with ⟨_,hk1⟩
  nlinarith [mul_nonneg hp.le (show 0 ≤ 11/5-K-C by linarith)]

theorem Occupancy.total_bound {x C K p : ℝ} (h : Occupancy x C K p) : x*p ≤ C := by
  rw [h.balance]
  have hp := h.pos
  have hk := h.kd_pos
  have h1 : 0 < 1-p := sub_pos.mpr h.lt_one
  have : 0 ≤ K*p/(1-p) := by positivity
  linarith

theorem Reaction.box_bounds {x C D K J p q : ℝ}
    (h : Reaction x C D K J p q)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J) :
    (81/100)*x ≤ (x+11/5)^2 * signal x p q ∧
    x * signal x p q ≤ 121/100 := by
  have hx := h.capture.x_nonneg
  have hp := h.capture.pos
  have hq := h.detector.pos
  have a := h.capture.box_lower hc hk
  have b := h.detector.box_lower hd hj
  have prod := mul_le_mul a b (by norm_num : (0:ℝ) ≤ 9/10) (by positivity : 0 ≤ (x+11/5)*p)
  have low := mul_le_mul_of_nonneg_left prod hx
  have c := h.capture.total_bound
  have d := h.detector.total_bound
  have c' : x*p ≤ 11/10 := le_trans c hc.2
  have d' : x*q ≤ 11/10 := le_trans d hd.2
  have upper := mul_le_mul c' d' (by positivity : 0 ≤ x*q) (by norm_num : (0:ℝ) ≤ 11/10)
  dsimp [signal]
  constructor <;> nlinarith

theorem low_source_margin {x d C D K J p q pd qd r : ℝ}
    (h : Reaction x C D K J p q) (j : Reaction (x/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hx : x ≤ 1/10) (hdil : 9 ≤ d) (hr : r ≤ 21/20) :
    r * signal (x/d) pd qd - signal x p q ≤ 0 := by
  have x0 := h.capture.x_nonneg
  have bs := h.signal_nonneg
  have bt := j.signal_nonneg
  have lb := (h.box_bounds hc hd hk hj).1
  have coeff : (x+11/5)^2 ≤ 529/100 := by nlinarith
  have lhs := mul_le_mul_of_nonneg_right coeff bs
  have low : (3/20)*x ≤ signal x p q := by nlinarith
  have tbound := j.signal_le_x
  have dpos : 0 < d := by linarith
  have xd : x/d ≤ x/9 := (div_le_div_iff₀ dpos (by norm_num)).2 (by nlinarith)
  have tb : signal (x/d) pd qd ≤ x/9 := le_trans tbound xd
  have rb := mul_le_mul hr tb bt (by norm_num : (0:ℝ) ≤ 21/20)
  nlinarith

theorem high_source_bounds {x d C D K J p q pd qd : ℝ}
    (h : Reaction x C D K J p q) (j : Reaction (x/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hx : 20 ≤ x) (hd0 : 9 ≤ d) (hd1 : d ≤ 11) :
    7/5 ≤ x * signal (x/d) pd qd ∧ x * signal x p q ≤ 121/100 := by
  have x0 : 0 < x := by linarith
  have d0 : 0 < d := by linarith
  have bt := j.signal_nonneg
  have lb := (j.box_bounds hc hd hk hj).1
  have mult := mul_le_mul_of_nonneg_right lb (sq_nonneg d)
  have identity : (x/d+11/5)^2*d^2 = (x+11/5*d)^2 := by field_simp
  have identity2 : (81/100)*(x/d)*d^2 = (81/100)*x*d := by field_simp
  have lbd : (81/100)*x*d ≤ (x+11/5*d)^2 * signal (x/d) pd qd := by
    calc
      _ = (81/100)*(x/d)*d^2 := identity2.symm
      _ ≤ ((x/d+11/5)^2 * signal (x/d) pd qd)*d^2 := mult
      _ = _ := by rw [mul_assoc, mul_comm (signal (x/d) pd qd), ← mul_assoc, identity]
  have small : x+11/5*d ≤ (221/100)*x := by linarith
  have large : 0 ≤ x+11/5*d := by positivity
  have sqb : (x+11/5*d)^2 ≤ (49/10)*x^2 := by
    nlinarith [sq_nonneg ((221/100)*x-(x+11/5*d)),
      mul_nonneg (show 0 ≤ (221/100)*x-(x+11/5*d) by linarith)
        (show 0 ≤ (221/100)*x+(x+11/5*d) by positivity)]
  have sqmul := mul_le_mul_of_nonneg_right sqb bt
  have xd : (729/100)*x ≤ (81/100)*x*d := by nlinarith
  have final : (7/5)*x ≤ x*(x*signal (x/d) pd qd) := by nlinarith
  constructor
  · nlinarith
  · exact (h.box_bounds hc hd hk hj).2

theorem high_source_margin {x d C D K J p q pd qd r : ℝ}
    (h : Reaction x C D K J p q) (j : Reaction (x/d) C D K J pd qd)
    (hc : InBox C) (hd : InBox D) (hk : InBox K) (hj : InBox J)
    (hx0 : 20 ≤ x) (hx1 : x ≤ 100) (hd0 : 9 ≤ d) (hd1 : d ≤ 11)
    (hr : 19/20 ≤ r) :
    3/2500 ≤ r*signal (x/d) pd qd-signal x p q := by
  have bounds := high_source_bounds h j hc hd hk hj hx0 hd0 hd1
  have bt := j.signal_nonneg
  have rbound := mul_le_mul_of_nonneg_right hr bt
  have x0 : 0 < x := by linarith
  have rb := mul_le_mul_of_nonneg_left rbound x0.le
  have pos : 0 ≤ r*signal (x/d) pd qd-signal x p q := by nlinarith [bounds.1,bounds.2]
  have top := mul_le_mul_of_nonneg_right hx1 pos
  nlinarith [bounds.1,bounds.2]

end SandwichImmunoassay
