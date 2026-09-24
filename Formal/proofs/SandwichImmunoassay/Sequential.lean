import proofs.SandwichImmunoassay.Robust

namespace SandwichImmunoassay

/-! ### Ideal capture–wash–detect model.

Capture stage: `Occupancy u C K p`, captured amount `u*p`.  Detection stage acts on the
captured amount: `Occupancy (u*p) D J q`, and the signal is `u*p*q = signal u p q`. -/

theorem Occupancy.captured_lt {u C K p : ℝ} (h : Occupancy u C K p) : u*p < C := by
  rw [h.balance]
  have hp := h.pos
  have hk := h.kd_pos
  have h1 : 0 < 1-p := sub_pos.mpr h.lt_one
  have : 0 < K*p/(1-p) := by positivity
  linarith only [this]

theorem Occupancy.captured_le_total {u C K p : ℝ} (h : Occupancy u C K p) : u*p ≤ u := by
  have free := mul_nonneg h.x_nonneg (sub_nonneg.mpr h.lt_one.le)
  nlinarith only [free]

theorem Occupancy.captured_quadratic {u C K p : ℝ} (h : Occupancy u C K p) :
    (C-u*p)*(u-u*p) = K*(u*p) := by
  linear_combination u*h.polynomial

theorem Occupancy.captured_strictMono {u1 u2 C K p1 p2 : ℝ}
    (h1 : Occupancy u1 C K p1) (h2 : Occupancy u2 C K p2) (hu : u1 < u2) :
    u1*p1 < u2*p2 := by
  by_contra hn
  have hle := not_lt.mp hn
  have q1 := h1.captured_quadratic
  have q2 := h2.captured_quadratic
  have a2 : 0 < C-u2*p2 := sub_pos.mpr h2.captured_lt
  have b1 : 0 ≤ u1-u1*p1 := sub_nonneg.mpr h1.captured_le_total
  have s1 : (C-u1*p1)*(u1-u1*p1) ≤ (C-u2*p2)*(u1-u1*p1) :=
    mul_le_mul_of_nonneg_right (by linarith only [hle]) b1
  have s2 : (C-u2*p2)*(u1-u1*p1) < (C-u2*p2)*(u2-u2*p2) :=
    mul_lt_mul_of_pos_left (by linarith only [hle,hu]) a2
  have lt : K*(u1*p1) < K*(u2*p2) := by linarith only [q1,q2,s1,s2]
  have := lt_of_mul_lt_mul_left lt h1.kd_pos.le
  linarith only [this,hle]

theorem Occupancy.captured_lipschitz {u1 u2 C K p1 p2 : ℝ}
    (h1 : Occupancy u1 C K p1) (h2 : Occupancy u2 C K p2) (hu : u1 ≤ u2) :
    u2*p2-u1*p1 ≤ u2-u1 := by
  by_contra hn
  have hlt := not_le.mp hn
  have q1 := h1.captured_quadratic
  have q2 := h2.captured_quadratic
  have a1 : 0 < C-u1*p1 := sub_pos.mpr h1.captured_lt
  have b2 : 0 ≤ u2-u2*p2 := sub_nonneg.mpr h2.captured_le_total
  have s1 : (C-u2*p2)*(u2-u2*p2) ≤ (C-u1*p1)*(u2-u2*p2) :=
    mul_le_mul_of_nonneg_right (by linarith only [hlt,hu]) b2
  have s2 : (C-u1*p1)*(u2-u2*p2) < (C-u1*p1)*(u1-u1*p1) :=
    mul_lt_mul_of_pos_left (by linarith only [hlt]) a1
  have lt : K*(u2*p2) < K*(u1*p1) := by linarith only [q1,q2,s1,s2]
  have := lt_of_mul_lt_mul_left lt h1.kd_pos.le
  linarith only [this,hlt,hu]

/-- Sequential (capture, wash, detect) equilibrium: the detector sees only the captured
amount `u*p`. -/
structure Sequential (u C D K J p q : ℝ) : Prop where
  capture : Occupancy u C K p
  detect : Occupancy (u*p) D J q

theorem sequential_exists {u C D K J : ℝ} (hu : 0 ≤ u)
    (hc : 0 < C) (hd : 0 < D) (hk : 0 < K) (hj : 0 < J) :
    ∃ p q, Sequential u C D K J p q := by
  obtain ⟨p,hp⟩ := occupancy_exists hu hc hk
  obtain ⟨q,hq⟩ := occupancy_exists (mul_nonneg hu hp.pos.le) hd hj
  exact ⟨p,q,hp,hq⟩

theorem sequential_strictMono {u1 u2 C D K J p1 p2 q1 q2 : ℝ}
    (h1 : Sequential u1 C D K J p1 q1) (h2 : Sequential u2 C D K J p2 q2) (hu : u1 < u2) :
    signal u1 p1 q1 < signal u2 p2 q2 := by
  unfold signal
  exact h1.detect.captured_strictMono h2.detect (h1.capture.captured_strictMono h2.capture hu)

theorem sequential_below_plateau {u C D K J p q qinf : ℝ}
    (h : Sequential u C D K J p q) (hinf : Occupancy C D J qinf) :
    signal u p q < C*qinf := by
  unfold signal
  exact h.detect.captured_strictMono hinf h.capture.captured_lt

theorem sequential_plateau_gap {u C D K J p q qinf : ℝ}
    (h : Sequential u C D K J p q) (hinf : Occupancy C D J qinf) (hu : C < u) :
    C*qinf-signal u p q ≤ K*C/(u-C) := by
  have wl := h.capture.captured_lt
  have lip := h.detect.captured_lipschitz hinf wl.le
  have quad := h.capture.captured_quadratic
  have kp := h.capture.kd_pos
  have gap : C-u*p ≤ K*C/(u-C) := by
    rw [le_div_iff₀ (sub_pos.mpr hu)]
    have s1 := mul_le_mul_of_nonneg_left (show u-C ≤ u-u*p by linarith only [wl])
      (sub_nonneg.mpr wl.le)
    have s2 := mul_le_mul_of_nonneg_left wl.le kp.le
    linarith only [quad,s1,s2]
  unfold signal
  linarith only [lip,gap]

/-! ### Imperfect wash: carry-over of `a` units of unbound analyte into the detection stage. -/

theorem carryover_retention {w a D J q0 qa : ℝ}
    (h0 : Occupancy w D J q0) (ha : Occupancy (w+a) D J qa) (ha0 : 0 ≤ a) :
    qa ≤ q0 ∧ D*q0 ≤ (D+a*q0)*qa ∧ D*(w*q0) ≤ (D+a)*(w*qa) := by
  have P0 := h0.polynomial
  have Pa := ha.polynomial
  have w0 := h0.x_nonneg
  have jp := h0.kd_pos
  have q0p := h0.pos
  have qap := ha.pos
  have s0 : 0 < 1-q0 := sub_pos.mpr h0.lt_one
  have sa : 0 < 1-qa := sub_pos.mpr ha.lt_one
  have mono : qa ≤ q0 := by
    by_contra hn
    have gt := sub_pos.mpr (not_le.mp hn)
    have coef : 0 < D+J+w-w*(q0+qa) := by
      nlinarith only [h0.total_bound,mul_nonneg w0 sa.le,jp]
    have prod : (qa-q0)*(D+J+w-w*(q0+qa)) = -(a*qa*(1-qa)) := by
      linear_combination P0-Pa
    have pos := mul_pos gt coef
    have carry : 0 ≤ a*qa*(1-qa) := mul_nonneg (mul_nonneg ha0 qap.le) sa.le
    linarith only [prod,pos,carry]
  have second : D*q0 ≤ (D+a*q0)*qa := by
    have identity : (D*q0-(D+a*q0)*qa)*((1-q0)*(1-qa)) = J*q0*qa*(qa-q0) := by
      linear_combination (q0*(1-q0))*Pa-(qa*(1-qa))*P0
    by_contra hn
    have gt := sub_pos.mpr (not_le.mp hn)
    have pos := mul_pos gt (mul_pos s0 sa)
    have sign := mul_nonneg (mul_nonneg (mul_nonneg jp.le q0p.le) qap.le) (sub_nonneg.mpr mono)
    linarith only [identity,pos,sign]
  refine ⟨mono,second,?_⟩
  have t1 := mul_le_mul_of_nonneg_left second w0
  have t2 := mul_nonneg (mul_nonneg (mul_nonneg w0 ha0) qap.le) s0.le
  nlinarith only [t1,t2]

theorem wash_specification {w a D J q0 qa β : ℝ}
    (h0 : Occupancy w D J q0) (ha : Occupancy (w+a) D J qa) (ha0 : 0 ≤ a)
    (hβ : 0 ≤ β) (spec : a*β ≤ D*(1-β)) :
    β*(w*q0) ≤ w*qa := by
  have third := (carryover_retention h0 ha ha0).2.2
  have wq : 0 ≤ w*qa := mul_nonneg h0.x_nonneg ha.pos.le
  have t1 := mul_le_mul_of_nonneg_left third hβ
  have t2 := mul_le_mul_of_nonneg_right spec wq
  have scaled : D*(β*(w*q0)) ≤ D*(w*qa) := by nlinarith only [t1,t2]
  exact le_of_mul_le_mul_left scaled h0.total_pos

theorem wash_900 {w a D J q0 qa : ℝ}
    (h0 : Occupancy w D J q0) (ha : Occupancy (w+a) D J qa) (ha0 : 0 ≤ a)
    (hD : 10 ≤ D) (hcarry : a ≤ 10/9) :
    (9/10)*(w*q0) ≤ w*qa := by
  exact wash_specification h0 ha ha0 (by norm_num) (by linarith only [hD,hcarry])

theorem carryover_tail {u C D K J p qa lam : ℝ}
    (h : Occupancy u C K p) (ha : Occupancy (u*p+lam*(u-u*p)) D J qa)
    (hlam : 0 ≤ lam) (hu : C ≤ u) :
    (u*p*qa)*(lam*(u-C)) ≤ C*D := by
  have cp := h.total_pos
  have qp := ha.pos
  have wC := h.total_bound
  have tb := ha.total_bound
  have a0 : 0 ≤ lam*(u-C) := mul_nonneg hlam (sub_nonneg.mpr hu)
  have a1 : lam*(u-C) ≤ lam*(u-u*p) :=
    mul_le_mul_of_nonneg_left (by linarith only [wC]) hlam
  have s1 : (u*p*qa)*(lam*(u-C)) ≤ (C*qa)*(lam*(u-u*p)) :=
    mul_le_mul (mul_le_mul_of_nonneg_right wC qp.le) a1 a0 (mul_nonneg cp.le qp.le)
  have t1 := mul_le_mul_of_nonneg_left tb cp.le
  have t2 : 0 ≤ C*(u*p*qa) :=
    mul_nonneg cp.le (mul_nonneg (mul_nonneg h.x_nonneg h.pos.le) qp.le)
  nlinarith only [s1,t1,t2]

end SandwichImmunoassay
