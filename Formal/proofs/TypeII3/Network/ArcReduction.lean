import proofs.TypeII3.Network.Canonical

namespace TypeII3

noncomputable def arcTheta (a : ArcRates) : ℝ := a.dQ / (a.eta + a.dQ)
noncomputable def arcH (a : ArcRates) : ℝ :=
  a.beta + a.dP + a.gamma * arcTheta a
noncomputable def arcD (a : ArcRates) : ℝ :=
  (a.c + a.dR) * arcH a - a.beta * a.c

noncomputable def arcPUp (a : ArcRates) (m : ℕ) : ℝ := a.c * m / arcD a
noncomputable def arcPLocal (a : ArcRates) : ℝ :=
  (a.c + a.dR) * arcTheta a / arcD a
noncomputable def arcQUp (a : ArcRates) (m : ℕ) : ℝ :=
  a.gamma * a.c * m / ((a.eta + a.dQ) * arcD a)
noncomputable def arcQLocal (a : ArcRates) : ℝ :=
  (a.beta * a.dR + (a.c + a.dR) * a.dP) /
    ((a.eta + a.dQ) * arcD a)
noncomputable def arcRUp (a : ArcRates) (m : ℕ) : ℝ :=
  arcH a * m / arcD a
noncomputable def arcRLocal (a : ArcRates) : ℝ :=
  a.beta * arcTheta a / arcD a

theorem arcTheta_pos (a : ArcRates) : 0 < arcTheta a := by
  unfold arcTheta
  exact div_pos a.dQ_pos (add_pos a.eta_pos a.dQ_pos)

theorem arcTheta_lt_one (a : ArcRates) : arcTheta a < 1 := by
  unfold arcTheta
  rw [div_lt_one (add_pos a.eta_pos a.dQ_pos)]
  linarith [a.eta_pos]

theorem arcH_pos (a : ArcRates) : 0 < arcH a := by
  unfold arcH
  exact add_pos (add_pos a.beta_pos a.dP_pos)
    (mul_pos a.gamma_pos (arcTheta_pos a))

theorem arcD_pos (a : ArcRates) : 0 < arcD a := by
  have ht := arcTheta_pos a
  have hident :
      arcD a = a.c * a.dP + a.c * a.gamma * arcTheta a +
        a.dR * a.beta + a.dR * a.dP + a.dR * a.gamma * arcTheta a := by
    unfold arcD arcH
    ring
  rw [hident]
  exact add_pos
    (add_pos
      (add_pos
        (add_pos (mul_pos a.c_pos a.dP_pos)
          (mul_pos (mul_pos a.c_pos a.gamma_pos) ht))
        (mul_pos a.dR_pos a.beta_pos))
      (mul_pos a.dR_pos a.dP_pos))
    (mul_pos (mul_pos a.dR_pos a.gamma_pos) ht)

theorem arc_coefficients_pos (a : ArcRates) {m : ℕ} (hm : 0 < m) :
    0 < arcPUp a m ∧ 0 < arcPLocal a ∧
    0 < arcQUp a m ∧ 0 < arcQLocal a ∧
    0 < arcRUp a m ∧ 0 < arcRLocal a := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ht := arcTheta_pos a
  have hH := arcH_pos a
  have hD := arcD_pos a
  unfold arcPUp arcPLocal arcQUp arcQLocal arcRUp arcRLocal
  constructor
  · exact div_pos (mul_pos a.c_pos hmR) hD
  constructor
  · exact div_pos (mul_pos (add_pos a.c_pos a.dR_pos) ht) hD
  constructor
  · exact div_pos (mul_pos (mul_pos a.gamma_pos a.c_pos) hmR)
      (mul_pos (add_pos a.eta_pos a.dQ_pos) hD)
  constructor
  · exact div_pos
      (add_pos (mul_pos a.beta_pos a.dR_pos)
        (mul_pos (add_pos a.c_pos a.dR_pos) a.dP_pos))
      (mul_pos (add_pos a.eta_pos a.dQ_pos) hD)
  constructor
  · exact div_pos (mul_pos hH hmR) hD
  · exact div_pos (mul_pos a.beta_pos ht) hD

/-- The upstream response of an arc strictly dominates its local response.
This is the physical gain that rules out the alternating mode on even cycles. -/
theorem arcRLocal_lt_arcRUp (a : ArcRates) {m : ℕ} (hm : 0 < m) :
    arcRLocal a < arcRUp a m := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ht0 := arcTheta_pos a
  have ht1 := arcTheta_lt_one a
  have hH := arcH_pos a
  have hnum : a.beta * arcTheta a < arcH a * (m : ℝ) := by
    have hb : a.beta * arcTheta a < a.beta := by nlinarith [a.beta_pos]
    have hbetaH : a.beta < arcH a := by
      unfold arcH
      nlinarith [a.dP_pos, mul_pos a.gamma_pos ht0]
    have hHm : arcH a ≤ arcH a * (m : ℝ) := by nlinarith
    exact lt_of_lt_of_le (lt_trans hb hbetaH) hHm
  unfold arcRLocal arcRUp
  exact (div_lt_div_iff_of_pos_right (arcD_pos a)).2 hnum

theorem arc_response
    (a : ArcRates) {m : ℕ} {delta deltaNext R P Q : ℝ}
    (hsteady : ArcSteady a m delta deltaNext R P Q) :
    R = arcRUp a m * delta + arcRLocal a * deltaNext ∧
    P = arcPUp a m * delta + arcPLocal a * deltaNext ∧
    Q = arcQUp a m * delta - arcQLocal a * deltaNext := by
  rcases hsteady with ⟨hR, hP, hQ⟩
  have heta : a.eta + a.dQ ≠ 0 := ne_of_gt (add_pos a.eta_pos a.dQ_pos)
  have hD : arcD a ≠ 0 := ne_of_gt (arcD_pos a)
  have hmid :
      a.c * R - arcH a * P + arcTheta a * deltaNext = 0 := by
    unfold arcH arcTheta
    field_simp [heta]
    linear_combination (a.eta + a.dQ) * hP + a.eta * hQ
  have hPformula : P = arcPUp a m * delta + arcPLocal a * deltaNext := by
    have hnum :
        arcD a * P = a.c * m * delta + (a.c + a.dR) * arcTheta a * deltaNext := by
      unfold arcD
      linear_combination -a.c * hR - (a.c + a.dR) * hmid
    calc
      P = (a.c * m * delta + (a.c + a.dR) * arcTheta a * deltaNext) /
          arcD a := (eq_div_iff hD).2 (by simpa [mul_comm] using hnum)
      _ = arcPUp a m * delta + arcPLocal a * deltaNext := by
        unfold arcPUp arcPLocal
        ring
  have hRformula : R = arcRUp a m * delta + arcRLocal a * deltaNext := by
    have hnum :
        arcD a * R = arcH a * m * delta + a.beta * arcTheta a * deltaNext := by
      unfold arcD
      linear_combination -arcH a * hR - a.beta * hmid
    calc
      R = (arcH a * m * delta + a.beta * arcTheta a * deltaNext) /
          arcD a := (eq_div_iff hD).2 (by simpa [mul_comm] using hnum)
      _ = arcRUp a m * delta + arcRLocal a * deltaNext := by
        unfold arcRUp arcRLocal
        ring
  have hQsimple : Q = (a.gamma * P - deltaNext) / (a.eta + a.dQ) := by
    apply (eq_div_iff heta).2
    linear_combination -hQ
  have hQformula : Q = arcQUp a m * delta - arcQLocal a * deltaNext := by
    rw [hQsimple, hPformula]
    unfold arcQUp arcQLocal arcPUp arcPLocal arcTheta
    field_simp [heta, hD]
    unfold arcD arcH arcTheta
    field_simp [heta]
    ring
  exact ⟨hRformula, hPformula, hQformula⟩

end TypeII3
