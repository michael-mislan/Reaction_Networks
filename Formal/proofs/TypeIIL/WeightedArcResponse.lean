import proofs.TypeIIL.WeightedArcGain

namespace TypeIIL

/-- Three endpoint balances after both weighted chains have been compressed. -/
def WeightedArcSteady (a b : WeightedChainSummary)
    (dR dP dQ : ℝ) (m : ℕ)
    (delta deltaNext R P Q : ℝ) : Prop :=
  m * delta - ((a.cL + a.leakL) * R - a.betaL * P) - dR * R = 0 ∧
  (a.cR * R - (a.betaR + a.leakR) * P) -
      ((b.cL + b.leakL) * P - b.betaL * Q) - dP * P + deltaNext = 0 ∧
  b.cR * P - (b.betaR + b.leakR) * Q - dQ * Q - deltaNext = 0

/-- Exact `R,P,Q` response for an arbitrary pair of compressed weighted
chains.  Unlike the unit case, `weightedArcQNext` is intentionally signed. -/
theorem weighted_arc_response
    (a b : WeightedChainSummary) {dR dP dQ : ℝ} {m : ℕ}
    {delta deltaNext R P Q : ℝ}
    (hdR : 0 < dR) (hdP : 0 < dP) (hdQ : 0 < dQ) (hm : 0 < m)
    (h : WeightedArcSteady a b dR dP dQ m delta deltaNext R P Q) :
    R = weightedArcRUp a b dR dP dQ m * delta +
          weightedArcRLocal a b dR dP dQ * deltaNext ∧
    P = weightedArcPUp a b dR dP dQ m * delta +
          weightedArcPLocal a b dR dP dQ * deltaNext ∧
    Q = weightedArcQUp a b dR dP dQ m * delta +
          weightedArcQNext a b dR dP dQ * deltaNext := by
  rcases h with ⟨hR, hP, hQ⟩
  let B := weightedArcB b dQ
  let sigma := weightedArcSigma b dQ
  let H := weightedArcH a b dP dQ
  let C := weightedArcC a dR
  let D := weightedArcD a b dR dP dQ
  have hBpos : 0 < B := by
    dsimp [B, weightedArcB]
    exact add_pos (add_pos_of_pos_of_nonneg b.betaR_pos b.leakR_nonneg) hdQ
  have hB : B ≠ 0 := ne_of_gt hBpos
  have hDpos : 0 < D := by
    simpa [D] using
      (weighted_arc_denominator_and_gain a b hdR hdP hdQ hm).1
  have hD : D ≠ 0 := ne_of_gt hDpos
  have hQsimple : Q = (b.cR * P - deltaNext) / B := by
    apply (eq_div_iff hB).2
    dsimp [B, weightedArcB]
    linear_combination -hQ
  have hmid : H * P = a.cR * R + sigma * deltaNext := by
    change (a.betaR + a.leakR + b.cL + b.leakL + dP -
        b.betaL * b.cR / B) * P =
      a.cR * R + (1 - b.betaL / B) * deltaNext
    dsimp [B, weightedArcB] at hB ⊢
    field_simp [hB]
    linear_combination -((b.betaR + b.leakR + dQ) * hP + b.betaL * hQ)
  have hRbalance : C * R = m * delta + a.betaL * P := by
    dsimp [C, weightedArcC]
    linarith [hR]
  have hRnum : D * R = H * m * delta + a.betaL * sigma * deltaNext := by
    calc
      D * R = H * (C * R) - a.betaL * a.cR * R := by
        dsimp [D, weightedArcD]
        ring
      _ = H * (m * delta + a.betaL * P) - a.betaL * a.cR * R := by
        rw [hRbalance]
      _ = H * m * delta + a.betaL * (H * P - a.cR * R) := by ring
      _ = H * m * delta + a.betaL * sigma * deltaNext := by rw [hmid]; ring
  have hPnum : D * P = a.cR * m * delta + C * sigma * deltaNext := by
    calc
      D * P = C * (H * P) - a.betaL * a.cR * P := by
        dsimp [D, weightedArcD]
        ring
      _ = C * (a.cR * R + sigma * deltaNext) - a.betaL * a.cR * P := by
        rw [hmid]
      _ = a.cR * (C * R - a.betaL * P) + C * sigma * deltaNext := by ring
      _ = a.cR * m * delta + C * sigma * deltaNext := by rw [hRbalance]; ring
  have hRformula : R = weightedArcRUp a b dR dP dQ m * delta +
      weightedArcRLocal a b dR dP dQ * deltaNext := by
    have hrdiv : R = (H * m * delta + a.betaL * sigma * deltaNext) / D :=
      (eq_div_iff hD).2 (by simpa [mul_comm] using hRnum)
    rw [hrdiv]
    unfold weightedArcRUp weightedArcRLocal
    dsimp [D, H, sigma]
    ring
  have hPformula : P = weightedArcPUp a b dR dP dQ m * delta +
      weightedArcPLocal a b dR dP dQ * deltaNext := by
    have hpdiv : P = (a.cR * m * delta + C * sigma * deltaNext) / D :=
      (eq_div_iff hD).2 (by simpa [mul_comm] using hPnum)
    rw [hpdiv]
    unfold weightedArcPUp weightedArcPLocal
    dsimp [D, C, sigma]
    ring
  have hQformula : Q = weightedArcQUp a b dR dP dQ m * delta +
      weightedArcQNext a b dR dP dQ * deltaNext := by
    rw [hQsimple, hPformula]
    unfold weightedArcQUp weightedArcQNext
    dsimp [B]
    field_simp [hB]
    ring
  exact ⟨hRformula, hPformula, hQformula⟩

end TypeIIL
