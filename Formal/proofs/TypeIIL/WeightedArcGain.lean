import proofs.TypeIIL.WeightedChain

namespace TypeIIL

noncomputable def weightedArcB (b : WeightedChainSummary) (dQ : ℝ) : ℝ :=
  b.betaR + b.leakR + dQ

noncomputable def weightedArcSigma (b : WeightedChainSummary) (dQ : ℝ) : ℝ :=
  1 - b.betaL / weightedArcB b dQ

noncomputable def weightedArcH (a b : WeightedChainSummary) (dP dQ : ℝ) : ℝ :=
  a.betaR + a.leakR + b.cL + b.leakL + dP -
    b.betaL * b.cR / weightedArcB b dQ

noncomputable def weightedArcC (a : WeightedChainSummary) (dR : ℝ) : ℝ :=
  a.cL + a.leakL + dR

noncomputable def weightedArcD (a b : WeightedChainSummary)
    (dR dP dQ : ℝ) : ℝ :=
  weightedArcC a dR * weightedArcH a b dP dQ - a.betaL * a.cR

noncomputable def weightedArcRUp (a b : WeightedChainSummary)
    (dR dP dQ : ℝ) (m : ℕ) : ℝ :=
  weightedArcH a b dP dQ * m / weightedArcD a b dR dP dQ

noncomputable def weightedArcRLocal (a b : WeightedChainSummary)
    (dR dP dQ : ℝ) : ℝ :=
  a.betaL * weightedArcSigma b dQ / weightedArcD a b dR dP dQ

noncomputable def weightedArcPUp (a b : WeightedChainSummary)
    (dR dP dQ : ℝ) (m : ℕ) : ℝ :=
  a.cR * m / weightedArcD a b dR dP dQ

noncomputable def weightedArcPLocal (a b : WeightedChainSummary)
    (dR dP dQ : ℝ) : ℝ :=
  weightedArcC a dR * weightedArcSigma b dQ /
    weightedArcD a b dR dP dQ

noncomputable def weightedArcQUp (a b : WeightedChainSummary)
    (dR dP dQ : ℝ) (m : ℕ) : ℝ :=
  b.cR * weightedArcPUp a b dR dP dQ m / weightedArcB b dQ

/-- Signed coefficient in `Q = qUp * delta + qNext * deltaNext`. -/
noncomputable def weightedArcQNext (a b : WeightedChainSummary)
    (dR dP dQ : ℝ) : ℝ :=
  b.cR * weightedArcPLocal a b dR dP dQ / weightedArcB b dQ -
    1 / weightedArcB b dQ

theorem weighted_arc_denominator_and_gain
    (a b : WeightedChainSummary) {dR dP dQ : ℝ} {m : ℕ}
    (hdR : 0 < dR) (hdP : 0 < dP) (hdQ : 0 < dQ) (hm : 0 < m) :
    0 < weightedArcD a b dR dP dQ ∧
    0 < weightedArcRLocal a b dR dP dQ ∧
    weightedArcRLocal a b dR dP dQ <
      weightedArcRUp a b dR dP dQ m := by
  let B := weightedArcB b dQ
  let sigma := weightedArcSigma b dQ
  let H := weightedArcH a b dP dQ
  let C := weightedArcC a dR
  let D := weightedArcD a b dR dP dQ
  have hB : 0 < B := by
    dsimp [B, weightedArcB]
    exact add_pos (add_pos_of_pos_of_nonneg b.betaR_pos b.leakR_nonneg) hdQ
  have hbetaB : b.betaL < B := by
    dsimp [B, weightedArcB]
    nlinarith [b.reverse_gain, b.leakR_nonneg]
  have hbetaRB : b.betaR < B := by
    dsimp [B, weightedArcB]
    nlinarith [b.leakR_nonneg]
  have hsigma : 0 < sigma := by
    dsimp [sigma, weightedArcSigma]
    exact sub_pos.mpr ((div_lt_one hB).2 hbetaB)
  have hsigma_lt : sigma < 1 := by
    dsimp [sigma, weightedArcSigma]
    exact sub_lt_self _ (div_pos b.betaL_pos hB)
  have htransport :
      0 < b.cL + b.leakL - b.betaL * b.cR / B := by
    have hstrict : b.betaL * b.cR < (b.cL + b.leakL) * B := by
      have hcB : b.cL * b.betaR < b.cL * B :=
        mul_lt_mul_of_pos_left hbetaRB b.cL_pos
      have hcouple : b.betaL * b.cR ≤ b.cL * b.betaR := b.coupling
      have hbase : b.betaL * b.cR < b.cL * B := lt_of_le_of_lt hcouple hcB
      have hleak : 0 ≤ b.leakL * B :=
        mul_nonneg b.leakL_nonneg (le_of_lt hB)
      nlinarith
    rw [sub_pos, div_lt_iff₀ hB]
    simpa [mul_comm] using hstrict
  have hHbeta : a.betaR < H := by
    dsimp [H, weightedArcH]
    nlinarith [a.leakR_nonneg, hdP, htransport]
  have hH : 0 < H := lt_trans a.betaR_pos hHbeta
  have hCleft : a.cL < C := by
    dsimp [C, weightedArcC]
    nlinarith [a.leakL_nonneg]
  have hC : 0 < C := lt_trans a.cL_pos hCleft
  have hprod : a.betaL * a.cR < C * H := by
    have h1 : a.cL * a.betaR < C * a.betaR :=
      mul_lt_mul_of_pos_right hCleft a.betaR_pos
    have h2 : C * a.betaR < C * H :=
      mul_lt_mul_of_pos_left hHbeta hC
    exact lt_of_le_of_lt a.coupling (lt_trans h1 h2)
  have hD : 0 < D := by
    dsimp [D, weightedArcD]
    exact sub_pos.mpr hprod
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnum : a.betaL * sigma < H * (m : ℝ) := by
    have hsmall : a.betaL * sigma < a.betaL := by
      nlinarith [a.betaL_pos, hsigma_lt]
    have habetaH : a.betaL < H :=
      lt_of_le_of_lt a.reverse_gain hHbeta
    have hHm : H ≤ H * (m : ℝ) := by nlinarith
    exact lt_of_lt_of_le (lt_trans hsmall habetaH) hHm
  constructor
  · exact hD
  constructor
  · unfold weightedArcRLocal
    exact div_pos (mul_pos a.betaL_pos hsigma) hD
  · unfold weightedArcRLocal weightedArcRUp
    exact (div_lt_div_iff_of_pos_right hD).2 hnum

/-- Although `weightedArcQNext` may have either sign, the fork-reduced
transfer always has positive cross determinant.  The cancellation identity
is `qUp*pLocal-qNext*pUp = pUp/B`. -/
theorem weighted_arc_transfer_cross_pos
    (a b : WeightedChainSummary) {dR dP dQ kPlus : ℝ} {m : ℕ}
    (hdR : 0 < dR) (hdP : 0 < dP) (hdQ : 0 < dQ)
    (hkPlus : 0 < kPlus) (hm : 0 < m) :
    0 < (kPlus * weightedArcQUp a b dR dP dQ m) *
          weightedArcPLocal a b dR dP dQ +
        weightedArcPUp a b dR dP dQ m *
          (1 - kPlus * weightedArcQNext a b dR dP dQ) := by
  have hgain := weighted_arc_denominator_and_gain a b hdR hdP hdQ hm
  have hD : 0 < weightedArcD a b dR dP dQ := hgain.1
  have hB : 0 < weightedArcB b dQ := by
    unfold weightedArcB
    exact add_pos (add_pos_of_pos_of_nonneg b.betaR_pos b.leakR_nonneg) hdQ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : 0 < weightedArcPUp a b dR dP dQ m := by
    unfold weightedArcPUp
    exact div_pos (mul_pos a.cR_pos hmR) hD
  have hid :
      weightedArcQUp a b dR dP dQ m *
          weightedArcPLocal a b dR dP dQ -
        weightedArcQNext a b dR dP dQ *
          weightedArcPUp a b dR dP dQ m =
        weightedArcPUp a b dR dP dQ m / weightedArcB b dQ := by
    unfold weightedArcQUp weightedArcQNext
    field_simp [ne_of_gt hB]
    ring
  calc
    (kPlus * weightedArcQUp a b dR dP dQ m) *
          weightedArcPLocal a b dR dP dQ +
        weightedArcPUp a b dR dP dQ m *
          (1 - kPlus * weightedArcQNext a b dR dP dQ) =
      weightedArcPUp a b dR dP dQ m + kPlus *
        (weightedArcQUp a b dR dP dQ m *
            weightedArcPLocal a b dR dP dQ -
          weightedArcQNext a b dR dP dQ *
            weightedArcPUp a b dR dP dQ m) := by ring
    _ = weightedArcPUp a b dR dP dQ m +
        kPlus * (weightedArcPUp a b dR dP dQ m /
          weightedArcB b dQ) := by rw [hid]
    _ > 0 := add_pos hp (mul_pos hkPlus (div_pos hp hB))

end TypeIIL
