import proofs.TypeIIL.WeightedArcResponse
import proofs.TypeIIL.MassActionForkSecant

namespace TypeIIL

def secantSectorA (kPlus kMinus U qUp pUp : ℝ) : ℝ :=
  kPlus * qUp - kMinus * U * pUp

def secantSectorB
    (kPlus kMinus U V qNext pLocal rUp : ℝ) : ℝ :=
  1 - kPlus * qNext + kMinus * U * pLocal + kMinus * V * rUp

def secantSectorC (kMinus V rLocal : ℝ) : ℝ := kMinus * V * rLocal

/-- Exact homogeneous three-current equation obtained from endpoint response
formulas and the fork-product secant identity. -/
theorem secant_sector_reduction
    {kPlus kMinus U V qUp qNext pUp pLocal rUp rLocal : ℝ}
    {deltaPrev delta deltaNext P Q R : ℝ}
    (hP : P = pUp * deltaPrev + pLocal * delta)
    (hQ : Q = qUp * deltaPrev + qNext * delta)
    (hR : R = rUp * delta + rLocal * deltaNext)
    (hFork : delta = kPlus * Q - kMinus * (U * P + V * R)) :
    secantSectorA kPlus kMinus U qUp pUp * deltaPrev =
      secantSectorB kPlus kMinus U V qNext pLocal rUp * delta +
        secantSectorC kMinus V rLocal * deltaNext := by
  rw [hP, hQ, hR] at hFork
  unfold secantSectorA secantSectorB secantSectorC
  linear_combination -hFork

/-- The dangerous first fork-secant coefficient cancels from the cross
determinant; only a strictly positive next-arc contribution remains. -/
theorem secant_sector_cross_pos
    {kPlus kMinus U V qUp qNext pUp pLocal rUp : ℝ}
    (hpUp : 0 < pUp) (hrUp : 0 < rUp)
    (hkMinus : 0 < kMinus) (hV : 0 < V)
    (hArcCross : 0 < (kPlus * qUp) * pLocal +
      pUp * (1 - kPlus * qNext)) :
    0 < secantSectorA kPlus kMinus U qUp pUp * pLocal +
      pUp * secantSectorB kPlus kMinus U V qNext pLocal rUp := by
  unfold secantSectorA secantSectorB
  exact fork_secant_cross_pos hpUp hrUp hkMinus hV hArcCross

theorem secant_sector_next_gain
    {kMinus V rUp rLocal : ℝ}
    (hkMinus : 0 < kMinus) (hV : 0 < V)
    (hrLocal : 0 < rLocal) (hgain : rLocal < rUp) :
    0 < secantSectorC kMinus V rLocal ∧
      secantSectorC kMinus V rLocal < kMinus * V * rUp := by
  unfold secantSectorC
  exact fork_secant_next_gain hkMinus hV hrLocal hgain

/-- Weighted-chain response coefficients instantiate the abstract cross
invariant, using one arc for `P,Q` and the cyclicly next arc for `R`. -/
theorem weighted_secant_sector_cross_pos
    (a b aNext bNext : WeightedChainSummary)
    {dR dP dQ dRNext dPNext dQNext kPlus kMinus U V : ℝ}
    {mPrev m : ℕ}
    (hdR : 0 < dR) (hdP : 0 < dP) (hdQ : 0 < dQ)
    (hdRNext : 0 < dRNext) (hdPNext : 0 < dPNext)
    (hdQNext : 0 < dQNext)
    (hkPlus : 0 < kPlus) (hkMinus : 0 < kMinus) (hV : 0 < V)
    (hmPrev : 0 < mPrev) (hm : 0 < m) :
    0 < secantSectorA kPlus kMinus U
          (weightedArcQUp a b dR dP dQ mPrev)
          (weightedArcPUp a b dR dP dQ mPrev) *
        weightedArcPLocal a b dR dP dQ +
      weightedArcPUp a b dR dP dQ mPrev *
        secantSectorB kPlus kMinus U V
          (weightedArcQNext a b dR dP dQ)
          (weightedArcPLocal a b dR dP dQ)
          (weightedArcRUp aNext bNext dRNext dPNext dQNext m) := by
  have hArcCross := weighted_arc_transfer_cross_pos
    a b hdR hdP hdQ hkPlus hmPrev
  have hD := (weighted_arc_denominator_and_gain a b hdR hdP hdQ hmPrev).1
  have hmR : (0 : ℝ) < mPrev := by exact_mod_cast hmPrev
  have hpUp : 0 < weightedArcPUp a b dR dP dQ mPrev := by
    unfold weightedArcPUp
    exact div_pos (mul_pos a.cR_pos hmR) hD
  have hnext := weighted_arc_denominator_and_gain
    aNext bNext hdRNext hdPNext hdQNext hm
  have hrUp : 0 < weightedArcRUp aNext bNext dRNext dPNext dQNext m :=
    lt_trans hnext.2.1 hnext.2.2
  exact secant_sector_cross_pos hpUp hrUp hkMinus hV hArcCross

theorem weighted_secant_sector_next_gain
    (aNext bNext : WeightedChainSummary)
    {dR dP dQ kMinus V : ℝ} {m : ℕ}
    (hdR : 0 < dR) (hdP : 0 < dP) (hdQ : 0 < dQ)
    (hkMinus : 0 < kMinus) (hV : 0 < V) (hm : 0 < m) :
    0 < secantSectorC kMinus V
        (weightedArcRLocal aNext bNext dR dP dQ) ∧
      secantSectorC kMinus V
          (weightedArcRLocal aNext bNext dR dP dQ) <
        kMinus * V * weightedArcRUp aNext bNext dR dP dQ m := by
  have hg := weighted_arc_denominator_and_gain aNext bNext hdR hdP hdQ hm
  exact secant_sector_next_gain hkMinus hV hg.2.1 hg.2.2

end TypeIIL
