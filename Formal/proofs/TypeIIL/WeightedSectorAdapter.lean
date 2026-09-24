import proofs.TypeIIL.SecantSectorReduction

namespace TypeIIL

/-- A pair of adjacent compressed weighted arcs and the intervening fork
secant produce one exact cyclic three-current row.  The same hypotheses also
give the positive cross determinant and the strict next-arc gain needed by
the cyclic closure argument. -/
theorem weighted_sector_row_and_invariants
    (aPrev bPrev aNext bNext : WeightedChainSummary)
    {dRPrev dPPrev dQPrev dRNext dPNext dQNext : ℝ}
    {kPlus kMinus U V : ℝ} {mPrev m : ℕ}
    {deltaPrev delta deltaNext RPrev P Q RNext PNext QNext : ℝ}
    (hdRPrev : 0 < dRPrev) (hdPPrev : 0 < dPPrev)
    (hdQPrev : 0 < dQPrev)
    (hdRNext : 0 < dRNext) (hdPNext : 0 < dPNext)
    (hdQNext : 0 < dQNext)
    (hkPlus : 0 < kPlus) (hkMinus : 0 < kMinus) (hV : 0 < V)
    (hmPrev : 0 < mPrev) (hm : 0 < m)
    (hPrev : WeightedArcSteady aPrev bPrev dRPrev dPPrev dQPrev mPrev
      deltaPrev delta RPrev P Q)
    (hNext : WeightedArcSteady aNext bNext dRNext dPNext dQNext m
      delta deltaNext RNext PNext QNext)
    (hFork : delta = kPlus * Q - kMinus * (U * P + V * RNext)) :
    secantSectorA kPlus kMinus U
        (weightedArcQUp aPrev bPrev dRPrev dPPrev dQPrev mPrev)
        (weightedArcPUp aPrev bPrev dRPrev dPPrev dQPrev mPrev) * deltaPrev =
      secantSectorB kPlus kMinus U V
          (weightedArcQNext aPrev bPrev dRPrev dPPrev dQPrev)
          (weightedArcPLocal aPrev bPrev dRPrev dPPrev dQPrev)
          (weightedArcRUp aNext bNext dRNext dPNext dQNext m) * delta +
        secantSectorC kMinus V
          (weightedArcRLocal aNext bNext dRNext dPNext dQNext) * deltaNext ∧
    0 < secantSectorA kPlus kMinus U
          (weightedArcQUp aPrev bPrev dRPrev dPPrev dQPrev mPrev)
          (weightedArcPUp aPrev bPrev dRPrev dPPrev dQPrev mPrev) *
        weightedArcPLocal aPrev bPrev dRPrev dPPrev dQPrev +
      weightedArcPUp aPrev bPrev dRPrev dPPrev dQPrev mPrev *
        secantSectorB kPlus kMinus U V
          (weightedArcQNext aPrev bPrev dRPrev dPPrev dQPrev)
          (weightedArcPLocal aPrev bPrev dRPrev dPPrev dQPrev)
          (weightedArcRUp aNext bNext dRNext dPNext dQNext m) ∧
    0 < secantSectorC kMinus V
          (weightedArcRLocal aNext bNext dRNext dPNext dQNext) ∧
    secantSectorC kMinus V
        (weightedArcRLocal aNext bNext dRNext dPNext dQNext) <
      kMinus * V *
        weightedArcRUp aNext bNext dRNext dPNext dQNext m := by
  rcases weighted_arc_response aPrev bPrev hdRPrev hdPPrev hdQPrev hmPrev hPrev
    with ⟨hRPrev, hP, hQ⟩
  rcases weighted_arc_response aNext bNext hdRNext hdPNext hdQNext hm hNext
    with ⟨hRNext, hPNext, hQNext⟩
  have hrow := secant_sector_reduction hP hQ hRNext hFork
  have hcross := weighted_secant_sector_cross_pos
    aPrev bPrev aNext bNext (U := U) hdRPrev hdPPrev hdQPrev
      hdRNext hdPNext hdQNext hkPlus hkMinus hV hmPrev hm
  have hgain := weighted_secant_sector_next_gain
    aNext bNext hdRNext hdPNext hdQNext hkMinus hV hm
  exact ⟨hrow, hcross, hgain.1, hgain.2⟩

end TypeIIL
