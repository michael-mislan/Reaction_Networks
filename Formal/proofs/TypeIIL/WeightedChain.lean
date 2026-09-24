import Mathlib

namespace TypeIIL

/-- Boundary response of a linear chain whose reactions may deliver an
integer multiple of their product species. -/
structure WeightedChainSummary where
  cL : ℝ
  betaL : ℝ
  cR : ℝ
  betaR : ℝ
  leakL : ℝ
  leakR : ℝ
  cL_pos : 0 < cL
  betaL_pos : 0 < betaL
  cR_pos : 0 < cR
  betaR_pos : 0 < betaR
  leakL_nonneg : 0 ≤ leakL
  leakR_nonneg : 0 ≤ leakR
  coupling : betaL * cR ≤ cL * betaR
  reverse_gain : betaL ≤ betaR

/-- A positive linear reaction `X → sY` has current `cX-betaY`; `s`
copies of that current arrive at `Y`.  Extension inserts a positively
degraded intermediate.  These are precisely the equations obtained by
secant-linearizing a weighted mass-action chain between two positive states. -/
inductive LinearWeightedChain where
  | direct (c beta : ℝ) (s : ℕ)
      (c_pos : 0 < c) (beta_pos : 0 < beta) (s_pos : 0 < s)
  | extend (q : LinearWeightedChain) (c beta : ℝ) (s : ℕ) (d : ℝ)
      (c_pos : 0 < c) (beta_pos : 0 < beta) (s_pos : 0 < s) (d_pos : 0 < d)

def LinearWeightedChain.State : LinearWeightedChain → Type
  | .direct _ _ _ _ _ _ => PUnit
  | .extend q _ _ _ _ _ _ _ _ => q.State × ℝ

noncomputable def LinearWeightedChain.summary :
    LinearWeightedChain → WeightedChainSummary
  | .direct c beta s hc hb hs => by
      have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
      exact
        { cL := c, betaL := beta, cR := s * c, betaR := s * beta
          leakL := 0, leakR := 0
          cL_pos := hc, betaL_pos := hb
          cR_pos := mul_pos (by exact_mod_cast hs) hc
          betaR_pos := mul_pos (by exact_mod_cast hs) hb
          leakL_nonneg := le_rfl, leakR_nonneg := le_rfl
          coupling := by ring_nf; exact le_rfl
          reverse_gain := by nlinarith }
  | .extend q c beta s d hc hb hs hd => by
      let a := q.summary
      let A := a.betaR + a.leakR + d
      let L := A + c
      have hA : 0 < A := by
        dsimp [A]
        exact add_pos (add_pos_of_pos_of_nonneg a.betaR_pos a.leakR_nonneg) hd
      have hL : 0 < L := add_pos hA hc
      have hsR : (0 : ℝ) < s := by exact_mod_cast hs
      have hcross : 0 ≤ a.cL * A - a.betaL * a.cR := by
        dsimp [A]
        nlinarith [a.coupling,
          mul_nonneg (le_of_lt a.cL_pos) a.leakR_nonneg,
          mul_pos a.cL_pos hd]
      have hcLnum : 0 < a.cL * L - a.betaL * a.cR := by
        dsimp [L]
        nlinarith [hcross, mul_pos a.cL_pos hc]
      let cL' := (a.cL * L - a.betaL * a.cR) / L
      let betaL' := a.betaL * beta / L
      let cR' := (s : ℝ) * c * a.cR / L
      let betaR' := (s : ℝ) * beta * A / L
      have hbase : a.betaL * c * a.cR ≤
          (a.cL * L - a.betaL * a.cR) * A := by
        have hfac : 0 ≤ L * (a.cL * A - a.betaL * a.cR) :=
          mul_nonneg (le_of_lt hL) hcross
        dsimp [L]
        nlinarith
      have hcoupling : betaL' * cR' ≤ cL' * betaR' := by
        have hmul := mul_le_mul_of_nonneg_left hbase
          (le_of_lt (mul_pos hsR hb))
        dsimp [betaL', cR', cL', betaR']
        have hL2 : 0 < L ^ 2 := sq_pos_of_pos hL
        rw [show (a.betaL * beta / L) * ((s : ℝ) * c * a.cR / L) =
              (a.betaL * beta * ((s : ℝ) * c * a.cR)) / L ^ 2 by
              field_simp [ne_of_gt hL],
            show ((a.cL * L - a.betaL * a.cR) / L) *
                ((s : ℝ) * beta * A / L) =
              ((a.cL * L - a.betaL * a.cR) * ((s : ℝ) * beta * A)) /
                L ^ 2 by
              field_simp [ne_of_gt hL]]
        apply (div_le_div_iff_of_pos_right hL2).2
        convert hmul using 1 <;> ring
      have hreverse : betaL' ≤ betaR' := by
        have hA' : a.betaL ≤ A := by
          dsimp [A]
          nlinarith [a.reverse_gain, a.leakR_nonneg, hd]
        have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
        have : a.betaL ≤ (s : ℝ) * A := by nlinarith [hA]
        dsimp [betaL', betaR']
        apply (div_le_div_iff_of_pos_right hL).2
        convert mul_le_mul_of_nonneg_right this (le_of_lt hb) using 1
        all_goals ring
      exact
        { cL := cL', betaL := betaL', cR := cR', betaR := betaR'
          leakL := a.leakL, leakR := 0
          cL_pos := div_pos hcLnum hL
          betaL_pos := div_pos (mul_pos a.betaL_pos hb) hL
          cR_pos := div_pos (mul_pos (mul_pos hsR hc) a.cR_pos) hL
          betaR_pos := div_pos (mul_pos (mul_pos hsR hb) hA) hL
          leakL_nonneg := a.leakL_nonneg, leakR_nonneg := le_rfl
          coupling := hcoupling, reverse_gain := hreverse }

/-- `LinearWeightedChainFlux q z X Y jL jR` records the current leaving
the left endpoint and the stoichiometrically delivered current entering the
right endpoint. -/
def LinearWeightedChainFlux :
    (q : LinearWeightedChain) → q.State → ℝ → ℝ → ℝ → ℝ → Prop
  | .direct c beta s _ _ _, _, X, Y, jL, jR =>
      jL = c * X - beta * Y ∧ jR = s * (c * X - beta * Y)
  | .extend q c beta s d _ _ _ _, z, X, Y, jL, jR =>
      ∃ jMid jEdge,
        LinearWeightedChainFlux q z.1 X z.2 jL jMid ∧
        jEdge = c * z.2 - beta * Y ∧
        jMid - jEdge - d * z.2 = 0 ∧
        jR = s * jEdge

/-- Exact boundary compression for a linear weighted chain. -/
theorem linear_weighted_chain_flux_compress
    (q : LinearWeightedChain) (z : q.State) {X Y jL jR : ℝ}
    (h : LinearWeightedChainFlux q z X Y jL jR) :
    let a := q.summary
    jL = (a.cL + a.leakL) * X - a.betaL * Y ∧
    jR = a.cR * X - (a.betaR + a.leakR) * Y := by
  induction q generalizing X Y jL jR with
  | direct c beta s hc hb hs =>
      rcases h with ⟨hL, hR⟩
      constructor
      · simpa [LinearWeightedChain.summary] using hL
      · simp only [LinearWeightedChain.summary]
        rw [hR]
        ring
  | extend q c beta s d hc hb hs hd ih =>
      rcases z with ⟨z, Z⟩
      rcases h with ⟨jMid, jEdge, hq, hedge, hZ, hout⟩
      rcases ih z hq with ⟨hleft, hright⟩
      let a := q.summary
      let A := a.betaR + a.leakR + d
      let L := A + c
      have hA : 0 < A := by
        dsimp [A]
        exact add_pos (add_pos_of_pos_of_nonneg a.betaR_pos a.leakR_nonneg) hd
      have hL : L ≠ 0 := ne_of_gt (add_pos hA hc)
      have hZformula : Z = (a.cR * X + beta * Y) / L := by
        apply (eq_div_iff hL).2
        rw [hright, hedge] at hZ
        dsimp [A, L]
        linear_combination -hZ
      constructor
      · rw [hleft, hZformula]
        simp only [LinearWeightedChain.summary]
        change (a.cL + a.leakL) * X - a.betaL *
            ((a.cR * X + beta * Y) / L) =
          (((a.cL * L - a.betaL * a.cR) / L) + a.leakL) * X -
            (a.betaL * beta / L) * Y
        field_simp [hL]
        ring
      · rw [hout, hedge, hZformula]
        simp only [LinearWeightedChain.summary]
        change (s : ℝ) * (c * ((a.cR * X + beta * Y) / L) - beta * Y) =
          ((s : ℝ) * c * a.cR / L) * X -
            (((s : ℝ) * beta * A / L) + 0) * Y
        field_simp [hL]
        ring

end TypeIIL
