import proofs.TypeIIL.WeightedChain
import proofs.TypeII3.Algebra.PowSecant

namespace TypeIIL

open TypeII3

/-- A literal reversible mass-action chain.  A direct edge has reaction
`X ⇌ sY`; extension appends such an edge and positively degrades the former
right endpoint. -/
inductive MassActionWeightedChain where
  | direct (kPlus kMinus : ℝ) (s : ℕ)
      (kPlus_pos : 0 < kPlus) (kMinus_pos : 0 < kMinus) (s_pos : 0 < s)
  | extend (q : MassActionWeightedChain) (kPlus kMinus : ℝ) (s : ℕ) (d : ℝ)
      (kPlus_pos : 0 < kPlus) (kMinus_pos : 0 < kMinus)
      (s_pos : 0 < s) (d_pos : 0 < d)

def MassActionWeightedChain.State : MassActionWeightedChain → Type
  | .direct _ _ _ _ _ _ => PUnit
  | .extend q _ _ _ _ _ _ _ _ => q.State × ℝ

def MassActionWeightedChain.PositiveState :
    (q : MassActionWeightedChain) → q.State → Prop
  | .direct _ _ _ _ _ _, _ => True
  | .extend q _ _ _ _ _ _ _ _, z => q.PositiveState z.1 ∧ 0 < z.2

/-- Literal nonlinear endpoint fluxes.  `jL` leaves the left endpoint and
`jR` is the stoichiometrically delivered current entering the right endpoint. -/
def MassActionWeightedChain.Flux :
    (q : MassActionWeightedChain) → q.State → ℝ → ℝ → ℝ → ℝ → Prop
  | .direct kPlus kMinus s _ _ _, _, X, Y, jL, jR =>
      jL = kPlus * X - kMinus * Y ^ s ∧
      jR = s * (kPlus * X - kMinus * Y ^ s)
  | .extend q kPlus kMinus s d _ _ _ _, z, X, Y, jL, jR =>
      ∃ jMid jEdge,
        q.Flux z.1 X z.2 jL jMid ∧
        jEdge = kPlus * z.2 - kMinus * Y ^ s ∧
        jMid - jEdge - d * z.2 = 0 ∧
        jR = s * jEdge

/-- The positive secant coefficient visible in the difference of two reverse
mass-action monomials. -/
noncomputable def massActionSecantBeta
    (kMinus x y : ℝ) (s : ℕ) : ℝ :=
  kMinus * secantPoly x y s

theorem massActionSecantBeta_pos
    {kMinus x y : ℝ} {s : ℕ}
    (hk : 0 < kMinus) (hx : 0 < x) (hy : 0 < y) (hs : 0 < s) :
    0 < massActionSecantBeta kMinus x y s := by
  unfold massActionSecantBeta
  exact mul_pos hk (secantPoly_pos hx hy hs)

theorem mass_action_edge_difference
    {kPlus kMinus X₁ X₂ Y₁ Y₂ : ℝ} {s : ℕ} :
    (kPlus * X₁ - kMinus * Y₁ ^ s) -
        (kPlus * X₂ - kMinus * Y₂ ^ s) =
      kPlus * (X₁ - X₂) -
        massActionSecantBeta kMinus Y₁ Y₂ s * (Y₁ - Y₂) := by
  have hp := pow_sub_pow_eq_mul_secantPoly Y₁ Y₂ s
  unfold massActionSecantBeta
  linear_combination -kMinus * hp

/-- Two positive nonlinear chain states with common rates produce an exact
`LinearWeightedChainFlux` for their difference.  This is the literal
mass-action-to-secant adapter required by the paper-level two-root theorem. -/
theorem mass_action_weighted_chain_two_state_linearize
    (q : MassActionWeightedChain)
    (z w : q.State) {X₁ X₂ Y₁ Y₂ jL₁ jL₂ jR₁ jR₂ : ℝ}
    (hz : q.PositiveState z) (hw : q.PositiveState w)
    (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hf₁ : q.Flux z X₁ Y₁ jL₁ jR₁)
    (hf₂ : q.Flux w X₂ Y₂ jL₂ jR₂) :
    ∃ (L : LinearWeightedChain) (u : L.State),
      LinearWeightedChainFlux L u (X₁ - X₂) (Y₁ - Y₂)
        (jL₁ - jL₂) (jR₁ - jR₂) := by
  induction q generalizing X₁ X₂ Y₁ Y₂ jL₁ jL₂ jR₁ jR₂ with
  | direct kPlus kMinus s hkPlus hkMinus hs =>
      let beta := massActionSecantBeta kMinus Y₁ Y₂ s
      have hbeta : 0 < beta :=
        massActionSecantBeta_pos hkMinus hY₁ hY₂ hs
      let L := LinearWeightedChain.direct kPlus beta s hkPlus hbeta hs
      refine ⟨L, PUnit.unit, ?_⟩
      rcases hf₁ with ⟨hL₁, hR₁⟩
      rcases hf₂ with ⟨hL₂, hR₂⟩
      change jL₁ - jL₂ = kPlus * (X₁ - X₂) - beta * (Y₁ - Y₂) ∧
        jR₁ - jR₂ = s *
          (kPlus * (X₁ - X₂) - beta * (Y₁ - Y₂))
      have hedge := mass_action_edge_difference
        (kPlus := kPlus) (kMinus := kMinus)
        (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂) (s := s)
      dsimp [beta] at hedge ⊢
      constructor
      · rw [hL₁, hL₂]
        exact hedge
      · rw [hR₁, hR₂]
        rw [← hedge]
        ring
  | extend q kPlus kMinus s d hkPlus hkMinus hs hd ih =>
      rcases z with ⟨z, Z₁⟩
      rcases w with ⟨w, Z₂⟩
      rcases hz with ⟨hz, hZ₁⟩
      rcases hw with ⟨hw, hZ₂⟩
      rcases hf₁ with ⟨jMid₁, jEdge₁, hq₁, hedge₁, hbal₁, hout₁⟩
      rcases hf₂ with ⟨jMid₂, jEdge₂, hq₂, hedge₂, hbal₂, hout₂⟩
      obtain ⟨Lq, uq, hlinq⟩ := ih z w hz hw hZ₁ hZ₂ hq₁ hq₂
      let beta := massActionSecantBeta kMinus Y₁ Y₂ s
      have hbeta : 0 < beta :=
        massActionSecantBeta_pos hkMinus hY₁ hY₂ hs
      let L := LinearWeightedChain.extend Lq kPlus beta s d hkPlus hbeta hs hd
      refine ⟨L, ⟨uq, Z₁ - Z₂⟩, ?_⟩
      refine ⟨jMid₁ - jMid₂, jEdge₁ - jEdge₂, hlinq, ?_, ?_, ?_⟩
      · rw [hedge₁, hedge₂]
        simpa [beta] using
          (mass_action_edge_difference
            (kPlus := kPlus) (kMinus := kMinus)
            (X₁ := Z₁) (X₂ := Z₂) (Y₁ := Y₁) (Y₂ := Y₂) (s := s))
      · linear_combination hbal₁ - hbal₂
      · rw [hout₁, hout₂]
        ring

end TypeIIL
