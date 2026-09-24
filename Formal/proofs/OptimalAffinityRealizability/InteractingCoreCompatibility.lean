import proofs.OptimalAffinityRealizability.GlobalInvariant
import proofs.ThermoCoreCompatibility.Main

namespace OptimalAffinityRealizability

noncomputable section

/-- In a square source, magnitude reconstruction is reactionwise: positive
one-way flows are forced directly by positive production and `q > 1`. -/
def SquareReactionwiseMagnitudeCompatible {n : ℕ} (J : ℝ)
    (production q : Fin n → ℝ) : Prop :=
  (∀ i, 0 < reconstructedReverseFlow J production q i) ∧
  (∀ i, 0 < reconstructedForwardFlow J production q i)

theorem squareSource_reactionwiseMagnitudeAutomatic {n : ℕ}
    (J : ℝ) (production q : Fin n → ℝ)
    (hJ : 0 < J) (hproduction : ∀ i, 0 < production i)
    (hq : ∀ i, 1 < q i) :
    SquareReactionwiseMagnitudeCompatible J production q :=
  reconstructedFlows_positive J production q hJ hproduction hq

/-- Shared interacting cores lie beyond the square reactionwise boundary:
direction compatibility does not force a common magnitude lift. -/
theorem interacting_direction_does_not_imply_magnitude :
    ∃ F : ThermoCoreCompatibility.CoreFamily
        (Core := ThermoCoreCompatibility.MagnitudePair.Core)
        ThermoCoreCompatibility.MagnitudePair.network,
      F.MultiPAC ∧ F.DirectionCompatible ∧ ¬ F.LinearComplexCompatible :=
  ⟨ThermoCoreCompatibility.MagnitudePair.family,
    ThermoCoreCompatibility.sourceValid_nonToric_magnitudeObstruction⟩

/-- Even a positive linear complex lift need not come from one species
activity vector. -/
theorem interacting_linearComplex_does_not_imply_speciesActivity :
    ∃ F : ThermoCoreCompatibility.CoreFamily
        (Core := ThermoCoreCompatibility.ToricPair.Core)
        ThermoCoreCompatibility.ToricPair.network,
      F.MultiPAC ∧ F.DirectionCompatible ∧
        F.LinearComplexCompatible ∧ ¬ F.MultiCAC :=
  ThermoCoreCompatibility.exists_sourceValid_genuineToricIncompatible_pair

/-- Full layered profile for an interacting-core assembly.  The last three
predicates are supplied by the kinetic source interface rather than silently
identified with thermodynamic compatibility. -/
structure LayeredInteractingCoreRealization
    {Species Reaction Core : Type*}
    [DecidableEq Species] [DecidableEq Reaction]
    [Fintype Species] [Fintype Core]
    {Q : ThermoCoreCompatibility.ReversibleCRN Species Reaction}
    (F : ThermoCoreCompatibility.CoreFamily (Core := Core) Q)
    (ResponseJetCompatible RegularBranchCompatible GlobalOptimumCompatible : Prop) where
  multiPAC : F.MultiPAC
  direction : F.DirectionCompatible
  linearComplex : F.LinearComplexCompatible
  speciesActivity : F.MultiCAC
  responseJet : ResponseJetCompatible
  regularBranch : RegularBranchCompatible
  globalOptimum : GlobalOptimumCompatible

/-- Typed boundary message retained by composition. -/
structure TypedKineticBoundaryRelation (Boundary Reaction : Type*) where
  logResponse : Boundary → ℝ
  forwardFlow : Reaction → ℝ
  reverseFlow : Reaction → ℝ
  forwardPositive : ∀ r, 0 < forwardFlow r
  reversePositive : ∀ r, 0 < reverseFlow r
  complexActivityFeasible : Prop
  responseJetCompatible : Prop
  regularBranchCompatible : Prop
  globalOptimumCompatible : Prop

def BoundaryRelationsJoinable {Boundary Reaction₁ Reaction₂ : Type*}
    (left : TypedKineticBoundaryRelation Boundary Reaction₁)
    (right : TypedKineticBoundaryRelation Boundary Reaction₂) : Prop :=
  left.logResponse = right.logResponse ∧
    left.complexActivityFeasible ∧ right.complexActivityFeasible

structure JoinedBoundaryProjection {Boundary Reaction₁ Reaction₂ : Type*}
    (left : TypedKineticBoundaryRelation Boundary Reaction₁)
    (right : TypedKineticBoundaryRelation Boundary Reaction₂) where
  joinable : BoundaryRelationsJoinable left right
  responseJetCompatible : left.responseJetCompatible ∧ right.responseJetCompatible
  regularBranchCompatible : left.regularBranchCompatible ∧ right.regularBranchCompatible
  globalOptimumCompatible : left.globalOptimumCompatible ∧ right.globalOptimumCompatible

/-- Exact adversarial composition suite: magnitude, toric, and phase-window
failures are simultaneously available to every proposed articulation rule. -/
theorem thermoComposition_adversarialSuite :
    (ThermoCoreCompatibility.MagnitudePair.family.MultiPAC ∧
      ThermoCoreCompatibility.MagnitudePair.family.DirectionCompatible ∧
      ¬ ThermoCoreCompatibility.MagnitudePair.family.LinearComplexCompatible) ∧
    (ThermoCoreCompatibility.ToricPair.family.MultiPAC ∧
      ThermoCoreCompatibility.ToricPair.family.DirectionCompatible ∧
      ThermoCoreCompatibility.ToricPair.family.LinearComplexCompatible ∧
      ¬ ThermoCoreCompatibility.ToricPair.family.MultiCAC) ∧
    (∀ (k : ℝ) (hk : 0 < k),
      ThermoCoreCompatibility.TrianglePhaseDiagram.PairMultiCAC k hk ↔
        1 / 2 < k ∧ k < 2) := by
  refine ⟨ThermoCoreCompatibility.sourceValid_nonToric_magnitudeObstruction,
    ThermoCoreCompatibility.ToricPair.genuineToricObstruction, ?_⟩
  intro k hk
  exact ThermoCoreCompatibility.magnitudePair_multiCAC_iff k hk

/-- Counter-articulation theorem: no rule based only on productive direction
can guarantee even the linear magnitude layer. -/
theorem directionOnly_articulation_refuted :
    ¬ (∀ F : ThermoCoreCompatibility.CoreFamily
        (Core := ThermoCoreCompatibility.MagnitudePair.Core)
        ThermoCoreCompatibility.MagnitudePair.network,
      F.MultiPAC → F.DirectionCompatible → F.LinearComplexCompatible) := by
  intro h
  exact ThermoCoreCompatibility.MagnitudePair.family_not_linearComplexCompatible
    (h ThermoCoreCompatibility.MagnitudePair.family
      ThermoCoreCompatibility.MagnitudePair.family_multiPAC
      ThermoCoreCompatibility.MagnitudePair.family_directionCompatible)

/-- Counter-articulation theorem at the next layer: independent complex
activities do not guarantee a common species-activity lift. -/
theorem linearComplexOnly_articulation_refuted :
    ¬ (∀ F : ThermoCoreCompatibility.CoreFamily
        (Core := ThermoCoreCompatibility.ToricPair.Core)
        ThermoCoreCompatibility.ToricPair.network,
      F.MultiPAC → F.DirectionCompatible → F.LinearComplexCompatible → F.MultiCAC) := by
  intro h
  exact ThermoCoreCompatibility.ToricPair.family_not_multiCAC
    (h ThermoCoreCompatibility.ToricPair.family
      ThermoCoreCompatibility.ToricPair.family_multiPAC
      ThermoCoreCompatibility.ToricPair.family_directionCompatible
      ThermoCoreCompatibility.ToricPair.family_linearComplexCompatible)

end
end OptimalAffinityRealizability
