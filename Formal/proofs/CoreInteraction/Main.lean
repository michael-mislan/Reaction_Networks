import proofs.CoreInteraction.Incidence
import proofs.CoreInteraction.MAF.Forest
import proofs.CoreInteraction.Degradation.Star
import proofs.CoreInteraction.Examples.MAFCycle
import proofs.CoreInteraction.Examples.DegradationStar
import proofs.AutocatalyticCS.PaperExample33
import proofs.TypeII3.Network.SourceMembership

/-!
Public CIC-MIN theorem bundle.  The interface exposes source reconstruction,
MAF forest exactness, the source-derived degradation-star spectral theorem,
and the four source-class regressions required by the guide.
-/

namespace CoreInteraction

open DegradationControl

variable {Species Reaction Factor CoreId I J : Type}
variable [Fintype Species] [Fintype Reaction] [Fintype Factor]
variable [DecidableEq Species] [DecidableEq Factor]
variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {Q : SourceNetwork Species Reaction}

def SourceContract (fac : Factorization Q Factor CoreId) : Prop :=
  (∀ s r, ∑ f : Factor, fac.factorInput f s r = Q.input s r) ∧
  (∀ s r, ∑ f : Factor, fac.factorOutput f s r = Q.output s r) ∧
  (∀ s r, ∑ f : Factor, fac.factorCatalyst f s r = Q.catalyst s r) ∧
  (∀ q x s, ∑ f : Factor, fac.residual q x f s =
    Factorization.globalResidual Q q x s) ∧
  (∀ f s, fac.incidenceGraph.Adj (Sum.inl f) (Sum.inr s) ↔ fac.support f s) ∧
  (∀ f s, fac.support f s → fac.IsPrivate f s ∨ fac.IsInterface s)

def DegradationStarContract (S : Degradation.SourceStarData I J)
    (u : I → J → ℝ) : Prop :=
  (0 < S.star.schurLoad u ↔
    HasPositiveRealSpectralBound (degradedMatrix
      (reactionPart S.reactions) S.degradation)) ∧
  (S.star.schurLoad u = 0 ↔
    IsRealSpectralBound (degradedMatrix
      (reactionPart S.reactions) S.degradation) 0) ∧
  (S.star.schurLoad u < 0 ↔
    HasNegativeRealSpectralBound (degradedMatrix
      (reactionPart S.reactions) S.degradation))

def MandatoryRegressions : Prop :=
  (¬ AutocatalyticCS.PaperExample33.ordinary.edgeFinset ⊆
    AutocatalyticCS.PaperExample33.extra.edgeFinset) ∧
  (¬ TypeII3.WeightedCounterexamplePassesMinimalityRegression) ∧
  (MAFComposition.ExactThreshold MAFComposition.N1Feasible 2 ∧
    MAFComposition.ExactThreshold MAFComposition.N2Feasible 2 ∧
    MAFComposition.ExactThreshold MAFComposition.N2N1Feasible 4 ∧
    (∃ v, ∃ c : Examples.MAFCycle.factorization.incidenceGraph.Walk v v,
      c.IsCycle)) ∧
  (Examples.DegradationStar.oneBranch.schurLoad
      Examples.DegradationStar.oneSolve = -(2 / 5 : ℝ) ∧
    Examples.DegradationStar.twoBranch.schurLoad
      Examples.DegradationStar.twoSolve = (1 / 5 : ℝ) ∧
    ExtinctionCertificate Examples.DegradationStar.oneBranch.matrix ∧
    GrowthCertificate Examples.DegradationStar.twoBranch.matrix)

structure CICMinBundle (fac : Factorization Q Factor CoreId)
    (S : Degradation.SourceStarData I J) (u : I → J → ℝ) : Prop where
  source : SourceContract fac
  mafForest : fac.IncidenceForest → ∀ q,
    fac.GlobalFeasibleAt q ↔ ∃ f, fac.FactorFeasibleAt q f
  degradationStar : DegradationStarContract S u
  regressions : MandatoryRegressions

theorem mandatoryRegressions : MandatoryRegressions := by
  exact ⟨AutocatalyticCS.PaperExample33.ordinary_edges_not_subset_extra,
    TypeII3.weighted_counterexample_not_source_minimal,
    Examples.MAFCycle.scalar_two_two_four_maps_to_cycle,
    Examples.DegradationStar.oneBranch_schurLoad,
    Examples.DegradationStar.twoBranch_schurLoad,
    Examples.DegradationStar.oneBranch_extinction,
    Examples.DegradationStar.twoBranch_growth⟩

omit [Fintype Species] [DecidableEq Species] in
/-- `CORE-INTERACTION-CALCULUS` / CIC-MIN: one warning-free theorem joins the
literal source factorization, exact MAF incidence-forest law, solve-witness
source-derived degradation-star spectral trichotomy, and all mandatory
interaction regressions. -/
theorem coreInteractionCalculus
    (fac : Factorization Q Factor CoreId)
    (S : Degradation.SourceStarData I J) (u : I → J → ℝ)
    (hu : S.star.SolveWitness u) (hupos : S.star.PositiveInternal u)
    (hc : S.star.PositiveRootCoupling)
    (hrs : ∀ r ∈ S.reactions, NonnegativeReaction r)
    (hsource : SourceIrreducible S.reactions) : CICMinBundle fac S u := by
  constructor
  · exact fac.sourceFaithfulFactorization_reconstructs
  · intro hforest q
    exact fac.maf_incidenceForest_exact q hforest
  · exact S.schurLoad_spectralTrichotomy u hu hupos hc hrs hsource
  · exact mandatoryRegressions

end CoreInteraction
