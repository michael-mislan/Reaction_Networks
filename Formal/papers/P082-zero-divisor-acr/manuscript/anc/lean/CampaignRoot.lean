import proofs.ACRZeroDivisors.SufficiencyCounterexample
import proofs.ACRZeroDivisors.OrderMain
import proofs.ACRZeroDivisors.MassActionCompleteness
import proofs.ACRZeroDivisors.BlockOrder
import proofs.ACRZeroDivisors.ReleaseFlux
import proofs.ACRZeroDivisors.ReleaseACR

namespace ACRZeroDivisors
open MvPolynomial

/-- Independent conclusions: no counterexample field depends on the input
hypotheses of the general completeness or product-release fields. -/
structure CampaignCertificate : Prop where
  necessity :
    (∀ r ∈ necessityNetwork, Bimolecular r) ∧ NonvacuousACR necessityNetwork 0 2 ∧
      ¬ ∃! a : ℝ, 0 < a ∧ CoordinateCandidate (steadyIdeal necessityNetwork) a
  sufficiency :
    (∀ r ∈ sufficiencyNetwork, Bimolecular r) ∧
    (∃ x, PositiveSteady sufficiencyNetwork x) ∧
    (∃! a : ℝ, 0 < a ∧ CoordinateCandidate4 (steadyIdeal sufficiencyNetwork) a) ∧
      ¬ ∃ a, NonvacuousACR sufficiencyNetwork 0 a
  unrestrictedOrder :
    OrderWitness.AdmissibleEliminationOrder ∧
    OrderWitness.ReducedBasisCertificate (OrderWitness.rationalSteadyIdeal OrderWitness.witnessNetwork) ∧
    (∀ r ∈ OrderWitness.witnessNetwork, Bimolecular r) ∧
    NonvacuousACR OrderWitness.witnessNetwork 2 1 ∧
    ((X 2-1 : Poly3) ∉ steadyIdeal OrderWitness.witnessNetwork ∧
      ∃ h : Poly3, h ∉ steadyIdeal OrderWitness.witnessNetwork ∧
        (X 2-1)*h ∈ steadyIdeal OrderWitness.witnessNetwork) ∧
    ¬ OrderWitness.AlgorithmCandidates {OrderWitness.b1,OrderWitness.b2,OrderWitness.b3} 1
  blockCompleteness : ∀ (n : ℕ) (σ ι : Type) [Fintype ι]
    (rs : List (Reaction n)) (e : Fin n ≃ Option σ)
    (full : MonomialOrder.{0,0} (Option σ)) (z : MonomialOrder.{0,0} σ)
    (b : ι → MvPolynomial (Option σ) ℚ), BlockCompatible full z →
    HasLeadingCover full ((rationalSteadyIdeal rs).map (rename e).toRingHom) b →
    (∀ i, b i ∈ (rationalSteadyIdeal rs).map (rename e).toRingHom) →
    ∀ a, NonvacuousACR rs (e.symm none) a →
      SpeciesCoordinateCandidate (steadyIdeal rs) (e.symm none) a →
      BlockAlgorithmCandidates z b a
  releaseAlgebra : ∀ (σ A : Type) [CommRing A] (n : ℕ)
    (f : σ → A) (F : A) (rates : Fin (n+1) → Aˣ) (w : σ → Fin (n+1) → A),
    Nonempty ((MvPolynomial (Fin (n+1)) A ⧸ releaseIdeal f F rates w) ≃+*
      (A ⧸ Ideal.span (Set.range f))) ∧
    ∀ a, (C a ∈ releaseIdeal f F rates w ∨
      ∃ p, p ∉ releaseIdeal f F rates w ∧ C a*p ∈ releaseIdeal f F rates w) ↔
      (a ∈ Ideal.span (Set.range f) ∨
        ∃ p, p ∉ Ideal.span (Set.range f) ∧ a*p ∈ Ideal.span (Set.range f))
  releaseACR : ∀ (σ : Type) (n : ℕ)
    (f : (σ → ℝ) → σ → ℝ) (F : (σ → ℝ) → ℝ)
    (rates : Fin (n+1) → ℝ) (w : σ → Fin (n+1) → ℝ),
    (∀ x, (∀ i, 0 < x i) → 0 < F x) → (∀ j, 0 < rates j) →
    ∀ i a, ((∃ x y, ReleaseNewState f F rates w x y) ∧
      ∀ x y, ReleaseNewState f F rates w x y → x i = a) ↔
      ((∃ x, ReleaseOldState f x) ∧ ∀ x, ReleaseOldState f x → x i = a)

theorem campaign_root : CampaignCertificate := by
  constructor
  · exact question313_necessity_counterexample
  · exact question313_sufficiency_counterexample
  · exact OrderWitness.unrestricted_order_counterexample
  · intro n σ ι _ rs e full z b hb hc hg a ha ht
    exact mass_action_block_algorithm_complete rs e full z hb b hc hg a ha ht
  · intro σ A _ n f F rates w
    refine ⟨⟨releaseQuotientEquiv f F rates w⟩,?_⟩
    intro a
    rw [releaseIdeal_eq_graph]
    exact graph_coefficient_candidate_iff _ _ a
  · intro σ n f F rates w hF hr i a
    exact release_acr_iff f F hF rates hr w i a

end ACRZeroDivisors
