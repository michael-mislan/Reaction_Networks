import proofs.OptimalAffinityCorrected.ResponseProfile

namespace OptimalAffinityCorrected

open scoped BigOperators
noncomputable section

/-!
An abstract response-optimum interface.  It records the one-way response data
and the two identities needed by the response theorem; it is deliberately not
advertised as a constructor from an arbitrary mass-action network.  Literal
source realizations are supplied separately for the recycling family and the
zero-diagonal circuit.
-/

structure ResponseOptimalPoint (n : ℕ) where
  sourceValid : Prop
  source_valid : sourceValid
  T : Fin n → Fin n → ℝ
  g : Fin n → ℕ
  Fplus : Fin n → ℝ
  Fminus : Fin n → ℝ
  expAffinity : ℝ
  forwardPositive : ∀ j, 0 < Fplus j
  responseIdentity : ∀ j, Fminus j = responseImage T Fplus j
  localForward : ∀ j, Fplus j < Fminus j
  affinityIdentity :
    expAffinity = ∏ j, (Fminus j / Fplus j) ^ (g j)

theorem ResponseOptimalPoint.forwardResponse {n : ℕ}
    (P : ResponseOptimalPoint n) : ForwardResponse P.T P.Fplus := by
  intro j
  refine ⟨P.forwardPositive j, ?_⟩
  rw [responseRatio, ← P.responseIdentity j]
  exact (lt_div_iff₀ (P.forwardPositive j)).2 (by
    nlinarith [P.localForward j, P.forwardPositive j])

theorem ResponseOptimalPoint.objectiveIdentity {n : ℕ}
    (P : ResponseOptimalPoint n) :
    P.expAffinity = responseObjective P.T P.g P.Fplus := by
  rw [P.affinityIdentity]
  unfold responseObjective responseRatio
  apply Finset.prod_congr rfl
  intro j hj
  rw [← P.responseIdentity j]

theorem response_optimum_adapter {n : ℕ} (P : ResponseOptimalPoint n) :
    ∃ f, ForwardResponse P.T f ∧
      P.expAffinity = responseObjective P.T P.g f := by
  exact ⟨P.Fplus, P.forwardResponse, P.objectiveIdentity⟩

theorem response_optimum_lower_bound {n : ℕ} (P : ResponseOptimalPoint n) :
    responseProfileBound P.T P.g ≤ P.expAffinity := by
  exact responseProfileBound_applies_at_optimum P.T P.g P.Fplus
    P.expAffinity P.forwardResponse P.objectiveIdentity

/-! Backward-compatible names.  The type is intentionally called
`ResponseOptimalPoint`: its fields are an abstract response certificate, not a
constructor from an arbitrary source-network datatype. -/

abbrev SourceOptimalPoint := ResponseOptimalPoint

theorem source_to_response_adapter {n : ℕ} (P : ResponseOptimalPoint n) :
    ∃ f, ForwardResponse P.T f ∧
      P.expAffinity = responseObjective P.T P.g f :=
  response_optimum_adapter P

theorem source_response_lower_bound {n : ℕ} (P : ResponseOptimalPoint n) :
    responseProfileBound P.T P.g ≤ P.expAffinity :=
  response_optimum_lower_bound P

end
end OptimalAffinityCorrected
