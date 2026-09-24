import proofs.RAFInteriorRealizability.CatalysisRealization

namespace RAFInteriorRealizability

universe u

variable {E : Type u} [Fintype E] [DecidableEq E]

/-- Constructive sufficiency of the finite Food-Support certificate. -/
theorem foodSupportCertificate_implies_sameGroundRAFRealizable
    (ψ : InteriorOperator E) :
    FoodSupportCertificate ψ → SameGroundRAFRealizable ψ := by
  rintro ⟨A, P, hAP⟩
  apply (sameGroundRAFRealizable_iff_fixedFamily ψ).2
  refine ⟨MarkerSource.realization A P, ?_⟩
  apply Finset.ext
  intro S
  rw [MarkerSource.mem_realization_fixedData_iff, hAP]

/-- Exact characterization of finite same-ground RAF interior operators.
The certificate is finite and constructive: an antimatroid food shell plus a
predecessor-support map on the same reaction ground set. -/
theorem sameGroundRAFRealizable_iff_foodSupportCertificate
    (ψ : InteriorOperator E) :
    SameGroundRAFRealizable ψ ↔ FoodSupportCertificate ψ :=
  ⟨sameGroundRAFRealizable_implies_foodSupportCertificate ψ,
    foodSupportCertificate_implies_sameGroundRAFRealizable ψ⟩

/-- Public statement of the RAF interior-operator realizability theorem. -/
theorem rafInteriorOperator_realizable_iff
    (ψ : InteriorOperator E) :
    SameGroundRAFRealizable ψ ↔
      ∃ A : AntimatroidData E, ∃ P : E → Finset E,
        ∀ S : Finset E,
          S ∈ ψ.family ↔ S ∈ A.family ∧ PredSupported P S :=
  sameGroundRAFRealizable_iff_foodSupportCertificate ψ

end RAFInteriorRealizability
