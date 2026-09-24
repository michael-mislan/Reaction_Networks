import proofs.RAFInteriorRealizability.Necessity

namespace RAFInteriorRealizability

universe u

variable {E : Type u} [Fintype E] [DecidableEq E]

/-- The finite set-theoretic certificate proposed by the Food-Support
factorization: an antimatroid shell and one predecessor set per reaction. -/
def FoodSupportCertificate (ψ : InteriorOperator E) : Prop :=
  ∃ A : AntimatroidData E, ∃ P : E → Finset E,
    ∀ S : Finset E,
      S ∈ ψ.family ↔ S ∈ A.family ∧ PredSupported P S

theorem sameGroundRAFRealizable_implies_foodSupportCertificate
    (ψ : InteriorOperator E) :
    SameGroundRAFRealizable ψ → FoodSupportCertificate ψ := by
  intro hreal
  obtain ⟨W, hfamily⟩ :=
    (sameGroundRAFRealizable_iff_fixedFamily ψ).1 hreal
  obtain ⟨A, P, hAP⟩ :=
    @literalRealization_has_foodSupport W.M E W.decEqM inferInstance inferInstance
      W.Q W.C
  refine ⟨A, P, fun S => ?_⟩
  have h := hAP S
  change S ∈ W.fixedData.family ↔ S ∈ A.family ∧ PredSupported P S at h
  rw [hfamily] at h
  exact h

end RAFInteriorRealizability
