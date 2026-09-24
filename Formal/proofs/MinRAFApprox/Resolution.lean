import proofs.MinRAFApprox.ComplexityTransfer

namespace MinRAFApprox.SetCoverSource

open RAF MinRAFApprox.Reaction

variable {m n M : Nat}

/-- The hardness family uses at most two reactants per reaction. -/
theorem source_input_card_le_two
    (r : MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M)) :
    ((crs m n M).inputs r).card ≤ 2 := by
  cases r with
  | gate i =>
      by_cases hi : i.val = 0 <;> simp [crs, hi]
  | block j k =>
      by_cases hk : k.val = 0 <;> simp [crs, hk]

/-- Every reaction in the hardness family has exactly one product. -/
theorem source_output_card_eq_one
    (r : MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M)) :
    ((crs m n M).outputs r).card = 1 := by
  cases r <;> simp [crs]

/-- The literal source uses a singleton food set. -/
theorem source_food_card_eq_one : (crs m n M).food.card = 1 := by
  simp [crs]

/-- Terminal resolution of the solution-approximation question.  The only
complexity-theoretic input is standard SET COVER inapproximability; all RAF
semantics, exact optimum correspondence, source size, extraction, and ratio
arithmetic are proved in the imported modules. -/
theorem constant_factor_approximation_resolution
    (P_eq_NP : Prop)
    (PolynomialCover : CoverAlgorithm → Prop)
    (PolynomialRAF : SourceRAFAlgorithm → Prop)
    (setCoverHardness : ¬ P_eq_NP →
      NoPolynomialCoverConstApprox PolynomialCover)
    (reductionPolynomial : ∀ A, PolynomialRAF A →
      PolynomialCover (inducedCover A)) :
    ¬ P_eq_NP → NoPolynomialSourceRAFConstApprox PolynomialRAF :=
  minRAF_no_constant_factor_approx_unless_P_eq_NP P_eq_NP
    PolynomialCover PolynomialRAF setCoverHardness reductionPolynomial

end MinRAFApprox.SetCoverSource
