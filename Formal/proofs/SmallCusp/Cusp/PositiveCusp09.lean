import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

def positiveCusp9Root : ℝ := 0

theorem positiveCusp9Root_equation : (1 : ℝ) * positiveCusp9Root = 0 := by
  norm_num [positiveCusp9Root]


theorem positiveCusp9Root_power_relations :
    let t := positiveCusp9Root
    ((1 : ℝ) * t) * t ^ 0 = 0 ∧
    ((1 : ℝ) * t) * t ^ 1 = 0 ∧
    ((1 : ℝ) * t) * t ^ 2 = 0 ∧
    ((1 : ℝ) * t) * t ^ 3 = 0 ∧
    ((1 : ℝ) * t) * t ^ 4 = 0 ∧
    ((1 : ℝ) * t) * t ^ 5 = 0 ∧
    ((1 : ℝ) * t) * t ^ 6 = 0 ∧
    ((1 : ℝ) * t) * t ^ 7 = 0 ∧
    ((1 : ℝ) * t) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp9Root_equation

  constructor
  · rw [h, zero_mul]
  constructor
  · rw [h, zero_mul]
  constructor
  · rw [h, zero_mul]
  constructor
  · rw [h, zero_mul]
  constructor
  · rw [h, zero_mul]
  constructor
  · rw [h, zero_mul]
  constructor
  · rw [h, zero_mul]
  constructor
  · rw [h, zero_mul]
  · rw [h, zero_mul]

def positiveCusp9 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp9Rates : Fin 5 → ℝ :=
  let t := positiveCusp9Root
  ![((2 : ℝ) / 7) * 1,
    ((2 : ℝ) / 21) * 1,
    ((2 : ℝ) / 7) * 1,
    ((2 : ℝ) / 7) * 1,
    ((1 : ℝ) / 21) * 1]

noncomputable def positiveCusp9RightKernel : Species → ℝ :=
  let t := positiveCusp9Root
  ![((-2 : ℝ) / 7) * 1,
    ((2 : ℝ) / 7) * 1]

noncomputable def positiveCusp9LeftKernel : Species → ℝ :=
  let t := positiveCusp9Root
  ![((-7 : ℝ) / 5) * 1,
    ((21 : ℝ) / 10) * 1]

noncomputable def positiveCusp9Center : Species → ℝ :=
  let t := positiveCusp9Root
  ![((24 : ℝ) / 245) * 1,
    ((16 : ℝ) / 245) * 1]

theorem positiveCusp9Rates_positive : PositiveVector positiveCusp9Rates := by
  have hl : (-1 : ℝ) < positiveCusp9Root := by norm_num [positiveCusp9Root]
  have hu : positiveCusp9Root < (1 : ℝ) := by norm_num [positiveCusp9Root]
  have hs : 0 ≤ positiveCusp9Root ^ 2 := sq_nonneg positiveCusp9Root
  intro k
  fin_cases k <;> simp [positiveCusp9Rates] <;> nlinarith

theorem positiveCusp9_jacobian_values :
    positiveCusp9.toNetwork.jacobian positiveCusp9Rates unitState 0 0 = ((-2 : ℝ) / 7) * 1 ∧
    positiveCusp9.toNetwork.jacobian positiveCusp9Rates unitState 0 1 = ((-2 : ℝ) / 7) * 1 ∧
    positiveCusp9.toNetwork.jacobian positiveCusp9Rates unitState 1 0 = ((-4 : ℝ) / 21) * 1 ∧
    positiveCusp9.toNetwork.jacobian positiveCusp9Rates unitState 1 1 = ((-4 : ℝ) / 21) * 1 := by
  norm_num [positiveCusp9, positiveCusp9Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp9_Bqq_values :
    positiveCusp9.toNetwork.hessianApply positiveCusp9Rates unitState
        positiveCusp9RightKernel positiveCusp9RightKernel 0 = ((16 : ℝ) / 343) * 1 ∧
    positiveCusp9.toNetwork.hessianApply positiveCusp9Rates unitState
        positiveCusp9RightKernel positiveCusp9RightKernel 1 = ((32 : ℝ) / 1029) * 1 := by
  rcases positiveCusp9Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp9, positiveCusp9Rates, positiveCusp9RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp9_Bqh_values :
    positiveCusp9.toNetwork.hessianApply positiveCusp9Rates unitState
        positiveCusp9RightKernel positiveCusp9Center 0 = ((-32 : ℝ) / 12005) * 1 ∧
    positiveCusp9.toNetwork.hessianApply positiveCusp9Rates unitState
        positiveCusp9RightKernel positiveCusp9Center 1 = ((-32 : ℝ) / 5145) * 1 := by
  rcases positiveCusp9Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp9, positiveCusp9Rates, positiveCusp9RightKernel,
    positiveCusp9Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp9_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp9.toNetwork positiveCusp9Rates
      positiveCusp9RightKernel positiveCusp9LeftKernel positiveCusp9Center 1 4).unfoldingMatrix =
      ((-189 : ℝ) / 25) * 1 := by
  rcases positiveCusp9Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp9, positiveCusp9Rates, positiveCusp9RightKernel, positiveCusp9LeftKernel,
      positiveCusp9Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
      unitState, dot, canonicalLeftKernel, canonicalRightKernel,
      unitChartCuspCertificate, twoRateDirections,
      CuspCertificate.unfoldingMatrix, CuspCertificate.unfoldingEntry,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.jacobianApply, SmallPlanarNetwork.jacobian,
      SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
      SmallPlanarNetwork.rateFieldVariation,
      SmallPlanarNetwork.rateJacobianVariation,
      SmallPlanarNetwork.multiDerivativeMonomial,
      SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.pairMultiIndex,
      SmallPlanarNetwork.stoich, Matrix.det_fin_two,
      Fin.sum_univ_succ, Fin.prod_univ_two]
  norm_num
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp9_cubic_value :
    dot positiveCusp9LeftKernel (positiveCusp9.toNetwork.hessianApply positiveCusp9Rates unitState
      positiveCusp9RightKernel positiveCusp9Center) = ((-16 : ℝ) / 1715) * 1 := by
  rcases positiveCusp9Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp9_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp9LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp9_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp9.toNetwork := by
  rcases positiveCusp9Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl : (-1 : ℝ) < positiveCusp9Root := by norm_num [positiveCusp9Root]
  have hu : positiveCusp9Root < (1 : ℝ) := by norm_num [positiveCusp9Root]
  have hs : 0 ≤ positiveCusp9Root ^ 2 := sq_nonneg positiveCusp9Root
  rcases positiveCusp9_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp9_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp9_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp9.toNetwork positiveCusp9Rates
    positiveCusp9RightKernel positiveCusp9LeftKernel positiveCusp9Center 1 4
  · exact positiveCusp9Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp9, positiveCusp9Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp9RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp9LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp9LeftKernel, positiveCusp9RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp9LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp9Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp9LeftKernel, positiveCusp9Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp9_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp9_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
