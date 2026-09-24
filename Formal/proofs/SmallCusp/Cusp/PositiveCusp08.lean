import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

def positiveCusp8Root : ℝ := 0

theorem positiveCusp8Root_equation : (1 : ℝ) * positiveCusp8Root = 0 := by
  norm_num [positiveCusp8Root]


theorem positiveCusp8Root_power_relations :
    let t := positiveCusp8Root
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
  have h := positiveCusp8Root_equation

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

def positiveCusp8 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp8Rates : Fin 5 → ℝ :=
  let t := positiveCusp8Root
  ![((9 : ℝ) / 32) * 1,
    ((5 : ℝ) / 48) * 1,
    ((13 : ℝ) / 48) * 1,
    ((5 : ℝ) / 16) * 1,
    ((1 : ℝ) / 32) * 1]

noncomputable def positiveCusp8RightKernel : Species → ℝ :=
  let t := positiveCusp8Root
  ![((-1 : ℝ) / 4) * 1,
    ((5 : ℝ) / 16) * 1]

noncomputable def positiveCusp8LeftKernel : Species → ℝ :=
  let t := positiveCusp8Root
  ![((-32 : ℝ) / 23) * 1,
    ((48 : ℝ) / 23) * 1]

noncomputable def positiveCusp8Center : Species → ℝ :=
  let t := positiveCusp8Root
  ![((675 : ℝ) / 5888) * 1,
    ((225 : ℝ) / 2944) * 1]

theorem positiveCusp8Rates_positive : PositiveVector positiveCusp8Rates := by
  have hl : (-1 : ℝ) < positiveCusp8Root := by norm_num [positiveCusp8Root]
  have hu : positiveCusp8Root < (1 : ℝ) := by norm_num [positiveCusp8Root]
  have hs : 0 ≤ positiveCusp8Root ^ 2 := sq_nonneg positiveCusp8Root
  intro k
  fin_cases k <;> simp [positiveCusp8Rates] <;> nlinarith

theorem positiveCusp8_jacobian_values :
    positiveCusp8.toNetwork.jacobian positiveCusp8Rates unitState 0 0 = ((-5 : ℝ) / 16) * 1 ∧
    positiveCusp8.toNetwork.jacobian positiveCusp8Rates unitState 0 1 = ((-1 : ℝ) / 4) * 1 ∧
    positiveCusp8.toNetwork.jacobian positiveCusp8Rates unitState 1 0 = ((-5 : ℝ) / 24) * 1 ∧
    positiveCusp8.toNetwork.jacobian positiveCusp8Rates unitState 1 1 = ((-1 : ℝ) / 6) * 1 := by
  norm_num [positiveCusp8, positiveCusp8Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp8_Bqq_values :
    positiveCusp8.toNetwork.hessianApply positiveCusp8Rates unitState
        positiveCusp8RightKernel positiveCusp8RightKernel 0 = ((225 : ℝ) / 4096) * 1 ∧
    positiveCusp8.toNetwork.hessianApply positiveCusp8Rates unitState
        positiveCusp8RightKernel positiveCusp8RightKernel 1 = ((75 : ℝ) / 2048) * 1 := by
  rcases positiveCusp8Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp8, positiveCusp8Rates, positiveCusp8RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp8_Bqh_values :
    positiveCusp8.toNetwork.hessianApply positiveCusp8Rates unitState
        positiveCusp8RightKernel positiveCusp8Center 0 = ((-5625 : ℝ) / 1507328) * 1 ∧
    positiveCusp8.toNetwork.hessianApply positiveCusp8Rates unitState
        positiveCusp8RightKernel positiveCusp8Center 1 = ((-12375 : ℝ) / 1507328) * 1 := by
  rcases positiveCusp8Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp8, positiveCusp8Rates, positiveCusp8RightKernel,
    positiveCusp8Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp8_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp8.toNetwork positiveCusp8Rates
      positiveCusp8RightKernel positiveCusp8LeftKernel positiveCusp8Center 1 4).unfoldingMatrix =
      ((-5376 : ℝ) / 529) * 1 := by
  rcases positiveCusp8Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp8, positiveCusp8Rates, positiveCusp8RightKernel, positiveCusp8LeftKernel,
      positiveCusp8Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp8_cubic_value :
    dot positiveCusp8LeftKernel (positiveCusp8.toNetwork.hessianApply positiveCusp8Rates unitState
      positiveCusp8RightKernel positiveCusp8Center) = ((-1125 : ℝ) / 94208) * 1 := by
  rcases positiveCusp8Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp8_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp8LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp8_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp8.toNetwork := by
  rcases positiveCusp8Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl : (-1 : ℝ) < positiveCusp8Root := by norm_num [positiveCusp8Root]
  have hu : positiveCusp8Root < (1 : ℝ) := by norm_num [positiveCusp8Root]
  have hs : 0 ≤ positiveCusp8Root ^ 2 := sq_nonneg positiveCusp8Root
  rcases positiveCusp8_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp8_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp8_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp8.toNetwork positiveCusp8Rates
    positiveCusp8RightKernel positiveCusp8LeftKernel positiveCusp8Center 1 4
  · exact positiveCusp8Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp8, positiveCusp8Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp8RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp8LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp8LeftKernel, positiveCusp8RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp8LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp8Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp8LeftKernel, positiveCusp8Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp8_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp8_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
