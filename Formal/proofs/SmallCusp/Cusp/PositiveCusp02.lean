import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

def positiveCusp2Root : ℝ := 0

theorem positiveCusp2Root_equation : (1 : ℝ) * positiveCusp2Root = 0 := by
  norm_num [positiveCusp2Root]


theorem positiveCusp2Root_power_relations :
    let t := positiveCusp2Root
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
  have h := positiveCusp2Root_equation

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

def positiveCusp2 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .y)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp2Rates : Fin 5 → ℝ :=
  let t := positiveCusp2Root
  ![((1 : ℝ) / 11) * 1,
    ((3 : ℝ) / 11) * 1,
    ((3 : ℝ) / 11) * 1,
    ((3 : ℝ) / 11) * 1,
    ((1 : ℝ) / 11) * 1]

noncomputable def positiveCusp2RightKernel : Species → ℝ :=
  let t := positiveCusp2Root
  ![((5 : ℝ) / 11) * 1,
    ((10 : ℝ) / 11) * 1]

noncomputable def positiveCusp2LeftKernel : Species → ℝ :=
  let t := positiveCusp2Root
  ![((33 : ℝ) / 65) * 1,
    ((11 : ℝ) / 13) * 1]

noncomputable def positiveCusp2Center : Species → ℝ :=
  let t := positiveCusp2Root
  ![((-250 : ℝ) / 1573) * 1,
    ((150 : ℝ) / 1573) * 1]

theorem positiveCusp2Rates_positive : PositiveVector positiveCusp2Rates := by
  have hl : (-1 : ℝ) < positiveCusp2Root := by norm_num [positiveCusp2Root]
  have hu : positiveCusp2Root < (1 : ℝ) := by norm_num [positiveCusp2Root]
  have hs : 0 ≤ positiveCusp2Root ^ 2 := sq_nonneg positiveCusp2Root
  intro k
  fin_cases k <;> simp [positiveCusp2Rates] <;> nlinarith

theorem positiveCusp2_jacobian_values :
    positiveCusp2.toNetwork.jacobian positiveCusp2Rates unitState 0 0 = ((-10 : ℝ) / 11) * 1 ∧
    positiveCusp2.toNetwork.jacobian positiveCusp2Rates unitState 0 1 = ((5 : ℝ) / 11) * 1 ∧
    positiveCusp2.toNetwork.jacobian positiveCusp2Rates unitState 1 0 = ((6 : ℝ) / 11) * 1 ∧
    positiveCusp2.toNetwork.jacobian positiveCusp2Rates unitState 1 1 = ((-3 : ℝ) / 11) * 1 := by
  norm_num [positiveCusp2, positiveCusp2Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp2_Bqq_values :
    positiveCusp2.toNetwork.hessianApply positiveCusp2Rates unitState
        positiveCusp2RightKernel positiveCusp2RightKernel 0 = ((-250 : ℝ) / 1331) * 1 ∧
    positiveCusp2.toNetwork.hessianApply positiveCusp2Rates unitState
        positiveCusp2RightKernel positiveCusp2RightKernel 1 = ((150 : ℝ) / 1331) * 1 := by
  rcases positiveCusp2Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp2, positiveCusp2Rates, positiveCusp2RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp2_Bqh_values :
    positiveCusp2.toNetwork.hessianApply positiveCusp2Rates unitState
        positiveCusp2RightKernel positiveCusp2Center 0 = ((9250 : ℝ) / 190333) * 1 ∧
    positiveCusp2.toNetwork.hessianApply positiveCusp2Rates unitState
        positiveCusp2RightKernel positiveCusp2Center 1 = ((-7500 : ℝ) / 190333) * 1 := by
  rcases positiveCusp2Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp2, positiveCusp2Rates, positiveCusp2RightKernel,
    positiveCusp2Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp2_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp2.toNetwork positiveCusp2Rates
      positiveCusp2RightKernel positiveCusp2LeftKernel positiveCusp2Center 0 4).unfoldingMatrix =
      ((-297 : ℝ) / 845) * 1 := by
  rcases positiveCusp2Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp2, positiveCusp2Rates, positiveCusp2RightKernel, positiveCusp2LeftKernel,
      positiveCusp2Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp2_cubic_value :
    dot positiveCusp2LeftKernel (positiveCusp2.toNetwork.hessianApply positiveCusp2Rates unitState
      positiveCusp2RightKernel positiveCusp2Center) = ((-150 : ℝ) / 17303) * 1 := by
  rcases positiveCusp2Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp2_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp2LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp2_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp2.toNetwork := by
  rcases positiveCusp2Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl : (-1 : ℝ) < positiveCusp2Root := by norm_num [positiveCusp2Root]
  have hu : positiveCusp2Root < (1 : ℝ) := by norm_num [positiveCusp2Root]
  have hs : 0 ≤ positiveCusp2Root ^ 2 := sq_nonneg positiveCusp2Root
  rcases positiveCusp2_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp2_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp2_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp2.toNetwork positiveCusp2Rates
    positiveCusp2RightKernel positiveCusp2LeftKernel positiveCusp2Center 0 4
  · exact positiveCusp2Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp2, positiveCusp2Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp2RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp2LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp2LeftKernel, positiveCusp2RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp2LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp2Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp2LeftKernel, positiveCusp2Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp2_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp2_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
