import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

def positiveCusp45Root : ℝ := 0

theorem positiveCusp45Root_equation : (1 : ℝ) * positiveCusp45Root = 0 := by
  norm_num [positiveCusp45Root]


theorem positiveCusp45Root_power_relations :
    let t := positiveCusp45Root
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
  have h := positiveCusp45Root_equation

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

def positiveCusp45 : CodedBimolNetwork where
  reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp45Rates : Fin 5 → ℝ :=
  let t := positiveCusp45Root
  ![((1 : ℝ) / 9) * 1,
    ((1 : ℝ) / 3) * 1,
    ((1 : ℝ) / 6) * 1,
    ((1 : ℝ) / 3) * 1,
    ((1 : ℝ) / 18) * 1]

noncomputable def positiveCusp45RightKernel : Species → ℝ :=
  let t := positiveCusp45Root
  ![((5 : ℝ) / 9) * 1,
    ((10 : ℝ) / 9) * 1]

noncomputable def positiveCusp45LeftKernel : Species → ℝ :=
  let t := positiveCusp45Root
  ![((3 : ℝ) / 10) * 1,
    ((3 : ℝ) / 4) * 1]

noncomputable def positiveCusp45Center : Species → ℝ :=
  let t := positiveCusp45Root
  ![((-125 : ℝ) / 486) * 1,
    ((25 : ℝ) / 243) * 1]

theorem positiveCusp45Rates_positive : PositiveVector positiveCusp45Rates := by
  have hl : (-1 : ℝ) < positiveCusp45Root := by norm_num [positiveCusp45Root]
  have hu : positiveCusp45Root < (1 : ℝ) := by norm_num [positiveCusp45Root]
  have hs : 0 ≤ positiveCusp45Root ^ 2 := sq_nonneg positiveCusp45Root
  intro k
  fin_cases k <;> simp [positiveCusp45Rates] <;> nlinarith

theorem positiveCusp45_jacobian_values :
    positiveCusp45.toNetwork.jacobian positiveCusp45Rates unitState 0 0 = ((-10 : ℝ) / 9) * 1 ∧
    positiveCusp45.toNetwork.jacobian positiveCusp45Rates unitState 0 1 = ((5 : ℝ) / 9) * 1 ∧
    positiveCusp45.toNetwork.jacobian positiveCusp45Rates unitState 1 0 = ((4 : ℝ) / 9) * 1 ∧
    positiveCusp45.toNetwork.jacobian positiveCusp45Rates unitState 1 1 = ((-2 : ℝ) / 9) * 1 := by
  norm_num [positiveCusp45, positiveCusp45Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp45_Bqq_values :
    positiveCusp45.toNetwork.hessianApply positiveCusp45Rates unitState
        positiveCusp45RightKernel positiveCusp45RightKernel 0 = ((-250 : ℝ) / 729) * 1 ∧
    positiveCusp45.toNetwork.hessianApply positiveCusp45Rates unitState
        positiveCusp45RightKernel positiveCusp45RightKernel 1 = ((100 : ℝ) / 729) * 1 := by
  rcases positiveCusp45Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp45, positiveCusp45Rates, positiveCusp45RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp45_Bqh_values :
    positiveCusp45.toNetwork.hessianApply positiveCusp45Rates unitState
        positiveCusp45RightKernel positiveCusp45Center 0 = ((3875 : ℝ) / 19683) * 1 ∧
    positiveCusp45.toNetwork.hessianApply positiveCusp45Rates unitState
        positiveCusp45RightKernel positiveCusp45Center 1 = ((-2000 : ℝ) / 19683) * 1 := by
  rcases positiveCusp45Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp45, positiveCusp45Rates, positiveCusp45RightKernel,
    positiveCusp45Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp45_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp45.toNetwork positiveCusp45Rates
      positiveCusp45RightKernel positiveCusp45LeftKernel positiveCusp45Center 0 4).unfoldingMatrix =
      ((-27 : ℝ) / 40) * 1 := by
  rcases positiveCusp45Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp45, positiveCusp45Rates, positiveCusp45RightKernel, positiveCusp45LeftKernel,
      positiveCusp45Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp45_cubic_value :
    dot positiveCusp45LeftKernel (positiveCusp45.toNetwork.hessianApply positiveCusp45Rates unitState
      positiveCusp45RightKernel positiveCusp45Center) = ((-25 : ℝ) / 1458) * 1 := by
  rcases positiveCusp45Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp45_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp45LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp45_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp45.toNetwork := by
  rcases positiveCusp45Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl : (-1 : ℝ) < positiveCusp45Root := by norm_num [positiveCusp45Root]
  have hu : positiveCusp45Root < (1 : ℝ) := by norm_num [positiveCusp45Root]
  have hs : 0 ≤ positiveCusp45Root ^ 2 := sq_nonneg positiveCusp45Root
  rcases positiveCusp45_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp45_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp45_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp45.toNetwork positiveCusp45Rates
    positiveCusp45RightKernel positiveCusp45LeftKernel positiveCusp45Center 0 4
  · exact positiveCusp45Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp45, positiveCusp45Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp45RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp45LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp45LeftKernel, positiveCusp45RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp45LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp45Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp45LeftKernel, positiveCusp45Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp45_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp45_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
