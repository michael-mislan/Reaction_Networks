import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

def positiveCusp35Root : ℝ := 0

theorem positiveCusp35Root_equation : (1 : ℝ) * positiveCusp35Root = 0 := by
  norm_num [positiveCusp35Root]


theorem positiveCusp35Root_power_relations :
    let t := positiveCusp35Root
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
  have h := positiveCusp35Root_equation

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

def positiveCusp35 : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp35Rates : Fin 5 → ℝ :=
  let t := positiveCusp35Root
  ![((1 : ℝ) / 19) * 1,
    ((6 : ℝ) / 19) * 1,
    ((5 : ℝ) / 19) * 1,
    ((6 : ℝ) / 19) * 1,
    ((1 : ℝ) / 19) * 1]

noncomputable def positiveCusp35RightKernel : Species → ℝ :=
  let t := positiveCusp35Root
  ![((6 : ℝ) / 19) * 1,
    ((12 : ℝ) / 19) * 1]

noncomputable def positiveCusp35LeftKernel : Species → ℝ :=
  let t := positiveCusp35Root
  ![((19 : ℝ) / 30) * 1,
    ((19 : ℝ) / 15) * 1]

noncomputable def positiveCusp35Center : Species → ℝ :=
  let t := positiveCusp35Root
  ![((-192 : ℝ) / 1805) * 1,
    ((96 : ℝ) / 1805) * 1]

theorem positiveCusp35Rates_positive : PositiveVector positiveCusp35Rates := by
  have hl : (-1 : ℝ) < positiveCusp35Root := by norm_num [positiveCusp35Root]
  have hu : positiveCusp35Root < (1 : ℝ) := by norm_num [positiveCusp35Root]
  have hs : 0 ≤ positiveCusp35Root ^ 2 := sq_nonneg positiveCusp35Root
  intro k
  fin_cases k <;> simp [positiveCusp35Rates] <;> nlinarith

theorem positiveCusp35_jacobian_values :
    positiveCusp35.toNetwork.jacobian positiveCusp35Rates unitState 0 0 = ((-12 : ℝ) / 19) * 1 ∧
    positiveCusp35.toNetwork.jacobian positiveCusp35Rates unitState 0 1 = ((6 : ℝ) / 19) * 1 ∧
    positiveCusp35.toNetwork.jacobian positiveCusp35Rates unitState 1 0 = ((6 : ℝ) / 19) * 1 ∧
    positiveCusp35.toNetwork.jacobian positiveCusp35Rates unitState 1 1 = ((-3 : ℝ) / 19) * 1 := by
  norm_num [positiveCusp35, positiveCusp35Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp35_Bqq_values :
    positiveCusp35.toNetwork.hessianApply positiveCusp35Rates unitState
        positiveCusp35RightKernel positiveCusp35RightKernel 0 = ((-576 : ℝ) / 6859) * 1 ∧
    positiveCusp35.toNetwork.hessianApply positiveCusp35Rates unitState
        positiveCusp35RightKernel positiveCusp35RightKernel 1 = ((288 : ℝ) / 6859) * 1 := by
  rcases positiveCusp35Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp35, positiveCusp35Rates, positiveCusp35RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp35_Bqh_values :
    positiveCusp35.toNetwork.hessianApply positiveCusp35Rates unitState
        positiveCusp35RightKernel positiveCusp35Center 0 = ((12672 : ℝ) / 651605) * 1 ∧
    positiveCusp35.toNetwork.hessianApply positiveCusp35Rates unitState
        positiveCusp35RightKernel positiveCusp35Center 1 = ((-14976 : ℝ) / 651605) * 1 := by
  rcases positiveCusp35Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp35, positiveCusp35Rates, positiveCusp35RightKernel,
    positiveCusp35Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp35_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp35.toNetwork positiveCusp35Rates
      positiveCusp35RightKernel positiveCusp35LeftKernel positiveCusp35Center 0 4).unfoldingMatrix =
      ((-114 : ℝ) / 25) * 1 := by
  rcases positiveCusp35Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp35, positiveCusp35Rates, positiveCusp35RightKernel, positiveCusp35LeftKernel,
      positiveCusp35Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp35_cubic_value :
    dot positiveCusp35LeftKernel (positiveCusp35.toNetwork.hessianApply positiveCusp35Rates unitState
      positiveCusp35RightKernel positiveCusp35Center) = ((-576 : ℝ) / 34295) * 1 := by
  rcases positiveCusp35Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp35_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp35LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp35_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp35.toNetwork := by
  rcases positiveCusp35Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl : (-1 : ℝ) < positiveCusp35Root := by norm_num [positiveCusp35Root]
  have hu : positiveCusp35Root < (1 : ℝ) := by norm_num [positiveCusp35Root]
  have hs : 0 ≤ positiveCusp35Root ^ 2 := sq_nonneg positiveCusp35Root
  rcases positiveCusp35_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp35_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp35_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp35.toNetwork positiveCusp35Rates
    positiveCusp35RightKernel positiveCusp35LeftKernel positiveCusp35Center 0 4
  · exact positiveCusp35Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp35, positiveCusp35Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp35RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp35LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp35LeftKernel, positiveCusp35RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp35LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp35Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp35LeftKernel, positiveCusp35Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp35_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp35_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
