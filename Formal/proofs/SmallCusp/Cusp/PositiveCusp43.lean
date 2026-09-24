import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

def positiveCusp43Root : ℝ := 0

theorem positiveCusp43Root_equation : (1 : ℝ) * positiveCusp43Root = 0 := by
  norm_num [positiveCusp43Root]


theorem positiveCusp43Root_power_relations :
    let t := positiveCusp43Root
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
  have h := positiveCusp43Root_equation

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

def positiveCusp43 : CodedBimolNetwork where
  reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp43Rates : Fin 5 → ℝ :=
  let t := positiveCusp43Root
  ![((4 : ℝ) / 33) * 1,
    ((4 : ℝ) / 11) * 1,
    ((9 : ℝ) / 55) * 1,
    ((52 : ℝ) / 165) * 1,
    ((2 : ℝ) / 55) * 1]

noncomputable def positiveCusp43RightKernel : Species → ℝ :=
  let t := positiveCusp43Root
  ![((16 : ℝ) / 33) * 1,
    ((12 : ℝ) / 11) * 1]

noncomputable def positiveCusp43LeftKernel : Species → ℝ :=
  let t := positiveCusp43Root
  ![((33 : ℝ) / 106) * 1,
    ((165 : ℝ) / 212) * 1]

noncomputable def positiveCusp43Center : Species → ℝ :=
  let t := positiveCusp43Root
  ![((-2000 : ℝ) / 6413) * 1,
    ((800 : ℝ) / 6413) * 1]

theorem positiveCusp43Rates_positive : PositiveVector positiveCusp43Rates := by
  have hl : (-1 : ℝ) < positiveCusp43Root := by norm_num [positiveCusp43Root]
  have hu : positiveCusp43Root < (1 : ℝ) := by norm_num [positiveCusp43Root]
  have hs : 0 ≤ positiveCusp43Root ^ 2 := sq_nonneg positiveCusp43Root
  intro k
  fin_cases k <;> simp [positiveCusp43Rates] <;> nlinarith

theorem positiveCusp43_jacobian_values :
    positiveCusp43.toNetwork.jacobian positiveCusp43Rates unitState 0 0 = ((-12 : ℝ) / 11) * 1 ∧
    positiveCusp43.toNetwork.jacobian positiveCusp43Rates unitState 0 1 = ((16 : ℝ) / 33) * 1 ∧
    positiveCusp43.toNetwork.jacobian positiveCusp43Rates unitState 1 0 = ((24 : ℝ) / 55) * 1 ∧
    positiveCusp43.toNetwork.jacobian positiveCusp43Rates unitState 1 1 = ((-32 : ℝ) / 165) * 1 := by
  norm_num [positiveCusp43, positiveCusp43Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp43_Bqq_values :
    positiveCusp43.toNetwork.hessianApply positiveCusp43Rates unitState
        positiveCusp43RightKernel positiveCusp43RightKernel 0 = ((-1600 : ℝ) / 3993) * 1 ∧
    positiveCusp43.toNetwork.hessianApply positiveCusp43Rates unitState
        positiveCusp43RightKernel positiveCusp43RightKernel 1 = ((640 : ℝ) / 3993) * 1 := by
  rcases positiveCusp43Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp43, positiveCusp43Rates, positiveCusp43RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp43_Bqh_values :
    positiveCusp43.toNetwork.hessianApply positiveCusp43Rates unitState
        positiveCusp43RightKernel positiveCusp43Center 0 = ((1376000 : ℝ) / 6983757) * 1 ∧
    positiveCusp43.toNetwork.hessianApply positiveCusp43Rates unitState
        positiveCusp43RightKernel positiveCusp43Center 1 = ((-753920 : ℝ) / 6983757) * 1 := by
  rcases positiveCusp43Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp43, positiveCusp43Rates, positiveCusp43RightKernel,
    positiveCusp43Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp43_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp43.toNetwork positiveCusp43Rates
      positiveCusp43RightKernel positiveCusp43LeftKernel positiveCusp43Center 0 4).unfoldingMatrix =
      ((-2772 : ℝ) / 2809) * 1 := by
  rcases positiveCusp43Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp43, positiveCusp43Rates, positiveCusp43RightKernel, positiveCusp43LeftKernel,
      positiveCusp43Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp43_cubic_value :
    dot positiveCusp43LeftKernel (positiveCusp43.toNetwork.hessianApply positiveCusp43Rates unitState
      positiveCusp43RightKernel positiveCusp43Center) = ((-1600 : ℝ) / 70543) * 1 := by
  rcases positiveCusp43Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp43_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp43LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp43_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp43.toNetwork := by
  rcases positiveCusp43Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl : (-1 : ℝ) < positiveCusp43Root := by norm_num [positiveCusp43Root]
  have hu : positiveCusp43Root < (1 : ℝ) := by norm_num [positiveCusp43Root]
  have hs : 0 ≤ positiveCusp43Root ^ 2 := sq_nonneg positiveCusp43Root
  rcases positiveCusp43_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp43_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp43_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp43.toNetwork positiveCusp43Rates
    positiveCusp43RightKernel positiveCusp43LeftKernel positiveCusp43Center 0 4
  · exact positiveCusp43Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp43, positiveCusp43Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp43RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp43LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp43LeftKernel, positiveCusp43RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp43LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp43Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp43LeftKernel, positiveCusp43Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp43_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp43_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
