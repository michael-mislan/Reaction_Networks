import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

def positiveCusp33Root : ℝ := 0

theorem positiveCusp33Root_equation : (1 : ℝ) * positiveCusp33Root = 0 := by
  norm_num [positiveCusp33Root]


theorem positiveCusp33Root_power_relations :
    let t := positiveCusp33Root
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
  have h := positiveCusp33Root_equation

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

def positiveCusp33 : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .xy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp33Rates : Fin 5 → ℝ :=
  let t := positiveCusp33Root
  ![((1 : ℝ) / 28) * 1,
    ((9 : ℝ) / 28) * 1,
    ((2 : ℝ) / 7) * 1,
    ((9 : ℝ) / 28) * 1,
    ((1 : ℝ) / 28) * 1]

noncomputable def positiveCusp33RightKernel : Species → ℝ :=
  let t := positiveCusp33Root
  ![((9 : ℝ) / 14) * 1,
    ((27 : ℝ) / 28) * 1]

noncomputable def positiveCusp33LeftKernel : Species → ℝ :=
  let t := positiveCusp33Root
  ![((56 : ℝ) / 117) * 1,
    ((28 : ℝ) / 39) * 1]

noncomputable def positiveCusp33Center : Species → ℝ :=
  let t := positiveCusp33Root
  ![((-729 : ℝ) / 5096) * 1,
    ((243 : ℝ) / 2548) * 1]

theorem positiveCusp33Rates_positive : PositiveVector positiveCusp33Rates := by
  have hl : (-1 : ℝ) < positiveCusp33Root := by norm_num [positiveCusp33Root]
  have hu : positiveCusp33Root < (1 : ℝ) := by norm_num [positiveCusp33Root]
  have hs : 0 ≤ positiveCusp33Root ^ 2 := sq_nonneg positiveCusp33Root
  intro k
  fin_cases k <;> simp [positiveCusp33Rates] <;> nlinarith

theorem positiveCusp33_jacobian_values :
    positiveCusp33.toNetwork.jacobian positiveCusp33Rates unitState 0 0 = ((-27 : ℝ) / 28) * 1 ∧
    positiveCusp33.toNetwork.jacobian positiveCusp33Rates unitState 0 1 = ((9 : ℝ) / 14) * 1 ∧
    positiveCusp33.toNetwork.jacobian positiveCusp33Rates unitState 1 0 = ((9 : ℝ) / 14) * 1 ∧
    positiveCusp33.toNetwork.jacobian positiveCusp33Rates unitState 1 1 = ((-3 : ℝ) / 7) * 1 := by
  norm_num [positiveCusp33, positiveCusp33Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp33_Bqq_values :
    positiveCusp33.toNetwork.hessianApply positiveCusp33Rates unitState
        positiveCusp33RightKernel positiveCusp33RightKernel 0 = ((-2187 : ℝ) / 10976) * 1 ∧
    positiveCusp33.toNetwork.hessianApply positiveCusp33Rates unitState
        positiveCusp33RightKernel positiveCusp33RightKernel 1 = ((729 : ℝ) / 5488) * 1 := by
  rcases positiveCusp33Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp33, positiveCusp33Rates, positiveCusp33RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp33_Bqh_values :
    positiveCusp33.toNetwork.hessianApply positiveCusp33Rates unitState
        positiveCusp33RightKernel positiveCusp33Center 0 = ((32805 : ℝ) / 499408) * 1 ∧
    positiveCusp33.toNetwork.hessianApply positiveCusp33Rates unitState
        positiveCusp33RightKernel positiveCusp33Center 1 = ((-72171 : ℝ) / 998816) * 1 := by
  rcases positiveCusp33Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp33, positiveCusp33Rates, positiveCusp33RightKernel,
    positiveCusp33Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp33_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp33.toNetwork positiveCusp33Rates
      positiveCusp33RightKernel positiveCusp33LeftKernel positiveCusp33Center 0 4).unfoldingMatrix =
      ((-1120 : ℝ) / 507) * 1 := by
  rcases positiveCusp33Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp33, positiveCusp33Rates, positiveCusp33RightKernel, positiveCusp33LeftKernel,
      positiveCusp33Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp33_cubic_value :
    dot positiveCusp33LeftKernel (positiveCusp33.toNetwork.hessianApply positiveCusp33Rates unitState
      positiveCusp33RightKernel positiveCusp33Center) = ((-729 : ℝ) / 35672) * 1 := by
  rcases positiveCusp33Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp33_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp33LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp33_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp33.toNetwork := by
  rcases positiveCusp33Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl : (-1 : ℝ) < positiveCusp33Root := by norm_num [positiveCusp33Root]
  have hu : positiveCusp33Root < (1 : ℝ) := by norm_num [positiveCusp33Root]
  have hs : 0 ≤ positiveCusp33Root ^ 2 := sq_nonneg positiveCusp33Root
  rcases positiveCusp33_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp33_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp33_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp33.toNetwork positiveCusp33Rates
    positiveCusp33RightKernel positiveCusp33LeftKernel positiveCusp33Center 0 4
  · exact positiveCusp33Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp33, positiveCusp33Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp33RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp33LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp33LeftKernel, positiveCusp33RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp33LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp33Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp33LeftKernel, positiveCusp33Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp33_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp33_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
