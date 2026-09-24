import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

def positiveCusp40Root : ℝ := 0

theorem positiveCusp40Root_equation : (1 : ℝ) * positiveCusp40Root = 0 := by
  norm_num [positiveCusp40Root]


theorem positiveCusp40Root_power_relations :
    let t := positiveCusp40Root
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
  have h := positiveCusp40Root_equation

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

def positiveCusp40 : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp40Rates : Fin 5 → ℝ :=
  let t := positiveCusp40Root
  ![((6 : ℝ) / 19) * 1,
    ((6 : ℝ) / 19) * 1,
    ((1 : ℝ) / 19) * 1,
    ((5 : ℝ) / 19) * 1,
    ((1 : ℝ) / 19) * 1]

noncomputable def positiveCusp40RightKernel : Species → ℝ :=
  let t := positiveCusp40Root
  ![((-3 : ℝ) / 19) * 1,
    ((3 : ℝ) / 19) * 1]

noncomputable def positiveCusp40LeftKernel : Species → ℝ :=
  let t := positiveCusp40Root
  ![((-19 : ℝ) / 6) * 1,
    ((19 : ℝ) / 6) * 1]

noncomputable def positiveCusp40Center : Species → ℝ :=
  let t := positiveCusp40Root
  ![((12 : ℝ) / 361) * 1,
    ((12 : ℝ) / 361) * 1]

theorem positiveCusp40Rates_positive : PositiveVector positiveCusp40Rates := by
  have hl : (-1 : ℝ) < positiveCusp40Root := by norm_num [positiveCusp40Root]
  have hu : positiveCusp40Root < (1 : ℝ) := by norm_num [positiveCusp40Root]
  have hs : 0 ≤ positiveCusp40Root ^ 2 := sq_nonneg positiveCusp40Root
  intro k
  fin_cases k <;> simp [positiveCusp40Rates] <;> nlinarith

theorem positiveCusp40_jacobian_values :
    positiveCusp40.toNetwork.jacobian positiveCusp40Rates unitState 0 0 = ((-3 : ℝ) / 19) * 1 ∧
    positiveCusp40.toNetwork.jacobian positiveCusp40Rates unitState 0 1 = ((-3 : ℝ) / 19) * 1 ∧
    positiveCusp40.toNetwork.jacobian positiveCusp40Rates unitState 1 0 = ((-3 : ℝ) / 19) * 1 ∧
    positiveCusp40.toNetwork.jacobian positiveCusp40Rates unitState 1 1 = ((-3 : ℝ) / 19) * 1 := by
  norm_num [positiveCusp40, positiveCusp40Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp40_Bqq_values :
    positiveCusp40.toNetwork.hessianApply positiveCusp40Rates unitState
        positiveCusp40RightKernel positiveCusp40RightKernel 0 = ((72 : ℝ) / 6859) * 1 ∧
    positiveCusp40.toNetwork.hessianApply positiveCusp40Rates unitState
        positiveCusp40RightKernel positiveCusp40RightKernel 1 = ((72 : ℝ) / 6859) * 1 := by
  rcases positiveCusp40Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp40, positiveCusp40Rates, positiveCusp40RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp40_Bqh_values :
    positiveCusp40.toNetwork.hessianApply positiveCusp40Rates unitState
        positiveCusp40RightKernel positiveCusp40Center 0 = ((216 : ℝ) / 130321) * 1 ∧
    positiveCusp40.toNetwork.hessianApply positiveCusp40Rates unitState
        positiveCusp40RightKernel positiveCusp40Center 1 = ((-216 : ℝ) / 130321) * 1 := by
  rcases positiveCusp40Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp40, positiveCusp40Rates, positiveCusp40RightKernel,
    positiveCusp40Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp40_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp40.toNetwork positiveCusp40Rates
      positiveCusp40RightKernel positiveCusp40LeftKernel positiveCusp40Center 2 4).unfoldingMatrix =
      (-57 : ℝ) * 1 := by
  rcases positiveCusp40Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp40, positiveCusp40Rates, positiveCusp40RightKernel, positiveCusp40LeftKernel,
      positiveCusp40Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp40_cubic_value :
    dot positiveCusp40LeftKernel (positiveCusp40.toNetwork.hessianApply positiveCusp40Rates unitState
      positiveCusp40RightKernel positiveCusp40Center) = ((-72 : ℝ) / 6859) * 1 := by
  rcases positiveCusp40Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp40_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp40LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp40_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp40.toNetwork := by
  rcases positiveCusp40Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl : (-1 : ℝ) < positiveCusp40Root := by norm_num [positiveCusp40Root]
  have hu : positiveCusp40Root < (1 : ℝ) := by norm_num [positiveCusp40Root]
  have hs : 0 ≤ positiveCusp40Root ^ 2 := sq_nonneg positiveCusp40Root
  rcases positiveCusp40_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp40_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp40_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp40.toNetwork positiveCusp40Rates
    positiveCusp40RightKernel positiveCusp40LeftKernel positiveCusp40Center 2 4
  · exact positiveCusp40Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp40, positiveCusp40Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp40RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp40LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp40LeftKernel, positiveCusp40RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp40LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp40Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp40LeftKernel, positiveCusp40Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp40_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp40_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
