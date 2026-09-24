import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

def positiveCusp42Root : ℝ := 0

theorem positiveCusp42Root_equation : (1 : ℝ) * positiveCusp42Root = 0 := by
  norm_num [positiveCusp42Root]


theorem positiveCusp42Root_power_relations :
    let t := positiveCusp42Root
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
  have h := positiveCusp42Root_equation

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

def positiveCusp42 : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp42Rates : Fin 5 → ℝ :=
  let t := positiveCusp42Root
  ![((8 : ℝ) / 27) * 1,
    ((8 : ℝ) / 27) * 1,
    ((2 : ℝ) / 27) * 1,
    ((8 : ℝ) / 27) * 1,
    ((1 : ℝ) / 27) * 1]

noncomputable def positiveCusp42RightKernel : Species → ℝ :=
  let t := positiveCusp42Root
  ![((-4 : ℝ) / 27) * 1,
    ((4 : ℝ) / 27) * 1]

noncomputable def positiveCusp42LeftKernel : Species → ℝ :=
  let t := positiveCusp42Root
  ![((-27 : ℝ) / 8) * 1,
    ((27 : ℝ) / 8) * 1]

noncomputable def positiveCusp42Center : Species → ℝ :=
  let t := positiveCusp42Root
  ![((32 : ℝ) / 729) * 1,
    ((32 : ℝ) / 729) * 1]

theorem positiveCusp42Rates_positive : PositiveVector positiveCusp42Rates := by
  have hl : (-1 : ℝ) < positiveCusp42Root := by norm_num [positiveCusp42Root]
  have hu : positiveCusp42Root < (1 : ℝ) := by norm_num [positiveCusp42Root]
  have hs : 0 ≤ positiveCusp42Root ^ 2 := sq_nonneg positiveCusp42Root
  intro k
  fin_cases k <;> simp [positiveCusp42Rates] <;> nlinarith

theorem positiveCusp42_jacobian_values :
    positiveCusp42.toNetwork.jacobian positiveCusp42Rates unitState 0 0 = ((-4 : ℝ) / 27) * 1 ∧
    positiveCusp42.toNetwork.jacobian positiveCusp42Rates unitState 0 1 = ((-4 : ℝ) / 27) * 1 ∧
    positiveCusp42.toNetwork.jacobian positiveCusp42Rates unitState 1 0 = ((-4 : ℝ) / 27) * 1 ∧
    positiveCusp42.toNetwork.jacobian positiveCusp42Rates unitState 1 1 = ((-4 : ℝ) / 27) * 1 := by
  norm_num [positiveCusp42, positiveCusp42Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp42_Bqq_values :
    positiveCusp42.toNetwork.hessianApply positiveCusp42Rates unitState
        positiveCusp42RightKernel positiveCusp42RightKernel 0 = ((256 : ℝ) / 19683) * 1 ∧
    positiveCusp42.toNetwork.hessianApply positiveCusp42Rates unitState
        positiveCusp42RightKernel positiveCusp42RightKernel 1 = ((256 : ℝ) / 19683) * 1 := by
  rcases positiveCusp42Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp42, positiveCusp42Rates, positiveCusp42RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp42_Bqh_values :
    positiveCusp42.toNetwork.hessianApply positiveCusp42Rates unitState
        positiveCusp42RightKernel positiveCusp42Center 0 = ((1024 : ℝ) / 531441) * 1 ∧
    positiveCusp42.toNetwork.hessianApply positiveCusp42Rates unitState
        positiveCusp42RightKernel positiveCusp42Center 1 = ((-1024 : ℝ) / 531441) * 1 := by
  rcases positiveCusp42Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp42, positiveCusp42Rates, positiveCusp42RightKernel,
    positiveCusp42Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp42_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp42.toNetwork positiveCusp42Rates
      positiveCusp42RightKernel positiveCusp42LeftKernel positiveCusp42Center 2 4).unfoldingMatrix =
      (-54 : ℝ) * 1 := by
  rcases positiveCusp42Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp42, positiveCusp42Rates, positiveCusp42RightKernel, positiveCusp42LeftKernel,
      positiveCusp42Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp42_cubic_value :
    dot positiveCusp42LeftKernel (positiveCusp42.toNetwork.hessianApply positiveCusp42Rates unitState
      positiveCusp42RightKernel positiveCusp42Center) = ((-256 : ℝ) / 19683) * 1 := by
  rcases positiveCusp42Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp42_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp42LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp42_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp42.toNetwork := by
  rcases positiveCusp42Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl : (-1 : ℝ) < positiveCusp42Root := by norm_num [positiveCusp42Root]
  have hu : positiveCusp42Root < (1 : ℝ) := by norm_num [positiveCusp42Root]
  have hs : 0 ≤ positiveCusp42Root ^ 2 := sq_nonneg positiveCusp42Root
  rcases positiveCusp42_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp42_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp42_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp42.toNetwork positiveCusp42Rates
    positiveCusp42RightKernel positiveCusp42LeftKernel positiveCusp42Center 2 4
  · exact positiveCusp42Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp42, positiveCusp42Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp42RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp42LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp42LeftKernel, positiveCusp42RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp42LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp42Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp42LeftKernel, positiveCusp42Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp42_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp42_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
