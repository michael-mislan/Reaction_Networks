import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

def positiveCusp32Root : ℝ := 0

theorem positiveCusp32Root_equation : (1 : ℝ) * positiveCusp32Root = 0 := by
  norm_num [positiveCusp32Root]


theorem positiveCusp32Root_power_relations :
    let t := positiveCusp32Root
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
  have h := positiveCusp32Root_equation

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

def positiveCusp32 : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .y)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp32Rates : Fin 5 → ℝ :=
  let t := positiveCusp32Root
  ![((1 : ℝ) / 32) * 1,
    ((13 : ℝ) / 48) * 1,
    ((5 : ℝ) / 16) * 1,
    ((9 : ℝ) / 32) * 1,
    ((5 : ℝ) / 48) * 1]

noncomputable def positiveCusp32RightKernel : Species → ℝ :=
  let t := positiveCusp32Root
  ![((25 : ℝ) / 48) * 1,
    ((15 : ℝ) / 16) * 1]

noncomputable def positiveCusp32LeftKernel : Species → ℝ :=
  let t := positiveCusp32Root
  ![((12 : ℝ) / 25) * 1,
    ((4 : ℝ) / 5) * 1]

noncomputable def positiveCusp32Center : Species → ℝ :=
  let t := positiveCusp32Root
  ![((-625 : ℝ) / 3072) * 1,
    ((125 : ℝ) / 1024) * 1]

theorem positiveCusp32Rates_positive : PositiveVector positiveCusp32Rates := by
  have hl : (-1 : ℝ) < positiveCusp32Root := by norm_num [positiveCusp32Root]
  have hu : positiveCusp32Root < (1 : ℝ) := by norm_num [positiveCusp32Root]
  have hs : 0 ≤ positiveCusp32Root ^ 2 := sq_nonneg positiveCusp32Root
  intro k
  fin_cases k <;> simp [positiveCusp32Rates] <;> nlinarith

theorem positiveCusp32_jacobian_values :
    positiveCusp32.toNetwork.jacobian positiveCusp32Rates unitState 0 0 = ((-15 : ℝ) / 16) * 1 ∧
    positiveCusp32.toNetwork.jacobian positiveCusp32Rates unitState 0 1 = ((25 : ℝ) / 48) * 1 ∧
    positiveCusp32.toNetwork.jacobian positiveCusp32Rates unitState 1 0 = ((9 : ℝ) / 16) * 1 ∧
    positiveCusp32.toNetwork.jacobian positiveCusp32Rates unitState 1 1 = ((-5 : ℝ) / 16) * 1 := by
  norm_num [positiveCusp32, positiveCusp32Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp32_Bqq_values :
    positiveCusp32.toNetwork.hessianApply positiveCusp32Rates unitState
        positiveCusp32RightKernel positiveCusp32RightKernel 0 = ((-3125 : ℝ) / 12288) * 1 ∧
    positiveCusp32.toNetwork.hessianApply positiveCusp32Rates unitState
        positiveCusp32RightKernel positiveCusp32RightKernel 1 = ((625 : ℝ) / 4096) * 1 := by
  rcases positiveCusp32Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp32, positiveCusp32Rates, positiveCusp32RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp32_Bqh_values :
    positiveCusp32.toNetwork.hessianApply positiveCusp32Rates unitState
        positiveCusp32RightKernel positiveCusp32Center 0 = ((171875 : ℝ) / 2359296) * 1 ∧
    positiveCusp32.toNetwork.hessianApply positiveCusp32Rates unitState
        positiveCusp32RightKernel positiveCusp32Center 1 = ((-15625 : ℝ) / 262144) * 1 := by
  rcases positiveCusp32Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp32, positiveCusp32Rates, positiveCusp32RightKernel,
    positiveCusp32Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp32_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp32.toNetwork positiveCusp32Rates
      positiveCusp32RightKernel positiveCusp32LeftKernel positiveCusp32Center 0 4).unfoldingMatrix =
      ((-112 : ℝ) / 125) * 1 := by
  rcases positiveCusp32Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp32, positiveCusp32Rates, positiveCusp32RightKernel, positiveCusp32LeftKernel,
      positiveCusp32Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp32_cubic_value :
    dot positiveCusp32LeftKernel (positiveCusp32.toNetwork.hessianApply positiveCusp32Rates unitState
      positiveCusp32RightKernel positiveCusp32Center) = ((-625 : ℝ) / 49152) * 1 := by
  rcases positiveCusp32Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp32_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp32LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp32_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp32.toNetwork := by
  rcases positiveCusp32Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl : (-1 : ℝ) < positiveCusp32Root := by norm_num [positiveCusp32Root]
  have hu : positiveCusp32Root < (1 : ℝ) := by norm_num [positiveCusp32Root]
  have hs : 0 ≤ positiveCusp32Root ^ 2 := sq_nonneg positiveCusp32Root
  rcases positiveCusp32_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp32_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp32_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp32.toNetwork positiveCusp32Rates
    positiveCusp32RightKernel positiveCusp32LeftKernel positiveCusp32Center 0 4
  · exact positiveCusp32Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp32, positiveCusp32Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp32RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp32LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp32LeftKernel, positiveCusp32RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp32LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp32Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp32LeftKernel, positiveCusp32Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp32_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp32_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
