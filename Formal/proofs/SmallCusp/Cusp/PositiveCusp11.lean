import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

def positiveCusp11Root : ℝ := 0

theorem positiveCusp11Root_equation : (1 : ℝ) * positiveCusp11Root = 0 := by
  norm_num [positiveCusp11Root]


theorem positiveCusp11Root_power_relations :
    let t := positiveCusp11Root
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
  have h := positiveCusp11Root_equation

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

def positiveCusp11 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .zero), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp11Rates : Fin 5 → ℝ :=
  let t := positiveCusp11Root
  ![((2 : ℝ) / 27) * 1,
    ((8 : ℝ) / 27) * 1,
    ((8 : ℝ) / 27) * 1,
    ((1 : ℝ) / 27) * 1,
    ((8 : ℝ) / 27) * 1]

noncomputable def positiveCusp11RightKernel : Species → ℝ :=
  let t := positiveCusp11Root
  ![((8 : ℝ) / 27) * 1,
    ((4 : ℝ) / 27) * 1]

noncomputable def positiveCusp11LeftKernel : Species → ℝ :=
  let t := positiveCusp11Root
  ![((27 : ℝ) / 10) * 1,
    ((27 : ℝ) / 20) * 1]

noncomputable def positiveCusp11Center : Species → ℝ :=
  let t := positiveCusp11Root
  ![((64 : ℝ) / 3645) * 1,
    ((-128 : ℝ) / 3645) * 1]

theorem positiveCusp11Rates_positive : PositiveVector positiveCusp11Rates := by
  have hl : (-1 : ℝ) < positiveCusp11Root := by norm_num [positiveCusp11Root]
  have hu : positiveCusp11Root < (1 : ℝ) := by norm_num [positiveCusp11Root]
  have hs : 0 ≤ positiveCusp11Root ^ 2 := sq_nonneg positiveCusp11Root
  intro k
  fin_cases k <;> simp [positiveCusp11Rates] <;> nlinarith

theorem positiveCusp11_jacobian_values :
    positiveCusp11.toNetwork.jacobian positiveCusp11Rates unitState 0 0 = ((-4 : ℝ) / 27) * 1 ∧
    positiveCusp11.toNetwork.jacobian positiveCusp11Rates unitState 0 1 = ((8 : ℝ) / 27) * 1 ∧
    positiveCusp11.toNetwork.jacobian positiveCusp11Rates unitState 1 0 = ((8 : ℝ) / 27) * 1 ∧
    positiveCusp11.toNetwork.jacobian positiveCusp11Rates unitState 1 1 = ((-16 : ℝ) / 27) * 1 := by
  norm_num [positiveCusp11, positiveCusp11Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp11_Bqq_values :
    positiveCusp11.toNetwork.hessianApply positiveCusp11Rates unitState
        positiveCusp11RightKernel positiveCusp11RightKernel 0 = ((256 : ℝ) / 19683) * 1 ∧
    positiveCusp11.toNetwork.hessianApply positiveCusp11Rates unitState
        positiveCusp11RightKernel positiveCusp11RightKernel 1 = ((-512 : ℝ) / 19683) * 1 := by
  rcases positiveCusp11Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp11, positiveCusp11Rates, positiveCusp11RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp11_Bqh_values :
    positiveCusp11.toNetwork.hessianApply positiveCusp11Rates unitState
        positiveCusp11RightKernel positiveCusp11Center 0 = ((-8192 : ℝ) / 2657205) * 1 ∧
    positiveCusp11.toNetwork.hessianApply positiveCusp11Rates unitState
        positiveCusp11RightKernel positiveCusp11Center 1 = ((2048 : ℝ) / 885735) * 1 := by
  rcases positiveCusp11Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp11, positiveCusp11Rates, positiveCusp11RightKernel,
    positiveCusp11Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp11_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp11.toNetwork positiveCusp11Rates
      positiveCusp11RightKernel positiveCusp11LeftKernel positiveCusp11Center 0 3).unfoldingMatrix =
      ((-216 : ℝ) / 25) * 1 := by
  rcases positiveCusp11Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp11, positiveCusp11Rates, positiveCusp11RightKernel, positiveCusp11LeftKernel,
      positiveCusp11Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp11_cubic_value :
    dot positiveCusp11LeftKernel (positiveCusp11.toNetwork.hessianApply positiveCusp11Rates unitState
      positiveCusp11RightKernel positiveCusp11Center) = ((-512 : ℝ) / 98415) * 1 := by
  rcases positiveCusp11Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp11_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp11LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp11_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp11.toNetwork := by
  rcases positiveCusp11Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl : (-1 : ℝ) < positiveCusp11Root := by norm_num [positiveCusp11Root]
  have hu : positiveCusp11Root < (1 : ℝ) := by norm_num [positiveCusp11Root]
  have hs : 0 ≤ positiveCusp11Root ^ 2 := sq_nonneg positiveCusp11Root
  rcases positiveCusp11_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp11_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp11_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp11.toNetwork positiveCusp11Rates
    positiveCusp11RightKernel positiveCusp11LeftKernel positiveCusp11Center 0 3
  · exact positiveCusp11Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp11, positiveCusp11Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp11RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp11LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp11LeftKernel, positiveCusp11RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp11LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp11Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp11LeftKernel, positiveCusp11Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp11_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp11_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
