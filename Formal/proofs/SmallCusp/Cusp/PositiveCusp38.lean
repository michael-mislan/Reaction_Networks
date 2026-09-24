import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

def positiveCusp38Root : ℝ := 0

theorem positiveCusp38Root_equation : (1 : ℝ) * positiveCusp38Root = 0 := by
  norm_num [positiveCusp38Root]


theorem positiveCusp38Root_power_relations :
    let t := positiveCusp38Root
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
  have h := positiveCusp38Root_equation

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

def positiveCusp38 : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp38Rates : Fin 5 → ℝ :=
  let t := positiveCusp38Root
  ![((2 : ℝ) / 47) * 1,
    ((16 : ℝ) / 47) * 1,
    ((2 : ℝ) / 47) * 1,
    ((18 : ℝ) / 47) * 1,
    ((9 : ℝ) / 47) * 1]

noncomputable def positiveCusp38RightKernel : Species → ℝ :=
  let t := positiveCusp38Root
  ![((18 : ℝ) / 47) * 1,
    ((6 : ℝ) / 47) * 1]

noncomputable def positiveCusp38LeftKernel : Species → ℝ :=
  let t := positiveCusp38Root
  ![((47 : ℝ) / 20) * 1,
    ((47 : ℝ) / 60) * 1]

noncomputable def positiveCusp38Center : Species → ℝ :=
  let t := positiveCusp38Root
  ![((108 : ℝ) / 11045) * 1,
    ((-324 : ℝ) / 11045) * 1]

theorem positiveCusp38Rates_positive : PositiveVector positiveCusp38Rates := by
  have hl : (-1 : ℝ) < positiveCusp38Root := by norm_num [positiveCusp38Root]
  have hu : positiveCusp38Root < (1 : ℝ) := by norm_num [positiveCusp38Root]
  have hs : 0 ≤ positiveCusp38Root ^ 2 := sq_nonneg positiveCusp38Root
  intro k
  fin_cases k <;> simp [positiveCusp38Rates] <;> nlinarith

theorem positiveCusp38_jacobian_values :
    positiveCusp38.toNetwork.jacobian positiveCusp38Rates unitState 0 0 = ((-6 : ℝ) / 47) * 1 ∧
    positiveCusp38.toNetwork.jacobian positiveCusp38Rates unitState 0 1 = ((18 : ℝ) / 47) * 1 ∧
    positiveCusp38.toNetwork.jacobian positiveCusp38Rates unitState 1 0 = ((18 : ℝ) / 47) * 1 ∧
    positiveCusp38.toNetwork.jacobian positiveCusp38Rates unitState 1 1 = ((-54 : ℝ) / 47) * 1 := by
  norm_num [positiveCusp38, positiveCusp38Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp38_Bqq_values :
    positiveCusp38.toNetwork.hessianApply positiveCusp38Rates unitState
        positiveCusp38RightKernel positiveCusp38RightKernel 0 = ((1296 : ℝ) / 103823) * 1 ∧
    positiveCusp38.toNetwork.hessianApply positiveCusp38Rates unitState
        positiveCusp38RightKernel positiveCusp38RightKernel 1 = ((-3888 : ℝ) / 103823) * 1 := by
  rcases positiveCusp38Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp38, positiveCusp38Rates, positiveCusp38RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp38_Bqh_values :
    positiveCusp38.toNetwork.hessianApply positiveCusp38Rates unitState
        positiveCusp38RightKernel positiveCusp38Center 0 = ((-108864 : ℝ) / 24398405) * 1 ∧
    positiveCusp38.toNetwork.hessianApply positiveCusp38Rates unitState
        positiveCusp38RightKernel positiveCusp38Center 1 = ((171072 : ℝ) / 24398405) * 1 := by
  rcases positiveCusp38Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp38, positiveCusp38Rates, positiveCusp38RightKernel,
    positiveCusp38Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp38_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp38.toNetwork positiveCusp38Rates
      positiveCusp38RightKernel positiveCusp38LeftKernel positiveCusp38Center 0 2).unfoldingMatrix =
      ((-47 : ℝ) / 5) * 1 := by
  rcases positiveCusp38Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp38, positiveCusp38Rates, positiveCusp38RightKernel, positiveCusp38LeftKernel,
      positiveCusp38Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp38_cubic_value :
    dot positiveCusp38LeftKernel (positiveCusp38.toNetwork.hessianApply positiveCusp38Rates unitState
      positiveCusp38RightKernel positiveCusp38Center) = ((-2592 : ℝ) / 519115) * 1 := by
  rcases positiveCusp38Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp38_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp38LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp38_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp38.toNetwork := by
  rcases positiveCusp38Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl : (-1 : ℝ) < positiveCusp38Root := by norm_num [positiveCusp38Root]
  have hu : positiveCusp38Root < (1 : ℝ) := by norm_num [positiveCusp38Root]
  have hs : 0 ≤ positiveCusp38Root ^ 2 := sq_nonneg positiveCusp38Root
  rcases positiveCusp38_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp38_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp38_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp38.toNetwork positiveCusp38Rates
    positiveCusp38RightKernel positiveCusp38LeftKernel positiveCusp38Center 0 2
  · exact positiveCusp38Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp38, positiveCusp38Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp38RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp38LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp38LeftKernel, positiveCusp38RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp38LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp38Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp38LeftKernel, positiveCusp38Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp38_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp38_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
