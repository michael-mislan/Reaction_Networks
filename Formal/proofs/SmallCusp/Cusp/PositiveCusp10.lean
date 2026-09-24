import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

def positiveCusp10Root : ℝ := 0

theorem positiveCusp10Root_equation : (1 : ℝ) * positiveCusp10Root = 0 := by
  norm_num [positiveCusp10Root]


theorem positiveCusp10Root_power_relations :
    let t := positiveCusp10Root
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
  have h := positiveCusp10Root_equation

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

def positiveCusp10 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .xy), (.y, .yy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp10Rates : Fin 5 → ℝ :=
  let t := positiveCusp10Root
  ![((12 : ℝ) / 43) * 1,
    ((14 : ℝ) / 129) * 1,
    ((34 : ℝ) / 129) * 1,
    ((14 : ℝ) / 43) * 1,
    ((1 : ℝ) / 43) * 1]

noncomputable def positiveCusp10RightKernel : Species → ℝ :=
  let t := positiveCusp10Root
  ![((-10 : ℝ) / 43) * 1,
    ((14 : ℝ) / 43) * 1]

noncomputable def positiveCusp10LeftKernel : Species → ℝ :=
  let t := positiveCusp10Root
  ![((-43 : ℝ) / 31) * 1,
    ((129 : ℝ) / 62) * 1]

noncomputable def positiveCusp10Center : Species → ℝ :=
  let t := positiveCusp10Root
  ![((7056 : ℝ) / 57319) * 1,
    ((4704 : ℝ) / 57319) * 1]

theorem positiveCusp10Rates_positive : PositiveVector positiveCusp10Rates := by
  have hl : (-1 : ℝ) < positiveCusp10Root := by norm_num [positiveCusp10Root]
  have hu : positiveCusp10Root < (1 : ℝ) := by norm_num [positiveCusp10Root]
  have hs : 0 ≤ positiveCusp10Root ^ 2 := sq_nonneg positiveCusp10Root
  intro k
  fin_cases k <;> simp [positiveCusp10Rates] <;> nlinarith

theorem positiveCusp10_jacobian_values :
    positiveCusp10.toNetwork.jacobian positiveCusp10Rates unitState 0 0 = ((-14 : ℝ) / 43) * 1 ∧
    positiveCusp10.toNetwork.jacobian positiveCusp10Rates unitState 0 1 = ((-10 : ℝ) / 43) * 1 ∧
    positiveCusp10.toNetwork.jacobian positiveCusp10Rates unitState 1 0 = ((-28 : ℝ) / 129) * 1 ∧
    positiveCusp10.toNetwork.jacobian positiveCusp10Rates unitState 1 1 = ((-20 : ℝ) / 129) * 1 := by
  norm_num [positiveCusp10, positiveCusp10Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp10_Bqq_values :
    positiveCusp10.toNetwork.hessianApply positiveCusp10Rates unitState
        positiveCusp10RightKernel positiveCusp10RightKernel 0 = ((4704 : ℝ) / 79507) * 1 ∧
    positiveCusp10.toNetwork.hessianApply positiveCusp10Rates unitState
        positiveCusp10RightKernel positiveCusp10RightKernel 1 = ((3136 : ℝ) / 79507) * 1 := by
  rcases positiveCusp10Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp10, positiveCusp10Rates, positiveCusp10RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp10_Bqh_values :
    positiveCusp10.toNetwork.hessianApply positiveCusp10Rates unitState
        positiveCusp10RightKernel positiveCusp10Center 0 = ((-460992 : ℝ) / 105982831) * 1 ∧
    positiveCusp10.toNetwork.hessianApply positiveCusp10Rates unitState
        positiveCusp10RightKernel positiveCusp10Center 1 = ((-987840 : ℝ) / 105982831) * 1 := by
  rcases positiveCusp10Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp10, positiveCusp10Rates, positiveCusp10RightKernel,
    positiveCusp10Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp10_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp10.toNetwork positiveCusp10Rates
      positiveCusp10RightKernel positiveCusp10LeftKernel positiveCusp10Center 1 4).unfoldingMatrix =
      ((-12255 : ℝ) / 961) * 1 := by
  rcases positiveCusp10Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp10, positiveCusp10Rates, positiveCusp10RightKernel, positiveCusp10LeftKernel,
      positiveCusp10Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp10_cubic_value :
    dot positiveCusp10LeftKernel (positiveCusp10.toNetwork.hessianApply positiveCusp10Rates unitState
      positiveCusp10RightKernel positiveCusp10Center) = ((-32928 : ℝ) / 2464717) * 1 := by
  rcases positiveCusp10Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp10_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp10LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp10_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp10.toNetwork := by
  rcases positiveCusp10Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl : (-1 : ℝ) < positiveCusp10Root := by norm_num [positiveCusp10Root]
  have hu : positiveCusp10Root < (1 : ℝ) := by norm_num [positiveCusp10Root]
  have hs : 0 ≤ positiveCusp10Root ^ 2 := sq_nonneg positiveCusp10Root
  rcases positiveCusp10_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp10_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp10_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp10.toNetwork positiveCusp10Rates
    positiveCusp10RightKernel positiveCusp10LeftKernel positiveCusp10Center 1 4
  · exact positiveCusp10Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp10, positiveCusp10Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp10RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp10LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp10LeftKernel, positiveCusp10RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp10LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp10Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp10LeftKernel, positiveCusp10Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp10_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp10_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
