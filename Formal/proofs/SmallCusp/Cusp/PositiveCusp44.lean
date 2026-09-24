import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

def positiveCusp44Root : ℝ := 0

theorem positiveCusp44Root_equation : (1 : ℝ) * positiveCusp44Root = 0 := by
  norm_num [positiveCusp44Root]


theorem positiveCusp44Root_power_relations :
    let t := positiveCusp44Root
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
  have h := positiveCusp44Root_equation

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

def positiveCusp44 : CodedBimolNetwork where
  reaction := ![(.x, .y), (.y, .xx), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp44Rates : Fin 5 → ℝ :=
  let t := positiveCusp44Root
  ![((14 : ℝ) / 111) * 1,
    ((14 : ℝ) / 37) * 1,
    ((6 : ℝ) / 37) * 1,
    ((34 : ℝ) / 111) * 1,
    ((1 : ℝ) / 37) * 1]

noncomputable def positiveCusp44RightKernel : Species → ℝ :=
  let t := positiveCusp44Root
  ![((50 : ℝ) / 111) * 1,
    ((40 : ℝ) / 37) * 1]

noncomputable def positiveCusp44LeftKernel : Species → ℝ :=
  let t := positiveCusp44Root
  ![((111 : ℝ) / 350) * 1,
    ((111 : ℝ) / 140) * 1]

noncomputable def positiveCusp44Center : Species → ℝ :=
  let t := positiveCusp44Root
  ![((-1400 : ℝ) / 4107) * 1,
    ((560 : ℝ) / 4107) * 1]

theorem positiveCusp44Rates_positive : PositiveVector positiveCusp44Rates := by
  have hl : (-1 : ℝ) < positiveCusp44Root := by norm_num [positiveCusp44Root]
  have hu : positiveCusp44Root < (1 : ℝ) := by norm_num [positiveCusp44Root]
  have hs : 0 ≤ positiveCusp44Root ^ 2 := sq_nonneg positiveCusp44Root
  intro k
  fin_cases k <;> simp [positiveCusp44Rates] <;> nlinarith

theorem positiveCusp44_jacobian_values :
    positiveCusp44.toNetwork.jacobian positiveCusp44Rates unitState 0 0 = ((-40 : ℝ) / 37) * 1 ∧
    positiveCusp44.toNetwork.jacobian positiveCusp44Rates unitState 0 1 = ((50 : ℝ) / 111) * 1 ∧
    positiveCusp44.toNetwork.jacobian positiveCusp44Rates unitState 1 0 = ((16 : ℝ) / 37) * 1 ∧
    positiveCusp44.toNetwork.jacobian positiveCusp44Rates unitState 1 1 = ((-20 : ℝ) / 111) * 1 := by
  norm_num [positiveCusp44, positiveCusp44Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp44_Bqq_values :
    positiveCusp44.toNetwork.hessianApply positiveCusp44Rates unitState
        positiveCusp44RightKernel positiveCusp44RightKernel 0 = ((-196000 : ℝ) / 455877) * 1 ∧
    positiveCusp44.toNetwork.hessianApply positiveCusp44Rates unitState
        positiveCusp44RightKernel positiveCusp44RightKernel 1 = ((78400 : ℝ) / 455877) * 1 := by
  rcases positiveCusp44Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp44, positiveCusp44Rates, positiveCusp44RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp44_Bqh_values :
    positiveCusp44.toNetwork.hessianApply positiveCusp44Rates unitState
        positiveCusp44RightKernel positiveCusp44Center 0 = ((9800000 : ℝ) / 50602347) * 1 ∧
    positiveCusp44.toNetwork.hessianApply positiveCusp44Rates unitState
        positiveCusp44RightKernel positiveCusp44Center 1 = ((-5566400 : ℝ) / 50602347) * 1 := by
  rcases positiveCusp44Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp44, positiveCusp44Rates, positiveCusp44RightKernel,
    positiveCusp44Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp44_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp44.toNetwork positiveCusp44Rates
      positiveCusp44RightKernel positiveCusp44LeftKernel positiveCusp44Center 0 4).unfoldingMatrix =
      ((-6327 : ℝ) / 4900) * 1 := by
  rcases positiveCusp44Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp44, positiveCusp44Rates, positiveCusp44RightKernel, positiveCusp44LeftKernel,
      positiveCusp44Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp44_cubic_value :
    dot positiveCusp44LeftKernel (positiveCusp44.toNetwork.hessianApply positiveCusp44Rates unitState
      positiveCusp44RightKernel positiveCusp44Center) = ((-3920 : ℝ) / 151959) * 1 := by
  rcases positiveCusp44Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp44_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp44LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp44_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp44.toNetwork := by
  rcases positiveCusp44Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl : (-1 : ℝ) < positiveCusp44Root := by norm_num [positiveCusp44Root]
  have hu : positiveCusp44Root < (1 : ℝ) := by norm_num [positiveCusp44Root]
  have hs : 0 ≤ positiveCusp44Root ^ 2 := sq_nonneg positiveCusp44Root
  rcases positiveCusp44_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp44_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp44_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp44.toNetwork positiveCusp44Rates
    positiveCusp44RightKernel positiveCusp44LeftKernel positiveCusp44Center 0 4
  · exact positiveCusp44Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp44, positiveCusp44Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp44RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp44LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp44LeftKernel, positiveCusp44RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp44LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp44Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp44LeftKernel, positiveCusp44Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp44_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp44_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
