import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp23Polynomial (t : ℝ) : ℝ := (79 : ℝ) * t ^ 2 + (-44 : ℝ) * t + (1 : ℝ) * 1

private theorem positiveCusp23Root_exists :
    ∃ t : ℝ, ((329 : ℝ) / 13859) < t ∧ t < ((321 : ℝ) / 13522) ∧ positiveCusp23Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ -(positiveCusp23Polynomial t)
  have hf : Continuous f := by
    dsimp [f, positiveCusp23Polynomial]
    fun_prop
  have hab : ((329 : ℝ) / 13859) ≤ ((321 : ℝ) / 13522) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((329 : ℝ) / 13859)) (f ((321 : ℝ) / 13522)) := by
    constructor <;> norm_num [f, positiveCusp23Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((329 : ℝ) / 13859) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp23Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((321 : ℝ) / 13522) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp23Polynomial] at hft
  · dsimp [f, positiveCusp23Polynomial] at hft ⊢
    nlinarith [hft]

noncomputable def positiveCusp23Root : ℝ := Classical.choose positiveCusp23Root_exists

theorem positiveCusp23Root_lower : ((329 : ℝ) / 13859) < positiveCusp23Root :=
  (Classical.choose_spec positiveCusp23Root_exists).1

theorem positiveCusp23Root_upper : positiveCusp23Root < ((321 : ℝ) / 13522) :=
  (Classical.choose_spec positiveCusp23Root_exists).2.1

theorem positiveCusp23Root_equation : (79 : ℝ) * positiveCusp23Root ^ 2 + (-44 : ℝ) * positiveCusp23Root + (1 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp23Root_exists).2.2


theorem positiveCusp23Root_power_relations :
    let t := positiveCusp23Root
    ((79 : ℝ) * t ^ 2 + (-44 : ℝ) * t + (1 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((79 : ℝ) * t ^ 2 + (-44 : ℝ) * t + (1 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((79 : ℝ) * t ^ 2 + (-44 : ℝ) * t + (1 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((79 : ℝ) * t ^ 2 + (-44 : ℝ) * t + (1 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((79 : ℝ) * t ^ 2 + (-44 : ℝ) * t + (1 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((79 : ℝ) * t ^ 2 + (-44 : ℝ) * t + (1 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((79 : ℝ) * t ^ 2 + (-44 : ℝ) * t + (1 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((79 : ℝ) * t ^ 2 + (-44 : ℝ) * t + (1 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((79 : ℝ) * t ^ 2 + (-44 : ℝ) * t + (1 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp23Root_equation

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

def positiveCusp23 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp23Rates : Fin 5 → ℝ :=
  let t := positiveCusp23Root
  ![((-1 : ℝ) / 3) * t + ((1 : ℝ) / 3) * 1,
    (2 : ℝ) * t,
    ((-7 : ℝ) / 3) * t + ((1 : ℝ) / 3) * 1,
    ((-1 : ℝ) / 3) * t + ((1 : ℝ) / 3) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp23RightKernel : Species → ℝ :=
  let t := positiveCusp23Root
  ![((13 : ℝ) / 3) * t + ((-1 : ℝ) / 3) * 1,
    ((5 : ℝ) / 3) * t + ((1 : ℝ) / 3) * 1]

noncomputable def positiveCusp23LeftKernel : Species → ℝ :=
  let t := positiveCusp23Root
  ![((553 : ℝ) / 180) * t + ((-229 : ℝ) / 180) * 1,
    ((-1817 : ℝ) / 540) * t + ((1091 : ℝ) / 540) * 1]

noncomputable def positiveCusp23Center : Species → ℝ :=
  let t := positiveCusp23Root
  ![((968 : ℝ) / 1185) * t + ((136 : ℝ) / 1185) * 1,
    ((-2264 : ℝ) / 1185) * t + ((152 : ℝ) / 1185) * 1]

theorem positiveCusp23Rates_positive : PositiveVector positiveCusp23Rates := by
  have hl := positiveCusp23Root_lower
  have hu := positiveCusp23Root_upper
  have hs : 0 ≤ positiveCusp23Root ^ 2 := sq_nonneg positiveCusp23Root
  intro k
  fin_cases k <;> simp [positiveCusp23Rates] <;> nlinarith

theorem positiveCusp23_jacobian_values :
    positiveCusp23.toNetwork.jacobian positiveCusp23Rates unitState 0 0 = ((-5 : ℝ) / 3) * positiveCusp23Root + ((-1 : ℝ) / 3) * 1 ∧
    positiveCusp23.toNetwork.jacobian positiveCusp23Rates unitState 0 1 = ((13 : ℝ) / 3) * positiveCusp23Root + ((-1 : ℝ) / 3) * 1 ∧
    positiveCusp23.toNetwork.jacobian positiveCusp23Rates unitState 1 0 = ((13 : ℝ) / 3) * positiveCusp23Root + ((-1 : ℝ) / 3) * 1 ∧
    positiveCusp23.toNetwork.jacobian positiveCusp23Rates unitState 1 1 = (-6 : ℝ) * positiveCusp23Root := by
  norm_num [positiveCusp23, positiveCusp23Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp23_Bqq_values :
    positiveCusp23.toNetwork.hessianApply positiveCusp23Rates unitState
        positiveCusp23RightKernel positiveCusp23RightKernel 0 = ((28960 : ℝ) / 6241) * positiveCusp23Root + ((-256 : ℝ) / 6241) * 1 ∧
    positiveCusp23.toNetwork.hessianApply positiveCusp23Rates unitState
        positiveCusp23RightKernel positiveCusp23RightKernel 1 = ((-48752 : ℝ) / 6241) * positiveCusp23Root + ((1424 : ℝ) / 6241) * 1 := by
  rcases positiveCusp23Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp23, positiveCusp23Rates, positiveCusp23RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp23_Bqh_values :
    positiveCusp23.toNetwork.hessianApply positiveCusp23Rates unitState
        positiveCusp23RightKernel positiveCusp23Center 0 = ((-10376736 : ℝ) / 2465195) * positiveCusp23Root + ((228768 : ℝ) / 2465195) * 1 ∧
    positiveCusp23.toNetwork.hessianApply positiveCusp23Rates unitState
        positiveCusp23RightKernel positiveCusp23Center 1 = ((12112608 : ℝ) / 2465195) * positiveCusp23Root + ((-319584 : ℝ) / 2465195) * 1 := by
  rcases positiveCusp23Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp23, positiveCusp23Rates, positiveCusp23RightKernel,
    positiveCusp23Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp23_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp23.toNetwork positiveCusp23Rates
      positiveCusp23RightKernel positiveCusp23LeftKernel positiveCusp23Center 1 4).unfoldingMatrix =
      ((16511 : ℝ) / 270) * positiveCusp23Root + ((-8801 : ℝ) / 270) * 1 := by
  rcases positiveCusp23Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp23, positiveCusp23Rates, positiveCusp23RightKernel, positiveCusp23LeftKernel,
      positiveCusp23Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp23_cubic_value :
    dot positiveCusp23LeftKernel (positiveCusp23.toNetwork.hessianApply positiveCusp23Rates unitState
      positiveCusp23RightKernel positiveCusp23Center) = ((-38128 : ℝ) / 93615) * positiveCusp23Root + ((-656 : ℝ) / 93615) * 1 := by
  rcases positiveCusp23Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp23_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp23LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp23_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp23.toNetwork := by
  rcases positiveCusp23Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp23Root_lower
  have hu := positiveCusp23Root_upper
  have hs : 0 ≤ positiveCusp23Root ^ 2 := sq_nonneg positiveCusp23Root
  rcases positiveCusp23_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp23_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp23_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp23.toNetwork positiveCusp23Rates
    positiveCusp23RightKernel positiveCusp23LeftKernel positiveCusp23Center 1 4
  · exact positiveCusp23Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp23, positiveCusp23Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp23RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp23LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp23LeftKernel, positiveCusp23RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp23LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp23Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp23LeftKernel, positiveCusp23Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp23_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp23_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
