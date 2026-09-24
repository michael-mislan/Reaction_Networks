import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp16Polynomial (t : ℝ) : ℝ := (10217 : ℝ) * t ^ 2 + (-790 : ℝ) * t + (-175 : ℝ) * 1

private theorem positiveCusp16Root_exists :
    ∃ t : ℝ, ((1894 : ℝ) / 10815) < t ∧ t < ((1825 : ℝ) / 10421) ∧ positiveCusp16Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp16Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp16Polynomial]
    fun_prop
  have hab : ((1894 : ℝ) / 10815) ≤ ((1825 : ℝ) / 10421) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((1894 : ℝ) / 10815)) (f ((1825 : ℝ) / 10421)) := by
    constructor <;> norm_num [f, positiveCusp16Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((1894 : ℝ) / 10815) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp16Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((1825 : ℝ) / 10421) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp16Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp16Root : ℝ := Classical.choose positiveCusp16Root_exists

theorem positiveCusp16Root_lower : ((1894 : ℝ) / 10815) < positiveCusp16Root :=
  (Classical.choose_spec positiveCusp16Root_exists).1

theorem positiveCusp16Root_upper : positiveCusp16Root < ((1825 : ℝ) / 10421) :=
  (Classical.choose_spec positiveCusp16Root_exists).2.1

theorem positiveCusp16Root_equation : (10217 : ℝ) * positiveCusp16Root ^ 2 + (-790 : ℝ) * positiveCusp16Root + (-175 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp16Root_exists).2.2


theorem positiveCusp16Root_power_relations :
    let t := positiveCusp16Root
    ((10217 : ℝ) * t ^ 2 + (-790 : ℝ) * t + (-175 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((10217 : ℝ) * t ^ 2 + (-790 : ℝ) * t + (-175 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((10217 : ℝ) * t ^ 2 + (-790 : ℝ) * t + (-175 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((10217 : ℝ) * t ^ 2 + (-790 : ℝ) * t + (-175 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((10217 : ℝ) * t ^ 2 + (-790 : ℝ) * t + (-175 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((10217 : ℝ) * t ^ 2 + (-790 : ℝ) * t + (-175 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((10217 : ℝ) * t ^ 2 + (-790 : ℝ) * t + (-175 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((10217 : ℝ) * t ^ 2 + (-790 : ℝ) * t + (-175 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((10217 : ℝ) * t ^ 2 + (-790 : ℝ) * t + (-175 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp16Root_equation

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

def positiveCusp16 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.xx, .y), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp16Rates : Fin 5 → ℝ :=
  let t := positiveCusp16Root
  ![((14 : ℝ) / 9) * t + ((-2 : ℝ) / 9) * 1,
    ((1 : ℝ) / 15) * t + ((1 : ℝ) / 3) * 1,
    ((-17 : ℝ) / 45) * t + ((1 : ℝ) / 9) * 1,
    ((-101 : ℝ) / 45) * t + ((7 : ℝ) / 9) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp16RightKernel : Species → ℝ :=
  let t := positiveCusp16Root
  ![((-101 : ℝ) / 45) * t + ((7 : ℝ) / 9) * 1,
    ((4 : ℝ) / 5) * t]

noncomputable def positiveCusp16LeftKernel : Species → ℝ :=
  let t := positiveCusp16Root
  ![((8776403 : ℝ) / 2081520) * t + ((650987 : ℝ) / 416304) * 1,
    ((-234991 : ℝ) / 59472) * t + ((89689 : ℝ) / 59472) * 1]

noncomputable def positiveCusp16Center : Species → ℝ :=
  let t := positiveCusp16Root
  ![((28284992 : ℝ) / 5425227) * t + ((-4887680 : ℝ) / 5425227) * 1,
    ((-1969200 : ℝ) / 602803) * t + ((324240 : ℝ) / 602803) * 1]

theorem positiveCusp16Rates_positive : PositiveVector positiveCusp16Rates := by
  have hl := positiveCusp16Root_lower
  have hu := positiveCusp16Root_upper
  have hs : 0 ≤ positiveCusp16Root ^ 2 := sq_nonneg positiveCusp16Root
  intro k
  fin_cases k <;> simp [positiveCusp16Rates] <;> nlinarith

theorem positiveCusp16_jacobian_values :
    positiveCusp16.toNetwork.jacobian positiveCusp16Rates unitState 0 0 = ((-4 : ℝ) / 5) * positiveCusp16Root ∧
    positiveCusp16.toNetwork.jacobian positiveCusp16Rates unitState 0 1 = ((-101 : ℝ) / 45) * positiveCusp16Root + ((7 : ℝ) / 9) * 1 ∧
    positiveCusp16.toNetwork.jacobian positiveCusp16Rates unitState 1 0 = ((73 : ℝ) / 45) * positiveCusp16Root + ((1 : ℝ) / 9) * 1 ∧
    positiveCusp16.toNetwork.jacobian positiveCusp16Rates unitState 1 1 = ((-79 : ℝ) / 45) * positiveCusp16Root + ((-7 : ℝ) / 9) * 1 := by
  norm_num [positiveCusp16, positiveCusp16Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp16_Bqq_values :
    positiveCusp16.toNetwork.hessianApply positiveCusp16Rates unitState
        positiveCusp16RightKernel positiveCusp16RightKernel 0 = ((2614485568 : ℝ) / 939483801) * positiveCusp16Root + ((-443907520 : ℝ) / 939483801) * 1 ∧
    positiveCusp16.toNetwork.hessianApply positiveCusp16Rates unitState
        positiveCusp16RightKernel positiveCusp16RightKernel 1 = ((-567356480 : ℝ) / 313161267) * positiveCusp16Root + ((86233280 : ℝ) / 313161267) * 1 := by
  rcases positiveCusp16Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp16, positiveCusp16Rates, positiveCusp16RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp16_Bqh_values :
    positiveCusp16.toNetwork.hessianApply positiveCusp16Rates unitState
        positiveCusp16RightKernel positiveCusp16Center 0 = ((-3737813429762048 : ℝ) / 566323653694203) * positiveCusp16Root + ((651620441185280 : ℝ) / 566323653694203) * 1 ∧
    positiveCusp16.toNetwork.hessianApply positiveCusp16Rates unitState
        positiveCusp16RightKernel positiveCusp16Center 1 = ((325982662244864 : ℝ) / 62924850410467) * positiveCusp16Root + ((-56573314864640 : ℝ) / 62924850410467) * 1 := by
  rcases positiveCusp16Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp16, positiveCusp16Rates, positiveCusp16RightKernel,
    positiveCusp16Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp16_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp16.toNetwork positiveCusp16Rates
      positiveCusp16RightKernel positiveCusp16LeftKernel positiveCusp16Center 0 2).unfoldingMatrix =
      ((-1298754389 : ℝ) / 61404840) * positiveCusp16Root + ((-36916157 : ℝ) / 12280968) * 1 := by
  rcases positiveCusp16Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp16, positiveCusp16Rates, positiveCusp16RightKernel, positiveCusp16LeftKernel,
      positiveCusp16Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp16_cubic_value :
    dot positiveCusp16LeftKernel (positiveCusp16.toNetwork.hessianApply positiveCusp16Rates unitState
      positiveCusp16RightKernel positiveCusp16Center) = ((39930631616 : ℝ) / 18476514753) * positiveCusp16Root + ((-7092733760 : ℝ) / 18476514753) * 1 := by
  rcases positiveCusp16Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp16_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp16LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp16_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp16.toNetwork := by
  rcases positiveCusp16Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp16Root_lower
  have hu := positiveCusp16Root_upper
  have hs : 0 ≤ positiveCusp16Root ^ 2 := sq_nonneg positiveCusp16Root
  rcases positiveCusp16_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp16_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp16_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp16.toNetwork positiveCusp16Rates
    positiveCusp16RightKernel positiveCusp16LeftKernel positiveCusp16Center 0 2
  · exact positiveCusp16Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp16, positiveCusp16Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp16RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp16LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp16LeftKernel, positiveCusp16RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp16LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp16Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp16LeftKernel, positiveCusp16Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp16_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp16_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
