import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp5Polynomial (t : ℝ) : ℝ := (452 : ℝ) * t ^ 3 + (-282 : ℝ) * t ^ 2 + (42 : ℝ) * t + (-1 : ℝ) * 1

private theorem positiveCusp5Root_exists :
    ∃ t : ℝ, ((330 : ℝ) / 11261) < t ∧ t < ((491 : ℝ) / 16755) ∧ positiveCusp5Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp5Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp5Polynomial]
    fun_prop
  have hab : ((330 : ℝ) / 11261) ≤ ((491 : ℝ) / 16755) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((330 : ℝ) / 11261)) (f ((491 : ℝ) / 16755)) := by
    constructor <;> norm_num [f, positiveCusp5Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((330 : ℝ) / 11261) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp5Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((491 : ℝ) / 16755) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp5Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp5Root : ℝ := Classical.choose positiveCusp5Root_exists

theorem positiveCusp5Root_lower : ((330 : ℝ) / 11261) < positiveCusp5Root :=
  (Classical.choose_spec positiveCusp5Root_exists).1

theorem positiveCusp5Root_upper : positiveCusp5Root < ((491 : ℝ) / 16755) :=
  (Classical.choose_spec positiveCusp5Root_exists).2.1

theorem positiveCusp5Root_equation : (452 : ℝ) * positiveCusp5Root ^ 3 + (-282 : ℝ) * positiveCusp5Root ^ 2 + (42 : ℝ) * positiveCusp5Root + (-1 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp5Root_exists).2.2


theorem positiveCusp5Root_power_relations :
    let t := positiveCusp5Root
    ((452 : ℝ) * t ^ 3 + (-282 : ℝ) * t ^ 2 + (42 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((452 : ℝ) * t ^ 3 + (-282 : ℝ) * t ^ 2 + (42 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((452 : ℝ) * t ^ 3 + (-282 : ℝ) * t ^ 2 + (42 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((452 : ℝ) * t ^ 3 + (-282 : ℝ) * t ^ 2 + (42 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((452 : ℝ) * t ^ 3 + (-282 : ℝ) * t ^ 2 + (42 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((452 : ℝ) * t ^ 3 + (-282 : ℝ) * t ^ 2 + (42 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((452 : ℝ) * t ^ 3 + (-282 : ℝ) * t ^ 2 + (42 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((452 : ℝ) * t ^ 3 + (-282 : ℝ) * t ^ 2 + (42 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((452 : ℝ) * t ^ 3 + (-282 : ℝ) * t ^ 2 + (42 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp5Root_equation

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

def positiveCusp5 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp5Rates : Fin 5 → ℝ :=
  let t := positiveCusp5Root
  ![((452 : ℝ) / 31) * t ^ 2 + ((-239 : ℝ) / 31) * t + ((17 : ℝ) / 31) * 1,
    ((678 : ℝ) / 31) * t ^ 2 + ((-281 : ℝ) / 31) * t + ((10 : ℝ) / 31) * 1,
    ((-904 : ℝ) / 31) * t ^ 2 + ((416 : ℝ) / 31) * t + ((-3 : ℝ) / 31) * 1,
    ((-226 : ℝ) / 31) * t ^ 2 + ((73 : ℝ) / 31) * t + ((7 : ℝ) / 31) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp5RightKernel : Species → ℝ :=
  let t := positiveCusp5Root
  ![((226 : ℝ) / 31) * t ^ 2 + ((-11 : ℝ) / 31) * t + ((-7 : ℝ) / 31) * 1,
    ((452 : ℝ) / 31) * t ^ 2 + ((-208 : ℝ) / 31) * t + ((17 : ℝ) / 31) * 1]

noncomputable def positiveCusp5LeftKernel : Species → ℝ :=
  let t := positiveCusp5Root
  ![((11300 : ℝ) / 33) * t ^ 2 + ((-4790 : ℝ) / 33) * t + ((92 : ℝ) / 33) * 1,
    ((111418 : ℝ) / 1023) * t ^ 2 + ((-52450 : ℝ) / 1023) * t + ((3493 : ℝ) / 1023) * 1]

noncomputable def positiveCusp5Center : Species → ℝ :=
  let t := positiveCusp5Root
  ![((996 : ℝ) / 341) * t ^ 2 + ((-494 : ℝ) / 341) * t + ((52 : ℝ) / 341) * 1,
    ((-652 : ℝ) / 341) * t ^ 2 + ((170 : ℝ) / 341) * t + ((18 : ℝ) / 341) * 1]

theorem positiveCusp5Rates_positive : PositiveVector positiveCusp5Rates := by
  have hl := positiveCusp5Root_lower
  have hu := positiveCusp5Root_upper
  have hs : 0 ≤ positiveCusp5Root ^ 2 := sq_nonneg positiveCusp5Root
  intro k
  fin_cases k <;> simp [positiveCusp5Rates] <;> nlinarith

theorem positiveCusp5_jacobian_values :
    positiveCusp5.toNetwork.jacobian positiveCusp5Rates unitState 0 0 = ((-452 : ℝ) / 31) * positiveCusp5Root ^ 2 + ((208 : ℝ) / 31) * positiveCusp5Root + ((-17 : ℝ) / 31) * 1 ∧
    positiveCusp5.toNetwork.jacobian positiveCusp5Rates unitState 0 1 = ((226 : ℝ) / 31) * positiveCusp5Root ^ 2 + ((-11 : ℝ) / 31) * positiveCusp5Root + ((-7 : ℝ) / 31) * 1 ∧
    positiveCusp5.toNetwork.jacobian positiveCusp5Rates unitState 1 0 = ((904 : ℝ) / 31) * positiveCusp5Root ^ 2 + ((-354 : ℝ) / 31) * positiveCusp5Root + ((3 : ℝ) / 31) * 1 ∧
    positiveCusp5.toNetwork.jacobian positiveCusp5Rates unitState 1 1 = ((-678 : ℝ) / 31) * positiveCusp5Root ^ 2 + ((219 : ℝ) / 31) * positiveCusp5Root + ((-10 : ℝ) / 31) * 1 := by
  norm_num [positiveCusp5, positiveCusp5Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp5_Bqq_values :
    positiveCusp5.toNetwork.hessianApply positiveCusp5Rates unitState
        positiveCusp5RightKernel positiveCusp5RightKernel 0 = ((5464 : ℝ) / 3503) * positiveCusp5Root ^ 2 + ((-2290 : ℝ) / 3503) * positiveCusp5Root + ((259 : ℝ) / 3503) * 1 ∧
    positiveCusp5.toNetwork.hessianApply positiveCusp5Rates unitState
        positiveCusp5RightKernel positiveCusp5RightKernel 1 = ((1780 : ℝ) / 3503) * positiveCusp5Root ^ 2 + ((-1900 : ℝ) / 3503) * positiveCusp5Root + ((169 : ℝ) / 3503) * 1 := by
  rcases positiveCusp5Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp5, positiveCusp5Rates, positiveCusp5RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp5_Bqh_values :
    positiveCusp5.toNetwork.hessianApply positiveCusp5Rates unitState
        positiveCusp5RightKernel positiveCusp5Center 0 = ((-542702 : ℝ) / 4354229) * positiveCusp5Root ^ 2 + ((135431 : ℝ) / 4354229) * positiveCusp5Root + ((-29906 : ℝ) / 4354229) * 1 ∧
    positiveCusp5.toNetwork.hessianApply positiveCusp5Rates unitState
        positiveCusp5RightKernel positiveCusp5Center 1 = ((-916022 : ℝ) / 4354229) * positiveCusp5Root ^ 2 + ((810695 : ℝ) / 4354229) * positiveCusp5Root + ((-67712 : ℝ) / 4354229) * 1 := by
  rcases positiveCusp5Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp5, positiveCusp5Rates, positiveCusp5RightKernel,
    positiveCusp5Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp5_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp5.toNetwork positiveCusp5Rates
      positiveCusp5RightKernel positiveCusp5LeftKernel positiveCusp5Center 1 4).unfoldingMatrix =
      ((-11365540 : ℝ) / 11253) * positiveCusp5Root ^ 2 + ((5466628 : ℝ) / 11253) * positiveCusp5Root + ((-328048 : ℝ) / 11253) * 1 := by
  rcases positiveCusp5Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp5, positiveCusp5Rates, positiveCusp5RightKernel, positiveCusp5LeftKernel,
      positiveCusp5Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp5_cubic_value :
    dot positiveCusp5LeftKernel (positiveCusp5.toNetwork.hessianApply positiveCusp5Rates unitState
      positiveCusp5RightKernel positiveCusp5Center) = ((-49924 : ℝ) / 38533) * positiveCusp5Root ^ 2 + ((23770 : ℝ) / 38533) * positiveCusp5Root + ((-1174 : ℝ) / 38533) * 1 := by
  rcases positiveCusp5Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp5_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp5LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp5_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp5.toNetwork := by
  rcases positiveCusp5Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp5Root_lower
  have hu := positiveCusp5Root_upper
  have hs : 0 ≤ positiveCusp5Root ^ 2 := sq_nonneg positiveCusp5Root
  rcases positiveCusp5_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp5_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp5_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp5.toNetwork positiveCusp5Rates
    positiveCusp5RightKernel positiveCusp5LeftKernel positiveCusp5Center 1 4
  · exact positiveCusp5Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp5, positiveCusp5Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp5RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp5LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp5LeftKernel, positiveCusp5RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp5LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp5Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp5LeftKernel, positiveCusp5Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp5_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp5_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
