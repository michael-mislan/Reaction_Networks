import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp3Polynomial (t : ℝ) : ℝ := (544 : ℝ) * t ^ 3 + (240 : ℝ) * t ^ 2 + (30 : ℝ) * t + (-1 : ℝ) * 1

private theorem positiveCusp3Root_exists :
    ∃ t : ℝ, ((433 : ℝ) / 15979) < t ∧ t < ((567 : ℝ) / 20924) ∧ positiveCusp3Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp3Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp3Polynomial]
    fun_prop
  have hab : ((433 : ℝ) / 15979) ≤ ((567 : ℝ) / 20924) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((433 : ℝ) / 15979)) (f ((567 : ℝ) / 20924)) := by
    constructor <;> norm_num [f, positiveCusp3Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((433 : ℝ) / 15979) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp3Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((567 : ℝ) / 20924) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp3Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp3Root : ℝ := Classical.choose positiveCusp3Root_exists

theorem positiveCusp3Root_lower : ((433 : ℝ) / 15979) < positiveCusp3Root :=
  (Classical.choose_spec positiveCusp3Root_exists).1

theorem positiveCusp3Root_upper : positiveCusp3Root < ((567 : ℝ) / 20924) :=
  (Classical.choose_spec positiveCusp3Root_exists).2.1

theorem positiveCusp3Root_equation : (544 : ℝ) * positiveCusp3Root ^ 3 + (240 : ℝ) * positiveCusp3Root ^ 2 + (30 : ℝ) * positiveCusp3Root + (-1 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp3Root_exists).2.2


theorem positiveCusp3Root_power_relations :
    let t := positiveCusp3Root
    ((544 : ℝ) * t ^ 3 + (240 : ℝ) * t ^ 2 + (30 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((544 : ℝ) * t ^ 3 + (240 : ℝ) * t ^ 2 + (30 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((544 : ℝ) * t ^ 3 + (240 : ℝ) * t ^ 2 + (30 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((544 : ℝ) * t ^ 3 + (240 : ℝ) * t ^ 2 + (30 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((544 : ℝ) * t ^ 3 + (240 : ℝ) * t ^ 2 + (30 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((544 : ℝ) * t ^ 3 + (240 : ℝ) * t ^ 2 + (30 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((544 : ℝ) * t ^ 3 + (240 : ℝ) * t ^ 2 + (30 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((544 : ℝ) * t ^ 3 + (240 : ℝ) * t ^ 2 + (30 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((544 : ℝ) * t ^ 3 + (240 : ℝ) * t ^ 2 + (30 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp3Root_equation

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

def positiveCusp3 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .xy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp3Rates : Fin 5 → ℝ :=
  let t := positiveCusp3Root
  ![((-204 : ℝ) / 11) * t ^ 2 + (-4 : ℝ) * t + ((5 : ℝ) / 22) * 1,
    ((-68 : ℝ) / 11) * t ^ 2 + (-3 : ℝ) * t + ((9 : ℝ) / 22) * 1,
    ((136 : ℝ) / 11) * t ^ 2 + (2 : ℝ) * t + ((2 : ℝ) / 11) * 1,
    ((136 : ℝ) / 11) * t ^ 2 + (4 : ℝ) * t + ((2 : ℝ) / 11) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp3RightKernel : Species → ℝ :=
  let t := positiveCusp3Root
  ![((272 : ℝ) / 11) * t ^ 2 + (6 : ℝ) * t + ((4 : ℝ) / 11) * 1,
    ((204 : ℝ) / 11) * t ^ 2 + (5 : ℝ) * t + ((17 : ℝ) / 22) * 1]

noncomputable def positiveCusp3LeftKernel : Species → ℝ :=
  let t := positiveCusp3Root
  ![((-66096 : ℝ) / 1265) * t ^ 2 + ((-1464 : ℝ) / 115) * t + ((1129 : ℝ) / 1265) * 1,
    ((-4352 : ℝ) / 253) * t ^ 2 + ((116 : ℝ) / 23) * t + ((167 : ℝ) / 253) * 1]

noncomputable def positiveCusp3Center : Species → ℝ :=
  let t := positiveCusp3Root
  ![((142 : ℝ) / 253) * t ^ 2 + ((-43 : ℝ) / 46) * t + ((-79 : ℝ) / 1012) * 1,
    ((-1552 : ℝ) / 253) * t ^ 2 + ((-30 : ℝ) / 23) * t + ((27 : ℝ) / 253) * 1]

theorem positiveCusp3Rates_positive : PositiveVector positiveCusp3Rates := by
  have hl := positiveCusp3Root_lower
  have hu := positiveCusp3Root_upper
  have hs : 0 ≤ positiveCusp3Root ^ 2 := sq_nonneg positiveCusp3Root
  intro k
  fin_cases k <;> simp [positiveCusp3Rates] <;> nlinarith

theorem positiveCusp3_jacobian_values :
    positiveCusp3.toNetwork.jacobian positiveCusp3Rates unitState 0 0 = ((-204 : ℝ) / 11) * positiveCusp3Root ^ 2 + (-5 : ℝ) * positiveCusp3Root + ((-17 : ℝ) / 22) * 1 ∧
    positiveCusp3.toNetwork.jacobian positiveCusp3Rates unitState 0 1 = ((272 : ℝ) / 11) * positiveCusp3Root ^ 2 + (6 : ℝ) * positiveCusp3Root + ((4 : ℝ) / 11) * 1 ∧
    positiveCusp3.toNetwork.jacobian positiveCusp3Rates unitState 1 0 = ((272 : ℝ) / 11) * positiveCusp3Root ^ 2 + (8 : ℝ) * positiveCusp3Root + ((4 : ℝ) / 11) * 1 ∧
    positiveCusp3.toNetwork.jacobian positiveCusp3Rates unitState 1 1 = ((-136 : ℝ) / 11) * positiveCusp3Root ^ 2 + (-6 : ℝ) * positiveCusp3Root + ((-2 : ℝ) / 11) * 1 := by
  norm_num [positiveCusp3, positiveCusp3Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp3_Bqq_values :
    positiveCusp3.toNetwork.hessianApply positiveCusp3Rates unitState
        positiveCusp3RightKernel positiveCusp3RightKernel 0 = ((53 : ℝ) / 187) * positiveCusp3Root ^ 2 + ((-3 : ℝ) / 68) * positiveCusp3Root + ((-195 : ℝ) / 1496) * 1 ∧
    positiveCusp3.toNetwork.hessianApply positiveCusp3Rates unitState
        positiveCusp3RightKernel positiveCusp3RightKernel 1 = ((786 : ℝ) / 187) * positiveCusp3Root ^ 2 + ((31 : ℝ) / 34) * positiveCusp3Root + ((43 : ℝ) / 748) * 1 := by
  rcases positiveCusp3Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp3, positiveCusp3Rates, positiveCusp3RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp3_Bqh_values :
    positiveCusp3.toNetwork.hessianApply positiveCusp3Rates unitState
        positiveCusp3RightKernel positiveCusp3Center 0 = ((204498 : ℝ) / 73117) * positiveCusp3Root ^ 2 + ((10923 : ℝ) / 13294) * positiveCusp3Root + ((3679 : ℝ) / 292468) * 1 ∧
    positiveCusp3.toNetwork.hessianApply positiveCusp3Rates unitState
        positiveCusp3RightKernel positiveCusp3Center 1 = ((-203397 : ℝ) / 73117) * positiveCusp3Root ^ 2 + ((-28555 : ℝ) / 26588) * positiveCusp3Root + ((-5319 : ℝ) / 584936) * 1 := by
  rcases positiveCusp3Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp3, positiveCusp3Rates, positiveCusp3RightKernel,
    positiveCusp3Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp3_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp3.toNetwork positiveCusp3Rates
      positiveCusp3RightKernel positiveCusp3LeftKernel positiveCusp3Center 0 4).unfoldingMatrix =
      ((948736 : ℝ) / 29095) * positiveCusp3Root ^ 2 + ((-90976 : ℝ) / 2645) * positiveCusp3Root + ((-2504 : ℝ) / 29095) * 1 := by
  rcases positiveCusp3Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp3, positiveCusp3Rates, positiveCusp3RightKernel, positiveCusp3LeftKernel,
      positiveCusp3Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp3_cubic_value :
    dot positiveCusp3LeftKernel (positiveCusp3.toNetwork.hessianApply positiveCusp3Rates unitState
      positiveCusp3RightKernel positiveCusp3Center) = ((14024 : ℝ) / 4301) * positiveCusp3Root ^ 2 + ((521 : ℝ) / 391) * positiveCusp3Root + ((-441 : ℝ) / 8602) * 1 := by
  rcases positiveCusp3Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp3_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp3LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp3_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp3.toNetwork := by
  rcases positiveCusp3Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp3Root_lower
  have hu := positiveCusp3Root_upper
  have hs : 0 ≤ positiveCusp3Root ^ 2 := sq_nonneg positiveCusp3Root
  rcases positiveCusp3_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp3_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp3_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp3.toNetwork positiveCusp3Rates
    positiveCusp3RightKernel positiveCusp3LeftKernel positiveCusp3Center 0 4
  · exact positiveCusp3Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp3, positiveCusp3Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp3RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp3LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp3LeftKernel, positiveCusp3RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp3LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp3Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp3LeftKernel, positiveCusp3Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp3_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp3_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
