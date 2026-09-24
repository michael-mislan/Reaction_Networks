import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp4Polynomial (t : ℝ) : ℝ := (3345 : ℝ) * t ^ 3 + (573 : ℝ) * t ^ 2 + (51 : ℝ) * t + (-1 : ℝ) * 1

private theorem positiveCusp4Root_exists :
    ∃ t : ℝ, ((182 : ℝ) / 11147) < t ∧ t < ((271 : ℝ) / 16598) ∧ positiveCusp4Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp4Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp4Polynomial]
    fun_prop
  have hab : ((182 : ℝ) / 11147) ≤ ((271 : ℝ) / 16598) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((182 : ℝ) / 11147)) (f ((271 : ℝ) / 16598)) := by
    constructor <;> norm_num [f, positiveCusp4Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((182 : ℝ) / 11147) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp4Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((271 : ℝ) / 16598) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp4Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp4Root : ℝ := Classical.choose positiveCusp4Root_exists

theorem positiveCusp4Root_lower : ((182 : ℝ) / 11147) < positiveCusp4Root :=
  (Classical.choose_spec positiveCusp4Root_exists).1

theorem positiveCusp4Root_upper : positiveCusp4Root < ((271 : ℝ) / 16598) :=
  (Classical.choose_spec positiveCusp4Root_exists).2.1

theorem positiveCusp4Root_equation : (3345 : ℝ) * positiveCusp4Root ^ 3 + (573 : ℝ) * positiveCusp4Root ^ 2 + (51 : ℝ) * positiveCusp4Root + (-1 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp4Root_exists).2.2


theorem positiveCusp4Root_power_relations :
    let t := positiveCusp4Root
    ((3345 : ℝ) * t ^ 3 + (573 : ℝ) * t ^ 2 + (51 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((3345 : ℝ) * t ^ 3 + (573 : ℝ) * t ^ 2 + (51 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((3345 : ℝ) * t ^ 3 + (573 : ℝ) * t ^ 2 + (51 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((3345 : ℝ) * t ^ 3 + (573 : ℝ) * t ^ 2 + (51 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((3345 : ℝ) * t ^ 3 + (573 : ℝ) * t ^ 2 + (51 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((3345 : ℝ) * t ^ 3 + (573 : ℝ) * t ^ 2 + (51 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((3345 : ℝ) * t ^ 3 + (573 : ℝ) * t ^ 2 + (51 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((3345 : ℝ) * t ^ 3 + (573 : ℝ) * t ^ 2 + (51 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((3345 : ℝ) * t ^ 3 + (573 : ℝ) * t ^ 2 + (51 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp4Root_equation

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

def positiveCusp4 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .xy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp4Rates : Fin 5 → ℝ :=
  let t := positiveCusp4Root
  ![((-10035 : ℝ) / 284) * t ^ 2 + ((-419 : ℝ) / 142) * t + ((49 : ℝ) / 284) * 1,
    ((-3345 : ℝ) / 284) * t ^ 2 + ((-471 : ℝ) / 142) * t + ((111 : ℝ) / 284) * 1,
    ((3345 : ℝ) / 142) * t ^ 2 + ((116 : ℝ) / 71) * t + ((31 : ℝ) / 142) * 1,
    ((3345 : ℝ) / 142) * t ^ 2 + ((258 : ℝ) / 71) * t + ((31 : ℝ) / 142) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp4RightKernel : Species → ℝ :=
  let t := positiveCusp4Root
  ![((3345 : ℝ) / 71) * t ^ 2 + ((232 : ℝ) / 71) * t + ((31 : ℝ) / 71) * 1,
    ((10035 : ℝ) / 284) * t ^ 2 + ((561 : ℝ) / 142) * t + ((235 : ℝ) / 284) * 1]

noncomputable def positiveCusp4LeftKernel : Species → ℝ :=
  let t := positiveCusp4Root
  ![((1160715 : ℝ) / 9088) * t ^ 2 + ((-42747 : ℝ) / 4544) * t + ((5787 : ℝ) / 9088) * 1,
    ((-3214545 : ℝ) / 9088) * t ^ 2 + ((-89679 : ℝ) / 4544) * t + ((11247 : ℝ) / 9088) * 1]

noncomputable def positiveCusp4Center : Species → ℝ :=
  let t := positiveCusp4Root
  ![((1194 : ℝ) / 71) * t ^ 2 + ((-164 : ℝ) / 71) * t + ((-6 : ℝ) / 71) * 1,
    ((-456 : ℝ) / 71) * t ^ 2 + ((-160 : ℝ) / 71) * t + ((8 : ℝ) / 71) * 1]

theorem positiveCusp4Rates_positive : PositiveVector positiveCusp4Rates := by
  have hl := positiveCusp4Root_lower
  have hu := positiveCusp4Root_upper
  have hs : 0 ≤ positiveCusp4Root ^ 2 := sq_nonneg positiveCusp4Root
  intro k
  fin_cases k <;> simp [positiveCusp4Rates] <;> nlinarith

theorem positiveCusp4_jacobian_values :
    positiveCusp4.toNetwork.jacobian positiveCusp4Rates unitState 0 0 = ((-10035 : ℝ) / 284) * positiveCusp4Root ^ 2 + ((-561 : ℝ) / 142) * positiveCusp4Root + ((-235 : ℝ) / 284) * 1 ∧
    positiveCusp4.toNetwork.jacobian positiveCusp4Rates unitState 0 1 = ((3345 : ℝ) / 71) * positiveCusp4Root ^ 2 + ((232 : ℝ) / 71) * positiveCusp4Root + ((31 : ℝ) / 71) * 1 ∧
    positiveCusp4.toNetwork.jacobian positiveCusp4Rates unitState 1 0 = ((3345 : ℝ) / 71) * positiveCusp4Root ^ 2 + ((516 : ℝ) / 71) * positiveCusp4Root + ((31 : ℝ) / 71) * 1 ∧
    positiveCusp4.toNetwork.jacobian positiveCusp4Rates unitState 1 1 = ((-3345 : ℝ) / 142) * positiveCusp4Root ^ 2 + ((-400 : ℝ) / 71) * positiveCusp4Root + ((-31 : ℝ) / 142) * 1 := by
  norm_num [positiveCusp4, positiveCusp4Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp4_Bqq_values :
    positiveCusp4.toNetwork.hessianApply positiveCusp4Rates unitState
        positiveCusp4RightKernel positiveCusp4RightKernel 0 = ((9808 : ℝ) / 79165) * positiveCusp4Root ^ 2 + ((-57504 : ℝ) / 79165) * positiveCusp4Root + ((-10416 : ℝ) / 79165) * 1 ∧
    positiveCusp4.toNetwork.hessianApply positiveCusp4Rates unitState
        positiveCusp4RightKernel positiveCusp4RightKernel 1 = ((496088 : ℝ) / 79165) * positiveCusp4Root ^ 2 + ((46256 : ℝ) / 79165) * positiveCusp4Root + ((6264 : ℝ) / 79165) * 1 := by
  rcases positiveCusp4Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp4, positiveCusp4Rates, positiveCusp4RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp4_Bqh_values :
    positiveCusp4.toNetwork.hessianApply positiveCusp4Rates unitState
        positiveCusp4RightKernel positiveCusp4Center 0 = ((726030272 : ℝ) / 88268975) * positiveCusp4Root ^ 2 + ((68182144 : ℝ) / 88268975) * positiveCusp4Root + ((1658816 : ℝ) / 88268975) * 1 ∧
    positiveCusp4.toNetwork.hessianApply positiveCusp4Rates unitState
        positiveCusp4RightKernel positiveCusp4Center 1 = ((-281557344 : ℝ) / 88268975) * positiveCusp4Root ^ 2 + ((-69620288 : ℝ) / 88268975) * positiveCusp4Root + ((-2139232 : ℝ) / 88268975) * 1 := by
  rcases positiveCusp4Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp4, positiveCusp4Rates, positiveCusp4RightKernel,
    positiveCusp4Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp4_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp4.toNetwork positiveCusp4Rates
      positiveCusp4RightKernel positiveCusp4LeftKernel positiveCusp4Center 0 4).unfoldingMatrix =
      ((-411435 : ℝ) / 2272) * positiveCusp4Root ^ 2 + ((287553 : ℝ) / 1136) * positiveCusp4Root + ((-12759 : ℝ) / 2272) * 1 := by
  rcases positiveCusp4Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp4, positiveCusp4Rates, positiveCusp4RightKernel, positiveCusp4LeftKernel,
      positiveCusp4Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp4_cubic_value :
    dot positiveCusp4LeftKernel (positiveCusp4.toNetwork.hessianApply positiveCusp4Rates unitState
      positiveCusp4RightKernel positiveCusp4Center) = ((-866208 : ℝ) / 79165) * positiveCusp4Root ^ 2 + ((49184 : ℝ) / 79165) * positiveCusp4Root + ((-1664 : ℝ) / 79165) * 1 := by
  rcases positiveCusp4Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp4_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp4LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp4_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp4.toNetwork := by
  rcases positiveCusp4Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp4Root_lower
  have hu := positiveCusp4Root_upper
  have hs : 0 ≤ positiveCusp4Root ^ 2 := sq_nonneg positiveCusp4Root
  rcases positiveCusp4_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp4_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp4_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp4.toNetwork positiveCusp4Rates
    positiveCusp4RightKernel positiveCusp4LeftKernel positiveCusp4Center 0 4
  · exact positiveCusp4Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp4, positiveCusp4Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp4RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp4LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp4LeftKernel, positiveCusp4RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp4LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp4Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp4LeftKernel, positiveCusp4Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp4_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp4_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
