import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp1Polynomial (t : ℝ) : ℝ := (62 : ℝ) * t ^ 3 + (42 : ℝ) * t ^ 2 + (12 : ℝ) * t + (-1 : ℝ) * 1

private theorem positiveCusp1Root_exists :
    ∃ t : ℝ, ((453 : ℝ) / 6823) < t ∧ t < ((1084 : ℝ) / 16327) ∧ positiveCusp1Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp1Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp1Polynomial]
    fun_prop
  have hab : ((453 : ℝ) / 6823) ≤ ((1084 : ℝ) / 16327) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((453 : ℝ) / 6823)) (f ((1084 : ℝ) / 16327)) := by
    constructor <;> norm_num [f, positiveCusp1Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((453 : ℝ) / 6823) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp1Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((1084 : ℝ) / 16327) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp1Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp1Root : ℝ := Classical.choose positiveCusp1Root_exists

theorem positiveCusp1Root_lower : ((453 : ℝ) / 6823) < positiveCusp1Root :=
  (Classical.choose_spec positiveCusp1Root_exists).1

theorem positiveCusp1Root_upper : positiveCusp1Root < ((1084 : ℝ) / 16327) :=
  (Classical.choose_spec positiveCusp1Root_exists).2.1

theorem positiveCusp1Root_equation : (62 : ℝ) * positiveCusp1Root ^ 3 + (42 : ℝ) * positiveCusp1Root ^ 2 + (12 : ℝ) * positiveCusp1Root + (-1 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp1Root_exists).2.2


theorem positiveCusp1Root_power_relations :
    let t := positiveCusp1Root
    ((62 : ℝ) * t ^ 3 + (42 : ℝ) * t ^ 2 + (12 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((62 : ℝ) * t ^ 3 + (42 : ℝ) * t ^ 2 + (12 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((62 : ℝ) * t ^ 3 + (42 : ℝ) * t ^ 2 + (12 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((62 : ℝ) * t ^ 3 + (42 : ℝ) * t ^ 2 + (12 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((62 : ℝ) * t ^ 3 + (42 : ℝ) * t ^ 2 + (12 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((62 : ℝ) * t ^ 3 + (42 : ℝ) * t ^ 2 + (12 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((62 : ℝ) * t ^ 3 + (42 : ℝ) * t ^ 2 + (12 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((62 : ℝ) * t ^ 3 + (42 : ℝ) * t ^ 2 + (12 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((62 : ℝ) * t ^ 3 + (42 : ℝ) * t ^ 2 + (12 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp1Root_equation

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

def positiveCusp1 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .x)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp1Rates : Fin 5 → ℝ :=
  let t := positiveCusp1Root
  ![((-186 : ℝ) / 71) * t ^ 2 + ((-94 : ℝ) / 71) * t + ((13 : ℝ) / 71) * 1,
    ((-62 : ℝ) / 71) * t ^ 2 + ((-126 : ℝ) / 71) * t + ((28 : ℝ) / 71) * 1,
    ((124 : ℝ) / 71) * t ^ 2 + ((39 : ℝ) / 71) * t + ((15 : ℝ) / 71) * 1,
    ((124 : ℝ) / 71) * t ^ 2 + ((110 : ℝ) / 71) * t + ((15 : ℝ) / 71) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp1RightKernel : Species → ℝ :=
  let t := positiveCusp1Root
  ![((248 : ℝ) / 71) * t ^ 2 + ((78 : ℝ) / 71) * t + ((30 : ℝ) / 71) * 1,
    ((186 : ℝ) / 71) * t ^ 2 + ((94 : ℝ) / 71) * t + ((58 : ℝ) / 71) * 1]

noncomputable def positiveCusp1LeftKernel : Species → ℝ :=
  let t := positiveCusp1Root
  ![((1023 : ℝ) / 71) * t ^ 2 + ((-51 : ℝ) / 71) * t + ((35 : ℝ) / 71) * 1,
    ((-2294 : ℝ) / 71) * t ^ 2 + ((-686 : ℝ) / 71) * t + ((113 : ℝ) / 71) * 1]

noncomputable def positiveCusp1Center : Species → ℝ :=
  let t := positiveCusp1Root
  ![((360 : ℝ) / 71) * t ^ 2 + ((72 : ℝ) / 71) * t + ((-16 : ℝ) / 71) * 1,
    ((104 : ℝ) / 71) * t ^ 2 + ((-36 : ℝ) / 71) * t + ((8 : ℝ) / 71) * 1]

theorem positiveCusp1Rates_positive : PositiveVector positiveCusp1Rates := by
  have hl := positiveCusp1Root_lower
  have hu := positiveCusp1Root_upper
  have hs : 0 ≤ positiveCusp1Root ^ 2 := sq_nonneg positiveCusp1Root
  intro k
  fin_cases k <;> simp [positiveCusp1Rates] <;> nlinarith

theorem positiveCusp1_jacobian_values :
    positiveCusp1.toNetwork.jacobian positiveCusp1Rates unitState 0 0 = ((-186 : ℝ) / 71) * positiveCusp1Root ^ 2 + ((-94 : ℝ) / 71) * positiveCusp1Root + ((-58 : ℝ) / 71) * 1 ∧
    positiveCusp1.toNetwork.jacobian positiveCusp1Rates unitState 0 1 = ((248 : ℝ) / 71) * positiveCusp1Root ^ 2 + ((78 : ℝ) / 71) * positiveCusp1Root + ((30 : ℝ) / 71) * 1 ∧
    positiveCusp1.toNetwork.jacobian positiveCusp1Rates unitState 1 0 = ((248 : ℝ) / 71) * positiveCusp1Root ^ 2 + ((149 : ℝ) / 71) * positiveCusp1Root + ((30 : ℝ) / 71) * 1 ∧
    positiveCusp1.toNetwork.jacobian positiveCusp1Rates unitState 1 1 = ((-124 : ℝ) / 71) * positiveCusp1Root ^ 2 + ((-110 : ℝ) / 71) * positiveCusp1Root + ((-15 : ℝ) / 71) * 1 := by
  norm_num [positiveCusp1, positiveCusp1Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp1_Bqq_values :
    positiveCusp1.toNetwork.hessianApply positiveCusp1Rates unitState
        positiveCusp1RightKernel positiveCusp1RightKernel 0 = ((328 : ℝ) / 2201) * positiveCusp1Root ^ 2 + ((-48 : ℝ) / 2201) * positiveCusp1Root + ((-368 : ℝ) / 2201) * 1 ∧
    positiveCusp1.toNetwork.hessianApply positiveCusp1Rates unitState
        positiveCusp1RightKernel positiveCusp1RightKernel 1 = ((1952 : ℝ) / 2201) * positiveCusp1Root ^ 2 + ((788 : ℝ) / 2201) * positiveCusp1Root + ((172 : ℝ) / 2201) * 1 := by
  rcases positiveCusp1Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp1, positiveCusp1Rates, positiveCusp1RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp1_Bqh_values :
    positiveCusp1.toNetwork.hessianApply positiveCusp1Rates unitState
        positiveCusp1RightKernel positiveCusp1Center 0 = ((33504 : ℝ) / 68231) * positiveCusp1Root ^ 2 + ((53504 : ℝ) / 68231) * positiveCusp1Root + ((-656 : ℝ) / 68231) * 1 ∧
    positiveCusp1.toNetwork.hessianApply positiveCusp1Rates unitState
        positiveCusp1RightKernel positiveCusp1Center 1 = ((57880 : ℝ) / 68231) * positiveCusp1Root ^ 2 + ((12144 : ℝ) / 68231) * positiveCusp1Root + ((-3740 : ℝ) / 68231) * 1 := by
  rcases positiveCusp1Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp1, positiveCusp1Rates, positiveCusp1RightKernel,
    positiveCusp1Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp1_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp1.toNetwork positiveCusp1Rates
      positiveCusp1RightKernel positiveCusp1LeftKernel positiveCusp1Center 0 4).unfoldingMatrix =
      ((-5394 : ℝ) / 71) * positiveCusp1Root ^ 2 + ((469 : ℝ) / 71) * positiveCusp1Root + ((-49 : ℝ) / 71) * 1 := by
  rcases positiveCusp1Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp1, positiveCusp1Rates, positiveCusp1RightKernel, positiveCusp1LeftKernel,
      positiveCusp1Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp1_cubic_value :
    dot positiveCusp1LeftKernel (positiveCusp1.toNetwork.hessianApply positiveCusp1Rates unitState
      positiveCusp1RightKernel positiveCusp1Center) = ((-5328 : ℝ) / 2201) * positiveCusp1Root ^ 2 + ((-2656 : ℝ) / 2201) * positiveCusp1Root + ((180 : ℝ) / 2201) * 1 := by
  rcases positiveCusp1Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp1_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp1LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp1_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp1.toNetwork := by
  rcases positiveCusp1Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp1Root_lower
  have hu := positiveCusp1Root_upper
  have hs : 0 ≤ positiveCusp1Root ^ 2 := sq_nonneg positiveCusp1Root
  rcases positiveCusp1_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp1_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp1_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp1.toNetwork positiveCusp1Rates
    positiveCusp1RightKernel positiveCusp1LeftKernel positiveCusp1Center 0 4
  · exact positiveCusp1Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp1, positiveCusp1Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp1RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp1LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp1LeftKernel, positiveCusp1RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp1LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp1Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp1LeftKernel, positiveCusp1Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp1_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp1_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
