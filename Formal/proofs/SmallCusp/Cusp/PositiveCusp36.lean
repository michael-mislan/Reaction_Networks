import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp36Polynomial (t : ℝ) : ℝ := (933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1

private theorem positiveCusp36Root_exists :
    ∃ t : ℝ, ((778 : ℝ) / 22845) < t ∧ t < ((789 : ℝ) / 23168) ∧ positiveCusp36Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ -(positiveCusp36Polynomial t)
  have hf : Continuous f := by
    dsimp [f, positiveCusp36Polynomial]
    fun_prop
  have hab : ((778 : ℝ) / 22845) ≤ ((789 : ℝ) / 23168) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((778 : ℝ) / 22845)) (f ((789 : ℝ) / 23168)) := by
    constructor <;> norm_num [f, positiveCusp36Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((778 : ℝ) / 22845) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp36Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((789 : ℝ) / 23168) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp36Polynomial] at hft
  · dsimp [f, positiveCusp36Polynomial] at hft ⊢
    nlinarith [hft]

noncomputable def positiveCusp36Root : ℝ := Classical.choose positiveCusp36Root_exists

theorem positiveCusp36Root_lower : ((778 : ℝ) / 22845) < positiveCusp36Root :=
  (Classical.choose_spec positiveCusp36Root_exists).1

theorem positiveCusp36Root_upper : positiveCusp36Root < ((789 : ℝ) / 23168) :=
  (Classical.choose_spec positiveCusp36Root_exists).2.1

theorem positiveCusp36Root_equation : (933 : ℝ) * positiveCusp36Root ^ 3 + (75 : ℝ) * positiveCusp36Root ^ 2 + (-33 : ℝ) * positiveCusp36Root + (1 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp36Root_exists).2.2


theorem positiveCusp36Root_power_relations :
    let t := positiveCusp36Root
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp36Root_equation

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

def positiveCusp36 : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp36Rates : Fin 5 → ℝ :=
  let t := positiveCusp36Root
  ![((-2799 : ℝ) / 172) * t ^ 2 + ((-158 : ℝ) / 43) * t + ((35 : ℝ) / 172) * 1,
    ((-933 : ℝ) / 43) * t ^ 2 + ((-311 : ℝ) / 43) * t + ((26 : ℝ) / 43) * 1,
    ((933 : ℝ) / 86) * t ^ 2 + ((91 : ℝ) / 43) * t + ((17 : ℝ) / 86) * 1,
    ((4665 : ℝ) / 172) * t ^ 2 + ((335 : ℝ) / 43) * t + ((-1 : ℝ) / 172) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp36RightKernel : Species → ℝ :=
  let t := positiveCusp36Root
  ![((-933 : ℝ) / 172) * t ^ 2 + ((-153 : ℝ) / 43) * t + ((69 : ℝ) / 172) * 1,
    ((933 : ℝ) / 172) * t ^ 2 + ((24 : ℝ) / 43) * t + ((103 : ℝ) / 172) * 1]

noncomputable def positiveCusp36LeftKernel : Species → ℝ :=
  let t := positiveCusp36Root
  ![((55669 : ℝ) / 688) * t ^ 2 + ((960 : ℝ) / 43) * t + ((-161 : ℝ) / 688) * 1,
    ((21459 : ℝ) / 688) * t ^ 2 + ((509 : ℝ) / 172) * t + ((821 : ℝ) / 688) * 1]

noncomputable def positiveCusp36Center : Species → ℝ :=
  let t := positiveCusp36Root
  ![((11799 : ℝ) / 344) * t ^ 2 + ((263 : ℝ) / 86) * t + ((-95 : ℝ) / 344) * 1,
    ((-12337 : ℝ) / 344) * t ^ 2 + ((-745 : ℝ) / 86) * t + ((137 : ℝ) / 344) * 1]

theorem positiveCusp36Rates_positive : PositiveVector positiveCusp36Rates := by
  have hl := positiveCusp36Root_lower
  have hu := positiveCusp36Root_upper
  have hs : 0 ≤ positiveCusp36Root ^ 2 := sq_nonneg positiveCusp36Root
  intro k
  fin_cases k <;> simp [positiveCusp36Rates] <;> nlinarith

theorem positiveCusp36_jacobian_values :
    positiveCusp36.toNetwork.jacobian positiveCusp36Rates unitState 0 0 = ((-933 : ℝ) / 172) * positiveCusp36Root ^ 2 + ((-24 : ℝ) / 43) * positiveCusp36Root + ((-103 : ℝ) / 172) * 1 ∧
    positiveCusp36.toNetwork.jacobian positiveCusp36Rates unitState 0 1 = ((-933 : ℝ) / 172) * positiveCusp36Root ^ 2 + ((-153 : ℝ) / 43) * positiveCusp36Root + ((69 : ℝ) / 172) * 1 ∧
    positiveCusp36.toNetwork.jacobian positiveCusp36Rates unitState 1 0 = ((4665 : ℝ) / 172) * positiveCusp36Root ^ 2 + ((335 : ℝ) / 43) * positiveCusp36Root + ((-1 : ℝ) / 172) * 1 ∧
    positiveCusp36.toNetwork.jacobian positiveCusp36Rates unitState 1 1 = ((2799 : ℝ) / 172) * positiveCusp36Root ^ 2 + ((72 : ℝ) / 43) * positiveCusp36Root + ((-35 : ℝ) / 172) * 1 := by
  norm_num [positiveCusp36, positiveCusp36Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp36_Bqq_values :
    positiveCusp36.toNetwork.hessianApply positiveCusp36Rates unitState
        positiveCusp36RightKernel positiveCusp36RightKernel 0 = ((462183 : ℝ) / 26746) * positiveCusp36Root ^ 2 + ((22614 : ℝ) / 13373) * positiveCusp36Root + ((-4735 : ℝ) / 26746) * 1 ∧
    positiveCusp36.toNetwork.hessianApply positiveCusp36Rates unitState
        positiveCusp36RightKernel positiveCusp36RightKernel 1 = ((-479337 : ℝ) / 26746) * positiveCusp36Root ^ 2 + ((-55874 : ℝ) / 13373) * positiveCusp36Root + ((5601 : ℝ) / 26746) * 1 := by
  rcases positiveCusp36Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp36, positiveCusp36Rates, positiveCusp36RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp36_Bqh_values :
    positiveCusp36.toNetwork.hessianApply positiveCusp36Rates unitState
        positiveCusp36RightKernel positiveCusp36Center 0 = ((-450285199 : ℝ) / 16636012) * positiveCusp36Root ^ 2 + ((-28395895 : ℝ) / 4159003) * positiveCusp36Root + ((4708215 : ℝ) / 16636012) * 1 ∧
    positiveCusp36.toNetwork.hessianApply positiveCusp36Rates unitState
        positiveCusp36RightKernel positiveCusp36Center 1 = ((743821197 : ℝ) / 16636012) * positiveCusp36Root ^ 2 + ((39342149 : ℝ) / 4159003) * positiveCusp36Root + ((-19880911 : ℝ) / 49908036) * 1 := by
  rcases positiveCusp36Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp36, positiveCusp36Rates, positiveCusp36RightKernel,
    positiveCusp36Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp36_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp36.toNetwork positiveCusp36Rates
      positiveCusp36RightKernel positiveCusp36LeftKernel positiveCusp36Center 0 4).unfoldingMatrix =
      ((-41052 : ℝ) / 43) * positiveCusp36Root ^ 2 + ((-7965 : ℝ) / 43) * positiveCusp36Root + ((121 : ℝ) / 129) * 1 := by
  rcases positiveCusp36Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp36, positiveCusp36Rates, positiveCusp36RightKernel, positiveCusp36LeftKernel,
      positiveCusp36Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp36_cubic_value :
    dot positiveCusp36LeftKernel (positiveCusp36.toNetwork.hessianApply positiveCusp36Rates unitState
      positiveCusp36RightKernel positiveCusp36Center) = ((-1546943 : ℝ) / 53492) * positiveCusp36Root ^ 2 + ((-62287 : ℝ) / 13373) * positiveCusp36Root + ((27541 : ℝ) / 160476) * 1 := by
  rcases positiveCusp36Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp36_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp36LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp36_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp36.toNetwork := by
  rcases positiveCusp36Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp36Root_lower
  have hu := positiveCusp36Root_upper
  have hs : 0 ≤ positiveCusp36Root ^ 2 := sq_nonneg positiveCusp36Root
  rcases positiveCusp36_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp36_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp36_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp36.toNetwork positiveCusp36Rates
    positiveCusp36RightKernel positiveCusp36LeftKernel positiveCusp36Center 0 4
  · exact positiveCusp36Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp36, positiveCusp36Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp36RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp36LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp36LeftKernel, positiveCusp36RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp36LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp36Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp36LeftKernel, positiveCusp36Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp36_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp36_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
