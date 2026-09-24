import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp27Polynomial (t : ℝ) : ℝ := (677 : ℝ) * t ^ 2 + (252 : ℝ) * t + (-12 : ℝ) * 1

private theorem positiveCusp27Root_exists :
    ∃ t : ℝ, ((905 : ℝ) / 21186) < t ∧ t < ((1066 : ℝ) / 24955) ∧ positiveCusp27Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp27Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp27Polynomial]
    fun_prop
  have hab : ((905 : ℝ) / 21186) ≤ ((1066 : ℝ) / 24955) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((905 : ℝ) / 21186)) (f ((1066 : ℝ) / 24955)) := by
    constructor <;> norm_num [f, positiveCusp27Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((905 : ℝ) / 21186) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp27Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((1066 : ℝ) / 24955) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp27Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp27Root : ℝ := Classical.choose positiveCusp27Root_exists

theorem positiveCusp27Root_lower : ((905 : ℝ) / 21186) < positiveCusp27Root :=
  (Classical.choose_spec positiveCusp27Root_exists).1

theorem positiveCusp27Root_upper : positiveCusp27Root < ((1066 : ℝ) / 24955) :=
  (Classical.choose_spec positiveCusp27Root_exists).2.1

theorem positiveCusp27Root_equation : (677 : ℝ) * positiveCusp27Root ^ 2 + (252 : ℝ) * positiveCusp27Root + (-12 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp27Root_exists).2.2


theorem positiveCusp27Root_power_relations :
    let t := positiveCusp27Root
    ((677 : ℝ) * t ^ 2 + (252 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((677 : ℝ) * t ^ 2 + (252 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((677 : ℝ) * t ^ 2 + (252 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((677 : ℝ) * t ^ 2 + (252 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((677 : ℝ) * t ^ 2 + (252 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((677 : ℝ) * t ^ 2 + (252 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((677 : ℝ) * t ^ 2 + (252 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((677 : ℝ) * t ^ 2 + (252 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((677 : ℝ) * t ^ 2 + (252 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp27Root_equation

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

def positiveCusp27 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp27Rates : Fin 5 → ℝ :=
  let t := positiveCusp27Root
  ![((9 : ℝ) / 8) * t + ((1 : ℝ) / 4) * 1,
    ((-17 : ℝ) / 10) * t + ((2 : ℝ) / 5) * 1,
    (1 : ℝ) * t,
    ((-3 : ℝ) / 20) * t + ((3 : ℝ) / 10) * 1,
    ((-11 : ℝ) / 40) * t + ((1 : ℝ) / 20) * 1]

noncomputable def positiveCusp27RightKernel : Species → ℝ :=
  let t := positiveCusp27Root
  ![((-2 : ℝ) / 5) * t + ((-1 : ℝ) / 5) * 1,
    ((37 : ℝ) / 20) * t + ((3 : ℝ) / 10) * 1]

noncomputable def positiveCusp27LeftKernel : Species → ℝ :=
  let t := positiveCusp27Root
  ![((142847 : ℝ) / 18700) * t + ((-13357 : ℝ) / 9350) * 1,
    ((15571 : ℝ) / 1870) * t + ((1544 : ℝ) / 935) * 1]

noncomputable def positiveCusp27Center : Species → ℝ :=
  let t := positiveCusp27Root
  ![((61235 : ℝ) / 126599) * t + ((11430 : ℝ) / 126599) * 1,
    ((-61010 : ℝ) / 126599) * t + ((10320 : ℝ) / 126599) * 1]

theorem positiveCusp27Rates_positive : PositiveVector positiveCusp27Rates := by
  have hl := positiveCusp27Root_lower
  have hu := positiveCusp27Root_upper
  have hs : 0 ≤ positiveCusp27Root ^ 2 := sq_nonneg positiveCusp27Root
  intro k
  fin_cases k <;> simp [positiveCusp27Rates] <;> nlinarith

theorem positiveCusp27_jacobian_values :
    positiveCusp27.toNetwork.jacobian positiveCusp27Rates unitState 0 0 = ((-37 : ℝ) / 20) * positiveCusp27Root + ((-3 : ℝ) / 10) * 1 ∧
    positiveCusp27.toNetwork.jacobian positiveCusp27Rates unitState 0 1 = ((-2 : ℝ) / 5) * positiveCusp27Root + ((-1 : ℝ) / 5) * 1 ∧
    positiveCusp27.toNetwork.jacobian positiveCusp27Rates unitState 1 0 = ((43 : ℝ) / 20) * positiveCusp27Root + ((-3 : ℝ) / 10) * 1 ∧
    positiveCusp27.toNetwork.jacobian positiveCusp27Rates unitState 1 1 = ((-9 : ℝ) / 20) * positiveCusp27Root + ((-1 : ℝ) / 10) * 1 := by
  norm_num [positiveCusp27, positiveCusp27Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp27_Bqq_values :
    positiveCusp27.toNetwork.hessianApply positiveCusp27Rates unitState
        positiveCusp27RightKernel positiveCusp27RightKernel 0 = ((-5945 : ℝ) / 458329) * positiveCusp27Root + ((25590 : ℝ) / 458329) * 1 ∧
    positiveCusp27.toNetwork.hessianApply positiveCusp27Rates unitState
        positiveCusp27RightKernel positiveCusp27RightKernel 1 = ((186680 : ℝ) / 458329) * positiveCusp27Root + ((5940 : ℝ) / 458329) * 1 := by
  rcases positiveCusp27Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp27, positiveCusp27Rates, positiveCusp27RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp27_Bqh_values :
    positiveCusp27.toNetwork.hessianApply positiveCusp27Rates unitState
        positiveCusp27RightKernel positiveCusp27Center 0 = ((6426303900 : ℝ) / 58023993071) * positiveCusp27Root + ((-543631800 : ℝ) / 58023993071) * 1 ∧
    positiveCusp27.toNetwork.hessianApply positiveCusp27Rates unitState
        positiveCusp27RightKernel positiveCusp27Center 1 = ((-10410430515 : ℝ) / 58023993071) * positiveCusp27Root + ((-370770570 : ℝ) / 58023993071) * 1 := by
  rcases positiveCusp27Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp27, positiveCusp27Rates, positiveCusp27RightKernel,
    positiveCusp27Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp27_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp27.toNetwork positiveCusp27Rates
      positiveCusp27RightKernel positiveCusp27LeftKernel positiveCusp27Center 2 4).unfoldingMatrix =
      ((-3265171 : ℝ) / 69938) * positiveCusp27Root + ((-593481 : ℝ) / 34969) * 1 := by
  rcases positiveCusp27Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp27, positiveCusp27Rates, positiveCusp27RightKernel, positiveCusp27LeftKernel,
      positiveCusp27Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp27_cubic_value :
    dot positiveCusp27LeftKernel (positiveCusp27.toNetwork.hessianApply positiveCusp27Rates unitState
      positiveCusp27RightKernel positiveCusp27Center) = ((-28977015 : ℝ) / 85707523) * positiveCusp27Root + ((-741570 : ℝ) / 85707523) * 1 := by
  rcases positiveCusp27Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp27_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp27LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp27_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp27.toNetwork := by
  rcases positiveCusp27Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp27Root_lower
  have hu := positiveCusp27Root_upper
  have hs : 0 ≤ positiveCusp27Root ^ 2 := sq_nonneg positiveCusp27Root
  rcases positiveCusp27_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp27_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp27_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp27.toNetwork positiveCusp27Rates
    positiveCusp27RightKernel positiveCusp27LeftKernel positiveCusp27Center 2 4
  · exact positiveCusp27Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp27, positiveCusp27Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp27RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp27LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp27LeftKernel, positiveCusp27RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp27LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp27Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp27LeftKernel, positiveCusp27Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp27_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp27_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
