import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp51Polynomial (t : ℝ) : ℝ := (881 : ℝ) * t ^ 3 + (-498 : ℝ) * t ^ 2 + (96 : ℝ) * t + (-4 : ℝ) * 1

private theorem positiveCusp51Root_exists :
    ∃ t : ℝ, ((918 : ℝ) / 16207) < t ∧ t < ((1057 : ℝ) / 18661) ∧ positiveCusp51Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp51Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp51Polynomial]
    fun_prop
  have hab : ((918 : ℝ) / 16207) ≤ ((1057 : ℝ) / 18661) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((918 : ℝ) / 16207)) (f ((1057 : ℝ) / 18661)) := by
    constructor <;> norm_num [f, positiveCusp51Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((918 : ℝ) / 16207) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp51Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((1057 : ℝ) / 18661) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp51Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp51Root : ℝ := Classical.choose positiveCusp51Root_exists

theorem positiveCusp51Root_lower : ((918 : ℝ) / 16207) < positiveCusp51Root :=
  (Classical.choose_spec positiveCusp51Root_exists).1

theorem positiveCusp51Root_upper : positiveCusp51Root < ((1057 : ℝ) / 18661) :=
  (Classical.choose_spec positiveCusp51Root_exists).2.1

theorem positiveCusp51Root_equation : (881 : ℝ) * positiveCusp51Root ^ 3 + (-498 : ℝ) * positiveCusp51Root ^ 2 + (96 : ℝ) * positiveCusp51Root + (-4 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp51Root_exists).2.2


theorem positiveCusp51Root_power_relations :
    let t := positiveCusp51Root
    ((881 : ℝ) * t ^ 3 + (-498 : ℝ) * t ^ 2 + (96 : ℝ) * t + (-4 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((881 : ℝ) * t ^ 3 + (-498 : ℝ) * t ^ 2 + (96 : ℝ) * t + (-4 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((881 : ℝ) * t ^ 3 + (-498 : ℝ) * t ^ 2 + (96 : ℝ) * t + (-4 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((881 : ℝ) * t ^ 3 + (-498 : ℝ) * t ^ 2 + (96 : ℝ) * t + (-4 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((881 : ℝ) * t ^ 3 + (-498 : ℝ) * t ^ 2 + (96 : ℝ) * t + (-4 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((881 : ℝ) * t ^ 3 + (-498 : ℝ) * t ^ 2 + (96 : ℝ) * t + (-4 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((881 : ℝ) * t ^ 3 + (-498 : ℝ) * t ^ 2 + (96 : ℝ) * t + (-4 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((881 : ℝ) * t ^ 3 + (-498 : ℝ) * t ^ 2 + (96 : ℝ) * t + (-4 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((881 : ℝ) * t ^ 3 + (-498 : ℝ) * t ^ 2 + (96 : ℝ) * t + (-4 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp51Root_equation

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

def positiveCusp51 : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp51Rates : Fin 5 → ℝ :=
  let t := positiveCusp51Root
  ![((4405 : ℝ) / 507) * t ^ 2 + ((-1678 : ℝ) / 507) * t + ((106 : ℝ) / 507) * 1,
    ((881 : ℝ) / 507) * t ^ 2 + ((-944 : ℝ) / 507) * t + ((224 : ℝ) / 507) * 1,
    ((881 : ℝ) / 169) * t ^ 2 + ((-437 : ℝ) / 169) * t + ((55 : ℝ) / 169) * 1,
    ((-2643 : ℝ) / 169) * t ^ 2 + ((1142 : ℝ) / 169) * t + ((4 : ℝ) / 169) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp51RightKernel : Species → ℝ :=
  let t := positiveCusp51Root
  ![((9691 : ℝ) / 507) * t ^ 2 + ((-3286 : ℝ) / 507) * t + ((436 : ℝ) / 507) * 1,
    ((7048 : ℝ) / 507) * t ^ 2 + ((-3496 : ℝ) / 507) * t + ((778 : ℝ) / 507) * 1]

noncomputable def positiveCusp51LeftKernel : Species → ℝ :=
  let t := positiveCusp51Root
  ![((-751493 : ℝ) / 16796) * t ^ 2 + ((131345 : ℝ) / 8398) * t + ((-1969 : ℝ) / 4199) * 1,
    ((-473978 : ℝ) / 16055) * t ^ 2 + ((253047 : ℝ) / 32110) * t + ((11631 : ℝ) / 32110) * 1]

noncomputable def positiveCusp51Center : Species → ℝ :=
  let t := positiveCusp51Root
  ![((-324016 : ℝ) / 48165) * t ^ 2 + ((102152 : ℝ) / 48165) * t + ((-6048 : ℝ) / 16055) * 1,
    ((54352 : ℝ) / 9633) * t ^ 2 + ((-9536 : ℝ) / 9633) * t + ((464 : ℝ) / 3211) * 1]

theorem positiveCusp51Rates_positive : PositiveVector positiveCusp51Rates := by
  have hl := positiveCusp51Root_lower
  have hu := positiveCusp51Root_upper
  have hs : 0 ≤ positiveCusp51Root ^ 2 := sq_nonneg positiveCusp51Root
  intro k
  fin_cases k <;> simp [positiveCusp51Rates] <;> nlinarith

theorem positiveCusp51_jacobian_values :
    positiveCusp51.toNetwork.jacobian positiveCusp51Rates unitState 0 0 = ((-7048 : ℝ) / 507) * positiveCusp51Root ^ 2 + ((3496 : ℝ) / 507) * positiveCusp51Root + ((-778 : ℝ) / 507) * 1 ∧
    positiveCusp51.toNetwork.jacobian positiveCusp51Rates unitState 0 1 = ((9691 : ℝ) / 507) * positiveCusp51Root ^ 2 + ((-3286 : ℝ) / 507) * positiveCusp51Root + ((436 : ℝ) / 507) * 1 ∧
    positiveCusp51.toNetwork.jacobian positiveCusp51Rates unitState 1 0 = ((881 : ℝ) / 507) * positiveCusp51Root ^ 2 + ((70 : ℝ) / 507) * positiveCusp51Root + ((224 : ℝ) / 507) * 1 ∧
    positiveCusp51.toNetwork.jacobian positiveCusp51Rates unitState 1 1 = ((-8810 : ℝ) / 507) * positiveCusp51Root ^ 2 + ((2342 : ℝ) / 507) * positiveCusp51Root + ((-212 : ℝ) / 507) * 1 := by
  norm_num [positiveCusp51, positiveCusp51Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp51_Bqq_values :
    positiveCusp51.toNetwork.hessianApply positiveCusp51Rates unitState
        positiveCusp51RightKernel positiveCusp51RightKernel 0 = ((-5520688 : ℝ) / 446667) * positiveCusp51Root ^ 2 + ((716880 : ℝ) / 148889) * positiveCusp51Root + ((-278144 : ℝ) / 446667) * 1 ∧
    positiveCusp51.toNetwork.hessianApply positiveCusp51Rates unitState
        positiveCusp51RightKernel positiveCusp51RightKernel 1 = ((4407680 : ℝ) / 446667) * positiveCusp51Root ^ 2 + ((-478304 : ℝ) / 148889) * positiveCusp51Root + ((133792 : ℝ) / 446667) * 1 := by
  rcases positiveCusp51Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp51, positiveCusp51Rates, positiveCusp51RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp51_Bqh_values :
    positiveCusp51.toNetwork.hessianApply positiveCusp51Rates unitState
        positiveCusp51RightKernel positiveCusp51Center 0 = ((46351652544 : ℝ) / 12461264855) * positiveCusp51Root ^ 2 + ((-47906461184 : ℝ) / 37383794565) * positiveCusp51Root + ((11467562048 : ℝ) / 37383794565) * 1 ∧
    positiveCusp51.toNetwork.hessianApply positiveCusp51Rates unitState
        positiveCusp51RightKernel positiveCusp51Center 1 = ((-18885805760 : ℝ) / 7476758913) * positiveCusp51Root ^ 2 + ((3281268736 : ℝ) / 7476758913) * positiveCusp51Root + ((-1063089856 : ℝ) / 7476758913) * 1 := by
  rcases positiveCusp51Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp51, positiveCusp51Rates, positiveCusp51RightKernel,
    positiveCusp51Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp51_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp51.toNetwork positiveCusp51Rates
      positiveCusp51RightKernel positiveCusp51LeftKernel positiveCusp51Center 0 4).unfoldingMatrix =
      ((-1436706608 : ℝ) / 25928825) * positiveCusp51Root ^ 2 + ((586636681 : ℝ) / 25928825) * positiveCusp51Root + ((-76683972 : ℝ) / 25928825) * 1 := by
  rcases positiveCusp51Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp51, positiveCusp51Rates, positiveCusp51RightKernel, positiveCusp51LeftKernel,
      positiveCusp51Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp51_cubic_value :
    dot positiveCusp51LeftKernel (positiveCusp51.toNetwork.hessianApply positiveCusp51Rates unitState
      positiveCusp51RightKernel positiveCusp51Center) = ((-59068688 : ℝ) / 42433365) * positiveCusp51Root ^ 2 + ((28502336 : ℝ) / 42433365) * positiveCusp51Root + ((-2369312 : ℝ) / 42433365) * 1 := by
  rcases positiveCusp51Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp51_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp51LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp51_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp51.toNetwork := by
  rcases positiveCusp51Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp51Root_lower
  have hu := positiveCusp51Root_upper
  have hs : 0 ≤ positiveCusp51Root ^ 2 := sq_nonneg positiveCusp51Root
  rcases positiveCusp51_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp51_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp51_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp51.toNetwork positiveCusp51Rates
    positiveCusp51RightKernel positiveCusp51LeftKernel positiveCusp51Center 0 4
  · exact positiveCusp51Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp51, positiveCusp51Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp51RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp51LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp51LeftKernel, positiveCusp51RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp51LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp51Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp51LeftKernel, positiveCusp51Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp51_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp51_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
