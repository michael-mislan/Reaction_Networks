import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp37Polynomial (t : ℝ) : ℝ := (1676 : ℝ) * t ^ 2 + (-70 : ℝ) * t + (-49 : ℝ) * 1

private theorem positiveCusp37Root_exists :
    ∃ t : ℝ, ((3080 : ℝ) / 15947) < t ∧ t < ((1723 : ℝ) / 8921) ∧ positiveCusp37Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp37Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp37Polynomial]
    fun_prop
  have hab : ((3080 : ℝ) / 15947) ≤ ((1723 : ℝ) / 8921) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((3080 : ℝ) / 15947)) (f ((1723 : ℝ) / 8921)) := by
    constructor <;> norm_num [f, positiveCusp37Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((3080 : ℝ) / 15947) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp37Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((1723 : ℝ) / 8921) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp37Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp37Root : ℝ := Classical.choose positiveCusp37Root_exists

theorem positiveCusp37Root_lower : ((3080 : ℝ) / 15947) < positiveCusp37Root :=
  (Classical.choose_spec positiveCusp37Root_exists).1

theorem positiveCusp37Root_upper : positiveCusp37Root < ((1723 : ℝ) / 8921) :=
  (Classical.choose_spec positiveCusp37Root_exists).2.1

theorem positiveCusp37Root_equation : (1676 : ℝ) * positiveCusp37Root ^ 2 + (-70 : ℝ) * positiveCusp37Root + (-49 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp37Root_exists).2.2


theorem positiveCusp37Root_power_relations :
    let t := positiveCusp37Root
    ((1676 : ℝ) * t ^ 2 + (-70 : ℝ) * t + (-49 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((1676 : ℝ) * t ^ 2 + (-70 : ℝ) * t + (-49 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((1676 : ℝ) * t ^ 2 + (-70 : ℝ) * t + (-49 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((1676 : ℝ) * t ^ 2 + (-70 : ℝ) * t + (-49 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((1676 : ℝ) * t ^ 2 + (-70 : ℝ) * t + (-49 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((1676 : ℝ) * t ^ 2 + (-70 : ℝ) * t + (-49 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((1676 : ℝ) * t ^ 2 + (-70 : ℝ) * t + (-49 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((1676 : ℝ) * t ^ 2 + (-70 : ℝ) * t + (-49 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((1676 : ℝ) * t ^ 2 + (-70 : ℝ) * t + (-49 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp37Root_equation

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

def positiveCusp37 : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp37Rates : Fin 5 → ℝ :=
  let t := positiveCusp37Root
  ![((14 : ℝ) / 15) * t + ((-2 : ℝ) / 15) * 1,
    ((-8 : ℝ) / 35) * t + ((2 : ℝ) / 5) * 1,
    ((-19 : ℝ) / 105) * t + ((1 : ℝ) / 15) * 1,
    ((-32 : ℝ) / 21) * t + ((2 : ℝ) / 3) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp37RightKernel : Species → ℝ :=
  let t := positiveCusp37Root
  ![((-32 : ℝ) / 21) * t + ((2 : ℝ) / 3) * 1,
    ((4 : ℝ) / 7) * t]

noncomputable def positiveCusp37LeftKernel : Species → ℝ :=
  let t := positiveCusp37Root
  ![((7123 : ℝ) / 2835) * t + ((1591 : ℝ) / 810) * 1,
    ((-6704 : ℝ) / 567) * t + ((499 : ℝ) / 162) * 1]

noncomputable def positiveCusp37Center : Species → ℝ :=
  let t := positiveCusp37Root
  ![((2632 : ℝ) / 419) * t + ((-504 : ℝ) / 419) * 1,
    ((-2672 : ℝ) / 1257) * t + ((476 : ℝ) / 1257) * 1]

theorem positiveCusp37Rates_positive : PositiveVector positiveCusp37Rates := by
  have hl := positiveCusp37Root_lower
  have hu := positiveCusp37Root_upper
  have hs : 0 ≤ positiveCusp37Root ^ 2 := sq_nonneg positiveCusp37Root
  intro k
  fin_cases k <;> simp [positiveCusp37Rates] <;> nlinarith

theorem positiveCusp37_jacobian_values :
    positiveCusp37.toNetwork.jacobian positiveCusp37Rates unitState 0 0 = ((-4 : ℝ) / 7) * positiveCusp37Root ∧
    positiveCusp37.toNetwork.jacobian positiveCusp37Rates unitState 0 1 = ((-32 : ℝ) / 21) * positiveCusp37Root + ((2 : ℝ) / 3) * 1 ∧
    positiveCusp37.toNetwork.jacobian positiveCusp37Rates unitState 1 0 = ((16 : ℝ) / 15) * positiveCusp37Root + ((2 : ℝ) / 15) * 1 ∧
    positiveCusp37.toNetwork.jacobian positiveCusp37Rates unitState 1 1 = ((-52 : ℝ) / 21) * positiveCusp37Root + ((-2 : ℝ) / 3) * 1 := by
  norm_num [positiveCusp37, positiveCusp37Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp37_Bqq_values :
    positiveCusp37.toNetwork.hessianApply positiveCusp37Rates unitState
        positiveCusp37RightKernel positiveCusp37RightKernel 0 = ((695984 : ℝ) / 526683) * positiveCusp37Root + ((-127568 : ℝ) / 526683) * 1 ∧
    positiveCusp37.toNetwork.hessianApply positiveCusp37Rates unitState
        positiveCusp37RightKernel positiveCusp37RightKernel 1 = ((-281056 : ℝ) / 526683) * positiveCusp37Root + ((33208 : ℝ) / 526683) * 1 := by
  rcases positiveCusp37Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp37, positiveCusp37Rates, positiveCusp37RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp37_Bqh_values :
    positiveCusp37.toNetwork.hessianApply positiveCusp37Rates unitState
        positiveCusp37RightKernel positiveCusp37Center 0 = ((-936988352 : ℝ) / 220680177) * positiveCusp37Root + ((179980304 : ℝ) / 220680177) * 1 ∧
    positiveCusp37.toNetwork.hessianApply positiveCusp37Rates unitState
        positiveCusp37RightKernel positiveCusp37Center 1 = ((496158976 : ℝ) / 220680177) * positiveCusp37Root + ((-94346896 : ℝ) / 220680177) * 1 := by
  rcases positiveCusp37Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp37, positiveCusp37Rates, positiveCusp37RightKernel,
    positiveCusp37Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp37_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp37.toNetwork positiveCusp37Rates
      positiveCusp37RightKernel positiveCusp37LeftKernel positiveCusp37Center 0 2).unfoldingMatrix =
      ((204472 : ℝ) / 2835) * positiveCusp37Root + ((-10438 : ℝ) / 405) * 1 := by
  rcases positiveCusp37Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp37, positiveCusp37Rates, positiveCusp37RightKernel, positiveCusp37LeftKernel,
      positiveCusp37Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp37_cubic_value :
    dot positiveCusp37LeftKernel (positiveCusp37.toNetwork.hessianApply positiveCusp37Rates unitState
      positiveCusp37RightKernel positiveCusp37Center) = ((2177200 : ℝ) / 526683) * positiveCusp37Root + ((-423472 : ℝ) / 526683) * 1 := by
  rcases positiveCusp37Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp37_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp37LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp37_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp37.toNetwork := by
  rcases positiveCusp37Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp37Root_lower
  have hu := positiveCusp37Root_upper
  have hs : 0 ≤ positiveCusp37Root ^ 2 := sq_nonneg positiveCusp37Root
  rcases positiveCusp37_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp37_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp37_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp37.toNetwork positiveCusp37Rates
    positiveCusp37RightKernel positiveCusp37LeftKernel positiveCusp37Center 0 2
  · exact positiveCusp37Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp37, positiveCusp37Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp37RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp37LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp37LeftKernel, positiveCusp37RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp37LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp37Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp37LeftKernel, positiveCusp37Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp37_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp37_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
