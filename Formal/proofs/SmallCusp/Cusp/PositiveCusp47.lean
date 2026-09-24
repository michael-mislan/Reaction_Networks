import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp47Polynomial (t : ℝ) : ℝ := (43 : ℝ) * t ^ 2 + (-64 : ℝ) * t + (16 : ℝ) * 1

private theorem positiveCusp47Root_exists :
    ∃ t : ℝ, ((5280 : ℝ) / 16609) < t ∧ t < ((6049 : ℝ) / 19028) ∧ positiveCusp47Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ -(positiveCusp47Polynomial t)
  have hf : Continuous f := by
    dsimp [f, positiveCusp47Polynomial]
    fun_prop
  have hab : ((5280 : ℝ) / 16609) ≤ ((6049 : ℝ) / 19028) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((5280 : ℝ) / 16609)) (f ((6049 : ℝ) / 19028)) := by
    constructor <;> norm_num [f, positiveCusp47Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((5280 : ℝ) / 16609) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp47Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((6049 : ℝ) / 19028) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp47Polynomial] at hft
  · dsimp [f, positiveCusp47Polynomial] at hft ⊢
    nlinarith [hft]

noncomputable def positiveCusp47Root : ℝ := Classical.choose positiveCusp47Root_exists

theorem positiveCusp47Root_lower : ((5280 : ℝ) / 16609) < positiveCusp47Root :=
  (Classical.choose_spec positiveCusp47Root_exists).1

theorem positiveCusp47Root_upper : positiveCusp47Root < ((6049 : ℝ) / 19028) :=
  (Classical.choose_spec positiveCusp47Root_exists).2.1

theorem positiveCusp47Root_equation : (43 : ℝ) * positiveCusp47Root ^ 2 + (-64 : ℝ) * positiveCusp47Root + (16 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp47Root_exists).2.2


theorem positiveCusp47Root_power_relations :
    let t := positiveCusp47Root
    ((43 : ℝ) * t ^ 2 + (-64 : ℝ) * t + (16 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((43 : ℝ) * t ^ 2 + (-64 : ℝ) * t + (16 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((43 : ℝ) * t ^ 2 + (-64 : ℝ) * t + (16 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((43 : ℝ) * t ^ 2 + (-64 : ℝ) * t + (16 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((43 : ℝ) * t ^ 2 + (-64 : ℝ) * t + (16 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((43 : ℝ) * t ^ 2 + (-64 : ℝ) * t + (16 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((43 : ℝ) * t ^ 2 + (-64 : ℝ) * t + (16 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((43 : ℝ) * t ^ 2 + (-64 : ℝ) * t + (16 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((43 : ℝ) * t ^ 2 + (-64 : ℝ) * t + (16 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp47Root_equation

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

def positiveCusp47 : CodedBimolNetwork where
  reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .yy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp47Rates : Fin 5 → ℝ :=
  let t := positiveCusp47Root
  ![((-3 : ℝ) / 4) * t + ((1 : ℝ) / 3) * 1,
    ((1 : ℝ) / 12) * t + ((1 : ℝ) / 3) * 1,
    ((-5 : ℝ) / 12) * t + ((1 : ℝ) / 3) * 1,
    (1 : ℝ) * t,
    ((1 : ℝ) / 12) * t]

noncomputable def positiveCusp47RightKernel : Species → ℝ :=
  let t := positiveCusp47Root
  ![((-5 : ℝ) / 6) * t + ((2 : ℝ) / 3) * 1,
    ((-2 : ℝ) / 3) * t + ((4 : ℝ) / 3) * 1]

noncomputable def positiveCusp47LeftKernel : Species → ℝ :=
  let t := positiveCusp47Root
  ![((989 : ℝ) / 160) * t + ((-67 : ℝ) / 40) * 1,
    ((387 : ℝ) / 80) * t + ((-3 : ℝ) / 4) * 1]

noncomputable def positiveCusp47Center : Species → ℝ :=
  let t := positiveCusp47Root
  ![((1952 : ℝ) / 645) * t + ((-832 : ℝ) / 645) * 1,
    ((-404 : ℝ) / 129) * t + ((48 : ℝ) / 43) * 1]

theorem positiveCusp47Rates_positive : PositiveVector positiveCusp47Rates := by
  have hl := positiveCusp47Root_lower
  have hu := positiveCusp47Root_upper
  have hs : 0 ≤ positiveCusp47Root ^ 2 := sq_nonneg positiveCusp47Root
  intro k
  fin_cases k <;> simp [positiveCusp47Rates] <;> nlinarith

theorem positiveCusp47_jacobian_values :
    positiveCusp47.toNetwork.jacobian positiveCusp47Rates unitState 0 0 = ((2 : ℝ) / 3) * positiveCusp47Root + ((-4 : ℝ) / 3) * 1 ∧
    positiveCusp47.toNetwork.jacobian positiveCusp47Rates unitState 0 1 = ((-5 : ℝ) / 6) * positiveCusp47Root + ((2 : ℝ) / 3) * 1 ∧
    positiveCusp47.toNetwork.jacobian positiveCusp47Rates unitState 1 0 = ((1 : ℝ) / 4) * positiveCusp47Root + ((1 : ℝ) / 3) * 1 ∧
    positiveCusp47.toNetwork.jacobian positiveCusp47Rates unitState 1 1 = ((7 : ℝ) / 12) * positiveCusp47Root + ((-1 : ℝ) / 3) * 1 := by
  norm_num [positiveCusp47, positiveCusp47Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp47_Bqq_values :
    positiveCusp47.toNetwork.hessianApply positiveCusp47Rates unitState
        positiveCusp47RightKernel positiveCusp47RightKernel 0 = ((17072 : ℝ) / 16641) * positiveCusp47Root + ((-12352 : ℝ) / 16641) * 1 ∧
    positiveCusp47.toNetwork.hessianApply positiveCusp47Rates unitState
        positiveCusp47RightKernel positiveCusp47RightKernel 1 = ((-13120 : ℝ) / 16641) * positiveCusp47Root + ((2240 : ℝ) / 5547) * 1 := by
  rcases positiveCusp47Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp47, positiveCusp47Rates, positiveCusp47RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp47_Bqh_values :
    positiveCusp47.toNetwork.hessianApply positiveCusp47Rates unitState
        positiveCusp47RightKernel positiveCusp47Center 0 = ((-12655808 : ℝ) / 3577815) * positiveCusp47Root + ((4764928 : ℝ) / 3577815) * 1 ∧
    positiveCusp47.toNetwork.hessianApply positiveCusp47Rates unitState
        positiveCusp47RightKernel positiveCusp47Center 1 = ((178304 : ℝ) / 49923) * positiveCusp47Root + ((-62464 : ℝ) / 49923) * 1 := by
  rcases positiveCusp47Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp47, positiveCusp47Rates, positiveCusp47RightKernel,
    positiveCusp47Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp47_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp47.toNetwork positiveCusp47Rates
      positiveCusp47RightKernel positiveCusp47LeftKernel positiveCusp47Center 0 4).unfoldingMatrix =
      ((-387 : ℝ) / 5) * positiveCusp47Root + ((558 : ℝ) / 25) * 1 := by
  rcases positiveCusp47Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp47, positiveCusp47Rates, positiveCusp47RightKernel, positiveCusp47LeftKernel,
      positiveCusp47Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp47_cubic_value :
    dot positiveCusp47LeftKernel (positiveCusp47.toNetwork.hessianApply positiveCusp47Rates unitState
      positiveCusp47RightKernel positiveCusp47Center) = ((-116656 : ℝ) / 83205) * positiveCusp47Root + ((34496 : ℝ) / 83205) * 1 := by
  rcases positiveCusp47Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp47_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp47LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp47_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp47.toNetwork := by
  rcases positiveCusp47Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp47Root_lower
  have hu := positiveCusp47Root_upper
  have hs : 0 ≤ positiveCusp47Root ^ 2 := sq_nonneg positiveCusp47Root
  rcases positiveCusp47_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp47_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp47_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp47.toNetwork positiveCusp47Rates
    positiveCusp47RightKernel positiveCusp47LeftKernel positiveCusp47Center 0 4
  · exact positiveCusp47Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp47, positiveCusp47Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp47RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp47LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp47LeftKernel, positiveCusp47RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp47LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp47Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp47LeftKernel, positiveCusp47Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp47_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp47_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
