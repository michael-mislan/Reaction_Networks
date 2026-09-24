import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp21Polynomial (t : ℝ) : ℝ := (530 : ℝ) * t ^ 2 + (130 : ℝ) * t + (-7 : ℝ) * 1

private theorem positiveCusp21Root_exists :
    ∃ t : ℝ, ((2315 : ℝ) / 50956) < t ∧ t < ((2226 : ℝ) / 48997) ∧ positiveCusp21Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp21Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp21Polynomial]
    fun_prop
  have hab : ((2315 : ℝ) / 50956) ≤ ((2226 : ℝ) / 48997) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((2315 : ℝ) / 50956)) (f ((2226 : ℝ) / 48997)) := by
    constructor <;> norm_num [f, positiveCusp21Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((2315 : ℝ) / 50956) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp21Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((2226 : ℝ) / 48997) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp21Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp21Root : ℝ := Classical.choose positiveCusp21Root_exists

theorem positiveCusp21Root_lower : ((2315 : ℝ) / 50956) < positiveCusp21Root :=
  (Classical.choose_spec positiveCusp21Root_exists).1

theorem positiveCusp21Root_upper : positiveCusp21Root < ((2226 : ℝ) / 48997) :=
  (Classical.choose_spec positiveCusp21Root_exists).2.1

theorem positiveCusp21Root_equation : (530 : ℝ) * positiveCusp21Root ^ 2 + (130 : ℝ) * positiveCusp21Root + (-7 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp21Root_exists).2.2


theorem positiveCusp21Root_power_relations :
    let t := positiveCusp21Root
    ((530 : ℝ) * t ^ 2 + (130 : ℝ) * t + (-7 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((530 : ℝ) * t ^ 2 + (130 : ℝ) * t + (-7 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((530 : ℝ) * t ^ 2 + (130 : ℝ) * t + (-7 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((530 : ℝ) * t ^ 2 + (130 : ℝ) * t + (-7 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((530 : ℝ) * t ^ 2 + (130 : ℝ) * t + (-7 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((530 : ℝ) * t ^ 2 + (130 : ℝ) * t + (-7 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((530 : ℝ) * t ^ 2 + (130 : ℝ) * t + (-7 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((530 : ℝ) * t ^ 2 + (130 : ℝ) * t + (-7 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((530 : ℝ) * t ^ 2 + (130 : ℝ) * t + (-7 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp21Root_equation

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

def positiveCusp21 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .zero), (.yy, .x)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp21Rates : Fin 5 → ℝ :=
  let t := positiveCusp21Root
  ![((33 : ℝ) / 23) * t + ((6 : ℝ) / 23) * 1,
    (1 : ℝ) * t,
    ((-54 : ℝ) / 23) * t + ((9 : ℝ) / 23) * 1,
    ((4 : ℝ) / 23) * t + ((7 : ℝ) / 23) * 1,
    ((-6 : ℝ) / 23) * t + ((1 : ℝ) / 23) * 1]

noncomputable def positiveCusp21RightKernel : Species → ℝ :=
  let t := positiveCusp21Root
  ![((-16 : ℝ) / 23) * t + ((-5 : ℝ) / 23) * 1,
    ((27 : ℝ) / 23) * t + ((7 : ℝ) / 23) * 1]

noncomputable def positiveCusp21LeftKernel : Species → ℝ :=
  let t := positiveCusp21Root
  ![((411280 : ℝ) / 2369) * t + ((-21550 : ℝ) / 2369) * 1,
    ((32330 : ℝ) / 2369) * t + ((3160 : ℝ) / 2369) * 1]

noncomputable def positiveCusp21Center : Species → ℝ :=
  let t := positiveCusp21Root
  ![((46538 : ℝ) / 125557) * t + ((67578 : ℝ) / 627785) * 1,
    ((27860 : ℝ) / 125557) * t + ((42042 : ℝ) / 627785) * 1]

theorem positiveCusp21Rates_positive : PositiveVector positiveCusp21Rates := by
  have hl := positiveCusp21Root_lower
  have hu := positiveCusp21Root_upper
  have hs : 0 ≤ positiveCusp21Root ^ 2 := sq_nonneg positiveCusp21Root
  intro k
  fin_cases k <;> simp [positiveCusp21Rates] <;> nlinarith

theorem positiveCusp21_jacobian_values :
    positiveCusp21.toNetwork.jacobian positiveCusp21Rates unitState 0 0 = ((-27 : ℝ) / 23) * positiveCusp21Root + ((-7 : ℝ) / 23) * 1 ∧
    positiveCusp21.toNetwork.jacobian positiveCusp21Rates unitState 0 1 = ((-16 : ℝ) / 23) * positiveCusp21Root + ((-5 : ℝ) / 23) * 1 ∧
    positiveCusp21.toNetwork.jacobian positiveCusp21Rates unitState 1 0 = ((42 : ℝ) / 23) * positiveCusp21Root + ((-7 : ℝ) / 23) * 1 ∧
    positiveCusp21.toNetwork.jacobian positiveCusp21Rates unitState 1 1 = ((-34 : ℝ) / 23) * positiveCusp21Root + ((-2 : ℝ) / 23) * 1 := by
  norm_num [positiveCusp21, positiveCusp21Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp21_Bqq_values :
    positiveCusp21.toNetwork.hessianApply positiveCusp21Rates unitState
        positiveCusp21RightKernel positiveCusp21RightKernel 0 = ((61186 : ℝ) / 323035) * positiveCusp21Root + ((17801 : ℝ) / 323035) * 1 ∧
    positiveCusp21.toNetwork.hessianApply positiveCusp21Rates unitState
        positiveCusp21RightKernel positiveCusp21RightKernel 1 = ((38794 : ℝ) / 323035) * positiveCusp21Root + ((10976 : ℝ) / 323035) * 1 := by
  rcases positiveCusp21Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp21, positiveCusp21Rates, positiveCusp21RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp21_Bqh_values :
    positiveCusp21.toNetwork.hessianApply positiveCusp21Rates unitState
        positiveCusp21RightKernel positiveCusp21Center 0 = ((-32295526 : ℝ) / 1763448065) * positiveCusp21Root + ((-47060643 : ℝ) / 8817240325) * 1 ∧
    positiveCusp21.toNetwork.hessianApply positiveCusp21Rates unitState
        positiveCusp21RightKernel positiveCusp21Center 1 = ((-12014378 : ℝ) / 352689613) * positiveCusp21Root + ((-3474471 : ℝ) / 352689613) * 1 := by
  rcases positiveCusp21Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp21, positiveCusp21Rates, positiveCusp21RightKernel,
    positiveCusp21Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp21_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp21.toNetwork positiveCusp21Rates
      positiveCusp21RightKernel positiveCusp21LeftKernel positiveCusp21Center 1 4).unfoldingMatrix =
      ((-143958600 : ℝ) / 244007) * positiveCusp21Root + ((378540 : ℝ) / 244007) * 1 := by
  rcases positiveCusp21Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp21, positiveCusp21Rates, positiveCusp21RightKernel, positiveCusp21LeftKernel,
      positiveCusp21Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp21_cubic_value :
    dot positiveCusp21LeftKernel (positiveCusp21.toNetwork.hessianApply positiveCusp21Rates unitState
      positiveCusp21RightKernel positiveCusp21Center) = ((-1530654 : ℝ) / 33272605) * positiveCusp21Root + ((-423276 : ℝ) / 33272605) * 1 := by
  rcases positiveCusp21Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp21_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp21LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp21_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp21.toNetwork := by
  rcases positiveCusp21Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp21Root_lower
  have hu := positiveCusp21Root_upper
  have hs : 0 ≤ positiveCusp21Root ^ 2 := sq_nonneg positiveCusp21Root
  rcases positiveCusp21_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp21_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp21_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp21.toNetwork positiveCusp21Rates
    positiveCusp21RightKernel positiveCusp21LeftKernel positiveCusp21Center 1 4
  · exact positiveCusp21Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp21, positiveCusp21Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp21RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp21LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp21LeftKernel, positiveCusp21RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp21LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp21Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp21LeftKernel, positiveCusp21Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp21_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp21_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
