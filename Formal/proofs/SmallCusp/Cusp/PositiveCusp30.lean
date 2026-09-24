import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp30Polynomial (t : ℝ) : ℝ := (530 : ℝ) * t ^ 2 + (130 : ℝ) * t + (-7 : ℝ) * 1

private theorem positiveCusp30Root_exists :
    ∃ t : ℝ, ((2315 : ℝ) / 50956) < t ∧ t < ((2226 : ℝ) / 48997) ∧ positiveCusp30Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp30Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp30Polynomial]
    fun_prop
  have hab : ((2315 : ℝ) / 50956) ≤ ((2226 : ℝ) / 48997) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((2315 : ℝ) / 50956)) (f ((2226 : ℝ) / 48997)) := by
    constructor <;> norm_num [f, positiveCusp30Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((2315 : ℝ) / 50956) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp30Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((2226 : ℝ) / 48997) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp30Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp30Root : ℝ := Classical.choose positiveCusp30Root_exists

theorem positiveCusp30Root_lower : ((2315 : ℝ) / 50956) < positiveCusp30Root :=
  (Classical.choose_spec positiveCusp30Root_exists).1

theorem positiveCusp30Root_upper : positiveCusp30Root < ((2226 : ℝ) / 48997) :=
  (Classical.choose_spec positiveCusp30Root_exists).2.1

theorem positiveCusp30Root_equation : (530 : ℝ) * positiveCusp30Root ^ 2 + (130 : ℝ) * positiveCusp30Root + (-7 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp30Root_exists).2.2


theorem positiveCusp30Root_power_relations :
    let t := positiveCusp30Root
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
  have h := positiveCusp30Root_equation

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

def positiveCusp30 : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp30Rates : Fin 5 → ℝ :=
  let t := positiveCusp30Root
  ![((-6 : ℝ) / 23) * t + ((1 : ℝ) / 23) * 1,
    ((-54 : ℝ) / 23) * t + ((9 : ℝ) / 23) * 1,
    ((4 : ℝ) / 23) * t + ((7 : ℝ) / 23) * 1,
    ((33 : ℝ) / 23) * t + ((6 : ℝ) / 23) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp30RightKernel : Species → ℝ :=
  let t := positiveCusp30Root
  ![((-15 : ℝ) / 23) * t + ((14 : ℝ) / 23) * 1,
    ((35 : ℝ) / 23) * t + ((21 : ℝ) / 23) * 1]

noncomputable def positiveCusp30LeftKernel : Species → ℝ :=
  let t := positiveCusp30Root
  ![((20935 : ℝ) / 12397) * t + ((4764 : ℝ) / 12397) * 1,
    ((-8215 : ℝ) / 1771) * t + ((1695 : ℝ) / 1771) * 1]

noncomputable def positiveCusp30Center : Species → ℝ :=
  let t := positiveCusp30Root
  ![((-46455 : ℝ) / 13409) * t + ((-595 : ℝ) / 13409) * 1,
    ((3195 : ℝ) / 13409) * t + ((1526 : ℝ) / 13409) * 1]

theorem positiveCusp30Rates_positive : PositiveVector positiveCusp30Rates := by
  have hl := positiveCusp30Root_lower
  have hu := positiveCusp30Root_upper
  have hs : 0 ≤ positiveCusp30Root ^ 2 := sq_nonneg positiveCusp30Root
  intro k
  fin_cases k <;> simp [positiveCusp30Rates] <;> nlinarith

theorem positiveCusp30_jacobian_values :
    positiveCusp30.toNetwork.jacobian positiveCusp30Rates unitState 0 0 = ((-35 : ℝ) / 23) * positiveCusp30Root + ((-21 : ℝ) / 23) * 1 ∧
    positiveCusp30.toNetwork.jacobian positiveCusp30Rates unitState 0 1 = ((-15 : ℝ) / 23) * positiveCusp30Root + ((14 : ℝ) / 23) * 1 ∧
    positiveCusp30.toNetwork.jacobian positiveCusp30Rates unitState 1 0 = ((43 : ℝ) / 23) * positiveCusp30Root + ((12 : ℝ) / 23) * 1 ∧
    positiveCusp30.toNetwork.jacobian positiveCusp30Rates unitState 1 1 = ((-27 : ℝ) / 23) * positiveCusp30Root + ((-7 : ℝ) / 23) * 1 := by
  norm_num [positiveCusp30, positiveCusp30Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp30_Bqq_values :
    positiveCusp30.toNetwork.hessianApply positiveCusp30Rates unitState
        positiveCusp30RightKernel positiveCusp30RightKernel 0 = ((-132220 : ℝ) / 64607) * positiveCusp30Root + ((-11459 : ℝ) / 64607) * 1 ∧
    positiveCusp30.toNetwork.hessianApply positiveCusp30Rates unitState
        positiveCusp30RightKernel positiveCusp30RightKernel 1 = ((1234 : ℝ) / 2809) * positiveCusp30Root + ((413 : ℝ) / 2809) * 1 := by
  rcases positiveCusp30Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp30, positiveCusp30Rates, positiveCusp30RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp30_Bqh_values :
    positiveCusp30.toNetwork.hessianApply positiveCusp30Rates unitState
        positiveCusp30RightKernel positiveCusp30Center 0 = ((-33652507 : ℝ) / 37665881) * positiveCusp30Root + ((4614281 : ℝ) / 37665881) * 1 ∧
    positiveCusp30.toNetwork.hessianApply positiveCusp30Rates unitState
        positiveCusp30RightKernel positiveCusp30Center 1 = ((3096803 : ℝ) / 37665881) * positiveCusp30Root + ((-2794855 : ℝ) / 37665881) * 1 := by
  rcases positiveCusp30Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp30, positiveCusp30Rates, positiveCusp30RightKernel,
    positiveCusp30Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp30_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp30.toNetwork positiveCusp30Rates
      positiveCusp30RightKernel positiveCusp30LeftKernel positiveCusp30Center 0 4).unfoldingMatrix =
      ((10961460 : ℝ) / 954569) * positiveCusp30Root + ((-2670435 : ℝ) / 954569) * 1 := by
  rcases positiveCusp30Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp30, positiveCusp30Rates, positiveCusp30RightKernel, positiveCusp30LeftKernel,
      positiveCusp30Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp30_cubic_value :
    dot positiveCusp30LeftKernel (positiveCusp30.toNetwork.hessianApply positiveCusp30Rates unitState
      positiveCusp30RightKernel positiveCusp30Center) = ((533037 : ℝ) / 710677) * positiveCusp30Root + ((-34755 : ℝ) / 710677) * 1 := by
  rcases positiveCusp30Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp30_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp30LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp30_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp30.toNetwork := by
  rcases positiveCusp30Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp30Root_lower
  have hu := positiveCusp30Root_upper
  have hs : 0 ≤ positiveCusp30Root ^ 2 := sq_nonneg positiveCusp30Root
  rcases positiveCusp30_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp30_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp30_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp30.toNetwork positiveCusp30Rates
    positiveCusp30RightKernel positiveCusp30LeftKernel positiveCusp30Center 0 4
  · exact positiveCusp30Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp30, positiveCusp30Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp30RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp30LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp30LeftKernel, positiveCusp30RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp30LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp30Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp30LeftKernel, positiveCusp30Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp30_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp30_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
