import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp0Polynomial (t : ℝ) : ℝ := (582 : ℝ) * t ^ 3 + (162 : ℝ) * t ^ 2 + (18 : ℝ) * t + (-1 : ℝ) * 1

private theorem positiveCusp0Root_exists :
    ∃ t : ℝ, ((459 : ℝ) / 11617) < t ∧ t < ((598 : ℝ) / 15135) ∧ positiveCusp0Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp0Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp0Polynomial]
    fun_prop
  have hab : ((459 : ℝ) / 11617) ≤ ((598 : ℝ) / 15135) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((459 : ℝ) / 11617)) (f ((598 : ℝ) / 15135)) := by
    constructor <;> norm_num [f, positiveCusp0Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((459 : ℝ) / 11617) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp0Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((598 : ℝ) / 15135) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp0Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp0Root : ℝ := Classical.choose positiveCusp0Root_exists

theorem positiveCusp0Root_lower : ((459 : ℝ) / 11617) < positiveCusp0Root :=
  (Classical.choose_spec positiveCusp0Root_exists).1

theorem positiveCusp0Root_upper : positiveCusp0Root < ((598 : ℝ) / 15135) :=
  (Classical.choose_spec positiveCusp0Root_exists).2.1

theorem positiveCusp0Root_equation : (582 : ℝ) * positiveCusp0Root ^ 3 + (162 : ℝ) * positiveCusp0Root ^ 2 + (18 : ℝ) * positiveCusp0Root + (-1 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp0Root_exists).2.2


theorem positiveCusp0Root_power_relations :
    let t := positiveCusp0Root
    ((582 : ℝ) * t ^ 3 + (162 : ℝ) * t ^ 2 + (18 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((582 : ℝ) * t ^ 3 + (162 : ℝ) * t ^ 2 + (18 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((582 : ℝ) * t ^ 3 + (162 : ℝ) * t ^ 2 + (18 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((582 : ℝ) * t ^ 3 + (162 : ℝ) * t ^ 2 + (18 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((582 : ℝ) * t ^ 3 + (162 : ℝ) * t ^ 2 + (18 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((582 : ℝ) * t ^ 3 + (162 : ℝ) * t ^ 2 + (18 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((582 : ℝ) * t ^ 3 + (162 : ℝ) * t ^ 2 + (18 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((582 : ℝ) * t ^ 3 + (162 : ℝ) * t ^ 2 + (18 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((582 : ℝ) * t ^ 3 + (162 : ℝ) * t ^ 2 + (18 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp0Root_equation

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

def positiveCusp0 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp0Rates : Fin 5 → ℝ :=
  let t := positiveCusp0Root
  ![((-1746 : ℝ) / 169) * t ^ 2 + ((-354 : ℝ) / 169) * t + ((32 : ℝ) / 169) * 1,
    ((-582 : ℝ) / 169) * t ^ 2 + ((-456 : ℝ) / 169) * t + ((67 : ℝ) / 169) * 1,
    ((1164 : ℝ) / 169) * t ^ 2 + ((236 : ℝ) / 169) * t + ((35 : ℝ) / 169) * 1,
    ((1164 : ℝ) / 169) * t ^ 2 + ((405 : ℝ) / 169) * t + ((35 : ℝ) / 169) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp0RightKernel : Species → ℝ :=
  let t := positiveCusp0Root
  ![((2328 : ℝ) / 169) * t ^ 2 + ((303 : ℝ) / 169) * t + ((70 : ℝ) / 169) * 1,
    ((1746 : ℝ) / 169) * t ^ 2 + ((523 : ℝ) / 169) * t + ((137 : ℝ) / 169) * 1]

noncomputable def positiveCusp0LeftKernel : Species → ℝ :=
  let t := positiveCusp0Root
  ![((1626108 : ℝ) / 37349) * t ^ 2 + ((294033 : ℝ) / 37349) * t + ((4110 : ℝ) / 37349) * 1,
    ((-111162 : ℝ) / 2197) * t ^ 2 + ((-35889 : ℝ) / 2197) * t + ((3333 : ℝ) / 2197) * 1]

noncomputable def positiveCusp0Center : Species → ℝ :=
  let t := positiveCusp0Root
  ![((21318 : ℝ) / 2197) * t ^ 2 + ((538 : ℝ) / 2197) * t + ((-400 : ℝ) / 2197) * 1,
    ((8406 : ℝ) / 2197) * t ^ 2 + ((760 : ℝ) / 2197) * t + ((170 : ℝ) / 2197) * 1]

theorem positiveCusp0Rates_positive : PositiveVector positiveCusp0Rates := by
  have hl := positiveCusp0Root_lower
  have hu := positiveCusp0Root_upper
  have hs : 0 ≤ positiveCusp0Root ^ 2 := sq_nonneg positiveCusp0Root
  intro k
  fin_cases k <;> simp [positiveCusp0Rates] <;> nlinarith

theorem positiveCusp0_jacobian_values :
    positiveCusp0.toNetwork.jacobian positiveCusp0Rates unitState 0 0 = ((-1746 : ℝ) / 169) * positiveCusp0Root ^ 2 + ((-523 : ℝ) / 169) * positiveCusp0Root + ((-137 : ℝ) / 169) * 1 ∧
    positiveCusp0.toNetwork.jacobian positiveCusp0Rates unitState 0 1 = ((2328 : ℝ) / 169) * positiveCusp0Root ^ 2 + ((303 : ℝ) / 169) * positiveCusp0Root + ((70 : ℝ) / 169) * 1 ∧
    positiveCusp0.toNetwork.jacobian positiveCusp0Rates unitState 1 0 = ((2328 : ℝ) / 169) * positiveCusp0Root ^ 2 + ((641 : ℝ) / 169) * positiveCusp0Root + ((70 : ℝ) / 169) * 1 ∧
    positiveCusp0.toNetwork.jacobian positiveCusp0Rates unitState 1 1 = ((-1164 : ℝ) / 169) * positiveCusp0Root ^ 2 + ((-405 : ℝ) / 169) * positiveCusp0Root + ((-35 : ℝ) / 169) * 1 := by
  norm_num [positiveCusp0, positiveCusp0Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp0_Bqq_values :
    positiveCusp0.toNetwork.hessianApply positiveCusp0Rates unitState
        positiveCusp0RightKernel positiveCusp0RightKernel 0 = ((-2324 : ℝ) / 16393) * positiveCusp0Root ^ 2 + ((-13170 : ℝ) / 16393) * positiveCusp0Root + ((-2728 : ℝ) / 16393) * 1 ∧
    positiveCusp0.toNetwork.hessianApply positiveCusp0Rates unitState
        positiveCusp0RightKernel positiveCusp0RightKernel 1 = ((3388 : ℝ) / 1261) * positiveCusp0Root ^ 2 + ((786 : ℝ) / 1261) * positiveCusp0Root + ((118 : ℝ) / 1261) * 1 := by
  rcases positiveCusp0Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp0, positiveCusp0Rates, positiveCusp0RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp0_Bqh_values :
    positiveCusp0.toNetwork.hessianApply positiveCusp0Rates unitState
        positiveCusp0RightKernel positiveCusp0Center 0 = ((58255006 : ℝ) / 20671573) * positiveCusp0Root ^ 2 + ((16113048 : ℝ) / 20671573) * positiveCusp0Root + ((1150066 : ℝ) / 62014719) * 1 ∧
    positiveCusp0.toNetwork.hessianApply positiveCusp0Rates unitState
        positiveCusp0RightKernel positiveCusp0Center 1 = ((-7990778 : ℝ) / 20671573) * positiveCusp0Root ^ 2 + ((-5267716 : ℝ) / 20671573) * positiveCusp0Root + ((-2180522 : ℝ) / 62014719) * 1 := by
  rcases positiveCusp0Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp0, positiveCusp0Rates, positiveCusp0RightKernel,
    positiveCusp0Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp0_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp0.toNetwork positiveCusp0Rates
      positiveCusp0RightKernel positiveCusp0LeftKernel positiveCusp0Center 0 4).unfoldingMatrix =
      ((-27314424 : ℝ) / 485537) * positiveCusp0Root ^ 2 + ((-9210177 : ℝ) / 485537) * positiveCusp0Root + ((-36474 : ℝ) / 485537) * 1 := by
  rcases positiveCusp0Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp0, positiveCusp0Rates, positiveCusp0RightKernel, positiveCusp0LeftKernel,
      positiveCusp0Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp0_cubic_value :
    dot positiveCusp0LeftKernel (positiveCusp0.toNetwork.hessianApply positiveCusp0Rates unitState
      positiveCusp0RightKernel positiveCusp0Center) = ((-370158 : ℝ) / 213109) * positiveCusp0Root ^ 2 + ((-94026 : ℝ) / 213109) * positiveCusp0Root + ((2152 : ℝ) / 213109) * 1 := by
  rcases positiveCusp0Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp0_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp0LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp0_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp0.toNetwork := by
  rcases positiveCusp0Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp0Root_lower
  have hu := positiveCusp0Root_upper
  have hs : 0 ≤ positiveCusp0Root ^ 2 := sq_nonneg positiveCusp0Root
  rcases positiveCusp0_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp0_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp0_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp0.toNetwork positiveCusp0Rates
    positiveCusp0RightKernel positiveCusp0LeftKernel positiveCusp0Center 0 4
  · exact positiveCusp0Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp0, positiveCusp0Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp0RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp0LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp0LeftKernel, positiveCusp0RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp0LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp0Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp0LeftKernel, positiveCusp0Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp0_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp0_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
