import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp7Polynomial (t : ℝ) : ℝ := (393 : ℝ) * t ^ 2 + (-54 : ℝ) * t + (1 : ℝ) * 1

private theorem positiveCusp7Root_exists :
    ∃ t : ℝ, ((330 : ℝ) / 14959) < t ∧ t < ((439 : ℝ) / 19900) ∧ positiveCusp7Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ -(positiveCusp7Polynomial t)
  have hf : Continuous f := by
    dsimp [f, positiveCusp7Polynomial]
    fun_prop
  have hab : ((330 : ℝ) / 14959) ≤ ((439 : ℝ) / 19900) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((330 : ℝ) / 14959)) (f ((439 : ℝ) / 19900)) := by
    constructor <;> norm_num [f, positiveCusp7Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((330 : ℝ) / 14959) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp7Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((439 : ℝ) / 19900) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp7Polynomial] at hft
  · dsimp [f, positiveCusp7Polynomial] at hft ⊢
    nlinarith [hft]

noncomputable def positiveCusp7Root : ℝ := Classical.choose positiveCusp7Root_exists

theorem positiveCusp7Root_lower : ((330 : ℝ) / 14959) < positiveCusp7Root :=
  (Classical.choose_spec positiveCusp7Root_exists).1

theorem positiveCusp7Root_upper : positiveCusp7Root < ((439 : ℝ) / 19900) :=
  (Classical.choose_spec positiveCusp7Root_exists).2.1

theorem positiveCusp7Root_equation : (393 : ℝ) * positiveCusp7Root ^ 2 + (-54 : ℝ) * positiveCusp7Root + (1 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp7Root_exists).2.2


theorem positiveCusp7Root_power_relations :
    let t := positiveCusp7Root
    ((393 : ℝ) * t ^ 2 + (-54 : ℝ) * t + (1 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((393 : ℝ) * t ^ 2 + (-54 : ℝ) * t + (1 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((393 : ℝ) * t ^ 2 + (-54 : ℝ) * t + (1 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((393 : ℝ) * t ^ 2 + (-54 : ℝ) * t + (1 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((393 : ℝ) * t ^ 2 + (-54 : ℝ) * t + (1 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((393 : ℝ) * t ^ 2 + (-54 : ℝ) * t + (1 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((393 : ℝ) * t ^ 2 + (-54 : ℝ) * t + (1 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((393 : ℝ) * t ^ 2 + (-54 : ℝ) * t + (1 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((393 : ℝ) * t ^ 2 + (-54 : ℝ) * t + (1 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp7Root_equation

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

def positiveCusp7 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp7Rates : Fin 5 → ℝ :=
  let t := positiveCusp7Root
  ![((-15 : ℝ) / 2) * t + ((1 : ℝ) / 2) * 1,
    ((-31 : ℝ) / 4) * t + ((1 : ℝ) / 4) * 1,
    (12 : ℝ) * t,
    ((9 : ℝ) / 4) * t + ((1 : ℝ) / 4) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp7RightKernel : Species → ℝ :=
  let t := positiveCusp7Root
  ![((7 : ℝ) / 4) * t + ((-1 : ℝ) / 4) * 1,
    ((-11 : ℝ) / 2) * t + ((1 : ℝ) / 2) * 1]

noncomputable def positiveCusp7LeftKernel : Species → ℝ :=
  let t := positiveCusp7Root
  ![((-2489 : ℝ) / 16) * t + ((109 : ℝ) / 48) * 1,
    ((-655 : ℝ) / 16) * t + ((139 : ℝ) / 48) * 1]

noncomputable def positiveCusp7Center : Species → ℝ :=
  let t := positiveCusp7Root
  ![((-1567 : ℝ) / 1179) * t + ((59 : ℝ) / 393) * 1,
    ((-545 : ℝ) / 1179) * t + ((95 : ℝ) / 1179) * 1]

theorem positiveCusp7Rates_positive : PositiveVector positiveCusp7Rates := by
  have hl := positiveCusp7Root_lower
  have hu := positiveCusp7Root_upper
  have hs : 0 ≤ positiveCusp7Root ^ 2 := sq_nonneg positiveCusp7Root
  intro k
  fin_cases k <;> simp [positiveCusp7Rates] <;> nlinarith

theorem positiveCusp7_jacobian_values :
    positiveCusp7.toNetwork.jacobian positiveCusp7Rates unitState 0 0 = ((11 : ℝ) / 2) * positiveCusp7Root + ((-1 : ℝ) / 2) * 1 ∧
    positiveCusp7.toNetwork.jacobian positiveCusp7Rates unitState 0 1 = ((7 : ℝ) / 4) * positiveCusp7Root + ((-1 : ℝ) / 4) * 1 ∧
    positiveCusp7.toNetwork.jacobian positiveCusp7Rates unitState 1 0 = (-10 : ℝ) * positiveCusp7Root ∧
    positiveCusp7.toNetwork.jacobian positiveCusp7Rates unitState 1 1 = ((23 : ℝ) / 4) * positiveCusp7Root + ((-1 : ℝ) / 4) * 1 := by
  norm_num [positiveCusp7, positiveCusp7Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp7_Bqq_values :
    positiveCusp7.toNetwork.hessianApply positiveCusp7Rates unitState
        positiveCusp7RightKernel positiveCusp7RightKernel 0 = ((-32498 : ℝ) / 51483) * positiveCusp7Root + ((3838 : ℝ) / 51483) * 1 ∧
    positiveCusp7.toNetwork.hessianApply positiveCusp7Rates unitState
        positiveCusp7RightKernel positiveCusp7RightKernel 1 = ((-27730 : ℝ) / 51483) * positiveCusp7Root + ((810 : ℝ) / 17161) * 1 := by
  rcases positiveCusp7Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp7, positiveCusp7Rates, positiveCusp7RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp7_Bqh_values :
    positiveCusp7.toNetwork.hessianApply positiveCusp7Rates unitState
        positiveCusp7RightKernel positiveCusp7Center 0 = ((3681932 : ℝ) / 60698457) * positiveCusp7Root + ((-499892 : ℝ) / 60698457) * 1 ∧
    positiveCusp7.toNetwork.hessianApply positiveCusp7Rates unitState
        positiveCusp7RightKernel positiveCusp7Center 1 = ((8941852 : ℝ) / 60698457) * positiveCusp7Root + ((-901412 : ℝ) / 60698457) * 1 := by
  rcases positiveCusp7Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp7, positiveCusp7Rates, positiveCusp7RightKernel,
    positiveCusp7Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp7_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp7.toNetwork positiveCusp7Rates
      positiveCusp7RightKernel positiveCusp7LeftKernel positiveCusp7Center 1 4).unfoldingMatrix =
      ((2227 : ℝ) / 2) * positiveCusp7Root + ((-263 : ℝ) / 6) * 1 := by
  rcases positiveCusp7Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp7, positiveCusp7Rates, positiveCusp7RightKernel, positiveCusp7LeftKernel,
      positiveCusp7Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp7_cubic_value :
    dot positiveCusp7LeftKernel (positiveCusp7.toNetwork.hessianApply positiveCusp7Rates unitState
      positiveCusp7RightKernel positiveCusp7Center) = ((50692 : ℝ) / 154449) * positiveCusp7Root + ((-3452 : ℝ) / 154449) * 1 := by
  rcases positiveCusp7Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp7_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp7LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp7_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp7.toNetwork := by
  rcases positiveCusp7Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp7Root_lower
  have hu := positiveCusp7Root_upper
  have hs : 0 ≤ positiveCusp7Root ^ 2 := sq_nonneg positiveCusp7Root
  rcases positiveCusp7_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp7_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp7_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp7.toNetwork positiveCusp7Rates
    positiveCusp7RightKernel positiveCusp7LeftKernel positiveCusp7Center 1 4
  · exact positiveCusp7Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp7, positiveCusp7Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp7RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp7LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp7LeftKernel, positiveCusp7RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp7LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp7Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp7LeftKernel, positiveCusp7Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp7_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp7_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
