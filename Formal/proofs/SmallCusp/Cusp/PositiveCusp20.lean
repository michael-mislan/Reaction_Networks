import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp20Polynomial (t : ℝ) : ℝ := (109 : ℝ) * t ^ 2 + (-6 : ℝ) * t + (-3 : ℝ) * 1

private theorem positiveCusp20Root_exists :
    ∃ t : ℝ, ((990 : ℝ) / 5059) < t ∧ t < ((4069 : ℝ) / 20793) ∧ positiveCusp20Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp20Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp20Polynomial]
    fun_prop
  have hab : ((990 : ℝ) / 5059) ≤ ((4069 : ℝ) / 20793) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((990 : ℝ) / 5059)) (f ((4069 : ℝ) / 20793)) := by
    constructor <;> norm_num [f, positiveCusp20Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((990 : ℝ) / 5059) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp20Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((4069 : ℝ) / 20793) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp20Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp20Root : ℝ := Classical.choose positiveCusp20Root_exists

theorem positiveCusp20Root_lower : ((990 : ℝ) / 5059) < positiveCusp20Root :=
  (Classical.choose_spec positiveCusp20Root_exists).1

theorem positiveCusp20Root_upper : positiveCusp20Root < ((4069 : ℝ) / 20793) :=
  (Classical.choose_spec positiveCusp20Root_exists).2.1

theorem positiveCusp20Root_equation : (109 : ℝ) * positiveCusp20Root ^ 2 + (-6 : ℝ) * positiveCusp20Root + (-3 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp20Root_exists).2.2


theorem positiveCusp20Root_power_relations :
    let t := positiveCusp20Root
    ((109 : ℝ) * t ^ 2 + (-6 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((109 : ℝ) * t ^ 2 + (-6 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((109 : ℝ) * t ^ 2 + (-6 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((109 : ℝ) * t ^ 2 + (-6 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((109 : ℝ) * t ^ 2 + (-6 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((109 : ℝ) * t ^ 2 + (-6 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((109 : ℝ) * t ^ 2 + (-6 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((109 : ℝ) * t ^ 2 + (-6 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((109 : ℝ) * t ^ 2 + (-6 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp20Root_equation

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

def positiveCusp20 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .y), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp20Rates : Fin 5 → ℝ :=
  let t := positiveCusp20Root
  ![((-3 : ℝ) / 8) * t + ((1 : ℝ) / 8) * 1,
    ((-1 : ℝ) / 8) * t + ((3 : ℝ) / 8) * 1,
    ((-9 : ℝ) / 4) * t + ((3 : ℝ) / 4) * 1,
    ((7 : ℝ) / 4) * t + ((-1 : ℝ) / 4) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp20RightKernel : Species → ℝ :=
  let t := positiveCusp20Root
  ![((9 : ℝ) / 4) * t + ((1 : ℝ) / 4) * 1,
    ((13 : ℝ) / 8) * t + ((1 : ℝ) / 8) * 1]

noncomputable def positiveCusp20LeftKernel : Species → ℝ :=
  let t := positiveCusp20Root
  ![((7957 : ℝ) / 134) * t + ((-1419 : ℝ) / 134) * 1,
    ((-2943 : ℝ) / 536) * t + ((925 : ℝ) / 536) * 1]

noncomputable def positiveCusp20Center : Species → ℝ :=
  let t := positiveCusp20Root
  ![((2659 : ℝ) / 14606) * t + ((403 : ℝ) / 14606) * 1,
    ((-4999 : ℝ) / 14606) * t + ((-483 : ℝ) / 14606) * 1]

theorem positiveCusp20Rates_positive : PositiveVector positiveCusp20Rates := by
  have hl := positiveCusp20Root_lower
  have hu := positiveCusp20Root_upper
  have hs : 0 ≤ positiveCusp20Root ^ 2 := sq_nonneg positiveCusp20Root
  intro k
  fin_cases k <;> simp [positiveCusp20Rates] <;> nlinarith

theorem positiveCusp20_jacobian_values :
    positiveCusp20.toNetwork.jacobian positiveCusp20Rates unitState 0 0 = ((-13 : ℝ) / 8) * positiveCusp20Root + ((-1 : ℝ) / 8) * 1 ∧
    positiveCusp20.toNetwork.jacobian positiveCusp20Rates unitState 0 1 = ((9 : ℝ) / 4) * positiveCusp20Root + ((1 : ℝ) / 4) * 1 ∧
    positiveCusp20.toNetwork.jacobian positiveCusp20Rates unitState 1 0 = ((-1 : ℝ) / 4) * positiveCusp20Root + ((3 : ℝ) / 4) * 1 ∧
    positiveCusp20.toNetwork.jacobian positiveCusp20Rates unitState 1 1 = ((-7 : ℝ) / 4) * positiveCusp20Root + ((-3 : ℝ) / 4) * 1 := by
  norm_num [positiveCusp20, positiveCusp20Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp20_Bqq_values :
    positiveCusp20.toNetwork.hessianApply positiveCusp20Rates unitState
        positiveCusp20RightKernel positiveCusp20RightKernel 0 = ((13603 : ℝ) / 47524) * positiveCusp20Root + ((1951 : ℝ) / 47524) * 1 ∧
    positiveCusp20.toNetwork.hessianApply positiveCusp20Rates unitState
        positiveCusp20RightKernel positiveCusp20RightKernel 1 = ((-11279 : ℝ) / 23762) * positiveCusp20Root + ((-1443 : ℝ) / 23762) * 1 := by
  rcases positiveCusp20Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp20, positiveCusp20Rates, positiveCusp20RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp20_Bqh_values :
    positiveCusp20.toNetwork.hessianApply positiveCusp20Rates unitState
        positiveCusp20RightKernel positiveCusp20Center 0 = ((-32169457 : ℝ) / 347067772) * positiveCusp20Root + ((-4427669 : ℝ) / 347067772) * 1 ∧
    positiveCusp20.toNetwork.hessianApply positiveCusp20Rates unitState
        positiveCusp20RightKernel positiveCusp20Center 1 = ((9176154 : ℝ) / 86766943) * positiveCusp20Root + ((1214418 : ℝ) / 86766943) * 1 := by
  rcases positiveCusp20Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp20, positiveCusp20Rates, positiveCusp20RightKernel,
    positiveCusp20Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp20_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp20.toNetwork positiveCusp20Rates
      positiveCusp20RightKernel positiveCusp20LeftKernel positiveCusp20Center 0 3).unfoldingMatrix =
      ((-1660179 : ℝ) / 8978) * positiveCusp20Root + ((314073 : ℝ) / 8978) * 1 := by
  rcases positiveCusp20Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp20, positiveCusp20Rates, positiveCusp20RightKernel, positiveCusp20LeftKernel,
      positiveCusp20Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp20_cubic_value :
    dot positiveCusp20LeftKernel (positiveCusp20.toNetwork.hessianApply positiveCusp20Rates unitState
      positiveCusp20RightKernel positiveCusp20Center) = ((-8399 : ℝ) / 1592054) * positiveCusp20Root + ((-13083 : ℝ) / 1592054) * 1 := by
  rcases positiveCusp20Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp20_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp20LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp20_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp20.toNetwork := by
  rcases positiveCusp20Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp20Root_lower
  have hu := positiveCusp20Root_upper
  have hs : 0 ≤ positiveCusp20Root ^ 2 := sq_nonneg positiveCusp20Root
  rcases positiveCusp20_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp20_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp20_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp20.toNetwork positiveCusp20Rates
    positiveCusp20RightKernel positiveCusp20LeftKernel positiveCusp20Center 0 3
  · exact positiveCusp20Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp20, positiveCusp20Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp20RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp20LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp20LeftKernel, positiveCusp20RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp20LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp20Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp20LeftKernel, positiveCusp20Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp20_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp20_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
