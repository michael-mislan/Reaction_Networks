import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp34Polynomial (t : ℝ) : ℝ := (800 : ℝ) * t ^ 2 + (120 : ℝ) * t + (-3 : ℝ) * 1

private theorem positiveCusp34Root_exists :
    ∃ t : ℝ, ((372 : ℝ) / 17045) < t ∧ t < ((161 : ℝ) / 7377) ∧ positiveCusp34Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp34Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp34Polynomial]
    fun_prop
  have hab : ((372 : ℝ) / 17045) ≤ ((161 : ℝ) / 7377) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((372 : ℝ) / 17045)) (f ((161 : ℝ) / 7377)) := by
    constructor <;> norm_num [f, positiveCusp34Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((372 : ℝ) / 17045) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp34Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((161 : ℝ) / 7377) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp34Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp34Root : ℝ := Classical.choose positiveCusp34Root_exists

theorem positiveCusp34Root_lower : ((372 : ℝ) / 17045) < positiveCusp34Root :=
  (Classical.choose_spec positiveCusp34Root_exists).1

theorem positiveCusp34Root_upper : positiveCusp34Root < ((161 : ℝ) / 7377) :=
  (Classical.choose_spec positiveCusp34Root_exists).2.1

theorem positiveCusp34Root_equation : (800 : ℝ) * positiveCusp34Root ^ 2 + (120 : ℝ) * positiveCusp34Root + (-3 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp34Root_exists).2.2


theorem positiveCusp34Root_power_relations :
    let t := positiveCusp34Root
    ((800 : ℝ) * t ^ 2 + (120 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((800 : ℝ) * t ^ 2 + (120 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((800 : ℝ) * t ^ 2 + (120 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((800 : ℝ) * t ^ 2 + (120 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((800 : ℝ) * t ^ 2 + (120 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((800 : ℝ) * t ^ 2 + (120 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((800 : ℝ) * t ^ 2 + (120 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((800 : ℝ) * t ^ 2 + (120 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((800 : ℝ) * t ^ 2 + (120 : ℝ) * t + (-3 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp34Root_equation

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

def positiveCusp34 : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .xy), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp34Rates : Fin 5 → ℝ :=
  let t := positiveCusp34Root
  ![((-1 : ℝ) / 2) * t + ((1 : ℝ) / 20) * 1,
    (-3 : ℝ) * t + ((2 : ℝ) / 5) * 1,
    ((3 : ℝ) / 10) * 1,
    ((5 : ℝ) / 2) * t + ((1 : ℝ) / 4) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp34RightKernel : Species → ℝ :=
  let t := positiveCusp34Root
  ![((3 : ℝ) / 5) * 1,
    (2 : ℝ) * t + ((9 : ℝ) / 10) * 1]

noncomputable def positiveCusp34LeftKernel : Species → ℝ :=
  let t := positiveCusp34Root
  ![((200 : ℝ) / 9) * t,
    ((-80 : ℝ) / 3) * t + ((4 : ℝ) / 3) * 1]

noncomputable def positiveCusp34Center : Species → ℝ :=
  let t := positiveCusp34Root
  ![((-24 : ℝ) / 5) * t + ((-3 : ℝ) / 50) * 1,
    (-2 : ℝ) * t + ((3 : ℝ) / 20) * 1]

theorem positiveCusp34Rates_positive : PositiveVector positiveCusp34Rates := by
  have hl := positiveCusp34Root_lower
  have hu := positiveCusp34Root_upper
  have hs : 0 ≤ positiveCusp34Root ^ 2 := sq_nonneg positiveCusp34Root
  intro k
  fin_cases k <;> simp [positiveCusp34Rates] <;> nlinarith

theorem positiveCusp34_jacobian_values :
    positiveCusp34.toNetwork.jacobian positiveCusp34Rates unitState 0 0 = (-2 : ℝ) * positiveCusp34Root + ((-9 : ℝ) / 10) * 1 ∧
    positiveCusp34.toNetwork.jacobian positiveCusp34Rates unitState 0 1 = ((3 : ℝ) / 5) * 1 ∧
    positiveCusp34.toNetwork.jacobian positiveCusp34Rates unitState 1 0 = (5 : ℝ) * positiveCusp34Root + ((1 : ℝ) / 2) * 1 ∧
    positiveCusp34.toNetwork.jacobian positiveCusp34Rates unitState 1 1 = (-4 : ℝ) * positiveCusp34Root + ((-3 : ℝ) / 10) * 1 := by
  norm_num [positiveCusp34, positiveCusp34Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp34_Bqq_values :
    positiveCusp34.toNetwork.hessianApply positiveCusp34Rates unitState
        positiveCusp34RightKernel positiveCusp34RightKernel 0 = ((-9 : ℝ) / 5) * positiveCusp34Root + ((-9 : ℝ) / 50) * 1 ∧
    positiveCusp34.toNetwork.hessianApply positiveCusp34Rates unitState
        positiveCusp34RightKernel positiveCusp34RightKernel 1 = ((3 : ℝ) / 10) * positiveCusp34Root + ((27 : ℝ) / 200) * 1 := by
  rcases positiveCusp34Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp34, positiveCusp34Rates, positiveCusp34RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp34_Bqh_values :
    positiveCusp34.toNetwork.hessianApply positiveCusp34Rates unitState
        positiveCusp34RightKernel positiveCusp34Center 0 = ((-27 : ℝ) / 50) * positiveCusp34Root + ((9 : ℝ) / 125) * 1 ∧
    positiveCusp34.toNetwork.hessianApply positiveCusp34Rates unitState
        positiveCusp34RightKernel positiveCusp34Center 1 = ((-12 : ℝ) / 25) * positiveCusp34Root + ((-117 : ℝ) / 2000) * 1 := by
  rcases positiveCusp34Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp34, positiveCusp34Rates, positiveCusp34RightKernel,
    positiveCusp34Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp34_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp34.toNetwork positiveCusp34Rates
      positiveCusp34RightKernel positiveCusp34LeftKernel positiveCusp34Center 0 4).unfoldingMatrix =
      ((1120 : ℝ) / 9) * positiveCusp34Root + ((-56 : ℝ) / 9) * 1 := by
  rcases positiveCusp34Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp34, positiveCusp34Rates, positiveCusp34RightKernel, positiveCusp34LeftKernel,
      positiveCusp34Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp34_cubic_value :
    dot positiveCusp34LeftKernel (positiveCusp34.toNetwork.hessianApply positiveCusp34Rates unitState
      positiveCusp34RightKernel positiveCusp34Center) = ((12 : ℝ) / 5) * positiveCusp34Root + ((-3 : ℝ) / 40) * 1 := by
  rcases positiveCusp34Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp34_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp34LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp34_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp34.toNetwork := by
  rcases positiveCusp34Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp34Root_lower
  have hu := positiveCusp34Root_upper
  have hs : 0 ≤ positiveCusp34Root ^ 2 := sq_nonneg positiveCusp34Root
  rcases positiveCusp34_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp34_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp34_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp34.toNetwork positiveCusp34Rates
    positiveCusp34RightKernel positiveCusp34LeftKernel positiveCusp34Center 0 4
  · exact positiveCusp34Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp34, positiveCusp34Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp34RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp34LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp34LeftKernel, positiveCusp34RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp34LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp34Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp34LeftKernel, positiveCusp34Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp34_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp34_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
