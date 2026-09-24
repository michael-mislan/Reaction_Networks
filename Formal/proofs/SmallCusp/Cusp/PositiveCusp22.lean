import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp22Polynomial (t : ℝ) : ℝ := (225 : ℝ) * t ^ 3 + (-135 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1

private theorem positiveCusp22Root_exists :
    ∃ t : ℝ, ((993 : ℝ) / 20962) < t ∧ t < ((1075 : ℝ) / 22693) ∧ positiveCusp22Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp22Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp22Polynomial]
    fun_prop
  have hab : ((993 : ℝ) / 20962) ≤ ((1075 : ℝ) / 22693) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((993 : ℝ) / 20962)) (f ((1075 : ℝ) / 22693)) := by
    constructor <;> norm_num [f, positiveCusp22Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((993 : ℝ) / 20962) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp22Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((1075 : ℝ) / 22693) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp22Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp22Root : ℝ := Classical.choose positiveCusp22Root_exists

theorem positiveCusp22Root_lower : ((993 : ℝ) / 20962) < positiveCusp22Root :=
  (Classical.choose_spec positiveCusp22Root_exists).1

theorem positiveCusp22Root_upper : positiveCusp22Root < ((1075 : ℝ) / 22693) :=
  (Classical.choose_spec positiveCusp22Root_exists).2.1

theorem positiveCusp22Root_equation : (225 : ℝ) * positiveCusp22Root ^ 3 + (-135 : ℝ) * positiveCusp22Root ^ 2 + (27 : ℝ) * positiveCusp22Root + (-1 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp22Root_exists).2.2


theorem positiveCusp22Root_power_relations :
    let t := positiveCusp22Root
    ((225 : ℝ) * t ^ 3 + (-135 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((225 : ℝ) * t ^ 3 + (-135 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((225 : ℝ) * t ^ 3 + (-135 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((225 : ℝ) * t ^ 3 + (-135 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((225 : ℝ) * t ^ 3 + (-135 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((225 : ℝ) * t ^ 3 + (-135 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((225 : ℝ) * t ^ 3 + (-135 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((225 : ℝ) * t ^ 3 + (-135 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((225 : ℝ) * t ^ 3 + (-135 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp22Root_equation

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

def positiveCusp22 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .yy), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp22Rates : Fin 5 → ℝ :=
  let t := positiveCusp22Root
  ![((15 : ℝ) / 2) * t ^ 2 + (-4 : ℝ) * t + ((1 : ℝ) / 2) * 1,
    ((15 : ℝ) / 2) * t ^ 2 + (-3 : ℝ) * t + ((1 : ℝ) / 6) * 1,
    (-15 : ℝ) * t ^ 2 + (7 : ℝ) * t,
    (-1 : ℝ) * t + ((1 : ℝ) / 3) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp22RightKernel : Species → ℝ :=
  let t := positiveCusp22Root
  ![(1 : ℝ) * t + ((-1 : ℝ) / 3) * 1,
    ((15 : ℝ) / 2) * t ^ 2 + (-4 : ℝ) * t + ((1 : ℝ) / 2) * 1]

noncomputable def positiveCusp22LeftKernel : Species → ℝ :=
  let t := positiveCusp22Root
  ![((-10125 : ℝ) / 118) * t ^ 2 + ((450 : ℝ) / 59) * t + ((-165 : ℝ) / 118) * 1,
    ((-675 : ℝ) / 59) * t ^ 2 + ((-765 : ℝ) / 118) * t + ((273 : ℝ) / 118) * 1]

noncomputable def positiveCusp22Center : Species → ℝ :=
  let t := positiveCusp22Root
  ![((70 : ℝ) / 59) * t ^ 2 + ((-644 : ℝ) / 885) * t + ((122 : ℝ) / 885) * 1,
    ((124 : ℝ) / 59) * t ^ 2 + ((-716 : ℝ) / 885) * t + ((88 : ℝ) / 885) * 1]

theorem positiveCusp22Rates_positive : PositiveVector positiveCusp22Rates := by
  have hl := positiveCusp22Root_lower
  have hu := positiveCusp22Root_upper
  have hs : 0 ≤ positiveCusp22Root ^ 2 := sq_nonneg positiveCusp22Root
  intro k
  fin_cases k <;> simp [positiveCusp22Rates] <;> nlinarith

theorem positiveCusp22_jacobian_values :
    positiveCusp22.toNetwork.jacobian positiveCusp22Rates unitState 0 0 = ((-15 : ℝ) / 2) * positiveCusp22Root ^ 2 + (4 : ℝ) * positiveCusp22Root + ((-1 : ℝ) / 2) * 1 ∧
    positiveCusp22.toNetwork.jacobian positiveCusp22Rates unitState 0 1 = (1 : ℝ) * positiveCusp22Root + ((-1 : ℝ) / 3) * 1 ∧
    positiveCusp22.toNetwork.jacobian positiveCusp22Rates unitState 1 0 = (15 : ℝ) * positiveCusp22Root ^ 2 + (-5 : ℝ) * positiveCusp22Root ∧
    positiveCusp22.toNetwork.jacobian positiveCusp22Rates unitState 1 1 = (-15 : ℝ) * positiveCusp22Root ^ 2 + (4 : ℝ) * positiveCusp22Root + ((-1 : ℝ) / 3) * 1 := by
  norm_num [positiveCusp22, positiveCusp22Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp22_Bqq_values :
    positiveCusp22.toNetwork.hessianApply positiveCusp22Rates unitState
        positiveCusp22RightKernel positiveCusp22RightKernel 0 = ((4 : ℝ) / 5) * positiveCusp22Root ^ 2 + ((-92 : ℝ) / 225) * positiveCusp22Root + ((16 : ℝ) / 225) * 1 ∧
    positiveCusp22.toNetwork.hessianApply positiveCusp22Rates unitState
        positiveCusp22RightKernel positiveCusp22RightKernel 1 = ((4 : ℝ) / 5) * positiveCusp22Root ^ 2 + ((-104 : ℝ) / 225) * positiveCusp22Root + ((4 : ℝ) / 75) * 1 := by
  rcases positiveCusp22Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp22, positiveCusp22Rates, positiveCusp22RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp22_Bqh_values :
    positiveCusp22.toNetwork.hessianApply positiveCusp22Rates unitState
        positiveCusp22RightKernel positiveCusp22Center 0 = ((-1252 : ℝ) / 13275) * positiveCusp22Root ^ 2 + ((9064 : ℝ) / 199125) * positiveCusp22Root + ((-1292 : ℝ) / 199125) * 1 ∧
    positiveCusp22.toNetwork.hessianApply positiveCusp22Rates unitState
        positiveCusp22RightKernel positiveCusp22Center 1 = ((1484 : ℝ) / 13275) * positiveCusp22Root ^ 2 + ((-248 : ℝ) / 199125) * positiveCusp22Root + ((-1756 : ℝ) / 199125) * 1 := by
  rcases positiveCusp22Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp22, positiveCusp22Rates, positiveCusp22RightKernel,
    positiveCusp22Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp22_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp22.toNetwork positiveCusp22Rates
      positiveCusp22RightKernel positiveCusp22LeftKernel positiveCusp22Center 1 4).unfoldingMatrix =
      ((-1389825 : ℝ) / 3481) * positiveCusp22Root ^ 2 + ((679320 : ℝ) / 3481) * positiveCusp22Root + ((-96399 : ℝ) / 3481) * 1 := by
  rcases positiveCusp22Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp22, positiveCusp22Rates, positiveCusp22RightKernel, positiveCusp22LeftKernel,
      positiveCusp22Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp22_cubic_value :
    dot positiveCusp22LeftKernel (positiveCusp22.toNetwork.hessianApply positiveCusp22Rates unitState
      positiveCusp22RightKernel positiveCusp22Center) = ((-48 : ℝ) / 295) * positiveCusp22Root ^ 2 + ((536 : ℝ) / 4425) * positiveCusp22Root + ((-224 : ℝ) / 13275) * 1 := by
  rcases positiveCusp22Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp22_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp22LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp22_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp22.toNetwork := by
  rcases positiveCusp22Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp22Root_lower
  have hu := positiveCusp22Root_upper
  have hs : 0 ≤ positiveCusp22Root ^ 2 := sq_nonneg positiveCusp22Root
  rcases positiveCusp22_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp22_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp22_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp22.toNetwork positiveCusp22Rates
    positiveCusp22RightKernel positiveCusp22LeftKernel positiveCusp22Center 1 4
  · exact positiveCusp22Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp22, positiveCusp22Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp22RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp22LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp22LeftKernel, positiveCusp22RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp22LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp22Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp22LeftKernel, positiveCusp22Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp22_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp22_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
