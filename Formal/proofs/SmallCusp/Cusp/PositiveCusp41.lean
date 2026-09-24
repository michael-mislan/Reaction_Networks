import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp41Polynomial (t : ℝ) : ℝ := (933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1

private theorem positiveCusp41Root_exists :
    ∃ t : ℝ, ((778 : ℝ) / 22845) < t ∧ t < ((789 : ℝ) / 23168) ∧ positiveCusp41Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ -(positiveCusp41Polynomial t)
  have hf : Continuous f := by
    dsimp [f, positiveCusp41Polynomial]
    fun_prop
  have hab : ((778 : ℝ) / 22845) ≤ ((789 : ℝ) / 23168) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((778 : ℝ) / 22845)) (f ((789 : ℝ) / 23168)) := by
    constructor <;> norm_num [f, positiveCusp41Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((778 : ℝ) / 22845) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp41Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((789 : ℝ) / 23168) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp41Polynomial] at hft
  · dsimp [f, positiveCusp41Polynomial] at hft ⊢
    nlinarith [hft]

noncomputable def positiveCusp41Root : ℝ := Classical.choose positiveCusp41Root_exists

theorem positiveCusp41Root_lower : ((778 : ℝ) / 22845) < positiveCusp41Root :=
  (Classical.choose_spec positiveCusp41Root_exists).1

theorem positiveCusp41Root_upper : positiveCusp41Root < ((789 : ℝ) / 23168) :=
  (Classical.choose_spec positiveCusp41Root_exists).2.1

theorem positiveCusp41Root_equation : (933 : ℝ) * positiveCusp41Root ^ 3 + (75 : ℝ) * positiveCusp41Root ^ 2 + (-33 : ℝ) * positiveCusp41Root + (1 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp41Root_exists).2.2


theorem positiveCusp41Root_power_relations :
    let t := positiveCusp41Root
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((933 : ℝ) * t ^ 3 + (75 : ℝ) * t ^ 2 + (-33 : ℝ) * t + (1 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp41Root_equation

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

def positiveCusp41 : CodedBimolNetwork where
  reaction := ![(.x, .xx), (.y, .yy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp41Rates : Fin 5 → ℝ :=
  let t := positiveCusp41Root
  ![((-933 : ℝ) / 43) * t ^ 2 + ((-311 : ℝ) / 43) * t + ((26 : ℝ) / 43) * 1,
    ((4665 : ℝ) / 172) * t ^ 2 + ((335 : ℝ) / 43) * t + ((-1 : ℝ) / 172) * 1,
    ((-2799 : ℝ) / 172) * t ^ 2 + ((-158 : ℝ) / 43) * t + ((35 : ℝ) / 172) * 1,
    ((933 : ℝ) / 86) * t ^ 2 + ((91 : ℝ) / 43) * t + ((17 : ℝ) / 86) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp41RightKernel : Species → ℝ :=
  let t := positiveCusp41Root
  ![((-933 : ℝ) / 86) * t ^ 2 + ((81 : ℝ) / 43) * t + ((-17 : ℝ) / 86) * 1,
    ((-2799 : ℝ) / 86) * t ^ 2 + ((-230 : ℝ) / 43) * t + ((35 : ℝ) / 86) * 1]

noncomputable def positiveCusp41LeftKernel : Species → ℝ :=
  let t := positiveCusp41Root
  ![((381597 : ℝ) / 8084) * t ^ 2 + ((3237 : ℝ) / 2021) * t + ((-23319 : ℝ) / 8084) * 1,
    ((-2626395 : ℝ) / 16168) * t ^ 2 + ((-132153 : ℝ) / 8084) * t + ((63429 : ℝ) / 16168) * 1]

noncomputable def positiveCusp41Center : Species → ℝ :=
  let t := positiveCusp41Root
  ![((22082 : ℝ) / 2021) * t ^ 2 + ((-9352 : ℝ) / 2021) * t + ((390 : ℝ) / 2021) * 1,
    ((12946 : ℝ) / 2021) * t ^ 2 + ((6924 : ℝ) / 2021) * t + ((-166 : ℝ) / 2021) * 1]

theorem positiveCusp41Rates_positive : PositiveVector positiveCusp41Rates := by
  have hl := positiveCusp41Root_lower
  have hu := positiveCusp41Root_upper
  have hs : 0 ≤ positiveCusp41Root ^ 2 := sq_nonneg positiveCusp41Root
  intro k
  fin_cases k <;> simp [positiveCusp41Rates] <;> nlinarith

theorem positiveCusp41_jacobian_values :
    positiveCusp41.toNetwork.jacobian positiveCusp41Rates unitState 0 0 = ((2799 : ℝ) / 86) * positiveCusp41Root ^ 2 + ((230 : ℝ) / 43) * positiveCusp41Root + ((-35 : ℝ) / 86) * 1 ∧
    positiveCusp41.toNetwork.jacobian positiveCusp41Rates unitState 0 1 = ((-933 : ℝ) / 86) * positiveCusp41Root ^ 2 + ((81 : ℝ) / 43) * positiveCusp41Root + ((-17 : ℝ) / 86) * 1 ∧
    positiveCusp41.toNetwork.jacobian positiveCusp41Rates unitState 1 0 = ((-1866 : ℝ) / 43) * positiveCusp41Root ^ 2 + ((-407 : ℝ) / 43) * positiveCusp41Root + ((9 : ℝ) / 43) * 1 ∧
    positiveCusp41.toNetwork.jacobian positiveCusp41Rates unitState 1 1 = ((2799 : ℝ) / 172) * positiveCusp41Root ^ 2 + ((72 : ℝ) / 43) * positiveCusp41Root + ((-35 : ℝ) / 172) * 1 := by
  norm_num [positiveCusp41, positiveCusp41Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp41_Bqq_values :
    positiveCusp41.toNetwork.hessianApply positiveCusp41Rates unitState
        positiveCusp41RightKernel positiveCusp41RightKernel 0 = ((-60932 : ℝ) / 13373) * positiveCusp41Root ^ 2 + ((42584 : ℝ) / 13373) * positiveCusp41Root + ((-3532 : ℝ) / 40119) * 1 ∧
    positiveCusp41.toNetwork.hessianApply positiveCusp41Rates unitState
        positiveCusp41RightKernel positiveCusp41RightKernel 1 = ((-162638 : ℝ) / 13373) * positiveCusp41Root ^ 2 + ((-48336 : ℝ) / 13373) * positiveCusp41Root + ((6034 : ℝ) / 40119) * 1 := by
  rcases positiveCusp41Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp41, positiveCusp41Rates, positiveCusp41RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp41_Bqh_values :
    positiveCusp41.toNetwork.hessianApply positiveCusp41Rates unitState
        positiveCusp41RightKernel positiveCusp41Center 0 = ((999500352 : ℝ) / 195473141) * positiveCusp41Root ^ 2 + ((-1815111088 : ℝ) / 586419423) * positiveCusp41Root + ((19823536 : ℝ) / 195473141) * 1 ∧
    positiveCusp41.toNetwork.hessianApply positiveCusp41Rates unitState
        positiveCusp41RightKernel positiveCusp41Center 1 = ((-719336032 : ℝ) / 195473141) * positiveCusp41Root ^ 2 + ((304480464 : ℝ) / 195473141) * positiveCusp41Root + ((-30195184 : ℝ) / 586419423) * 1 := by
  rcases positiveCusp41Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp41, positiveCusp41Rates, positiveCusp41RightKernel,
    positiveCusp41Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp41_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp41.toNetwork positiveCusp41Rates
      positiveCusp41RightKernel positiveCusp41LeftKernel positiveCusp41Center 2 4).unfoldingMatrix =
      ((532434177 : ℝ) / 189974) * positiveCusp41Root ^ 2 + ((33573405 : ℝ) / 94987) * positiveCusp41Root + ((-16060443 : ℝ) / 189974) * 1 := by
  rcases positiveCusp41Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp41, positiveCusp41Rates, positiveCusp41RightKernel, positiveCusp41LeftKernel,
      positiveCusp41Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp41_cubic_value :
    dot positiveCusp41LeftKernel (positiveCusp41.toNetwork.hessianApply positiveCusp41Rates unitState
      positiveCusp41RightKernel positiveCusp41Center) = ((9577416 : ℝ) / 628531) * positiveCusp41Root ^ 2 + ((665104 : ℝ) / 628531) * positiveCusp41Root + ((-127640 : ℝ) / 1885593) * 1 := by
  rcases positiveCusp41Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp41_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp41LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp41_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp41.toNetwork := by
  rcases positiveCusp41Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp41Root_lower
  have hu := positiveCusp41Root_upper
  have hs : 0 ≤ positiveCusp41Root ^ 2 := sq_nonneg positiveCusp41Root
  rcases positiveCusp41_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp41_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp41_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp41.toNetwork positiveCusp41Rates
    positiveCusp41RightKernel positiveCusp41LeftKernel positiveCusp41Center 2 4
  · exact positiveCusp41Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp41, positiveCusp41Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp41RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp41LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp41LeftKernel, positiveCusp41RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp41LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp41Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp41LeftKernel, positiveCusp41Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp41_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp41_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
