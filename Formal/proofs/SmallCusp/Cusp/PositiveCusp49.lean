import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp49Polynomial (t : ℝ) : ℝ := (61 : ℝ) * t ^ 2 + (-17 : ℝ) * t + (1 : ℝ) * 1

private theorem positiveCusp49Root_exists :
    ∃ t : ℝ, ((1926 : ℝ) / 9911) < t ∧ t < ((2255 : ℝ) / 11604) ∧ positiveCusp49Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp49Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp49Polynomial]
    fun_prop
  have hab : ((1926 : ℝ) / 9911) ≤ ((2255 : ℝ) / 11604) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((1926 : ℝ) / 9911)) (f ((2255 : ℝ) / 11604)) := by
    constructor <;> norm_num [f, positiveCusp49Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((1926 : ℝ) / 9911) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp49Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((2255 : ℝ) / 11604) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp49Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp49Root : ℝ := Classical.choose positiveCusp49Root_exists

theorem positiveCusp49Root_lower : ((1926 : ℝ) / 9911) < positiveCusp49Root :=
  (Classical.choose_spec positiveCusp49Root_exists).1

theorem positiveCusp49Root_upper : positiveCusp49Root < ((2255 : ℝ) / 11604) :=
  (Classical.choose_spec positiveCusp49Root_exists).2.1

theorem positiveCusp49Root_equation : (61 : ℝ) * positiveCusp49Root ^ 2 + (-17 : ℝ) * positiveCusp49Root + (1 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp49Root_exists).2.2


theorem positiveCusp49Root_power_relations :
    let t := positiveCusp49Root
    ((61 : ℝ) * t ^ 2 + (-17 : ℝ) * t + (1 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((61 : ℝ) * t ^ 2 + (-17 : ℝ) * t + (1 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((61 : ℝ) * t ^ 2 + (-17 : ℝ) * t + (1 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((61 : ℝ) * t ^ 2 + (-17 : ℝ) * t + (1 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((61 : ℝ) * t ^ 2 + (-17 : ℝ) * t + (1 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((61 : ℝ) * t ^ 2 + (-17 : ℝ) * t + (1 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((61 : ℝ) * t ^ 2 + (-17 : ℝ) * t + (1 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((61 : ℝ) * t ^ 2 + (-17 : ℝ) * t + (1 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((61 : ℝ) * t ^ 2 + (-17 : ℝ) * t + (1 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp49Root_equation

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

def positiveCusp49 : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp49Rates : Fin 5 → ℝ :=
  let t := positiveCusp49Root
  ![(2 : ℝ) * t,
    (-10 : ℝ) * t + (2 : ℝ) * 1,
    (-5 : ℝ) * t + (1 : ℝ) * 1,
    (12 : ℝ) * t + (-2 : ℝ) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp49RightKernel : Species → ℝ :=
  let t := positiveCusp49Root
  ![(-8 : ℝ) * t + (2 : ℝ) * 1,
    (-30 : ℝ) * t + (6 : ℝ) * 1]

noncomputable def positiveCusp49LeftKernel : Species → ℝ :=
  let t := positiveCusp49Root
  ![((305 : ℝ) / 18) * t + ((-4 : ℝ) / 3) * 1,
    ((122 : ℝ) / 27) * t + ((-7 : ℝ) / 54) * 1]

noncomputable def positiveCusp49Center : Species → ℝ :=
  let t := positiveCusp49Root
  ![((5536 : ℝ) / 183) * t + ((-1072 : ℝ) / 183) * 1,
    ((-2192 : ℝ) / 183) * t + ((416 : ℝ) / 183) * 1]

theorem positiveCusp49Rates_positive : PositiveVector positiveCusp49Rates := by
  have hl := positiveCusp49Root_lower
  have hu := positiveCusp49Root_upper
  have hs : 0 ≤ positiveCusp49Root ^ 2 := sq_nonneg positiveCusp49Root
  intro k
  fin_cases k <;> simp [positiveCusp49Rates] <;> nlinarith

theorem positiveCusp49_jacobian_values :
    positiveCusp49.toNetwork.jacobian positiveCusp49Rates unitState 0 0 = (30 : ℝ) * positiveCusp49Root + (-6 : ℝ) * 1 ∧
    positiveCusp49.toNetwork.jacobian positiveCusp49Rates unitState 0 1 = (-8 : ℝ) * positiveCusp49Root + (2 : ℝ) * 1 ∧
    positiveCusp49.toNetwork.jacobian positiveCusp49Rates unitState 1 0 = (-8 : ℝ) * positiveCusp49Root + (2 : ℝ) * 1 ∧
    positiveCusp49.toNetwork.jacobian positiveCusp49Rates unitState 1 1 = (-6 : ℝ) * positiveCusp49Root := by
  norm_num [positiveCusp49, positiveCusp49Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp49_Bqq_values :
    positiveCusp49.toNetwork.hessianApply positiveCusp49Rates unitState
        positiveCusp49RightKernel positiveCusp49RightKernel 0 = ((445632 : ℝ) / 3721) * positiveCusp49Root + ((-86496 : ℝ) / 3721) * 1 ∧
    positiveCusp49.toNetwork.hessianApply positiveCusp49Rates unitState
        positiveCusp49RightKernel positiveCusp49RightKernel 1 = ((-172320 : ℝ) / 3721) * positiveCusp49Root + ((33216 : ℝ) / 3721) * 1 := by
  rcases positiveCusp49Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp49, positiveCusp49Rates, positiveCusp49RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp49_Bqh_values :
    positiveCusp49.toNetwork.hessianApply positiveCusp49Rates unitState
        positiveCusp49RightKernel positiveCusp49Center 0 = ((-40898816 : ℝ) / 226981) * positiveCusp49Root + ((7946048 : ℝ) / 226981) * 1 ∧
    positiveCusp49.toNetwork.hessianApply positiveCusp49Rates unitState
        positiveCusp49RightKernel positiveCusp49Center 1 = ((23049984 : ℝ) / 226981) * positiveCusp49Root + ((-4476096 : ℝ) / 226981) * 1 := by
  rcases positiveCusp49Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp49, positiveCusp49Rates, positiveCusp49RightKernel,
    positiveCusp49Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp49_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp49.toNetwork positiveCusp49Rates
      positiveCusp49RightKernel positiveCusp49LeftKernel positiveCusp49Center 1 2).unfoldingMatrix =
      ((-244 : ℝ) / 3) * positiveCusp49Root + ((185 : ℝ) / 27) * 1 := by
  rcases positiveCusp49Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp49, positiveCusp49Rates, positiveCusp49RightKernel, positiveCusp49LeftKernel,
      positiveCusp49Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp49_cubic_value :
    dot positiveCusp49LeftKernel (positiveCusp49.toNetwork.hessianApply positiveCusp49Rates unitState
      positiveCusp49RightKernel positiveCusp49Center) = ((30368 : ℝ) / 3721) * positiveCusp49Root + ((-5920 : ℝ) / 3721) * 1 := by
  rcases positiveCusp49Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp49_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp49LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp49_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp49.toNetwork := by
  rcases positiveCusp49Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp49Root_lower
  have hu := positiveCusp49Root_upper
  have hs : 0 ≤ positiveCusp49Root ^ 2 := sq_nonneg positiveCusp49Root
  rcases positiveCusp49_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp49_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp49_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp49.toNetwork positiveCusp49Rates
    positiveCusp49RightKernel positiveCusp49LeftKernel positiveCusp49Center 1 2
  · exact positiveCusp49Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp49, positiveCusp49Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp49RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp49LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp49LeftKernel, positiveCusp49RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp49LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp49Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp49LeftKernel, positiveCusp49Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp49_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp49_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
