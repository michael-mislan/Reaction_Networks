import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp29Polynomial (t : ℝ) : ℝ := (13931 : ℝ) * t ^ 3 + (-8331 : ℝ) * t ^ 2 + (825 : ℝ) * t + (-17 : ℝ) * 1

private theorem positiveCusp29Root_exists :
    ∃ t : ℝ, ((251 : ℝ) / 8862) < t ∧ t < ((414 : ℝ) / 14617) ∧ positiveCusp29Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp29Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp29Polynomial]
    fun_prop
  have hab : ((251 : ℝ) / 8862) ≤ ((414 : ℝ) / 14617) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((251 : ℝ) / 8862)) (f ((414 : ℝ) / 14617)) := by
    constructor <;> norm_num [f, positiveCusp29Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((251 : ℝ) / 8862) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp29Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((414 : ℝ) / 14617) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp29Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp29Root : ℝ := Classical.choose positiveCusp29Root_exists

theorem positiveCusp29Root_lower : ((251 : ℝ) / 8862) < positiveCusp29Root :=
  (Classical.choose_spec positiveCusp29Root_exists).1

theorem positiveCusp29Root_upper : positiveCusp29Root < ((414 : ℝ) / 14617) :=
  (Classical.choose_spec positiveCusp29Root_exists).2.1

theorem positiveCusp29Root_equation : (13931 : ℝ) * positiveCusp29Root ^ 3 + (-8331 : ℝ) * positiveCusp29Root ^ 2 + (825 : ℝ) * positiveCusp29Root + (-17 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp29Root_exists).2.2


theorem positiveCusp29Root_power_relations :
    let t := positiveCusp29Root
    ((13931 : ℝ) * t ^ 3 + (-8331 : ℝ) * t ^ 2 + (825 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((13931 : ℝ) * t ^ 3 + (-8331 : ℝ) * t ^ 2 + (825 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((13931 : ℝ) * t ^ 3 + (-8331 : ℝ) * t ^ 2 + (825 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((13931 : ℝ) * t ^ 3 + (-8331 : ℝ) * t ^ 2 + (825 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((13931 : ℝ) * t ^ 3 + (-8331 : ℝ) * t ^ 2 + (825 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((13931 : ℝ) * t ^ 3 + (-8331 : ℝ) * t ^ 2 + (825 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((13931 : ℝ) * t ^ 3 + (-8331 : ℝ) * t ^ 2 + (825 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((13931 : ℝ) * t ^ 3 + (-8331 : ℝ) * t ^ 2 + (825 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((13931 : ℝ) * t ^ 3 + (-8331 : ℝ) * t ^ 2 + (825 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp29Root_equation

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

def positiveCusp29 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp29Rates : Fin 5 → ℝ :=
  let t := positiveCusp29Root
  ![((13931 : ℝ) / 912) * t ^ 2 + ((-4481 : ℝ) / 456) * t + ((515 : ℝ) / 912) * 1,
    ((-13931 : ℝ) / 456) * t ^ 2 + ((3797 : ℝ) / 228) * t + ((-59 : ℝ) / 456) * 1,
    ((13931 : ℝ) / 608) * t ^ 2 + ((-3417 : ℝ) / 304) * t + ((211 : ℝ) / 608) * 1,
    ((-13931 : ℝ) / 1824) * t ^ 2 + ((3113 : ℝ) / 912) * t + ((397 : ℝ) / 1824) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp29RightKernel : Species → ℝ :=
  let t := positiveCusp29Root
  ![((13931 : ℝ) / 1824) * t ^ 2 + ((535 : ℝ) / 912) * t + ((-397 : ℝ) / 1824) * 1,
    ((69655 : ℝ) / 1824) * t ^ 2 + ((-17389 : ℝ) / 912) * t + ((1663 : ℝ) / 1824) * 1]

noncomputable def positiveCusp29LeftKernel : Species → ℝ :=
  let t := positiveCusp29Root
  ![((64458737 : ℝ) / 554496) * t ^ 2 + ((-15505433 : ℝ) / 277248) * t + ((243581 : ℝ) / 554496) * 1,
    ((70560515 : ℝ) / 554496) * t ^ 2 + ((-18792677 : ℝ) / 277248) * t + ((2103683 : ℝ) / 554496) * 1]

noncomputable def positiveCusp29Center : Species → ℝ :=
  let t := positiveCusp29Root
  ![((2503 : ℝ) / 722) * t ^ 2 + ((-1253 : ℝ) / 361) * t + ((159 : ℝ) / 722) * 1,
    ((-1022 : ℝ) / 361) * t ^ 2 + ((804 : ℝ) / 361) * t + ((2 : ℝ) / 361) * 1]

theorem positiveCusp29Rates_positive : PositiveVector positiveCusp29Rates := by
  have hl := positiveCusp29Root_lower
  have hu := positiveCusp29Root_upper
  have hs : 0 ≤ positiveCusp29Root ^ 2 := sq_nonneg positiveCusp29Root
  intro k
  fin_cases k <;> simp [positiveCusp29Rates] <;> nlinarith

theorem positiveCusp29_jacobian_values :
    positiveCusp29.toNetwork.jacobian positiveCusp29Rates unitState 0 0 = ((-69655 : ℝ) / 1824) * positiveCusp29Root ^ 2 + ((17389 : ℝ) / 912) * positiveCusp29Root + ((-1663 : ℝ) / 1824) * 1 ∧
    positiveCusp29.toNetwork.jacobian positiveCusp29Rates unitState 0 1 = ((13931 : ℝ) / 1824) * positiveCusp29Root ^ 2 + ((535 : ℝ) / 912) * positiveCusp29Root + ((-397 : ℝ) / 1824) * 1 ∧
    positiveCusp29.toNetwork.jacobian positiveCusp29Rates unitState 1 0 = ((97517 : ℝ) / 1824) * positiveCusp29Root ^ 2 + ((-23615 : ℝ) / 912) * positiveCusp29Root + ((869 : ℝ) / 1824) * 1 ∧
    positiveCusp29.toNetwork.jacobian positiveCusp29Rates unitState 1 1 = ((-13931 : ℝ) / 608) * positiveCusp29Root ^ 2 + ((2809 : ℝ) / 304) * positiveCusp29Root + ((-211 : ℝ) / 608) * 1 := by
  norm_num [positiveCusp29, positiveCusp29Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp29_Bqq_values :
    positiveCusp29.toNetwork.hessianApply positiveCusp29Rates unitState
        positiveCusp29RightKernel positiveCusp29RightKernel 0 = ((-1649364 : ℝ) / 264689) * positiveCusp29Root ^ 2 + ((138872 : ℝ) / 264689) * positiveCusp29Root + ((14092 : ℝ) / 264689) * 1 ∧
    positiveCusp29.toNetwork.hessianApply positiveCusp29Rates unitState
        positiveCusp29RightKernel positiveCusp29RightKernel 1 = ((3021696 : ℝ) / 264689) * positiveCusp29Root ^ 2 + ((-1123072 : ℝ) / 264689) * positiveCusp29Root + ((38272 : ℝ) / 264689) * 1 := by
  rcases positiveCusp29Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp29, positiveCusp29Rates, positiveCusp29RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp29_Bqh_values :
    positiveCusp29.toNetwork.hessianApply positiveCusp29Rates unitState
        positiveCusp29RightKernel positiveCusp29Center 0 = ((456697987296 : ℝ) / 70060266721) * positiveCusp29Root ^ 2 + ((-83077723968 : ℝ) / 70060266721) * positiveCusp29Root + ((1554773472 : ℝ) / 70060266721) * 1 ∧
    positiveCusp29.toNetwork.hessianApply positiveCusp29Rates unitState
        positiveCusp29RightKernel positiveCusp29Center 1 = ((-512806862400 : ℝ) / 70060266721) * positiveCusp29Root ^ 2 + ((102866459520 : ℝ) / 70060266721) * positiveCusp29Root + ((-3678339648 : ℝ) / 70060266721) * 1 := by
  rcases positiveCusp29Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp29, positiveCusp29Rates, positiveCusp29RightKernel,
    positiveCusp29Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp29_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp29.toNetwork positiveCusp29Rates
      positiveCusp29RightKernel positiveCusp29LeftKernel positiveCusp29Center 2 4).unfoldingMatrix =
      ((-6084211009 : ℝ) / 5267712) * positiveCusp29Root ^ 2 + ((1675015627 : ℝ) / 2633856) * positiveCusp29Root + ((-205355449 : ℝ) / 5267712) * 1 := by
  rcases positiveCusp29Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp29, positiveCusp29Rates, positiveCusp29RightKernel, positiveCusp29LeftKernel,
      positiveCusp29Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp29_cubic_value :
    dot positiveCusp29LeftKernel (positiveCusp29.toNetwork.hessianApply positiveCusp29Rates unitState
      positiveCusp29RightKernel positiveCusp29Center) = ((-30409372 : ℝ) / 5029091) * positiveCusp29Root ^ 2 + ((13134056 : ℝ) / 5029091) * positiveCusp29Root + ((-481852 : ℝ) / 5029091) * 1 := by
  rcases positiveCusp29Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp29_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp29LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp29_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp29.toNetwork := by
  rcases positiveCusp29Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp29Root_lower
  have hu := positiveCusp29Root_upper
  have hs : 0 ≤ positiveCusp29Root ^ 2 := sq_nonneg positiveCusp29Root
  rcases positiveCusp29_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp29_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp29_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp29.toNetwork positiveCusp29Rates
    positiveCusp29RightKernel positiveCusp29LeftKernel positiveCusp29Center 2 4
  · exact positiveCusp29Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp29, positiveCusp29Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp29RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp29LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp29LeftKernel, positiveCusp29RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp29LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp29Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp29LeftKernel, positiveCusp29Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp29_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp29_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
