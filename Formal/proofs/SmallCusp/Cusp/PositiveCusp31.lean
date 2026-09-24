import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp31Polynomial (t : ℝ) : ℝ := (226 : ℝ) * t ^ 3 + (54 : ℝ) * t ^ 2 + (-45 : ℝ) * t + (3 : ℝ) * 1

private theorem positiveCusp31Root_exists :
    ∃ t : ℝ, ((2612 : ℝ) / 34491) < t ∧ t < ((2695 : ℝ) / 35587) ∧ positiveCusp31Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ -(positiveCusp31Polynomial t)
  have hf : Continuous f := by
    dsimp [f, positiveCusp31Polynomial]
    fun_prop
  have hab : ((2612 : ℝ) / 34491) ≤ ((2695 : ℝ) / 35587) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((2612 : ℝ) / 34491)) (f ((2695 : ℝ) / 35587)) := by
    constructor <;> norm_num [f, positiveCusp31Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((2612 : ℝ) / 34491) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp31Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((2695 : ℝ) / 35587) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp31Polynomial] at hft
  · dsimp [f, positiveCusp31Polynomial] at hft ⊢
    nlinarith [hft]

noncomputable def positiveCusp31Root : ℝ := Classical.choose positiveCusp31Root_exists

theorem positiveCusp31Root_lower : ((2612 : ℝ) / 34491) < positiveCusp31Root :=
  (Classical.choose_spec positiveCusp31Root_exists).1

theorem positiveCusp31Root_upper : positiveCusp31Root < ((2695 : ℝ) / 35587) :=
  (Classical.choose_spec positiveCusp31Root_exists).2.1

theorem positiveCusp31Root_equation : (226 : ℝ) * positiveCusp31Root ^ 3 + (54 : ℝ) * positiveCusp31Root ^ 2 + (-45 : ℝ) * positiveCusp31Root + (3 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp31Root_exists).2.2


theorem positiveCusp31Root_power_relations :
    let t := positiveCusp31Root
    ((226 : ℝ) * t ^ 3 + (54 : ℝ) * t ^ 2 + (-45 : ℝ) * t + (3 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((226 : ℝ) * t ^ 3 + (54 : ℝ) * t ^ 2 + (-45 : ℝ) * t + (3 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((226 : ℝ) * t ^ 3 + (54 : ℝ) * t ^ 2 + (-45 : ℝ) * t + (3 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((226 : ℝ) * t ^ 3 + (54 : ℝ) * t ^ 2 + (-45 : ℝ) * t + (3 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((226 : ℝ) * t ^ 3 + (54 : ℝ) * t ^ 2 + (-45 : ℝ) * t + (3 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((226 : ℝ) * t ^ 3 + (54 : ℝ) * t ^ 2 + (-45 : ℝ) * t + (3 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((226 : ℝ) * t ^ 3 + (54 : ℝ) * t ^ 2 + (-45 : ℝ) * t + (3 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((226 : ℝ) * t ^ 3 + (54 : ℝ) * t ^ 2 + (-45 : ℝ) * t + (3 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((226 : ℝ) * t ^ 3 + (54 : ℝ) * t ^ 2 + (-45 : ℝ) * t + (3 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp31Root_equation

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

def positiveCusp31 : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .zero), (.y, .xx), (.xx, .xy), (.xy, .x)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp31Rates : Fin 5 → ℝ :=
  let t := positiveCusp31Root
  ![((339 : ℝ) / 151) * t ^ 2 + ((145 : ℝ) / 151) * t + ((-17 : ℝ) / 302) * 1,
    ((452 : ℝ) / 151) * t ^ 2 + ((-8 : ℝ) / 151) * t + ((39 : ℝ) / 151) * 1,
    ((-226 : ℝ) / 151) * t ^ 2 + ((-147 : ℝ) / 151) * t + ((56 : ℝ) / 151) * 1,
    ((-565 : ℝ) / 151) * t ^ 2 + ((-141 : ℝ) / 151) * t + ((129 : ℝ) / 302) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp31RightKernel : Species → ℝ :=
  let t := positiveCusp31Root
  ![((-452 : ℝ) / 151) * t ^ 2 + ((-294 : ℝ) / 151) * t + ((112 : ℝ) / 151) * 1,
    ((-678 : ℝ) / 151) * t ^ 2 + ((-290 : ℝ) / 151) * t + ((168 : ℝ) / 151) * 1]

noncomputable def positiveCusp31LeftKernel : Species → ℝ :=
  let t := positiveCusp31Root
  ![((-47912 : ℝ) / 1057) * t ^ 2 + ((-3395 : ℝ) / 151) * t + ((5171 : ℝ) / 2114) * 1,
    ((11187 : ℝ) / 1057) * t ^ 2 + ((511 : ℝ) / 151) * t + ((949 : ℝ) / 2114) * 1]

noncomputable def positiveCusp31Center : Species → ℝ :=
  let t := positiveCusp31Root
  ![((3280 : ℝ) / 1057) * t ^ 2 + ((-48 : ℝ) / 151) * t + ((-174 : ℝ) / 1057) * 1,
    ((-236 : ℝ) / 1057) * t ^ 2 + ((-54 : ℝ) / 151) * t + ((144 : ℝ) / 1057) * 1]

theorem positiveCusp31Rates_positive : PositiveVector positiveCusp31Rates := by
  have hl := positiveCusp31Root_lower
  have hu := positiveCusp31Root_upper
  have hs : 0 ≤ positiveCusp31Root ^ 2 := sq_nonneg positiveCusp31Root
  intro k
  fin_cases k <;> simp [positiveCusp31Rates] <;> nlinarith

theorem positiveCusp31_jacobian_values :
    positiveCusp31.toNetwork.jacobian positiveCusp31Rates unitState 0 0 = ((678 : ℝ) / 151) * positiveCusp31Root ^ 2 + ((290 : ℝ) / 151) * positiveCusp31Root + ((-168 : ℝ) / 151) * 1 ∧
    positiveCusp31.toNetwork.jacobian positiveCusp31Rates unitState 0 1 = ((-452 : ℝ) / 151) * positiveCusp31Root ^ 2 + ((-294 : ℝ) / 151) * positiveCusp31Root + ((112 : ℝ) / 151) * 1 ∧
    positiveCusp31.toNetwork.jacobian positiveCusp31Rates unitState 1 0 = ((-1130 : ℝ) / 151) * positiveCusp31Root ^ 2 + ((-433 : ℝ) / 151) * positiveCusp31Root + ((129 : ℝ) / 151) * 1 ∧
    positiveCusp31.toNetwork.jacobian positiveCusp31Rates unitState 1 1 = ((226 : ℝ) / 151) * positiveCusp31Root ^ 2 + ((-4 : ℝ) / 151) * positiveCusp31Root + ((-56 : ℝ) / 151) * 1 := by
  norm_num [positiveCusp31, positiveCusp31Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp31_Bqq_values :
    positiveCusp31.toNetwork.hessianApply positiveCusp31Rates unitState
        positiveCusp31RightKernel positiveCusp31RightKernel 0 = ((40624 : ℝ) / 17063) * positiveCusp31Root ^ 2 + ((3060 : ℝ) / 17063) * positiveCusp31Root + ((-4272 : ℝ) / 17063) * 1 ∧
    positiveCusp31.toNetwork.hessianApply positiveCusp31Rates unitState
        positiveCusp31RightKernel positiveCusp31RightKernel 1 = ((-12620 : ℝ) / 17063) * positiveCusp31Root ^ 2 + ((-6132 : ℝ) / 17063) * positiveCusp31Root + ((2940 : ℝ) / 17063) * 1 := by
  rcases positiveCusp31Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp31, positiveCusp31Rates, positiveCusp31RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp31_Bqh_values :
    positiveCusp31.toNetwork.hessianApply positiveCusp31Rates unitState
        positiveCusp31RightKernel positiveCusp31Center 0 = ((9854640 : ℝ) / 13496833) * positiveCusp31Root ^ 2 + ((-1110408 : ℝ) / 1928119) * positiveCusp31Root + ((1423908 : ℝ) / 13496833) * 1 ∧
    positiveCusp31.toNetwork.hessianApply positiveCusp31Rates unitState
        positiveCusp31RightKernel positiveCusp31Center 1 = ((2307948 : ℝ) / 13496833) * positiveCusp31Root ^ 2 + ((408636 : ℝ) / 1928119) * positiveCusp31Root + ((-1020840 : ℝ) / 13496833) * 1 := by
  rcases positiveCusp31Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp31, positiveCusp31Rates, positiveCusp31RightKernel,
    positiveCusp31Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp31_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp31.toNetwork positiveCusp31Rates
      positiveCusp31RightKernel positiveCusp31LeftKernel positiveCusp31Center 0 4).unfoldingMatrix =
      ((55483 : ℝ) / 7399) * positiveCusp31Root ^ 2 + ((21787 : ℝ) / 2114) * positiveCusp31Root + ((-33687 : ℝ) / 14798) * 1 := by
  rcases positiveCusp31Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp31, positiveCusp31Rates, positiveCusp31RightKernel, positiveCusp31LeftKernel,
      positiveCusp31Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp31_cubic_value :
    dot positiveCusp31LeftKernel (positiveCusp31.toNetwork.hessianApply positiveCusp31Rates unitState
      positiveCusp31RightKernel positiveCusp31Center) = ((-126528 : ℝ) / 119441) * positiveCusp31Root ^ 2 + ((7734 : ℝ) / 17063) * positiveCusp31Root + ((-4920 : ℝ) / 119441) * 1 := by
  rcases positiveCusp31Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp31_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp31LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp31_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp31.toNetwork := by
  rcases positiveCusp31Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp31Root_lower
  have hu := positiveCusp31Root_upper
  have hs : 0 ≤ positiveCusp31Root ^ 2 := sq_nonneg positiveCusp31Root
  rcases positiveCusp31_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp31_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp31_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp31.toNetwork positiveCusp31Rates
    positiveCusp31RightKernel positiveCusp31LeftKernel positiveCusp31Center 0 4
  · exact positiveCusp31Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp31, positiveCusp31Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp31RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp31LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp31LeftKernel, positiveCusp31RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp31LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp31Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp31LeftKernel, positiveCusp31Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp31_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp31_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
