import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp48Polynomial (t : ℝ) : ℝ := (150 : ℝ) * t ^ 3 + (-102 : ℝ) * t ^ 2 + (24 : ℝ) * t + (-1 : ℝ) * 1

private theorem positiveCusp48Root_exists :
    ∃ t : ℝ, ((453 : ℝ) / 8635) < t ∧ t < ((631 : ℝ) / 12028) ∧ positiveCusp48Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp48Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp48Polynomial]
    fun_prop
  have hab : ((453 : ℝ) / 8635) ≤ ((631 : ℝ) / 12028) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((453 : ℝ) / 8635)) (f ((631 : ℝ) / 12028)) := by
    constructor <;> norm_num [f, positiveCusp48Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((453 : ℝ) / 8635) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp48Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((631 : ℝ) / 12028) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp48Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp48Root : ℝ := Classical.choose positiveCusp48Root_exists

theorem positiveCusp48Root_lower : ((453 : ℝ) / 8635) < positiveCusp48Root :=
  (Classical.choose_spec positiveCusp48Root_exists).1

theorem positiveCusp48Root_upper : positiveCusp48Root < ((631 : ℝ) / 12028) :=
  (Classical.choose_spec positiveCusp48Root_exists).2.1

theorem positiveCusp48Root_equation : (150 : ℝ) * positiveCusp48Root ^ 3 + (-102 : ℝ) * positiveCusp48Root ^ 2 + (24 : ℝ) * positiveCusp48Root + (-1 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp48Root_exists).2.2


theorem positiveCusp48Root_power_relations :
    let t := positiveCusp48Root
    ((150 : ℝ) * t ^ 3 + (-102 : ℝ) * t ^ 2 + (24 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((150 : ℝ) * t ^ 3 + (-102 : ℝ) * t ^ 2 + (24 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((150 : ℝ) * t ^ 3 + (-102 : ℝ) * t ^ 2 + (24 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((150 : ℝ) * t ^ 3 + (-102 : ℝ) * t ^ 2 + (24 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((150 : ℝ) * t ^ 3 + (-102 : ℝ) * t ^ 2 + (24 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((150 : ℝ) * t ^ 3 + (-102 : ℝ) * t ^ 2 + (24 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((150 : ℝ) * t ^ 3 + (-102 : ℝ) * t ^ 2 + (24 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((150 : ℝ) * t ^ 3 + (-102 : ℝ) * t ^ 2 + (24 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((150 : ℝ) * t ^ 3 + (-102 : ℝ) * t ^ 2 + (24 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp48Root_equation

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

def positiveCusp48 : CodedBimolNetwork where
  reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .yy), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp48Rates : Fin 5 → ℝ :=
  let t := positiveCusp48Root
  ![((750 : ℝ) / 71) * t ^ 2 + ((-346 : ℝ) / 71) * t + ((22 : ℝ) / 71) * 1,
    ((-150 : ℝ) / 71) * t ^ 2 + ((-16 : ℝ) / 71) * t + ((24 : ℝ) / 71) * 1,
    ((300 : ℝ) / 71) * t ^ 2 + ((-181 : ℝ) / 71) * t + ((23 : ℝ) / 71) * 1,
    ((-900 : ℝ) / 71) * t ^ 2 + ((472 : ℝ) / 71) * t + ((2 : ℝ) / 71) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp48RightKernel : Species → ℝ :=
  let t := positiveCusp48Root
  ![((600 : ℝ) / 71) * t ^ 2 + ((-220 : ℝ) / 71) * t + ((46 : ℝ) / 71) * 1,
    ((300 : ℝ) / 71) * t ^ 2 + ((-252 : ℝ) / 71) * t + ((94 : ℝ) / 71) * 1]

noncomputable def positiveCusp48LeftKernel : Species → ℝ :=
  let t := positiveCusp48Root
  ![((-16800 : ℝ) / 781) * t ^ 2 + ((8574 : ℝ) / 781) * t + ((-375 : ℝ) / 1562) * 1,
    ((-11100 : ℝ) / 781) * t ^ 2 + ((3573 : ℝ) / 781) * t + ((427 : ℝ) / 781) * 1]

noncomputable def positiveCusp48Center : Species → ℝ :=
  let t := positiveCusp48Root
  ![((-64 : ℝ) / 781) * t ^ 2 + ((-128 : ℝ) / 781) * t + ((-560 : ℝ) / 2343) * 1,
    ((368 : ℝ) / 781) * t ^ 2 + ((736 : ℝ) / 781) * t + ((32 : ℝ) / 781) * 1]

theorem positiveCusp48Rates_positive : PositiveVector positiveCusp48Rates := by
  have hl := positiveCusp48Root_lower
  have hu := positiveCusp48Root_upper
  have hs : 0 ≤ positiveCusp48Root ^ 2 := sq_nonneg positiveCusp48Root
  intro k
  fin_cases k <;> simp [positiveCusp48Rates] <;> nlinarith

theorem positiveCusp48_jacobian_values :
    positiveCusp48.toNetwork.jacobian positiveCusp48Rates unitState 0 0 = ((-300 : ℝ) / 71) * positiveCusp48Root ^ 2 + ((252 : ℝ) / 71) * positiveCusp48Root + ((-94 : ℝ) / 71) * 1 ∧
    positiveCusp48.toNetwork.jacobian positiveCusp48Rates unitState 0 1 = ((600 : ℝ) / 71) * positiveCusp48Root ^ 2 + ((-220 : ℝ) / 71) * positiveCusp48Root + ((46 : ℝ) / 71) * 1 ∧
    positiveCusp48.toNetwork.jacobian positiveCusp48Rates unitState 1 0 = ((-150 : ℝ) / 71) * positiveCusp48Root ^ 2 + ((126 : ℝ) / 71) * positiveCusp48Root + ((24 : ℝ) / 71) * 1 ∧
    positiveCusp48.toNetwork.jacobian positiveCusp48Rates unitState 1 1 = ((-750 : ℝ) / 71) * positiveCusp48Root ^ 2 + ((204 : ℝ) / 71) * positiveCusp48Root + ((-22 : ℝ) / 71) * 1 := by
  norm_num [positiveCusp48, positiveCusp48Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp48_Bqq_values :
    positiveCusp48.toNetwork.hessianApply positiveCusp48Rates unitState
        positiveCusp48RightKernel positiveCusp48RightKernel 0 = ((-7584 : ℝ) / 1775) * positiveCusp48Root ^ 2 + ((3008 : ℝ) / 1775) * positiveCusp48Root + ((-2176 : ℝ) / 5325) * 1 ∧
    positiveCusp48.toNetwork.hessianApply positiveCusp48Rates unitState
        positiveCusp48RightKernel positiveCusp48RightKernel 1 = ((8608 : ℝ) / 1775) * positiveCusp48Root ^ 2 + ((-2096 : ℝ) / 1775) * positiveCusp48Root + ((304 : ℝ) / 1775) * 1 := by
  rcases positiveCusp48Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp48, positiveCusp48Rates, positiveCusp48RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp48_Bqh_values :
    positiveCusp48.toNetwork.hessianApply positiveCusp48Rates unitState
        positiveCusp48RightKernel positiveCusp48Center 0 = ((-5495104 : ℝ) / 1464375) * positiveCusp48Root ^ 2 + ((1955648 : ℝ) / 1464375) * positiveCusp48Root + ((213248 : ℝ) / 1464375) * 1 ∧
    positiveCusp48.toNetwork.hessianApply positiveCusp48Rates unitState
        positiveCusp48RightKernel positiveCusp48Center 1 = ((1982144 : ℝ) / 488125) * positiveCusp48Root ^ 2 + ((-984128 : ℝ) / 488125) * positiveCusp48Root + ((-13184 : ℝ) / 1464375) * 1 := by
  rcases positiveCusp48Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp48, positiveCusp48Rates, positiveCusp48RightKernel,
    positiveCusp48Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp48_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp48.toNetwork positiveCusp48Rates
      positiveCusp48RightKernel positiveCusp48LeftKernel positiveCusp48Center 0 4).unfoldingMatrix =
      ((-6000 : ℝ) / 121) * positiveCusp48Root ^ 2 + ((2630 : ℝ) / 121) * positiveCusp48Root + ((-274 : ℝ) / 121) * 1 := by
  rcases positiveCusp48Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp48, positiveCusp48Rates, positiveCusp48RightKernel, positiveCusp48LeftKernel,
      positiveCusp48Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp48_cubic_value :
    dot positiveCusp48LeftKernel (positiveCusp48.toNetwork.hessianApply positiveCusp48Rates unitState
      positiveCusp48RightKernel positiveCusp48Center) = ((-56992 : ℝ) / 19525) * positiveCusp48Root ^ 2 + ((82912 : ℝ) / 58575) * positiveCusp48Root + ((-1696 : ℝ) / 19525) * 1 := by
  rcases positiveCusp48Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp48_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp48LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp48_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp48.toNetwork := by
  rcases positiveCusp48Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp48Root_lower
  have hu := positiveCusp48Root_upper
  have hs : 0 ≤ positiveCusp48Root ^ 2 := sq_nonneg positiveCusp48Root
  rcases positiveCusp48_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp48_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp48_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp48.toNetwork positiveCusp48Rates
    positiveCusp48RightKernel positiveCusp48LeftKernel positiveCusp48Center 0 4
  · exact positiveCusp48Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp48, positiveCusp48Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp48RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp48LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp48LeftKernel, positiveCusp48RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp48LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp48Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp48LeftKernel, positiveCusp48Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp48_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp48_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
