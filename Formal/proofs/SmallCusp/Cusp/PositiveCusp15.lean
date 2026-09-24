import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp15Polynomial (t : ℝ) : ℝ := (1051 : ℝ) * t ^ 2 + (216 : ℝ) * t + (-12 : ℝ) * 1

private theorem positiveCusp15Root_exists :
    ∃ t : ℝ, ((686 : ℝ) / 15081) < t ∧ t < ((873 : ℝ) / 19192) ∧ positiveCusp15Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp15Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp15Polynomial]
    fun_prop
  have hab : ((686 : ℝ) / 15081) ≤ ((873 : ℝ) / 19192) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((686 : ℝ) / 15081)) (f ((873 : ℝ) / 19192)) := by
    constructor <;> norm_num [f, positiveCusp15Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((686 : ℝ) / 15081) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp15Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((873 : ℝ) / 19192) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp15Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp15Root : ℝ := Classical.choose positiveCusp15Root_exists

theorem positiveCusp15Root_lower : ((686 : ℝ) / 15081) < positiveCusp15Root :=
  (Classical.choose_spec positiveCusp15Root_exists).1

theorem positiveCusp15Root_upper : positiveCusp15Root < ((873 : ℝ) / 19192) :=
  (Classical.choose_spec positiveCusp15Root_exists).2.1

theorem positiveCusp15Root_equation : (1051 : ℝ) * positiveCusp15Root ^ 2 + (216 : ℝ) * positiveCusp15Root + (-12 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp15Root_exists).2.2


theorem positiveCusp15Root_power_relations :
    let t := positiveCusp15Root
    ((1051 : ℝ) * t ^ 2 + (216 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((1051 : ℝ) * t ^ 2 + (216 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((1051 : ℝ) * t ^ 2 + (216 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((1051 : ℝ) * t ^ 2 + (216 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((1051 : ℝ) * t ^ 2 + (216 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((1051 : ℝ) * t ^ 2 + (216 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((1051 : ℝ) * t ^ 2 + (216 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((1051 : ℝ) * t ^ 2 + (216 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((1051 : ℝ) * t ^ 2 + (216 : ℝ) * t + (-12 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp15Root_equation

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

def positiveCusp15 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .y), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp15Rates : Fin 5 → ℝ :=
  let t := positiveCusp15Root
  ![((-19 : ℝ) / 51) * t + ((4 : ℝ) / 51) * 1,
    ((-3 : ℝ) / 17) * t + ((6 : ℝ) / 17) * 1,
    ((-79 : ℝ) / 51) * t + ((22 : ℝ) / 51) * 1,
    (1 : ℝ) * t,
    ((56 : ℝ) / 51) * t + ((7 : ℝ) / 51) * 1]

noncomputable def positiveCusp15RightKernel : Species → ℝ :=
  let t := positiveCusp15Root
  ![((224 : ℝ) / 51) * t + ((28 : ℝ) / 51) * 1,
    ((65 : ℝ) / 17) * t + ((6 : ℝ) / 17) * 1]

noncomputable def positiveCusp15LeftKernel : Species → ℝ :=
  let t := positiveCusp15Root
  ![((-22071 : ℝ) / 12784) * t + ((44031 : ℝ) / 44744) * 1,
    ((15765 : ℝ) / 1316) * t + ((87 : ℝ) / 1316) * 1]

noncomputable def positiveCusp15Center : Species → ℝ :=
  let t := positiveCusp15Root
  ![((184828 : ℝ) / 148191) * t + ((392 : ℝ) / 49397) * 1,
    ((435260 : ℝ) / 2519247) * t + ((-87080 : ℝ) / 839749) * 1]

theorem positiveCusp15Rates_positive : PositiveVector positiveCusp15Rates := by
  have hl := positiveCusp15Root_lower
  have hu := positiveCusp15Root_upper
  have hs : 0 ≤ positiveCusp15Root ^ 2 := sq_nonneg positiveCusp15Root
  intro k
  fin_cases k <;> simp [positiveCusp15Rates] <;> nlinarith

theorem positiveCusp15_jacobian_values :
    positiveCusp15.toNetwork.jacobian positiveCusp15Rates unitState 0 0 = ((-65 : ℝ) / 17) * positiveCusp15Root + ((-6 : ℝ) / 17) * 1 ∧
    positiveCusp15.toNetwork.jacobian positiveCusp15Rates unitState 0 1 = ((224 : ℝ) / 51) * positiveCusp15Root + ((28 : ℝ) / 51) * 1 ∧
    positiveCusp15.toNetwork.jacobian positiveCusp15Rates unitState 1 0 = ((28 : ℝ) / 17) * positiveCusp15Root + ((12 : ℝ) / 17) * 1 ∧
    positiveCusp15.toNetwork.jacobian positiveCusp15Rates unitState 1 1 = ((-145 : ℝ) / 51) * positiveCusp15Root + ((-50 : ℝ) / 51) * 1 := by
  norm_num [positiveCusp15, positiveCusp15Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp15_Bqq_values :
    positiveCusp15.toNetwork.hessianApply positiveCusp15Rates unitState
        positiveCusp15RightKernel positiveCusp15RightKernel 0 = ((69776 : ℝ) / 9941409) * positiveCusp15Root + ((349664 : ℝ) / 3313803) * 1 ∧
    positiveCusp15.toNetwork.hessianApply positiveCusp15Rates unitState
        positiveCusp15RightKernel positiveCusp15RightKernel 1 = ((-117909680 : ℝ) / 169003953) * positiveCusp15Root + ((-7048160 : ℝ) / 56334651) * 1 := by
  rcases positiveCusp15Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp15, positiveCusp15Rates, positiveCusp15RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp15_Bqh_values :
    positiveCusp15.toNetwork.hessianApply positiveCusp15Rates unitState
        positiveCusp15RightKernel positiveCusp15Center 0 = ((-1565347047488 : ℝ) / 2782762755447) * positiveCusp15Root + ((-19510630272 : ℝ) / 927587585149) * 1 ∧
    positiveCusp15.toNetwork.hessianApply positiveCusp15Rates unitState
        positiveCusp15RightKernel positiveCusp15Center 1 = ((242781524608 : ℝ) / 927587585149) * positiveCusp15Root + ((84345818368 : ℝ) / 2782762755447) * 1 := by
  rcases positiveCusp15Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp15, positiveCusp15Rates, positiveCusp15RightKernel,
    positiveCusp15Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp15_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp15.toNetwork positiveCusp15Rates
      positiveCusp15RightKernel positiveCusp15LeftKernel positiveCusp15Center 0 3).unfoldingMatrix =
      ((-10830555 : ℝ) / 300424) * positiveCusp15Root + ((13095 : ℝ) / 1051484) * 1 := by
  rcases positiveCusp15Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp15, positiveCusp15Rates, positiveCusp15RightKernel, positiveCusp15LeftKernel,
      positiveCusp15Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp15_cubic_value :
    dot positiveCusp15LeftKernel (positiveCusp15.toNetwork.hessianApply positiveCusp15Rates unitState
      positiveCusp15RightKernel positiveCusp15Center) = ((-865646544 : ℝ) / 882576199) * positiveCusp15Root + ((24882592 : ℝ) / 882576199) * 1 := by
  rcases positiveCusp15Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp15_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp15LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp15_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp15.toNetwork := by
  rcases positiveCusp15Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp15Root_lower
  have hu := positiveCusp15Root_upper
  have hs : 0 ≤ positiveCusp15Root ^ 2 := sq_nonneg positiveCusp15Root
  rcases positiveCusp15_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp15_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp15_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp15.toNetwork positiveCusp15Rates
    positiveCusp15RightKernel positiveCusp15LeftKernel positiveCusp15Center 0 3
  · exact positiveCusp15Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp15, positiveCusp15Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp15RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp15LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp15LeftKernel, positiveCusp15RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp15LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp15Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp15LeftKernel, positiveCusp15Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp15_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp15_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
