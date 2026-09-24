import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp46Polynomial (t : ℝ) : ℝ := (3859 : ℝ) * t ^ 3 + (-2202 : ℝ) * t ^ 2 + (300 : ℝ) * t + (-8 : ℝ) * 1

private theorem positiveCusp46Root_exists :
    ∃ t : ℝ, ((614 : ℝ) / 17443) < t ∧ t < ((455 : ℝ) / 12926) ∧ positiveCusp46Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp46Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp46Polynomial]
    fun_prop
  have hab : ((614 : ℝ) / 17443) ≤ ((455 : ℝ) / 12926) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((614 : ℝ) / 17443)) (f ((455 : ℝ) / 12926)) := by
    constructor <;> norm_num [f, positiveCusp46Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((614 : ℝ) / 17443) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp46Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((455 : ℝ) / 12926) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp46Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp46Root : ℝ := Classical.choose positiveCusp46Root_exists

theorem positiveCusp46Root_lower : ((614 : ℝ) / 17443) < positiveCusp46Root :=
  (Classical.choose_spec positiveCusp46Root_exists).1

theorem positiveCusp46Root_upper : positiveCusp46Root < ((455 : ℝ) / 12926) :=
  (Classical.choose_spec positiveCusp46Root_exists).2.1

theorem positiveCusp46Root_equation : (3859 : ℝ) * positiveCusp46Root ^ 3 + (-2202 : ℝ) * positiveCusp46Root ^ 2 + (300 : ℝ) * positiveCusp46Root + (-8 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp46Root_exists).2.2


theorem positiveCusp46Root_power_relations :
    let t := positiveCusp46Root
    ((3859 : ℝ) * t ^ 3 + (-2202 : ℝ) * t ^ 2 + (300 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((3859 : ℝ) * t ^ 3 + (-2202 : ℝ) * t ^ 2 + (300 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((3859 : ℝ) * t ^ 3 + (-2202 : ℝ) * t ^ 2 + (300 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((3859 : ℝ) * t ^ 3 + (-2202 : ℝ) * t ^ 2 + (300 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((3859 : ℝ) * t ^ 3 + (-2202 : ℝ) * t ^ 2 + (300 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((3859 : ℝ) * t ^ 3 + (-2202 : ℝ) * t ^ 2 + (300 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((3859 : ℝ) * t ^ 3 + (-2202 : ℝ) * t ^ 2 + (300 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((3859 : ℝ) * t ^ 3 + (-2202 : ℝ) * t ^ 2 + (300 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((3859 : ℝ) * t ^ 3 + (-2202 : ℝ) * t ^ 2 + (300 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp46Root_equation

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

def positiveCusp46 : CodedBimolNetwork where
  reaction := ![(.x, .xy), (.y, .xx), (.xx, .zero), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp46Rates : Fin 5 → ℝ :=
  let t := positiveCusp46Root
  ![((19295 : ℝ) / 788) * t ^ 2 + ((-1905 : ℝ) / 197) * t + ((79 : ℝ) / 197) * 1,
    ((-3859 : ℝ) / 788) * t ^ 2 + ((184 : ℝ) / 197) * t + ((63 : ℝ) / 197) * 1,
    ((3859 : ℝ) / 394) * t ^ 2 + ((-959 : ℝ) / 197) * t + ((71 : ℝ) / 197) * 1,
    ((-11577 : ℝ) / 394) * t ^ 2 + ((2483 : ℝ) / 197) * t + ((-16 : ℝ) / 197) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp46RightKernel : Species → ℝ :=
  let t := positiveCusp46Root
  ![((3859 : ℝ) / 197) * t ^ 2 + ((-1721 : ℝ) / 197) * t + ((142 : ℝ) / 197) * 1,
    ((3859 : ℝ) / 394) * t ^ 2 + ((-1353 : ℝ) / 197) * t + ((268 : ℝ) / 197) * 1]

noncomputable def positiveCusp46LeftKernel : Species → ℝ :=
  let t := positiveCusp46Root
  ![((-16250249 : ℝ) / 195424) * t ^ 2 + ((271198 : ℝ) / 6107) * t + ((-57393 : ℝ) / 48856) * 1,
    ((-63932053 : ℝ) / 781696) * t ^ 2 + ((6683175 : ℝ) / 195424) * t + ((-64207 : ℝ) / 195424) * 1]

noncomputable def positiveCusp46Center : Species → ℝ :=
  let t := positiveCusp46Root
  ![((-251414 : ℝ) / 6107) * t ^ 2 + ((109880 : ℝ) / 6107) * t + ((-5384 : ℝ) / 6107) * 1,
    ((271468 : ℝ) / 6107) * t ^ 2 + ((-114952 : ℝ) / 6107) * t + ((4384 : ℝ) / 6107) * 1]

theorem positiveCusp46Rates_positive : PositiveVector positiveCusp46Rates := by
  have hl := positiveCusp46Root_lower
  have hu := positiveCusp46Root_upper
  have hs : 0 ≤ positiveCusp46Root ^ 2 := sq_nonneg positiveCusp46Root
  intro k
  fin_cases k <;> simp [positiveCusp46Rates] <;> nlinarith

theorem positiveCusp46_jacobian_values :
    positiveCusp46.toNetwork.jacobian positiveCusp46Rates unitState 0 0 = ((-3859 : ℝ) / 394) * positiveCusp46Root ^ 2 + ((1353 : ℝ) / 197) * positiveCusp46Root + ((-268 : ℝ) / 197) * 1 ∧
    positiveCusp46.toNetwork.jacobian positiveCusp46Rates unitState 0 1 = ((3859 : ℝ) / 197) * positiveCusp46Root ^ 2 + ((-1721 : ℝ) / 197) * positiveCusp46Root + ((142 : ℝ) / 197) * 1 ∧
    positiveCusp46.toNetwork.jacobian positiveCusp46Rates unitState 1 0 = ((-3859 : ℝ) / 788) * positiveCusp46Root ^ 2 + ((578 : ℝ) / 197) * positiveCusp46Root + ((63 : ℝ) / 197) * 1 ∧
    positiveCusp46.toNetwork.jacobian positiveCusp46Rates unitState 1 1 = ((-19295 : ℝ) / 788) * positiveCusp46Root ^ 2 + ((1511 : ℝ) / 197) * positiveCusp46Root + ((-79 : ℝ) / 197) * 1 := by
  norm_num [positiveCusp46, positiveCusp46Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp46_Bqq_values :
    positiveCusp46.toNetwork.hessianApply positiveCusp46Rates unitState
        positiveCusp46RightKernel positiveCusp46RightKernel 0 = ((-15693560 : ℝ) / 760223) * positiveCusp46Root ^ 2 + ((7381280 : ℝ) / 760223) * positiveCusp46Root + ((-534368 : ℝ) / 760223) * 1 ∧
    positiveCusp46.toNetwork.hessianApply positiveCusp46Rates unitState
        positiveCusp46RightKernel positiveCusp46RightKernel 1 = ((13154176 : ℝ) / 760223) * positiveCusp46Root ^ 2 + ((-5798416 : ℝ) / 760223) * positiveCusp46Root + ((296224 : ℝ) / 760223) * 1 := by
  rcases positiveCusp46Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp46, positiveCusp46Rates, positiveCusp46RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp46_Bqh_values :
    positiveCusp46.toNetwork.hessianApply positiveCusp46Rates unitState
        positiveCusp46RightKernel positiveCusp46Center 0 = ((4034982693408 : ℝ) / 90944717267) * positiveCusp46Root ^ 2 + ((-1733232831552 : ℝ) / 90944717267) * positiveCusp46Root + ((74997007872 : ℝ) / 90944717267) * 1 ∧
    positiveCusp46.toNetwork.hessianApply positiveCusp46Rates unitState
        positiveCusp46RightKernel positiveCusp46Center 1 = ((-4132005839616 : ℝ) / 90944717267) * positiveCusp46Root ^ 2 + ((1748352216768 : ℝ) / 90944717267) * positiveCusp46Root + ((-66623711616 : ℝ) / 90944717267) * 1 := by
  rcases positiveCusp46Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp46, positiveCusp46Rates, positiveCusp46RightKernel,
    positiveCusp46Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp46_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp46.toNetwork positiveCusp46Rates
      positiveCusp46RightKernel positiveCusp46LeftKernel positiveCusp46Center 0 4).unfoldingMatrix =
      ((6622680735 : ℝ) / 24232576) * positiveCusp46Root ^ 2 + ((-654557821 : ℝ) / 6058144) * positiveCusp46Root + ((10193501 : ℝ) / 6058144) * 1 := by
  rcases positiveCusp46Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp46, positiveCusp46Rates, positiveCusp46RightKernel, positiveCusp46LeftKernel,
      positiveCusp46Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp46_cubic_value :
    dot positiveCusp46LeftKernel (positiveCusp46.toNetwork.hessianApply positiveCusp46Rates unitState
      positiveCusp46RightKernel positiveCusp46Center) = ((391543488 : ℝ) / 23566913) * positiveCusp46Root ^ 2 + ((-160975200 : ℝ) / 23566913) * positiveCusp46Root + ((4539648 : ℝ) / 23566913) * 1 := by
  rcases positiveCusp46Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp46_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp46LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp46_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp46.toNetwork := by
  rcases positiveCusp46Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp46Root_lower
  have hu := positiveCusp46Root_upper
  have hs : 0 ≤ positiveCusp46Root ^ 2 := sq_nonneg positiveCusp46Root
  rcases positiveCusp46_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp46_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp46_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp46.toNetwork positiveCusp46Rates
    positiveCusp46RightKernel positiveCusp46LeftKernel positiveCusp46Center 0 4
  · exact positiveCusp46Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp46, positiveCusp46Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp46RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp46LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp46LeftKernel, positiveCusp46RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp46LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp46Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp46LeftKernel, positiveCusp46Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp46_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp46_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
