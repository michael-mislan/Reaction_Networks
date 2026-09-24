import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp6Polynomial (t : ℝ) : ℝ := (121 : ℝ) * t ^ 3 + (-99 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1

private theorem positiveCusp6Root_exists :
    ∃ t : ℝ, ((2289 : ℝ) / 52439) < t ∧ t < ((2300 : ℝ) / 52691) ∧ positiveCusp6Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp6Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp6Polynomial]
    fun_prop
  have hab : ((2289 : ℝ) / 52439) ≤ ((2300 : ℝ) / 52691) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((2289 : ℝ) / 52439)) (f ((2300 : ℝ) / 52691)) := by
    constructor <;> norm_num [f, positiveCusp6Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((2289 : ℝ) / 52439) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp6Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((2300 : ℝ) / 52691) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp6Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp6Root : ℝ := Classical.choose positiveCusp6Root_exists

theorem positiveCusp6Root_lower : ((2289 : ℝ) / 52439) < positiveCusp6Root :=
  (Classical.choose_spec positiveCusp6Root_exists).1

theorem positiveCusp6Root_upper : positiveCusp6Root < ((2300 : ℝ) / 52691) :=
  (Classical.choose_spec positiveCusp6Root_exists).2.1

theorem positiveCusp6Root_equation : (121 : ℝ) * positiveCusp6Root ^ 3 + (-99 : ℝ) * positiveCusp6Root ^ 2 + (27 : ℝ) * positiveCusp6Root + (-1 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp6Root_exists).2.2


theorem positiveCusp6Root_power_relations :
    let t := positiveCusp6Root
    ((121 : ℝ) * t ^ 3 + (-99 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((121 : ℝ) * t ^ 3 + (-99 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((121 : ℝ) * t ^ 3 + (-99 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((121 : ℝ) * t ^ 3 + (-99 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((121 : ℝ) * t ^ 3 + (-99 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((121 : ℝ) * t ^ 3 + (-99 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((121 : ℝ) * t ^ 3 + (-99 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((121 : ℝ) * t ^ 3 + (-99 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((121 : ℝ) * t ^ 3 + (-99 : ℝ) * t ^ 2 + (27 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp6Root_equation

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

def positiveCusp6 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .y), (.y, .yy), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp6Rates : Fin 5 → ℝ :=
  let t := positiveCusp6Root
  ![((11 : ℝ) / 2) * t ^ 2 + (-4 : ℝ) * t + ((1 : ℝ) / 2) * 1,
    ((33 : ℝ) / 4) * t ^ 2 + ((-9 : ℝ) / 2) * t + ((1 : ℝ) / 4) * 1,
    (-11 : ℝ) * t ^ 2 + (7 : ℝ) * t,
    ((-11 : ℝ) / 4) * t ^ 2 + ((1 : ℝ) / 2) * t + ((1 : ℝ) / 4) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp6RightKernel : Species → ℝ :=
  let t := positiveCusp6Root
  ![((11 : ℝ) / 4) * t ^ 2 + ((-1 : ℝ) / 2) * t + ((-1 : ℝ) / 4) * 1,
    ((11 : ℝ) / 2) * t ^ 2 + (-4 : ℝ) * t + ((1 : ℝ) / 2) * 1]

noncomputable def positiveCusp6LeftKernel : Species → ℝ :=
  let t := positiveCusp6Root
  ![(-11 : ℝ) * t ^ 2 + ((3 : ℝ) / 4) * t + ((-53 : ℝ) / 44) * 1,
    ((11 : ℝ) / 4) * t ^ 2 + ((-31 : ℝ) / 4) * t + ((26 : ℝ) / 11) * 1]

noncomputable def positiveCusp6Center : Species → ℝ :=
  let t := positiveCusp6Root
  ![(-1 : ℝ) * t ^ 2 + ((2 : ℝ) / 11) * t + ((1 : ℝ) / 11) * 1,
    (3 : ℝ) * t ^ 2 + ((-10 : ℝ) / 11) * t + ((1 : ℝ) / 11) * 1]

theorem positiveCusp6Rates_positive : PositiveVector positiveCusp6Rates := by
  have hl := positiveCusp6Root_lower
  have hu := positiveCusp6Root_upper
  have hs : 0 ≤ positiveCusp6Root ^ 2 := sq_nonneg positiveCusp6Root
  intro k
  fin_cases k <;> simp [positiveCusp6Rates] <;> nlinarith

theorem positiveCusp6_jacobian_values :
    positiveCusp6.toNetwork.jacobian positiveCusp6Rates unitState 0 0 = ((-11 : ℝ) / 2) * positiveCusp6Root ^ 2 + (4 : ℝ) * positiveCusp6Root + ((-1 : ℝ) / 2) * 1 ∧
    positiveCusp6.toNetwork.jacobian positiveCusp6Rates unitState 0 1 = ((11 : ℝ) / 4) * positiveCusp6Root ^ 2 + ((-1 : ℝ) / 2) * positiveCusp6Root + ((-1 : ℝ) / 4) * 1 ∧
    positiveCusp6.toNetwork.jacobian positiveCusp6Rates unitState 1 0 = (11 : ℝ) * positiveCusp6Root ^ 2 + (-5 : ℝ) * positiveCusp6Root ∧
    positiveCusp6.toNetwork.jacobian positiveCusp6Rates unitState 1 1 = ((-33 : ℝ) / 4) * positiveCusp6Root ^ 2 + ((5 : ℝ) / 2) * positiveCusp6Root + ((-1 : ℝ) / 4) * 1 := by
  norm_num [positiveCusp6, positiveCusp6Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp6_Bqq_values :
    positiveCusp6.toNetwork.hessianApply positiveCusp6Rates unitState
        positiveCusp6RightKernel positiveCusp6RightKernel 0 = ((6 : ℝ) / 11) * positiveCusp6Root ^ 2 + ((-8 : ℝ) / 121) * positiveCusp6Root + ((6 : ℝ) / 121) * 1 ∧
    positiveCusp6.toNetwork.hessianApply positiveCusp6Rates unitState
        positiveCusp6RightKernel positiveCusp6RightKernel 1 = ((18 : ℝ) / 11) * positiveCusp6Root ^ 2 + ((-160 : ℝ) / 121) * positiveCusp6Root + ((10 : ℝ) / 121) * 1 := by
  rcases positiveCusp6Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp6, positiveCusp6Rates, positiveCusp6RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp6_Bqh_values :
    positiveCusp6.toNetwork.hessianApply positiveCusp6Rates unitState
        positiveCusp6RightKernel positiveCusp6Center 0 = ((-64 : ℝ) / 121) * positiveCusp6Root ^ 2 + ((256 : ℝ) / 1331) * positiveCusp6Root + ((-16 : ℝ) / 1331) * 1 ∧
    positiveCusp6.toNetwork.hessianApply positiveCusp6Rates unitState
        positiveCusp6RightKernel positiveCusp6Center 1 = ((248 : ℝ) / 121) * positiveCusp6Root ^ 2 + ((-912 : ℝ) / 1331) * positiveCusp6Root + ((24 : ℝ) / 1331) * 1 := by
  rcases positiveCusp6Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp6, positiveCusp6Rates, positiveCusp6RightKernel,
    positiveCusp6Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp6_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp6.toNetwork positiveCusp6Rates
      positiveCusp6RightKernel positiveCusp6LeftKernel positiveCusp6Center 1 4).unfoldingMatrix =
      ((-237 : ℝ) / 2) * positiveCusp6Root ^ 2 + ((830 : ℝ) / 11) * positiveCusp6Root + ((-3715 : ℝ) / 242) * 1 := by
  rcases positiveCusp6Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp6, positiveCusp6Rates, positiveCusp6RightKernel, positiveCusp6LeftKernel,
      positiveCusp6Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp6_cubic_value :
    dot positiveCusp6LeftKernel (positiveCusp6.toNetwork.hessianApply positiveCusp6Rates unitState
      positiveCusp6RightKernel positiveCusp6Center) = ((-4 : ℝ) / 11) * positiveCusp6Root ^ 2 + ((64 : ℝ) / 121) * positiveCusp6Root + ((-4 : ℝ) / 121) * 1 := by
  rcases positiveCusp6Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp6_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp6LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp6_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp6.toNetwork := by
  rcases positiveCusp6Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp6Root_lower
  have hu := positiveCusp6Root_upper
  have hs : 0 ≤ positiveCusp6Root ^ 2 := sq_nonneg positiveCusp6Root
  rcases positiveCusp6_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp6_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp6_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp6.toNetwork positiveCusp6Rates
    positiveCusp6RightKernel positiveCusp6LeftKernel positiveCusp6Center 1 4
  · exact positiveCusp6Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp6, positiveCusp6Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp6RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp6LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp6LeftKernel, positiveCusp6RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp6LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp6Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp6LeftKernel, positiveCusp6Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp6_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp6_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
