import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp25Polynomial (t : ℝ) : ℝ := (2971 : ℝ) * t ^ 3 + (-867 : ℝ) * t ^ 2 + (489 : ℝ) * t + (-25 : ℝ) * 1

private theorem positiveCusp25Root_exists :
    ∃ t : ℝ, ((7563 : ℝ) / 136135) < t ∧ t < ((7564 : ℝ) / 136153) ∧ positiveCusp25Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp25Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp25Polynomial]
    fun_prop
  have hab : ((7563 : ℝ) / 136135) ≤ ((7564 : ℝ) / 136153) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((7563 : ℝ) / 136135)) (f ((7564 : ℝ) / 136153)) := by
    constructor <;> norm_num [f, positiveCusp25Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((7563 : ℝ) / 136135) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp25Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((7564 : ℝ) / 136153) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp25Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp25Root : ℝ := Classical.choose positiveCusp25Root_exists

theorem positiveCusp25Root_lower : ((7563 : ℝ) / 136135) < positiveCusp25Root :=
  (Classical.choose_spec positiveCusp25Root_exists).1

theorem positiveCusp25Root_upper : positiveCusp25Root < ((7564 : ℝ) / 136153) :=
  (Classical.choose_spec positiveCusp25Root_exists).2.1

theorem positiveCusp25Root_equation : (2971 : ℝ) * positiveCusp25Root ^ 3 + (-867 : ℝ) * positiveCusp25Root ^ 2 + (489 : ℝ) * positiveCusp25Root + (-25 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp25Root_exists).2.2


theorem positiveCusp25Root_power_relations :
    let t := positiveCusp25Root
    ((2971 : ℝ) * t ^ 3 + (-867 : ℝ) * t ^ 2 + (489 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((2971 : ℝ) * t ^ 3 + (-867 : ℝ) * t ^ 2 + (489 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((2971 : ℝ) * t ^ 3 + (-867 : ℝ) * t ^ 2 + (489 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((2971 : ℝ) * t ^ 3 + (-867 : ℝ) * t ^ 2 + (489 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((2971 : ℝ) * t ^ 3 + (-867 : ℝ) * t ^ 2 + (489 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((2971 : ℝ) * t ^ 3 + (-867 : ℝ) * t ^ 2 + (489 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((2971 : ℝ) * t ^ 3 + (-867 : ℝ) * t ^ 2 + (489 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((2971 : ℝ) * t ^ 3 + (-867 : ℝ) * t ^ 2 + (489 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((2971 : ℝ) * t ^ 3 + (-867 : ℝ) * t ^ 2 + (489 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp25Root_equation

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

def positiveCusp25 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp25Rates : Fin 5 → ℝ :=
  let t := positiveCusp25Root
  ![((2971 : ℝ) / 928) * t ^ 2 + ((-747 : ℝ) / 464) * t + ((367 : ℝ) / 928) * 1,
    ((-14855 : ℝ) / 3712) * t ^ 2 + ((3271 : ℝ) / 1856) * t + ((949 : ℝ) / 3712) * 1,
    ((8913 : ℝ) / 3712) * t ^ 2 + ((-849 : ℝ) / 1856) * t + ((173 : ℝ) / 3712) * 1,
    ((-2971 : ℝ) / 1856) * t ^ 2 + ((-645 : ℝ) / 928) * t + ((561 : ℝ) / 1856) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp25RightKernel : Species → ℝ :=
  let t := positiveCusp25Root
  ![((2971 : ℝ) / 1856) * t ^ 2 + ((645 : ℝ) / 928) * t + ((-561 : ℝ) / 1856) * 1,
    ((14855 : ℝ) / 1856) * t ^ 2 + ((-2343 : ℝ) / 928) * t + ((907 : ℝ) / 1856) * 1]

noncomputable def positiveCusp25LeftKernel : Species → ℝ :=
  let t := positiveCusp25Root
  ![((246593 : ℝ) / 118784) * t ^ 2 + ((23611 : ℝ) / 296960) * t + ((-126371 : ℝ) / 118784) * 1,
    ((5641929 : ℝ) / 296960) * t ^ 2 + ((-875209 : ℝ) / 148480) * t + ((131777 : ℝ) / 59392) * 1]

noncomputable def positiveCusp25Center : Species → ℝ :=
  let t := positiveCusp25Root
  ![((-158 : ℝ) / 145) * t ^ 2 + ((44 : ℝ) / 145) * t + ((2 : ℝ) / 29) * 1,
    ((2769 : ℝ) / 1160) * t ^ 2 + ((-17 : ℝ) / 580) * t + ((9 : ℝ) / 232) * 1]

theorem positiveCusp25Rates_positive : PositiveVector positiveCusp25Rates := by
  have hl := positiveCusp25Root_lower
  have hu := positiveCusp25Root_upper
  have hs : 0 ≤ positiveCusp25Root ^ 2 := sq_nonneg positiveCusp25Root
  intro k
  fin_cases k <;> simp [positiveCusp25Rates] <;> nlinarith

theorem positiveCusp25_jacobian_values :
    positiveCusp25.toNetwork.jacobian positiveCusp25Rates unitState 0 0 = ((-14855 : ℝ) / 1856) * positiveCusp25Root ^ 2 + ((2343 : ℝ) / 928) * positiveCusp25Root + ((-907 : ℝ) / 1856) * 1 ∧
    positiveCusp25.toNetwork.jacobian positiveCusp25Rates unitState 0 1 = ((2971 : ℝ) / 1856) * positiveCusp25Root ^ 2 + ((645 : ℝ) / 928) * positiveCusp25Root + ((-561 : ℝ) / 1856) * 1 ∧
    positiveCusp25.toNetwork.jacobian positiveCusp25Rates unitState 1 0 = ((2971 : ℝ) / 464) * positiveCusp25Root ^ 2 + ((-51 : ℝ) / 232) * positiveCusp25Root + ((-97 : ℝ) / 464) * 1 ∧
    positiveCusp25.toNetwork.jacobian positiveCusp25Rates unitState 1 1 = ((-8913 : ℝ) / 3712) * positiveCusp25Root ^ 2 + ((-2863 : ℝ) / 1856) * positiveCusp25Root + ((-173 : ℝ) / 3712) * 1 := by
  norm_num [positiveCusp25, positiveCusp25Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp25_Bqq_values :
    positiveCusp25.toNetwork.hessianApply positiveCusp25Rates unitState
        positiveCusp25RightKernel positiveCusp25RightKernel 0 = ((169779 : ℝ) / 86159) * positiveCusp25Root ^ 2 + ((-13094 : ℝ) / 86159) * positiveCusp25Root + ((3847 : ℝ) / 86159) * 1 ∧
    positiveCusp25.toNetwork.hessianApply positiveCusp25Rates unitState
        positiveCusp25RightKernel positiveCusp25RightKernel 1 = ((-89249 : ℝ) / 86159) * positiveCusp25Root ^ 2 + ((-51838 : ℝ) / 86159) * positiveCusp25Root + ((5123 : ℝ) / 86159) * 1 := by
  rcases positiveCusp25Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp25, positiveCusp25Rates, positiveCusp25RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp25_Bqh_values :
    positiveCusp25.toNetwork.hessianApply positiveCusp25Rates unitState
        positiveCusp25RightKernel positiveCusp25Center 0 = ((-236961376 : ℝ) / 1279891945) * positiveCusp25Root ^ 2 + ((127833280 : ℝ) / 255978389) * positiveCusp25Root + ((-7605344 : ℝ) / 255978389) * 1 ∧
    positiveCusp25.toNetwork.hessianApply positiveCusp25Rates unitState
        positiveCusp25RightKernel positiveCusp25Center 1 = ((-271645992 : ℝ) / 1279891945) * positiveCusp25Root ^ 2 + ((-1139116976 : ℝ) / 1279891945) * positiveCusp25Root + ((10292248 : ℝ) / 255978389) * 1 := by
  rcases positiveCusp25Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp25, positiveCusp25Rates, positiveCusp25RightKernel,
    positiveCusp25Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp25_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp25.toNetwork positiveCusp25Rates
      positiveCusp25RightKernel positiveCusp25LeftKernel positiveCusp25Center 2 4).unfoldingMatrix =
      ((-23972999 : ℝ) / 185600) * positiveCusp25Root ^ 2 + ((1520711 : ℝ) / 92800) * positiveCusp25Root + ((-152195 : ℝ) / 7424) * 1 := by
  rcases positiveCusp25Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp25, positiveCusp25Rates, positiveCusp25RightKernel, positiveCusp25LeftKernel,
      positiveCusp25Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp25_cubic_value :
    dot positiveCusp25LeftKernel (positiveCusp25.toNetwork.hessianApply positiveCusp25Rates unitState
      positiveCusp25RightKernel positiveCusp25Center) = ((772752 : ℝ) / 430795) * positiveCusp25Root ^ 2 + ((-69536 : ℝ) / 430795) * positiveCusp25Root + ((-1136 : ℝ) / 86159) * 1 := by
  rcases positiveCusp25Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp25_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp25LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp25_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp25.toNetwork := by
  rcases positiveCusp25Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp25Root_lower
  have hu := positiveCusp25Root_upper
  have hs : 0 ≤ positiveCusp25Root ^ 2 := sq_nonneg positiveCusp25Root
  rcases positiveCusp25_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp25_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp25_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp25.toNetwork positiveCusp25Rates
    positiveCusp25RightKernel positiveCusp25LeftKernel positiveCusp25Center 2 4
  · exact positiveCusp25Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp25, positiveCusp25Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp25RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp25LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp25LeftKernel, positiveCusp25RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp25LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp25Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp25LeftKernel, positiveCusp25Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp25_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp25_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
