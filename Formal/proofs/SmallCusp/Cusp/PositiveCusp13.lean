import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp13Polynomial (t : ℝ) : ℝ := (1007 : ℝ) * t ^ 3 + (-483 : ℝ) * t ^ 2 + (45 : ℝ) * t + (-1 : ℝ) * 1

private theorem positiveCusp13Root_exists :
    ∃ t : ℝ, ((57 : ℝ) / 1712) < t ∧ t < ((2138 : ℝ) / 64215) ∧ positiveCusp13Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp13Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp13Polynomial]
    fun_prop
  have hab : ((57 : ℝ) / 1712) ≤ ((2138 : ℝ) / 64215) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((57 : ℝ) / 1712)) (f ((2138 : ℝ) / 64215)) := by
    constructor <;> norm_num [f, positiveCusp13Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((57 : ℝ) / 1712) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp13Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((2138 : ℝ) / 64215) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp13Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp13Root : ℝ := Classical.choose positiveCusp13Root_exists

theorem positiveCusp13Root_lower : ((57 : ℝ) / 1712) < positiveCusp13Root :=
  (Classical.choose_spec positiveCusp13Root_exists).1

theorem positiveCusp13Root_upper : positiveCusp13Root < ((2138 : ℝ) / 64215) :=
  (Classical.choose_spec positiveCusp13Root_exists).2.1

theorem positiveCusp13Root_equation : (1007 : ℝ) * positiveCusp13Root ^ 3 + (-483 : ℝ) * positiveCusp13Root ^ 2 + (45 : ℝ) * positiveCusp13Root + (-1 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp13Root_exists).2.2


theorem positiveCusp13Root_power_relations :
    let t := positiveCusp13Root
    ((1007 : ℝ) * t ^ 3 + (-483 : ℝ) * t ^ 2 + (45 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((1007 : ℝ) * t ^ 3 + (-483 : ℝ) * t ^ 2 + (45 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((1007 : ℝ) * t ^ 3 + (-483 : ℝ) * t ^ 2 + (45 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((1007 : ℝ) * t ^ 3 + (-483 : ℝ) * t ^ 2 + (45 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((1007 : ℝ) * t ^ 3 + (-483 : ℝ) * t ^ 2 + (45 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((1007 : ℝ) * t ^ 3 + (-483 : ℝ) * t ^ 2 + (45 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((1007 : ℝ) * t ^ 3 + (-483 : ℝ) * t ^ 2 + (45 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((1007 : ℝ) * t ^ 3 + (-483 : ℝ) * t ^ 2 + (45 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((1007 : ℝ) * t ^ 3 + (-483 : ℝ) * t ^ 2 + (45 : ℝ) * t + (-1 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp13Root_equation

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

def positiveCusp13 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.xx, .zero), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp13Rates : Fin 5 → ℝ :=
  let t := positiveCusp13Root
  ![((5035 : ℝ) / 136) * t ^ 2 + ((-977 : ℝ) / 68) * t + ((67 : ℝ) / 136) * 1,
    ((-1007 : ℝ) / 136) * t ^ 2 + ((141 : ℝ) / 68) * t + ((41 : ℝ) / 136) * 1,
    (1 : ℝ) * t,
    ((-3021 : ℝ) / 68) * t ^ 2 + ((627 : ℝ) / 34) * t + ((-13 : ℝ) / 68) * 1,
    ((1007 : ℝ) / 68) * t ^ 2 + ((-243 : ℝ) / 34) * t + ((27 : ℝ) / 68) * 1]

noncomputable def positiveCusp13RightKernel : Species → ℝ :=
  let t := positiveCusp13Root
  ![((-3021 : ℝ) / 68) * t ^ 2 + ((627 : ℝ) / 34) * t + ((-13 : ℝ) / 68) * 1,
    ((5035 : ℝ) / 136) * t ^ 2 + ((-841 : ℝ) / 68) * t + ((67 : ℝ) / 136) * 1]

noncomputable def positiveCusp13LeftKernel : Species → ℝ :=
  let t := positiveCusp13Root
  ![((29203 : ℝ) / 1536) * t ^ 2 + ((-13549 : ℝ) / 768) * t + ((1521 : ℝ) / 512) * 1,
    ((-29203 : ℝ) / 256) * t ^ 2 + ((18493 : ℝ) / 384) * t + ((-493 : ℝ) / 768) * 1]

noncomputable def positiveCusp13Center : Species → ℝ :=
  let t := positiveCusp13Root
  ![((49348 : ℝ) / 289) * t ^ 2 + ((-19432 : ℝ) / 289) * t + ((596 : ℝ) / 289) * 1,
    ((-31842 : ℝ) / 289) * t ^ 2 + ((12812 : ℝ) / 289) * t + ((-402 : ℝ) / 289) * 1]

theorem positiveCusp13Rates_positive : PositiveVector positiveCusp13Rates := by
  have hl := positiveCusp13Root_lower
  have hu := positiveCusp13Root_upper
  have hs : 0 ≤ positiveCusp13Root ^ 2 := sq_nonneg positiveCusp13Root
  intro k
  fin_cases k <;> simp [positiveCusp13Rates] <;> nlinarith

theorem positiveCusp13_jacobian_values :
    positiveCusp13.toNetwork.jacobian positiveCusp13Rates unitState 0 0 = ((-5035 : ℝ) / 136) * positiveCusp13Root ^ 2 + ((841 : ℝ) / 68) * positiveCusp13Root + ((-67 : ℝ) / 136) * 1 ∧
    positiveCusp13.toNetwork.jacobian positiveCusp13Rates unitState 0 1 = ((-3021 : ℝ) / 68) * positiveCusp13Root ^ 2 + ((627 : ℝ) / 34) * positiveCusp13Root + ((-13 : ℝ) / 68) * 1 ∧
    positiveCusp13.toNetwork.jacobian positiveCusp13Rates unitState 1 0 = ((1007 : ℝ) / 34) * positiveCusp13Root ^ 2 + ((-243 : ℝ) / 17) * positiveCusp13Root + ((27 : ℝ) / 34) * 1 ∧
    positiveCusp13.toNetwork.jacobian positiveCusp13Rates unitState 1 1 = ((-1007 : ℝ) / 68) * positiveCusp13Root ^ 2 + ((345 : ℝ) / 34) * positiveCusp13Root + ((-95 : ℝ) / 68) * 1 := by
  norm_num [positiveCusp13, positiveCusp13Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp13_Bqq_values :
    positiveCusp13.toNetwork.hessianApply positiveCusp13Rates unitState
        positiveCusp13RightKernel positiveCusp13RightKernel 0 = ((338698160 : ℝ) / 4947391) * positiveCusp13Root ^ 2 + ((-132914720 : ℝ) / 4947391) * positiveCusp13Root + ((4126256 : ℝ) / 4947391) * 1 ∧
    positiveCusp13.toNetwork.hessianApply positiveCusp13Rates unitState
        positiveCusp13RightKernel positiveCusp13RightKernel 1 = ((-223031584 : ℝ) / 4947391) * positiveCusp13Root ^ 2 + ((90485056 : ℝ) / 4947391) * positiveCusp13Root + ((-2985376 : ℝ) / 4947391) * 1 := by
  rcases positiveCusp13Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp13, positiveCusp13Rates, positiveCusp13RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp13_Bqh_values :
    positiveCusp13.toNetwork.hessianApply positiveCusp13Rates unitState
        positiveCusp13RightKernel positiveCusp13Center 0 = ((-18348889168128 : ℝ) / 84694386529) * positiveCusp13Root ^ 2 + ((7292353033728 : ℝ) / 84694386529) * positiveCusp13Root + ((-222897852672 : ℝ) / 84694386529) * 1 ∧
    positiveCusp13.toNetwork.hessianApply positiveCusp13Rates unitState
        positiveCusp13RightKernel positiveCusp13Center 1 = ((14419604093184 : ℝ) / 84694386529) * positiveCusp13Root ^ 2 + ((-5757837934080 : ℝ) / 84694386529) * positiveCusp13Root + ((176377579776 : ℝ) / 84694386529) * 1 := by
  rcases positiveCusp13Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp13, positiveCusp13Rates, positiveCusp13RightKernel,
    positiveCusp13Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp13_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp13.toNetwork positiveCusp13Rates
      positiveCusp13RightKernel positiveCusp13LeftKernel positiveCusp13Center 0 2).unfoldingMatrix =
      ((146015 : ℝ) / 576) * positiveCusp13Root ^ 2 + ((-23437 : ℝ) / 288) * positiveCusp13Root + ((-3577 : ℝ) / 576) * 1 := by
  rcases positiveCusp13Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp13, positiveCusp13Rates, positiveCusp13RightKernel, positiveCusp13LeftKernel,
      positiveCusp13Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp13_cubic_value :
    dot positiveCusp13LeftKernel (positiveCusp13.toNetwork.hessianApply positiveCusp13Rates unitState
      positiveCusp13RightKernel positiveCusp13Center) = ((364197648 : ℝ) / 4947391) * positiveCusp13Root ^ 2 + ((-146320864 : ℝ) / 4947391) * positiveCusp13Root + ((4437776 : ℝ) / 4947391) * 1 := by
  rcases positiveCusp13Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp13_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp13LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp13_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp13.toNetwork := by
  rcases positiveCusp13Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp13Root_lower
  have hu := positiveCusp13Root_upper
  have hs : 0 ≤ positiveCusp13Root ^ 2 := sq_nonneg positiveCusp13Root
  rcases positiveCusp13_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp13_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp13_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp13.toNetwork positiveCusp13Rates
    positiveCusp13RightKernel positiveCusp13LeftKernel positiveCusp13Center 0 2
  · exact positiveCusp13Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp13, positiveCusp13Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp13RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp13LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp13LeftKernel, positiveCusp13RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp13LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp13Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp13LeftKernel, positiveCusp13Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp13_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp13_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
