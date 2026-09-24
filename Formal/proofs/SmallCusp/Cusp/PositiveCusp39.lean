import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp39Polynomial (t : ℝ) : ℝ := (584 : ℝ) * t ^ 3 + (-525 : ℝ) * t ^ 2 + (258 : ℝ) * t + (-25 : ℝ) * 1

private theorem positiveCusp39Root_exists :
    ∃ t : ℝ, ((13757 : ℝ) / 111135) < t ∧ t < ((13808 : ℝ) / 111547) ∧ positiveCusp39Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp39Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp39Polynomial]
    fun_prop
  have hab : ((13757 : ℝ) / 111135) ≤ ((13808 : ℝ) / 111547) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((13757 : ℝ) / 111135)) (f ((13808 : ℝ) / 111547)) := by
    constructor <;> norm_num [f, positiveCusp39Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((13757 : ℝ) / 111135) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp39Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((13808 : ℝ) / 111547) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp39Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp39Root : ℝ := Classical.choose positiveCusp39Root_exists

theorem positiveCusp39Root_lower : ((13757 : ℝ) / 111135) < positiveCusp39Root :=
  (Classical.choose_spec positiveCusp39Root_exists).1

theorem positiveCusp39Root_upper : positiveCusp39Root < ((13808 : ℝ) / 111547) :=
  (Classical.choose_spec positiveCusp39Root_exists).2.1

theorem positiveCusp39Root_equation : (584 : ℝ) * positiveCusp39Root ^ 3 + (-525 : ℝ) * positiveCusp39Root ^ 2 + (258 : ℝ) * positiveCusp39Root + (-25 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp39Root_exists).2.2


theorem positiveCusp39Root_power_relations :
    let t := positiveCusp39Root
    ((584 : ℝ) * t ^ 3 + (-525 : ℝ) * t ^ 2 + (258 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((584 : ℝ) * t ^ 3 + (-525 : ℝ) * t ^ 2 + (258 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((584 : ℝ) * t ^ 3 + (-525 : ℝ) * t ^ 2 + (258 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((584 : ℝ) * t ^ 3 + (-525 : ℝ) * t ^ 2 + (258 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((584 : ℝ) * t ^ 3 + (-525 : ℝ) * t ^ 2 + (258 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((584 : ℝ) * t ^ 3 + (-525 : ℝ) * t ^ 2 + (258 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((584 : ℝ) * t ^ 3 + (-525 : ℝ) * t ^ 2 + (258 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((584 : ℝ) * t ^ 3 + (-525 : ℝ) * t ^ 2 + (258 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((584 : ℝ) * t ^ 3 + (-525 : ℝ) * t ^ 2 + (258 : ℝ) * t + (-25 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp39Root_equation

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

def positiveCusp39 : CodedBimolNetwork where
  reaction := ![(.zero, .xy), (.x, .yy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp39Rates : Fin 5 → ℝ :=
  let t := positiveCusp39Root
  ![((1460 : ℝ) / 1283) * t ^ 2 + ((-1567 : ℝ) / 2566) * t + ((231 : ℝ) / 2566) * 1,
    ((-584 : ℝ) / 1283) * t ^ 2 + ((-713 : ℝ) / 1283) * t + ((467 : ℝ) / 1283) * 1,
    (1 : ℝ) * t,
    ((-2044 : ℝ) / 1283) * t ^ 2 + ((2707 : ℝ) / 2566) * t + ((703 : ℝ) / 2566) * 1,
    ((1168 : ℝ) / 1283) * t ^ 2 + ((-1140 : ℝ) / 1283) * t + ((349 : ℝ) / 1283) * 1]

noncomputable def positiveCusp39RightKernel : Species → ℝ :=
  let t := positiveCusp39Root
  ![((-2044 : ℝ) / 1283) * t ^ 2 + ((2707 : ℝ) / 2566) * t + ((703 : ℝ) / 2566) * 1,
    ((1460 : ℝ) / 1283) * t ^ 2 + ((999 : ℝ) / 2566) * t + ((231 : ℝ) / 2566) * 1]

noncomputable def positiveCusp39LeftKernel : Species → ℝ :=
  let t := positiveCusp39Root
  ![((15476 : ℝ) / 3849) * t ^ 2 + ((-44323 : ℝ) / 7698) * t + ((11360 : ℝ) / 3849) * 1,
    ((-20294 : ℝ) / 3849) * t ^ 2 + ((42023 : ℝ) / 15396) * t + ((8461 : ℝ) / 15396) * 1]

noncomputable def positiveCusp39Center : Species → ℝ :=
  let t := positiveCusp39Root
  ![((7672 : ℝ) / 3849) * t ^ 2 + ((-1987 : ℝ) / 3849) * t + ((157 : ℝ) / 3849) * 1,
    ((-1544 : ℝ) / 3849) * t ^ 2 + ((-1639 : ℝ) / 3849) * t + ((145 : ℝ) / 3849) * 1]

theorem positiveCusp39Rates_positive : PositiveVector positiveCusp39Rates := by
  have hl := positiveCusp39Root_lower
  have hu := positiveCusp39Root_upper
  have hs : 0 ≤ positiveCusp39Root ^ 2 := sq_nonneg positiveCusp39Root
  intro k
  fin_cases k <;> simp [positiveCusp39Rates] <;> nlinarith

theorem positiveCusp39_jacobian_values :
    positiveCusp39.toNetwork.jacobian positiveCusp39Rates unitState 0 0 = ((-1460 : ℝ) / 1283) * positiveCusp39Root ^ 2 + ((-999 : ℝ) / 2566) * positiveCusp39Root + ((-231 : ℝ) / 2566) * 1 ∧
    positiveCusp39.toNetwork.jacobian positiveCusp39Rates unitState 0 1 = ((-2044 : ℝ) / 1283) * positiveCusp39Root ^ 2 + ((2707 : ℝ) / 2566) * positiveCusp39Root + ((703 : ℝ) / 2566) * 1 ∧
    positiveCusp39.toNetwork.jacobian positiveCusp39Rates unitState 1 0 = ((876 : ℝ) / 1283) * positiveCusp39Root ^ 2 + ((-427 : ℝ) / 2566) * positiveCusp39Root + ((1165 : ℝ) / 2566) * 1 ∧
    positiveCusp39.toNetwork.jacobian positiveCusp39Rates unitState 1 1 = ((-2628 : ℝ) / 1283) * positiveCusp39Root ^ 2 + ((6413 : ℝ) / 2566) * positiveCusp39Root + ((-3495 : ℝ) / 2566) * 1 := by
  norm_num [positiveCusp39, positiveCusp39Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp39_Bqq_values :
    positiveCusp39.toNetwork.hessianApply positiveCusp39Rates unitState
        positiveCusp39RightKernel positiveCusp39RightKernel 0 = ((110608 : ℝ) / 93659) * positiveCusp39Root ^ 2 + ((-46970 : ℝ) / 93659) * positiveCusp39Root + ((4982 : ℝ) / 93659) * 1 ∧
    positiveCusp39.toNetwork.hessianApply positiveCusp39Rates unitState
        positiveCusp39RightKernel positiveCusp39RightKernel 1 = ((-46000 : ℝ) / 93659) * positiveCusp39Root ^ 2 + ((-1818 : ℝ) / 93659) * positiveCusp39Root + ((-1530 : ℝ) / 93659) * 1 := by
  rcases positiveCusp39Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp39, positiveCusp39Rates, positiveCusp39RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp39_Bqh_values :
    positiveCusp39.toNetwork.hessianApply positiveCusp39Rates unitState
        positiveCusp39RightKernel positiveCusp39Center 0 = ((-23859968 : ℝ) / 20511321) * positiveCusp39Root ^ 2 + ((2982416 : ℝ) / 20511321) * positiveCusp39Root + ((-71696 : ℝ) / 20511321) * 1 ∧
    positiveCusp39.toNetwork.hessianApply positiveCusp39Rates unitState
        positiveCusp39RightKernel positiveCusp39Center 1 = ((15087328 : ℝ) / 20511321) * positiveCusp39Root ^ 2 + ((3661256 : ℝ) / 20511321) * positiveCusp39Root + ((-568664 : ℝ) / 20511321) * 1 := by
  rcases positiveCusp39Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp39, positiveCusp39Rates, positiveCusp39RightKernel,
    positiveCusp39Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp39_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp39.toNetwork positiveCusp39Rates
      positiveCusp39RightKernel positiveCusp39LeftKernel positiveCusp39Center 0 2).unfoldingMatrix =
      ((-52560 : ℝ) / 1283) * positiveCusp39Root ^ 2 + ((34621 : ℝ) / 1283) * positiveCusp39Root + ((-8007 : ℝ) / 1283) * 1 := by
  rcases positiveCusp39Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp39, positiveCusp39Rates, positiveCusp39RightKernel, positiveCusp39LeftKernel,
      positiveCusp39Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp39_cubic_value :
    dot positiveCusp39LeftKernel (positiveCusp39.toNetwork.hessianApply positiveCusp39Rates unitState
      positiveCusp39RightKernel positiveCusp39Center) = ((105280 : ℝ) / 93659) * positiveCusp39Root ^ 2 + ((-17340 : ℝ) / 93659) * positiveCusp39Root + ((244 : ℝ) / 93659) * 1 := by
  rcases positiveCusp39Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp39_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp39LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp39_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp39.toNetwork := by
  rcases positiveCusp39Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp39Root_lower
  have hu := positiveCusp39Root_upper
  have hs : 0 ≤ positiveCusp39Root ^ 2 := sq_nonneg positiveCusp39Root
  rcases positiveCusp39_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp39_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp39_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp39.toNetwork positiveCusp39Rates
    positiveCusp39RightKernel positiveCusp39LeftKernel positiveCusp39Center 0 2
  · exact positiveCusp39Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp39, positiveCusp39Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp39RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp39LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp39LeftKernel, positiveCusp39RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp39LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp39Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp39LeftKernel, positiveCusp39Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp39_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp39_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
