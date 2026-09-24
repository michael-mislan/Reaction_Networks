import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp14Polynomial (t : ℝ) : ℝ := (206 : ℝ) * t ^ 3 + (51 : ℝ) * t ^ 2 + (-21 : ℝ) * t + (1 : ℝ) * 1

private theorem positiveCusp14Root_exists :
    ∃ t : ℝ, ((1198 : ℝ) / 20827) < t ∧ t < ((803 : ℝ) / 13960) ∧ positiveCusp14Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ -(positiveCusp14Polynomial t)
  have hf : Continuous f := by
    dsimp [f, positiveCusp14Polynomial]
    fun_prop
  have hab : ((1198 : ℝ) / 20827) ≤ ((803 : ℝ) / 13960) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((1198 : ℝ) / 20827)) (f ((803 : ℝ) / 13960)) := by
    constructor <;> norm_num [f, positiveCusp14Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((1198 : ℝ) / 20827) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp14Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((803 : ℝ) / 13960) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp14Polynomial] at hft
  · dsimp [f, positiveCusp14Polynomial] at hft ⊢
    nlinarith [hft]

noncomputable def positiveCusp14Root : ℝ := Classical.choose positiveCusp14Root_exists

theorem positiveCusp14Root_lower : ((1198 : ℝ) / 20827) < positiveCusp14Root :=
  (Classical.choose_spec positiveCusp14Root_exists).1

theorem positiveCusp14Root_upper : positiveCusp14Root < ((803 : ℝ) / 13960) :=
  (Classical.choose_spec positiveCusp14Root_exists).2.1

theorem positiveCusp14Root_equation : (206 : ℝ) * positiveCusp14Root ^ 3 + (51 : ℝ) * positiveCusp14Root ^ 2 + (-21 : ℝ) * positiveCusp14Root + (1 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp14Root_exists).2.2


theorem positiveCusp14Root_power_relations :
    let t := positiveCusp14Root
    ((206 : ℝ) * t ^ 3 + (51 : ℝ) * t ^ 2 + (-21 : ℝ) * t + (1 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((206 : ℝ) * t ^ 3 + (51 : ℝ) * t ^ 2 + (-21 : ℝ) * t + (1 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((206 : ℝ) * t ^ 3 + (51 : ℝ) * t ^ 2 + (-21 : ℝ) * t + (1 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((206 : ℝ) * t ^ 3 + (51 : ℝ) * t ^ 2 + (-21 : ℝ) * t + (1 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((206 : ℝ) * t ^ 3 + (51 : ℝ) * t ^ 2 + (-21 : ℝ) * t + (1 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((206 : ℝ) * t ^ 3 + (51 : ℝ) * t ^ 2 + (-21 : ℝ) * t + (1 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((206 : ℝ) * t ^ 3 + (51 : ℝ) * t ^ 2 + (-21 : ℝ) * t + (1 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((206 : ℝ) * t ^ 3 + (51 : ℝ) * t ^ 2 + (-21 : ℝ) * t + (1 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((206 : ℝ) * t ^ 3 + (51 : ℝ) * t ^ 2 + (-21 : ℝ) * t + (1 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp14Root_equation

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

def positiveCusp14 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .y), (.xy, .xx)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp14Rates : Fin 5 → ℝ :=
  let t := positiveCusp14Root
  ![((-618 : ℝ) / 71) * t ^ 2 + ((-283 : ℝ) / 71) * t + ((23 : ℝ) / 71) * 1,
    ((206 : ℝ) / 71) * t ^ 2 + ((47 : ℝ) / 71) * t + ((16 : ℝ) / 71) * 1,
    ((-412 : ℝ) / 71) * t ^ 2 + ((-307 : ℝ) / 71) * t + ((39 : ℝ) / 71) * 1,
    (1 : ℝ) * t,
    ((824 : ℝ) / 71) * t ^ 2 + ((472 : ℝ) / 71) * t + ((-7 : ℝ) / 71) * 1]

noncomputable def positiveCusp14RightKernel : Species → ℝ :=
  let t := positiveCusp14Root
  ![((824 : ℝ) / 71) * t ^ 2 + ((472 : ℝ) / 71) * t + ((-7 : ℝ) / 71) * 1,
    ((-618 : ℝ) / 71) * t ^ 2 + ((-141 : ℝ) / 71) * t + ((23 : ℝ) / 71) * 1]

noncomputable def positiveCusp14LeftKernel : Species → ℝ :=
  let t := positiveCusp14Root
  ![((14214 : ℝ) / 497) * t ^ 2 + ((-9253 : ℝ) / 497) * t + ((1672 : ℝ) / 497) * 1,
    ((-25544 : ℝ) / 497) * t ^ 2 + ((6242 : ℝ) / 497) * t + ((359 : ℝ) / 497) * 1]

noncomputable def positiveCusp14Center : Species → ℝ :=
  let t := positiveCusp14Root
  ![((-26876 : ℝ) / 497) * t ^ 2 + ((-8630 : ℝ) / 497) * t + ((594 : ℝ) / 497) * 1,
    ((12112 : ℝ) / 497) * t ^ 2 + ((8096 : ℝ) / 497) * t + ((-522 : ℝ) / 497) * 1]

theorem positiveCusp14Rates_positive : PositiveVector positiveCusp14Rates := by
  have hl := positiveCusp14Root_lower
  have hu := positiveCusp14Root_upper
  have hs : 0 ≤ positiveCusp14Root ^ 2 := sq_nonneg positiveCusp14Root
  intro k
  fin_cases k <;> simp [positiveCusp14Rates] <;> nlinarith

theorem positiveCusp14_jacobian_values :
    positiveCusp14.toNetwork.jacobian positiveCusp14Rates unitState 0 0 = ((618 : ℝ) / 71) * positiveCusp14Root ^ 2 + ((141 : ℝ) / 71) * positiveCusp14Root + ((-23 : ℝ) / 71) * 1 ∧
    positiveCusp14.toNetwork.jacobian positiveCusp14Rates unitState 0 1 = ((824 : ℝ) / 71) * positiveCusp14Root ^ 2 + ((472 : ℝ) / 71) * positiveCusp14Root + ((-7 : ℝ) / 71) * 1 ∧
    positiveCusp14.toNetwork.jacobian positiveCusp14Rates unitState 1 0 = ((-412 : ℝ) / 71) * positiveCusp14Root ^ 2 + ((-236 : ℝ) / 71) * positiveCusp14Root + ((39 : ℝ) / 71) * 1 ∧
    positiveCusp14.toNetwork.jacobian positiveCusp14Rates unitState 1 1 = ((-412 : ℝ) / 71) * positiveCusp14Root ^ 2 + ((-165 : ℝ) / 71) * positiveCusp14Root + ((-32 : ℝ) / 71) * 1 := by
  norm_num [positiveCusp14, positiveCusp14Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp14_Bqq_values :
    positiveCusp14.toNetwork.hessianApply positiveCusp14Rates unitState
        positiveCusp14RightKernel positiveCusp14RightKernel 0 = ((-245452 : ℝ) / 7313) * positiveCusp14Root ^ 2 + ((-106010 : ℝ) / 7313) * positiveCusp14Root + ((7010 : ℝ) / 7313) * 1 ∧
    positiveCusp14.toNetwork.hessianApply positiveCusp14Rates unitState
        positiveCusp14RightKernel positiveCusp14RightKernel 1 = ((186860 : ℝ) / 7313) * positiveCusp14Root ^ 2 + ((76152 : ℝ) / 7313) * positiveCusp14Root + ((-5186 : ℝ) / 7313) * 1 := by
  rcases positiveCusp14Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp14, positiveCusp14Rates, positiveCusp14RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp14_Bqh_values :
    positiveCusp14.toNetwork.hessianApply positiveCusp14Rates unitState
        positiveCusp14RightKernel positiveCusp14Center 0 = ((709013308 : ℝ) / 5272673) * positiveCusp14Root ^ 2 + ((290840346 : ℝ) / 5272673) * positiveCusp14Root + ((-19094830 : ℝ) / 5272673) * 1 ∧
    positiveCusp14.toNetwork.hessianApply positiveCusp14Rates unitState
        positiveCusp14RightKernel positiveCusp14Center 1 = ((-562993244 : ℝ) / 5272673) * positiveCusp14Root ^ 2 + ((-246093642 : ℝ) / 5272673) * positiveCusp14Root + ((16034386 : ℝ) / 5272673) * 1 := by
  rcases positiveCusp14Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp14, positiveCusp14Rates, positiveCusp14RightKernel,
    positiveCusp14Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp14_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp14.toNetwork positiveCusp14Rates
      positiveCusp14RightKernel positiveCusp14LeftKernel positiveCusp14Center 0 3).unfoldingMatrix =
      ((12785596 : ℝ) / 3479) * positiveCusp14Root ^ 2 + ((-2871670 : ℝ) / 3479) * positiveCusp14Root + ((104136 : ℝ) / 3479) * 1 := by
  rcases positiveCusp14Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp14, positiveCusp14Rates, positiveCusp14RightKernel, positiveCusp14LeftKernel,
      positiveCusp14Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp14_cubic_value :
    dot positiveCusp14LeftKernel (positiveCusp14.toNetwork.hessianApply positiveCusp14Rates unitState
      positiveCusp14RightKernel positiveCusp14Center) = ((-349660 : ℝ) / 51191) * positiveCusp14Root ^ 2 + ((-509830 : ℝ) / 51191) * positiveCusp14Root + ((30232 : ℝ) / 51191) * 1 := by
  rcases positiveCusp14Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp14_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp14LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp14_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp14.toNetwork := by
  rcases positiveCusp14Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp14Root_lower
  have hu := positiveCusp14Root_upper
  have hs : 0 ≤ positiveCusp14Root ^ 2 := sq_nonneg positiveCusp14Root
  rcases positiveCusp14_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp14_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp14_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp14.toNetwork positiveCusp14Rates
    positiveCusp14RightKernel positiveCusp14LeftKernel positiveCusp14Center 0 3
  · exact positiveCusp14Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp14, positiveCusp14Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp14RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp14LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp14LeftKernel, positiveCusp14RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp14LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp14Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp14LeftKernel, positiveCusp14Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp14_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp14_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
