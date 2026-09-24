import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp26Polynomial (t : ℝ) : ℝ := (8485 : ℝ) * t ^ 2 + (-1166 : ℝ) * t + (25 : ℝ) * 1

private theorem positiveCusp26Root_exists :
    ∃ t : ℝ, ((34 : ℝ) / 1279) < t ∧ t < ((2087 : ℝ) / 78508) ∧ positiveCusp26Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ -(positiveCusp26Polynomial t)
  have hf : Continuous f := by
    dsimp [f, positiveCusp26Polynomial]
    fun_prop
  have hab : ((34 : ℝ) / 1279) ≤ ((2087 : ℝ) / 78508) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((34 : ℝ) / 1279)) (f ((2087 : ℝ) / 78508)) := by
    constructor <;> norm_num [f, positiveCusp26Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((34 : ℝ) / 1279) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp26Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((2087 : ℝ) / 78508) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp26Polynomial] at hft
  · dsimp [f, positiveCusp26Polynomial] at hft ⊢
    nlinarith [hft]

noncomputable def positiveCusp26Root : ℝ := Classical.choose positiveCusp26Root_exists

theorem positiveCusp26Root_lower : ((34 : ℝ) / 1279) < positiveCusp26Root :=
  (Classical.choose_spec positiveCusp26Root_exists).1

theorem positiveCusp26Root_upper : positiveCusp26Root < ((2087 : ℝ) / 78508) :=
  (Classical.choose_spec positiveCusp26Root_exists).2.1

theorem positiveCusp26Root_equation : (8485 : ℝ) * positiveCusp26Root ^ 2 + (-1166 : ℝ) * positiveCusp26Root + (25 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp26Root_exists).2.2


theorem positiveCusp26Root_power_relations :
    let t := positiveCusp26Root
    ((8485 : ℝ) * t ^ 2 + (-1166 : ℝ) * t + (25 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((8485 : ℝ) * t ^ 2 + (-1166 : ℝ) * t + (25 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((8485 : ℝ) * t ^ 2 + (-1166 : ℝ) * t + (25 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((8485 : ℝ) * t ^ 2 + (-1166 : ℝ) * t + (25 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((8485 : ℝ) * t ^ 2 + (-1166 : ℝ) * t + (25 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((8485 : ℝ) * t ^ 2 + (-1166 : ℝ) * t + (25 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((8485 : ℝ) * t ^ 2 + (-1166 : ℝ) * t + (25 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((8485 : ℝ) * t ^ 2 + (-1166 : ℝ) * t + (25 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((8485 : ℝ) * t ^ 2 + (-1166 : ℝ) * t + (25 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp26Root_equation

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

def positiveCusp26 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .y), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp26Rates : Fin 5 → ℝ :=
  let t := positiveCusp26Root
  ![((-105 : ℝ) / 13) * t + ((7 : ℝ) / 13) * 1,
    ((115 : ℝ) / 13) * t + ((1 : ℝ) / 13) * 1,
    ((-56 : ℝ) / 13) * t + ((2 : ℝ) / 13) * 1,
    ((33 : ℝ) / 13) * t + ((3 : ℝ) / 13) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp26RightKernel : Species → ℝ :=
  let t := positiveCusp26Root
  ![((19 : ℝ) / 13) * t + ((-3 : ℝ) / 13) * 1,
    ((-191 : ℝ) / 13) * t + ((11 : ℝ) / 13) * 1]

noncomputable def positiveCusp26LeftKernel : Species → ℝ :=
  let t := positiveCusp26Root
  ![((-3538245 : ℝ) / 374192) * t + ((-235003 : ℝ) / 374192) * 1,
    ((-144245 : ℝ) / 4112) * t + ((11337 : ℝ) / 4112) * 1]

noncomputable def positiveCusp26Center : Species → ℝ :=
  let t := positiveCusp26Root
  ![((-1947848 : ℝ) / 436129) * t + ((106232 : ℝ) / 436129) * 1,
    ((21025900 : ℝ) / 5669677) * t + ((-217756 : ℝ) / 5669677) * 1]

theorem positiveCusp26Rates_positive : PositiveVector positiveCusp26Rates := by
  have hl := positiveCusp26Root_lower
  have hu := positiveCusp26Root_upper
  have hs : 0 ≤ positiveCusp26Root ^ 2 := sq_nonneg positiveCusp26Root
  intro k
  fin_cases k <;> simp [positiveCusp26Rates] <;> nlinarith

theorem positiveCusp26_jacobian_values :
    positiveCusp26.toNetwork.jacobian positiveCusp26Rates unitState 0 0 = ((191 : ℝ) / 13) * positiveCusp26Root + ((-11 : ℝ) / 13) * 1 ∧
    positiveCusp26.toNetwork.jacobian positiveCusp26Rates unitState 0 1 = ((19 : ℝ) / 13) * positiveCusp26Root + ((-3 : ℝ) / 13) * 1 ∧
    positiveCusp26.toNetwork.jacobian positiveCusp26Rates unitState 1 0 = ((-145 : ℝ) / 13) * positiveCusp26Root + ((1 : ℝ) / 13) * 1 ∧
    positiveCusp26.toNetwork.jacobian positiveCusp26Rates unitState 1 1 = ((30 : ℝ) / 13) * positiveCusp26Root + ((-2 : ℝ) / 13) * 1 := by
  norm_num [positiveCusp26, positiveCusp26Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp26_Bqq_values :
    positiveCusp26.toNetwork.hessianApply positiveCusp26Rates unitState
        positiveCusp26RightKernel positiveCusp26RightKernel 0 = ((26300848 : ℝ) / 14399045) * positiveCusp26Root + ((57232 : ℝ) / 2879809) * 1 ∧
    positiveCusp26.toNetwork.hessianApply positiveCusp26Rates unitState
        positiveCusp26RightKernel positiveCusp26RightKernel 1 = ((-161058688 : ℝ) / 37437517) * positiveCusp26Root + ((5516224 : ℝ) / 37437517) * 1 := by
  rcases positiveCusp26Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp26, positiveCusp26Rates, positiveCusp26RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp26_Bqh_values :
    positiveCusp26.toNetwork.hessianApply positiveCusp26Rates unitState
        positiveCusp26RightKernel positiveCusp26Center 0 = ((-908985690373824 : ℝ) / 408189671292325) * positiveCusp26Root + ((854951219136 : ℝ) / 16327586851693) * 1 ∧
    positiveCusp26.toNetwork.hessianApply positiveCusp26Rates unitState
        positiveCusp26RightKernel positiveCusp26Center 1 = ((47241809991936 : ℝ) / 81637934258465) * positiveCusp26Root + ((-550296198144 : ℝ) / 16327586851693) * 1 := by
  rcases positiveCusp26Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp26, positiveCusp26Rates, positiveCusp26RightKernel,
    positiveCusp26Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp26_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp26.toNetwork positiveCusp26Rates
      positiveCusp26RightKernel positiveCusp26LeftKernel positiveCusp26Center 2 4).unfoldingMatrix =
      ((1163845025 : ℝ) / 3434548) * positiveCusp26Root + ((-117127565 : ℝ) / 3434548) * 1 := by
  rcases positiveCusp26Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp26, positiveCusp26Rates, positiveCusp26RightKernel, positiveCusp26LeftKernel,
      positiveCusp26Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp26_cubic_value :
    dot positiveCusp26LeftKernel (positiveCusp26.toNetwork.hessianApply positiveCusp26Rates unitState
      positiveCusp26RightKernel positiveCusp26Center) = ((36419057136 : ℝ) / 9621441869) * positiveCusp26Root + ((-1231914096 : ℝ) / 9621441869) * 1 := by
  rcases positiveCusp26Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp26_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp26LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp26_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp26.toNetwork := by
  rcases positiveCusp26Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp26Root_lower
  have hu := positiveCusp26Root_upper
  have hs : 0 ≤ positiveCusp26Root ^ 2 := sq_nonneg positiveCusp26Root
  rcases positiveCusp26_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp26_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp26_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp26.toNetwork positiveCusp26Rates
    positiveCusp26RightKernel positiveCusp26LeftKernel positiveCusp26Center 2 4
  · exact positiveCusp26Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp26, positiveCusp26Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp26RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp26LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp26LeftKernel, positiveCusp26RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp26LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp26Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp26LeftKernel, positiveCusp26Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp26_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp26_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
