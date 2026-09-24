import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp50Polynomial (t : ℝ) : ℝ := (1913 : ℝ) * t ^ 2 + (-284 : ℝ) * t + (8 : ℝ) * 1

private theorem positiveCusp50Root_exists :
    ∃ t : ℝ, ((489 : ℝ) / 12941) < t ∧ t < ((461 : ℝ) / 12200) ∧ positiveCusp50Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ -(positiveCusp50Polynomial t)
  have hf : Continuous f := by
    dsimp [f, positiveCusp50Polynomial]
    fun_prop
  have hab : ((489 : ℝ) / 12941) ≤ ((461 : ℝ) / 12200) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((489 : ℝ) / 12941)) (f ((461 : ℝ) / 12200)) := by
    constructor <;> norm_num [f, positiveCusp50Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((489 : ℝ) / 12941) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp50Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((461 : ℝ) / 12200) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp50Polynomial] at hft
  · dsimp [f, positiveCusp50Polynomial] at hft ⊢
    nlinarith [hft]

noncomputable def positiveCusp50Root : ℝ := Classical.choose positiveCusp50Root_exists

theorem positiveCusp50Root_lower : ((489 : ℝ) / 12941) < positiveCusp50Root :=
  (Classical.choose_spec positiveCusp50Root_exists).1

theorem positiveCusp50Root_upper : positiveCusp50Root < ((461 : ℝ) / 12200) :=
  (Classical.choose_spec positiveCusp50Root_exists).2.1

theorem positiveCusp50Root_equation : (1913 : ℝ) * positiveCusp50Root ^ 2 + (-284 : ℝ) * positiveCusp50Root + (8 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp50Root_exists).2.2


theorem positiveCusp50Root_power_relations :
    let t := positiveCusp50Root
    ((1913 : ℝ) * t ^ 2 + (-284 : ℝ) * t + (8 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((1913 : ℝ) * t ^ 2 + (-284 : ℝ) * t + (8 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((1913 : ℝ) * t ^ 2 + (-284 : ℝ) * t + (8 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((1913 : ℝ) * t ^ 2 + (-284 : ℝ) * t + (8 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((1913 : ℝ) * t ^ 2 + (-284 : ℝ) * t + (8 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((1913 : ℝ) * t ^ 2 + (-284 : ℝ) * t + (8 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((1913 : ℝ) * t ^ 2 + (-284 : ℝ) * t + (8 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((1913 : ℝ) * t ^ 2 + (-284 : ℝ) * t + (8 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((1913 : ℝ) * t ^ 2 + (-284 : ℝ) * t + (8 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp50Root_equation

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

def positiveCusp50 : CodedBimolNetwork where
  reaction := ![(.x, .yy), (.y, .xx), (.xx, .zero), (.xy, .yy), (.yy, .x)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp50Rates : Fin 5 → ℝ :=
  let t := positiveCusp50Root
  ![((-40 : ℝ) / 9) * t + ((2 : ℝ) / 9) * 1,
    ((-17 : ℝ) / 9) * t + ((4 : ℝ) / 9) * 1,
    ((-11 : ℝ) / 3) * t + ((1 : ℝ) / 3) * 1,
    (9 : ℝ) * t,
    (1 : ℝ) * t]

noncomputable def positiveCusp50RightKernel : Species → ℝ :=
  let t := positiveCusp50Root
  ![((-97 : ℝ) / 9) * t + ((8 : ℝ) / 9) * 1,
    ((-91 : ℝ) / 9) * t + ((14 : ℝ) / 9) * 1]

noncomputable def positiveCusp50LeftKernel : Species → ℝ :=
  let t := positiveCusp50Root
  ![((541379 : ℝ) / 4620) * t + ((-4789 : ℝ) / 1155) * 1,
    ((32521 : ℝ) / 308) * t + ((-501 : ℝ) / 154) * 1]

noncomputable def positiveCusp50Center : Species → ℝ :=
  let t := positiveCusp50Root
  ![((57287540 : ℝ) / 1325709) * t + ((-2614960 : ℝ) / 1325709) * 1,
    ((-7976560 : ℝ) / 189387) * t + ((326000 : ℝ) / 189387) * 1]

theorem positiveCusp50Rates_positive : PositiveVector positiveCusp50Rates := by
  have hl := positiveCusp50Root_lower
  have hu := positiveCusp50Root_upper
  have hs : 0 ≤ positiveCusp50Root ^ 2 := sq_nonneg positiveCusp50Root
  intro k
  fin_cases k <;> simp [positiveCusp50Rates] <;> nlinarith

theorem positiveCusp50_jacobian_values :
    positiveCusp50.toNetwork.jacobian positiveCusp50Rates unitState 0 0 = ((91 : ℝ) / 9) * positiveCusp50Root + ((-14 : ℝ) / 9) * 1 ∧
    positiveCusp50.toNetwork.jacobian positiveCusp50Rates unitState 0 1 = ((-97 : ℝ) / 9) * positiveCusp50Root + ((8 : ℝ) / 9) * 1 ∧
    positiveCusp50.toNetwork.jacobian positiveCusp50Rates unitState 1 0 = ((1 : ℝ) / 9) * positiveCusp50Root + ((4 : ℝ) / 9) * 1 ∧
    positiveCusp50.toNetwork.jacobian positiveCusp50Rates unitState 1 1 = ((62 : ℝ) / 9) * positiveCusp50Root + ((-4 : ℝ) / 9) * 1 := by
  norm_num [positiveCusp50, positiveCusp50Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp50_Bqq_values :
    positiveCusp50.toNetwork.hessianApply positiveCusp50Rates unitState
        positiveCusp50RightKernel positiveCusp50RightKernel 0 = ((358948040 : ℝ) / 32936121) * positiveCusp50Root + ((-28749760 : ℝ) / 32936121) * 1 ∧
    positiveCusp50.toNetwork.hessianApply positiveCusp50Rates unitState
        positiveCusp50RightKernel positiveCusp50RightKernel 1 = ((-237212080 : ℝ) / 32936121) * positiveCusp50Root + ((14769440 : ℝ) / 32936121) * 1 := by
  rcases positiveCusp50Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp50, positiveCusp50Rates, positiveCusp50RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp50_Bqh_values :
    positiveCusp50.toNetwork.hessianApply positiveCusp50Rates unitState
        positiveCusp50RightKernel positiveCusp50Center 0 = ((-64268130843040 : ℝ) / 1617174519807) * positiveCusp50Root + ((2838008548160 : ℝ) / 1617174519807) * 1 ∧
    positiveCusp50.toNetwork.hessianApply positiveCusp50Rates unitState
        positiveCusp50RightKernel positiveCusp50Center 1 = ((2976533828960 : ℝ) / 77008310467) * positiveCusp50Root + ((-123047215040 : ℝ) / 77008310467) * 1 := by
  rcases positiveCusp50Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp50, positiveCusp50Rates, positiveCusp50RightKernel,
    positiveCusp50Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp50_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp50.toNetwork positiveCusp50Rates
      positiveCusp50RightKernel positiveCusp50LeftKernel positiveCusp50Center 0 4).unfoldingMatrix =
      ((-11954337 : ℝ) / 11858) * positiveCusp50Root + ((210156 : ℝ) / 5929) * 1 := by
  rcases positiveCusp50Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp50, positiveCusp50Rates, positiveCusp50RightKernel, positiveCusp50LeftKernel,
      positiveCusp50Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp50_cubic_value :
    dot positiveCusp50LeftKernel (positiveCusp50.toNetwork.hessianApply positiveCusp50Rates unitState
      positiveCusp50RightKernel positiveCusp50Center) = ((-8035777520 : ℝ) / 845360439) * positiveCusp50Root + ((278436640 : ℝ) / 845360439) * 1 := by
  rcases positiveCusp50Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp50_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp50LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp50_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp50.toNetwork := by
  rcases positiveCusp50Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp50Root_lower
  have hu := positiveCusp50Root_upper
  have hs : 0 ≤ positiveCusp50Root ^ 2 := sq_nonneg positiveCusp50Root
  rcases positiveCusp50_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp50_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp50_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp50.toNetwork positiveCusp50Rates
    positiveCusp50RightKernel positiveCusp50LeftKernel positiveCusp50Center 0 4
  · exact positiveCusp50Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp50, positiveCusp50Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp50RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp50LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp50LeftKernel, positiveCusp50RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp50LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp50Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp50LeftKernel, positiveCusp50Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp50_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp50_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
