import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp18Polynomial (t : ℝ) : ℝ := (99 : ℝ) * t ^ 2 + (-24 : ℝ) * t + (1 : ℝ) * 1

private theorem positiveCusp18Root_exists :
    ∃ t : ℝ, ((3218 : ℝ) / 17029) < t ∧ t < ((2255 : ℝ) / 11933) ∧ positiveCusp18Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp18Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp18Polynomial]
    fun_prop
  have hab : ((3218 : ℝ) / 17029) ≤ ((2255 : ℝ) / 11933) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((3218 : ℝ) / 17029)) (f ((2255 : ℝ) / 11933)) := by
    constructor <;> norm_num [f, positiveCusp18Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((3218 : ℝ) / 17029) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp18Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((2255 : ℝ) / 11933) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp18Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp18Root : ℝ := Classical.choose positiveCusp18Root_exists

theorem positiveCusp18Root_lower : ((3218 : ℝ) / 17029) < positiveCusp18Root :=
  (Classical.choose_spec positiveCusp18Root_exists).1

theorem positiveCusp18Root_upper : positiveCusp18Root < ((2255 : ℝ) / 11933) :=
  (Classical.choose_spec positiveCusp18Root_exists).2.1

theorem positiveCusp18Root_equation : (99 : ℝ) * positiveCusp18Root ^ 2 + (-24 : ℝ) * positiveCusp18Root + (1 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp18Root_exists).2.2


theorem positiveCusp18Root_power_relations :
    let t := positiveCusp18Root
    ((99 : ℝ) * t ^ 2 + (-24 : ℝ) * t + (1 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((99 : ℝ) * t ^ 2 + (-24 : ℝ) * t + (1 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((99 : ℝ) * t ^ 2 + (-24 : ℝ) * t + (1 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((99 : ℝ) * t ^ 2 + (-24 : ℝ) * t + (1 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((99 : ℝ) * t ^ 2 + (-24 : ℝ) * t + (1 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((99 : ℝ) * t ^ 2 + (-24 : ℝ) * t + (1 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((99 : ℝ) * t ^ 2 + (-24 : ℝ) * t + (1 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((99 : ℝ) * t ^ 2 + (-24 : ℝ) * t + (1 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((99 : ℝ) * t ^ 2 + (-24 : ℝ) * t + (1 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp18Root_equation

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

def positiveCusp18 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xy, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp18Rates : Fin 5 → ℝ :=
  let t := positiveCusp18Root
  ![(-5 : ℝ) * t + (1 : ℝ) * 1,
    (2 : ℝ) * t,
    (7 : ℝ) * t + (-1 : ℝ) * 1,
    (-5 : ℝ) * t + (1 : ℝ) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp18RightKernel : Species → ℝ :=
  let t := positiveCusp18Root
  ![(9 : ℝ) * t + (-1 : ℝ) * 1,
    (-3 : ℝ) * t + (1 : ℝ) * 1]

noncomputable def positiveCusp18LeftKernel : Species → ℝ :=
  let t := positiveCusp18Root
  ![((231 : ℝ) / 20) * t + ((-23 : ℝ) / 20) * 1,
    ((-33 : ℝ) / 20) * t + ((19 : ℝ) / 20) * 1]

noncomputable def positiveCusp18Center : Species → ℝ :=
  let t := positiveCusp18Root
  ![((-248 : ℝ) / 55) * t + ((152 : ℝ) / 165) * 1,
    ((-216 : ℝ) / 55) * t + ((104 : ℝ) / 165) * 1]

theorem positiveCusp18Rates_positive : PositiveVector positiveCusp18Rates := by
  have hl := positiveCusp18Root_lower
  have hu := positiveCusp18Root_upper
  have hs : 0 ≤ positiveCusp18Root ^ 2 := sq_nonneg positiveCusp18Root
  intro k
  fin_cases k <;> simp [positiveCusp18Rates] <;> nlinarith

theorem positiveCusp18_jacobian_values :
    positiveCusp18.toNetwork.jacobian positiveCusp18Rates unitState 0 0 = (3 : ℝ) * positiveCusp18Root + (-1 : ℝ) * 1 ∧
    positiveCusp18.toNetwork.jacobian positiveCusp18Rates unitState 0 1 = (9 : ℝ) * positiveCusp18Root + (-1 : ℝ) * 1 ∧
    positiveCusp18.toNetwork.jacobian positiveCusp18Rates unitState 1 0 = (9 : ℝ) * positiveCusp18Root + (-1 : ℝ) * 1 ∧
    positiveCusp18.toNetwork.jacobian positiveCusp18Rates unitState 1 1 = (-6 : ℝ) * positiveCusp18Root := by
  norm_num [positiveCusp18, positiveCusp18Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp18_Bqq_values :
    positiveCusp18.toNetwork.hessianApply positiveCusp18Rates unitState
        positiveCusp18RightKernel positiveCusp18RightKernel 0 = ((-608 : ℝ) / 121) * positiveCusp18Root + ((128 : ℝ) / 121) * 1 ∧
    positiveCusp18.toNetwork.hessianApply positiveCusp18Rates unitState
        positiveCusp18RightKernel positiveCusp18RightKernel 1 = ((-592 : ℝ) / 121) * positiveCusp18Root + ((272 : ℝ) / 363) * 1 := by
  rcases positiveCusp18Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp18, positiveCusp18Rates, positiveCusp18RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp18_Bqh_values :
    positiveCusp18.toNetwork.hessianApply positiveCusp18Rates unitState
        positiveCusp18RightKernel positiveCusp18Center 0 = ((7328 : ℝ) / 6655) * positiveCusp18Root + ((-4832 : ℝ) / 19965) * 1 ∧
    positiveCusp18.toNetwork.hessianApply positiveCusp18Rates unitState
        positiveCusp18RightKernel positiveCusp18Center 1 = ((18336 : ℝ) / 6655) * positiveCusp18Root + ((-28832 : ℝ) / 59895) * 1 := by
  rcases positiveCusp18Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp18, positiveCusp18Rates, positiveCusp18RightKernel,
    positiveCusp18Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp18_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp18.toNetwork positiveCusp18Rates
      positiveCusp18RightKernel positiveCusp18LeftKernel positiveCusp18Center 0 3).unfoldingMatrix =
      ((-297 : ℝ) / 20) * positiveCusp18Root + ((17 : ℝ) / 20) * 1 := by
  rcases positiveCusp18Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp18, positiveCusp18Rates, positiveCusp18RightKernel, positiveCusp18LeftKernel,
      positiveCusp18Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp18_cubic_value :
    dot positiveCusp18LeftKernel (positiveCusp18.toNetwork.hessianApply positiveCusp18Rates unitState
      positiveCusp18RightKernel positiveCusp18Center) = ((2416 : ℝ) / 1815) * positiveCusp18Root + ((-1424 : ℝ) / 5445) * 1 := by
  rcases positiveCusp18Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp18_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp18LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp18_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp18.toNetwork := by
  rcases positiveCusp18Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp18Root_lower
  have hu := positiveCusp18Root_upper
  have hs : 0 ≤ positiveCusp18Root ^ 2 := sq_nonneg positiveCusp18Root
  rcases positiveCusp18_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp18_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp18_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp18.toNetwork positiveCusp18Rates
    positiveCusp18RightKernel positiveCusp18LeftKernel positiveCusp18Center 0 3
  · exact positiveCusp18Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp18, positiveCusp18Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp18RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp18LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp18LeftKernel, positiveCusp18RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp18LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp18Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp18LeftKernel, positiveCusp18Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp18_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp18_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
