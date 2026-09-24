import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp17Polynomial (t : ℝ) : ℝ := (167 : ℝ) * t ^ 3 + (-198 : ℝ) * t ^ 2 + (84 : ℝ) * t + (-8 : ℝ) * 1

private theorem positiveCusp17Root_exists :
    ∃ t : ℝ, ((3203 : ℝ) / 24366) < t ∧ t < ((3562 : ℝ) / 27097) ∧ positiveCusp17Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp17Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp17Polynomial]
    fun_prop
  have hab : ((3203 : ℝ) / 24366) ≤ ((3562 : ℝ) / 27097) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((3203 : ℝ) / 24366)) (f ((3562 : ℝ) / 27097)) := by
    constructor <;> norm_num [f, positiveCusp17Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((3203 : ℝ) / 24366) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp17Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((3562 : ℝ) / 27097) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp17Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp17Root : ℝ := Classical.choose positiveCusp17Root_exists

theorem positiveCusp17Root_lower : ((3203 : ℝ) / 24366) < positiveCusp17Root :=
  (Classical.choose_spec positiveCusp17Root_exists).1

theorem positiveCusp17Root_upper : positiveCusp17Root < ((3562 : ℝ) / 27097) :=
  (Classical.choose_spec positiveCusp17Root_exists).2.1

theorem positiveCusp17Root_equation : (167 : ℝ) * positiveCusp17Root ^ 3 + (-198 : ℝ) * positiveCusp17Root ^ 2 + (84 : ℝ) * positiveCusp17Root + (-8 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp17Root_exists).2.2


theorem positiveCusp17Root_power_relations :
    let t := positiveCusp17Root
    ((167 : ℝ) * t ^ 3 + (-198 : ℝ) * t ^ 2 + (84 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((167 : ℝ) * t ^ 3 + (-198 : ℝ) * t ^ 2 + (84 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((167 : ℝ) * t ^ 3 + (-198 : ℝ) * t ^ 2 + (84 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((167 : ℝ) * t ^ 3 + (-198 : ℝ) * t ^ 2 + (84 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((167 : ℝ) * t ^ 3 + (-198 : ℝ) * t ^ 2 + (84 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((167 : ℝ) * t ^ 3 + (-198 : ℝ) * t ^ 2 + (84 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((167 : ℝ) * t ^ 3 + (-198 : ℝ) * t ^ 2 + (84 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((167 : ℝ) * t ^ 3 + (-198 : ℝ) * t ^ 2 + (84 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((167 : ℝ) * t ^ 3 + (-198 : ℝ) * t ^ 2 + (84 : ℝ) * t + (-8 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp17Root_equation

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

def positiveCusp17 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.xx, .xy), (.xy, .xx), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp17Rates : Fin 5 → ℝ :=
  let t := positiveCusp17Root
  ![((835 : ℝ) / 408) * t ^ 2 + ((-143 : ℝ) / 102) * t + ((19 : ℝ) / 102) * 1,
    ((-167 : ℝ) / 408) * t ^ 2 + ((-53 : ℝ) / 102) * t + ((37 : ℝ) / 102) * 1,
    (1 : ℝ) * t,
    ((-167 : ℝ) / 68) * t ^ 2 + ((32 : ℝ) / 17) * t + ((3 : ℝ) / 17) * 1,
    ((167 : ℝ) / 204) * t ^ 2 + ((-49 : ℝ) / 51) * t + ((14 : ℝ) / 51) * 1]

noncomputable def positiveCusp17RightKernel : Species → ℝ :=
  let t := positiveCusp17Root
  ![((-167 : ℝ) / 68) * t ^ 2 + ((32 : ℝ) / 17) * t + ((3 : ℝ) / 17) * 1,
    ((835 : ℝ) / 408) * t ^ 2 + ((-41 : ℝ) / 102) * t + ((19 : ℝ) / 102) * 1]

noncomputable def positiveCusp17LeftKernel : Species → ℝ :=
  let t := positiveCusp17Root
  ![((334 : ℝ) / 99) * t ^ 2 + ((-8507 : ℝ) / 1584) * t + ((2297 : ℝ) / 792) * 1,
    ((-14195 : ℝ) / 4224) * t ^ 2 + ((2621 : ℝ) / 1056) * t + ((199 : ℝ) / 352) * 1]

noncomputable def positiveCusp17Center : Species → ℝ :=
  let t := positiveCusp17Root
  ![((11109 : ℝ) / 6358) * t ^ 2 + ((-1926 : ℝ) / 3179) * t + ((186 : ℝ) / 3179) * 1,
    ((-2220 : ℝ) / 3179) * t ^ 2 + ((4 : ℝ) / 3179) * t + ((-40 : ℝ) / 3179) * 1]

theorem positiveCusp17Rates_positive : PositiveVector positiveCusp17Rates := by
  have hl := positiveCusp17Root_lower
  have hu := positiveCusp17Root_upper
  have hs : 0 ≤ positiveCusp17Root ^ 2 := sq_nonneg positiveCusp17Root
  intro k
  fin_cases k <;> simp [positiveCusp17Rates] <;> nlinarith

theorem positiveCusp17_jacobian_values :
    positiveCusp17.toNetwork.jacobian positiveCusp17Rates unitState 0 0 = ((-835 : ℝ) / 408) * positiveCusp17Root ^ 2 + ((41 : ℝ) / 102) * positiveCusp17Root + ((-19 : ℝ) / 102) * 1 ∧
    positiveCusp17.toNetwork.jacobian positiveCusp17Rates unitState 0 1 = ((-167 : ℝ) / 68) * positiveCusp17Root ^ 2 + ((32 : ℝ) / 17) * positiveCusp17Root + ((3 : ℝ) / 17) * 1 ∧
    positiveCusp17.toNetwork.jacobian positiveCusp17Rates unitState 1 0 = ((167 : ℝ) / 102) * positiveCusp17Root ^ 2 + ((-47 : ℝ) / 51) * positiveCusp17Root + ((28 : ℝ) / 51) * 1 ∧
    positiveCusp17.toNetwork.jacobian positiveCusp17Rates unitState 1 1 = ((-167 : ℝ) / 204) * positiveCusp17Root ^ 2 + ((100 : ℝ) / 51) * positiveCusp17Root + ((-65 : ℝ) / 51) * 1 := by
  norm_num [positiveCusp17, positiveCusp17Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp17_Bqq_values :
    positiveCusp17.toNetwork.hessianApply positiveCusp17Rates unitState
        positiveCusp17RightKernel positiveCusp17RightKernel 0 = ((1409512 : ℝ) / 820471) * positiveCusp17Root ^ 2 + ((-672224 : ℝ) / 820471) * positiveCusp17Root + ((72928 : ℝ) / 820471) * 1 ∧
    positiveCusp17.toNetwork.hessianApply positiveCusp17Rates unitState
        positiveCusp17RightKernel positiveCusp17RightKernel 1 = ((-742376 : ℝ) / 820471) * positiveCusp17Root ^ 2 + ((243856 : ℝ) / 820471) * positiveCusp17Root + ((-43328 : ℝ) / 820471) * 1 := by
  rcases positiveCusp17Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp17, positiveCusp17Rates, positiveCusp17RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp17_Bqh_values :
    positiveCusp17.toNetwork.hessianApply positiveCusp17Rates unitState
        positiveCusp17RightKernel positiveCusp17Center 0 = ((-11829730824 : ℝ) / 25622488859) * positiveCusp17Root ^ 2 + ((-7356245664 : ℝ) / 25622488859) * positiveCusp17Root + ((1071795936 : ℝ) / 25622488859) * 1 ∧
    positiveCusp17.toNetwork.hessianApply positiveCusp17Rates unitState
        positiveCusp17RightKernel positiveCusp17Center 1 = ((2748124408 : ℝ) / 25622488859) * positiveCusp17Root ^ 2 + ((13467786016 : ℝ) / 25622488859) * positiveCusp17Root + ((-1649477024 : ℝ) / 25622488859) * 1 := by
  rcases positiveCusp17Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp17, positiveCusp17Rates, positiveCusp17RightKernel,
    positiveCusp17Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp17_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp17.toNetwork positiveCusp17Rates
      positiveCusp17RightKernel positiveCusp17LeftKernel positiveCusp17Center 0 2).unfoldingMatrix =
      ((-510853 : ℝ) / 34848) * positiveCusp17Root ^ 2 + ((61891 : ℝ) / 4356) * positiveCusp17Root + ((-35311 : ℝ) / 8712) * 1 := by
  rcases positiveCusp17Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp17, positiveCusp17Rates, positiveCusp17RightKernel, positiveCusp17LeftKernel,
      positiveCusp17Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp17_cubic_value :
    dot positiveCusp17LeftKernel (positiveCusp17.toNetwork.hessianApply positiveCusp17Rates unitState
      positiveCusp17RightKernel positiveCusp17Center) = ((1867026 : ℝ) / 9025181) * positiveCusp17Root ^ 2 + ((1142760 : ℝ) / 9025181) * positiveCusp17Root + ((-212088 : ℝ) / 9025181) * 1 := by
  rcases positiveCusp17Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp17_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp17LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp17_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp17.toNetwork := by
  rcases positiveCusp17Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp17Root_lower
  have hu := positiveCusp17Root_upper
  have hs : 0 ≤ positiveCusp17Root ^ 2 := sq_nonneg positiveCusp17Root
  rcases positiveCusp17_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp17_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp17_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp17.toNetwork positiveCusp17Rates
    positiveCusp17RightKernel positiveCusp17LeftKernel positiveCusp17Center 0 2
  · exact positiveCusp17Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp17, positiveCusp17Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp17RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp17LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp17LeftKernel, positiveCusp17RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp17LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp17Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp17LeftKernel, positiveCusp17Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp17_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp17_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
