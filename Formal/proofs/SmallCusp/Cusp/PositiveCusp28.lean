import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp28Polynomial (t : ℝ) : ℝ := (1457 : ℝ) * t ^ 3 + (-1011 : ℝ) * t ^ 2 + (339 : ℝ) * t + (-17 : ℝ) * 1

private theorem positiveCusp28Root_exists :
    ∃ t : ℝ, ((1500 : ℝ) / 25027) < t ∧ t < ((463 : ℝ) / 7725) ∧ positiveCusp28Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ positiveCusp28Polynomial t
  have hf : Continuous f := by
    dsimp [f, positiveCusp28Polynomial]
    fun_prop
  have hab : ((1500 : ℝ) / 25027) ≤ ((463 : ℝ) / 7725) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((1500 : ℝ) / 25027)) (f ((463 : ℝ) / 7725)) := by
    constructor <;> norm_num [f, positiveCusp28Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((1500 : ℝ) / 25027) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp28Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((463 : ℝ) / 7725) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp28Polynomial] at hft
  · simpa [f] using hft

noncomputable def positiveCusp28Root : ℝ := Classical.choose positiveCusp28Root_exists

theorem positiveCusp28Root_lower : ((1500 : ℝ) / 25027) < positiveCusp28Root :=
  (Classical.choose_spec positiveCusp28Root_exists).1

theorem positiveCusp28Root_upper : positiveCusp28Root < ((463 : ℝ) / 7725) :=
  (Classical.choose_spec positiveCusp28Root_exists).2.1

theorem positiveCusp28Root_equation : (1457 : ℝ) * positiveCusp28Root ^ 3 + (-1011 : ℝ) * positiveCusp28Root ^ 2 + (339 : ℝ) * positiveCusp28Root + (-17 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp28Root_exists).2.2


theorem positiveCusp28Root_power_relations :
    let t := positiveCusp28Root
    ((1457 : ℝ) * t ^ 3 + (-1011 : ℝ) * t ^ 2 + (339 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((1457 : ℝ) * t ^ 3 + (-1011 : ℝ) * t ^ 2 + (339 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((1457 : ℝ) * t ^ 3 + (-1011 : ℝ) * t ^ 2 + (339 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((1457 : ℝ) * t ^ 3 + (-1011 : ℝ) * t ^ 2 + (339 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((1457 : ℝ) * t ^ 3 + (-1011 : ℝ) * t ^ 2 + (339 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((1457 : ℝ) * t ^ 3 + (-1011 : ℝ) * t ^ 2 + (339 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((1457 : ℝ) * t ^ 3 + (-1011 : ℝ) * t ^ 2 + (339 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((1457 : ℝ) * t ^ 3 + (-1011 : ℝ) * t ^ 2 + (339 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((1457 : ℝ) * t ^ 3 + (-1011 : ℝ) * t ^ 2 + (339 : ℝ) * t + (-17 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp28Root_equation

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

def positiveCusp28 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.y, .yy), (.xx, .xy), (.xy, .zero), (.yy, .zero)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp28Rates : Fin 5 → ℝ :=
  let t := positiveCusp28Root
  ![((1457 : ℝ) / 628) * t ^ 2 + ((-603 : ℝ) / 314) * t + ((253 : ℝ) / 628) * 1,
    ((-1457 : ℝ) / 314) * t ^ 2 + ((446 : ℝ) / 157) * t + ((61 : ℝ) / 314) * 1,
    ((4371 : ℝ) / 1256) * t ^ 2 + ((-867 : ℝ) / 628) * t + ((131 : ℝ) / 1256) * 1,
    ((-1457 : ℝ) / 1256) * t ^ 2 + ((-339 : ℝ) / 628) * t + ((375 : ℝ) / 1256) * 1,
    (1 : ℝ) * t]

noncomputable def positiveCusp28RightKernel : Species → ℝ :=
  let t := positiveCusp28Root
  ![((1457 : ℝ) / 1256) * t ^ 2 + ((339 : ℝ) / 628) * t + ((-375 : ℝ) / 1256) * 1,
    ((7285 : ℝ) / 1256) * t ^ 2 + ((-2073 : ℝ) / 628) * t + ((637 : ℝ) / 1256) * 1]

noncomputable def positiveCusp28LeftKernel : Species → ℝ :=
  let t := positiveCusp28Root
  ![((-278287 : ℝ) / 55264) * t ^ 2 + ((-48421 : ℝ) / 27632) * t + ((-60255 : ℝ) / 55264) * 1,
    ((980561 : ℝ) / 110528) * t ^ 2 + ((-488087 : ℝ) / 55264) * t + ((283309 : ℝ) / 110528) * 1]

noncomputable def positiveCusp28Center : Species → ℝ :=
  let t := positiveCusp28Root
  ![((-192 : ℝ) / 1727) * t ^ 2 + ((-104 : ℝ) / 1727) * t + ((152 : ℝ) / 1727) * 1,
    ((2752 : ℝ) / 1727) * t ^ 2 + ((-812 : ℝ) / 1727) * t + ((124 : ℝ) / 1727) * 1]

theorem positiveCusp28Rates_positive : PositiveVector positiveCusp28Rates := by
  have hl := positiveCusp28Root_lower
  have hu := positiveCusp28Root_upper
  have hs : 0 ≤ positiveCusp28Root ^ 2 := sq_nonneg positiveCusp28Root
  intro k
  fin_cases k <;> simp [positiveCusp28Rates] <;> nlinarith

theorem positiveCusp28_jacobian_values :
    positiveCusp28.toNetwork.jacobian positiveCusp28Rates unitState 0 0 = ((-7285 : ℝ) / 1256) * positiveCusp28Root ^ 2 + ((2073 : ℝ) / 628) * positiveCusp28Root + ((-637 : ℝ) / 1256) * 1 ∧
    positiveCusp28.toNetwork.jacobian positiveCusp28Rates unitState 0 1 = ((1457 : ℝ) / 1256) * positiveCusp28Root ^ 2 + ((339 : ℝ) / 628) * positiveCusp28Root + ((-375 : ℝ) / 1256) * 1 ∧
    positiveCusp28.toNetwork.jacobian positiveCusp28Rates unitState 1 0 = ((10199 : ℝ) / 1256) * positiveCusp28Root ^ 2 + ((-1395 : ℝ) / 628) * positiveCusp28Root + ((-113 : ℝ) / 1256) * 1 ∧
    positiveCusp28.toNetwork.jacobian positiveCusp28Rates unitState 1 1 = ((-4371 : ℝ) / 1256) * positiveCusp28Root ^ 2 + ((-389 : ℝ) / 628) * positiveCusp28Root + ((-131 : ℝ) / 1256) * 1 := by
  norm_num [positiveCusp28, positiveCusp28Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp28_Bqq_values :
    positiveCusp28.toNetwork.hessianApply positiveCusp28Rates unitState
        positiveCusp28RightKernel positiveCusp28RightKernel 0 = ((108120 : ℝ) / 228749) * positiveCusp28Root ^ 2 + ((-13184 : ℝ) / 228749) * positiveCusp28Root + ((9704 : ℝ) / 228749) * 1 ∧
    positiveCusp28.toNetwork.hessianApply positiveCusp28Rates unitState
        positiveCusp28RightKernel positiveCusp28RightKernel 1 = ((134572 : ℝ) / 228749) * positiveCusp28Root ^ 2 + ((-156824 : ℝ) / 228749) * positiveCusp28Root + ((14380 : ℝ) / 228749) * 1 := by
  rcases positiveCusp28Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp28, positiveCusp28Rates, positiveCusp28RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp28_Bqh_values :
    positiveCusp28.toNetwork.hessianApply positiveCusp28Rates unitState
        positiveCusp28RightKernel positiveCusp28Center 0 = ((-1230394608 : ℝ) / 3666160223) * positiveCusp28Root ^ 2 + ((591065120 : ℝ) / 3666160223) * positiveCusp28Root + ((-39731504 : ℝ) / 3666160223) * 1 ∧
    positiveCusp28.toNetwork.hessianApply positiveCusp28Rates unitState
        positiveCusp28RightKernel positiveCusp28Center 1 = ((3800838568 : ℝ) / 3666160223) * positiveCusp28Root ^ 2 + ((-1812362960 : ℝ) / 3666160223) * positiveCusp28Root + ((60932392 : ℝ) / 3666160223) * 1 := by
  rcases positiveCusp28Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp28, positiveCusp28Rates, positiveCusp28RightKernel,
    positiveCusp28Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp28_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp28.toNetwork positiveCusp28Rates
      positiveCusp28RightKernel positiveCusp28LeftKernel positiveCusp28Center 2 4).unfoldingMatrix =
      ((-18913317 : ℝ) / 151976) * positiveCusp28Root ^ 2 + ((2734937 : ℝ) / 37994) * positiveCusp28Root + ((-3026399 : ℝ) / 151976) * 1 := by
  rcases positiveCusp28Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp28, positiveCusp28Rates, positiveCusp28RightKernel, positiveCusp28LeftKernel,
      positiveCusp28Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp28_cubic_value :
    dot positiveCusp28LeftKernel (positiveCusp28.toNetwork.hessianApply positiveCusp28Rates unitState
      positiveCusp28RightKernel positiveCusp28Center) = ((1172290 : ℝ) / 2516239) * positiveCusp28Root ^ 2 + ((3628 : ℝ) / 2516239) * positiveCusp28Root + ((-45422 : ℝ) / 2516239) * 1 := by
  rcases positiveCusp28Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp28_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp28LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp28_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp28.toNetwork := by
  rcases positiveCusp28Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp28Root_lower
  have hu := positiveCusp28Root_upper
  have hs : 0 ≤ positiveCusp28Root ^ 2 := sq_nonneg positiveCusp28Root
  rcases positiveCusp28_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp28_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp28_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp28.toNetwork positiveCusp28Rates
    positiveCusp28RightKernel positiveCusp28LeftKernel positiveCusp28Center 2 4
  · exact positiveCusp28Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp28, positiveCusp28Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp28RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp28LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp28LeftKernel, positiveCusp28RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp28LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp28Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp28LeftKernel, positiveCusp28Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp28_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp28_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
