import proofs.SmallCusp.Cusp.CanonicalChart
import proofs.SmallCusp.Obstruction.ConicDeterminantRational

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace SmallCusp

private def positiveCusp12Polynomial (t : ℝ) : ℝ := (9523 : ℝ) * t ^ 3 + (681 : ℝ) * t ^ 2 + (-135 : ℝ) * t + (3 : ℝ) * 1

private theorem positiveCusp12Root_exists :
    ∃ t : ℝ, ((113 : ℝ) / 4108) < t ∧ t < ((1082 : ℝ) / 39335) ∧ positiveCusp12Polynomial t = 0 := by
  let f : ℝ → ℝ := fun t ↦ -(positiveCusp12Polynomial t)
  have hf : Continuous f := by
    dsimp [f, positiveCusp12Polynomial]
    fun_prop
  have hab : ((113 : ℝ) / 4108) ≤ ((1082 : ℝ) / 39335) := by norm_num
  have hz : (0 : ℝ) ∈ Set.Icc (f ((113 : ℝ) / 4108)) (f ((1082 : ℝ) / 39335)) := by
    constructor <;> norm_num [f, positiveCusp12Polynomial]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf.continuousOn hz
  refine ⟨t, ?_, ?_, ?_⟩
  · rcases ht with ⟨htl, -⟩
    by_contra hn
    have : t = ((113 : ℝ) / 4108) := le_antisymm (le_of_not_gt hn) htl
    subst t
    norm_num [f, positiveCusp12Polynomial] at hft
  · rcases ht with ⟨-, htr⟩
    by_contra hn
    have : t = ((1082 : ℝ) / 39335) := le_antisymm htr (le_of_not_gt hn)
    subst t
    norm_num [f, positiveCusp12Polynomial] at hft
  · dsimp [f, positiveCusp12Polynomial] at hft ⊢
    nlinarith [hft]

noncomputable def positiveCusp12Root : ℝ := Classical.choose positiveCusp12Root_exists

theorem positiveCusp12Root_lower : ((113 : ℝ) / 4108) < positiveCusp12Root :=
  (Classical.choose_spec positiveCusp12Root_exists).1

theorem positiveCusp12Root_upper : positiveCusp12Root < ((1082 : ℝ) / 39335) :=
  (Classical.choose_spec positiveCusp12Root_exists).2.1

theorem positiveCusp12Root_equation : (9523 : ℝ) * positiveCusp12Root ^ 3 + (681 : ℝ) * positiveCusp12Root ^ 2 + (-135 : ℝ) * positiveCusp12Root + (3 : ℝ) * 1 = 0 :=
  (Classical.choose_spec positiveCusp12Root_exists).2.2


theorem positiveCusp12Root_power_relations :
    let t := positiveCusp12Root
    ((9523 : ℝ) * t ^ 3 + (681 : ℝ) * t ^ 2 + (-135 : ℝ) * t + (3 : ℝ) * 1) * t ^ 0 = 0 ∧
    ((9523 : ℝ) * t ^ 3 + (681 : ℝ) * t ^ 2 + (-135 : ℝ) * t + (3 : ℝ) * 1) * t ^ 1 = 0 ∧
    ((9523 : ℝ) * t ^ 3 + (681 : ℝ) * t ^ 2 + (-135 : ℝ) * t + (3 : ℝ) * 1) * t ^ 2 = 0 ∧
    ((9523 : ℝ) * t ^ 3 + (681 : ℝ) * t ^ 2 + (-135 : ℝ) * t + (3 : ℝ) * 1) * t ^ 3 = 0 ∧
    ((9523 : ℝ) * t ^ 3 + (681 : ℝ) * t ^ 2 + (-135 : ℝ) * t + (3 : ℝ) * 1) * t ^ 4 = 0 ∧
    ((9523 : ℝ) * t ^ 3 + (681 : ℝ) * t ^ 2 + (-135 : ℝ) * t + (3 : ℝ) * 1) * t ^ 5 = 0 ∧
    ((9523 : ℝ) * t ^ 3 + (681 : ℝ) * t ^ 2 + (-135 : ℝ) * t + (3 : ℝ) * 1) * t ^ 6 = 0 ∧
    ((9523 : ℝ) * t ^ 3 + (681 : ℝ) * t ^ 2 + (-135 : ℝ) * t + (3 : ℝ) * 1) * t ^ 7 = 0 ∧
    ((9523 : ℝ) * t ^ 3 + (681 : ℝ) * t ^ 2 + (-135 : ℝ) * t + (3 : ℝ) * 1) * t ^ 8 = 0 := by
  dsimp
  have h := positiveCusp12Root_equation

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

def positiveCusp12 : CodedBimolNetwork where
  reaction := ![(.zero, .x), (.x, .yy), (.y, .zero), (.xx, .zero), (.yy, .xx)]
  noSelf := by decide
  injective := by decide

noncomputable def positiveCusp12Rates : Fin 5 → ℝ :=
  let t := positiveCusp12Root
  ![((47615 : ℝ) / 888) * t ^ 2 + ((1065 : ℝ) / 148) * t + ((-51 : ℝ) / 296) * 1,
    ((-9523 : ℝ) / 296) * t ^ 2 + ((-639 : ℝ) / 148) * t + ((149 : ℝ) / 296) * 1,
    ((9523 : ℝ) / 444) * t ^ 2 + ((65 : ℝ) / 74) * t + ((49 : ℝ) / 148) * 1,
    (1 : ℝ) * t,
    ((-9523 : ℝ) / 222) * t ^ 2 + ((-176 : ℝ) / 37) * t + ((25 : ℝ) / 74) * 1]

noncomputable def positiveCusp12RightKernel : Species → ℝ :=
  let t := positiveCusp12Root
  ![((-19046 : ℝ) / 111) * t ^ 2 + ((-704 : ℝ) / 37) * t + ((50 : ℝ) / 37) * 1,
    ((-9523 : ℝ) / 296) * t ^ 2 + ((-47 : ℝ) / 148) * t + ((149 : ℝ) / 296) * 1]

noncomputable def positiveCusp12LeftKernel : Species → ℝ :=
  let t := positiveCusp12Root
  ![((2809285 : ℝ) / 18944) * t ^ 2 + ((790865 : ℝ) / 9472) * t + ((-26787 : ℝ) / 18944) * 1,
    ((29149903 : ℝ) / 18944) * t ^ 2 + ((1780303 : ℝ) / 9472) * t + ((-107697 : ℝ) / 18944) * 1]

noncomputable def positiveCusp12Center : Species → ℝ :=
  let t := positiveCusp12Root
  ![((-13328 : ℝ) / 37) * t ^ 2 + ((-1872 : ℝ) / 37) * t + ((64 : ℝ) / 37) * 1,
    ((5174 : ℝ) / 37) * t ^ 2 + ((668 : ℝ) / 37) * t + ((-26 : ℝ) / 37) * 1]

theorem positiveCusp12Rates_positive : PositiveVector positiveCusp12Rates := by
  have hl := positiveCusp12Root_lower
  have hu := positiveCusp12Root_upper
  have hs : 0 ≤ positiveCusp12Root ^ 2 := sq_nonneg positiveCusp12Root
  intro k
  fin_cases k <;> simp [positiveCusp12Rates] <;> nlinarith

theorem positiveCusp12_jacobian_values :
    positiveCusp12.toNetwork.jacobian positiveCusp12Rates unitState 0 0 = ((9523 : ℝ) / 296) * positiveCusp12Root ^ 2 + ((47 : ℝ) / 148) * positiveCusp12Root + ((-149 : ℝ) / 296) * 1 ∧
    positiveCusp12.toNetwork.jacobian positiveCusp12Rates unitState 0 1 = ((-19046 : ℝ) / 111) * positiveCusp12Root ^ 2 + ((-704 : ℝ) / 37) * positiveCusp12Root + ((50 : ℝ) / 37) * 1 ∧
    positiveCusp12.toNetwork.jacobian positiveCusp12Rates unitState 1 0 = ((-9523 : ℝ) / 148) * positiveCusp12Root ^ 2 + ((-639 : ℝ) / 74) * positiveCusp12Root + ((149 : ℝ) / 148) * 1 ∧
    positiveCusp12.toNetwork.jacobian positiveCusp12Rates unitState 1 1 = ((66661 : ℝ) / 444) * positiveCusp12Root ^ 2 + ((1343 : ℝ) / 74) * positiveCusp12Root + ((-249 : ℝ) / 148) * 1 := by
  norm_num [positiveCusp12, positiveCusp12Rates, CodedBimolNetwork.toNetwork,
    BimolComplexCode.decode, unitState, SmallPlanarNetwork.jacobian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

theorem positiveCusp12_Bqq_values :
    positiveCusp12.toNetwork.hessianApply positiveCusp12Rates unitState
        positiveCusp12RightKernel positiveCusp12RightKernel 0 = ((-39021568 : ℝ) / 1057053) * positiveCusp12Root ^ 2 + ((-1668992 : ℝ) / 352351) * positiveCusp12Root + ((91264 : ℝ) / 352351) * 1 ∧
    positiveCusp12.toNetwork.hessianApply positiveCusp12Rates unitState
        positiveCusp12RightKernel positiveCusp12RightKernel 1 = ((30271040 : ℝ) / 1057053) * positiveCusp12Root ^ 2 + ((1073920 : ℝ) / 352351) * positiveCusp12Root + ((-91584 : ℝ) / 352351) * 1 := by
  rcases positiveCusp12Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp12, positiveCusp12Rates, positiveCusp12RightKernel,
    CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
    SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp12_Bqh_values :
    positiveCusp12.toNetwork.hessianApply positiveCusp12Rates unitState
        positiveCusp12RightKernel positiveCusp12Center 0 = ((-995810758400 : ℝ) / 10066315719) * positiveCusp12Root ^ 2 + ((-47086315008 : ℝ) / 3355438573) * positiveCusp12Root + ((1419034368 : ℝ) / 3355438573) * 1 ∧
    positiveCusp12.toNetwork.hessianApply positiveCusp12Rates unitState
        positiveCusp12RightKernel positiveCusp12Center 1 = ((263234737664 : ℝ) / 10066315719) * positiveCusp12Root ^ 2 + ((13158599680 : ℝ) / 3355438573) * positiveCusp12Root + ((-317875712 : ℝ) / 3355438573) * 1 := by
  rcases positiveCusp12Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  constructor <;> norm_num [positiveCusp12, positiveCusp12Rates, positiveCusp12RightKernel,
    positiveCusp12Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
    unitState, SmallPlanarNetwork.hessianApply, SmallPlanarNetwork.hessian,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    Fin.sum_univ_succ] <;>
    ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith

theorem positiveCusp12_unfolding_value :
    Matrix.det (unitChartCuspCertificate positiveCusp12.toNetwork positiveCusp12Rates
      positiveCusp12RightKernel positiveCusp12LeftKernel positiveCusp12Center 0 3).unfoldingMatrix =
      ((13170309 : ℝ) / 1184) * positiveCusp12Root ^ 2 + ((494719 : ℝ) / 592) * positiveCusp12Root + ((-40455 : ℝ) / 1184) * 1 := by
  rcases positiveCusp12Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [positiveCusp12, positiveCusp12Rates, positiveCusp12RightKernel, positiveCusp12LeftKernel,
      positiveCusp12Center, CodedBimolNetwork.toNetwork, BimolComplexCode.decode,
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

theorem positiveCusp12_cubic_value :
    dot positiveCusp12LeftKernel (positiveCusp12.toNetwork.hessianApply positiveCusp12Rates unitState
      positiveCusp12RightKernel positiveCusp12Center) = ((-27040736 : ℝ) / 352351) * positiveCusp12Root ^ 2 + ((-3627200 : ℝ) / 352351) * positiveCusp12Root + ((114464 : ℝ) / 352351) * 1 := by
  rcases positiveCusp12Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  rcases positiveCusp12_Bqh_values with ⟨hbh0, hbh1⟩
  simp [dot, Fin.sum_univ_two, hbh0, hbh1, positiveCusp12LeftKernel]
  all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  all_goals linarith

theorem positiveCusp12_admitsTransverseCusp :
    AdmitsTransverseCusp positiveCusp12.toNetwork := by
  rcases positiveCusp12Root_power_relations with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hl := positiveCusp12Root_lower
  have hu := positiveCusp12Root_upper
  have hs : 0 ≤ positiveCusp12Root ^ 2 := sq_nonneg positiveCusp12Root
  rcases positiveCusp12_jacobian_values with ⟨hj00, hj01, hj10, hj11⟩
  rcases positiveCusp12_Bqq_values with ⟨hbq0, hbq1⟩
  rcases positiveCusp12_Bqh_values with ⟨hbh0, hbh1⟩
  apply unitChartCusp_admits positiveCusp12.toNetwork positiveCusp12Rates
    positiveCusp12RightKernel positiveCusp12LeftKernel positiveCusp12Center 0 3
  · exact positiveCusp12Rates_positive
  · intro k
    fin_cases k <;> norm_num [positiveCusp12, positiveCusp12Rates,
      CodedBimolNetwork.toNetwork, BimolComplexCode.decode, unitState,
      SmallPlanarNetwork.massAction, SmallPlanarNetwork.monomial,
      SmallPlanarNetwork.stoich, Fin.sum_univ_succ, Fin.prod_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      positiveCusp12RightKernel, hj00, hj01, hj10, hj11, Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · intro k
    fin_cases k <;> simp [positiveCusp12LeftKernel, hj00, hj01, hj10, hj11,
      Fin.sum_univ_two] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp12LeftKernel, positiveCusp12RightKernel, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [hj00, hj11]
    all_goals nlinarith only [hl, hu, hs]
  · simp [dot, Fin.sum_univ_two, hbq0, hbq1, positiveCusp12LeftKernel]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · intro k
    fin_cases k <;> simp [SmallPlanarNetwork.jacobianApply,
      Fin.sum_univ_two, hbq0, hbq1, positiveCusp12Center,
      hj00, hj01, hj10, hj11] <;>
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢ <;> linarith
  · norm_num [positiveCusp12LeftKernel, positiveCusp12Center, dot, Fin.sum_univ_two]
    all_goals ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    all_goals linarith
  · rw [positiveCusp12_cubic_value]
    all_goals nlinarith only [hl, hu, hs]
  · rw [positiveCusp12_unfolding_value]
    all_goals nlinarith only [hl, hu, hs]

end SmallCusp
