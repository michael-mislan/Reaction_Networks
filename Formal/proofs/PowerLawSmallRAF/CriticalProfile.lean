import proofs.PowerLawSmallRAF.CriticalWindow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace PowerLawSmallRAF

open Filter Topology Set intervalIntegral

noncomputable def criticalIntegral (b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..Real.log 2, Real.exp (-b * t)

theorem integral_exp_neg_mul (b : ℝ) (hb : b ≠ 0) (L : ℝ) :
    (∫ t in (0 : ℝ)..L, Real.exp (-b * t)) =
      (1 - Real.exp (-b * L)) / b := by
  have hneg : -b ≠ 0 := neg_ne_zero.mpr hb
  have D : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Real.exp ((-b) * y) / (-b))
        (Real.exp ((-b) * x)) x := by
    intro x
    conv => congr
    rw [← mul_div_cancel_right₀ (Real.exp ((-b) * x)) hneg]
    have h := ((Real.hasDerivAt_exp _).comp x
      ((hasDerivAt_id x).const_mul (-b))).div_const (-b)
    convert h using 1
    simp only [id_eq, mul_one]
  rw [integral_deriv_eq_sub' _ (funext fun x => (D x).deriv)
    (fun x _ => (D x).differentiableAt)]
  · norm_num
    field_simp [hb]
    ring
  · fun_prop

theorem criticalIntegral_eq (b : ℝ) :
    criticalIntegral b =
      if b = 0 then Real.log 2 else (1 - Real.exp (-b * Real.log 2)) / b := by
  by_cases hb : b = 0
  · subst b
    simp [criticalIntegral]
  · rw [if_neg hb]
    exact integral_exp_neg_mul b hb (Real.log 2)

theorem criticalLambda_eq_integral (b : ℝ) :
    criticalLambda b = criticalIntegral b / (Real.pi ^ 2 / 6) := by
  rw [criticalLambda, criticalIntegral_eq]
  split_ifs with hb
  · rfl
  · have hzeta : Real.pi ^ 2 / 6 ≠ 0 := by positivity
    field_simp [hb, hzeta]

theorem continuous_criticalIntegral : Continuous criticalIntegral := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun b t : ℝ => Real.exp (-b * t)) (by fun_prop)
    0 (Real.log 2)

theorem strictAnti_criticalIntegral : StrictAnti criticalIntegral := by
  intro b₁ b₂ hb
  dsimp [criticalIntegral]
  refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    (by fun_prop) (by fun_prop) ?_ ?_
  · intro t ht
    apply Real.exp_le_exp.mpr
    nlinarith [ht.1]
  · refine ⟨Real.log 2, by constructor <;> linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)], ?_⟩
    apply Real.exp_lt_exp.mpr
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

theorem continuous_criticalLambda : Continuous criticalLambda := by
  rw [show criticalLambda = fun b => criticalIntegral b / (Real.pi ^ 2 / 6) by
    funext b
    exact criticalLambda_eq_integral b]
  exact continuous_criticalIntegral.div_const (Real.pi ^ 2 / 6)

theorem strictAnti_criticalLambda : StrictAnti criticalLambda := by
  intro b₁ b₂ hb
  rw [criticalLambda_eq_integral, criticalLambda_eq_integral]
  exact div_lt_div_of_pos_right (strictAnti_criticalIntegral hb) (by positivity)

theorem criticalLambda_tendsto_atTop :
    Tendsto criticalLambda atTop (𝓝 0) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : Tendsto (fun b : ℝ => Real.exp (-b * Real.log 2)) atTop (𝓝 0) := by
    have hinner : Tendsto (fun b : ℝ => -b * Real.log 2) atTop atBot := by
      have h := tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hlog)
      convert h using 1
      funext b
      simp
      ring
    exact Real.tendsto_exp_atBot.comp hinner
  have hnum : Tendsto (fun b : ℝ => 1 - Real.exp (-b * Real.log 2)) atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using hone.sub hexp
  have hden : Tendsto (fun b : ℝ => b * (Real.pi ^ 2 / 6)) atTop atTop :=
    by simpa [mul_comm] using
      Tendsto.const_mul_atTop (by positivity : 0 < Real.pi ^ 2 / 6) tendsto_id
  have hquot : Tendsto
      (fun b : ℝ => (1 - Real.exp (-b * Real.log 2)) /
        (b * (Real.pi ^ 2 / 6))) atTop (𝓝 0) := by
    simpa using hnum.div_atTop hden
  apply hquot.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  rw [criticalLambda, if_neg (ne_of_gt hb)]

theorem criticalLambda_neg_tendsto_atTop :
    Tendsto (fun x : ℝ => criticalLambda (-x)) atTop atTop := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase : Tendsto
      (fun y : ℝ => ((1 : ℝ) * Real.exp y + (-1 : ℝ)) / y ^ (1 : ℕ))
      atTop atTop :=
    Real.tendsto_mul_exp_add_div_pow_atTop 1 (-1) 1 (by norm_num)
  have hcomp := hbase.comp (tendsto_id.const_mul_atTop hlog)
  have hscale : 0 < Real.log 2 / (Real.pi ^ 2 / 6) := by positivity
  have hscaled := Tendsto.const_mul_atTop hscale hcomp
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [criticalLambda, if_neg (neg_ne_zero.mpr (ne_of_gt hx))]
  simp only [Function.comp_apply, id_eq, one_mul, pow_one]
  field_simp [ne_of_gt hx, ne_of_gt hlog]
  ring

theorem criticalLambda_tendsto_atBot :
    Tendsto criticalLambda atBot atTop := by
  have h := criticalLambda_neg_tendsto_atTop.comp tendsto_neg_atBot_atTop
  convert h using 1
  simp [Function.comp_def]

theorem criticalLambda_pos (b : ℝ) : 0 < criticalLambda b := by
  rw [criticalLambda_eq_integral]
  apply div_pos
  · exact intervalIntegral.intervalIntegral_pos_of_pos
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (-b * t)).intervalIntegrable
        0 (Real.log 2))
      (fun t => Real.exp_pos (-b * t))
      (Real.log_pos (by norm_num))
  · positivity

theorem existsUnique_criticalLambda_eq (lam : ℝ) (hlam : 0 < lam) :
    ∃! b : ℝ, criticalLambda b = lam := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, lam < criticalLambda A :=
    (criticalLambda_tendsto_atBot.eventually_gt_atTop lam).exists
  obtain ⟨B, hB⟩ : ∃ B : ℝ, criticalLambda B < lam :=
    ((tendsto_order.1 criticalLambda_tendsto_atTop).2 lam hlam).exists
  have hAB : A ≤ B := by
    by_contra h
    have hBA : B < A := lt_of_not_ge h
    exact lt_asymm (strictAnti_criticalLambda hBA) (hB.trans hA)
  have hmem : lam ∈ Icc (criticalLambda B) (criticalLambda A) := ⟨hB.le, hA.le⟩
  obtain ⟨b, _, hb⟩ :=
    intermediate_value_Icc' hAB continuous_criticalLambda.continuousOn hmem
  refine ⟨b, hb, ?_⟩
  intro c hc
  exact strictAnti_criticalLambda.injective (hc.trans hb.symm)

theorem range_criticalLambda : Set.range criticalLambda = Ioi 0 := by
  ext lam
  constructor
  · rintro ⟨b, rfl⟩
    exact criticalLambda_pos b
  · intro hlam
    obtain ⟨b, hb, _⟩ := existsUnique_criticalLambda_eq lam hlam
    exact ⟨b, hb⟩

noncomputable def criticalLambdaInv (lam : Ioi (0 : ℝ)) : ℝ :=
  Classical.choose (existsUnique_criticalLambda_eq lam lam.property)

theorem criticalLambda_criticalLambdaInv (lam : Ioi (0 : ℝ)) :
    criticalLambda (criticalLambdaInv lam) = lam :=
  (existsUnique_criticalLambda_eq lam lam.property).choose_spec.1

theorem criticalLambdaInv_unique (lam : Ioi (0 : ℝ)) (b : ℝ) :
    criticalLambda b = lam ↔ b = criticalLambdaInv lam := by
  constructor
  · intro hb
    exact (existsUnique_criticalLambda_eq lam lam.property).unique hb
      (criticalLambda_criticalLambdaInv lam)
  · rintro rfl
    exact criticalLambda_criticalLambdaInv lam

theorem criticalLambdaInv_lt_iff (lam : Ioi (0 : ℝ)) (b : ℝ) :
    criticalLambdaInv lam < b ↔ criticalLambda b < lam := by
  rw [← criticalLambda_criticalLambdaInv lam]
  exact strictAnti_criticalLambda.lt_iff_gt.symm

theorem criticalLambdaInv_gt_iff (lam : Ioi (0 : ℝ)) (b : ℝ) :
    b < criticalLambdaInv lam ↔ lam < criticalLambda b := by
  rw [← criticalLambda_criticalLambdaInv lam]
  exact strictAnti_criticalLambda.lt_iff_gt.symm

end PowerLawSmallRAF
