import proofs.HeritableCompositions.GenerationBudget

namespace HeritableCompositions

theorem exponential_budget_le (B c N η : ℝ) (hB : 0 < B) (hc : 0 < c) (hη : 0 < η)
    (hN : Real.log (B/η)/c ≤ N) : B*Real.exp (-N*c) ≤ η := by
  have hlog : Real.log (B/η) ≤ N*c := (div_le_iff₀ hc).mp hN
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (div_pos hB hη)] at hexp
  have hb : B ≤ Real.exp (N*c)*η := (div_le_iff₀ hη).mp hexp
  have hh := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-N*c)).le
  have he : Real.exp (N*c)*Real.exp (-N*c) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hr : Real.exp (N*c)*η*Real.exp (-N*c) = η := by
    calc
      _ = η*(Real.exp (N*c)*Real.exp (-N*c)) := by ring
      _ = η := by rw [he,mul_one]
  rwa [hr] at hh

theorem generationPrefactor_pos (γ : ℝ) (hγ : 0 < γ) : 0 < generationPrefactor γ := by
  unfold generationPrefactor
  positivity

noncomputable def copyThreshold (γ : ℝ) : ℕ :=
  max 140000000000000000000 (Nat.ceil (Real.log (2*generationPrefactor γ)/heredityExponent))

theorem copyThreshold_large (γ : ℝ) (N : ℕ) (hN : copyThreshold γ ≤ N) :
    (140000000000000000000 : ℝ) ≤ N := by
  have hn : 140000000000000000000 ≤ N := (Nat.le_max_left _ _).trans hN
  exact_mod_cast hn

theorem copyThreshold_positive (γ : ℝ) (N : ℕ) (hN : copyThreshold γ ≤ N) : 1 ≤ N := by
  have hn : 140000000000000000000 ≤ N := (Nat.le_max_left _ _).trans hN
  omega

theorem copyThreshold_nonvacuous (γ : ℝ) (hγ : 0 < γ) (N : ℕ) (hN : copyThreshold γ ≤ N) :
    generationPrefactor γ*Real.exp (-(N : ℝ)*heredityExponent) ≤ 1/2 := by
  have hn : Nat.ceil (Real.log (2*generationPrefactor γ)/heredityExponent) ≤ N :=
    (Nat.le_max_right _ _).trans hN
  have hnr : (Nat.ceil (Real.log (2*generationPrefactor γ)/heredityExponent) : ℝ) ≤ N := by exact_mod_cast hn
  have hreal : Real.log (2*generationPrefactor γ)/heredityExponent ≤ N := (Nat.le_ceil _).trans hnr
  apply exponential_budget_le _ _ _ _ (generationPrefactor_pos γ hγ) heredityExponent_pos (by norm_num)
  convert hreal using 1
  congr 2
  ring

theorem generation_tradeoff (γ : ℝ) (hγ : 0 < γ) (N G : ℕ) (hG : 1 ≤ G)
    (η : ℝ) (hη : 0 < η)
    (hN : Real.log (generationPrefactor γ*(G : ℝ)/η)/heredityExponent ≤ N) :
    (G : ℝ)*(generationPrefactor γ*Real.exp (-(N : ℝ)*heredityExponent)) ≤ η := by
  have hGr : (0 : ℝ) < G := by exact_mod_cast (by omega : 0 < G)
  have h := exponential_budget_le (generationPrefactor γ*(G : ℝ)) heredityExponent N η
    (mul_pos (generationPrefactor_pos γ hγ) hGr) heredityExponent_pos hη hN
  nlinarith only [h]

end HeritableCompositions
