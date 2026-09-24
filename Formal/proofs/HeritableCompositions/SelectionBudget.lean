import proofs.HeritableCompositions.GenerationTheorem

namespace HeritableCompositions
open FiniteCopy

noncomputable def highTime (γ : ℝ) : ℝ := 110/(297*γ)
noncomputable def lowTime (γ : ℝ) : ℝ := 40/(101*γ)

theorem selection_time_gap (γ : ℝ) (hγ : 0 < γ) : highTime γ < lowTime γ := by
  unfold highTime lowTime
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [hγ]

theorem high_time_large (γ : ℝ) (hγ : 0 < γ) (hmax : γ ≤ 1/100000000000) :
    4032 ≤ highTime γ := by
  unfold highTime
  apply (le_div_iff₀ (by positivity)).mpr
  linarith only [hmax]

noncomputable def highSecondDuration (γ : ℝ) (hγ : 0 < γ) (hmax : γ ≤ 1/100000000000) : NNReal :=
  ⟨highTime γ-4032,sub_nonneg.mpr (high_time_large γ hγ hmax)⟩

theorem high_second_budget (γ : ℝ) (hγ : 0 < γ) (hmax : γ ≤ 1/100000000000) :
    1099/1000 ≤ (γ*(297/100))*(highSecondDuration γ hγ hmax : ℝ) := by
  change 1099/1000 ≤ (γ*(297/100))*(110/(297*γ)-4032)
  have hg : γ ≠ 0 := ne_of_gt hγ
  have he : (γ*(297/100))*(110/(297*γ)-4032) = 11/10-(γ*(297/100))*4032 := by
    field_simp
    ring
  rw [he]
  linarith only [hmax]

theorem high_second_le_deadline (γ : ℝ) (hγ : 0 < γ) (hmax : γ ≤ 1/100000000000) :
    (highSecondDuration γ hγ hmax : ℝ) ≤ 10/(9*γ) := by
  have ht : highTime γ ≤ 10/(9*γ) := by
    unfold highTime
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith only [hγ]
  change highTime γ-4032 ≤ _
  linarith only [ht]

end HeritableCompositions
