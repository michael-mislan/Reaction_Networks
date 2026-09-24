import Mathlib

namespace CompositionalMemory

/-- Choose generation durations and a positive membrane rate before population parameters. -/
theorem exists_generation_timing (H birth Z lo allowance : ℝ)
    (hH : 0 < H) (hb : 0 ≤ birth) (hZ : 0 ≤ Z) (hlo : 0 < lo)
    (ha : 0 < allowance) :
    ∃ γ t₀ t₁ : ℝ, 0 < γ ∧ γ ≤ allowance ∧ 0 < t₀ ∧ 0 < t₁ ∧
      4*birth ≤ H*t₀ ∧ γ*Z*t₀ ≤ 2/5 ∧ γ*lo*t₁=11/10 := by
  let t₀ := 1+4*birth/H
  have ht : 0 < t₀ := by dsimp [t₀]; positivity
  let γ := min allowance (1/(5*(Z+1)*(t₀+1)))
  have hg : 0 < γ := by dsimp [γ]; positivity
  have hga : γ ≤ allowance := min_le_left _ _
  have hgb : γ*(5*(Z+1)*(t₀+1)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hzt : Z*t₀ ≤ (Z+1)*(t₀+1) := by nlinarith only [hZ, ht]
  have he : γ*Z*t₀ ≤ 2/5 := by
    nlinarith only [hgb, mul_le_mul_of_nonneg_left hzt hg.le]
  have hr : 4*birth ≤ H*t₀ := by
    dsimp [t₀]
    field_simp
    nlinarith only [hH]
  refine ⟨γ,t₀,11/(10*γ*lo),hg,hga,ht,by positivity,hr,he,?_⟩
  field_simp

end CompositionalMemory
