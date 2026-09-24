import Mathlib.Tactic

namespace RAF1519.Refinement
noncomputable section

theorem collection_inventory_integer (V Q : ℕ) (hV : 0 < (V:ℝ))
    (hQ : 39/1000 ≤ (Q:ℝ)/(V:ℝ)) : ⌈(V:ℝ)/56⌉₊ ≤ Q := by
  apply Nat.ceil_le.mpr
  have hh := (le_div_iff₀ hV).mp hQ
  linarith

theorem collection_freeX_integer (V Q : ℕ) (hV : 0 < (V:ℝ))
    (hQ : 6/1000 ≤ (Q:ℝ)/(V:ℝ)) : ⌈(V:ℝ)/1080⌉₊ ≤ Q := by
  apply Nat.ceil_le.mpr
  have hh := (le_div_iff₀ hV).mp hQ
  linarith

theorem gross_service_integer (V G : ℕ) (hV : 0 < (V:ℝ))
    (hG : (G:ℝ)/(V:ℝ) ≤ 181/1000) : G ≤ ⌊(V:ℝ)/5⌋₊ := by
  apply Nat.le_floor
  have hh := (div_le_iff₀ hV).mp hG
  linarith

theorem pulse_food_integer (V C D : ℕ) (hV : 0 < (V:ℝ))
    (hC : (C:ℝ)/(V:ℝ) ≤ 4001/1000) (hD : (D:ℝ) ≤ (151/200)*(V:ℝ)) : C+D ≤ 5*V := by
  have hh := (div_le_iff₀ hV).mp hC
  have hr : (C:ℝ)+(D:ℝ) ≤ 5*(V:ℝ) := by linarith
  exact_mod_cast hr

end
end RAF1519.Refinement
