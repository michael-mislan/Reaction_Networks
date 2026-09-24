import Mathlib

namespace CompositionalMemory

theorem exists_partition_tolerance (L r parent birth : ℝ)
    (hL : 0 ≤ L) (hr : 0 ≤ r) (hgap : parent < birth) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ parent+2*L*r*δ+L*δ^2 < birth := by
  let δ := min 1 ((birth-parent)/(2*(1+2*L*r+L)))
  have hden : 0 < 2*(1+2*L*r+L) := by positivity
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos (sub_pos.mpr hgap) hden)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hbudget : δ*(2*(1+2*L*r+L)) ≤ birth-parent :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hsq : δ^2 ≤ δ := by nlinarith only [mul_le_mul_of_nonneg_left hδ1 hδ.le]
  refine ⟨δ,hδ,hδ1,?_⟩
  nlinarith only [hbudget,mul_le_mul_of_nonneg_left hsq hL,hgap,hδ]

theorem exists_coercive_parent_radius (c parent : ℝ) (hc : 0 < c) (hp : 0 ≤ parent) :
    ∃ r : ℝ, 0 < r ∧ parent ≤ c*r^2 := by
  let r := 1+parent/c
  have hr : 1 ≤ r := by dsimp [r]; linarith only [div_nonneg hp hc.le]
  have heq : c*r=c+parent := by dsimp [r]; field_simp
  have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ c*r by positivity)
  refine ⟨r,by linarith,?_⟩
  nlinarith only [hh,heq,hc]

end CompositionalMemory
