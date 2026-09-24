import proofs.SmallResidentCompositionCopying.Regions

namespace SmallResidentCompositionCopying

theorem module_mass_lower (a b : ℝ) (ha : 6 ≤ a) (hb : 0 ≤ b)
    (hb' : b ≤ 874) : (3:ℝ)/440 ≤ a/(a+b) := by
  have ht : 0 < a+b := by linarith
  apply (le_div_iff₀ ht).2
  linarith

/-- Other resident counts are included in each normalization denominator.
This bound applies to either differing module; adding the remaining two
coordinate distances preserves the lower bound. -/
theorem composition_gap (x y u v a b : ℝ)
    (hl : 100*y ≤ 3*(x+y)) (hh : u+v ≤ 20*v)
    (hxl : 6 ≤ x+y) (hxh : 6 ≤ u+v)
    (ha : 0 ≤ a) (ha' : a ≤ 874) (hb : 0 ≤ b) :
    (3:ℝ)/22000 ≤
      |u/(u+v+b)-x/(x+y+a)| + |v/(u+v+b)-y/(x+y+a)| := by
  have ht : 0 < x+y+a := by linarith
  have hs : 0 < u+v+b := by linarith
  have hlo : 100*(y/(x+y+a)) ≤ 3*(x/(x+y+a)+y/(x+y+a)) := by
    have h := div_le_div_of_nonneg_right hl (le_of_lt ht)
    convert h using 1 <;> ring
  have hhi : u/(u+v+b)+v/(u+v+b) ≤ 20*(v/(u+v+b)) := by
    have h := div_le_div_of_nonneg_right hh (le_of_lt hs)
    convert h using 1 <;> ring
  have hm : (3:ℝ)/440 ≤ x/(x+y+a)+y/(x+y+a) := by
    convert module_mass_lower (x+y) a hxl ha ha' using 1
    ring
  exact normalized_local_separation _ _ _ _ hlo hhi hm

theorem full_composition_gap (x y u v a₁ a₂ b₁ b₂ : ℝ)
    (hl : 100*y ≤ 3*(x+y)) (hh : u+v ≤ 20*v)
    (hxl : 6 ≤ x+y) (hxh : 6 ≤ u+v)
    (ha : 0 ≤ a₁+a₂) (ha' : a₁+a₂ ≤ 874) (hb : 0 ≤ b₁+b₂) :
    (3:ℝ)/22000 ≤
      |u/(u+v+(b₁+b₂))-x/(x+y+(a₁+a₂))| +
      |v/(u+v+(b₁+b₂))-y/(x+y+(a₁+a₂))| +
      |b₁/(u+v+(b₁+b₂))-a₁/(x+y+(a₁+a₂))| +
      |b₂/(u+v+(b₁+b₂))-a₂/(x+y+(a₁+a₂))| := by
  have h := composition_gap x y u v (a₁+a₂) (b₁+b₂) hl hh hxl hxh ha ha' hb
  have h₁ := abs_nonneg (b₁/(u+v+(b₁+b₂))-a₁/(x+y+(a₁+a₂)))
  have h₂ := abs_nonneg (b₂/(u+v+(b₁+b₂))-a₂/(x+y+(a₁+a₂)))
  linarith

end SmallResidentCompositionCopying
