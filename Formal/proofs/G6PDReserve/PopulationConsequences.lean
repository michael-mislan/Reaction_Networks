import proofs.G6PDReserve.PopulationRoot

namespace G6PDReserve.Population
noncomputable section

theorem interval_endpoints (L U x : ℝ) :
    (U-L)/2 ≤ |x-L| ∨ (U-L)/2 ≤ |x-U| := by
  have h1 := neg_le_abs (x-U)
  have h2 := le_abs_self (x-L)
  by_contra h
  push Not at h
  linarith

theorem interval_midpoint (L U p : ℝ) (hl : L ≤ p) (hu : p ≤ U) :
    |(L+U)/2-p| ≤ (U-L)/2 := by
  rw [abs_le]
  constructor <;> linarith

theorem bulk_minimax :
    (∀ x : ℝ, ∃ p, Realized p ∧ 21/82 ≤ |x-p|) ∧
    (∀ p : ℝ, Realized p → |61/82-p| ≤ 21/82) := by
  constructor
  · intro x
    have h := interval_endpoints (20/41) 1 x
    norm_num at h
    rcases h with h | h
    · exact ⟨20/41,(sharp_bulk _).mpr ⟨le_rfl,by norm_num⟩,h⟩
    · exact ⟨1,(sharp_bulk _).mpr ⟨by norm_num,le_rfl⟩,h⟩
  · intro p hp
    have hb := (sharp_bulk p).mp hp
    have h := interval_midpoint (20/41) 1 p hb.1 hb.2
    norm_num at h
    exact h

theorem repaired_minimax :
    (∀ x : ℝ, ∃ p, RepairedRealized p ∧ 31/490 ≤ |x-p|) ∧
    (∀ p : ℝ, RepairedRealized p → |361/490-p| ≤ 31/490) := by
  constructor
  · intro x
    have h := interval_endpoints (33/49) (4/5) x
    norm_num at h
    rcases h with h | h
    · exact ⟨33/49,(sharp_repaired _).mpr ⟨le_rfl,by norm_num⟩,h⟩
    · exact ⟨4/5,(sharp_repaired _).mpr ⟨by norm_num,le_rfl⟩,h⟩
  · intro p hp
    have hb := (sharp_repaired p).mp hp
    have h := interval_midpoint (33/49) (4/5) p hb.1 hb.2
    norm_num at h
    exact h

theorem decision_requirement (p s f r su fu target lower : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hs : s ≤ su) (hf : f ≤ fu)
    (he : r = s*p+f*(1-p)) (hr : lower ≤ r)
    (hgap : 0 < su-fu) (hreq : fu+(su-fu)*target ≤ lower) : target ≤ p := by
  have h := add_le_add (mul_le_mul_of_nonneg_right hs hp)
    (mul_le_mul_of_nonneg_right hf (by linarith : 0 ≤ 1-p))
  nlinarith

theorem extra_error_budget (p s f r ε : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hs : s ≤ 1) (hf : f ≤ 1/50)
    (he : r = s*p+f*(1-p)) (hr : 17/25-ε ≤ r) (hε : ε ≤ 1/150) :
    2/3 ≤ p := by
  exact decision_requirement p s f r 1 (1/50) (2/3) (17/25-ε)
    hp hp1 hs hf he hr (by norm_num) (by linarith)

/-- A and B are successful and failing weighted masses after dividing cell
weights by their positive minimum. p is the number-weighted fraction. -/
theorem weight_conversion (p A B R : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hR : 1 ≤ R)
    (ha : p ≤ A) (haR : A ≤ R*p)
    (hb : 1-p ≤ B) (hbR : B ≤ R*(1-p)) :
    let r := A/(A+B)
    r/(R*(1-r)+r) ≤ p ∧ p ≤ R*r/(1-r+R*r) := by
  dsimp
  let r := A/(A+B)
  have hA : 0 ≤ A := le_trans hp ha
  have hB : 0 ≤ B := by linarith
  have hsum : 0 < A+B := by linarith
  have hr : 0 ≤ r := div_nonneg hA hsum.le
  have hr1 : r ≤ 1 := (div_le_iff₀ hsum).mpr (by linarith)
  have he : r*(A+B) = A := div_mul_cancel₀ A (ne_of_gt hsum)
  have hD : 0 < R*(1-r)+r := by nlinarith [mul_nonneg (by linarith : 0 ≤ R-1) (by linarith : 0 ≤ 1-r)]
  have hE : 0 < 1-r+R*r := by nlinarith [mul_nonneg (by linarith : 0 ≤ R-1) hr]
  change r/(R*(1-r)+r) ≤ p ∧ p ≤ R*r/(1-r+R*r)
  constructor
  · apply (div_le_iff₀ hD).mpr
    have h1 := mul_le_mul_of_nonneg_left hb hr
    have h2 := mul_le_mul_of_nonneg_left haR (by linarith : 0 ≤ 1-r)
    nlinarith
  · apply (le_div_iff₀ hE).mpr
    have h1 := mul_le_mul_of_nonneg_left ha (by linarith : 0 ≤ 1-r)
    have h2 := mul_le_mul_of_nonneg_left hbR hr
    nlinarith

theorem normalization_boundary (R : ℝ) (hR : 1 ≤ R) :
    (2/3 ≤ 33/(33+16*R)) ↔ R ≤ 33/32 := by
  rw [le_div_iff₀ (by linarith : 0 < 33+16*R)]
  constructor <;> intro h <;> linarith

theorem exact_consequence_constants :
    (1/50+(1-1/50)*(2/3):ℝ) = 101/150 ∧
    (17/25-101/150:ℝ) = 1/150 ∧ (33/49-2/3:ℝ) = 1/147 ∧
    (33/(33+16*(6/5)):ℝ) = 55/87 ∧ ((4*(6/5))/(1+4*(6/5)):ℝ) = 24/29 := by
  norm_num

end
end G6PDReserve.Population
