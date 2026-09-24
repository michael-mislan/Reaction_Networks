import proofs.ThermoCoreCompatibility.MultiInterface.WeightedPair

namespace ThermoCoreCompatibility.MultiInterface

def ru (a b x y f : ℝ) := 2*b*(f*y-x^2)-a*(x-y)
def rv (a b x y f : ℝ) := a*(x-y)-b*(f*y-x^2)

theorem activity_corner (a b x y f Lx Ux Ly Uy fl fu : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ Lx) (hy : 0 ≤ Ly) (hf : 0 ≤ fl)
    (hxl : Lx ≤ x) (hxu : x ≤ Ux) (hyl : Ly ≤ y) (hyu : y ≤ Uy)
    (hfl : fl ≤ f) (hfu : f ≤ fu) :
    ru a b Ux Ly fl ≤ ru a b x y f ∧ rv a b Lx Uy fu ≤ rv a b x y f := by
  have hx0 : 0 ≤ x := le_trans hx hxl
  have hy0 : 0 ≤ y := le_trans hy hyl
  have hf0 : 0 ≤ f := le_trans hf hfl
  have hs₁ : x^2 ≤ Ux^2 := (sq_le_sq₀ hx0 (le_trans hx0 hxu)).2 hxu
  have hs₂ : Lx^2 ≤ x^2 := (sq_le_sq₀ hx hx0).2 hxl
  have hm₁ : fl*Ly ≤ f*y := mul_le_mul hfl hyl hy hf0
  have hm₂ : f*y ≤ fu*Uy := mul_le_mul hfu hyu hy0 (le_trans hf0 hfu)
  have ba₁ := mul_le_mul_of_nonneg_left hs₁ hb
  have ba₂ := mul_le_mul_of_nonneg_left hs₂ hb
  have bf₁ := mul_le_mul_of_nonneg_left hm₁ hb
  have bf₂ := mul_le_mul_of_nonneg_left hm₂ hb
  have ax₁ := mul_le_mul_of_nonneg_left hxu ha
  have ax₂ := mul_le_mul_of_nonneg_left hxl ha
  have ay₁ := mul_le_mul_of_nonneg_left hyl ha
  have ay₂ := mul_le_mul_of_nonneg_left hyu ha
  dsimp [ru,rv]
  constructor <;> nlinarith

theorem affine_interval_lower (c t l u m z : ℝ) (hl : l ≤ z) (hu : z ≤ u)
    (h₁ : m ≤ c*l+t) (h₂ : m ≤ c*u+t) : m ≤ c*z+t := by
  by_cases hc : 0 ≤ c
  · have := mul_le_mul_of_nonneg_left hl hc; linarith
  · have := mul_le_mul_of_nonpos_left hu (le_of_not_ge hc); linarith

theorem factor_corners (c d a b al au bl bu m : ℝ)
    (ha : al ≤ a) (ha' : a ≤ au) (hb : bl ≤ b) (hb' : b ≤ bu)
    (h₁ : m ≤ c*al+d*bl) (h₂ : m ≤ c*al+d*bu)
    (h₃ : m ≤ c*au+d*bl) (h₄ : m ≤ c*au+d*bu) : m ≤ c*a+d*b := by
  have hL : m ≤ c*al+d*b := by
    have := affine_interval_lower d (c*al) bl bu m b hb hb' (by linarith) (by linarith)
    linarith
  have hU : m ≤ c*au+d*b := by
    have := affine_interval_lower d (c*au) bl bu m b hb hb' (by linarith) (by linarith)
    linarith
  exact affine_interval_lower c (d*b) al au m a ha ha' hL hU

end ThermoCoreCompatibility.MultiInterface
