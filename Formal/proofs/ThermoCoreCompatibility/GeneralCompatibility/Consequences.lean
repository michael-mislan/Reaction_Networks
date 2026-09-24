import proofs.ThermoCoreCompatibility.BeyondJunction.MarginTransfer
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Quantitative consequences used in the paper: one-sided rational rounding,
the capacity ceiling, monotonicity of the responses in the kinetic ratio with
the sharp robustness obstruction, and the response band for cores of order `d`.
-/

namespace ThermoCoreCompatibility.GeneralCompatibility

open MultiInterface BeyondJunction

/-- Downward rounding loses `η` on the lower side and `2η` on the upper side. -/
theorem round_down_margin (w : Factors) {zu zv qu qv t η : ℝ}
    (hqu0 : 0 ≤ qu) (hquz : qu ≤ zu) (hzu1 : zu ≤ 1) (hu : zu - qu ≤ η)
    (hqvz : qv ≤ zv) (hv : zv - qv ≤ η)
    (hlow : w.lower zu + t ≤ zv) (hup : zv + t ≤ w.upper zu) :
    w.lower qu + (t - η) ≤ qv ∧ qv + (t - 2*η) ≤ w.upper qu := by
  have hzu0 : 0 ≤ zu := hqu0.trans hquz
  have hmono : w.lower qu ≤ w.lower zu :=
    w.lower_strictMono.monotoneOn hqu0 hzu0 hquz
  have hlip := upper_lipschitz w (x := zu) (y := qu)
    ⟨hzu0, hzu1⟩ ⟨hqu0, hquz.trans hzu1⟩
  have habs : |zu - qu| = zu - qu := abs_of_nonneg (sub_nonneg.mpr hquz)
  rw [habs] at hlip
  have h1 := (abs_le.mp hlip).2
  constructor <;> linarith

/-- The smaller normalized residual is at most half the band width, and the
band width is at most `ab / (4 (a+b)(a+2b))`. -/
theorem min_residual_le_capacity (w : Factors) (x y : ℝ) :
    min (y - w.lower x) (w.upper x - y) ≤
      w.a*w.b/(8*((w.a+w.b)*(w.a+2*w.b))) := by
  have hgap := w.gap x
  have hden : 0 < (w.a+w.b)*(w.a+2*w.b) := mul_pos w.upper_den_pos w.lower_den_pos
  have hab : 0 < w.a*w.b := mul_pos w.a_pos w.b_pos
  have hx : x*(1-x) ≤ 1/4 := by nlinarith [sq_nonneg (x - 1/2)]
  have hwidth : w.upper x - w.lower x ≤ w.a*w.b/(4*((w.a+w.b)*(w.a+2*w.b))) := by
    rw [hgap, div_le_div_iff₀ hden (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hx (mul_nonneg hab.le hden.le)]
  have hhalf : min (y - w.lower x) (w.upper x - y) ≤ (w.upper x - w.lower x)/2 := by
    rcases le_total (y - w.lower x) (w.upper x - y) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have heq : w.a*w.b/(4*((w.a+w.b)*(w.a+2*w.b)))/2 =
      w.a*w.b/(8*((w.a+w.b)*(w.a+2*w.b))) := by
    field_simp
    ring
  linarith [heq]

/-- Universal ceiling: `ab/((a+b)(a+2b)) ≤ 3 - 2√2`, with equality iff `a = √2 b`. -/
theorem ratio_factor_le (w : Factors) :
    w.a*w.b/((w.a+w.b)*(w.a+2*w.b)) ≤ 3 - 2*Real.sqrt 2 := by
  have hden : 0 < (w.a+w.b)*(w.a+2*w.b) := mul_pos w.upper_den_pos w.lower_den_pos
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  set s := Real.sqrt 2 with hsdef
  have hc : 0 ≤ 3 - 2*s := by nlinarith [sq_nonneg (s - 1)]
  rw [div_le_iff₀ hden]
  have hid : (3-2*s)*((w.a+w.b)*(w.a+2*w.b)) - w.a*w.b =
      (3-2*s)*(w.a - s*w.b)^2 + (2 - s*s)*(4*w.a*w.b + (3-2*s)*w.b^2) := by ring
  have hsq : 0 ≤ (3-2*s)*(w.a - s*w.b)^2 := mul_nonneg hc (sq_nonneg _)
  rw [hs] at hid
  linarith

/-- Both responses are nondecreasing in the ratio `a/b` on `[0,1]`. -/
theorem lower_mono_ratio (w₁ w₂ : Factors) (hr : w₁.a*w₂.b ≤ w₂.a*w₁.b)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : w₁.lower x ≤ w₂.lower x := by
  unfold Factors.lower
  rw [div_le_div_iff₀ w₁.lower_den_pos w₂.lower_den_pos]
  have h := mul_nonneg (mul_nonneg hx0 (sub_nonneg.mpr hx1)) (sub_nonneg.mpr hr)
  nlinarith

theorem upper_mono_ratio (w₁ w₂ : Factors) (hr : w₁.a*w₂.b ≤ w₂.a*w₁.b)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : w₁.upper x ≤ w₂.upper x := by
  unfold Factors.upper
  rw [div_le_div_iff₀ w₁.upper_den_pos w₂.upper_den_pos]
  have h := mul_nonneg (mul_nonneg hx0 (sub_nonneg.mpr hx1)) (sub_nonneg.mpr hr)
  nlinarith

/-- Robustness obstruction: if the largest ratio is at least twice the smallest,
the robust band `lower⁺ < y < upper⁻` is empty on `[0,1]`. -/
theorem robust_band_empty (wm wp : Factors) (hr : 2*(wm.a*wp.b) ≤ wp.a*wm.b)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : wm.upper x ≤ wp.lower x := by
  unfold Factors.upper Factors.lower
  rw [div_le_div_iff₀ wm.upper_den_pos wp.lower_den_pos]
  have h := mul_nonneg (mul_nonneg hx0 (sub_nonneg.mpr hx1)) (sub_nonneg.mpr hr)
  nlinarith

/-- Response band of a core of order `d`: `X_u ⇌ X_v`, `X_v + (d-1)F ⇌ d X_u`. -/
theorem order_d_band (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (d : ℕ) (hd : 1 ≤ d)
    (x y : ℝ) :
    (0 < (d:ℝ)*(b*(y - x^d)) - a*(x-y) ∧ 0 < a*(x-y) - b*(y - x^d)) ↔
      (a*x + (d:ℝ)*b*x^d)/(a + (d:ℝ)*b) < y ∧ y < (a*x + b*x^d)/(a+b) := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  have h1 : 0 < a + (d:ℝ)*b := by positivity
  have h2 : 0 < a + b := add_pos ha hb
  rw [div_lt_iff₀ h1, lt_div_iff₀ h2]
  constructor
  · rintro ⟨hu, hv⟩; constructor <;> nlinarith
  · rintro ⟨hu, hv⟩; constructor <;> nlinarith

end ThermoCoreCompatibility.GeneralCompatibility
