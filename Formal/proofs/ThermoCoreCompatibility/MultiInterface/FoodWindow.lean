import proofs.ThermoCoreCompatibility.MultiInterface.OperatingBox

namespace ThermoCoreCompatibility.MultiInterface

theorem food_window (a b x y f : ℝ) (hb : 0 < b) (hy : 0 < y) :
    (0 < ru a b x y f ∧ 0 < rv a b x y f) ↔
    (x^2+a*(x-y)/(2*b))/y < f ∧ f < (x^2+a*(x-y)/b)/y := by
  rw [div_lt_iff₀ hy, lt_div_iff₀ hy]
  have hb0 : b ≠ 0 := ne_of_gt hb
  have h₂ : 2*b ≠ 0 := by positivity
  have e₁ : (a*(x-y)/(2*b))*(2*b) = a*(x-y) := div_mul_cancel₀ _ h₂
  have e₂ : (a*(x-y)/b)*b = a*(x-y) := div_mul_cancel₀ _ hb0
  dsimp [ru,rv]
  constructor <;> rintro ⟨hu,hv⟩ <;> constructor <;> nlinarith

theorem food_scaling (a b f x y : ℝ) :
    a*(f*x-f*y) = f*(a*(x-y)) ∧
    b*(f*(f*y)-(f*x)^2) = f*((b*f)*(y-x^2)) := by
  constructor <;> ring

theorem instantaneous_loss (P x D d : ℝ) (hx : 0 < x) :
    0 < P-(D+d)*x ↔ D < P/x-d := by
  have he : (P/x)*x = P := div_mul_cancel₀ _ (ne_of_gt hx)
  constructor
  · intro h
    by_contra hn
    have := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hx.le
    nlinarith
  · intro h
    have := mul_lt_mul_of_pos_right h hx
    nlinarith

end ThermoCoreCompatibility.MultiInterface
