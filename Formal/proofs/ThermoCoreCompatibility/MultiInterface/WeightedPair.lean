import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

namespace ThermoCoreCompatibility.MultiInterface

structure Factors where
  a : ℝ
  b : ℝ
  a_pos : 0 < a
  b_pos : 0 < b

namespace Factors

variable (w : Factors)

noncomputable def lower (x : ℝ) : ℝ := (w.a*x+2*w.b*x^2)/(w.a+2*w.b)
noncomputable def upper (x : ℝ) : ℝ := (w.a*x+w.b*x^2)/(w.a+w.b)
def Productive (x y : ℝ) : Prop :=
  0 < 2*(w.b*(y-x^2))-w.a*(x-y) ∧ 0 < w.a*(x-y)-w.b*(y-x^2)

theorem lower_den_pos : 0 < w.a+2*w.b := by have := w.a_pos; have := w.b_pos; positivity
theorem upper_den_pos : 0 < w.a+w.b := add_pos w.a_pos w.b_pos

theorem residual_lower (x y : ℝ) :
    2*(w.b*(y-x^2))-w.a*(x-y) = (w.a+2*w.b)*(y-w.lower x) := by
  unfold lower
  field_simp [ne_of_gt w.lower_den_pos]
  ring

theorem residual_upper (x y : ℝ) :
    w.a*(x-y)-w.b*(y-x^2) = (w.a+w.b)*(w.upper x-y) := by
  unfold upper
  field_simp [ne_of_gt w.upper_den_pos]
  ring

theorem productive_iff (x y : ℝ) : w.Productive x y ↔ w.lower x < y ∧ y < w.upper x := by
  unfold Productive
  rw [w.residual_lower, w.residual_upper]
  simp only [mul_pos_iff_of_pos_left w.lower_den_pos,
    mul_pos_iff_of_pos_left w.upper_den_pos, sub_pos]

theorem currents_positive {x y : ℝ} (h : w.Productive x y) :
    0 < w.a*(x-y) ∧ 0 < w.b*(y-x^2) := by
  obtain ⟨h₁,h₂⟩ := h
  constructor <;> linarith

theorem decreases {x y : ℝ} (h : w.Productive x y) : y < x := by
  have hh := (w.currents_positive h).1
  exact sub_pos.mp ((mul_pos_iff_of_pos_left w.a_pos).mp hh)

theorem gap (x : ℝ) :
    w.upper x-w.lower x = w.a*w.b*x*(1-x)/((w.a+w.b)*(w.a+2*w.b)) := by
  unfold upper lower
  have hd : w.a+w.b*2 ≠ 0 := by nlinarith [w.a_pos, w.b_pos]
  field_simp [ne_of_gt w.lower_den_pos, ne_of_gt w.upper_den_pos, hd]
  ring

theorem lower_lt_upper {x : ℝ} (hx : 0 < x) (hx1 : x < 1) : w.lower x < w.upper x := by
  have : 0 < w.upper x-w.lower x := by
    rw [w.gap]
    exact div_pos (mul_pos (mul_pos (mul_pos w.a_pos w.b_pos) hx) (sub_pos.mpr hx1))
      (mul_pos w.upper_den_pos w.lower_den_pos)
  linarith

@[simp] theorem lower_zero : w.lower 0 = 0 := by simp [lower]
@[simp] theorem upper_zero : w.upper 0 = 0 := by simp [upper]
@[simp] theorem lower_one : w.lower 1 = 1 := by simp [lower, ne_of_gt w.lower_den_pos]
@[simp] theorem upper_one : w.upper 1 = 1 := by simp [upper, ne_of_gt w.upper_den_pos]

theorem lower_strictMono : StrictMonoOn w.lower (Set.Ici 0) := by
  intro x hx y hy hxy
  unfold lower
  apply (div_lt_div_iff_of_pos_right w.lower_den_pos).2
  have hs : x^2 ≤ y^2 := (sq_le_sq₀ hx hy).2 hxy.le
  have hp := mul_lt_mul_of_pos_left hxy w.a_pos
  have hq := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*w.b by have := w.b_pos; positivity)
  linarith

theorem upper_strictMono : StrictMonoOn w.upper (Set.Ici 0) := by
  intro x hx y hy hxy
  unfold upper
  apply (div_lt_div_iff_of_pos_right w.upper_den_pos).2
  have hs : x^2 ≤ y^2 := (sq_le_sq₀ hx hy).2 hxy.le
  have hp := mul_lt_mul_of_pos_left hxy w.a_pos
  have hq := mul_le_mul_of_nonneg_left hs w.b_pos.le
  linarith

theorem lower_pos {x : ℝ} (hx : 0 < x) : 0 < w.lower x := by
  simpa using w.lower_strictMono (by simp) hx.le hx

theorem upper_lt_self {x : ℝ} (hx : 0 < x) (hx1 : x < 1) : w.upper x < x := by
  unfold upper
  apply (div_lt_iff₀ w.upper_den_pos).2
  have hs : x^2 < x := by nlinarith
  have := mul_lt_mul_of_pos_left hs w.b_pos
  nlinarith

theorem continuous_lower : Continuous w.lower := by unfold lower; fun_prop
theorem continuous_upper : Continuous w.upper := by unfold upper; fun_prop

end Factors
end ThermoCoreCompatibility.MultiInterface
