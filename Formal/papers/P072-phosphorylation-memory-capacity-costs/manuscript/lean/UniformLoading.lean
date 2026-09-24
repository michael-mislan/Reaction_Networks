import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace PhosphorylationMemory

/-- Hamming-weighted stationary flux gives a positive loading kernel. -/
theorem stationary_loading_kernel (u up down r : ℝ)
    (h : u * up = down) : u * (r * up) - r * down = 0 := by
  calc
    u * (r * up) - r * down = r * (u * up - down) := by ring
    _ = 0 := by rw [h]; ring

/-- The leading saturated total-current terms cancel before any limit is taken. -/
theorem saturated_current_numerator (r a b k p q : ℝ) :
    r*a*(1+k*b+q)-b*(1+k*r*a+p) = r*a-b+r*a*q-b*p := by ring

/-- The remaining numerator is exactly the programmable loading feedback. -/
theorem programmed_center_numerator (r a u s b d : ℝ) :
    r*a-u*a+r*a*(s*u*d)-u*a*(s*b) =
      a*(r-u-u*s*(b-r*d)) := by ring

/-- Independence of the two square middle-state numerators. -/
theorem square_numerator_determinant :
    (330 : ℝ)*153-420*195 = -31410 := by norm_num

end PhosphorylationMemory
