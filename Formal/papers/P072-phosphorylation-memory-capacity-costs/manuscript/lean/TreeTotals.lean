import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace PhosphorylationMemory

/-- The denominator identity that makes positivity automatic in the regular chart. -/
theorem denominator_split (b d r u : ℝ) :
    b - u*d = (b-r*d)+(r-u)*d := by ring

/-- Eliminating the common free-enzyme concentration from the two totals. -/
theorem ratio_loading (b d r u s : ℝ)
    (h : u*(1+s*b)=r*(1+s*u*d)) : s*u*(b-r*d)=r-u := by
  nlinarith [h]

/-- Positive exceptional-ratio derivative: no continuum is hidden at 0/0. -/
theorem exceptional_derivative (a f u b d s : ℝ)
    (ha : 0<a) (hf : 0<f) (hu : 0<u) (hb : 0<b) (hd : 0<d) :
    0 < a+f*u*(b+d)/(1+s*u*d)^2 := by
  have hnum : 0 ≤ f*u*(b+d) := le_of_lt (mul_pos (mul_pos hf hu) (add_pos hb hd))
  have hfrac : 0 ≤ f*u*(b+d)/(1+s*u*d)^2 := div_nonneg hnum (sq_nonneg _)
  linarith

end PhosphorylationMemory
