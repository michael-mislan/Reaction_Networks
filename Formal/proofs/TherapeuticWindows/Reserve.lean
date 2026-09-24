import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace TherapeuticWindows

/-- The logistic total birth rate is at most Kr/4, without a discretization. -/
theorem logistic_cap (K h r : ℝ) (hK : 0 < K) (hr : 0 ≤ r) :
    r*h*(1-h/K) ≤ K*r/4 := by
  have hs : 0 ≤ (h-K/2)^2 := sq_nonneg _
  have base : h*(1-h/K) ≤ K/4 := by
    field_simp
    nlinarith
  nlinarith

/-- Finite telescoping factor in the excursion bound, generalized in the proof text. -/
theorem ten_step_excursion_product :
    (∏ j ∈ Finset.range 10, (20*(61/100 : ℚ)/12)/(j+1)) =
    (20*(61/100 : ℚ)/12)^10 / Nat.factorial 10 := by
  norm_num [Finset.prod_range_succ, Nat.factorial]

def reserveBound : ℚ :=
  20*(61/100)*120 * (20*(61/100)/12)^10 / Nat.factorial 10

theorem reserve_certificate : 0 < reserveBound ∧ reserveBound < 1/2000 := by
  norm_num [reserveBound, Nat.factorial]

theorem exposure_repair_algebra (charge final initial repair integral cap T : ℝ)
    (hidentity : charge = final-initial+repair*integral)
    (hfinal : final ≤ cap) (hint : integral ≤ cap*T) (hr : 0 ≤ repair) :
    charge ≤ cap-initial+repair*cap*T := by
  nlinarith

end TherapeuticWindows
