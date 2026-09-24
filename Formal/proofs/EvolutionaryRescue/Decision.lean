import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace EvolutionaryRescue

/-- These are presentation-interval arithmetic, not assumed ODE enclosures. -/
theorem displayed_interval_margins :
    (969581567445558/10^15:ℚ)-969579866104742/10^15 > 16/10^7 ∧
    (969623237350068/10^15:ℚ)-969621466763781/10^15 > 16/10^7 := by
  norm_num

theorem robustness_reserve : (180:ℚ)/10^9 < 16/10^7 := by norm_num

theorem attained_target_arithmetic : (1:ℚ)-969581567445558/10^15 < 31/1000 := by
  norm_num

theorem feasibility_floor_arithmetic : (99:ℚ)/100/2105 > 47/100000 := by norm_num

/-- A scalar error-to-decision implication; the source errors are certified separately. -/
theorem decision_preserved (qa qb ia ib ea eb : ℝ)
    (ha : ia-ea≤qa) (hb : qb≤ib+eb) (hm : ib+eb<ia-ea) : qb<qa := by
  linarith

end EvolutionaryRescue
