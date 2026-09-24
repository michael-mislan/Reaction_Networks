import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace EvolutionaryRescue

theorem regret_lower_bound (a b p : ℝ) (ha : 0<a) (hb : 0<b) :
    a*b/(a+b) ≤ max (p*a) ((1-p)*b) := by
  have hab : 0<a+b := by positivity
  by_cases h : b/(a+b) ≤ p
  · apply le_trans _ (le_max_left _ _)
    apply (div_le_iff₀ hab).2
    have hp := (div_le_iff₀ hab).1 h
    nlinarith [mul_nonneg (le_of_lt ha) (sub_nonneg.mpr hp)]
  · apply le_trans _ (le_max_right _ _)
    apply (div_le_iff₀ hab).2
    have hp : p*(a+b)≤b := (le_div_iff₀ hab).1 (le_of_lt (lt_of_not_ge h))
    nlinarith [mul_nonneg (le_of_lt hb) (sub_nonneg.mpr hp)]

theorem regret_equalizer (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (b/(a+b))*a=a*b/(a+b) ∧ (1-b/(a+b))*b=a*b/(a+b) := by
  have hab : a+b≠0 := ne_of_gt (add_pos ha hb)
  constructor
  · field_simp [hab]
  · field_simp [hab]
    ring

end EvolutionaryRescue
