import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

namespace TherapeuticWindows

def expLower (x : ℚ) (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n+1), x^j / Nat.factorial j

theorem exponential_lower_certificates :
    8000 < expLower 9 25 ∧ 50 < expLower (99/25) 15 := by
  norm_num [expLower, Finset.sum_range_succ, Nat.factorial]

theorem delivered_course_arithmetic :
    (29/101 : ℚ)*(49/50) > 28/100 ∧
    (1/100 : ℚ)+29/99 < 31/100 ∧
    (89/1000 : ℚ)*108-(141/1000)*4 ≥ 9 ∧
    (29/100 : ℚ)*112 < 33 ∧
    (3248/99 : ℚ) < 33 ∧
    (3/10 : ℚ)+29/99+1/200 < 61/100 ∧
    (214/5 : ℚ)/8000 = 107/20000 ∧
    (107/20000 : ℚ) < 1/100 := by
  norm_num

end TherapeuticWindows
