import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

namespace TherapeuticWindows

def clockValue (sigma : ℕ) : ℚ :=
  ∑ j ∈ Finset.range 5, (-1 : ℚ)^j * Nat.choose 4 j *
    (∏ ell ∈ Finset.range (sigma*j), (10+ell : ℚ)/(21+ell))

theorem clock_one : clockValue 1 = 13/138 := by
  norm_num [clockValue, Finset.sum_range_succ, Finset.prod_range_succ, Nat.choose]

theorem clock_two : clockValue 2 = 1618/4347 := by
  norm_num [clockValue, Finset.sum_range_succ, Finset.prod_range_succ, Nat.choose]

theorem exclusion_certificate :
    clockValue 2 + 20*(1/1000 : ℚ)*120/4 < 49/50 := by
  rw [clock_two]
  norm_num

end TherapeuticWindows
