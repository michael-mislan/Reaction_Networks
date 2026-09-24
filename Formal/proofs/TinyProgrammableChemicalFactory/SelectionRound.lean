import Mathlib

namespace TinyProgrammableChemicalFactory

def discardedTail (cutoff : ℕ) : ℚ :=
  (1+∑ j ∈ Finset.range 21, if cutoff<j then ((20 : ℕ).choose j : ℚ) else 0)/2^20

theorem selection_five_four :
    1-(20 : ℚ)/5000-discardedTail 16=16297339/16384000 := by
  norm_num [discardedTail,Finset.sum_range_succ,Nat.choose]

theorem selection_four_three :
    1-(20 : ℚ)/5000-discardedTail 15=129773087/131072000 := by
  norm_num [discardedTail,Finset.sum_range_succ,Nat.choose]

theorem robust_readout (g b mg mb : ℤ)
    (hg : 4≤g) (hb : b≤1)
    (heg : |mg-g|≤1) (heb : |mb-b|≤1) :
    (3 : ℤ) ≤ mg ∧ mb < 3 := by
  rw [abs_le] at heg heb
  omega

end TinyProgrammableChemicalFactory
