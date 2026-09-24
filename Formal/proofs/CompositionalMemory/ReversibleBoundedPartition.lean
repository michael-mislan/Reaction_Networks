import proofs.CompositionalMemory.BoundedPartition

namespace CompositionalMemory
open Classical FiniteIntegerRows ControlledRows

theorem bounded_reversible_partition (x y : Nat) (col : Fin 2) :
    (∑ a : Fin 849, ∑ b : Fin 213,
      if controlledBothNewborn 53 col.val x y a.val b.val then widePartitionWeight x y a.val b.val else 0)=
      terminalReward 53 x y col.val := by
  fin_cases col
  · have hp (a b : Nat) : controlledBothNewborn 53 0 x y a b ↔
        (6 ≤ a ∧ a ≤ 106 ∧ 6 ≤ x-a ∧ x-a ≤ 106) ∧
        (0 ≤ b ∧ b ≤ 8 ∧ 0 ≤ y-b ∧ y-b ≤ 8) := by
      unfold controlledBothNewborn newborn
      norm_num
      omega
    simp_rw [hp]
    simpa [terminalReward] using bounded_separable_partition_reward x y 6 106 0 8 849 213
      (by norm_num) (by norm_num)
  · have hp (a b : Nat) : controlledBothNewborn 53 1 x y a b ↔
        (371 ≤ a ∧ a ≤ 742 ∧ 371 ≤ x-a ∧ x-a ≤ 742) ∧
        (6 ≤ b ∧ b ≤ 132 ∧ 6 ≤ y-b ∧ y-b ≤ 132) := by
      unfold controlledBothNewborn newborn
      norm_num
      omega
    simp_rw [hp]
    simpa [terminalReward] using bounded_separable_partition_reward x y 371 742 6 132 849 213
      (by norm_num) (by norm_num)

end CompositionalMemory
