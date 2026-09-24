import proofs.CompositionalMemory.ControlledTerminalTransport
import proofs.CompositionalMemory.WidePartitionLaw

namespace CompositionalMemory
open Classical FiniteIntegerRows ControlledRows

def controlledBothNewborn (N col x y a b : Nat) : Prop :=
  newborn N col a b ∧ newborn N col (x-a) (y-b)

theorem controlled_newborn_disjoint (N : Nat) (hN : 0 < N) (x y : Nat) :
    ¬(newborn N 0 x y ∧ newborn N 1 x y) := by
  unfold newborn
  omega

theorem controlled_exact_partition_probability (N x y : Nat) (col : Fin 2) :
    (∑ a ∈ Finset.range (x+1), ∑ b ∈ Finset.range (y+1),
      if controlledBothNewborn N col.val x y a b then widePartitionWeight x y a b else 0)=
      terminalReward N x y col.val := by
  fin_cases col
  · have hp (a b : Nat) : controlledBothNewborn N 0 x y a b ↔
        ((N+9)/10 ≤ a ∧ a ≤ 2*N ∧ (N+9)/10 ≤ x-a ∧ x-a ≤ 2*N) ∧
        (0 ≤ b ∧ b ≤ 4*N/25 ∧ 0 ≤ y-b ∧ y-b ≤ 4*N/25) := by
      unfold controlledBothNewborn newborn
      omega
    simp_rw [hp]
    simpa only [terminalReward,if_pos rfl] using
      separable_partition_reward x y ((N+9)/10) (2*N) 0 (4*N/25)
  · have hp (a b : Nat) : controlledBothNewborn N 1 x y a b ↔
        (7*N ≤ a ∧ a ≤ 14*N ∧ 7*N ≤ x-a ∧ x-a ≤ 14*N) ∧
        ((N+9)/10 ≤ b ∧ b ≤ 25*N/10 ∧ (N+9)/10 ≤ y-b ∧ y-b ≤ 25*N/10) := by
      unfold controlledBothNewborn newborn
      omega
    simp_rw [hp]
    simpa [terminalReward] using
      separable_partition_reward x y (7*N) (14*N) ((N+9)/10) (25*N/10)

noncomputable def coupledPartitionWeight (x0 y0 x1 y1 a0 b0 a1 b1 : Nat) : ℝ :=
  widePartitionWeight x0 y0 a0 b0*widePartitionWeight x1 y1 a1 b1

theorem coupledPartitionWeight_nonneg (x0 y0 x1 y1 a0 b0 a1 b1 : Nat) :
    0 ≤ coupledPartitionWeight x0 y0 x1 y1 a0 b0 a1 b1 :=
  mul_nonneg (widePartitionWeight_nonneg _ _ _ _) (widePartitionWeight_nonneg _ _ _ _)

theorem coupledPartitionWeight_sum (x0 y0 x1 y1 : Nat) :
    (∑ a0 ∈ Finset.range (x0+1), ∑ b0 ∈ Finset.range (y0+1),
      ∑ a1 ∈ Finset.range (x1+1), ∑ b1 ∈ Finset.range (y1+1),
      coupledPartitionWeight x0 y0 x1 y1 a0 b0 a1 b1)=1 := by
  simp only [coupledPartitionWeight,← Finset.mul_sum,widePartitionWeight_sum,mul_one]

/-- Exact four-species partition probability. Species allocations are
independent, while the two siblings are complementary in every coordinate. -/
theorem coupled_exact_partition_probability (N x0 y0 x1 y1 : Nat) (word : Fin 2 → Fin 2) :
    (∑ a0 ∈ Finset.range (x0+1), ∑ b0 ∈ Finset.range (y0+1),
      ∑ a1 ∈ Finset.range (x1+1), ∑ b1 ∈ Finset.range (y1+1),
      if controlledBothNewborn N (word 0).val x0 y0 a0 b0 ∧
         controlledBothNewborn N (word 1).val x1 y1 a1 b1
      then coupledPartitionWeight x0 y0 x1 y1 a0 b0 a1 b1 else 0)=
    terminalReward N x0 y0 (word 0).val*terminalReward N x1 y1 (word 1).val := by
  have he (a0 b0 a1 b1 : Nat) :
      (if controlledBothNewborn N (word 0).val x0 y0 a0 b0 ∧
          controlledBothNewborn N (word 1).val x1 y1 a1 b1
       then coupledPartitionWeight x0 y0 x1 y1 a0 b0 a1 b1 else 0)=
      (if controlledBothNewborn N (word 0).val x0 y0 a0 b0 then widePartitionWeight x0 y0 a0 b0 else 0)*
      (if controlledBothNewborn N (word 1).val x1 y1 a1 b1 then widePartitionWeight x1 y1 a1 b1 else 0) := by
    unfold coupledPartitionWeight
    split_ifs <;> simp_all
  simp_rw [he]
  simp only [← Finset.mul_sum,controlled_exact_partition_probability]
  simp only [← Finset.sum_mul,controlled_exact_partition_probability]

end CompositionalMemory
