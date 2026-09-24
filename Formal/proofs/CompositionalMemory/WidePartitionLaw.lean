import proofs.CompositionalMemory.WidePayoffBounds
import proofs.HeritableCompositions.BinomialMoment

namespace CompositionalMemory
open Classical FiniteIntegerRows HeritableCompositions
set_option maxHeartbeats 60000

noncomputable def widePartitionWeight (x y a b : Nat) : ℝ :=
  fairBinomialWeight x a*fairBinomialWeight y b

theorem widePartitionWeight_nonneg (x y a b : Nat) : 0 ≤ widePartitionWeight x y a b :=
  mul_nonneg (fairBinomialWeight_nonneg _ _) (fairBinomialWeight_nonneg _ _)

theorem widePartitionWeight_sum (x y : Nat) :
    (∑ a ∈ Finset.range (x+1), ∑ b ∈ Finset.range (y+1), widePartitionWeight x y a b)=1 := by
  simp only [widePartitionWeight,← Finset.mul_sum,fair_binomial_sum,mul_one]

def wideBothNewborn (col x y a b : Nat) : Prop :=
  wideNewborn col a b ∧ wideNewborn col (x-a) (y-b)

theorem wide_newborn_disjoint (x y : Nat) : ¬(wideNewborn 0 x y ∧ wideNewborn 1 x y) := by
  unfold wideNewborn
  omega

theorem splitNumerator_probability (n lo hi : Nat) :
    (∑ a ∈ Finset.range (n+1),
      if lo ≤ a ∧ a ≤ hi ∧ lo ≤ n-a ∧ n-a ≤ hi then fairBinomialWeight n a else 0)=
    (splitNumerator n lo hi : ℝ)/(2 : ℝ)^n := by
  simp only [splitNumerator,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,fairBinomialWeight]
  rw [Finset.sum_div]
  simp only [ite_div,zero_div]

theorem separable_partition_reward (x y loX hiX loY hiY : Nat) :
    (∑ a ∈ Finset.range (x+1), ∑ b ∈ Finset.range (y+1),
      if (loX ≤ a ∧ a ≤ hiX ∧ loX ≤ x-a ∧ x-a ≤ hiX) ∧
         (loY ≤ b ∧ b ≤ hiY ∧ loY ≤ y-b ∧ y-b ≤ hiY)
      then widePartitionWeight x y a b else 0) =
    (splitNumerator x loX hiX : ℝ)*(splitNumerator y loY hiY : ℝ)/(2 : ℝ)^(x+y) := by
  have he : (∑ a ∈ Finset.range (x+1), ∑ b ∈ Finset.range (y+1),
      if (loX ≤ a ∧ a ≤ hiX ∧ loX ≤ x-a ∧ x-a ≤ hiX) ∧
         (loY ≤ b ∧ b ≤ hiY ∧ loY ≤ y-b ∧ y-b ≤ hiY)
      then widePartitionWeight x y a b else 0) =
      (∑ a ∈ Finset.range (x+1), if loX ≤ a ∧ a ≤ hiX ∧ loX ≤ x-a ∧ x-a ≤ hiX
        then fairBinomialWeight x a else 0)*
      (∑ b ∈ Finset.range (y+1), if loY ≤ b ∧ b ≤ hiY ∧ loY ≤ y-b ∧ y-b ≤ hiY
        then fairBinomialWeight y b else 0) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    unfold widePartitionWeight
    split_ifs <;> simp_all
  rw [he,splitNumerator_probability,splitNumerator_probability,pow_add]
  exact div_mul_div_comm _ _ _ _

/-- The reward is the exact probability that both complementary daughters
return to the same specified newborn region. The two siblings are not
sampled independently; their molecule counts add to the parent counts. -/
theorem wide_exact_partition_probability (col x y : Nat) (hc : col=0 ∨ col=1) :
    (∑ a ∈ Finset.range (x+1), ∑ b ∈ Finset.range (y+1),
      if wideBothNewborn col x y a b then widePartitionWeight x y a b else 0)=
    exactTerminalReward x y col := by
  classical
  rcases hc with rfl | rfl
  · have hp (a b : Nat) : wideBothNewborn 0 x y a b ↔
        (3 ≤ a ∧ a ≤ 50 ∧ 3 ≤ x-a ∧ x-a ≤ 50) ∧
        (0 ≤ b ∧ b ≤ 4 ∧ 0 ≤ y-b ∧ y-b ≤ 4) := by
      unfold wideBothNewborn wideNewborn
      omega
    simp_rw [hp]
    simpa only [exactTerminalReward,if_pos rfl] using separable_partition_reward x y 3 50 0 4
  · have hp (a b : Nat) : wideBothNewborn 1 x y a b ↔
        (175 ≤ a ∧ a ≤ 350 ∧ 175 ≤ x-a ∧ x-a ≤ 350) ∧
        (3 ≤ b ∧ b ≤ 62 ∧ 3 ≤ y-b ∧ y-b ≤ 62) := by
      unfold wideBothNewborn wideNewborn
      omega
    simp_rw [hp]
    simpa [exactTerminalReward] using separable_partition_reward x y 175 350 3 62

end CompositionalMemory
