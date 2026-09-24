import proofs.CompositionalMemory.CoupledPartitionLaw

namespace CompositionalMemory
open Classical FiniteIntegerRows ControlledRows HeritableCompositions

theorem sum_range_eq_of_two_support_bounds (f : Nat → ℝ) (A B : Nat)
    (hA : ∀ i, A ≤ i → f i=0) (hB : ∀ i, B ≤ i → f i=0) :
    (∑ i ∈ Finset.range A,f i)=∑ i ∈ Finset.range B,f i := by
  by_cases hAB : A ≤ B
  · apply Finset.sum_subset (Finset.range_mono hAB)
    intro i _ hi
    exact hA i (by simpa only [Finset.mem_range,not_lt] using hi)
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega : B ≤ A))
    intro i _ hi
    exact hB i (by simpa only [Finset.mem_range,not_lt] using hi)

theorem bounded_binomial_split (n lo hi cap : Nat) (hc : hi < cap) :
    (∑ a : Fin cap, if lo ≤ a.val ∧ a.val ≤ hi ∧ lo ≤ n-a.val ∧ n-a.val ≤ hi
      then fairBinomialWeight n a.val else 0)=(splitNumerator n lo hi : ℝ)/(2 : ℝ)^n := by
  rw [Fin.sum_univ_eq_sum_range
    (fun a : Nat => if lo ≤ a ∧ a ≤ hi ∧ lo ≤ n-a ∧ n-a ≤ hi
      then fairBinomialWeight n a else 0) cap]
  apply Eq.trans _ (splitNumerator_probability n lo hi)
  apply sum_range_eq_of_two_support_bounds
  · intro i hi'
    have hh : ¬(lo ≤ i ∧ i ≤ hi ∧ lo ≤ n-i ∧ n-i ≤ hi) := by omega
    exact if_neg hh
  · intro i hi'
    have hh : n < i := by omega
    simp [fairBinomialWeight,Nat.choose_eq_zero_of_lt hh]

theorem bounded_separable_partition_reward (x y loX hiX loY hiY capX capY : Nat)
    (hx : hiX < capX) (hy : hiY < capY) :
    (∑ a : Fin capX, ∑ b : Fin capY,
      if (loX ≤ a.val ∧ a.val ≤ hiX ∧ loX ≤ x-a.val ∧ x-a.val ≤ hiX) ∧
         (loY ≤ b.val ∧ b.val ≤ hiY ∧ loY ≤ y-b.val ∧ y-b.val ≤ hiY)
      then widePartitionWeight x y a.val b.val else 0)=
    (splitNumerator x loX hiX : ℝ)*(splitNumerator y loY hiY : ℝ)/(2 : ℝ)^(x+y) := by
  have he : (∑ a : Fin capX, ∑ b : Fin capY,
      if (loX ≤ a.val ∧ a.val ≤ hiX ∧ loX ≤ x-a.val ∧ x-a.val ≤ hiX) ∧
         (loY ≤ b.val ∧ b.val ≤ hiY ∧ loY ≤ y-b.val ∧ y-b.val ≤ hiY)
      then widePartitionWeight x y a.val b.val else 0)=
      (∑ a : Fin capX, if loX ≤ a.val ∧ a.val ≤ hiX ∧ loX ≤ x-a.val ∧ x-a.val ≤ hiX
        then fairBinomialWeight x a.val else 0)*
      (∑ b : Fin capY, if loY ≤ b.val ∧ b.val ≤ hiY ∧ loY ≤ y-b.val ∧ y-b.val ≤ hiY
        then fairBinomialWeight y b.val else 0) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    unfold widePartitionWeight
    split_ifs <;> simp_all
  rw [he,bounded_binomial_split _ _ _ _ hx,bounded_binomial_split _ _ _ _ hy,pow_add]
  exact div_mul_div_comm _ _ _ _

theorem bounded_controlled_partition (x y : Nat) (col : Fin 2) :
    (∑ a : Fin 753, ∑ b : Fin 189,
      if controlledBothNewborn 47 col.val x y a.val b.val then widePartitionWeight x y a.val b.val else 0)=
      terminalReward 47 x y col.val := by
  fin_cases col
  · have hp (a b : Nat) : controlledBothNewborn 47 0 x y a b ↔
        (5 ≤ a ∧ a ≤ 94 ∧ 5 ≤ x-a ∧ x-a ≤ 94) ∧
        (0 ≤ b ∧ b ≤ 7 ∧ 0 ≤ y-b ∧ y-b ≤ 7) := by
      unfold controlledBothNewborn newborn
      norm_num
      omega
    simp_rw [hp]
    simpa [terminalReward] using bounded_separable_partition_reward x y 5 94 0 7 753 189
      (by norm_num) (by norm_num)
  · have hp (a b : Nat) : controlledBothNewborn 47 1 x y a b ↔
        (329 ≤ a ∧ a ≤ 658 ∧ 329 ≤ x-a ∧ x-a ≤ 658) ∧
        (5 ≤ b ∧ b ≤ 117 ∧ 5 ≤ y-b ∧ y-b ≤ 117) := by
      unfold controlledBothNewborn newborn
      norm_num
      omega
    simp_rw [hp]
    simpa [terminalReward] using bounded_separable_partition_reward x y 329 658 5 117 753 189
      (by norm_num) (by norm_num)

end CompositionalMemory
