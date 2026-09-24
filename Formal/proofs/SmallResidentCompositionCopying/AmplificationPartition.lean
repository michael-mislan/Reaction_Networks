import proofs.SmallResidentCompositionCopying.AmplificationDeadline
import proofs.HeritableCompositions.BinomialMoment

namespace SmallResidentCompositionCopying.Amplification
open Classical FiniteCopy CompositionalMemory HeritableCompositions
noncomputable section

def goodAllocation (a b : ℕ) : Prop :=
  (1 ≤ a ∧ a ≤ 19 ∧ 1 ≤ 20-a ∧ 20-a ≤ 19) ∧
  (1 ≤ b ∧ b ≤ 19 ∧ 1 ≤ 20-b ∧ 20-b ≤ 19)

def allocationWeight (a b : ℕ) : ℝ := fairBinomialWeight 20 a * fairBinomialWeight 20 b

theorem allocation_normalized :
    (∑ a ∈ Finset.range 21, ∑ b ∈ Finset.range 21, allocationWeight a b) = 1 := by
  simp only [allocationWeight,← Finset.mul_sum]
  norm_num [show 21=20+1 by norm_num,fair_binomial_sum]

theorem one_module_partition :
    (∑ a ∈ Finset.range 21,
      if 1 ≤ a ∧ a ≤ 19 ∧ 1 ≤ 20-a ∧ 20-a ≤ 19 then fairBinomialWeight 20 a else 0) =
    (1048574:ℝ)/1048576 := by
  norm_num [Finset.sum_range_succ,fairBinomialWeight,Nat.choose]

/-- The product concerns allocations of distinct molecules in the two modules.
Each summand already tests both complementary siblings. -/
theorem exact_partition :
    (∑ a ∈ Finset.range 21, ∑ b ∈ Finset.range 21,
      if goodAllocation a b then allocationWeight a b else 0) = partitionSuccess := by
  have h : (∑ a ∈ Finset.range 21, ∑ b ∈ Finset.range 21,
      if goodAllocation a b then allocationWeight a b else 0) =
      (∑ a ∈ Finset.range 21,
        if 1 ≤ a ∧ a ≤ 19 ∧ 1 ≤ 20-a ∧ 20-a ≤ 19 then fairBinomialWeight 20 a else 0)^2 := by
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    unfold goodAllocation allocationWeight
    split_ifs <;> simp_all
  rw [h,one_module_partition]
  rfl

def daughterCounts (a b : ℕ) (h : goodAllocation a b) : Counts :=
  (⟨a-1,by rcases h with ⟨⟨_,_,_,_⟩,_⟩; omega⟩,
   ⟨b-1,by rcases h with ⟨_,⟨_,_,_,_⟩⟩; omega⟩)

def complementCounts (a b : ℕ) (h : goodAllocation a b) : Counts :=
  (⟨20-a-1,by rcases h with ⟨⟨_,_,_,_⟩,_⟩; omega⟩,
   ⟨20-b-1,by rcases h with ⟨_,⟨_,_,_,_⟩⟩; omega⟩)

def newborn (z : Counts) : Prop := z.1.val < 19 ∧ z.2.val < 19

theorem daughters_restart (a b : ℕ) (h : goodAllocation a b) :
    newborn (daughterCounts a b h) ∧ newborn (complementCounts a b h) := by
  rcases h with ⟨⟨_,_,_,_⟩,⟨_,_,_,_⟩⟩
  dsimp [newborn,daughterCounts,complementCounts]
  omega

theorem complementary_counts (a b : ℕ) (h : goodAllocation a b) :
    ((daughterCounts a b h).1.val+1)+((complementCounts a b h).1.val+1)=20 ∧
    ((daughterCounts a b h).2.val+1)+((complementCounts a b h).2.val+1)=20 := by
  rcases h with ⟨⟨_,_,_,_⟩,⟨_,_,_,_⟩⟩
  dsimp [daughterCounts,complementCounts]
  omega

end
end SmallResidentCompositionCopying.Amplification
