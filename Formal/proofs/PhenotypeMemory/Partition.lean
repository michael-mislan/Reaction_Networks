import proofs.HeritableCompositions.BinomialMoment

namespace PhenotypeMemory
open HeritableCompositions

noncomputable def jointWeight (a r i j : ℕ) : ℝ :=
  fairBinomialWeight a i * fairBinomialWeight r j

theorem joint_partition_normalized (a r : ℕ) :
    ∑ i ∈ Finset.range (a+1), ∑ j ∈ Finset.range (r+1),
      jointWeight a r i j = 1 := by
  simp only [jointWeight, ← Finset.mul_sum, fair_binomial_sum, mul_one]

theorem joint_partition_nonnegative (a r i j : ℕ) :
    0 ≤ jointWeight a r i j :=
  mul_nonneg (fairBinomialWeight_nonneg a i) (fairBinomialWeight_nonneg r j)

theorem daughter_material (a r i j N : ℕ)
    (h : a+r ≤ N) (hi : i ≤ a) (hj : j ≤ r) :
    i+(a-i)=a ∧ j+(r-j)=r ∧ i+j ≤ N ∧ (a-i)+(r-j) ≤ N := by
  omega

theorem reset_probability (a r : ℕ) :
    jointWeight a r 0 0 = 1/(2:ℝ)^(a+r) := by
  simp [jointWeight, fairBinomialWeight, pow_add, mul_comm]

theorem reset_lower_bound (a r N : ℕ) (h : a+r ≤ N) :
    1/(2:ℝ)^N ≤ jointWeight a r 0 0 := by
  rw [reset_probability]
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) h)

/-- Realized complementary two-mark partition, without assuming sister independence. -/
theorem two_mark_dependence :
    jointWeight 2 0 1 0 = 1/2 ∧
    jointWeight 2 0 1 0 + jointWeight 2 0 2 0 = 3/4 ∧
    (3/4:ℝ)^2 - jointWeight 2 0 1 0 = 1/16 := by
  norm_num [jointWeight, fairBinomialWeight, Nat.choose]

end PhenotypeMemory
