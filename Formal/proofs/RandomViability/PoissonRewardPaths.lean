import proofs.RandomViability.JumpRewardPaths

namespace RandomViability
open Classical FiniteCopy
noncomputable section
namespace FiniteLabeledKernel
variable {α β : Type*} [Fintype β] (K : FiniteLabeledKernel α β)

theorem pathTail_bounds (g : α → β → ℝ) (n : ℕ) (x : α) (s : ℝ) :
    0 ≤ K.pathTail g n x s ∧ K.pathTail g n x s ≤ 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro p _
    split_ifs
    · exact K.pathWeight_nonneg n x p
    · exact le_refl 0
  · calc
      _ ≤ ∑ p, K.pathWeight n x p := by
        apply Finset.sum_le_sum
        intro p _
        split_ifs
        · exact le_refl _
        · exact K.pathWeight_nonneg n x p
      _ = 1 := K.pathWeight_sum n x

/-- Probability of the reward event under the normalized Poisson mixture of
the finite labeled path laws. -/
def poissonPathTail (g : α → β → ℝ) (t : NNReal) (x : α) (s : ℝ) : ℝ :=
  ∑' n, poissonWeight t n * K.pathTail g n x s

theorem poissonPathTail_summable (g : α → β → ℝ) (t : NNReal) (x : α) (s : ℝ) :
    Summable (fun n => poissonWeight t n * K.pathTail g n x s) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (poissonWeight_nonneg t n) (K.pathTail_bounds g n x s).1)
    (fun n => ?_) (poissonWeight_sum t).summable
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (K.pathTail_bounds g n x s).2
    (poissonWeight_nonneg t n)

theorem poissonPathTail_bounds (g : α → β → ℝ) (t : NNReal) (x : α) (s : ℝ) :
    0 ≤ K.poissonPathTail g t x s ∧ K.poissonPathTail g t x s ≤ 1 := by
  constructor
  · exact tsum_nonneg (fun n => mul_nonneg (poissonWeight_nonneg t n) (K.pathTail_bounds g n x s).1)
  · have hh := Summable.tsum_le_tsum
      (fun n => show poissonWeight t n * K.pathTail g n x s ≤ poissonWeight t n from by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (K.pathTail_bounds g n x s).2
          (poissonWeight_nonneg t n))
      (K.poissonPathTail_summable g t x s) (poissonWeight_sum t).summable
    simpa only [poissonPathTail, (poissonWeight_sum t).tsum_eq] using hh

theorem poissonPathTail_le (g : α → β → ℝ) (hg : ∀ x b, 0 ≤ g x b)
    (t : NNReal) (x : α) (s C : ℝ) (hs : 0 < s)
    (hbound : ∀ n : ℕ, K.pathExpectation g n x ≤ (n : ℝ)*C) :
    K.poissonPathTail g t x s ≤ (t : ℝ)*C/s := by
  have hsum : HasSum (fun n : ℕ => poissonWeight t n * ((n : ℝ)*C/s)) ((t : ℝ)*C/s) := by
    convert (poissonWeight_mean t).mul_right (C/s) using 1
    · funext n
      ring
    · ring
  have hb : ∀ n : ℕ, poissonWeight t n * K.pathTail g n x s ≤
      poissonWeight t n * ((n : ℝ)*C/s) := by
    intro n
    apply mul_le_mul_of_nonneg_left _ (poissonWeight_nonneg t n)
    exact (K.pathTail_markov g hg n x s hs).trans (div_le_div_of_nonneg_right (hbound n) hs.le)
  have hh := Summable.tsum_le_tsum hb (K.poissonPathTail_summable g t x s) hsum.summable
  simpa only [poissonPathTail, hsum.tsum_eq] using hh

end FiniteLabeledKernel
end
end RandomViability
