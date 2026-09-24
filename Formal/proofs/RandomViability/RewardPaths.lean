import proofs.RandomViability.KernelReward

namespace RandomViability
open Classical FiniteCopy
noncomputable section

universe u
def RewardPath (β : Type u) : ℕ → Type u
  | 0 => PUnit
  | n+1 => β × RewardPath β n

instance rewardPathFintype {β : Type*} [Fintype β] (n : ℕ) : Fintype (RewardPath β n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (β × RewardPath β n))

structure FiniteLabeledKernel (α β : Type*) [Fintype β] where
  next : α → β → α
  prob : α → β → ℝ
  nonneg : ∀ x b, 0 ≤ prob x b
  row_sum : ∀ x, ∑ b, prob x b = 1

namespace FiniteLabeledKernel
variable {α β : Type*} [Fintype β] (K : FiniteLabeledKernel α β)

def pathWeight (K : FiniteLabeledKernel α β) : (n : ℕ) → α → RewardPath β n → ℝ
  | 0, _, _ => 1
  | n+1, x, p => K.prob x p.1 * pathWeight K n (K.next x p.1) p.2

def pathReward (K : FiniteLabeledKernel α β) (g : α → β → ℝ) : (n : ℕ) → α → RewardPath β n → ℝ
  | 0, _, _ => 0
  | n+1, x, p => g x p.1 + pathReward K g n (K.next x p.1) p.2

theorem pathWeight_nonneg (n : ℕ) (x : α) (p : RewardPath β n) : 0 ≤ K.pathWeight n x p := by
  induction n generalizing x with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (K.nonneg x p.1) (ih _ p.2)

theorem pathWeight_sum (n : ℕ) (x : α) : ∑ p, K.pathWeight n x p = 1 := by
  induction n generalizing x with
  | zero => simp [pathWeight, RewardPath]
  | succ n ih =>
    change (∑ p : β × RewardPath β n, K.prob x p.1 * pathWeight K n (K.next x p.1) p.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ih, mul_one]
    exact K.row_sum x

def pathExpectation (g : α → β → ℝ) (n : ℕ) (x : α) : ℝ :=
  ∑ p, K.pathWeight n x p * K.pathReward g n x p

theorem pathExpectation_succ (g : α → β → ℝ) (n : ℕ) (x : α) :
    K.pathExpectation g (n+1) x =
      ∑ b, K.prob x b * (g x b + K.pathExpectation g n (K.next x b)) := by
  change (∑ p : β × RewardPath β n, (K.prob x p.1 * pathWeight K n (K.next x p.1) p.2) *
    (g x p.1 + pathReward K g n (K.next x p.1) p.2)) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = ∑ p : RewardPath β n, ((K.prob x b * g x b) * K.pathWeight n (K.next x b) p +
        K.prob x b * (K.pathWeight n (K.next x b) p * K.pathReward g n (K.next x b) p)) := by
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, K.pathWeight_sum, mul_one]
      unfold pathExpectation
      ring

theorem pathReward_nonneg (g : α → β → ℝ) (hg : ∀ x b, 0 ≤ g x b)
    (n : ℕ) (x : α) (p : RewardPath β n) : 0 ≤ K.pathReward g n x p := by
  induction n generalizing x with
  | zero => exact le_refl 0
  | succ n ih => exact add_nonneg (hg x p.1) (ih _ p.2)

def pathTail (g : α → β → ℝ) (n : ℕ) (x : α) (s : ℝ) : ℝ :=
  ∑ p, if s ≤ K.pathReward g n x p then K.pathWeight n x p else 0

theorem pathTail_markov (g : α → β → ℝ) (hg : ∀ x b, 0 ≤ g x b)
    (n : ℕ) (x : α) (s : ℝ) (hs : 0 < s) :
    K.pathTail g n x s ≤ K.pathExpectation g n x / s := by
  apply (le_div_iff₀ hs).mpr
  unfold pathTail pathExpectation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  split_ifs with hp
  · exact mul_le_mul_of_nonneg_left hp (K.pathWeight_nonneg n x p)
  · simp only [zero_mul]
    exact mul_nonneg (K.pathWeight_nonneg n x p) (K.pathReward_nonneg g hg n x p)

theorem kernelAccumulatedReward_rec [Fintype α] (P : FiniteKernel α) (f : α → ℝ)
    (n : ℕ) (x : α) :
    kernelAccumulatedReward P f (n+1) x = f x + P.step (kernelAccumulatedReward P f n) x := by
  unfold kernelAccumulatedReward
  rw [Finset.sum_range_succ']
  simp only [FiniteKernel.steps]
  unfold FiniteKernel.step
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

theorem pathExpectation_eq_kernel [Fintype α] (P : FiniteKernel α)
    (hcompat : ∀ (f : α → ℝ) x, P.step f x = ∑ b, K.prob x b * f (K.next x b))
    (g : α → β → ℝ) (n : ℕ) (x : α) :
    K.pathExpectation g n x = kernelAccumulatedReward P (fun y => ∑ b, K.prob y b * g y b) n x := by
  induction n generalizing x with
  | zero => simp [pathExpectation, pathReward, kernelAccumulatedReward]
  | succ n ih =>
    rw [K.pathExpectation_succ, kernelAccumulatedReward_rec]
    simp_rw [ih]
    rw [hcompat]
    simp only [mul_add, Finset.sum_add_distrib]

end FiniteLabeledKernel
end
end RandomViability


