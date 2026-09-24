import proofs.FiniteCopy.KernelExpectations

namespace RandomViability
open FiniteCopy

/-- Propagation of affine one-step drift through the actual iterated kernel.
The moment bound is concluded, not assumed along the trajectory. -/
theorem kernel_moment_bound {α : Type*} [Fintype α] (P : FiniteKernel α)
    (m : α → ℝ) (r C : ℝ) (hr : 0 ≤ r)
    (hstep : ∀ x, P.step m x ≤ r * m x + (1-r)*C)
    (x : α) (hinit : m x ≤ C) (n : ℕ) : P.steps n m x ≤ C := by
  have hc : ∀ y, P.step (fun z => m z - C) y ≤ r * (m y - C) := by
    intro y
    have he : P.step (fun z => m z - C) y = P.step m y - C := by
      simp only [sub_eq_add_neg, P.step_add, P.step_const]
    rw [he]
    nlinarith [hstep y]
  have hd := P.steps_decay_bound (fun z => m z-C) r hr hc n x
  have he : P.steps n (fun z => m z-C) x = P.steps n m x-C := by
    simp only [sub_eq_add_neg, P.steps_add, P.steps_const]
  rw [he] at hd
  have hn := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hr n) (sub_nonpos.mpr hinit)
  linarith

noncomputable def kernelAccumulatedReward {α : Type*} [Fintype α]
    (P : FiniteKernel α) (reward : α → ℝ) (n : ℕ) (x : α) : ℝ :=
  ∑ i ∈ Finset.range n, P.steps i reward x

theorem kernel_accumulated_reward_bound {α : Type*} [Fintype α] (P : FiniteKernel α)
    (m reward : α → ℝ) (r C a : ℝ) (hr : 0 ≤ r) (ha : 0 ≤ a)
    (hstep : ∀ y, P.step m y ≤ r*m y+(1-r)*C)
    (hreward : ∀ y, reward y ≤ a*m y)
    (x : α) (hinit : m x ≤ C) (n : ℕ) :
    kernelAccumulatedReward P reward n x ≤ (n : ℝ)*a*C := by
  have hb : ∀ i, P.steps i reward x ≤ a*C := by
    intro i
    have hh := P.steps_mono hreward i x
    rw [P.steps_scale] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (kernel_moment_bound P m r C hr hstep x hinit i) ha)
  calc
    _ ≤ ∑ _i ∈ Finset.range n, a*C := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem poissonized_moment_bound {α : Type*} [Fintype α] (P : FiniteKernel α)
    (m : α → ℝ) (r C : ℝ) (hr : 0 ≤ r) (hm : ∀ y, 0 ≤ m y)
    (hstep : ∀ y, P.step m y ≤ r*m y+(1-r)*C)
    (x : α) (hinit : m x ≤ C) (t : NNReal) : P.poissonized t m x ≤ C := by
  have hs := (poissonWeight_sum t).mul_right C
  have hb : ∀ n, poissonWeight t n * P.steps n m x ≤ poissonWeight t n * C := by
    intro n
    exact mul_le_mul_of_nonneg_left (kernel_moment_bound P m r C hr hstep x hinit n)
      (poissonWeight_nonneg t n)
  have hh := Summable.tsum_le_tsum hb (P.nonneg_summable t m hm x) hs.summable
  simpa only [hs.tsum_eq, one_mul] using hh

noncomputable def poissonAccumulatedReward {α : Type*} [Fintype α]
    (P : FiniteKernel α) (reward : α → ℝ) (t : NNReal) (x : α) : ℝ :=
  ∑' n, poissonWeight t n * kernelAccumulatedReward P reward n x

theorem poisson_accumulated_reward_bound {α : Type*} [Fintype α] (P : FiniteKernel α)
    (m reward : α → ℝ) (r C a : ℝ) (hr : 0 ≤ r) (ha : 0 ≤ a)
    (hstep : ∀ y, P.step m y ≤ r*m y+(1-r)*C)
    (hreward : ∀ y, reward y ≤ a*m y) (hreward0 : ∀ y, 0 ≤ reward y)
    (x : α) (hinit : m x ≤ C) (t : NNReal) :
    poissonAccumulatedReward P reward t x ≤ (t : ℝ)*a*C := by
  have hs : HasSum (fun n : ℕ => poissonWeight t n * ((n : ℝ)*a*C)) ((t : ℝ)*a*C) := by
    convert (poissonWeight_mean t).mul_right (a*C) using 1
    · funext n
      ring
    · ring
  have hb : ∀ n : ℕ, poissonWeight t n * kernelAccumulatedReward P reward n x ≤
      poissonWeight t n * ((n : ℝ)*a*C) := by
    intro n
    exact mul_le_mul_of_nonneg_left
      (kernel_accumulated_reward_bound P m reward r C a hr ha hstep hreward x hinit n)
      (poissonWeight_nonneg t n)
  have hzero : ∀ n : ℕ, 0 ≤ poissonWeight t n * kernelAccumulatedReward P reward n x := by
    intro n
    apply mul_nonneg (poissonWeight_nonneg t n)
    exact Finset.sum_nonneg (fun i _ => P.steps_nonneg i hreward0 x)
  have hsum := Summable.of_nonneg_of_le hzero hb hs.summable
  have hh := Summable.tsum_le_tsum hb hsum hs.summable
  simpa only [poissonAccumulatedReward, hs.tsum_eq] using hh

end RandomViability
