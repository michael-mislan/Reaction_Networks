import Mathlib

/-! Finite transition kernels and their actual iterated laws. These estimates
will be Poissonized and docked to finite stopped versions of the count source.
No stochastic exit or expectation estimate is included as an assumption. -/
namespace FiniteCopy

structure FiniteKernel (α : Type*) [Fintype α] where
  prob : α → α → ℝ
  nonneg : ∀ x y, 0 ≤ prob x y
  row_sum : ∀ x, ∑ y, prob x y = 1

namespace FiniteKernel
variable {α : Type*} [Fintype α] (P : FiniteKernel α)

noncomputable def step (f : α → ℝ) (x : α) : ℝ := ∑ y, P.prob x y*f y
noncomputable def steps (P : FiniteKernel α) : ℕ → (α → ℝ) → α → ℝ
  | 0, f => f
  | n+1, f => P.step (steps P n f)

theorem step_mono {f g : α → ℝ} (h : ∀ x, f x ≤ g x) (x : α) :
    P.step f x ≤ P.step g x := by
  apply Finset.sum_le_sum
  intro y _
  exact mul_le_mul_of_nonneg_left (h y) (P.nonneg x y)

theorem step_const (c : ℝ) (x : α) : P.step (fun _ => c) x = c := by
  simp [step, ← Finset.sum_mul, P.row_sum]

theorem step_add (f g : α → ℝ) (x : α) :
    P.step (fun y => f y+g y) x = P.step f x+P.step g x := by
  simp [step, mul_add, Finset.sum_add_distrib]

theorem step_scale (c : ℝ) (f : α → ℝ) (x : α) :
    P.step (fun y => c*f y) x = c*P.step f x := by
  simp only [step, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem steps_mono {f g : α → ℝ} (h : ∀ x, f x ≤ g x) (n : ℕ) (x : α) :
    P.steps n f x ≤ P.steps n g x := by
  induction n generalizing x with
  | zero => exact h x
  | succ n ih => exact P.step_mono ih x

theorem steps_const (n : ℕ) (c : ℝ) (x : α) : P.steps n (fun _ => c) x = c := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change P.step (P.steps n (fun _ => c)) x = c
    rw [show P.steps n (fun _ => c) = (fun _ => c) from funext ih, P.step_const]

theorem steps_scale (n : ℕ) (c : ℝ) (f : α → ℝ) (x : α) :
    P.steps n (fun y => c*f y) x = c*P.steps n f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change P.step (P.steps n (fun y => c*f y)) x = c*P.step (P.steps n f) x
    rw [show P.steps n (fun y => c*f y) = (fun y => c*P.steps n f y) from funext ih,
      P.step_scale]

theorem steps_nonneg (n : ℕ) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) (x : α) :
    0 ≤ P.steps n f x := by
  have h := P.steps_mono hf n x
  simpa only [P.steps_const n 0 x] using h

theorem steps_le_one (n : ℕ) {f : α → ℝ} (hf : ∀ x, f x ≤ 1) (x : α) :
    P.steps n f x ≤ 1 := by
  have h := P.steps_mono hf n x
  simpa only [P.steps_const n 1 x] using h

/-- The discrete generator inequality is propagated by the actual kernel. -/
theorem steps_drift_bound (V : α → ℝ) (b : ℝ)
    (h : ∀ x, P.step V x ≤ V x+b) (n : ℕ) (x : α) :
    P.steps n V x ≤ V x+(n : ℝ)*b := by
  induction n generalizing x with
  | zero => simp [steps]
  | succ n ih =>
    have hm := P.step_mono ih x
    have he : P.step (fun y => V y+(n : ℝ)*b) x = P.step V x+(n : ℝ)*b := by
      rw [P.step_add, P.step_const]
    rw [he] at hm
    change P.step (P.steps n V) x ≤ V x+((n+1 : ℕ) : ℝ)*b
    push_cast
    linarith [h x]

/-- Includes a killed observable when its one-step generator is dissipative. -/
theorem steps_decay_bound (W : α → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ x, P.step W x ≤ r*W x) (n : ℕ) (x : α) :
    P.steps n W x ≤ r^n*W x := by
  induction n generalizing x with
  | zero => simp [steps]
  | succ n ih =>
    have hm := P.step_mono ih x
    rw [P.step_scale] at hm
    have hh := mul_le_mul_of_nonneg_left (h x) (pow_nonneg hr n)
    change P.step (P.steps n W) x ≤ r^(n+1)*W x
    rw [pow_succ]
    nlinarith only [hm,hh]

noncomputable def eventIndicator (A : Set α) (x : α) : ℝ := by
  classical
  exact if x ∈ A then 1 else 0

omit [Fintype α] in
theorem eventIndicator_bounds (A : Set α) (x : α) :
    0 ≤ eventIndicator A x ∧ eventIndicator A x ≤ 1 := by
  classical
  by_cases hx : x ∈ A <;> simp [eventIndicator, hx]

theorem event_probability_bounds (A : Set α) (n : ℕ) (x : α) :
    0 ≤ P.steps n (eventIndicator A) x ∧ P.steps n (eventIndicator A) x ≤ 1 :=
  ⟨P.steps_nonneg n (fun y => (eventIndicator_bounds A y).1) x,
    P.steps_le_one n (fun y => (eventIndicator_bounds A y).2) x⟩

theorem event_drift_bound (A : Set α) (V : α → ℝ) (a b : ℝ)
    (hV : ∀ x, 0 ≤ V x) (hA : ∀ x ∈ A, a ≤ V x)
    (h : ∀ x, P.step V x ≤ V x+b) (n : ℕ) (x : α) :
    a*P.steps n (eventIndicator A) x ≤ V x+(n : ℝ)*b := by
  have hind : ∀ y, a*eventIndicator A y ≤ V y := by
    intro y
    classical
    by_cases hy : y ∈ A
    · simpa [eventIndicator, hy] using hA y hy
    · simpa [eventIndicator, hy] using hV y
  have hm := P.steps_mono hind n x
  rw [P.steps_scale] at hm
  exact hm.trans (P.steps_drift_bound V b h n x)

end FiniteKernel
end FiniteCopy
