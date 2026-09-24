import proofs.FiniteCopy.PoissonKernel

namespace FiniteCopy
open scoped NNReal

/-- Finite reaction choices, retaining an additive event count. -/
structure MarkedKernel (α β : Type*) [Fintype β] where
  prob : α → β → ℝ
  next : α → β → α
  mark : β → ℝ
  nonneg : ∀ x r, 0 ≤ prob x r
  row_sum : ∀ x, ∑ r, prob x r = 1

namespace MarkedKernel
variable {α β : Type*} [Fintype β] (P : MarkedKernel α β)

noncomputable def step (f : α → ℝ → ℝ) (x : α) (z : ℝ) : ℝ :=
  ∑ r, P.prob x r*f (P.next x r) (z+P.mark r)

noncomputable def law (P : MarkedKernel α β) : ℕ → (α → ℝ → ℝ) → α → ℝ → ℝ
  | 0,f => f
  | n+1,f => P.step (law P n f)

theorem step_mono (f g : α → ℝ → ℝ) (h : ∀ x z, f x z ≤ g x z) (x : α) (z : ℝ) :
    P.step f x z ≤ P.step g x z := by
  apply Finset.sum_le_sum
  intro r _
  exact mul_le_mul_of_nonneg_left (h _ _) (P.nonneg x r)

theorem step_scale (c : ℝ) (f : α → ℝ → ℝ) (x : α) (z : ℝ) :
    P.step (fun y w => c*f y w) x z = c*P.step f x z := by
  unfold step
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem law_mono (f g : α → ℝ → ℝ) (h : ∀ x z, f x z ≤ g x z)
    (n : ℕ) (x : α) (z : ℝ) : P.law n f x z ≤ P.law n g x z := by
  induction n generalizing x z with
  | zero => exact h x z
  | succ n ih => exact P.step_mono _ _ ih x z

theorem law_const (c : ℝ) (n : ℕ) (x : α) (z : ℝ) : P.law n (fun _ _ => c) x z = c := by
  induction n generalizing x z with
  | zero => rfl
  | succ n ih =>
    change (∑ r, P.prob x r*P.law n (fun _ _ => c) (P.next x r) (z+P.mark r)) = c
    simp only [ih,← Finset.sum_mul,P.row_sum,one_mul]

theorem law_scale (c : ℝ) (f : α → ℝ → ℝ) (n : ℕ) (x : α) (z : ℝ) :
    P.law n (fun y w => c*f y w) x z = c*P.law n f x z := by
  induction n generalizing x z with
  | zero => rfl
  | succ n ih =>
    change P.step (P.law n (fun y w => c*f y w)) x z = c*P.step (P.law n f) x z
    rw [show P.law n (fun y w => c*f y w) = (fun y w => c*P.law n f y w) from funext (fun y => funext (ih y))]
    exact P.step_scale c _ x z

theorem law_decay (f : α → ℝ → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ x z, P.step f x z ≤ r*f x z) (n : ℕ) (x : α) (z : ℝ) :
    P.law n f x z ≤ r^n*f x z := by
  induction n generalizing x z with
  | zero => simp [law]
  | succ n ih =>
    have hm := P.step_mono _ _ ih x z
    rw [P.step_scale] at hm
    have hh := mul_le_mul_of_nonneg_left (h x z) (pow_nonneg hr n)
    change P.step (P.law n f) x z ≤ r^(n+1)*f x z
    rw [pow_succ]
    nlinarith only [hm,hh]

noncomputable def eventIndicator (A : Set (α × ℝ)) (x : α) (z : ℝ) : ℝ := by
  classical
  exact if (x,z) ∈ A then 1 else 0

theorem event_bounds (A : Set (α × ℝ)) (n : ℕ) (x : α) (z : ℝ) :
    0 ≤ P.law n (eventIndicator A) x z ∧ P.law n (eventIndicator A) x z ≤ 1 := by
  classical
  have hlo (y w) : (0 : ℝ) ≤ eventIndicator A y w := by unfold eventIndicator; split_ifs <;> norm_num
  have hhi (y w) : eventIndicator A y w ≤ 1 := by unfold eventIndicator; split_ifs <;> norm_num
  constructor
  · have h := P.law_mono _ _ hlo n x z
    simpa only [P.law_const] using h
  · have h := P.law_mono _ _ hhi n x z
    simpa only [P.law_const] using h

noncomputable def poissonized (t : ℝ≥0) (f : α → ℝ → ℝ) (x : α) (z : ℝ) : ℝ :=
  ∑' n, poissonWeight t n*P.law n f x z

theorem event_summable (t : ℝ≥0) (A : Set (α × ℝ)) (x : α) (z : ℝ) :
    Summable (fun n => poissonWeight t n*P.law n (eventIndicator A) x z) :=
  Summable.of_nonneg_of_le
    (fun n => mul_nonneg (poissonWeight_nonneg t n) (P.event_bounds A n x z).1)
    (fun n => mul_le_of_le_one_right (poissonWeight_nonneg t n) (P.event_bounds A n x z).2)
    (poissonWeight_sum t).summable

theorem poissonized_event_decay (t : ℝ≥0) (A : Set (α × ℝ)) (f : α → ℝ → ℝ)
    (c r : ℝ) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hA : ∀ x z, eventIndicator A x z ≤ c*f x z)
    (h : ∀ x z, P.step f x z ≤ r*f x z) (x : α) (z : ℝ) :
    P.poissonized t (eventIndicator A) x z ≤ c*Real.exp ((t : ℝ)*(r-1))*f x z := by
  have hm (n) : P.law n (eventIndicator A) x z ≤ c*(r^n*f x z) := by
    have hh := P.law_mono _ _ hA n x z
    rw [P.law_scale] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (P.law_decay f r hr h n x z) hc)
  have hs : HasSum (fun n => poissonWeight t n*(c*(r^n*f x z)))
      (c*Real.exp ((t : ℝ)*(r-1))*f x z) := by
    convert (poissonWeight_geometric t r).mul_right (c*f x z) using 1
    · funext n; ring
    · ring
  exact (Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hm n) (poissonWeight_nonneg t n))
    (P.event_summable t A x z) hs.summable).trans_eq hs.tsum_eq

end MarkedKernel
end FiniteCopy
