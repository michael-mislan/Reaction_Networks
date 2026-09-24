import proofs.FiniteCopy.KernelExpectations

namespace RandomViability.Binding
noncomputable section
open FiniteCopy
open scoped NNReal

def twoPeriod {α : Type*} [Fintype α] (P Q : FiniteKernel α) (t : ℝ≥0) (f : α → ℝ) (x : α) : ℝ :=
  P.poissonized t (fun y => Q.poissonized t f y) x

theorem twoPeriod_nonneg {α : Type*} [Fintype α] (P Q : FiniteKernel α)
    (t : ℝ≥0) (f : α → ℝ) (hf : ∀ x,0≤f x) (x : α) : 0≤twoPeriod P Q t f x :=
  P.poissonized_nonneg t _ (Q.poissonized_nonneg t f hf) x

theorem twoPeriod_mono {α : Type*} [Fintype α] (P Q : FiniteKernel α)
    (t : ℝ≥0) (f g : α → ℝ) (hf : ∀ x,0≤f x) (hg : ∀ x,0≤g x)
    (hfg : ∀ x,f x≤g x) (x : α) : twoPeriod P Q t f x ≤ twoPeriod P Q t g x :=
  P.poissonized_mono t _ _ (Q.poissonized_nonneg t f hf) (Q.poissonized_nonneg t g hg)
    (Q.poissonized_mono t f g hf hg hfg) x

theorem twoPeriod_const {α : Type*} [Fintype α] (P Q : FiniteKernel α)
    (t : ℝ≥0) (c : ℝ) (x : α) : twoPeriod P Q t (fun _=>c) x=c := by
  unfold twoPeriod
  simp only [Q.poissonized_const,P.poissonized_const]

theorem twoPeriod_add {α : Type*} [Fintype α] (P Q : FiniteKernel α)
    (t : ℝ≥0) (f g : α → ℝ) (hf : ∀ x,0≤f x) (hg : ∀ x,0≤g x) (x : α) :
    twoPeriod P Q t (fun y=>f y+g y) x = twoPeriod P Q t f x+twoPeriod P Q t g x := by
  unfold twoPeriod
  simp only [Q.poissonized_add t f g hf hg]
  exact P.poissonized_add t _ _ (Q.poissonized_nonneg t f hf) (Q.poissonized_nonneg t g hg) x

theorem twoPeriod_foster {α : Type*} [Fintype α] (P Q : FiniteKernel α)
    (t : ℝ≥0) (V : α → ℝ) (b c : ℝ) (hV : ∀ x,0≤V x) (hc : 0≤c)
    (hP : ∀ x,P.poissonized t V x≤V x+b) (hQ : ∀ x,Q.poissonized t V x≤V x+c)
    (x : α) : twoPeriod P Q t V x≤V x+b+c := by
  have h := P.poissonized_mono t (fun y=>Q.poissonized t V y) (fun y=>V y+c)
    (Q.poissonized_nonneg t V hV) (fun y=>add_nonneg (hV y) hc) hQ x
  rw [P.poissonized_add t V (fun _=>c) hV (fun _=>hc),P.poissonized_const] at h
  exact h.trans (add_le_add (hP x) le_rfl)

theorem poissonized_fixed {α : Type*} [Fintype α] (P : FiniteKernel α) (f : α → ℝ)
    (h : ∀ x,P.step f x=f x) (t : ℝ≥0) (x : α) : P.poissonized t f x=f x := by
  have hn (n : ℕ) : ∀ y,P.steps n f y=f y := by
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [FiniteKernel.steps,show P.steps n f=f from funext ih]
      exact h y
  unfold FiniteKernel.poissonized
  simp_rw [hn]
  exact ((poissonWeight_sum t).mul_right (f x)).tsum_eq.trans (one_mul _)

end
end RandomViability.Binding
