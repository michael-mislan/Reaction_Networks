import proofs.FiniteCopy.PoissonKernel

namespace DiagnosticWindows
open FiniteCopy
open scoped BigOperators

variable {α ι : Type*} [Fintype α] [Fintype ι]

theorem steps_eigen (P : FiniteKernel α) (V : α → ℝ) (r : ℝ)
    (h : ∀ x, P.step V x = r*V x) (n : ℕ) (x : α) :
    P.steps n V x = r^n*V x := by
  induction n generalizing x with
  | zero => simp [FiniteKernel.steps]
  | succ n ih =>
    change P.step (P.steps n V) x = _
    rw [show P.steps n V = (fun y => r^n*V y) from funext ih,
      P.step_scale,h,pow_succ]
    ring

theorem step_sum (P : FiniteKernel α) (V : ι → α → ℝ) (x : α) :
    P.step (fun y => ∑ i, V i y) x = ∑ i, P.step (V i) x := by
  simp only [FiniteKernel.step,Finset.mul_sum]
  exact Finset.sum_comm

theorem steps_sum (P : FiniteKernel α) (V : ι → α → ℝ) (n : ℕ) (x : α) :
    P.steps n (fun y => ∑ i, V i y) x = ∑ i, P.steps n (V i) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change P.step (P.steps n (fun y => ∑ i, V i y)) x = _
    rw [show P.steps n (fun y => ∑ i, V i y) =
      (fun y => ∑ i, P.steps n (V i) y) from funext ih,step_sum]
    rfl

/-- Signed spectral components are permitted. No positivity or probability
estimate is assumed for the components; the underlying kernel is normalized. -/
theorem spectral_survival (P : FiniteKernel α) (f : α → ℝ)
    (V : ι → α → ℝ) (r : ι → ℝ)
    (hsum : ∀ x, f x = ∑ i, V i x)
    (heigen : ∀ i x, P.step (V i) x = r i*V i x)
    (t : NNReal) (x : α) :
    P.poissonized t f x = ∑ i, Real.exp ((t:ℝ)*(r i-1))*V i x := by
  have hs := hasSum_sum (s := Finset.univ)
    (fun i _ => (poissonWeight_geometric t (r i)).mul_right (V i x))
  have he (n : ℕ) : poissonWeight t n * P.steps n f x =
      ∑ i, (poissonWeight t n*(r i)^n)*V i x := by
    rw [show f = (fun y => ∑ i, V i y) from funext hsum,steps_sum]
    simp_rw [steps_eigen P _ _ (heigen _)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold FiniteKernel.poissonized
  simp_rw [he]
  exact hs.tsum_eq

end DiagnosticWindows
