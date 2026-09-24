import proofs.FiniteCopy.PoissonKernel

namespace HeritableCompositions
open FiniteCopy

theorem steps_additive {α : Type*} [Fintype α] (P : FiniteKernel α)
    (n : ℕ) (f g : α → ℝ) (x : α) :
    P.steps n (fun y => f y+g y) x = P.steps n f x+P.steps n g x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change P.step (P.steps n (fun y => f y+g y)) x = P.step (P.steps n f) x+P.step (P.steps n g) x
    rw [show P.steps n (fun y => f y+g y) = (fun y => P.steps n f y+P.steps n g y) from funext ih]
    exact P.step_add _ _ x

theorem steps_absolute_bound {α : Type*} [Fintype α] (P : FiniteKernel α)
    (f : α → ℝ) (n : ℕ) (x : α) : |P.steps n f x| ≤ ∑ y, |f y| := by
  have hab (y : α) : |f y| ≤ ∑ z, |f z| :=
    Finset.single_le_sum (fun z _ => abs_nonneg (f z)) (Finset.mem_univ y)
  have hlo := P.steps_mono (fun y => (abs_le.mp (hab y)).1) n x
  have hhi := P.steps_mono (fun y => (abs_le.mp (hab y)).2) n x
  rw [P.steps_const] at hlo hhi
  exact abs_le.mpr ⟨hlo,hhi⟩

theorem poisson_summable {α : Type*} [Fintype α] (P : FiniteKernel α)
    (t : NNReal) (f : α → ℝ) (x : α) :
    Summable (fun n => poissonWeight t n*P.steps n f x) := by
  apply Summable.of_norm_bounded ((poissonWeight_sum t).summable.mul_right (∑ y, |f y|))
  intro n
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (poissonWeight_nonneg t n)]
  exact mul_le_mul_of_nonneg_left (steps_absolute_bound P f n x) (poissonWeight_nonneg t n)

theorem poisson_mono {α : Type*} [Fintype α] (P : FiniteKernel α)
    (t : NNReal) (f g : α → ℝ) (h : ∀ x, f x ≤ g x) (x : α) :
    P.poissonized t f x ≤ P.poissonized t g x :=
  Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (P.steps_mono h n x)
    (poissonWeight_nonneg t n)) (poisson_summable P t f x) (poisson_summable P t g x)

theorem poisson_constant {α : Type*} [Fintype α] (P : FiniteKernel α)
    (t : NNReal) (c : ℝ) (x : α) : P.poissonized t (fun _ => c) x = c := by
  unfold FiniteKernel.poissonized
  simp_rw [P.steps_const]
  simpa using ((poissonWeight_sum t).mul_right c).tsum_eq

theorem poisson_additive {α : Type*} [Fintype α] (P : FiniteKernel α)
    (t : NNReal) (f g : α → ℝ) (x : α) :
    P.poissonized t (fun y => f y+g y) x = P.poissonized t f x+P.poissonized t g x := by
  unfold FiniteKernel.poissonized
  simp_rw [steps_additive,mul_add]
  exact (poisson_summable P t f x).tsum_add (poisson_summable P t g x)

theorem poisson_bad_state_bound {α : Type*} [Fintype α] (P : FiniteKernel α)
    (t : NNReal) (A : Set α) (f : α → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ x, f x ≤ 1) (hgood : ∀ x, x ∉ A → f x ≤ ε) (x : α) :
    P.poissonized t f x ≤ P.poissonized t (FiniteKernel.eventIndicator A) x+ε := by
  classical
  have hp (y : α) : f y ≤ FiniteKernel.eventIndicator A y+ε := by
    by_cases hy : y ∈ A
    · simp only [FiniteKernel.eventIndicator,if_pos hy]
      linarith only [hf y,hε]
    · simpa only [FiniteKernel.eventIndicator,if_neg hy,zero_add] using hgood y hy
  have h := poisson_mono P t f (fun y => FiniteKernel.eventIndicator A y+ε) hp x
  rwa [poisson_additive,poisson_constant] at h

end HeritableCompositions
