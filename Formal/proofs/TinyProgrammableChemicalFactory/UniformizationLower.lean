import proofs.HeritableCompositions.KernelComposition

namespace TinyProgrammableChemicalFactory
open FiniteCopy HeritableCompositions

/-- Any nonnegative finite weighted lower iterate bounds the actual Poisson kernel.
The arithmetic producer must prove its weight and iterate premises separately. -/
theorem truncated_uniformization_lower {α : Type*} [Fintype α]
    (P : FiniteKernel α) (t : NNReal) (f : α → ℝ) (hf : ∀ x, 0≤f x)
    (J : ℕ) (w : ℕ → ℝ) (a : ℕ → α → ℝ)
    (hw : ∀ j, w j≤poissonWeight t j)
    (ha0 : ∀ j x, 0≤a j x) (ha : ∀ j x, a j x≤P.steps j f x) (x : α) :
    ∑ j ∈ Finset.range J, w j*a j x ≤ P.poissonized t f x := by
  calc
    _ ≤ ∑ j ∈ Finset.range J, poissonWeight t j*P.steps j f x := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul (hw j) (ha j x) (ha0 j x) (poissonWeight_nonneg t j)
    _ ≤ _ := by
      unfold FiniteKernel.poissonized
      exact Summable.sum_le_tsum (Finset.range J)
        (fun j _ => mul_nonneg (poissonWeight_nonneg t j) (P.steps_nonneg j hf x))
        (poisson_summable P t f x)

/-- Repeated downward updates stay below a monotone exact block evolution. -/
theorem block_iteration_lower {α : Type*} (B E : (α → ℝ) → α → ℝ)
    (hE : Monotone E) (hB : ∀ v, B v≤E v)
    (u v : α → ℝ) (huv : u≤v) (n : ℕ) :
    B^[n] u ≤ E^[n] v := by
  induction n with
  | zero => exact huv
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    exact (hB _).trans (hE ih)

end TinyProgrammableChemicalFactory
