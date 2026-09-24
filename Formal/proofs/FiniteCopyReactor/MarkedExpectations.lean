import proofs.FiniteCopyReactor.ThreeStageUpper

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy Classical

theorem marked_law_bounds {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (f : α → ℝ → ℝ) (C : ℝ) (hf : ∀ x z, 0 ≤ f x z ∧ f x z ≤ C)
    (n : ℕ) (x : α) (z : ℝ) : 0 ≤ P.law n f x z ∧ P.law n f x z ≤ C := by
  constructor
  · have h := P.law_mono _ _ (fun y w => (hf y w).1) n x z
    simpa only [P.law_const] using h
  · have h := P.law_mono _ _ (fun y w => (hf y w).2) n x z
    simpa only [P.law_const] using h

theorem marked_summable {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (f : α → ℝ → ℝ) (C : ℝ) (hf : ∀ x z, 0 ≤ f x z ∧ f x z ≤ C)
    (t : NNReal) (x : α) (z : ℝ) : Summable (fun n => poissonWeight t n*P.law n f x z) :=
  Summable.of_nonneg_of_le
    (fun n => mul_nonneg (poissonWeight_nonneg t n) (marked_law_bounds P f C hf n x z).1)
    (fun n => mul_le_mul_of_nonneg_left (marked_law_bounds P f C hf n x z).2 (poissonWeight_nonneg t n))
    ((poissonWeight_sum t).mul_right C).summable

theorem marked_poisson_bounds {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (f : α → ℝ → ℝ) (C : ℝ) (hf : ∀ x z, 0 ≤ f x z ∧ f x z ≤ C)
    (t : NNReal) (x : α) (z : ℝ) : 0 ≤ P.poissonized t f x z ∧ P.poissonized t f x z ≤ C := by
  constructor
  · exact tsum_nonneg (fun n => mul_nonneg (poissonWeight_nonneg t n) (marked_law_bounds P f C hf n x z).1)
  · exact (Summable.tsum_le_tsum
      (fun n => mul_le_mul_of_nonneg_left (marked_law_bounds P f C hf n x z).2 (poissonWeight_nonneg t n))
      (marked_summable P f C hf t x z) ((poissonWeight_sum t).mul_right C).summable).trans_eq
      (by simpa only [one_mul] using ((poissonWeight_sum t).mul_right C).tsum_eq)

theorem marked_poisson_mono {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (f g : α → ℝ → ℝ) (C D : ℝ)
    (hf : ∀ x z, 0 ≤ f x z ∧ f x z ≤ C) (hg : ∀ x z, 0 ≤ g x z ∧ g x z ≤ D)
    (h : ∀ x z, f x z ≤ g x z) (t : NNReal) (x : α) (z : ℝ) :
    P.poissonized t f x z ≤ P.poissonized t g x z :=
  Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (P.law_mono f g h n x z) (poissonWeight_nonneg t n))
    (marked_summable P f C hf t x z) (marked_summable P g D hg t x z)

theorem marked_poisson_add {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (f g : α → ℝ → ℝ) (C D : ℝ)
    (hf : ∀ x z, 0 ≤ f x z ∧ f x z ≤ C) (hg : ∀ x z, 0 ≤ g x z ∧ g x z ≤ D)
    (t : NNReal) (x : α) (z : ℝ) :
    P.poissonized t (fun y w => f y w+g y w) x z=P.poissonized t f x z+P.poissonized t g x z := by
  unfold MarkedKernel.poissonized
  simp_rw [P.law_add,mul_add]
  exact (marked_summable P f C hf t x z).tsum_add (marked_summable P g D hg t x z)

end
end FiniteCopyReactor
