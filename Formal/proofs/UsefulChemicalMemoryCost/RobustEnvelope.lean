import proofs.TinyProgrammableChemicalFactory.UniformizationLower

namespace UsefulChemicalMemoryCost
open FiniteCopy HeritableCompositions

noncomputable def envelope {α : Type*} [Fintype α]
    (P Q : FiniteKernel α) (f : α → ℝ) (x : α) : ℝ :=
  min (P.step f x) (Q.step f x)

theorem envelope_mono {α : Type*} [Fintype α] (P Q : FiniteKernel α) :
    Monotone (envelope P Q) := by
  intro f g h x
  exact min_le_min (P.step_mono h x) (Q.step_mono h x)

theorem min_le_affine (a b t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    min a b ≤ (1-t)*a+t*b := by
  have h₁ := mul_le_mul_of_nonneg_left (min_le_left a b) (sub_nonneg.mpr ht1)
  have h₂ := mul_le_mul_of_nonneg_left (min_le_right a b) ht
  nlinarith

/-- Entrywise affine dependence is required of the literal kernels.
No affine dependence of the terminal probability is asserted. -/
theorem envelope_le_kernel {α : Type*} [Fintype α]
    (P Q R : FiniteKernel α) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hr : ∀ x y, R.prob x y = (1-t)*P.prob x y+t*Q.prob x y)
    (f : α → ℝ) (x : α) : envelope P Q f x ≤ R.step f x := by
  have he : R.step f x = (1-t)*P.step f x+t*Q.step f x := by
    simp only [FiniteKernel.step, hr, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum]
  rw [he]
  exact min_le_affine _ _ _ ht ht1

theorem envelope_iterates_lower {α : Type*} [Fintype α]
    (P Q R : FiniteKernel α)
    (hr : ∀ f x, envelope P Q f x ≤ R.step f x)
    (f : α → ℝ) (n : ℕ) (x : α) :
    (envelope P Q)^[n] f x ≤ R.steps n f x := by
  induction n generalizing x with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hr _ x).trans (R.step_mono ih x)

theorem envelope_nonneg {α : Type*} [Fintype α]
    (P Q : FiniteKernel α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (n : ℕ) :
    ∀ x, 0 ≤ (envelope P Q)^[n] f x := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    intro x
    rw [Function.iterate_succ_apply']
    apply le_min
    · simpa only [P.step_const] using P.step_mono ih x
    · simpa only [Q.step_const] using Q.step_mono ih x

/-- A finite robust Poisson lower block, uniformly for every enclosed kernel. -/
theorem robust_poisson_lower {α : Type*} [Fintype α]
    (P Q R : FiniteKernel α)
    (hr : ∀ f x, envelope P Q f x ≤ R.step f x)
    (t : NNReal) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (J : ℕ) (w : ℕ → ℝ) (hw : ∀ j, w j ≤ poissonWeight t j) (x : α) :
    ∑ j ∈ Finset.range J, w j * (envelope P Q)^[j] f x ≤ R.poissonized t f x := by
  exact TinyProgrammableChemicalFactory.truncated_uniformization_lower
    R t f hf J w (fun j => (envelope P Q)^[j] f) hw
    (envelope_nonneg P Q f hf) (fun j y => envelope_iterates_lower P Q R hr f j y) x

theorem complement_upper {α : Type*} [Fintype α]
    (P : FiniteKernel α) (t : NNReal) (h : α → ℝ) (l : ℝ) (x : α)
    (hl : l ≤ P.poissonized t (fun y => 1-h y) x) :
    P.poissonized t h x ≤ 1-l := by
  have he := poisson_additive P t h (fun y => 1-h y) x
  have hc : (fun y => h y+(1-h y)) = (fun _ => (1 : ℝ)) := by
    funext y
    ring
  rw [hc, poisson_constant] at he
  linarith

end UsefulChemicalMemoryCost
