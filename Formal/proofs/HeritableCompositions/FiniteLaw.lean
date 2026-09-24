import proofs.HeritableCompositions.KernelComposition

namespace HeritableCompositions
open FiniteCopy

structure FiniteLaw (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def expect (μ : FiniteLaw α) (f : α → ℝ) : ℝ := ∑ x, μ.mass x*f x

noncomputable def pure (x : α) : FiniteLaw α := by
  classical
  exact ⟨fun y => if y=x then 1 else 0,fun y => by dsimp; positivity,by simp⟩

noncomputable def bind (μ : FiniteLaw α) (f : α → FiniteLaw β) : FiniteLaw β := {
  mass := fun y => ∑ x, μ.mass x*(f x).mass y
  nonneg := fun y => Finset.sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x) ((f x).nonneg y))
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,FiniteLaw.total,mul_one] }

theorem expect_pure (x : α) (f : α → ℝ) : (pure x).expect f = f x := by
  classical
  simp [expect,pure]

theorem expect_const (μ : FiniteLaw α) (c : ℝ) : μ.expect (fun _ => c) = c := by
  simp only [expect,← Finset.sum_mul,μ.total,one_mul]

theorem expect_mono (μ : FiniteLaw α) (f g : α → ℝ) (h : ∀ x, f x ≤ g x) :
    μ.expect f ≤ μ.expect g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x))

theorem expect_bind (μ : FiniteLaw α) (f : α → FiniteLaw β) (g : β → ℝ) :
    (μ.bind f).expect g = μ.expect (fun x => (f x).expect g) := by
  simp only [expect,bind,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

end FiniteLaw

theorem poisson_scalar {α : Type*} [Fintype α] (P : FiniteKernel α)
    (t : NNReal) (c : ℝ) (f : α → ℝ) (x : α) :
    P.poissonized t (fun y => c*f y) x = c*P.poissonized t f x := by
  unfold FiniteKernel.poissonized
  simp_rw [P.steps_scale]
  rw [← tsum_mul_left]
  congr 1
  funext n
  ring

theorem poisson_finite_sum {α β : Type*} [Fintype α] (P : FiniteKernel α)
    (t : NNReal) (S : Finset β) (f : β → α → ℝ) (x : α) :
    P.poissonized t (fun y => ∑ i ∈ S, f i y) x = ∑ i ∈ S, P.poissonized t (f i) x := by
  classical
  induction S using Finset.induction with
  | empty => simp only [Finset.sum_empty,poisson_constant]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi,poisson_additive,ih]

noncomputable def poissonLaw {α : Type*} [Fintype α] (P : FiniteKernel α)
    (t : NNReal) (x : α) : FiniteLaw α := by
  classical
  refine ⟨fun y => P.poissonized t (FiniteKernel.eventIndicator {y}) x,
    fun y => (P.poissonized_event_bounds t {y} x).1,?_⟩
  rw [← poisson_finite_sum]
  have h : (fun z => ∑ y : α, FiniteKernel.eventIndicator {y} z) = (fun _ => (1 : ℝ)) := by
    funext z
    simp [FiniteKernel.eventIndicator]
  rw [h,poisson_constant]

theorem poissonLaw_expect {α : Type*} [Fintype α] (P : FiniteKernel α)
    (t : NNReal) (x : α) (f : α → ℝ) :
    (poissonLaw P t x).expect f = P.poissonized t f x := by
  classical
  unfold FiniteLaw.expect poissonLaw
  have hterm (y : α) : P.poissonized t (FiniteKernel.eventIndicator {y}) x*f y =
      P.poissonized t (fun z => f y*FiniteKernel.eventIndicator {y} z) x := by
    rw [poisson_scalar]
    ring
  simp_rw [hterm]
  rw [← poisson_finite_sum]
  congr 1
  funext z
  simp [FiniteKernel.eventIndicator,mul_ite]

end HeritableCompositions
