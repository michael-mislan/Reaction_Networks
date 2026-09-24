import proofs.FiniteCopy.KernelExpectations

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy Classical
open scoped BigOperators NNReal

theorem finite_steps_sum {α ι : Type*} [Fintype α] [Fintype ι] (P : FiniteKernel α)
    (f : ι → α → ℝ) (n : ℕ) (x : α) :
    P.steps n (fun y => ∑ i,f i y) x=∑ i,P.steps n (f i) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change (∑ y,P.prob x y*P.steps n (fun z => ∑ i,f i z) y) = _
    simp only [ih,Finset.mul_sum]
    rw [Finset.sum_comm]
    rfl

def pointTest {α : Type*} (y : α) (x : α) : ℝ := if x=y then 1 else 0

theorem finite_steps_basis {α : Type*} [Fintype α] (P : FiniteKernel α)
    (f : α → ℝ) (n : ℕ) (x : α) :
    P.steps n f x=∑ y,f y*P.steps n (pointTest y) x := by
  have hf : f=(fun z => ∑ y,f y*pointTest y z) := by
    funext z
    simp [pointTest]
  conv_lhs => rw [hf]
  rw [finite_steps_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact P.steps_scale n (f y) (pointTest y) x

theorem finite_poisson_basis {α : Type*} [Fintype α] (P : FiniteKernel α)
    (f : α → ℝ) (t : NNReal) (x : α) :
    P.poissonized t f x=∑ y,f y*P.poissonized t (pointTest y) x := by
  have hs (y : α) : Summable (fun n => poissonWeight t n*(f y*P.steps n (pointTest y) x)) := by
    have hn (z : α) : 0 ≤ pointTest y z := by unfold pointTest; split_ifs <;> norm_num
    convert (P.nonneg_summable t (pointTest y) hn x).mul_left (f y) using 1
    funext n
    ring
  unfold FiniteKernel.poissonized
  simp_rw [finite_steps_basis P f,Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun y _ => hs y)]
  apply Finset.sum_congr rfl
  intro y _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

theorem finite_poisson_tsum {α : Type*} [Fintype α] (P : FiniteKernel α)
    (f : ℕ → α → ℝ) (hf : ∀ x, Summable (fun n => f n x)) (t : NNReal) (x : α) :
    P.poissonized t (fun y => ∑' n,f n y) x=∑' n,P.poissonized t (f n) x := by
  rw [finite_poisson_basis]
  have he (n) := finite_poisson_basis P (f n) t x
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun y _ => (hf y).mul_right (P.poissonized t (pointTest y) x))]
  simp_rw [tsum_mul_right]

end
end FiniteCopyReactor
