import proofs.FiniteCopy.UniformizedBounds

namespace FiniteCopy
open scoped NNReal
namespace FiniteKernel
variable {α : Type*} [Fintype α] (P : FiniteKernel α)

theorem nonneg_summable (t : ℝ≥0) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (x : α) :
    Summable (fun n => poissonWeight t n*P.steps n f x) := by
  have hbound (y) : f y ≤ ∑ z, f z :=
    Finset.single_le_sum (fun z _ => hf z) (Finset.mem_univ y)
  have hstep (n) : P.steps n f x ≤ ∑ z, f z := by
    have h := P.steps_mono hbound n x
    simpa only [P.steps_const] using h
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (poissonWeight_nonneg t n) (P.steps_nonneg n hf x))
    (fun n => mul_le_mul_of_nonneg_left (hstep n) (poissonWeight_nonneg t n))
    ((poissonWeight_sum t).mul_right (∑ z, f z)).summable

theorem poissonized_nonneg (t : ℝ≥0) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (x : α) :
    0 ≤ P.poissonized t f x :=
  tsum_nonneg (fun n => mul_nonneg (poissonWeight_nonneg t n) (P.steps_nonneg n hf x))

theorem poissonized_mono (t : ℝ≥0) (f g : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (hfg : ∀ x, f x ≤ g x) (x : α) :
    P.poissonized t f x ≤ P.poissonized t g x :=
  Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (P.steps_mono hfg n x)
    (poissonWeight_nonneg t n)) (P.nonneg_summable t f hf x) (P.nonneg_summable t g hg x)

theorem poissonized_const (t : ℝ≥0) (c : ℝ) (x : α) :
    P.poissonized t (fun _ => c) x = c := by
  unfold poissonized
  simp_rw [P.steps_const]
  simpa only [one_mul] using ((poissonWeight_sum t).mul_right c).tsum_eq

theorem steps_add (n : ℕ) (f g : α → ℝ) (x : α) :
    P.steps n (fun y => f y+g y) x = P.steps n f x+P.steps n g x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change P.step (P.steps n (fun y => f y+g y)) x = P.step (P.steps n f) x+P.step (P.steps n g) x
    rw [show P.steps n (fun y => f y+g y) = (fun y => P.steps n f y+P.steps n g y) from funext ih]
    exact P.step_add _ _ x

theorem poissonized_add (t : ℝ≥0) (f g : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (x : α) :
    P.poissonized t (fun y => f y+g y) x = P.poissonized t f x+P.poissonized t g x := by
  unfold poissonized
  simp_rw [P.steps_add,mul_add]
  exact (P.nonneg_summable t f hf x).tsum_add (P.nonneg_summable t g hg x)

theorem poissonized_scale (t : ℝ≥0) (c : ℝ) (f : α → ℝ) (x : α) :
    P.poissonized t (fun y => c*f y) x = c*P.poissonized t f x := by
  unfold poissonized
  simp_rw [P.steps_scale]
  rw [← tsum_mul_left]
  congr 1
  funext n
  ring

theorem poissonized_drift_bound (t : ℝ≥0) (V : α → ℝ) (b : ℝ)
    (hV : ∀ x, 0 ≤ V x) (h : ∀ x, P.step V x ≤ V x+b) (x : α) :
    P.poissonized t V x ≤ V x+(t : ℝ)*b := by
  have hs : HasSum (fun n => poissonWeight t n*(V x+(n : ℝ)*b)) (V x+(t : ℝ)*b) := by
    convert ((poissonWeight_sum t).mul_right (V x)).add ((poissonWeight_mean t).mul_right b) using 1
    · funext n; ring
    · ring
  exact (Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left
    (P.steps_drift_bound V b h n x) (poissonWeight_nonneg t n))
    (P.nonneg_summable t V hV x) hs.summable).trans_eq hs.tsum_eq

end FiniteKernel
end FiniteCopy
