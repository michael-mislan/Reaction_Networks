import proofs.FiniteCopy.KernelExpectations

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy Classical
open scoped NNReal

/-- Compare a continuing kernel to the same kernel frozen on a stopping set.
An upper drift bound pays for all evolution after the stopping time. -/
theorem stopped_steps_comparison {α : Type*} [Fintype α] (P Q : FiniteKernel α)
    (active : α → Prop) (hQ : ∀ f x, Q.step f x = if active x then P.step f x else f x)
    (f : α → ℝ) (b : ℝ) (hb : 0 ≤ b) (hf : ∀ x, P.step f x ≤ f x+b)
    (n : ℕ) (x : α) : P.steps n f x ≤ Q.steps n f x+(n:ℝ)*b := by
  have hfreeze (n : ℕ) (x : α) (hx : ¬active x) : Q.steps n f x=f x := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [FiniteKernel.steps,hQ,if_neg hx] using ih
  induction n generalizing x with
  | zero => simp only [FiniteKernel.steps,Nat.cast_zero,zero_mul,add_zero,le_refl]
  | succ n ih =>
    by_cases hx : active x
    · have h := P.step_mono ih x
      rw [P.step_add,P.step_const] at h
      change P.steps (n+1) f x ≤ _ at h
      have he : Q.steps (n+1) f x=P.step (Q.steps n f) x := by
        simp only [FiniteKernel.steps,hQ,if_pos hx]
      rw [← he] at h
      exact h.trans (by push_cast; nlinarith)
    · rw [hfreeze (n+1) x hx]
      exact P.steps_drift_bound f b hf (n+1) x

theorem stopped_poisson_comparison {α : Type*} [Fintype α] (P Q : FiniteKernel α)
    (active : α → Prop) (hQ : ∀ f x, Q.step f x = if active x then P.step f x else f x)
    (f : α → ℝ) (hf0 : ∀ x, 0 ≤ f x) (b : ℝ) (hb : 0 ≤ b)
    (hf : ∀ x, P.step f x ≤ f x+b) (t : ℝ≥0) (x : α) :
    P.poissonized t f x ≤ Q.poissonized t f x+(t:ℝ)*b := by
  have hm := (poissonWeight_mean t).mul_right b
  have hs := (Q.nonneg_summable t f hf0 x).add hm.summable
  have hh := Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left
      (stopped_steps_comparison P Q active hQ f b hb hf n x) (poissonWeight_nonneg t n))
    (P.nonneg_summable t f hf0 x)
    (show Summable (fun n => poissonWeight t n*(Q.steps n f x+(n:ℝ)*b)) by
      convert hs using 1; funext n; ring)
  apply hh.trans_eq
  simp_rw [mul_add]
  rw [Summable.tsum_add (Q.nonneg_summable t f hf0 x)]
  · congr 1
    convert hm.tsum_eq using 1
    congr 1
    funext n
    ring
  · convert hm.summable using 1
    funext n
    ring

end
end FiniteCopyReactor
