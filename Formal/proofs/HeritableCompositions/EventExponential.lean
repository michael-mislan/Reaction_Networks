import proofs.FiniteCopy.UniformizedBounds

namespace HeritableCompositions
open FiniteCopy

theorem poissonized_event_exponential {α : Type*} [Fintype α]
    (P : FiniteKernel α) (t : NNReal) (A : Set α) (W : α → ℝ) (a r : ℝ)
    (hW : ∀ x, 0 ≤ W x) (hA : ∀ x ∈ A, a ≤ W x) (hr : 0 ≤ r)
    (hstep : ∀ x, P.step W x ≤ r*W x) (x : α) :
    a*P.poissonized t (FiniteKernel.eventIndicator A) x ≤
      Real.exp ((t : ℝ)*(r-1))*W x := by
  have hind : ∀ y, a*FiniteKernel.eventIndicator A y ≤ W y := by
    intro y
    classical
    by_cases hy : y ∈ A
    · simpa [FiniteKernel.eventIndicator,hy] using hA y hy
    · simpa [FiniteKernel.eventIndicator,hy] using hW y
  have hiter (n : ℕ) : a*P.steps n (FiniteKernel.eventIndicator A) x ≤ r^n*W x := by
    have hm := P.steps_mono hind n x
    rw [P.steps_scale] at hm
    exact hm.trans (P.steps_decay_bound W r hr hstep n x)
  have hsR : HasSum (fun n => poissonWeight t n*(r^n*W x))
      (Real.exp ((t : ℝ)*(r-1))*W x) := by
    convert (poissonWeight_geometric t r).mul_right (W x) using 1
    funext n
    ring
  have hsL : Summable (fun n => poissonWeight t n*(a*P.steps n (FiniteKernel.eventIndicator A) x)) := by
    convert (P.event_summable t A x).mul_left a using 1
    funext n
    ring
  calc
    a*P.poissonized t (FiniteKernel.eventIndicator A) x =
      ∑' n, poissonWeight t n*(a*P.steps n (FiniteKernel.eventIndicator A) x) := by
        rw [FiniteKernel.poissonized, ← tsum_mul_left]
        congr 1
        funext n
        ring
    _ ≤ ∑' n, poissonWeight t n*(r^n*W x) :=
      Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hiter n)
        (poissonWeight_nonneg t n)) hsL hsR.summable
    _ = _ := hsR.tsum_eq

theorem uniformized_event_exponential {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (q t : NNReal)
    (hq : 0 < (q : ℝ)) (hclock : ∀ x, M.total x ≤ q)
    (A : Set α) (W : α → ℝ) (a k : ℝ)
    (hW : ∀ x, 0 ≤ W x) (hA : ∀ x ∈ A, a ≤ W x) (hk : k ≤ q)
    (hgen : ∀ x, M.generator W x ≤ -k*W x) (x : α) :
    a*(M.uniformize q hq hclock).poissonized (q*t) (FiniteKernel.eventIndicator A) x ≤
      Real.exp (-k*(t : ℝ))*W x := by
  have hr : 0 ≤ 1-k/(q : ℝ) := sub_nonneg.mpr ((div_le_one hq).mpr hk)
  have h := poissonized_event_exponential (M.uniformize q hq hclock) (q*t)
    A W a (1-k/(q : ℝ)) hW hA hr (M.uniformize_decay q hq hclock W k hgen) x
  have heq : ((q*t : NNReal) : ℝ)*((1-k/(q : ℝ))-1) = -k*(t : ℝ) := by
    rw [NNReal.coe_mul]
    field_simp
    ring
  simpa only [heq] using h

end HeritableCompositions
