import proofs.HeritableCompositions.EventExponential

namespace HeritableCompositions
open FiniteCopy

theorem steps_affine_decay {α : Type*} [Fintype α] (P : FiniteKernel α)
    (W : α → ℝ) (r C : ℝ) (hr : 0 ≤ r)
    (hstep : ∀ x, P.step W x ≤ r*W x+(1-r)*C) (n : ℕ) (x : α) :
    P.steps n W x ≤ r^n*W x+(1-r^n)*C := by
  induction n generalizing x with
  | zero => simp [FiniteKernel.steps]
  | succ n ih =>
    have hm := P.step_mono ih x
    rw [P.step_add,P.step_scale,P.step_const] at hm
    have hh := mul_le_mul_of_nonneg_left (hstep x) (pow_nonneg hr n)
    change P.step (P.steps n W) x ≤ _
    rw [pow_succ]
    nlinarith only [hm,hh]

theorem poissonized_event_affine {α : Type*} [Fintype α] (P : FiniteKernel α)
    (t : NNReal) (A : Set α) (W : α → ℝ) (a r C : ℝ)
    (hW : ∀ x, 0 ≤ W x) (hA : ∀ x ∈ A, a ≤ W x) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hstep : ∀ x, P.step W x ≤ r*W x+(1-r)*C) (x : α) :
    a*P.poissonized t (FiniteKernel.eventIndicator A) x ≤
      Real.exp ((t : ℝ)*(r-1))*W x+C := by
  have hind : ∀ y, a*FiniteKernel.eventIndicator A y ≤ W y := by
    intro y
    classical
    by_cases hy : y ∈ A
    · simpa [FiniteKernel.eventIndicator,hy] using hA y hy
    · simpa [FiniteKernel.eventIndicator,hy] using hW y
  have hiter (n : ℕ) : a*P.steps n (FiniteKernel.eventIndicator A) x ≤ r^n*W x+C := by
    have hm := P.steps_mono hind n x
    rw [P.steps_scale] at hm
    have hd := steps_affine_decay P W r C hr hstep n x
    nlinarith only [hm,hd,mul_nonneg (pow_nonneg hr n) hC]
  have hsR : HasSum (fun n => poissonWeight t n*(r^n*W x+C))
      (Real.exp ((t : ℝ)*(r-1))*W x+C) := by
    convert ((poissonWeight_geometric t r).mul_right (W x)).add ((poissonWeight_sum t).mul_right C) using 1
    · funext n
      ring
    · ring
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
    _ ≤ ∑' n, poissonWeight t n*(r^n*W x+C) :=
      Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hiter n)
        (poissonWeight_nonneg t n)) hsL hsR.summable
    _ = _ := hsR.tsum_eq

theorem uniformized_event_affine {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (q t : NNReal)
    (hq : 0 < (q : ℝ)) (hclock : ∀ x, M.total x ≤ q)
    (A : Set α) (W : α → ℝ) (a k C : ℝ)
    (hW : ∀ x, 0 ≤ W x) (hA : ∀ x ∈ A, a ≤ W x) (hk : k ≤ q) (hC : 0 ≤ C)
    (hgen : ∀ x, M.generator W x ≤ -k*W x+k*C) (x : α) :
    a*(M.uniformize q hq hclock).poissonized (q*t) (FiniteKernel.eventIndicator A) x ≤
      Real.exp (-k*(t : ℝ))*W x+C := by
  have hr : 0 ≤ 1-k/(q : ℝ) := sub_nonneg.mpr ((div_le_one hq).mpr hk)
  have hstep (y) : (M.uniformize q hq hclock).step W y ≤
      (1-k/(q : ℝ))*W y+(1-(1-k/(q : ℝ)))*C := by
    rw [M.uniformize_step]
    have hh := div_le_div_of_nonneg_right (hgen y) hq.le
    calc
      W y+M.generator W y/(q : ℝ) ≤ W y+(-k*W y+k*C)/(q : ℝ) := add_le_add le_rfl hh
      _ = _ := by ring
  have h := poissonized_event_affine (M.uniformize q hq hclock) (q*t)
    A W a (1-k/(q : ℝ)) C hW hA hr hC hstep x
  have heq : ((q*t : NNReal) : ℝ)*((1-k/(q : ℝ))-1) = -k*(t : ℝ) := by
    rw [NNReal.coe_mul]
    field_simp
    ring
  simpa only [heq] using h

end HeritableCompositions
