import proofs.FiniteCopy.FiniteJump
import proofs.StartupCount.DoubleLossTilt

set_option maxHeartbeats 40000

namespace FiniteCopy.FiniteKernel
variable {α : Type*} [Fintype α] (P : FiniteCopy.FiniteKernel α)

theorem steps_affine_decay (f : α → ℝ) (r b : ℝ) (hr : 0 ≤ r)
    (h : ∀ x,P.step f x ≤ r*f x+(1-r)*b) (n : ℕ) (x : α) :
    P.steps n f x ≤ r^n*f x+(1-r^n)*b := by
  induction n generalizing x with
  | zero => simp [steps]
  | succ n ih =>
    have hm := P.step_mono ih x
    rw [P.step_add,P.step_scale,P.step_const] at hm
    have hh := mul_le_mul_of_nonneg_left (h x) (pow_nonneg hr n)
    change P.step (P.steps n f) x ≤ _
    rw [pow_succ]
    nlinarith only [hm,hh]

/-- Affine drift pays a constant equilibrium floor. Only the actual iterated
kernel and its Poisson mixture occur; no Dynkin formula is assumed. -/
theorem poissonized_affine_decay (t : NNReal) (f : α → ℝ) (hf : ∀ x,0 ≤ f x)
    (r b : ℝ) (hr : 0 ≤ r) (hb : 0 ≤ b)
    (h : ∀ x,P.step f x ≤ r*f x+(1-r)*b) (x : α) :
    P.poissonized t f x ≤ Real.exp ((t : ℝ)*(r-1))*f x+b := by
  have hd (n : ℕ) : P.steps n f x ≤ r^n*f x+b := by
    have hh := P.steps_affine_decay f r b hr h n x
    have hp : 0 ≤ r^n*b := mul_nonneg (pow_nonneg hr n) hb
    linarith
  have hsR : HasSum (fun n => poissonWeight t n*(r^n*f x+b))
      (Real.exp ((t : ℝ)*(r-1))*f x+b) := by
    convert ((poissonWeight_geometric t r).mul_right (f x)).add
      ((poissonWeight_sum t).mul_right b) using 1
    · funext n; ring
    · ring
  have hm (n : ℕ) : poissonWeight t n*P.steps n f x ≤
      poissonWeight t n*(r^n*f x+b) :=
    mul_le_mul_of_nonneg_left (hd n) (poissonWeight_nonneg t n)
  have hsL : Summable (fun n => poissonWeight t n*P.steps n f x) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (poissonWeight_nonneg t n)
      (P.steps_nonneg n hf x)) hm hsR.summable
  exact (Summable.tsum_le_tsum hm hsL hsR.summable).trans_eq hsR.tsum_eq

theorem poissonized_affine_event (t : NNReal) (f : α → ℝ) (hf : ∀ x,0 ≤ f x)
    (r b a : ℝ) (hr : 0 ≤ r) (hb : 0 ≤ b) (A : Set α)
    (hA : ∀ y ∈ A,a ≤ f y)
    (h : ∀ x,P.step f x ≤ r*f x+(1-r)*b) (x : α) :
    a*P.poissonized t (eventIndicator A) x ≤ Real.exp ((t : ℝ)*(r-1))*f x+b := by
  classical
  have hind (y : α) : a*eventIndicator A y ≤ f y := by
    by_cases hy : y ∈ A
    · simpa [eventIndicator,hy] using hA y hy
    · simpa [eventIndicator,hy] using hf y
  have hd (n : ℕ) : a*P.steps n (eventIndicator A) x ≤ r^n*f x+b := by
    have hm := P.steps_mono hind n x
    rw [P.steps_scale] at hm
    have hh := P.steps_affine_decay f r b hr h n x
    have hp := mul_nonneg (pow_nonneg hr n) hb
    linarith
  have hsR : HasSum (fun n => poissonWeight t n*(r^n*f x+b))
      (Real.exp ((t : ℝ)*(r-1))*f x+b) := by
    convert ((poissonWeight_geometric t r).mul_right (f x)).add
      ((poissonWeight_sum t).mul_right b) using 1
    · funext n; ring
    · ring
  have hsL : Summable (fun n => poissonWeight t n*(a*P.steps n (eventIndicator A) x)) := by
    convert (P.event_summable t A x).mul_left a using 1
    funext n; ring
  calc
    _ = ∑' n,poissonWeight t n*(a*P.steps n (eventIndicator A) x) := by
      rw [poissonized,← tsum_mul_left]
      congr 1
      funext n; ring
    _ ≤ ∑' n,poissonWeight t n*(r^n*f x+b) :=
      Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hd n)
        (poissonWeight_nonneg t n)) hsL hsR.summable
    _ = _ := hsR.tsum_eq

end FiniteCopy.FiniteKernel

namespace FiniteCopy.FiniteJumpModel
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : FiniteJumpModel α β)

theorem poissonized_affine_generator (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ x,M.total x ≤ q) (f : α → ℝ) (hf : ∀ x,0 ≤ f x)
    (c B : ℝ) (hc : 0 < c) (hcq : c ≤ q) (hB : 0 ≤ B)
    (hgen : ∀ x,M.generator f x ≤ -c*f x+B) (x : α) :
    (M.uniformize q hq hclock).poissonized (q*t) f x ≤
      Real.exp (-c*(t : ℝ))*f x+B/c := by
  let r : ℝ := 1-c/q
  have hr : 0 ≤ r := sub_nonneg.mpr ((div_le_one hq).mpr hcq)
  have hstep (y : α) : (M.uniformize q hq hclock).step f y ≤ r*f y+(1-r)*(B/c) := by
    rw [M.uniformize_step]
    have hh := div_le_div_of_nonneg_right (hgen y) hq.le
    have he : f y+(-c*f y+B)/q = r*f y+(1-r)*(B/c) := by
      dsimp [r]
      field_simp [ne_of_gt hc, ne_of_gt hq]
      ring
    linarith only [hh, he]
  have h := (M.uniformize q hq hclock).poissonized_affine_decay (q*t) f hf r (B/c)
    hr (div_nonneg hB hc.le) hstep x
  have he : ((q*t : NNReal) : ℝ)*(r-1) = -c*(t : ℝ) := by
    dsimp [r]
    field_simp [ne_of_gt hq]
    ring
  simpa only [he] using h

end FiniteCopy.FiniteJumpModel

namespace StartupCount

theorem weighted_power_decreases (m K : ℕ) (hm : 10 ≤ m) (hK : m ≤ K) :
    (K : ℝ)*(9/10 : ℝ)^K ≤ (m : ℝ)*(9/10 : ℝ)^m := by
  induction K, hK using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    have hkreal : (10 : ℝ) ≤ k := by exact_mod_cast (hm.trans hk)
    have hp := pow_nonneg (show (0 : ℝ) ≤ 9/10 by norm_num) k
    have hstep : (k+1 : ℝ)*(9/10)*(9/10 : ℝ)^k ≤ (k : ℝ)*(9/10 : ℝ)^k := by
      nlinarith
    push_cast
    rw [pow_succ]
    nlinarith only [hstep,ih]

theorem affine_power_envelope (m K : ℕ) (hm : 10 ≤ m) (i a c : ℝ)
    (ha : 0 ≤ a) (hi : c+a*m ≤ i) :
    (-i+a*K)*(9/10 : ℝ)^K ≤ -c*(9/10 : ℝ)^K+a*m*(9/10 : ℝ)^m := by
  have hp : 0 ≤ (9/10 : ℝ)^K := by positivity
  have hb : 0 ≤ a*m*(9/10 : ℝ)^m := by positivity
  by_cases hK : K ≤ m
  · have hkm : (K : ℝ) ≤ m := by exact_mod_cast hK
    have hh := mul_le_mul_of_nonneg_left hkm ha
    have hi' := mul_le_mul_of_nonneg_right (show -i+a*K ≤ -c by linarith) hp
    linarith
  · have hw := mul_le_mul_of_nonneg_left (weighted_power_decreases m K hm (by omega)) ha
    have him : c ≤ i := by nlinarith [show (0 : ℝ) ≤ m by positivity]
    have hh := mul_le_mul_of_nonneg_right him hp
    nlinarith only [hw,hh]

end StartupCount
