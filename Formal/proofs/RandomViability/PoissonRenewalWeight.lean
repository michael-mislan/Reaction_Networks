import proofs.FiniteCopy.PoissonKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace RandomViability
open MeasureTheory FiniteCopy
noncomputable section
set_option maxHeartbeats 30000

/-- Real-parameter extension used only on nonnegative time intervals. -/
def clockWeight (q t : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-q*t)*(q*t)^k/(k.factorial : ℝ)

theorem clockWeight_eq_poisson (q t : NNReal) (k : ℕ) :
    clockWeight q t k = poissonWeight (q*t) k := by
  simp only [clockWeight, poissonWeight, NNReal.coe_mul, neg_mul]

theorem clockWeight_continuous (q : ℝ) (k : ℕ) : Continuous (fun t => clockWeight q t k) := by
  unfold clockWeight
  fun_prop

theorem clockWeight_nonneg (q t : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t) (k : ℕ) :
    0 ≤ clockWeight q t k := by
  unfold clockWeight
  positivity

/-- First-tick convolution raises the Poisson opportunity count by one. -/
theorem clockWeight_renewal (q T : ℝ) (k : ℕ) :
    (∫ u in (0 : ℝ)..T, q*Real.exp (-q*(T-u))*clockWeight q u k) =
      clockWeight q T (k+1) := by
  have he (u : ℝ) : q*Real.exp (-q*(T-u))*clockWeight q u k =
      (q*Real.exp (-q*T)*q^k/(k.factorial : ℝ))*u^k := by
    unfold clockWeight
    have hh : Real.exp (-q*(T-u))*Real.exp (-q*u) = Real.exp (-q*T) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_pow]
    calc
      _ = q*(Real.exp (-q*(T-u))*Real.exp (-q*u))*q^k*u^k/(k.factorial : ℝ) := by ring
      _ = _ := by rw [hh]; ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  unfold clockWeight
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow]
  simp only [zero_pow (Nat.succ_ne_zero k), sub_zero]
  rw [pow_succ q k]
  field_simp

end
end RandomViability
