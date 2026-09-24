import proofs.RandomViability.PoissonRenewalSeries
import proofs.FiniteCopy.FiniteKernel

namespace CompositionalMemory
open Classical RandomViability FiniteCopy MeasureTheory
open scoped ENNReal
noncomputable section
variable {α : Type*} [Fintype α]

/-- Safe-history iteration with an arbitrary nonnegative continuation payoff. -/
def safeClockSteps (P : FiniteKernel α) (D : Set α) (f : α → ℝ≥0∞) : ℕ → α → ℝ≥0∞
  | 0,x => if x ∈ D then f x else 0
  | n+1,x => if x ∈ D then ∑ y,ENNReal.ofReal (P.prob x y)*safeClockSteps P D f n y else 0

def safeClockPayoff (P : FiniteKernel α) (D : Set α) (f : α → ℝ≥0∞)
    (q T : ℝ) (x : α) : ℝ≥0∞ :=
  ∑' n,ENNReal.ofReal (clockWeight q T n)*safeClockSteps P D f n x

theorem safeClockPayoff_shift (P : FiniteKernel α) (D : Set α) (f : α → ℝ≥0∞)
    (q T : ℝ) (x : α) (hx : x ∈ D) :
    (∑' n,ENNReal.ofReal (clockWeight q T n)*safeClockSteps P D f (n+1) x) =
      ∑ y,ENNReal.ofReal (P.prob x y)*safeClockPayoff P D f q T y := by
  simp only [safeClockSteps,if_pos hx,Finset.mul_sum]
  calc
    _ = ∑ y,∑' n,ENNReal.ofReal (clockWeight q T n)*
        (ENNReal.ofReal (P.prob x y)*safeClockSteps P D f n y) := by
      simp_rw [← tsum_fintype (L := SummationFilter.unconditional α)]
      exact ENNReal.tsum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      unfold safeClockPayoff
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro n
      ac_rfl

/-- First clock opportunity equation for precisely the same safe-history terminal payoff. -/
theorem safeClockPayoff_renewal (P : FiniteKernel α) (D : Set α) (f : α → ℝ≥0∞)
    (q T : ℝ) (hq : 0 ≤ q) (hT : 0 ≤ T) (x : α) :
    safeClockPayoff P D f q T x =
      if x ∈ D then ENNReal.ofReal (Real.exp (-q*T))*f x +
        ∫⁻ u in Set.Ioc 0 T,ENNReal.ofReal (q*Real.exp (-q*(T-u)))*
          ∑ y,ENNReal.ofReal (P.prob x y)*safeClockPayoff P D f q u y
      else 0 := by
  by_cases hx : x ∈ D
  · rw [if_pos hx]
    have hh := clockWeight_series_renewal q T hq hT (fun n => safeClockSteps P D f n x)
    simp_rw [safeClockPayoff_shift P D f q _ x hx] at hh
    simpa only [safeClockSteps,if_pos hx] using hh
  · rw [if_neg hx]
    apply ENNReal.tsum_eq_zero.mpr
    intro n
    cases n <;> simp only [safeClockSteps,if_neg hx,mul_zero]

end
end CompositionalMemory
