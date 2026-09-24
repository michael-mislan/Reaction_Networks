import proofs.FiniteCopyReactor.MarkedExpectations
import proofs.RandomViability.PoissonRenewalSeries

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopy
open scoped ENNReal BigOperators

def tickValue {α β : Type*} [Fintype β] (P : MarkedKernel α β) : ℕ → (α → ℝ≥0∞) → α → ℝ≥0∞
  | 0,f,x => f x
  | n+1,f,x => ∑ b,ENNReal.ofReal (P.prob x b)*tickValue P n f (P.next x b)

theorem tick_value_const {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (n : ℕ) (c : ℝ≥0∞) (x : α) : tickValue P n (fun _ => c) x=c := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [tickValue,ih,← Finset.sum_mul]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => P.nonneg x b),P.row_sum,ENNReal.ofReal_one,one_mul]

theorem tick_value_mono {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (n : ℕ) (f g : α → ℝ≥0∞) (h : ∀ x,f x ≤ g x) (x : α) : tickValue P n f x ≤ tickValue P n g x := by
  induction n generalizing x with
  | zero => exact h x
  | succ n ih => exact Finset.sum_le_sum (fun b _ => mul_le_mul_right (ih _) _)

theorem tick_value_real {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (n : ℕ) (f : α → ℝ) (hf : ∀ x,0 ≤ f x) (x : α) (z : ℝ) :
    tickValue P n (fun x => ENNReal.ofReal (f x)) x=ENNReal.ofReal (P.law n (fun y _ => f y) x z) := by
  have hn (k y w) : 0 ≤ P.law k (fun y _ => f y) y w := by
    have h := P.law_mono (fun _ _ => 0) (fun y _ => f y) (fun y _ => hf y) k y w
    simpa only [P.law_const] using h
  induction n generalizing x z with
  | zero => rfl
  | succ n ih =>
    change (∑ b,ENNReal.ofReal (P.prob x b)*tickValue P n (fun x => ENNReal.ofReal (f x)) (P.next x b))=
      ENNReal.ofReal (∑ b,P.prob x b*P.law n (fun y _ => f y) (P.next x b) (z+P.mark b))
    rw [ENNReal.ofReal_sum_of_nonneg (fun b _ => mul_nonneg (P.nonneg x b) (hn n _ _))]
    apply Finset.sum_congr rfl
    intro b _
    rw [ih (P.next x b) (z+P.mark b),ENNReal.ofReal_mul (P.nonneg x b)]

def clockEndpoint {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (q T : ℝ) (f : α → ℝ≥0∞) (x : α) : ℝ≥0∞ :=
  ∑' n,ENNReal.ofReal (clockWeight q T n)*tickValue P n f x

theorem clock_endpoint_shift {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (q u : ℝ) (f : α → ℝ≥0∞) (x : α) :
    (∑' n,ENNReal.ofReal (clockWeight q u n)*tickValue P (n+1) f x)=
      ∑ b,ENNReal.ofReal (P.prob x b)*clockEndpoint P q u f (P.next x b) := by
  simp only [tickValue,Finset.mul_sum]
  calc
    _ = ∑ b,∑' n,ENNReal.ofReal (clockWeight q u n)*
        (ENNReal.ofReal (P.prob x b)*tickValue P n f (P.next x b)) := by
      simp_rw [← tsum_fintype (L := SummationFilter.unconditional β)]
      exact ENNReal.tsum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      unfold clockEndpoint
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro n
      ac_rfl

theorem clock_endpoint_renewal {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (q T : ℝ) (hq : 0 ≤ q) (hT : 0 ≤ T) (f : α → ℝ≥0∞) (x : α) :
    clockEndpoint P q T f x=ENNReal.ofReal (Real.exp (-q*T))*f x+
      ∫⁻ u in Set.Ioc 0 T,ENNReal.ofReal (q*Real.exp (-q*(T-u)))*
        ∑ b,ENNReal.ofReal (P.prob x b)*clockEndpoint P q u f (P.next x b) := by
  have h := clockWeight_series_renewal q T hq hT (fun n => tickValue P n f x)
  simp_rw [clock_endpoint_shift] at h
  simpa only [clockEndpoint,tickValue] using h

end
end FiniteCopyReactor
