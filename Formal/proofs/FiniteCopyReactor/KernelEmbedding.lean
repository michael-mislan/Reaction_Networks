import proofs.FiniteCopyReactor.CausalClock

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory RandomViability FiniteCopy
open scoped ENNReal

variable {α γ β : Type*} [Fintype β]

/-- A state map need commute only on supported labels; zero-probability updates are irrelevant. -/
theorem tick_value_map (P : MarkedKernel α β) (Q : MarkedKernel γ β) (φ : α → γ)
    (hp : ∀ x b,P.prob x b=Q.prob (φ x) b)
    (hn : ∀ x b,P.prob x b ≠ 0 → φ (P.next x b)=Q.next (φ x) b)
    (f : γ → ℝ≥0∞) (n : ℕ) (x : α) :
    tickValue P n (fun y => f (φ y)) x=tickValue Q n f (φ x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change (∑ b,ENNReal.ofReal (P.prob x b)*tickValue P n (fun y => f (φ y)) (P.next x b))=
      ∑ b,ENNReal.ofReal (Q.prob (φ x) b)*tickValue Q n f (Q.next (φ x) b)
    apply Finset.sum_congr rfl
    intro b _
    by_cases hz : P.prob x b=0
    · rw [← hp x b,hz,ENNReal.ofReal_zero,zero_mul,zero_mul]
    · rw [ih,hn x b hz,hp x b]

theorem clock_endpoint_map (P : MarkedKernel α β) (Q : MarkedKernel γ β) (φ : α → γ)
    (hp : ∀ x b,P.prob x b=Q.prob (φ x) b)
    (hn : ∀ x b,P.prob x b ≠ 0 → φ (P.next x b)=Q.next (φ x) b)
    (f : γ → ℝ≥0∞) (q T : ℝ) (x : α) :
    clockEndpoint P q T (fun y => f (φ y)) x=clockEndpoint Q q T f (φ x) := by
  unfold clockEndpoint
  apply tsum_congr
  intro n
  rw [tick_value_map P Q φ hp hn]

theorem causal_clock_map (P : MarkedKernel α β) (Q : MarkedKernel γ β) (φ : α → γ)
    (hp : ∀ x b,P.prob x b=Q.prob (φ x) b)
    (hn : ∀ x b,P.prob x b ≠ 0 → φ (P.next x b)=Q.next (φ x) b)
    (f : γ → ℝ≥0∞) (q T : ℝ) (x : α) :
    causalClockEndpoint P q (fun y => f (φ y)) x T=causalClockEndpoint Q q f (φ x) T := by
  unfold causalClockEndpoint
  rw [clock_endpoint_map P Q φ hp hn]

theorem clock_endpoint_real_nn (P : MarkedKernel α β) (q T : NNReal)
    (f : α → ℝ) (C : ℝ) (hf : ∀ y,0 ≤ f y ∧ f y ≤ C) (x : α) (z : ℝ) :
    clockEndpoint P q T (fun y => ENNReal.ofReal (f y)) x=
      ENNReal.ofReal (P.poissonized (q*T) (fun y _ => f y) x z) := by
  unfold clockEndpoint MarkedKernel.poissonized
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (poissonWeight_nonneg (q*T) n)
      (marked_law_bounds P (fun y _ => f y) C (fun y _ => hf y) n x z).1)
    (marked_summable P (fun y _ => f y) C (fun y _ => hf y) (q*T) x z)]
  simp_rw [clockWeight_eq_poisson,tick_value_real P _ f (fun y => (hf y).1) _ z,
    ENNReal.ofReal_mul (poissonWeight_nonneg (q*T) _)]

end
end FiniteCopyReactor
