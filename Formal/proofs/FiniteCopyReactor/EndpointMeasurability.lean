import proofs.FiniteCopyReactor.EndpointBounds
import proofs.FiniteCopyReactor.ClockEndpoint

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopy
open scoped ENNReal BigOperators

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem chronological_endpoint_measurable (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (f : α → ℝ≥0∞) :
    Measurable (fun p : ℝ × α => chronologicalEndpoint next rate hr ht f p.2 p.1) := by
  apply measurable_from_prod_countable_left
  intro x
  change Measurable (fun T => ∫⁻ z,endpointObservable (β := β) f T z ∂jumpTrajectoryLaw x next rate hr ht)
  exact (endpoint_observable_measurable (β := β) f).lintegral_prod_right'

omit [MeasurableSpace β] [MeasurableSingletonClass β] in
theorem clock_endpoint_measurable (P : MarkedKernel α β) (q : ℝ) (f : α → ℝ≥0∞) :
    Measurable (fun p : ℝ × α => clockEndpoint P q p.1 f p.2) := by
  apply measurable_from_prod_countable_left
  intro x
  change Measurable (fun T => ∑' n,ENNReal.ofReal (clockWeight q T n)*tickValue P n f x)
  apply Measurable.tsum
  intro n
  exact (clockWeight_continuous q n).measurable.ennreal_ofReal.mul measurable_const

omit [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β] in
theorem clock_endpoint_le_one (P : MarkedKernel α β) (q T : ℝ) (hq : 0 ≤ q) (hT : 0 ≤ T)
    (f : α → ℝ≥0∞) (hf : ∀ x,f x ≤ 1) (x : α) : clockEndpoint P q T f x ≤ 1 := by
  have htick (n) : tickValue P n f x ≤ 1 :=
    (tick_value_mono P n f (fun _ => 1) hf x).trans_eq (tick_value_const P n 1 x)
  calc
    _ ≤ ∑' n,ENNReal.ofReal (clockWeight q T n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      simpa only [mul_one] using mul_le_mul_right (htick n) (ENNReal.ofReal (clockWeight q T n))
    _ = 1 := by
      let a : NNReal := ⟨q,hq⟩
      let b : NNReal := ⟨T,hT⟩
      change (∑' n,ENNReal.ofReal (clockWeight a b n))=1
      simp_rw [clockWeight_eq_poisson]
      rw [← ENNReal.ofReal_tsum_of_nonneg (poissonWeight_nonneg (a*b)) (poissonWeight_sum (a*b)).summable,
        (poissonWeight_sum (a*b)).tsum_eq,ENNReal.ofReal_one]

end
end FiniteCopyReactor
