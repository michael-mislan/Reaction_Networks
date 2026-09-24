import proofs.CompositionalMemory.SafeClockBounds
import proofs.CompositionalMemory.CausalDeadlineIntegral

namespace CompositionalMemory
open Classical RandomViability FiniteCopy MeasureTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 60000
variable {α : Type*} [Fintype α]

def causalSafeClock (P : FiniteKernel α) (D : Set α) (f : α → ℝ≥0∞) (q T : ℝ) (x : α) : ℝ≥0∞ :=
  if 0 ≤ T then safeClockPayoff P D f q T x else 0

theorem causalSafeClock_negative (P : FiniteKernel α) (D : Set α) (f : α → ℝ≥0∞)
    (q T : ℝ) (hT : T < 0) (x : α) : causalSafeClock P D f q T x=0 := by
  simp only [causalSafeClock,if_neg (not_le.mpr hT)]

theorem causalSafeClock_le_one (P : FiniteKernel α) (D : Set α) (f : α → ℝ≥0∞)
    (hf : ∀ x,f x ≤ 1) (q : NNReal) (T : ℝ) (x : α) : causalSafeClock P D f q T x ≤ 1 := by
  by_cases hT : 0 ≤ T
  · rw [causalSafeClock,if_pos hT]
    exact (show safeClockPayoff P D f q T x ≤ 1 from safeClockPayoff_le_one P D f hf q ⟨T,hT⟩ x)
  · simp only [causalSafeClock,if_neg hT]; exact zero_le

/-- The finite Poisson law obeys the same causal common-clock integral form. -/
theorem causalSafeClock_causal (P : FiniteKernel α) (D : Set α) (f : α → ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) (x : α) (hx : x ∈ D) :
    causalSafeClock P D f q T x=causalExp q T*f x+
      renewalConv (causalExp q)
        (fun t => ENNReal.ofReal q*∑ y,ENNReal.ofReal (P.prob x y)*causalSafeClock P D f q t y) T := by
  have hn (t : ℝ) (ht : t < 0) :
      ENNReal.ofReal q*(∑ y,ENNReal.ofReal (P.prob x y)*causalSafeClock P D f q t y)=0 := by
    simp only [causalSafeClock_negative P D f q t ht,mul_zero,Finset.sum_const_zero]
  rw [causalConv_deadline_integral q T _ hn]
  have he : (∫⁻ u in Set.Ioc 0 T,ENNReal.ofReal (Real.exp (-q*(T-u)))*
      (ENNReal.ofReal q*∑ y,ENNReal.ofReal (P.prob x y)*causalSafeClock P D f q u y)) =
      ∫⁻ u in Set.Ioc 0 T,ENNReal.ofReal (q*Real.exp (-q*(T-u)))*
        ∑ y,ENNReal.ofReal (P.prob x y)*safeClockPayoff P D f q u y := by
    apply lintegral_congr_ae
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    apply Filter.Eventually.of_forall
    intro u hu
    simp only [causalSafeClock,if_pos hu.1.le,ENNReal.ofReal_mul hq]
    ring
  rw [he]
  simp only [causalSafeClock,if_pos hT,causalExp]
  rw [safeClockPayoff_renewal P D f q T hq hT x,if_pos hx]

theorem causalSafeClock_outside (P : FiniteKernel α) (D : Set α) (f : α → ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (x : α) (hx : x ∉ D) : causalSafeClock P D f q T x=0 := by
  by_cases hT : 0 ≤ T
  · rw [causalSafeClock,if_pos hT,safeClockPayoff_renewal P D f q T hq hT x,if_neg hx]
  · exact causalSafeClock_negative P D f q T (lt_of_not_ge hT) x

theorem causalSafeClock_causal_all (P : FiniteKernel α) (D : Set α) (f : α → ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (x : α) (hx : x ∈ D) :
    causalSafeClock P D f q T x=causalExp q T*f x+
      renewalConv (causalExp q)
        (fun t => ENNReal.ofReal q*∑ y,ENNReal.ofReal (P.prob x y)*causalSafeClock P D f q t y) T := by
  by_cases hT : 0 ≤ T
  · exact causalSafeClock_causal P D f q hq T hT x hx
  · rw [causalSafeClock_negative P D f q T (lt_of_not_ge hT) x]
    simp only [causalExp,if_neg hT,zero_mul,zero_add]
    symm
    apply lintegral_eq_zero_of_ae_eq_zero
    apply Filter.Eventually.of_forall
    intro u
    by_cases hu : 0 ≤ u
    · have htu : T-u < 0 := by linarith
      simp only [causalSafeClock_negative P D f q (T-u) htu,mul_zero,Finset.sum_const_zero,Pi.zero_apply]
    · simp [causalExp,hu]

variable [MeasurableSpace α] [MeasurableSingletonClass α]

theorem causalSafeClock_measurable (P : FiniteKernel α) (D : Set α) (f : α → ℝ≥0∞) (q : ℝ) :
    Measurable (fun p : α × ℝ => causalSafeClock P D f q p.2 p.1) := by
  exact Measurable.ite (measurableSet_le measurable_const measurable_snd)
    (safeClockPayoff_measurable P D f q) measurable_const

end
end CompositionalMemory
