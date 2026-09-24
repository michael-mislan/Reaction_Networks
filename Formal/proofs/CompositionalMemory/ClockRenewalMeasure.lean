import proofs.RandomViability.WeightedRenewal
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace CompositionalMemory
open Classical RandomViability MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 60000
variable {α : Type*} [MeasurableSpace α]

def clockRenewalMeasure (K : α → PMF α) (q : ℝ) (D : Set α) (p : α × ℝ) : Measure (α × ℝ) :=
  if p.1 ∈ D ∧ 0 ≤ p.2 then
    ((K p.1).toMeasure.prod (expMeasure q)).map (fun y : α × ℝ => (y.1,p.2-y.2))
  else 0

def clockRenewalWeight (q : ℝ) (p : α × ℝ) : ℝ :=
  if 0 ≤ p.2 then Real.exp (q*p.2) else 0

theorem clockRenewalWeight_measurable (q : ℝ) : Measurable (clockRenewalWeight (α := α) q) := by
  exact Measurable.ite (measurableSet_le measurable_const measurable_snd) (by fun_prop) measurable_const

/-- The common clock contracts the causal exponential weight by at least one half. -/
theorem clock_renewal_half_weight (K : α → PMF α) (q : ℝ) (hq : 0 < q) (D : Set α) (p : α × ℝ) :
    (∫⁻ y,ENNReal.ofReal (clockRenewalWeight q y) ∂clockRenewalMeasure K q D p) ≤
      ENNReal.ofReal (1/2 : ℝ)*ENNReal.ofReal (clockRenewalWeight q p) := by
  letI := isProbabilityMeasure_expMeasure hq
  unfold clockRenewalMeasure
  by_cases hp : p.1 ∈ D ∧ 0 ≤ p.2
  · rw [if_pos hp,lintegral_map (clockRenewalWeight_measurable q).ennreal_ofReal
      (measurable_fst.prodMk (measurable_const.sub measurable_snd))]
    have hm : Measurable (fun y : α × ℝ => ENNReal.ofReal (Real.exp (q*(p.2-y.2)))) := by fun_prop
    calc
      _ ≤ ∫⁻ y,ENNReal.ofReal (Real.exp (q*(p.2-y.2))) ∂(K p.1).toMeasure.prod (expMeasure q) := by
        apply lintegral_mono
        intro y
        apply ENNReal.ofReal_le_ofReal
        simp only [clockRenewalWeight]
        split_ifs <;> first | exact le_rfl | exact (Real.exp_pos _).le
      _ = ENNReal.ofReal (Real.exp (q*p.2))*ENNReal.ofReal (1/2 : ℝ) := by
        rw [lintegral_prod _ hm.aemeasurable]
        dsimp only
        rw [exponential_renewal_half_weight q p.2 hq,lintegral_const]
        simp only [measure_univ,mul_one]
      _ = _ := by simp only [clockRenewalWeight,if_pos hp.2]; exact mul_comm _ _
  · rw [if_neg hp,lintegral_zero_measure]
    exact zero_le

/-- Bounded causal solutions of the same finite-clock renewal equation coincide. -/
theorem clock_renewal_unique (K : α → PMF α) (q : ℝ) (hq : 0 < q) (D : Set α)
    (F G B : α × ℝ → ℝ≥0∞) (hFm : Measurable F) (hGm : Measurable G)
    (hFb : ∀ p,F p ≤ 1) (hGb : ∀ p,G p ≤ 1)
    (hFneg : ∀ p,p.2 < 0 → F p=0) (hGneg : ∀ p,p.2 < 0 → G p=0)
    (hF : ∀ p,F p=B p+∫⁻ y,F y ∂clockRenewalMeasure K q D p)
    (hG : ∀ p,G p=B p+∫⁻ y,G y ∂clockRenewalMeasure K q D p) : F=G := by
  have hb (J : α × ℝ → ℝ≥0∞) (hJ : ∀ p,J p ≤ 1) (hJn : ∀ p,p.2 < 0 → J p=0)
      (p : α × ℝ) : J p ≤ ENNReal.ofReal (clockRenewalWeight q p) := by
    by_cases hp : 0 ≤ p.2
    · apply (hJ p).trans
      simp only [clockRenewalWeight,if_pos hp]
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hq.le hp))
    · rw [hJn p (lt_of_not_ge hp)]
      exact zero_le
  exact weighted_half_renewal_unique (clockRenewalMeasure K q D) F G B (clockRenewalWeight q)
    hFm hGm (clockRenewalWeight_measurable q) (hb F hFb hFneg) (hb G hGb hGneg)
    hF hG (clock_renewal_half_weight K q hq D)

end
end CompositionalMemory
