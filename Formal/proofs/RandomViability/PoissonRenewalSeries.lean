import proofs.RandomViability.PoissonRenewalWeight
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

namespace RandomViability
open MeasureTheory FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 30000

theorem clockWeight_renewal_lintegral (q T : ℝ) (hq : 0 ≤ q) (hT : 0 ≤ T) (k : ℕ) :
    (∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal
      (q*Real.exp (-q*(T-u))*clockWeight q u k)) =
      ENNReal.ofReal (clockWeight q T (k+1)) := by
  have hc : Continuous (fun u => q*Real.exp (-q*(T-u))*clockWeight q u k) := by
    unfold clockWeight
    fun_prop
  have hi : IntegrableOn (fun u => q*Real.exp (-q*(T-u))*clockWeight q u k) (Set.Ioc 0 T) :=
    hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 T)]
      (fun u => q*Real.exp (-q*(T-u))*clockWeight q u k) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    exact Filter.Eventually.of_forall (fun u hu => mul_nonneg (mul_nonneg hq (Real.exp_pos _).le)
      (clockWeight_nonneg q u hq hu.1.le k))
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    ← intervalIntegral.integral_of_le hT, clockWeight_renewal]

/-- Nonnegative Poisson mixtures satisfy the first-tick renewal identity.
The coefficients may encode state/reward events and need not be monotone. -/
theorem clockWeight_series_renewal (q T : ℝ) (hq : 0 ≤ q) (hT : 0 ≤ T)
    (a : ℕ → ℝ≥0∞) :
    (∑' k, ENNReal.ofReal (clockWeight q T k)*a k) =
      ENNReal.ofReal (Real.exp (-q*T))*a 0 +
        ∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (q*Real.exp (-q*(T-u))) *
          ∑' k, ENNReal.ofReal (clockWeight q u k)*a (k+1) := by
  have hm (k : ℕ) : Measurable (fun u => ENNReal.ofReal
      (q*Real.exp (-q*(T-u))*clockWeight q u k)) := by
    apply Measurable.ennreal_ofReal
    exact ((measurable_const.mul ((measurable_const.mul (measurable_const.sub measurable_id)).exp)).mul
      (clockWeight_continuous q k).measurable)
  have he : (∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (q*Real.exp (-q*(T-u))) *
      ∑' k, ENNReal.ofReal (clockWeight q u k)*a (k+1)) =
      ∑' k, ENNReal.ofReal (clockWeight q T (k+1))*a (k+1) := by
    simp_rw [← ENNReal.tsum_mul_left, ← mul_assoc,
      ← ENNReal.ofReal_mul (mul_nonneg hq (Real.exp_pos _).le)]
    rw [lintegral_tsum (fun k => ((hm k).mul measurable_const).aemeasurable)]
    apply tsum_congr
    intro k
    rw [lintegral_mul_const _ (hm k), clockWeight_renewal_lintegral q T hq hT k]
  rw [he, tsum_eq_zero_add' ENNReal.summable]
  simp only [clockWeight, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]

end
end RandomViability
