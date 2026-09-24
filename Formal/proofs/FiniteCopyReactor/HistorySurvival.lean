import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {H : Type*} [MeasurableSpace H]

/-- Restriction records success mass only; it is not a renormalized or rejection-sampled law. -/
def successfulHistoryKernel (K : Kernel H H) (S : Set H) (hS : MeasurableSet S) : ℕ → Kernel H H
  | 0 => Kernel.id
  | n+1 => successfulHistoryKernel K S hS n ∘ₖ K.restrict hS

/-- Histories may contain continuous observations. Only their conditional transition law is used. -/
theorem history_survival_product (K : Kernel H H) (D S : Set H) (hS : MeasurableSet S)
    (hSD : S ⊆ D) (c : ℝ≥0∞) (hc : ∀ h ∈ D,c ≤ K h S) (n : ℕ) (h : H) (hh : h ∈ D) :
    c^n ≤ successfulHistoryKernel K S hS n h Set.univ := by
  induction n generalizing h with
  | zero => simp [successfulHistoryKernel,Kernel.id_apply]
  | succ n ih =>
    rw [successfulHistoryKernel,Kernel.comp_apply' _ _ _ MeasurableSet.univ,Kernel.restrict_apply]
    calc
      c^(n+1)=c^n*c := pow_succ c n
      _ ≤ c^n*K h S := mul_le_mul_right (hc h hh) _
      _ = ∫⁻ _ in S,c^n ∂K h := by simp only [lintegral_const,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
      _ ≤ ∫⁻ y in S,successfulHistoryKernel K S hS n y Set.univ ∂K h := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hS] with y hy
        exact ih y (hSD hy)

theorem history_survival_linear (K : Kernel H H) (D S : Set H) (hS : MeasurableSet S)
    (hSD : S ⊆ D) (e : ℝ) (he' : e ≤ 1)
    (hc : ∀ h ∈ D,ENNReal.ofReal (1-e) ≤ K h S) (n : ℕ) (h : H) (hh : h ∈ D) :
    ENNReal.ofReal (1-(n:ℝ)*e) ≤ successfulHistoryKernel K S hS n h Set.univ := by
  have hb : 1-(n:ℝ)*e ≤ (1-e)^n := by
    have hp := one_add_mul_le_pow (a := -e) (by linarith : (-2:ℝ) ≤ -e) n
    simpa only [mul_neg,sub_eq_add_neg] using hp
  have hp := ENNReal.ofReal_le_ofReal hb
  rw [ENNReal.ofReal_pow (by linarith : 0 ≤ 1-e)] at hp
  exact hp.trans (history_survival_product K D S hS hSD _ hc n h hh)

end
end FiniteCopyReactor
