import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

namespace LowFounderPrediction
open MeasureTheory

/-- A pathwise transfer, allowing arbitrary dependence of deletion and errors. -/
theorem observed_budget {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (N D A : Ω → ℕ) (k : ℕ)
    (hD : ∀ ω, D ω ≤ N ω) :
    μ.real {ω | N ω ≤ k} ≤
      μ.real {ω | D ω + A ω ≤ k} + μ.real {ω | 0 < A ω} := by
  have hs : {ω | N ω ≤ k} ⊆
      {ω | D ω + A ω ≤ k} ∪ {ω | 0 < A ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at *
    have := hD ω
    omega
  exact (measureReal_mono hs).trans (measureReal_union_le _ _)

/-- Arithmetic assembly only: the source transfer premise remains explicit. -/
theorem robust_budget_arithmetic (reference latent observed : ℝ)
    (hbase : 467880212635/481696324816 ≤ reference)
    (hsource : reference - 7/1000 ≤ latent)
    (hobs : latent ≤ observed + 1/100) :
    57461421889141/60212040602000 ≤ observed := by
  linarith

theorem robust_margin :
    (19/20 : ℝ) < 57461421889141/60212040602000 := by norm_num

/-- Empty preparations contribute success one, not merely the single-founder bound. -/
theorem preparation_budget (e w m L γ : ℝ) (he : 0 ≤ e) (hL : 0 ≤ L)
    (hL1 : L ≤ 1) (hsum : e+w+m = 1) (hm : m ≤ γ) :
    (1-γ)*L ≤ e+w*L := by
  nlinarith [mul_nonneg he (sub_nonneg.mpr hL1),
    mul_nonneg (sub_nonneg.mpr hm) hL]

/-- Conditional training coverage must be established separately. -/
theorem conditional_coverage_accounting (q B δ coverage : ℝ)
    (hB : 0 ≤ B) (hq : 1-δ ≤ q) (hcov : q*B ≤ coverage) :
    (1-δ)*B ≤ coverage := by nlinarith

/-- A globally bounded false-object event is subtracted after training/preparation losses. -/
theorem unconditional_false_accounting (q L γ δ η latent observed : ℝ)
    (hbase : (1-δ)*(1-γ)*L ≤ q) (hsource : q ≤ latent)
    (hobs : latent ≤ observed+η) :
    (1-δ)*(1-γ)*L-η ≤ observed := by linarith

end LowFounderPrediction
