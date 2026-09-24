import proofs.TherapeuticWindows.Source
import proofs.TherapeuticWindows.Reserve
import proofs.TherapeuticWindows.Clock
import proofs.TherapeuticWindows.Delivery
import proofs.TherapeuticWindows.Robustness

namespace TherapeuticWindows

/-- Finite source-instantiated algebra only. The stochastic theorem is proved in THEORY.md. -/
theorem finite_therapeutic_window_certificate :
    (∀ (e : ℝ), 29/100 ≤ e → e ≤ 31/100 →
      ∀ i, meanAction e weight i ≤ -(9/100)*weight i) ∧
    (clockValue 2 + 20*(1/1000 : ℚ)*120/4 < 49/50) ∧
    (0 < reserveBound ∧ reserveBound < 1/2000) ∧
    ((107/20000 : ℚ) < 1/100) ∧
    (∀ (e : ℝ), 1/100 ≤ e → e ≤ 31/100 →
      ∀ i, perturbationEnvelope e i ≤ weight i/1000) ∧
    (8000 < expLower 9 25 ∧ 50 < expLower (99/25) 15) := by
  exact ⟨source_contraction, exclusion_certificate, reserve_certificate, by norm_num,
    perturbation_budget, exponential_lower_certificates⟩

end TherapeuticWindows
