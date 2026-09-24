import proofs.TherapeuticWindows.AnchoredReserve
import proofs.TherapeuticWindows.WideBox

namespace TherapeuticWindows

/-- Source-specific finite algebra supporting the conventional publication theorem. -/
theorem publication_certificate :
    (∀ e : ℝ, 29/100 ≤ e → e ≤ 31/100 →
      ∀ i, meanAction e weight i ≤ -(99/1000)*weight i) ∧
    (∀ e : ℝ, 1/100 ≤ e → e ≤ 31/100 →
      ∀ i, relativeEnvelope e i ≤ (27/20)*weight i) ∧
    (0 < anchoredWitness ∧ anchoredWitness < 7/1000000) ∧
    (5000 < expLower (43/5) 30) ∧
    ((1 : ℚ)-107/12500-7/1000000 = 991433/1000000) := by
  exact ⟨tighter_contraction, relative_envelope_bound, anchored_witness_certificate,
    wide_exponential_certificate, by norm_num⟩

end TherapeuticWindows
