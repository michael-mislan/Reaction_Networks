import proofs.ThermoCoreCompatibility.GeneralCompatibility.ActiveSupport
import proofs.ThermoCoreCompatibility.GeneralCompatibility.CycleBranches
import proofs.ThermoCoreCompatibility.GeneralCompatibility.CycleJump
import proofs.ThermoCoreCompatibility.GeneralCompatibility.FiniteProgress
import proofs.ThermoCoreCompatibility.GeneralCompatibility.SourceImplications
import proofs.ThermoCoreCompatibility.GeneralCompatibility.CandidateTransport

/-!
Compiled terminal source bridge at the declared mixed formalization boundary.
The conventional local-CAD theorem constructs t and proves hstable. This file
does not claim to implement or formalize CAD or the graph path enumerator.
The imported finite-progress theorem proves termination of successful anchor
updates from their local semantics, rather than assuming termination.
-/

namespace ThermoCoreCompatibility.GeneralCompatibility

open MultiInterface

theorem source_decision_at_stable_threshold {V E : Type*} [Fintype E]
    (src dst : E → V) (w : E → Factors) (lo hi : V → ℝ)
    {t : ℝ} (ht : 0 < t)
    (hstable : ∀ σ : ℝ, 0 < σ → σ ≤ t →
      ((∃ z, BoxedMargin src dst w lo hi σ z) ↔
        ∃ z, BoxedMargin src dst w lo hi t z)) :
    (∃ z : V → ℝ, (∀ v, lo v ≤ z v ∧ z v ≤ hi v) ∧
      ∀ e, (w e).Productive (z (src e)) (z (dst e))) ↔
      ∃ z, BoxedMargin src dst w lo hi t z := by
  have h := strict_decision_of_stable_margin src dst w lo hi ht hstable
  constructor
  · rintro ⟨z, hz⟩
    exact h.mp ⟨z, (boxed_strict_iff_source src dst w lo hi z).mpr hz⟩
  · intro hm
    obtain ⟨z, hz⟩ := h.mpr hm
    exact ⟨z, (boxed_strict_iff_source src dst w lo hi z).mp hz⟩

theorem no_productive_source_of_no_threshold_state {V E : Type*} [Fintype E]
    (src dst : E → V) (w : E → Factors) (lo hi : V → ℝ)
    {t : ℝ} (ht : 0 < t)
    (hstable : ∀ σ : ℝ, 0 < σ → σ ≤ t →
      ((∃ z, BoxedMargin src dst w lo hi σ z) ↔
        ∃ z, BoxedMargin src dst w lo hi t z))
    (hnone : ¬ ∃ z, BoxedMargin src dst w lo hi t z) :
    ¬ ∃ z : V → ℝ, (∀ v, lo v ≤ z v ∧ z v ≤ hi v) ∧
      ∀ e, (w e).Productive (z (src e)) (z (dst e)) := by
  exact fun hz => hnone ((source_decision_at_stable_threshold
    src dst w lo hi ht hstable).mp hz)

end ThermoCoreCompatibility.GeneralCompatibility
