import proofs.ThermoCoreCompatibility.GeneralCompatibility.StrictDecision

namespace ThermoCoreCompatibility.GeneralCompatibility

open MultiInterface

/-- Local label tests transfer a global state. Candidate coverage remains an
explicit obligation, supplied conventionally by the path/cycle algorithm. -/
theorem feasible_of_candidate_transport {V E : Type*}
    (src dst : E → V) (w : E → Factors) (lo hi : V → ℝ)
    (I : V → Type*) (a b : ∀ v, I v → ℝ) (τ σ : ℝ)
    (hcover : ∀ z, BoxedMargin src dst w lo hi τ z →
      ∀ v, ∃ i, z v = a v i)
    (hbox : ∀ v i, (lo v ≤ a v i ∧ a v i ≤ hi v) →
      lo v ≤ b v i ∧ b v i ≤ hi v)
    (hedge : ∀ e i j,
      ((w e).lower (a (src e) i) + τ ≤ a (dst e) j ∧
        a (dst e) j + τ ≤ (w e).upper (a (src e) i)) →
      ((w e).lower (b (src e) i) + σ ≤ b (dst e) j ∧
        b (dst e) j + σ ≤ (w e).upper (b (src e) i))) :
    (∃ z, BoxedMargin src dst w lo hi τ z) →
      ∃ z, BoxedMargin src dst w lo hi σ z := by
  classical
  rintro ⟨z, hz⟩
  choose i hi' using hcover z hz
  refine ⟨fun v => b v (i v), ?_, ?_⟩
  · intro v
    apply hbox v (i v)
    rw [← hi' v]
    exact hz.1 v
  · intro e
    apply hedge e (i (src e)) (i (dst e))
    rw [← hi' (src e), ← hi' (dst e)]
    exact hz.2 e

theorem boxed_strict_iff_source {V E : Type*}
    (src dst : E → V) (w : E → Factors) (lo hi : V → ℝ) (z : V → ℝ) :
    BoxedStrict src dst w lo hi z ↔
      (∀ v, lo v ≤ z v ∧ z v ≤ hi v) ∧
        ∀ e, (w e).Productive (z (src e)) (z (dst e)) := by
  constructor
  · intro hz
    exact ⟨hz.1, fun e => ((w e).productive_iff _ _).mpr (hz.2 e)⟩
  · intro hz
    exact ⟨hz.1, fun e => ((w e).productive_iff _ _).mp (hz.2 e)⟩

end ThermoCoreCompatibility.GeneralCompatibility
