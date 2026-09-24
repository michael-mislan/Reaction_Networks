import proofs.ThermoCoreCompatibility.GeneralCompatibility.ClosedMargin

namespace ThermoCoreCompatibility.GeneralCompatibility

open MultiInterface

theorem finite_positive_uniform {I : Type*} [Fintype I] (f : I → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ f i := by
  classical
  have aux (s : Finset I) : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ f i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert a s _ ih =>
      obtain ⟨δ, hδ, hs⟩ := ih
      refine ⟨min δ (f a), lt_min hδ (hf a), ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_right _ _
      · exact le_trans (min_le_left _ _) (hs i hi)
  obtain ⟨δ, hδ, hs⟩ := aux Finset.univ
  exact ⟨δ, hδ, fun i => hs i (Finset.mem_univ i)⟩

def BoxedStrict {V E : Type*} (src dst : E → V) (w : E → Factors)
    (lo hi : V → ℝ) (z : V → ℝ) : Prop :=
  (∀ v, lo v ≤ z v ∧ z v ≤ hi v) ∧
    ∀ e, (w e).lower (z (src e)) < z (dst e) ∧
      z (dst e) < (w e).upper (z (src e))

theorem strict_iff_positive_margin {V E : Type*} [Fintype E]
    (src dst : E → V) (w : E → Factors) (lo hi : V → ℝ) (z : V → ℝ) :
    BoxedStrict src dst w lo hi z ↔
      ∃ τ : ℝ, 0 < τ ∧ BoxedMargin src dst w lo hi τ z := by
  constructor
  · intro hz
    obtain ⟨τ, hτ, hgap⟩ := finite_positive_uniform
      (fun e => min (z (dst e) - (w e).lower (z (src e)))
        ((w e).upper (z (src e)) - z (dst e)))
      (fun e => lt_min (sub_pos.mpr (hz.2 e).1) (sub_pos.mpr (hz.2 e).2))
    refine ⟨τ, hτ, hz.1, ?_⟩
    intro e
    have h₁ := le_trans (hgap e) (min_le_left _ _)
    have h₂ := le_trans (hgap e) (min_le_right _ _)
    constructor <;> linarith
  · rintro ⟨τ, hτ, hz⟩
    refine ⟨hz.1, ?_⟩
    intro e
    have h₁ := (hz.2 e).1
    have h₂ := (hz.2 e).2
    constructor <;> linarith

theorem margin_downward {V E : Type*} (src dst : E → V) (w : E → Factors)
    (lo hi : V → ℝ) {σ τ : ℝ} (hστ : σ ≤ τ) {z : V → ℝ}
    (hz : BoxedMargin src dst w lo hi τ z) : BoxedMargin src dst w lo hi σ z := by
  refine ⟨hz.1, ?_⟩
  intro e
  have h₁ := (hz.2 e).1
  have h₂ := (hz.2 e).2
  constructor <;> linarith

/-- The stability hypothesis is explicit: this lemma does not compute a threshold. -/
theorem strict_decision_of_stable_margin {V E : Type*} [Fintype E]
    (src dst : E → V) (w : E → Factors) (lo hi : V → ℝ)
    {t : ℝ} (ht : 0 < t)
    (hstable : ∀ σ : ℝ, 0 < σ → σ ≤ t →
      ((∃ z, BoxedMargin src dst w lo hi σ z) ↔
        ∃ z, BoxedMargin src dst w lo hi t z)) :
    (∃ z, BoxedStrict src dst w lo hi z) ↔
      ∃ z, BoxedMargin src dst w lo hi t z := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨τ, hτ, hm⟩ := (strict_iff_positive_margin src dst w lo hi z).mp hz
    apply (hstable (min τ t) (lt_min hτ ht) (min_le_right _ _)).mp
    exact ⟨z, margin_downward src dst w lo hi (min_le_left _ _) hm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, (strict_iff_positive_margin src dst w lo hi z).mpr ⟨t, ht, hz⟩⟩

end ThermoCoreCompatibility.GeneralCompatibility
