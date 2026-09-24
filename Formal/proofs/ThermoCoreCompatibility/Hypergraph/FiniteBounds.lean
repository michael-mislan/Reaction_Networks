import proofs.ThermoCoreCompatibility.Hypergraph.PrivateTriangleBounds

namespace ThermoCoreCompatibility.Hypergraph

/-- Exact finite strict lower/upper elimination in a closed box, including a
singleton box. Nonempty index sets avoid artificial extrema for empty families. -/
theorem finite_bounds_box_iff {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (hs : s.Nonempty) (ht : t.Nonempty) (L : ι → ℝ) (U : κ → ℝ)
    {l u : ℝ} (hlu : l ≤ u) :
    (∃ b, l ≤ b ∧ b ≤ u ∧ (∀ i ∈ s, L i < b) ∧ (∀ k ∈ t, b < U k)) ↔
      (∀ i ∈ s, ∀ k ∈ t, L i < U k) ∧
        (∀ k ∈ t, l < U k) ∧ (∀ i ∈ s, L i < u) := by
  constructor
  · rintro ⟨b, hl, hu, hL, hU⟩
    exact ⟨fun i hi k hk => lt_trans (hL i hi) (hU k hk),
      fun k hk => lt_of_le_of_lt hl (hU k hk),
      fun i hi => lt_of_lt_of_le (hL i hi) hu⟩
  · rintro ⟨hcross, hl, hu⟩
    let lo := s.sup' hs L
    let up := t.inf' ht U
    have hlo : lo < up := by
      dsimp [lo, up]
      rw [Finset.sup'_lt_iff]
      intro i hi
      rw [Finset.lt_inf'_iff]
      exact hcross i hi
    have hlup : l < up := by
      dsimp [up]
      exact (Finset.lt_inf'_iff ht).mpr hl
    have hlou : lo < u := by
      dsimp [lo]
      exact (Finset.sup'_lt_iff hs).mpr hu
    obtain ⟨b, hb₁, hb₂, hb₃, _, hb₅⟩ :=
      (private_interval_box_iff hlu).2 ⟨hlo, hlo, hlup, hlou, hlou⟩
    refine ⟨b, hb₁, hb₂, ?_, ?_⟩
    · exact (Finset.sup'_lt_iff hs).mp hb₃
    · exact (Finset.lt_inf'_iff ht).mp hb₅

end ThermoCoreCompatibility.Hypergraph
