import proofs.IrrRAFEnumeration.CompletionCNF

namespace IrrRAFEnumeration

variable {α : Type*} [DecidableEq α]

/-- Every raw completion-CNF residual remains cross-intersecting.  If `S` is
the set of variables fixed true and `Z` the set fixed false, a surviving input
edge avoids `S` and loses `Z`, while a surviving known transversal avoids `Z`
and loses `S`.  Their original intersection therefore survives both
restrictions. -/
theorem residual_cross_intersects
    {H G : Finset (Finset α)}
    (hGhits : ∀ T ∈ G, Hits H T)
    {S Z E T : Finset α}
    (hE : E ∈ H) (hES : Disjoint E S)
    (hT : T ∈ G) (hTZ : Disjoint T Z) :
    ¬ Disjoint (E \ Z) (T \ S) := by
  have hTE : ¬ Disjoint T E := hGhits T hT E hE
  obtain ⟨x, hxT, hxE⟩ := Finset.not_disjoint_iff.mp hTE
  apply Finset.not_disjoint_iff.mpr
  refine ⟨x, ?_, ?_⟩
  · exact Finset.mem_sdiff.mpr ⟨hxE, fun hxZ =>
      (Finset.disjoint_left.mp hTZ) hxT hxZ⟩
  · exact Finset.mem_sdiff.mpr ⟨hxT, fun hxS =>
      (Finset.disjoint_left.mp hES) hxE hxS⟩

/-- In particular, any supplied subfamily of the blocker satisfies the
hypothesis needed by `residual_cross_intersects`. -/
theorem blocker_subfamily_residual_cross_intersects
    [Fintype α]
    {H G : Finset (Finset α)} (hGH : G ⊆ blocker H)
    {S Z E T : Finset α}
    (hE : E ∈ H) (hES : Disjoint E S)
    (hT : T ∈ G) (hTZ : Disjoint T Z) :
    ¬ Disjoint (E \ Z) (T \ S) := by
  apply residual_cross_intersects (H := H) (G := G) ?_ hE hES hT hTZ
  intro U hUG
  exact (mem_blocker.mp (hGH hUG)).1

end IrrRAFEnumeration
