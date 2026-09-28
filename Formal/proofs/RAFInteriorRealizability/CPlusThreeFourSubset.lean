import proofs.RAFInteriorRealizability.CPlusThreeTransport

/-!
Transport the four-vertex graph obstruction to an arbitrary four-element
subset of a finite ground set.
-/

namespace RAFInteriorRealizability

universe u

variable {E : Type u} [Fintype E] [DecidableEq E]

theorem four_seed_graph_obstruction_card_four
    (hcard : Fintype.card E = 4) (P : E → Finset E)
    (hsmall : ∀ S : Finset E, S.Nonempty → S.card < 3 → ¬ PredSupported P S)
    (htriple : ∀ S : Finset E, S.card = 3 → PredSupported P S) : False := by
  let e : Fin 4 ≃ E := (Fintype.equivFinOfCardEq hcard).symm
  apply four_seed_graph_obstruction (pullbackPredecessors P e)
  · intro S hNe hS
    have hCard : (S.image e).card = S.card :=
      Finset.card_image_of_injective S e.injective
    intro hSupported
    exact (hsmall (S.image e) (hNe.image e) (by omega))
      ((predSupported_pullback_iff P e S).mp hSupported)
  · intro S hS
    have hCard : (S.image e).card = S.card :=
      Finset.card_image_of_injective S e.injective
    exact (predSupported_pullback_iff P e S).mpr
      (htriple (S.image e) (by omega))

omit [Fintype E] in
theorem four_seed_graph_obstruction_on_subset
    (P : E → Finset E) (Y : Finset E) (hY : Y.card = 4)
    (hsmall : ∀ S : Finset E, S ⊆ Y → S.Nonempty → S.card < 3 → ¬ PredSupported P S)
    (htriple : ∀ S : Finset E, S ⊆ Y → S.card = 3 → PredSupported P S) :
    False := by
  classical
  have hSubtype : Fintype.card {e // e ∈ Y} = 4 := by simpa using hY
  apply four_seed_graph_obstruction_card_four hSubtype (restrictPredecessors P Y)
  · intro S hNe hS
    have hCard : (S.image Subtype.val).card = S.card :=
      Finset.card_image_of_injective S Subtype.val_injective
    have hSubset : S.image Subtype.val ⊆ Y := by
      intro e he
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
      exact x.property
    intro hs
    exact (hsmall (S.image Subtype.val) hSubset (hNe.image Subtype.val) (by omega))
      ((predSupported_restrict_iff P Y S).mp hs)
  · intro S hS
    have hCard : (S.image Subtype.val).card = S.card :=
      Finset.card_image_of_injective S Subtype.val_injective
    have hSubset : S.image Subtype.val ⊆ Y := by
      intro e he
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
      exact x.property
    exact (predSupported_restrict_iff P Y S).mpr
      (htriple (S.image Subtype.val) hSubset (by omega))

end RAFInteriorRealizability
