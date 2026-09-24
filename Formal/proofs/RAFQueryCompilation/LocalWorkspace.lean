import proofs.RAFQueryCompilation.MaskCertificate

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- All molecular values a local replay can need or produce, before its answer
is known. Counts and old masks can change membership but cannot enlarge this set. -/
def sourceEnvelope (Q : CRS M R) (needs : R → Finset M) (E : Finset R) : Finset M :=
  (Q.food ∪ E.biUnion needs) ∪ E.biUnion Q.outputs

theorem replaySchedule_subset_envelope (Q : CRS M R) (S E : Finset R)
    (hS : S ⊆ E) (order : List R) :
    replaySchedule Q S order ⊆ Q.food ∪ E.biUnion Q.outputs := by
  have aux : ∀ (l : List R) (pool : Finset M),
      pool ⊆ Q.food ∪ E.biUnion Q.outputs →
      l.foldl (scheduleStep Q S) pool ⊆ Q.food ∪ E.biUnion Q.outputs := by
    intro l
    induction l with
    | nil => intro pool hp; exact hp
    | cons r rs ih =>
      intro pool hp
      apply ih
      unfold scheduleStep
      split
      next h =>
        apply Finset.union_subset hp
        intro x hx
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,hS h.1,hx⟩)
      next => exact hp
  exact aux order Q.food Finset.subset_union_left

theorem local_replay_workspace (Q : CRS M R) (needs : R → Finset M)
    (E S : Finset R) (hS : S ⊆ E) (oldMask : R → Bool) (counts : M → ℕ)
    (order : List R) :
    replaySchedule (withFood Q (maskFood Q needs E oldMask counts)) S order ⊆
      sourceEnvelope Q needs E := by
  apply (replaySchedule_subset_envelope _ S E hS order).trans
  apply Finset.union_subset
  · apply Finset.Subset.trans _ Finset.subset_union_left
    exact Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.filter_subset _ _)
  · exact Finset.subset_union_right

omit [DecidableEq R] in
theorem sourceEnvelope_card_le (Q : CRS M R) (needs : R → Finset M)
    (E : Finset R) :
    (sourceEnvelope Q needs E).card ≤
      Q.food.card + (E.biUnion needs).card + (E.biUnion Q.outputs).card := by
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _)

theorem local_replay_card_le (Q : CRS M R) (needs : R → Finset M)
    (E S : Finset R) (hS : S ⊆ E) (oldMask : R → Bool) (counts : M → ℕ)
    (order : List R) :
    (replaySchedule (withFood Q (maskFood Q needs E oldMask counts)) S order).card ≤
      Q.food.card + (E.biUnion needs).card + (E.biUnion Q.outputs).card :=
  (Finset.card_le_card (local_replay_workspace Q needs E S hS oldMask counts order)).trans
    (sourceEnvelope_card_le Q needs E)

end RAFQueryCompilation
