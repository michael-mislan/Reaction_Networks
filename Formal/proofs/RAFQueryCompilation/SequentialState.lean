import proofs.RAFQueryCompilation.VectorModify

namespace RAFQueryCompilation
open RAF

theorem local_removed {R : Type*} [DecidableEq R] (S E L : Finset R) (hl : L ⊆ E) :
    S \ ((S \ E) ∪ L) = (S ∩ E) \ L := by
  ext r
  have h := @hl r
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  tauto

theorem local_added {R : Type*} [DecidableEq R] (S E L : Finset R) (hl : L ⊆ E) :
    ((S \ E) ∪ L) \ S = L \ (S ∩ E) := by
  ext r
  have h := @hl r
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  tauto

theorem patchAnswerMask_correct {m : ℕ} (mask : Vector Bool m)
    (S E L : Finset (Fin m)) (hm : ∀ r, mask[r.val] = true ↔ r ∈ S)
    (hl : L ⊆ E) (r : Fin m) :
    (patchVector mask E (fun i => decide (i ∈ L)))[r.val] = true ↔
      r ∈ (S \ E) ∪ L := by
  rw [patchVector_get]
  by_cases he : r ∈ E
  · simp only [he, if_true, decide_eq_true_eq, Finset.mem_union, Finset.mem_sdiff,
      not_true_eq_false, and_false, false_or]
  · have hn : r ∉ L := fun h => he (hl h)
    simp only [he, if_false, hm r, Finset.mem_union, Finset.mem_sdiff, not_false_eq_true,
      and_true, hn, or_false]

theorem producerCount_zero_of_not_output {M R : Type*} [DecidableEq M]
    (Q : CRS M R) (S : Finset R) (x : M) (hx : x ∉ S.biUnion Q.outputs) :
    producerCount Q S x = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  obtain ⟨hr, ho⟩ := Finset.mem_filter.mp hr
  exact hx (Finset.mem_biUnion.mpr ⟨r, hr, ho⟩)

def patchCounts {n m : ℕ} (Q : CRS (Fin n) (Fin m)) (counts : Vector ℕ n)
    (removed added : Finset (Fin m)) : Vector ℕ n :=
  modifyVector counts ((removed ∪ added).biUnion Q.outputs)
    (fun x value => value - producerCount Q removed x + producerCount Q added x)

theorem patchCounts_get {n m : ℕ} (Q : CRS (Fin n) (Fin m)) (counts : Vector ℕ n)
    (removed added : Finset (Fin m)) (x : Fin n) :
    (patchCounts Q counts removed added)[x.val] =
      counts[x.val] - producerCount Q removed x + producerCount Q added x := by
  rw [patchCounts, modifyVector_get]
  by_cases hx : x ∈ (removed ∪ added).biUnion Q.outputs
  · simp only [hx, if_true]
  · have hr : x ∉ removed.biUnion Q.outputs := by
      intro h
      obtain ⟨r, hr, ho⟩ := Finset.mem_biUnion.mp h
      exact hx (Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_left _ hr, ho⟩)
    have ha : x ∉ added.biUnion Q.outputs := by
      intro h
      obtain ⟨r, hr, ho⟩ := Finset.mem_biUnion.mp h
      exact hx (Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_right _ hr, ho⟩)
    simp only [hx, if_false, producerCount_zero_of_not_output Q removed x hr,
      producerCount_zero_of_not_output Q added x ha, Nat.sub_zero, Nat.add_zero]

theorem patchCounts_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m)) (counts : Vector ℕ n)
    (S E L : Finset (Fin m)) (hl : L ⊆ E)
    (hc : ∀ x, counts[x.val] = producerCount Q S x) (x : Fin n) :
    (patchCounts Q counts ((S ∩ E) \ L) (L \ (S ∩ E)))[x.val] =
      producerCount Q ((S \ E) ∪ L) x := by
  rw [patchCounts_get, hc x, ← local_removed S E L hl, ← local_added S E L hl]
  exact (producer_count_delta Q S ((S \ E) ∪ L) x).symm

end RAFQueryCompilation
