import proofs.RAFQueryCompilation.SequentialState

namespace RAFQueryCompilation
open RAF

theorem patchAvailability_correct {m : ℕ} (mask : Vector Bool m)
    (A removed added : Finset (Fin m)) (hm : ∀ r, mask[r.val] = true ↔ r ∈ A)
    (r : Fin m) :
    (patchVector mask (removed ∪ added) (fun i => decide (i ∈ added)))[r.val] = true ↔
      r ∈ (A \ removed) ∪ added := by
  rw [patchAnswerMask_correct mask A _ added hm Finset.subset_union_right]
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

theorem checkMaskedLocal_subset {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (C : Catalysis (Fin n) (Fin m)) [∀ x r, Decidable (C x r)]
    (succ : Fin m → Finset (Fin m)) (needs : Fin m → Finset (Fin n))
    (oldMask availableMask : Fin m → Bool) (D E : Finset (Fin m))
    (counts : Fin n → ℕ) (cert : List (List (Fin m))) {L : Finset (Fin m)}
    (h : checkMaskedLocal Q C succ needs oldMask availableMask D E counts cert = some L) :
    L ⊆ E := by
  unfold checkMaskedLocal at h
  split at h
  next =>
    rw [checkPruning_sound _ C cert _ h]
    exact (evaluate_subset _ C _).trans (Finset.filter_subset _ _)
  next => contradiction

/-- Accepted checker output preserves both next-answer membership and producer counts. -/
theorem accepted_state_transition {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (C : Catalysis (Fin n) (Fin m)) [∀ x r, Decidable (C x r)]
    (succ : Fin m → Finset (Fin m)) (needs : Fin m → Finset (Fin n))
    (hi : IndexSound Q C succ) (hn : NeedsSound Q C needs)
    (A removed added E : Finset (Fin m)) (counts : Vector ℕ n)
    (cert : List (List (Fin m))) (oldMask baseMask : Vector Bool m)
    (ho : ∀ r, oldMask[r.val] = true ↔ r ∈ evaluate Q C A)
    (ha : ∀ r, baseMask[r.val] = true ↔ r ∈ A)
    (hc : ∀ x, counts[x.val] = producerCount Q (evaluate Q C A) x)
    {L : Finset (Fin m)}
    (h : checkMaskedLocal Q C succ needs (fun r => oldMask[r.val])
      (editedMask (fun r => baseMask[r.val]) removed added) (removed ∪ added) E
      (fun x => counts[x.val]) cert = some L) :
    (∀ r, (patchVector oldMask E (fun i => decide (i ∈ L)))[r.val] = true ↔
      r ∈ evaluate Q C ((A \ removed) ∪ added)) ∧
    (∀ x, (patchCounts Q counts ((maskRegion E (fun r => oldMask[r.val])) \ L)
      (L \ maskRegion E (fun r => oldMask[r.val])))[x.val] =
      producerCount Q (evaluate Q C ((A \ removed) ∪ added)) x) := by
  have hl := checkMaskedLocal_subset Q C succ needs _ _ _ E _ cert h
  have he := checkReferenceEdit_sound Q C succ needs hi hn A removed added E
    (fun x => counts[x.val]) cert _ _ ho ha hc h
  constructor
  · intro r
    rw [he]
    exact patchAnswerMask_correct oldMask _ E L ho hl r
  · intro x
    rw [maskRegion_eq E _ _ ho, restrictToRegion_eq, he]
    exact patchCounts_correct Q counts _ E L hl hc x

end RAFQueryCompilation
