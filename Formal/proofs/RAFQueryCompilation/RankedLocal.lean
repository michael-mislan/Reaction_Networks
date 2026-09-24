import proofs.RAFQueryCompilation.RankedRegion
import proofs.RAFQueryCompilation.MaskCertificate

namespace RAFQueryCompilation
open RAF

/-- The existing local evaluator is sound for a selected-witness deletion region.
Its candidate is restricted to the old maximum, as justified by deletion monotonicity. -/
theorem checkMaskedLocal_ranked_deletion {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A D E : Finset (Fin m))
    (parents : Fin m → Finset (Fin m)) (rank : Fin m → ℕ)
    (table : Vector (Finset (Fin m)) m)
    (ht : ∀ p r, r ∈ table[p.val] ↔ p ∈ parents r)
    (hw : checkRankedSupport Q cats (evaluate Q (fun x r => x ∈ cats r) A) parents rank = true)
    (needs : Fin m → Finset (Fin n)) (hn : NeedsSound Q (fun x r => x ∈ cats r) needs)
    (oldMask : Fin m → Bool) (counts : Fin n → ℕ)
    (ho : ∀ r, oldMask r = true ↔ r ∈ evaluate Q (fun x r => x ∈ cats r) A)
    (hc : ∀ x, counts x = producerCount Q (evaluate Q (fun x r => x ∈ cats r) A) x)
    (cert : List (List (Fin m))) {L : Finset (Fin m)}
    (h : checkMaskedLocal Q (fun x r => x ∈ cats r) (fun p => table[p.val]) needs
      oldMask (fun r => oldMask r && decide (r ∉ D)) D E counts cert = some L) :
    evaluate Q (fun x r => x ∈ cats r) (A \ D) =
      (evaluate Q (fun x r => x ∈ cats r) A \ E) ∪ L := by
  let S := evaluate Q (fun x r => x ∈ cats r) A
  have hf : maskFood Q needs E oldMask counts = sparseFood Q needs S E counts := by
    simp only [maskFood, sparseFood, maskRegion_eq E S oldMask ho]
  have hm : maskRegion E (fun r => oldMask r && decide (r ∉ D)) = (S \ D) ∩ E := by
    ext r
    simp only [maskRegion, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
      ho, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  unfold checkMaskedLocal at h
  split at h
  next hr =>
    have hl := checkPruning_sound _ (fun x r => x ∈ cats r) cert _ h
    rw [hf, hm] at hl
    rw [sparse_food_exact Q (fun x r => x ∈ cats r) needs hn S E _ counts hc
      Finset.inter_subset_right] at hl
    rw [ranked_checked_deletion Q cats A D E parents rank table ht hw hr, hl]
  next => contradiction

end RAFQueryCompilation
