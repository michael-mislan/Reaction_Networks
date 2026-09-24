import proofs.RAFQueryCompilation.RankedWitness
import proofs.RAFQueryCompilation.IncidenceIndex

namespace RAFQueryCompilation
open RAF

/-- The table contains selected witness dependents, rather than all possible source dependents. -/
theorem witness_region_closed {m : ℕ} (S D E : Finset (Fin m))
    (parents : Fin m → Finset (Fin m)) (table : Vector (Finset (Fin m)) m)
    (ht : ∀ p r, r ∈ table[p.val] ↔ p ∈ parents r)
    (h : checkRegion (fun p => table[p.val]) D E = true) :
    D ⊆ E ∧ ∀ r ∈ S \ E, parents r ∩ S ⊆ S \ E := by
  have hc := h
  simp only [checkRegion, decide_eq_true_eq] at hc
  refine ⟨hc.1, ?_⟩
  intro r hr p hp
  obtain ⟨hparent, hpS⟩ := Finset.mem_inter.mp hp
  refine Finset.mem_sdiff.mpr ⟨hpS, ?_⟩
  intro hpE
  exact (Finset.mem_sdiff.mp hr).2 (hc.2 p hpE ((ht p r).mpr hparent))

/-- A once-checked source witness and a local region check justify exact deletion evaluation.
The witness-table interface is implemented by `sourceConsumers_mem`. -/
theorem ranked_checked_deletion {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A D E : Finset (Fin m))
    (parents : Fin m → Finset (Fin m)) (rank : Fin m → ℕ)
    (table : Vector (Finset (Fin m)) m)
    (ht : ∀ p r, r ∈ table[p.val] ↔ p ∈ parents r)
    (hw : checkRankedSupport Q cats (evaluate Q (fun x r => x ∈ cats r) A) parents rank = true)
    (hr : checkRegion (fun p => table[p.val]) D E = true) :
    evaluate Q (fun x r => x ∈ cats r) (A \ D) =
      (evaluate Q (fun x r => x ∈ cats r) A \ E) ∪
      evaluate (residualSource Q (evaluate Q (fun x r => x ∈ cats r) A \ E))
        (fun x r => x ∈ cats r) ((evaluate Q (fun x r => x ∈ cats r) A \ D) ∩ E) := by
  have hc := witness_region_closed (evaluate Q (fun x r => x ∈ cats r) A) D E parents table ht hr
  exact ranked_deletion_localization Q cats A D E parents rank
    (checkRankedSupport_sound Q cats _ parents rank hw) hc.1 hc.2

end RAFQueryCompilation
