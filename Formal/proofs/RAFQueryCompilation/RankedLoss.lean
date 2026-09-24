import proofs.RAFQueryCompilation.RankedQuery

namespace RAFQueryCompilation
open RAF

def rankedLossQuery {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (table : Vector (Finset (Fin m)) m)
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m) (D E : Finset (Fin m))
    (cert : List (List (Fin m))) : Option (Finset (Fin m)) :=
  (checkMaskedLocal Q (fun x r => x ∈ cats r) (fun p => table[p.val]) needs
    (fun r => state.answer[r.val]) (fun r => state.answer[r.val] && decide (r ∉ D))
    D E (fun x => state.counts[x.val]) cert).map fun L =>
      maskRegion E (fun r => state.answer[r.val]) \ L

theorem rankedLossQuery_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A D E : Finset (Fin m))
    (parents : Fin m → Finset (Fin m)) (rank : Fin m → ℕ)
    (table : Vector (Finset (Fin m)) m) (ht : ∀ p r, r ∈ table[p.val] ↔ p ∈ parents r)
    (hw : checkRankedSupport Q cats (evaluate Q (fun x r => x ∈ cats r) A) parents rank = true)
    (needs : Fin m → Finset (Fin n)) (hn : NeedsSound Q (fun x r => x ∈ cats r) needs)
    (state : QueryState n m)
    (ho : ∀ r, state.answer[r.val] = true ↔ r ∈ evaluate Q (fun x r => x ∈ cats r) A)
    (hc : ∀ x, state.counts[x.val] = producerCount Q (evaluate Q (fun x r => x ∈ cats r) A) x)
    (cert : List (List (Fin m))) {lost : Finset (Fin m)}
    (h : rankedLossQuery Q cats table needs state D E cert = some lost) :
    lost = evaluate Q (fun x r => x ∈ cats r) A \ evaluate Q (fun x r => x ∈ cats r) (A \ D) := by
  unfold rankedLossQuery at h
  cases hs : checkMaskedLocal Q (fun x r => x ∈ cats r) (fun p => table[p.val]) needs
    (fun r => state.answer[r.val]) (fun r => state.answer[r.val] && decide (r ∉ D))
    D E (fun x => state.counts[x.val]) cert with
  | none => simp only [hs, Option.map_none, reduceCtorEq] at h
  | some L =>
    simp only [hs, Option.map_some, Option.some.injEq] at h
    rw [← h, maskRegion_eq E _ _ ho, restrictToRegion_eq]
    have he := checkMaskedLocal_ranked_deletion Q cats A D E parents rank table ht hw
      needs hn (fun r => state.answer[r.val]) (fun x => state.counts[x.val]) ho hc cert hs
    have hL := checkMaskedLocal_subset Q (fun x r => x ∈ cats r) (fun p => table[p.val])
      needs (fun r => state.answer[r.val]) (fun r => state.answer[r.val] && decide (r ∉ D))
      D E (fun x => state.counts[x.val]) cert hs
    rw [he, local_removed _ E L hL]

def rankedLossTotal {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (table : Vector (Finset (Fin m)) m)
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m) (D E : Finset (Fin m))
    (cert : List (List (Fin m))) : Finset (Fin m) × Bool :=
  match rankedLossQuery Q cats table needs state D E cert with
  | some lost => (lost, true)
  | none => (maskSet state.answer \ (freshEvaluate Q cats (freshAvailable state D ∅)).1, false)

theorem rankedLossTotal_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A D E : Finset (Fin m))
    (parents : Fin m → Finset (Fin m)) (rank : Fin m → ℕ)
    (table : Vector (Finset (Fin m)) m) (ht : ∀ p r, r ∈ table[p.val] ↔ p ∈ parents r)
    (hw : checkRankedSupport Q cats (evaluate Q (fun x r => x ∈ cats r) A) parents rank = true)
    (needs : Fin m → Finset (Fin n)) (hn : NeedsSound Q (fun x r => x ∈ cats r) needs)
    (state : QueryState n m)
    (ho : ∀ r, state.answer[r.val] = true ↔ r ∈ evaluate Q (fun x r => x ∈ cats r) A)
    (ha : ∀ r, state.available[r.val] = true ↔ r ∈ A)
    (hc : ∀ x, state.counts[x.val] = producerCount Q (evaluate Q (fun x r => x ∈ cats r) A) x)
    (cert : List (List (Fin m))) :
    (rankedLossTotal Q cats table needs state D E cert).1 =
      evaluate Q (fun x r => x ∈ cats r) A \ evaluate Q (fun x r => x ∈ cats r) (A \ D) := by
  cases hs : rankedLossQuery Q cats table needs state D E cert with
  | some lost =>
    simp only [rankedLossTotal, hs]
    exact rankedLossQuery_correct Q cats A D E parents rank table ht hw needs hn state ho hc cert hs
  | none =>
    have hm : maskSet state.answer = evaluate Q (fun x r => x ∈ cats r) A := by
      ext r
      simp only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and, ho]
    simp only [rankedLossTotal, hs, hm, freshEvaluate_refines,
      freshAvailable_correct state A D ∅ ha, Finset.union_empty]

end RAFQueryCompilation
