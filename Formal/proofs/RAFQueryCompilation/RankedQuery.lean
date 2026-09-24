import proofs.RAFQueryCompilation.RankedLocal
import proofs.RAFQueryCompilation.PointQuery

namespace RAFQueryCompilation
open RAF

def rankedPointQuery {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (table : Vector (Finset (Fin m)) m)
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m) (D E : Finset (Fin m))
    (cert : List (List (Fin m))) (probes : List (Fin m)) : Option (List Bool) :=
  (checkMaskedLocal Q (fun x r => x ∈ cats r) (fun p => table[p.val]) needs
    (fun r => state.answer[r.val]) (fun r => state.answer[r.val] && decide (r ∉ D))
    D E (fun x => state.counts[x.val]) cert).map fun L =>
      probes.map (fun r => if r ∈ E then decide (r ∈ L) else state.answer[r.val])

theorem rankedPointQuery_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A D E : Finset (Fin m))
    (parents : Fin m → Finset (Fin m)) (rank : Fin m → ℕ)
    (table : Vector (Finset (Fin m)) m)
    (ht : ∀ p r, r ∈ table[p.val] ↔ p ∈ parents r)
    (hw : checkRankedSupport Q cats (evaluate Q (fun x r => x ∈ cats r) A) parents rank = true)
    (needs : Fin m → Finset (Fin n)) (hn : NeedsSound Q (fun x r => x ∈ cats r) needs)
    (state : QueryState n m)
    (ho : ∀ r, state.answer[r.val] = true ↔ r ∈ evaluate Q (fun x r => x ∈ cats r) A)
    (hc : ∀ x, state.counts[x.val] = producerCount Q (evaluate Q (fun x r => x ∈ cats r) A) x)
    (cert : List (List (Fin m))) (probes : List (Fin m)) {values : List Bool}
    (h : rankedPointQuery Q cats table needs state D E cert probes = some values) :
    values = probes.map (fun r => decide (r ∈ evaluate Q (fun x r => x ∈ cats r) (A \ D))) := by
  unfold rankedPointQuery at h
  cases hs : checkMaskedLocal Q (fun x r => x ∈ cats r) (fun p => table[p.val]) needs
    (fun r => state.answer[r.val]) (fun r => state.answer[r.val] && decide (r ∉ D))
    D E (fun x => state.counts[x.val]) cert with
  | none => simp only [hs, Option.map_none, reduceCtorEq] at h
  | some L =>
    simp only [hs, Option.map_some, Option.some.injEq] at h
    rw [← h]
    have he := checkMaskedLocal_ranked_deletion Q cats A D E parents rank table ht hw
      needs hn (fun r => state.answer[r.val]) (fun x => state.counts[x.val]) ho hc cert hs
    have hL := checkMaskedLocal_subset Q (fun x r => x ∈ cats r) (fun p => table[p.val])
      needs (fun r => state.answer[r.val]) (fun r => state.answer[r.val] && decide (r ∉ D))
      D E (fun x => state.counts[x.val]) cert hs
    apply List.map_congr_left
    intro r _
    apply Bool.eq_iff_iff.mpr
    by_cases hr : r ∈ E
    · simp [hr, he]
    · have hnL : r ∉ L := fun hh => hr (hL hh)
      simp [hr, he, hnL, ho]

def rankedPointTotal {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (table : Vector (Finset (Fin m)) m)
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m) (D E : Finset (Fin m))
    (cert : List (List (Fin m))) (probes : List (Fin m)) : List Bool × Bool :=
  match rankedPointQuery Q cats table needs state D E cert probes with
  | some values => (values, true)
  | none => ((freshPointQuery Q cats state.available D ∅ probes).members, false)

theorem rankedPointTotal_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A D E : Finset (Fin m))
    (parents : Fin m → Finset (Fin m)) (rank : Fin m → ℕ)
    (table : Vector (Finset (Fin m)) m)
    (ht : ∀ p r, r ∈ table[p.val] ↔ p ∈ parents r)
    (hw : checkRankedSupport Q cats (evaluate Q (fun x r => x ∈ cats r) A) parents rank = true)
    (needs : Fin m → Finset (Fin n)) (hn : NeedsSound Q (fun x r => x ∈ cats r) needs)
    (state : QueryState n m)
    (ho : ∀ r, state.answer[r.val] = true ↔ r ∈ evaluate Q (fun x r => x ∈ cats r) A)
    (ha : ∀ r, state.available[r.val] = true ↔ r ∈ A)
    (hc : ∀ x, state.counts[x.val] = producerCount Q (evaluate Q (fun x r => x ∈ cats r) A) x)
    (cert : List (List (Fin m))) (probes : List (Fin m)) :
    (rankedPointTotal Q cats table needs state D E cert probes).1 =
      probes.map (fun r => decide (r ∈ evaluate Q (fun x r => x ∈ cats r) (A \ D))) := by
  cases hs : rankedPointQuery Q cats table needs state D E cert probes with
  | some values =>
    simp only [rankedPointTotal, hs]
    exact rankedPointQuery_correct Q cats A D E parents rank table ht hw needs hn state ho hc cert probes hs
  | none =>
    simp only [rankedPointTotal, hs]
    simpa only [Finset.union_empty] using (freshPointQuery_correct Q cats state.available A D ∅ probes ha).1

end RAFQueryCompilation
