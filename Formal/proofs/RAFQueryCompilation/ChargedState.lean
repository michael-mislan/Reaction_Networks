import proofs.RAFQueryCompilation.PatchFootprint

namespace RAFQueryCompilation
open RAF

structure QueryState (n m : ℕ) where
  answer : Vector Bool m
  available : Vector Bool m
  counts : Vector ℕ n

/-- The same three assignments used by the sequential runtime, as a pure step. -/
def applyLocalState {n m : ℕ} (Q : CRS (Fin n) (Fin m)) (state : QueryState n m)
    (removed added E L : Finset (Fin m)) : QueryState n m :=
  let oldInside := maskRegion E (fun r => state.answer[r.val])
  { answer := patchVector state.answer E (fun r => decide (r ∈ L))
    available := patchVector state.available (removed ∪ added) (fun r => decide (r ∈ added))
    counts := patchCounts Q state.counts (oldInside \ L) (L \ oldInside) }

def stateCharge {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : CRS M R) (E D oldInside L : Finset R) : ℕ :=
  let touched := ((oldInside \ L) ∪ (L \ oldInside)).biUnion Q.outputs
  let outputs := ∑ r ∈ oldInside ∪ L, (Q.outputs r).card
  1 + (E.card+D.card+oldInside.card+L.card+1)^2 + (touched.card+1)^2 +
    (touched.card+1)*(oldInside.card+L.card+1)*(outputs+1)

def stateCap {M R : Type*} [DecidableEq M]
    (Q : CRS M R) (E : Finset R) : ℕ :=
  1 + (4*E.card+1)^2 + ((E.biUnion Q.outputs).card+1)^2 +
    ((E.biUnion Q.outputs).card+1)*(2*E.card+1)*((∑ r ∈ E, (Q.outputs r).card)+1)

theorem stateCharge_le {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : CRS M R) (E D oldInside L : Finset R)
    (hd : D ⊆ E) (hs : oldInside ⊆ E) (hl : L ⊆ E) :
    stateCharge Q E D oldInside L ≤ stateCap Q E := by
  have hD := Finset.card_le_card hd
  have hS := Finset.card_le_card hs
  have hL := Finset.card_le_card hl
  have ht := Finset.card_le_card (patch_products_subset Q E (oldInside \ L) (L \ oldInside)
    (Finset.sdiff_subset.trans hs) (Finset.sdiff_subset.trans hl))
  have ho : (∑ r ∈ oldInside ∪ L, (Q.outputs r).card) ≤ ∑ r ∈ E, (Q.outputs r).card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hs hl) (by intros; omega)
  have h1 := Nat.pow_le_pow_left (by omega :
    E.card+D.card+oldInside.card+L.card+1 ≤ 4*E.card+1) 2
  have h2 := Nat.pow_le_pow_left (Nat.add_le_add_right ht 1) 2
  have h3 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.add_le_add_right ht 1)
    (by omega : oldInside.card+L.card+1 ≤ 2*E.card+1)) (Nat.add_le_add_right ho 1)
  dsimp only [stateCharge, stateCap]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left h1 1) h2) h3

/-- Indexed-storage charge; physical whole-array copying is not identified
with a coordinate update. The storage model is an explicit complexity premise. -/
def chargedState {n m : ℕ} (Q : CRS (Fin n) (Fin m)) (state : QueryState n m)
    (removed added E L : Finset (Fin m)) : QueryState n m × ℕ :=
  (applyLocalState Q state removed added E L,
    stateCharge Q E (removed ∪ added) (maskRegion E (fun r => state.answer[r.val])) L)

theorem chargedState_refines {n m : ℕ} (Q : CRS (Fin n) (Fin m)) (state : QueryState n m)
    (removed added E L : Finset (Fin m)) :
    (chargedState Q state removed added E L).1 = applyLocalState Q state removed added E L := rfl

theorem chargedState_bound {n m : ℕ} (Q : CRS (Fin n) (Fin m)) (state : QueryState n m)
    (removed added E L : Finset (Fin m)) (hd : removed ∪ added ⊆ E) (hl : L ⊆ E) :
    (chargedState Q state removed added E L).2 ≤ stateCap Q E :=
  stateCharge_le Q E _ _ L hd (Finset.filter_subset _ _) hl

theorem applyLocalState_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (C : Catalysis (Fin n) (Fin m)) [∀ x r, Decidable (C x r)]
    (succ : Fin m → Finset (Fin m)) (needs : Fin m → Finset (Fin n))
    (hi : IndexSound Q C succ) (hn : NeedsSound Q C needs)
    (A removed added E : Finset (Fin m)) (state : QueryState n m)
    (cert : List (List (Fin m)))
    (ho : ∀ r, state.answer[r.val] = true ↔ r ∈ evaluate Q C A)
    (ha : ∀ r, state.available[r.val] = true ↔ r ∈ A)
    (hc : ∀ x, state.counts[x.val] = producerCount Q (evaluate Q C A) x)
    {L : Finset (Fin m)}
    (h : checkMaskedLocal Q C succ needs (fun r => state.answer[r.val])
      (editedMask (fun r => state.available[r.val]) removed added) (removed ∪ added) E
      (fun x => state.counts[x.val]) cert = some L) :
    (∀ r, (applyLocalState Q state removed added E L).answer[r.val] = true ↔
      r ∈ evaluate Q C ((A \ removed) ∪ added)) ∧
    (∀ x, (applyLocalState Q state removed added E L).counts[x.val] =
      producerCount Q (evaluate Q C ((A \ removed) ∪ added)) x) ∧
    (∀ r, (applyLocalState Q state removed added E L).available[r.val] = true ↔
      r ∈ (A \ removed) ∪ added) := by
  have hs := accepted_state_transition Q C succ needs hi hn A removed added E
    state.counts cert state.answer state.available ho ha hc h
  exact ⟨hs.1, hs.2, fun r => patchAvailability_correct state.available A removed added ha r⟩

end RAFQueryCompilation
