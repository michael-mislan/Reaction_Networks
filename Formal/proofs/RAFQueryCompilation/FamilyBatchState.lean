import proofs.RAFQueryCompilation.FamilyBatch

namespace RAFQueryCompilation.ModuleFamily
open RAF

def familyFinalAvailable {n : ℕ} : List (PairEdit n) → Finset (Fin (n*2+1)) → Finset (Fin (n*2+1))
  | [], A => A
  | edit::rest, A => familyFinalAvailable rest ((A \ edit.removed) ∪ edit.added)

def FamilyStateCorrect {n : ℕ} (A : Finset (Fin (n*2+1)))
    (state : QueryState (n*2+1+1) (n*2+1)) : Prop :=
  (∀ r, state.answer[r.val] = true ↔ r ∈ evaluate (indexedSource n) (fun x r => x ∈ indexedCats n r) A) ∧
  (∀ x, state.counts[x.val] = producerCount (indexedSource n)
    (evaluate (indexedSource n) (fun x r => x ∈ indexedCats n r) A) x) ∧
  (∀ r, state.available[r.val] = true ↔ r ∈ A)

theorem familyBatch_state_correct {n : ℕ} (edits : List (PairEdit n))
    (state : QueryState (n*2+1+1) (n*2+1)) (A : Finset (Fin (n*2+1)))
    (h : FamilyStateCorrect A state) :
    FamilyStateCorrect (familyFinalAvailable edits A) (familyBatch edits state).1 := by
  induction edits generalizing state A with
  | nil => exact h
  | cons edit rest ih =>
    let next := hybridQuery (indexedSource n) (indexedCats n)
      (sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r))
      (sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r)) state
      edit.removed edit.added (indexedRegion edit.pair) (indexedCertificate edit.pair) 1011
    have hs : FamilyStateCorrect ((A \ edit.removed) ∪ edit.added) next.1 :=
      hybridQuery_state_correct (indexedSource n) (indexedCats n) _ _
        (sourceSuccessors_sound _ _) (sourceNeeds_sound _ _)
        A edit.removed edit.added (indexedRegion edit.pair) state (indexedCertificate edit.pair) 1011
        h.1 h.2.2 h.2.1
    exact ih next.1 ((A \ edit.removed) ∪ edit.added) hs

theorem familyFreshBatch_state_correct {n : ℕ} (edits : List (PairEdit n))
    (state : QueryState (n*2+1+1) (n*2+1)) (A : Finset (Fin (n*2+1)))
    (h : FamilyStateCorrect A state) :
    FamilyStateCorrect (familyFinalAvailable edits A) (familyFreshBatch edits state).1 := by
  induction edits generalizing state A with
  | nil => exact h
  | cons edit rest ih =>
    let next := freshQuery (indexedSource n) (indexedCats n) state edit.removed edit.added
    have hs : FamilyStateCorrect ((A \ edit.removed) ∪ edit.added) next.1 :=
      freshQuery_state_correct (indexedSource n) (indexedCats n) state A edit.removed edit.added h.2.2
    exact ih next.1 ((A \ edit.removed) ∪ edit.added) hs

end RAFQueryCompilation.ModuleFamily
