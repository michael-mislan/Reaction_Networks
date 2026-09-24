import proofs.RAFQueryCompilation.SupportState

namespace RAFQueryCompilation
open RAF

def eraseSupportList {R : Type*} [DecidableEq R] : Finset R → List R → Finset R
  | A, [] => A
  | A, r::rest => eraseSupportList (A.erase r) rest

def checkSupportList {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) : SupportState n m → List (Fin m) → Option (SupportState n m)
  | state, [] => some state
  | state, r::rest =>
    match checkSupportRemoval Q cats state r with
    | none => none
    | some next => checkSupportList Q cats next rest

theorem checkSupportList_sound {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (order : List (Fin m))
    (state next : SupportState n m) (A : Finset (Fin m))
    (ha : ∀ r, state.active[r.val] = true ↔ r ∈ A)
    (hc : ∀ x, state.counts[x.val] = producerCount Q A x)
    (h : checkSupportList Q cats state order = some next) :
    (∀ r, next.active[r.val] = true ↔ r ∈ eraseSupportList A order) ∧
    (∀ x, next.counts[x.val] = producerCount Q (eraseSupportList A order) x) ∧
    evaluate Q (fun x r => x ∈ cats r) (eraseSupportList A order) = evaluate Q (fun x r => x ∈ cats r) A := by
  induction order generalizing state A with
  | nil =>
    cases Option.some.inj h
    exact ⟨ha,hc,rfl⟩
  | cons r rest ih =>
    cases hs : checkSupportRemoval Q cats state r with
    | none => simp [checkSupportList,hs] at h
    | some middle =>
      have hm := checkSupportRemoval_sound Q cats state middle A r ha hc hs
      have ht := ih middle (A.erase r) hm.1 hm.2.1 (by simpa [checkSupportList,hs] using h)
      exact ⟨ht.1,ht.2.1,ht.2.2.trans hm.2.2⟩

end RAFQueryCompilation
