import proofs.RAFQueryCompilation.SupportRemoval
import proofs.RAFQueryCompilation.SequentialState

namespace RAFQueryCompilation
open RAF

structure SupportState (n m : ℕ) where
  active : Vector Bool m
  counts : Vector ℕ n

def dropSupport {n m : ℕ} (Q : CRS (Fin n) (Fin m)) (state : SupportState n m)
    (r : Fin m) : SupportState n m :=
  { active := patchVector state.active {r} (fun _ => false)
    counts := patchCounts Q state.counts {r} ∅ }

def checkSupportRemoval {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (state : SupportState n m) (r : Fin m) :
    Option (SupportState n m) :=
  if state.active[r.val] = true ∧ countSupported Q cats (fun x => state.counts[x.val]) r = false
  then some (dropSupport Q state r) else none

theorem dropSupport_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (state : SupportState n m) (A : Finset (Fin m)) (r : Fin m) (hr : r ∈ A)
    (ha : ∀ s, state.active[s.val] = true ↔ s ∈ A)
    (hc : ∀ x, state.counts[x.val] = producerCount Q A x) :
    (∀ s, (dropSupport Q state r).active[s.val] = true ↔ s ∈ A.erase r) ∧
    (∀ x, (dropSupport Q state r).counts[x.val] = producerCount Q (A.erase r) x) := by
  have hd : A \ A.erase r = {r} := by
    ext s
    by_cases he : s = r
    · subst s; simp [hr]
    · simp [he]
  have he : A.erase r \ A = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr (Finset.erase_subset _ _)
  constructor
  · intro s
    have hm := patchAnswerMask_correct state.active A {r} ∅ ha (Finset.empty_subset _) s
    simpa [dropSupport,and_comm] using hm
  · intro x
    have hp := producer_count_delta Q A (A.erase r) x
    rw [hd,he] at hp
    simpa [dropSupport,patchCounts_get,hc] using hp.symm

theorem checkSupportRemoval_sound {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (state next : SupportState n m)
    (A : Finset (Fin m)) (r : Fin m)
    (ha : ∀ s, state.active[s.val] = true ↔ s ∈ A)
    (hc : ∀ x, state.counts[x.val] = producerCount Q A x)
    (h : checkSupportRemoval Q cats state r = some next) :
    (∀ s, next.active[s.val] = true ↔ s ∈ A.erase r) ∧
    (∀ x, next.counts[x.val] = producerCount Q (A.erase r) x) ∧
    evaluate Q (fun x r => x ∈ cats r) (A.erase r) = evaluate Q (fun x r => x ∈ cats r) A := by
  unfold checkSupportRemoval at h
  split at h
  next ht =>
    cases Option.some.inj h
    have hs := dropSupport_correct Q state A r ((ha r).mp ht.1) ha hc
    exact ⟨hs.1,hs.2,evaluate_erase_unsupported Q cats A _ hc r ht.2⟩
  next => contradiction

end RAFQueryCompilation
