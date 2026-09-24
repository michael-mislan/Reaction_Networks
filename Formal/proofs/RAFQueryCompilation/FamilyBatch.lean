import proofs.RAFQueryCompilation.IndexedFamilyCost
import proofs.RAFQueryCompilation.IndexedFamilyStructure

namespace RAFQueryCompilation.ModuleFamily
open RAF

structure PairEdit (n : ℕ) where
  pair : Fin n
  removed : Finset (Fin (n*2+1))
  added : Finset (Fin (n*2+1))
  localEdits : removed ∪ added ⊆ indexedRegion pair

def familyBatch {n : ℕ} : List (PairEdit n) → QueryState (n*2+1+1) (n*2+1) →
    QueryState (n*2+1+1) (n*2+1) × ℕ
  | [], state => (state,0)
  | edit::rest, state =>
    let step := hybridQuery (indexedSource n) (indexedCats n)
      (sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r))
      (sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r)) state
      edit.removed edit.added (indexedRegion edit.pair) (indexedCertificate edit.pair) 1011
    let tail := familyBatch rest step.1
    (tail.1,step.2+tail.2)

def familyFreshBatch {n : ℕ} : List (PairEdit n) → QueryState (n*2+1+1) (n*2+1) →
    QueryState (n*2+1+1) (n*2+1) × ℕ
  | [], state => (state,0)
  | edit::rest, state =>
    let step := freshQuery (indexedSource n) (indexedCats n) state edit.removed edit.added
    let tail := familyFreshBatch rest step.1
    (tail.1,step.2+tail.2)

theorem familyBatch_bound {n : ℕ} (edits : List (PairEdit n))
    (state : QueryState (n*2+1+1) (n*2+1)) :
    (familyBatch edits state).2 ≤ 1012*edits.length := by
  induction edits generalizing state with
  | nil => simp [familyBatch]
  | cons edit rest ih =>
    have hs := indexed_hybrid_charge edit.pair state edit.removed edit.added edit.localEdits
    have ht := ih (hybridQuery (indexedSource n) (indexedCats n)
      (sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r))
      (sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r)) state
      edit.removed edit.added (indexedRegion edit.pair) (indexedCertificate edit.pair) 1011).1
    simp only [familyBatch,List.length_cons]
    omega

theorem familyFreshBatch_reads {n : ℕ} (edits : List (PairEdit n))
    (state : QueryState (n*2+1+1) (n*2+1)) :
    (n*2+1)*edits.length ≤ (familyFreshBatch edits state).2 := by
  induction edits generalizing state with
  | nil => simp [familyFreshBatch]
  | cons edit rest ih =>
    have hs := freshQuery_reads (indexedSource n) (indexedCats n) state edit.removed edit.added
    have ht := ih (freshQuery (indexedSource n) (indexedCats n) state edit.removed edit.added).1
    simp only [familyFreshBatch,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

/-- Setup remains an explicit charge, not free preprocessing. This implication
is conditional on the actual setup charge being covered by the batch length. -/
theorem familyBatch_with_setup {n : ℕ} (edits : List (PairEdit n))
    (state : QueryState (n*2+1+1) (n*2+1)) (setup : ℕ) (hsetup : setup ≤ edits.length) :
    setup+(familyBatch edits state).2 ≤ 1013*edits.length := by
  have h := familyBatch_bound edits state
  omega

theorem familyBatch_strict_saving {n : ℕ} (edits : List (PairEdit n))
    (state : QueryState (n*2+1+1) (n*2+1)) (setup : ℕ)
    (h : setup+1012*edits.length < (n*2+1)*edits.length) :
    setup+(familyBatch edits state).2 < (familyFreshBatch edits state).2 := by
  have hl := familyBatch_bound edits state
  have hr := familyFreshBatch_reads edits state
  omega

end RAFQueryCompilation.ModuleFamily
