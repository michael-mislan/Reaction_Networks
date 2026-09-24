import proofs.RAFQueryCompilation.FamilyBatchState
import proofs.RAFQueryCompilation.PointQuery

namespace RAFQueryCompilation.ModuleFamily
open RAF

def familyPointBaseline {n : ℕ} : List (PairEdit n) → Vector Bool (n*2+1) → PointStep (n*2+1)
  | [], available => ⟨[],available,0⟩
  | edit::rest, available =>
    let step := freshPointQuery (indexedSource n) (indexedCats n) available edit.removed edit.added
      [reactionCode n (some (edit.pair,true))]
    let tail := familyPointBaseline rest step.available
    ⟨step.members++tail.members,tail.available,step.charge+tail.charge⟩

def familyPointTrace {n : ℕ} : List (PairEdit n) → Finset (Fin (n*2+1)) → List Bool
  | [], _ => []
  | edit::rest, A =>
    let B := (A \ edit.removed) ∪ edit.added
    decide (reactionCode n (some (edit.pair,true)) ∈
      evaluate (indexedSource n) (fun x r => x ∈ indexedCats n r) B)::familyPointTrace rest B

theorem familyPointBaseline_correct {n : ℕ} (edits : List (PairEdit n))
    (available : Vector Bool (n*2+1)) (A : Finset (Fin (n*2+1)))
    (ha : ∀ r, available[r.val] = true ↔ r ∈ A) :
    (familyPointBaseline edits available).members = familyPointTrace edits A ∧
    (∀ r, (familyPointBaseline edits available).available[r.val] = true ↔
      r ∈ familyFinalAvailable edits A) := by
  induction edits generalizing available A with
  | nil => exact ⟨rfl,ha⟩
  | cons edit rest ih =>
    let step := freshPointQuery (indexedSource n) (indexedCats n) available edit.removed edit.added
      [reactionCode n (some (edit.pair,true))]
    have hs := freshPointQuery_correct (indexedSource n) (indexedCats n) available A
      edit.removed edit.added [reactionCode n (some (edit.pair,true))] ha
    have ht := ih step.available ((A \ edit.removed) ∪ edit.added) hs.2
    constructor
    · change step.members++(familyPointBaseline rest step.available).members = _
      rw [hs.1,ht.1]
      rfl
    · exact ht.2

theorem familyPointBaseline_reads {n : ℕ} (edits : List (PairEdit n))
    (available : Vector Bool (n*2+1)) :
    (n*2+1)*edits.length ≤ (familyPointBaseline edits available).charge := by
  induction edits generalizing available with
  | nil => simp [familyPointBaseline]
  | cons edit rest ih =>
    have hs := freshPointQuery_reads (indexedSource n) (indexedCats n) available edit.removed edit.added
      [reactionCode n (some (edit.pair,true))]
    have ht := ih (freshPointQuery (indexedSource n) (indexedCats n) available edit.removed edit.added
      [reactionCode n (some (edit.pair,true))]).available
    simp only [familyPointBaseline,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

/-- One additional mask read per query is included on the reuse side. -/
theorem family_saves_against_points {n : ℕ} (edits : List (PairEdit n))
    (state : QueryState (n*2+1+1) (n*2+1)) (setup : ℕ)
    (h : setup+1013*edits.length < (n*2+1)*edits.length) :
    setup+(familyBatch edits state).2+edits.length < (familyPointBaseline edits state.available).charge := by
  have hl := familyBatch_bound edits state
  have hr := familyPointBaseline_reads edits state.available
  omega

end RAFQueryCompilation.ModuleFamily
