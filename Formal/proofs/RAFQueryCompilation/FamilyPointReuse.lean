import proofs.RAFQueryCompilation.FamilySetup

namespace RAFQueryCompilation.ModuleFamily
open RAF

structure FamilyPointResult (n : ℕ) where
  members : List Bool
  state : QueryState (n*2+1+1) (n*2+1)
  charge : ℕ

/-- The charge extends the existing row-cardinality model by one mask read and
one output-list constructor per answer. It is not a native allocation bound. -/
def familyPointReuse {n : ℕ} : List (PairEdit n) →
    QueryState (n*2+1+1) (n*2+1) → FamilyPointResult n
  | [], state => ⟨[], state, 0⟩
  | edit::rest, state =>
    let step := hybridQuery (indexedSource n) (indexedCats n)
      (sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r))
      (sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r)) state
      edit.removed edit.added (indexedRegion edit.pair) (indexedCertificate edit.pair) 1011
    let answer := step.1.answer[(reactionCode n (some (edit.pair,true))).val]
    let tail := familyPointReuse rest step.1
    ⟨answer::tail.members, tail.state, step.2+2+tail.charge⟩

theorem familyPointReuse_correct {n : ℕ} (edits : List (PairEdit n))
    (state : QueryState (n*2+1+1) (n*2+1)) (A : Finset (Fin (n*2+1)))
    (h : FamilyStateCorrect A state) :
    (familyPointReuse edits state).members = familyPointTrace edits A ∧
    FamilyStateCorrect (familyFinalAvailable edits A) (familyPointReuse edits state).state := by
  induction edits generalizing state A with
  | nil => exact ⟨rfl,h⟩
  | cons edit rest ih =>
    let step := hybridQuery (indexedSource n) (indexedCats n)
      (sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r))
      (sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r)) state
      edit.removed edit.added (indexedRegion edit.pair) (indexedCertificate edit.pair) 1011
    have hs : FamilyStateCorrect ((A \ edit.removed) ∪ edit.added) step.1 :=
      hybridQuery_state_correct (indexedSource n) (indexedCats n) _ _
        (sourceSuccessors_sound _ _) (sourceNeeds_sound _ _)
        A edit.removed edit.added (indexedRegion edit.pair) state (indexedCertificate edit.pair) 1011
        h.1 h.2.2 h.2.1
    have ht := ih step.1 ((A \ edit.removed) ∪ edit.added) hs
    constructor
    · change step.1.answer[(reactionCode n (some (edit.pair,true))).val] ::
        (familyPointReuse rest step.1).members = _
      rw [ht.1]
      congr 1
      exact Bool.eq_iff_iff.mpr ((hs.1 _).trans (decide_eq_true_iff).symm)
    · exact ht.2

theorem familyPointReuse_baseline_eq {n : ℕ} (edits : List (PairEdit n))
    (state : QueryState (n*2+1+1) (n*2+1)) (A : Finset (Fin (n*2+1)))
    (h : FamilyStateCorrect A state) :
    (familyPointReuse edits state).members = (familyPointBaseline edits state.available).members := by
  rw [(familyPointReuse_correct edits state A h).1,
    (familyPointBaseline_correct edits state.available A h.2.2).1]

theorem familyPointReuse_bound {n : ℕ} (edits : List (PairEdit n))
    (state : QueryState (n*2+1+1) (n*2+1)) :
    (familyPointReuse edits state).charge ≤ 1014*edits.length := by
  induction edits generalizing state with
  | nil => simp [familyPointReuse]
  | cons edit rest ih =>
    have hs := indexed_hybrid_charge edit.pair state edit.removed edit.added edit.localEdits
    have ht := ih (hybridQuery (indexedSource n) (indexedCats n)
      (sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r))
      (sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r)) state
      edit.removed edit.added (indexedRegion edit.pair) (indexedCertificate edit.pair) 1011).1
    simp only [familyPointReuse,List.length_cons]
    omega

theorem familyPointReuse_saves_with_setup {n : ℕ} (A : Finset (Fin (n*2+1)))
    (edits : List (PairEdit n))
    (h : familySetupCap n+1014*edits.length < (n*2+1)*edits.length) :
    (compileSource (indexedSource n) (indexedCats n) A).charge+
      (familyPointReuse edits (compileSource (indexedSource n) (indexedCats n) A).state).charge <
      (familyPointBaseline edits (compileSource (indexedSource n) (indexedCats n) A).state.available).charge := by
  have hs := family_setup_bound A
  have ht := familyPointReuse_bound edits (compileSource (indexedSource n) (indexedCats n) A).state
  have hb := familyPointBaseline_reads edits (compileSource (indexedSource n) (indexedCats n) A).state.available
  omega

end RAFQueryCompilation.ModuleFamily
