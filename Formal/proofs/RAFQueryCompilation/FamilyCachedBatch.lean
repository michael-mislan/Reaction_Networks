import proofs.RAFQueryCompilation.FamilyProtocol

namespace RAFQueryCompilation.ModuleFamily
open RAF

/-- Pass the compiled vectors through the entire batch. In particular, the
successor and needs arguments below are vector reads, not source builders. -/
def familyCachedPointReuse {n : ℕ} (cache : CompiledSource (n*2+1+1) (n*2+1)) :
    List (PairEdit n) → QueryState (n*2+1+1) (n*2+1) → FamilyPointResult n
  | [], state => ⟨[],state,0⟩
  | edit::rest, state =>
    let step := hybridQuery (indexedSource n) (indexedCats n)
      (fun r => cache.successors[r.val]) (fun r => cache.needs[r.val]) state
      edit.removed edit.added (indexedRegion edit.pair) (indexedCertificate edit.pair) 1011
    let answer := step.1.answer[(reactionCode n (some (edit.pair,true))).val]
    let tail := familyCachedPointReuse cache rest step.1
    ⟨answer::tail.members,tail.state,step.2+2+tail.charge⟩

theorem familyCachedPointReuse_refines {n : ℕ}
    (cache : CompiledSource (n*2+1+1) (n*2+1))
    (hs : ∀ r, cache.successors[r.val] =
      sourceSuccessors (indexedSource n) (fun x r => x ∈ indexedCats n r) r)
    (hn : ∀ r, cache.needs[r.val] =
      sourceNeeds (indexedSource n) (fun x r => x ∈ indexedCats n r) r)
    (edits : List (PairEdit n)) (state : QueryState (n*2+1+1) (n*2+1)) :
    familyCachedPointReuse cache edits state = familyPointReuse edits state := by
  induction edits generalizing state with
  | nil => rfl
  | cons edit rest ih =>
    simp only [familyCachedPointReuse,familyPointReuse,hs,hn,ih]

/-- Source compilation appears once and its value is passed to the recursion. -/
def familyCachedRun {n : ℕ} (A : Finset (Fin (n*2+1))) (edits : List (PairEdit n)) :
    FamilyPointResult n :=
  let cache := compileSource (indexedSource n) (indexedCats n) A
  let result := familyCachedPointReuse cache edits cache.state
  { result with charge := cache.charge+result.charge }

theorem familyCachedRun_members {n : ℕ} (A : Finset (Fin (n*2+1)))
    (edits : List (PairEdit n)) :
    (familyCachedRun A edits).members = familyPointTrace edits A := by
  have hr := familyCachedPointReuse_refines
    (compileSource (indexedSource n) (indexedCats n) A)
    (by intro r; simp [compileSource]) (by intro r; simp [compileSource])
    edits (compileSource (indexedSource n) (indexedCats n) A).state
  have hc := familyPointReuse_correct edits
    (compileSource (indexedSource n) (indexedCats n) A).state A
    (compileSource_state_correct (indexedSource n) (indexedCats n) A)
  simpa only [familyCachedRun,hr] using hc.1

theorem familyCachedRun_bound {n : ℕ} (A : Finset (Fin (n*2+1)))
    (edits : List (PairEdit n)) :
    (familyCachedRun A edits).charge ≤ familySetupCap n+1014*edits.length := by
  have hr := familyCachedPointReuse_refines
    (compileSource (indexedSource n) (indexedCats n) A)
    (by intro r; simp [compileSource]) (by intro r; simp [compileSource])
    edits (compileSource (indexedSource n) (indexedCats n) A).state
  have hc := familyPointReuse_bound edits
    (compileSource (indexedSource n) (indexedCats n) A).state
  have hs := family_setup_bound A
  simp only [familyCachedRun,hr]
  omega

end RAFQueryCompilation.ModuleFamily
