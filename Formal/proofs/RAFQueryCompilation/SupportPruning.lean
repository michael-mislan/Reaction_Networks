import proofs.RAFQueryCompilation.SupportReplay
import proofs.RAFQueryCompilation.PruningCertificate
import proofs.RAFQueryCompilation.SourceCounts

namespace RAFQueryCompilation
open RAF

structure SupportRound (m : ℕ) where
  removals : List (Fin m)
  closureOrder : List (Fin m)

def initialSupport {n m : ℕ} (Q : CRS (Fin n) (Fin m)) (A : Finset (Fin m)) : SupportState n m :=
  { active := patchVector (Vector.replicate m false) A (fun _ => true)
    counts := sourceCounts Q A }

def activeSupport {n m : ℕ} (state : SupportState n m) : Finset (Fin m) :=
  Finset.univ.filter (fun r => state.active[r.val])

/-- Support removals are checked with current counts; food closure is still mandatory. -/
def checkSupportPruning {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) : Finset (Fin m) → List (SupportRound m) → Option (Finset (Fin m))
  | _, [] => none
  | A, round::rest =>
    match checkSupportList Q cats (initialSupport Q A) round.removals with
    | none => none
    | some state =>
      let B := activeSupport state
      match checkClosure Q B round.closureOrder with
      | none => none
      | some pool =>
        let T := pruneWithPool Q (fun x r => x ∈ cats r) B pool
        if T = B then some B else checkSupportPruning Q cats T rest

theorem checkSupportPruning_sound {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (cert : List (SupportRound m)) (A : Finset (Fin m))
    {answer : Finset (Fin m)} (h : checkSupportPruning Q cats A cert = some answer) :
    answer = evaluate Q (fun x r => x ∈ cats r) A := by
  induction cert generalizing A with
  | nil => simp [checkSupportPruning] at h
  | cons round rest ih =>
    cases hs : checkSupportList Q cats (initialSupport Q A) round.removals with
    | none => simp [checkSupportPruning,hs] at h
    | some state =>
      have hi := checkSupportList_sound Q cats round.removals (initialSupport Q A) state A
        (by intro r; simp [initialSupport,patchVector_get])
        (by intro x; simp [initialSupport,sourceCounts_correct]) hs
      have hb : activeSupport state = eraseSupportList A round.removals := by
        ext r
        simp [activeSupport,hi.1]
      have he : evaluate Q (fun x r => x ∈ cats r) (activeSupport state) =
          evaluate Q (fun x r => x ∈ cats r) A := by rw [hb]; exact hi.2.2
      cases hc : checkClosure Q (activeSupport state) round.closureOrder with
      | none => simp [checkSupportPruning,hs,hc] at h
      | some pool =>
        have hp := checkClosure_sound Q (activeSupport state) round.closureOrder hc
        subst pool
        simp only [checkSupportPruning,hs,hc] at h
        change (if executablePrune Q (fun x r => x ∈ cats r) (activeSupport state) = activeSupport state
          then some (activeSupport state) else checkSupportPruning Q cats
            (executablePrune Q (fun x r => x ∈ cats r) (activeSupport state)) rest) = some answer at h
        split at h
        next hf =>
          cases Option.some.inj h
          exact (evaluate_of_fixed Q _ _ hf).symm.trans he
        next =>
          exact (ih _ h).trans ((evaluate_prune Q _ _).trans he)

end RAFQueryCompilation
