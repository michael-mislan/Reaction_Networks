import proofs.IrrRAFEnumeration.CompletionQueryClock
import proofs.IrrRAFEnumeration.CompletionVerdictReset

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

def clockQueryInner (k : Nat) (registers : Fin 3 → Tape) (query : List Bool) :
    Fin (3+k+1) → Tape :=
  frameWork (m := 1) (frameWork (m := k) registers (fun _ => regTape 0))
    (fun _ => parkedInput query)

theorem clockQuery_entry {r : Nat} (k : Nat) (U : Finset (Fin r)) (pos index : Nat)
    (base blocks query : List Bool) :
    placedClockWork 7 0 (queryDecisionWork (3+k) U pos index base blocks query)
      (clockQueryInner k initialWork query) =
      queryDecisionWork (3+k) U pos index base blocks query := by
  funext i
  by_cases hi : placeWorkInMiddle (post := 0) 7 (3+k+1) i
  · have hlo : ¬i.val < 7 := by unfold placeWorkInMiddle at hi; omega
    by_cases hik : i.val < 7+(3+k)
    · have hsub : i.val-7 < 3+k := by unfold placeWorkInMiddle at hi; omega
      simp [placedClockWork,hi,placeWorkCoord,clockQueryInner,frameWork,
        initialWork,queryDecisionWork,queryPrefix,hik,hlo,hsub]
    · have hsub : ¬i.val-7 < 3+k := by omega
      simp [placedClockWork,hi,placeWorkCoord,clockQueryInner,frameWork,
        queryDecisionWork,hik,hsub]
  · simp [placedClockWork,hi]

def clockedQueryWork {r : Nat} (p : Polynomial Nat) (k : Nat) (U : Finset (Fin r))
    (pos index : Nat) (base blocks query : List Bool) : Fin (7+(3+k)+1) → Tape :=
  placedClockWork 7 0 (queryDecisionWork (3+k) U pos index base blocks query)
    (clockQueryInner k (clockWork p query.length) query)

def clockedQueryPrepareTM (p : Polynomial Nat) (k : Nat) : TM (7+(3+k)+1) :=
  seqTM (queryPrepareTM (3+k)) (placeWorkTM 7 0 (virtualQueryClockTM p k))

/-- One actual preparation program writes the completion query and computes
its unary clock, preserving query state and the fresh SAT workspace. -/
theorem clockedQueryPrepareTM_correct {d r : Nat} (p : Polynomial Nat) (k : Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) (inp : Tape) (hp : Parked inp) :
    let base := SAT.CNF.encode (assembledBase Q C)
    let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
    let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)
    (clockedQueryPrepareTM p k).HoareTime
      (EmitPred inp (queryDecisionWork (3+k) U 1 0 base blocks []) [])
      (EmitPred inp (clockedQueryWork p k U (1+r) r base blocks query) [])
      (dynamicQueryTime base.length blocks.length r+query.length+5+setupTime p query.length) := by
  dsimp only
  let base := SAT.CNF.encode (assembledBase Q C)
  let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
  let query := SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
    PositiveCompletionCNF.containerExclusions U)
  let W := queryDecisionWork (3+k) U (1+r) r base blocks query
  have hw : ∀ i, Parked (W i) := by
    intro i
    unfold W queryDecisionWork queryPrefix frameWork
    split
    · split
      · exact dynamicWork_parked _ _ _ _ _ _
      · exact parked_regTape _
    · exact parkedInput_parked _
  have h1 := queryPrepareTM_correct (3+k) Q C G U inp hp
  have h2 := placedQueryClockTM_correct p k query inp hp W (fun i _ => hw i)
  change (placeWorkTM 7 0 (virtualQueryClockTM p k)).HoareTime
    (EmitPred inp (placedClockWork 7 0 W (clockQueryInner k initialWork query)) [])
    (EmitPred inp (clockedQueryWork p k U (1+r) r base blocks query) [])
    (setupTime p query.length) at h2
  rw [show placedClockWork 7 0 W (clockQueryInner k initialWork query) = W from
    clockQuery_entry k U (1+r) r base blocks query] at h2
  exact (seqTM_hoareTime _ _ h1 (emitPred_transition hp hw []) h2).mono_bound
    (by dsimp [query]; omega)

end IrrRAFEnumeration.CompletionQuery
