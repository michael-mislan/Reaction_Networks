import proofs.RAFQueryCompilation.ClosedPoolCheck
import proofs.RAFQueryCompilation.RankedLoss

namespace RAFQueryCompilation
open RAF

def checkPruningDirect {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R]
    (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)] :
    Finset R → List (List R) → Option (Finset R)
  | _, [] => none
  | A, order::rest =>
    match checkClosureWithoutUnion Q A order with
    | none => none
    | some pool =>
      let T := pruneWithPool Q C A pool
      if T=A then some A else checkPruningDirect Q C T rest

theorem checkPruningDirect_eq {M R : Type*} [DecidableEq M] [Fintype M] [DecidableEq R]
    (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)]
    (A : Finset R) (cert : List (List R)) : checkPruningDirect Q C A cert = checkPruning Q C A cert := by
  induction cert generalizing A with
  | nil => rfl
  | cons order rest ih =>
    simp only [checkPruningDirect,checkPruning,checkClosureWithoutUnion_eq,ih]
    rfl

def directLocalLoss {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (table : Vector (Finset (Fin m)) m)
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m) (D E : Finset (Fin m))
    (cert : List (List (Fin m))) : Finset (Fin m) × Bool :=
  let localResult := if checkRegion (fun p => table[p.val]) D E then
      checkPruningDirect (withFood Q (maskFood Q needs E (fun r => state.answer[r.val])
        (fun x => state.counts[x.val]))) (fun x r => x ∈ cats r)
        (maskRegion E (fun r => state.answer[r.val] && decide (r ∉ D))) cert
    else none
  match localResult with
  | some L => (maskRegion E (fun r => state.answer[r.val]) \ L,true)
  | none => (maskSet state.answer \ (freshEvaluate Q cats (freshAvailable state D ∅)).1,false)

theorem directLocalLoss_eq {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (table : Vector (Finset (Fin m)) m)
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m) (D E : Finset (Fin m))
    (cert : List (List (Fin m))) :
    directLocalLoss Q cats table needs state D E cert = rankedLossTotal Q cats table needs state D E cert := by
  simp only [directLocalLoss,checkPruningDirect_eq,rankedLossTotal,rankedLossQuery,checkMaskedLocal]
  split <;> simp_all only [Option.map_none,Option.map_some]

end RAFQueryCompilation
