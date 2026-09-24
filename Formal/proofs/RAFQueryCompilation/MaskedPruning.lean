import proofs.RAFQueryCompilation.FreshEvaluation
import proofs.RAFQueryCompilation.VectorPatch

namespace RAFQueryCompilation
open RAF

def pruneWithMoleculeMask {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A : Finset (Fin m)) (pool : Finset (Fin n)) :
    Finset (Fin m) :=
  let mask := patchVector (Vector.replicate n false) pool (fun _ => true)
  A.filter fun r =>
    (((Q.inputs r).sort (· ≤ ·)).all fun x => mask[x.val]) &&
    (((cats r).sort (· ≤ ·)).any fun x => mask[x.val])

theorem pruneWithMoleculeMask_eq {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A : Finset (Fin m)) (pool : Finset (Fin n)) :
    pruneWithMoleculeMask Q cats A pool = pruneWithPool Q (fun x r => x ∈ cats r) A pool := by
  ext r
  simp [pruneWithMoleculeMask, pruneWithPool, List.all_eq_true, List.any_eq_true,
    patchVector_get, Finset.subset_iff]; aesop

def maskedFreshPruningFuel {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) : ℕ → Finset (Fin m) → Finset (Fin m)
  | 0, A => A
  | fuel+1, A =>
    let pool := (freshClosureFuel Q A n Q.food).1
    let next := pruneWithMoleculeMask Q cats A pool
    if next = A then A else maskedFreshPruningFuel Q cats fuel next

theorem maskedFreshPruningFuel_refines {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (fuel : ℕ) (A : Finset (Fin m)) :
    maskedFreshPruningFuel Q cats fuel A = (freshPruningFuel Q cats fuel A).1 := by
  induction fuel generalizing A with
  | zero => rfl
  | succ fuel ih =>
    simp only [maskedFreshPruningFuel, freshPruningFuel, Fintype.card_fin, pruneWithMoleculeMask_eq]
    split
    · rfl
    · exact ih _

def maskedFreshEvaluate {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A : Finset (Fin m)) : Finset (Fin m) :=
  maskedFreshPruningFuel Q cats A.card A

theorem maskedFreshEvaluate_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A : Finset (Fin m)) :
    maskedFreshEvaluate Q cats A = evaluate Q (fun x r => x ∈ cats r) A := by
  rw [maskedFreshEvaluate, maskedFreshPruningFuel_refines]
  exact freshEvaluate_refines Q cats A

end RAFQueryCompilation
