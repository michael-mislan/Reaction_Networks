import proofs.RAFQueryCompilation.SequentialState

namespace RAFQueryCompilation
open RAF

def addOutputCounts {n m : ℕ} (Q : CRS (Fin n) (Fin m)) (counts : Vector ℕ n)
    (r : Fin m) : Vector ℕ n := modifyVector counts (Q.outputs r) (fun _ value => value+1)

def countSourceRows {n m : ℕ} (Q : CRS (Fin n) (Fin m)) : List (Fin m) → Vector ℕ n → Vector ℕ n
  | [], counts => counts
  | r::rest, counts => countSourceRows Q rest (addOutputCounts Q counts r)

theorem countSourceRows_get {n m : ℕ} (Q : CRS (Fin n) (Fin m)) (order : List (Fin m))
    (counts : Vector ℕ n) (hnd : order.Nodup) (x : Fin n) :
    (countSourceRows Q order counts)[x.val] = counts[x.val]+producerCount Q order.toFinset x := by
  induction order generalizing counts with
  | nil => simp [countSourceRows,producerCount]
  | cons r rest ih =>
    have hn := List.nodup_cons.mp hnd
    have hr : r ∉ rest.toFinset := by simpa using hn.1
    simp only [countSourceRows,ih _ hn.2,addOutputCounts,modifyVector_get,List.toFinset_cons]
    by_cases hx : x ∈ Q.outputs r
    · simp [producerCount,Finset.filter_insert,hx,hr,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · simp [producerCount,Finset.filter_insert,hx]

/-- Initialize by traversing output incidences once, rather than scanning A per molecule. -/
def sourceCounts {n m : ℕ} (Q : CRS (Fin n) (Fin m)) (A : Finset (Fin m)) : Vector ℕ n :=
  countSourceRows Q (A.sort (· ≤ ·)) (Vector.replicate n 0)

theorem sourceCounts_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m)) (A : Finset (Fin m)) (x : Fin n) :
    (sourceCounts Q A)[x.val] = producerCount Q A x := by
  simp [sourceCounts,countSourceRows_get Q _ _ (Finset.sort_nodup _ _) x]

end RAFQueryCompilation
