import proofs.RAFQueryCompilation.FreshEvaluation
import proofs.RAFQueryCompilation.BudgetQueryState

namespace RAFQueryCompilation
open RAF

def freshAvailable {n m : ℕ} (state : QueryState n m) (removed added : Finset (Fin m)) :
    Finset (Fin m) :=
  Finset.univ.filter (fun r => editedMask (fun s => state.available[s.val]) removed added r)

def rebuildState {n m : ℕ} (Q : CRS (Fin n) (Fin m)) (B answer : Finset (Fin m)) : QueryState n m :=
  { answer := Vector.ofFn (fun r => decide (r ∈ answer))
    available := Vector.ofFn (fun r => decide (r ∈ B))
    counts := Vector.ofFn (producerCount Q answer) }

/-- Dense mask scan, including membership in both edit lists. -/
def freshMaskCharge {m : ℕ} (removed added : Finset (Fin m)) : ℕ :=
  1+m*(removed.card+added.card+3)

/-- Allocate and populate three vectors. Counts scan the answer's output rows.
Row lengths and vector accesses use the declared cached-cardinality RAM model. -/
def rebuildCharge {n m : ℕ} (Q : CRS (Fin n) (Fin m)) (B answer : Finset (Fin m)) : ℕ :=
  2*m+n+answer.card+m*(answer.card+1)+m*(B.card+1)+
    n*(answer.card+1)*((∑ r ∈ answer, (Q.outputs r).card)+1)

def freshQuery {n m : ℕ} (Q : CRS (Fin n) (Fin m)) (cats : Fin m → Finset (Fin n))
    (state : QueryState n m) (removed added : Finset (Fin m)) : QueryState n m × ℕ :=
  let B := freshAvailable state removed added
  let result := freshEvaluate Q cats B
  (rebuildState Q B result.1,
    freshMaskCharge removed added+result.2+rebuildCharge Q B result.1)

theorem freshAvailable_correct {n m : ℕ} (state : QueryState n m)
    (A removed added : Finset (Fin m))
    (ha : ∀ r, state.available[r.val] = true ↔ r ∈ A) :
    freshAvailable state removed added = (A \ removed) ∪ added := by
  ext r
  simpa only [freshAvailable, Finset.mem_filter, Finset.mem_univ, true_and] using
    editedMask_correct (fun s => state.available[s.val]) A removed added ha r

theorem freshQuery_state_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (state : QueryState n m)
    (A removed added : Finset (Fin m))
    (ha : ∀ r, state.available[r.val] = true ↔ r ∈ A) :
    (∀ r, (freshQuery Q cats state removed added).1.answer[r.val] = true ↔
      r ∈ evaluate Q (fun x r => x ∈ cats r) ((A \ removed) ∪ added)) ∧
    (∀ x, (freshQuery Q cats state removed added).1.counts[x.val] =
      producerCount Q (evaluate Q (fun x r => x ∈ cats r) ((A \ removed) ∪ added)) x) ∧
    (∀ r, (freshQuery Q cats state removed added).1.available[r.val] = true ↔
      r ∈ (A \ removed) ∪ added) := by
  simp [freshQuery, freshEvaluate_refines, freshAvailable_correct state A removed added ha, rebuildState]

theorem freshQuery_reads {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (state : QueryState n m)
    (removed added : Finset (Fin m)) : m ≤ (freshQuery Q cats state removed added).2 := by
  have h : m ≤ m*(removed.card+added.card+3) :=
    Nat.le_mul_of_pos_right _ (by omega)
  dsimp only [freshQuery, freshMaskCharge]
  omega

end RAFQueryCompilation
