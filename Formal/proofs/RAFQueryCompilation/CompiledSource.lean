import proofs.RAFQueryCompilation.FreshQuery
import proofs.RAFQueryCompilation.FreshBounds

namespace RAFQueryCompilation
open RAF

/-- Explicit allowance for the literal all-pairs source index builders.
This is the cached-row-cardinality charge model, not native elapsed time. -/
def sourceIndexCharge {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) : ℕ :=
  2*m + (∑ r : Fin m, (1+n*(cats r).card+n+
    ((Q.inputs r).card+(cats r).card+1)^2)) +
    ∑ e : Fin m, (1+2*m+∑ r : Fin m,
      ((Q.outputs e).card+1)*(Q.food.card+(Q.inputs r).card+(cats r).card+3))

structure CompiledSource (n m : ℕ) where
  state : QueryState n m
  successors : Vector (Finset (Fin m)) m
  needs : Vector (Finset (Fin n)) m
  initialAnswer : Finset (Fin m)
  charge : ℕ

/-- Construct indices and initial state from source data, without an initial certificate. -/
def compileSource {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A : Finset (Fin m)) : CompiledSource n m :=
  let result := freshEvaluate Q cats A
  { state := rebuildState Q A result.1
    successors := Vector.ofFn (sourceSuccessors Q (fun x r => x ∈ cats r))
    needs := Vector.ofFn (sourceNeeds Q (fun x r => x ∈ cats r))
    initialAnswer := result.1
    charge := sourceIndexCharge Q cats+result.2+rebuildCharge Q A result.1 }

theorem compileSource_state_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A : Finset (Fin m)) :
    (∀ r, (compileSource Q cats A).state.answer[r.val] = true ↔
      r ∈ evaluate Q (fun x r => x ∈ cats r) A) ∧
    (∀ x, (compileSource Q cats A).state.counts[x.val] =
      producerCount Q (evaluate Q (fun x r => x ∈ cats r) A) x) ∧
    (∀ r, (compileSource Q cats A).state.available[r.val] = true ↔ r ∈ A) := by
  simp [compileSource, rebuildState, freshEvaluate_refines]

theorem compileSource_indices_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A : Finset (Fin m)) :
    IndexSound Q (fun x r => x ∈ cats r)
      (fun r => (compileSource Q cats A).successors[r.val]) ∧
    NeedsSound Q (fun x r => x ∈ cats r)
      (fun r => (compileSource Q cats A).needs[r.val]) := by
  simpa [compileSource] using
    And.intro (sourceSuccessors_sound Q (fun x r => x ∈ cats r))
      (sourceNeeds_sound Q (fun x r => x ∈ cats r))

end RAFQueryCompilation
