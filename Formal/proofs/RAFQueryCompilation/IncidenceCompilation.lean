import proofs.RAFQueryCompilation.IncidenceIndex
import proofs.RAFQueryCompilation.SupportHybrid

namespace RAFQueryCompilation
open RAF

/-- Executable source state without evaluating a separate all-pairs charge expression. -/
structure IncidenceSource (n m : ℕ) where
  state : QueryState n m
  successors : Vector (Finset (Fin m)) m
  needs : Vector (Finset (Fin n)) m
  initialAnswer : Finset (Fin m)

def compileIncidenceSource {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A : Finset (Fin m)) : IncidenceSource n m :=
  let answer := (freshEvaluate Q cats A).1
  let needs := Vector.ofFn (incidenceNeeds Q cats)
  let consumers := sourceConsumers (fun r => needs[r.val])
  { state := fastRebuildState Q A answer
    successors := Vector.ofFn (incidenceSuccessors Q consumers)
    needs := needs
    initialAnswer := answer }

theorem compileIncidenceSource_state_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A : Finset (Fin m)) :
    (∀ r, (compileIncidenceSource Q cats A).state.answer[r.val] = true ↔
      r ∈ evaluate Q (fun x r => x ∈ cats r) A) ∧
    (∀ x, (compileIncidenceSource Q cats A).state.counts[x.val] =
      producerCount Q (evaluate Q (fun x r => x ∈ cats r) A) x) ∧
    (∀ r, (compileIncidenceSource Q cats A).state.available[r.val] = true ↔ r ∈ A) := by
  simp [compileIncidenceSource, fastRebuildState, patchVector_get,
    sourceCounts_correct, freshEvaluate_refines]

theorem compileIncidenceSource_indices_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A : Finset (Fin m)) :
    IndexSound Q (fun x r => x ∈ cats r)
      (fun r => (compileIncidenceSource Q cats A).successors[r.val]) ∧
    NeedsSound Q (fun x r => x ∈ cats r)
      (fun r => (compileIncidenceSource Q cats A).needs[r.val]) := by
  simpa [compileIncidenceSource] using
    And.intro (incidenceSuccessors_sound Q cats) (incidenceNeeds_sound Q cats)

end RAFQueryCompilation
