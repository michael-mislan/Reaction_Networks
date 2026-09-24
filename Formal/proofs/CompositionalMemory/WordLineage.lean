import proofs.CompositionalMemory.SourceBirthGeometry

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

/-- Follow the first daughter, requiring BOTH daughters to return at every
ancestral division. The second daughter's subsequent descendants are not tested. -/
noncomputable def wordLineageNext {α : Type*} [Fintype α]
    (K : α → FiniteLaw (Option (α × α))) : Option α → FiniteLaw (Option α)
  | none => FiniteLaw.pure none
  | some n => (K n).bind (fun x => FiniteLaw.pure (x.map Prod.fst))

noncomputable def wordLineageKernel {α : Type*} [Fintype α]
    (K : α → FiniteLaw (Option (α × α))) : FiniteKernel (Option α) := {
  prob := fun x y => (wordLineageNext K x).mass y
  nonneg := fun x y => (wordLineageNext K x).nonneg y
  row_sum := fun x => (wordLineageNext K x).total }

noncomputable def wordLineageSuccess {α : Type*} [Fintype α]
    (K : α → FiniteLaw (Option (α × α))) (G : ℕ) (n : α) : ℝ :=
  1-(wordLineageKernel K).steps G (FiniteKernel.eventIndicator {none}) (some n)

theorem word_lineage_bound {α : Type*} [Fintype α]
    (K : α → FiniteLaw (Option (α × α))) (ε : ℝ) (hε : 0 ≤ ε)
    (hK : ∀ n, (K n).mass none ≤ ε) (G : ℕ) (n : α) :
    1-(G : ℝ)*ε ≤ wordLineageSuccess K G n := by
  classical
  have hstep (x : Option α) :
      (wordLineageKernel K).step (FiniteKernel.eventIndicator {none}) x ≤
        FiniteKernel.eventIndicator {none} x+ε := by
    change (wordLineageNext K x).expect (FiniteKernel.eventIndicator {none}) ≤ _
    rw [expect_failure]
    cases x with
    | none => simpa [wordLineageNext,FiniteLaw.pure,FiniteKernel.eventIndicator] using
        (le_add_of_nonneg_right hε : (1 : ℝ) ≤ 1+ε)
    | some x => simpa [wordLineageNext,option_map_failure,FiniteKernel.eventIndicator] using hK x
  have h := (wordLineageKernel K).steps_drift_bound (FiniteKernel.eventIndicator {none}) ε hstep G (some n)
  simp only [FiniteKernel.eventIndicator,Set.mem_singleton_iff,Option.some_ne_none,if_false,zero_add] at h
  unfold wordLineageSuccess
  linarith only [h]

end CompositionalMemory
