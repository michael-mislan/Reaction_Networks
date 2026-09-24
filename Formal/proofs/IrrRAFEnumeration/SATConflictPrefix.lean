import proofs.IrrRAFEnumeration.SATPreparedConflict

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource

def conflictSourcePrefix {n m : Nat} (Φ : Fin m → Finset (Choice n)) : List Bool :=
  sourcePrefixBits Φ ++
    (List.ofFn (fun i : Fin n => reactionRows Φ (auxiliaryReaction (.conflict i)))).flatten

def afterConflictRows {n m : Nat} (Φ : Fin m → Finset (Choice n)) : List Bool :=
  (List.ofFn (fun j : Fin (Fintype.card (Step n m)+1-n) =>
    reactionRows Φ (.inr ⟨n+j.val,by
      have hn : n ≤ Fintype.card (Step n m)+1 := by rw [step_card]; omega
      have hj := j.isLt
      omega⟩))).flatten

/-- The initialized conflict machine's output is literally the next prefix
of sourceBits; the remaining auxiliary reactions begin at index n. -/
theorem sourceBits_eq_conflict_prefix_append {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    sourceBits Φ = conflictSourcePrefix Φ ++ afterConflictRows Φ := by
  have hn : n ≤ Fintype.card (Step n m)+1 := by rw [step_card]; omega
  have he : Fintype.card (Step n m)+1 = n+(Fintype.card (Step n m)+1-n) := by omega
  let f := fun j : Fin (Fintype.card (Step n m)+1) => reactionRows Φ (.inr j)
  have hs := (List.ofFn_congr he f).trans
    (ofFn_sum_equiv (a := n) (b := Fintype.card (Step n m)+1-n)
      (fun j => f (Fin.cast he.symm j)))
  have hl : List.ofFn (fun i : Fin n => f (Fin.cast he.symm (finSumFinEquiv (.inl i)))) =
      List.ofFn (fun i : Fin n => reactionRows Φ (auxiliaryReaction (.conflict i))) := by
    apply congrArg List.ofFn
    funext i
    apply congrArg (reactionRows Φ)
    apply congrArg Sum.inr
    apply Fin.ext
    simp [stepCode,stepOffset,stepEquiv,finSumFinEquiv]
  rw [hl] at hs
  have hr : (List.ofFn (fun j : Fin (Fintype.card (Step n m)+1-n) =>
      f (Fin.cast he.symm (finSumFinEquiv (.inr j))))).flatten = afterConflictRows Φ := by
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext j
    apply congrArg (reactionRows Φ)
    apply congrArg Sum.inr
    apply Fin.ext
    simp [finSumFinEquiv]
  rw [sourceBits_eq_prefix_append Φ]
  change sourcePrefixBits Φ ++ (List.ofFn f).flatten = _
  rw [hs,List.flatten_append,hr]
  simp only [conflictSourcePrefix,List.append_assoc]

end IrrRAFEnumeration.SATSource
