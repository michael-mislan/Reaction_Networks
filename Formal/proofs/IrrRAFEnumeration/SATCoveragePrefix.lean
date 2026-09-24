import proofs.IrrRAFEnumeration.SATPreparedCoverage

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource

def coverageSourcePrefix {n m : Nat} (Φ : Fin m → Finset (Choice n)) : List Bool :=
  conflictSourcePrefix Φ ++ coverageSourceRows Φ

def afterCoverageRows {n m : Nat} (Φ : Fin m → Finset (Choice n)) : List Bool :=
  (List.ofFn (fun j : Fin (Fintype.card (Step n m)+1-3*n) =>
    reactionRows Φ (.inr ⟨3*n+j.val,by
      have hn : 3*n ≤ Fintype.card (Step n m)+1 := by rw [step_card]; omega
      have hj := j.isLt
      omega⟩))).flatten

theorem sourceBits_eq_coverage_prefix_append {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    sourceBits Φ = coverageSourcePrefix Φ ++ afterCoverageRows Φ := by
  have hn : 3*n ≤ Fintype.card (Step n m)+1 := by rw [step_card]; omega
  have he : Fintype.card (Step n m)+1-n = n*2+(Fintype.card (Step n m)+1-3*n) := by omega
  let f := fun j : Fin (Fintype.card (Step n m)+1-n) => reactionRows Φ (.inr
    ⟨n+j.val,by have hj := j.isLt; omega⟩)
  have hs := (List.ofFn_congr he f).trans
    (ofFn_sum_equiv (a := n*2) (b := Fintype.card (Step n m)+1-3*n)
      (fun j => f (Fin.cast he.symm j)))
  have hl : (List.ofFn (fun i : Fin (n*2) =>
      f (Fin.cast he.symm (finSumFinEquiv (.inl i))))).flatten = coverageSourceRows Φ := by
    rw [ofFn_prod_equiv]
    have hf : ∀ xs : List (List (List Bool)), xs.flatten.flatten = (xs.map List.flatten).flatten := by
      intro xs
      induction xs with
      | nil => rfl
      | cons x xs ih => simp only [List.flatten_cons,List.flatten_append,List.map_cons,ih]
    rw [hf,List.map_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    have h0 : f (Fin.cast he.symm (finSumFinEquiv (.inl (finProdFinEquiv (i,0))))) =
        reactionRows Φ (auxiliaryReaction (.coverage (i,false))) := by
      apply congrArg (reactionRows Φ)
      apply congrArg Sum.inr
      apply Fin.ext
      simp [stepCode,stepOffset,stepEquiv,finSumFinEquiv,
        choiceOffset,finProdFinEquiv,bitCode,Nat.mul_comm]
    have h1 : f (Fin.cast he.symm (finSumFinEquiv (.inl (finProdFinEquiv (i,1))))) =
        reactionRows Φ (auxiliaryReaction (.coverage (i,true))) := by
      apply congrArg (reactionRows Φ)
      apply congrArg Sum.inr
      apply Fin.ext
      simp [stepCode,stepOffset,stepEquiv,finSumFinEquiv,
        choiceOffset,finProdFinEquiv,bitCode,Nat.mul_comm]
    simp only [Function.comp_apply,List.ofFn_succ,List.ofFn_zero,
      List.flatten_cons,List.flatten_nil,List.append_nil]
    exact congrArg₂ List.append h0 h1
  have hr : (List.ofFn (fun j : Fin (Fintype.card (Step n m)+1-3*n) =>
      f (Fin.cast he.symm (finSumFinEquiv (.inr j))))).flatten = afterCoverageRows Φ := by
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext j
    apply congrArg (reactionRows Φ)
    apply congrArg Sum.inr
    apply Fin.ext
    simp [finSumFinEquiv]
    omega
  rw [sourceBits_eq_conflict_prefix_append Φ]
  change conflictSourcePrefix Φ ++ (List.ofFn f).flatten = _
  rw [hs,List.flatten_append,hl,hr]
  simp only [coverageSourcePrefix,List.append_assoc]

end IrrRAFEnumeration.SATSource
