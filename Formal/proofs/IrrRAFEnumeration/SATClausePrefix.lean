import proofs.IrrRAFEnumeration.SATPreparedClause

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource

theorem clauseRowsPrefix_eq_ofFn {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (j : Fin m) (fuel : Nat) :
    clauseRowsPrefix Φ j fuel = (List.ofFn (fun i : Fin fuel => clauseRowAt Φ j i.val)).flatten := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [clauseRowsPrefix,List.ofFn_succ_last,List.flatten_append]
      simpa only [Fin.val_castSucc,Fin.val_last,List.flatten_cons,List.flatten_nil,List.append_nil]
        using congrArg (fun xs => xs ++ clauseRowAt Φ j fuel) ih

theorem clausePhasePrefix_eq_ofFn {n m : Nat} (Φ : Fin m → Finset (Choice n)) (fuel : Nat) :
    clausePhasePrefix Φ fuel = (List.ofFn (fun j : Fin fuel =>
      if hj : j.val < m then clauseRowsPrefix Φ ⟨j.val,hj⟩ (2*n) else [])).flatten := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [clausePhasePrefix,List.ofFn_succ_last,List.flatten_append]
      simpa only [Fin.val_castSucc,Fin.val_last,List.flatten_cons,List.flatten_nil,List.append_nil]
        using congrArg (fun xs => xs ++ (if hj : fuel < m then
          clauseRowsPrefix Φ ⟨fuel,hj⟩ (2*n) else [])) ih

def clauseSourceRows {n m : Nat} (Φ : Fin m → Finset (Choice n)) : List Bool :=
  (List.ofFn (fun j : Fin m => (List.ofFn (fun x : Fin (n*2) =>
    reactionRows Φ (auxiliaryReaction (.clause j ((choiceOffset n).symm x))))).flatten)).flatten

theorem clausePhasePrefix_eq_sourceRows {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    clausePhasePrefix Φ m = clauseSourceRows Φ := by
  rw [clausePhasePrefix_eq_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  rw [dif_pos j.isLt,show 2*n = n*2 by omega,clauseRowsPrefix_eq_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext x
  simp only [clauseRowAt,dif_pos x.isLt]

def clauseSourcePrefix {n m : Nat} (Φ : Fin m → Finset (Choice n)) : List Bool :=
  coverageSourcePrefix Φ ++ clausePhasePrefix Φ m

def afterClauseRows {n m : Nat} (Φ : Fin m → Finset (Choice n)) : List Bool :=
  (List.ofFn (fun j : Fin 2 => reactionRows Φ (.inr
    ⟨3*n+m*(n*2)+j.val,by rw [step_card]; have hj := j.isLt; nlinarith⟩))).flatten

theorem sourceBits_eq_clause_prefix_append {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    sourceBits Φ = clauseSourcePrefix Φ ++ afterClauseRows Φ := by
  have hn : 3*n ≤ Fintype.card (Step n m)+1 := by rw [step_card]; omega
  have he : Fintype.card (Step n m)+1-3*n = m*(n*2)+2 := by
    rw [step_card]
    have hm : m*(n*2) = 2*n*m := by ring
    omega
  let f := fun j : Fin (Fintype.card (Step n m)+1-3*n) => reactionRows Φ (.inr
    ⟨3*n+j.val,by have hj := j.isLt; omega⟩)
  have hs := (List.ofFn_congr he f).trans
    (ofFn_sum_equiv (a := m*(n*2)) (b := 2) (fun j => f (Fin.cast he.symm j)))
  have hl : (List.ofFn (fun i : Fin (m*(n*2)) =>
      f (Fin.cast he.symm (finSumFinEquiv (.inl i))))).flatten = clauseSourceRows Φ := by
    rw [ofFn_prod_equiv]
    have hf : ∀ xs : List (List (List Bool)), xs.flatten.flatten = (xs.map List.flatten).flatten := by
      intro xs
      induction xs with
      | nil => rfl
      | cons x xs ih => simp only [List.flatten_cons,List.flatten_append,List.map_cons,ih]
    rw [hf,List.map_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext j
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext x
    apply congrArg (reactionRows Φ)
    apply congrArg Sum.inr
    apply Fin.ext
    simp [stepCode,stepOffset,stepEquiv,finSumFinEquiv]
    omega
  have hr : (List.ofFn (fun j : Fin 2 =>
      f (Fin.cast he.symm (finSumFinEquiv (.inr j))))).flatten = afterClauseRows Φ := by
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext j
    apply congrArg (reactionRows Φ)
    apply congrArg Sum.inr
    apply Fin.ext
    simp [finSumFinEquiv,Nat.add_assoc]
  rw [sourceBits_eq_coverage_prefix_append Φ]
  change coverageSourcePrefix Φ ++ (List.ofFn f).flatten = _
  rw [hs,List.flatten_append,hl,hr,← clausePhasePrefix_eq_sourceRows]
  simp only [clauseSourcePrefix,List.append_assoc]

end IrrRAFEnumeration.SATSource
