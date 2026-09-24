import proofs.IrrRAFEnumeration.CompletionSupportFamily
import proofs.IrrRAFEnumeration.PositiveBaseQuery

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PositiveCompletionCNF

def initialFoodClauses {d r : Nat} (Q : CRS (Fin d) (Fin r)) : SAT.CNF :=
  each d (fun x => if x ∈ Q.food then [] else
    [negative [rowVar r ⟨0,by omega⟩ x]])

/-- Clause order chosen by the actual family emitters. -/
def assembledBase {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] : SAT.CNF :=
  [positive ((List.finRange r).map selectVar)] ++ initialFoodClauses Q ++
  (List.finRange d).flatMap (firingLayerClauses Q) ++
  (List.finRange d).flatMap (supportLayerClauses Q) ++
  (List.finRange r).flatMap (reactantClauses Q) ++
  (List.finRange r).map (catalystClause C)

theorem assembledBase_eval_iff {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (a : SAT.Assignment) :
    SAT.CNF.eval a (assembledBase Q C) = true ↔
      SAT.CNF.eval a (baseFormula Q C) = true := by
  have hflat {α : Type} (xs : List α) (f : α → SAT.CNF) :
      SAT.CNF.eval a (xs.flatMap f) = true ↔
        ∀ x ∈ xs, SAT.CNF.eval a (f x) = true := by
    simp [SAT.CNF.eval,List.all_eq_true]
  have hnil : SAT.CNF.eval a [] = true := rfl
  simp only [assembledBase,baseFormula,formula,initialFoodClauses,
    firingLayerClauses,firingClauses,supportLayerClauses,supportClause,
    reactantClauses,catalystClause,eval_append,hflat,eval_map,eval_each,
    eval_singleton,List.mem_finRange,forall_const,Finset.mem_univ,ite_true,
    List.map_nil,hnil,and_true,forall_and,forall_true_iff,and_assoc]


/-- The assembled byte order is suitable for every dynamic completion query. -/
theorem assembledQuery_satisfiable_iff {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) :
    (assembledBase Q C ++ outputBlockers G ++ containerExclusions U).Satisfiable ↔
      PositiveCompletion.Available (IsRAF Q C) G.toFinset U := by
  rw [← baseQuery_satisfiable_iff Q C G U]
  apply exists_congr
  intro a
  simp only [baseQuery,eval_append,assembledBase_eval_iff]

theorem original_food_cell {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (x : Fin d) :
    (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))).cells
      (d+r+3+x.val) = Γ.ofBool (decide (x ∈ Q.food)) := by
  have h := original_incidence_cell Q C (.inl x)
  simpa [slotCode,incidence,finSumFinEquiv] using h

theorem original_food_maskClauses {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] :
    maskClauses (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
      (d+r+3) r d = initialFoodClauses Q := by
  have h := maskClauses_eq_each
    (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
    (d+r+3) r d (fun x => decide (x ∈ Q.food)) (original_food_cell Q C)
  simpa [initialFoodClauses,negative,rowVar] using h

end IrrRAFEnumeration.CompletionQuery
