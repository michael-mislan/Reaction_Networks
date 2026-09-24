import proofs.IrrRAFEnumeration.SATRawRectangleBody
import proofs.IrrRAFEnumeration.SATRawIncidenceDock
import proofs.IrrRAFEnumeration.SATRowAssembly

namespace IrrRAFEnumeration.SATSource
open Complexity SAT SATCompletion

theorem rectangleRowPrefix_eq_ofFn (φ : CNF) (j N : Nat) :
    rectangleRowPrefix φ j N = (List.ofFn (fun v : Fin N =>
      [incidenceCNFMatch false v.val φ j,incidenceCNFMatch true v.val φ j])).flatten := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [rectangleRowPrefix,List.ofFn_succ_last,List.flatten_append]
    simpa only [Fin.val_castSucc,Fin.val_last,List.flatten_cons,List.flatten_nil,List.append_nil]
      using congrArg (fun xs => xs ++
        [incidenceCNFMatch false N φ j,incidenceCNFMatch true N φ j]) ih

theorem rectangleRowsPrefix_eq_ofFn (φ : CNF) (N M : Nat) :
    rectangleRowsPrefix φ N M =
      (List.ofFn (fun j : Fin M => rectangleRowPrefix φ j.val N)).flatten := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [rectangleRowsPrefix,List.ofFn_succ_last,List.flatten_append]
    simpa only [Fin.val_castSucc,Fin.val_last,List.flatten_cons,List.flatten_nil,List.append_nil]
      using congrArg (fun xs => xs ++ rectangleRowPrefix φ M N) ih

/-- The counted loops emit exactly the existing rectangular incidence body,
including duplicate-literal collapse and empty rows. -/
theorem rectangleRowsPrefix_eq_cnfBody (φ : CNF) (N : Nat) :
    rectangleRowsPrefix φ N φ.length = cnfBody (libraryRect φ N) := by
  rw [rectangleRowsPrefix_eq_ofFn,cnfBody,ofFn_prod_equiv]
  simp only [Equiv.symm_apply_apply]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  rw [rectangleRowPrefix_eq_ofFn,ofFn_prod_equiv]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  have he : ∀ b : Fin 2, (choiceOffset N).symm (finProdFinEquiv (v,b)) =
      (v,bitCode.symm b) := by
    intro b
    apply (choiceOffset N).injective
    simp [choiceOffset]
  simp only [he]
  rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_zero]
  change [incidenceCNFMatch false v.val φ j.val,incidenceCNFMatch true v.val φ j.val] =
    [decide ((v,false) ∈ libraryRect φ N j),decide ((v,true) ∈ libraryRect φ N j)]
  rw [incidenceCNFMatch_libraryRect φ N j (v,false),
    incidenceCNFMatch_libraryRect φ N j (v,true)]

end IrrRAFEnumeration.SATSource
