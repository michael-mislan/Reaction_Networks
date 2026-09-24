import proofs.IrrRAFEnumeration.SATLiteralPhase
import proofs.IrrRAFEnumeration.SATRunConstruction

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

theorem literalPrefix_eq_ofFn (edge fuel : Nat) :
    literalPrefix edge fuel =
      (List.ofFn (fun i : Fin fuel => literalRows edge (i.val+1) (edge-(i.val+1)))).flatten := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      rw [literalPrefix, List.ofFn_succ_last, List.flatten_append]
      simpa only [Fin.val_castSucc,Fin.val_last,List.flatten_cons,List.flatten_nil,
        List.append_nil] using congrArg (fun xs => xs ++ literalRows edge (fuel+1) (edge-(fuel+1))) ih

theorem literalRows_eq_reactionRows {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (i : Fin (Fintype.card (Choice n))) :
    literalRows (moleculeCount n m-1) (i.val+1) (moleculeCount n m-1-(i.val+1)) =
      reactionRows Φ (.inl i) := by
  obtain ⟨x,rfl⟩ := (inputCode n).surjective i
  have hpos : wirePosition (Wire.literal (m := m) x) = (inputCode n x).val+1 := rfl
  have htail : moleculeCount n m-1-((inputCode n x).val+1) =
      moleculeCount n m-((inputCode n x).val+1)-1 := by omega
  have hc := catalyst_row (m := m) (Sum.inl (inputCode n x))
  change spanRow (1+Fintype.card (Wire n m)+Fintype.card (Step n m)) 1
    (moleculeCount n m-(1+Fintype.card (Wire n m)+Fintype.card (Step n m))-1) = _ at hc
  have he : 1+Fintype.card (Wire n m)+Fintype.card (Step n m) = moleculeCount n m-1 := by
    dsimp [moleculeCount]; omega
  rw [he] at hc
  have hz : moleculeCount n m-(moleculeCount n m-1)-1 = 0 := by omega
  rw [hz] at hc
  unfold literalRows reactionRows
  rw [literal_input_row Φ x, htail, ← hpos, literal_output_row Φ x, hc]

/-- The complete literal-reaction phase emits exactly its original CRS
matrix rows, with explicit initialized phase registers and charged loop work. -/
theorem literalPhaseTM_source_correct {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (ys : List Bool) :
    literalPhaseTM.HoareTime
      (EmitPred (parkedInput (cnfBits Φ))
        (literalRegs (moleculeCount n m-1) (Fintype.card (Choice n)) 0) ys)
      (EmitPred (parkedInput (cnfBits Φ))
        (literalRegs (moleculeCount n m-1) (Fintype.card (Choice n)) (Fintype.card (Choice n)))
        (ys ++ (List.ofFn (fun i : Fin (Fintype.card (Choice n)) => reactionRows Φ (.inl i))).flatten))
      (Fintype.card (Choice n)*(14*(moleculeCount n m-1)+51)+2) := by
  have hf : Fintype.card (Choice n) ≤ moleculeCount n m-1 := by
    simp [Choice,moleculeCount,wire_card,step_card]
    omega
  have he : literalPrefix (moleculeCount n m-1) (Fintype.card (Choice n)) =
      (List.ofFn (fun i : Fin (Fintype.card (Choice n)) => reactionRows Φ (.inl i))).flatten := by
    rw [literalPrefix_eq_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    exact literalRows_eq_reactionRows Φ i
  have h := literalPhaseTM_correct (moleculeCount n m-1) (Fintype.card (Choice n)) hf
    (parkedInput (cnfBits Φ)) ys (parkedInput_parked _)
  rw [he] at h
  exact h

end IrrRAFEnumeration.SATSource
