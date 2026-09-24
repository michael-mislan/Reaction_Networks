import proofs.IrrRAFEnumeration.SATBoundaryRows

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource

theorem spanRow_two (a c : Nat) : spanRow a 2 c = markedRow a 0 c true := by
  simp [spanRow, markedRow, List.replicate_succ, List.append_assoc]

def auxiliaryInputRow {n m : Nat} : Step n m → List Bool
  | .conflict i => spanRow (2*i.val+1) 2 (moleculeCount n m-(2*i.val+1)-2)
  | .coverage x => spanRow ((choiceOffset n x).val+1) 1
      (moleculeCount n m-((choiceOffset n x).val+1)-1)
  | .clause _ x => spanRow ((choiceOffset n x).val+1) 1
      (moleculeCount n m-((choiceOffset n x).val+1)-1)
  | .finish => spanRow (2*n+1) (n+m) (moleculeCount n m-(3*n+m+1))

theorem auxiliaryInputRow_correct {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (s : Step n m) :
    auxiliaryInputRow s = moleculeRow ((crs (rules Φ)).inputs (auxiliaryReaction s)) := by
  cases s with
  | conflict i =>
      have h0 : (moleculeCode _ _ (signalMolecule (Wire.literal (m := m) (i,false)))).val =
          2*i.val+1 := by
        rw [signalMolecule_position]
        simp [wirePosition, choiceOffset, bitCode, finProdFinEquiv]
      have h1 : (moleculeCode _ _ (signalMolecule (Wire.literal (m := m) (i,true)))).val =
          2*i.val+2 := by
        rw [signalMolecule_position]
        simp [wirePosition, choiceOffset, bitCode, finProdFinEquiv]
        omega
      have h := markedRow_optional
        (signalMolecule (Wire.literal (m := m) (i,false)))
        (signalMolecule (Wire.literal (m := m) (i,true))) true (by rw [h0,h1]; omega)
      rw [h0,h1] at h
      have hgap : 2*i.val+2-(2*i.val+1)-1 = 0 := by omega
      rw [hgap, ← spanRow_two] at h
      have htail : moleculeCount n m-(2*i.val+2)-1 = moleculeCount n m-(2*i.val+1)-2 := by omega
      change spanRow (2*i.val+1) 2 (moleculeCount n m-(2*i.val+2)-1) = _ at h
      rw [htail] at h
      simpa [auxiliaryInputRow, crs, rules, auxiliaryReaction, needs, signalMolecule,
        Finset.pair_comm] using h
  | coverage x =>
      have h := spanRow_singleton (signalMolecule (Wire.literal (m := m) x))
      rw [signalMolecule_position] at h
      simpa [auxiliaryInputRow, wirePosition, moleculeCount, crs, rules, auxiliaryReaction,
        needs, signalMolecule] using h
  | clause j x =>
      have h := spanRow_singleton (signalMolecule (Wire.literal (m := m) x))
      rw [signalMolecule_position] at h
      simpa [auxiliaryInputRow, wirePosition, moleculeCount, crs, rules, auxiliaryReaction,
        needs, signalMolecule] using h
  | finish => exact finish_input_row Φ

end IrrRAFEnumeration.SATSource
