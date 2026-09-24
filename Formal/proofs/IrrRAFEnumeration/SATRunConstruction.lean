import proofs.IrrRAFEnumeration.SATInputRows
import proofs.IrrRAFEnumeration.SATRowAssembly
import proofs.IrrRAFEnumeration.SATUniformCompiler

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource

def catalystRun {n m : Nat}
    (r : Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m))) : List Bool :=
  spanRow (1+Fintype.card (Wire n m)+(catalystIndex r).val) 1
    (moleculeCount n m-(1+Fintype.card (Wire n m)+(catalystIndex r).val)-1)

theorem catalystRun_correct {n m : Nat}
    (r : Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m))) :
    catalystRun (m := m) r = List.ofFn (fun x : Fin (moleculeCount n m) =>
      decide ((moleculeCode _ _).symm x = Molecule.marker (catalystIndex r))) := catalyst_row r

def runReactionRows {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m)) → List Bool
  | .inl i =>
      let x := (inputCode n).symm i
      spanRow 0 1 (moleculeCount n m-1) ++
        spanRow (wirePosition (Wire.literal (m := m) x)) 1
          (moleculeCount n m-wirePosition (Wire.literal (m := m) x)-1) ++
        catalystRun (m := m) (.inl i)
  | .inr j =>
      if hj : j.val < Fintype.card (Step n m) then
        let s := (stepCode n m).symm ⟨j.val,hj⟩
        auxiliaryInputRow s ++ auxiliaryOutputRow Φ s ++ catalystRun (m := m) (.inr j)
      else spanRow (3*n+m+1) 1 (moleculeCount n m-(3*n+m+1)-1) ++
        blockLastRow 1 (Fintype.card (Wire n m)) (Fintype.card (Step n m)) ++
        catalystRun (m := m) (.inr j)

theorem runReactionRows_correct {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (r : Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m))) :
    runReactionRows Φ r = reactionRows Φ r := by
  cases r with
  | inl i =>
      obtain ⟨x,rfl⟩ := (inputCode n).surjective i
      simp only [runReactionRows, Equiv.symm_apply_apply]
      rw [literal_input_row Φ x, literal_output_row Φ x, catalystRun_correct]
      rfl
  | inr j =>
      by_cases hj : j.val < Fintype.card (Step n m)
      · let s := (stepCode n m).symm ⟨j.val,hj⟩
        have hs : auxiliaryReaction s = (Sum.inr j :
            Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m))) := by
          simp only [auxiliaryReaction, s, Equiv.apply_symm_apply]
          all_goals rfl
        simp only [runReactionRows, dif_pos hj]
        change auxiliaryInputRow s ++ auxiliaryOutputRow Φ s ++
          catalystRun (m := m) (.inr j) = _
        rw [auxiliaryInputRow_correct Φ s, auxiliaryOutputRow_correct Φ s,
          catalystRun_correct, hs]
        rfl
      · have he : j = Fin.last (Fintype.card (Step n m)) := by
          apply Fin.ext
          have hlt := j.isLt
          simp only [Fin.val_last]
          omega
        subst j
        simp only [runReactionRows, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
        change spanRow (3*n+m+1) 1 (moleculeCount n m-(3*n+m+1)-1) ++
          blockLastRow 1 (Fintype.card (Wire n m)) (Fintype.card (Step n m)) ++
          catalystRun (m := m) (reset (n := Fintype.card (Choice n))) = _
        rw [reset_input_row Φ, reset_output_row Φ, catalystRun_correct]
        rfl

def runSourceBody {n m : Nat} (Φ : Fin m → Finset (Choice n)) : List Bool :=
  spanRow 0 1 (moleculeCount n m-1) ++
    (List.ofFn (fun r : Fin (reactionCount n m) =>
      runReactionRows Φ ((reactionCode _ _).symm r))).flatten

theorem runSourceBody_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    runSourceBody Φ = sourceBody Φ := by
  rw [runSourceBody, sourceBody_eq_rows]
  congr 1
  · have h := spanRow_singleton (Molecule.food :
        Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m)))
    simpa [moleculeCode_food, moleculeCount, crs] using h
  · apply congrArg List.flatten
    apply congrArg List.ofFn
    funext r
    exact runReactionRows_correct Φ _

def runSourceBits {n m : Nat} (Φ : Fin m → Finset (Choice n)) : List Bool :=
  List.replicate (moleculeCount n m) true ++ [false] ++
    List.replicate (reactionCount n m) true ++ [false] ++ runSourceBody Φ

theorem runSourceBits_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    runSourceBits Φ = sourceBits Φ := by
  rw [runSourceBits, runSourceBody_correct]
  rfl

/-- Uniform run-based source construction; the timed phase-machine assembly
remains separate from this exact executable bitstring equality. -/
def runCompiler (bits : List Bool) : List Bool :=
  let p := decodeHeader bits
  runSourceBits (decodeClauses p.1 p.2.1 p.2.2)

theorem runCompiler_correct (bits : List Bool) : runCompiler bits = compileCNF bits :=
  runSourceBits_correct _

end IrrRAFEnumeration.SATSource
