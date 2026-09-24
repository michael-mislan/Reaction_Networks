import proofs.IrrRAFEnumeration.SATLiteralBody

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def literalPrefix (edge : Nat) : Nat → List Bool
  | 0 => []
  | i+1 => literalPrefix edge i ++ literalRows edge (i+1) (edge-(i+1))

def literalRegs (edge fuel i : Nat) : Fin 6 → Tape :=
  ![regTape 0,regTape 1,regTape edge,regTape (i+1),regTape (edge-(i+1)),regTape fuel]

def literalPhaseTM : TM 6 := forRegTM (literalBodyTM 0 1 2 3 4) 5

theorem literalPhaseTM_correct (edge fuel : Nat) (hf : fuel ≤ edge)
    (inp : Tape) (ys : List Bool) (hp : Parked inp) :
    literalPhaseTM.HoareTime (EmitPred inp (literalRegs edge fuel 0) ys)
      (EmitPred inp (literalRegs edge fuel fuel) (ys ++ literalPrefix edge fuel))
      (fuel*(14*edge+51)+2) := by
  have hw : ∀ i j, Parked (literalRegs edge fuel i j) := by
    intro i j
    fin_cases j <;> exact parked_regTape _
  have hbody : ∀ i, i < fuel → (literalBodyTM (0 : Fin 6) 1 2 3 4).HoareTime
      (EmitPred inp (Function.update (literalRegs edge fuel i) 5 ⟨i+2,regCells fuel⟩)
        (ys ++ literalPrefix edge i))
      (EmitPred inp (Function.update (literalRegs edge fuel (i+1)) 5 ⟨i+2,regCells fuel⟩)
        (ys ++ literalPrefix edge (i+1))) (14*edge+48) := by
    intro i hi
    let W := Function.update (literalRegs edge fuel i) 5 ⟨i+2,regCells fuel⟩
    have hw' : ∀ j, Parked (W j) := by
      intro j
      by_cases hj : j = 5
      · subst j
        exact parked_regCells (by omega)
      · simpa only [W, Function.update_of_ne hj] using hw i j
    have h := literalBodyTM_correct (0 : Fin 6) 1 2 3 4 (by decide)
      edge (i+1) (edge-(i+1)) inp W (ys ++ literalPrefix edge i) hp hw'
      (by simp [W,literalRegs]) (by simp [W,literalRegs]) (by simp [W,literalRegs])
      (by simp [W,literalRegs]) (by simp [W,literalRegs])
    have hwork : Function.update (Function.update W 3 (regTape (i+1+1)))
        4 (regTape (edge-(i+1)-1)) =
        Function.update (literalRegs edge fuel (i+1)) 5 ⟨i+2,regCells fuel⟩ := by
      have hs : edge-(i+1)-1 = edge-(i+1+1) := by omega
      funext j
      fin_cases j <;> simp [W,literalRegs,hs]
    rw [hwork] at h
    have htime : 8*edge+6*(i+1)+6*(edge-(i+1))+48 = 14*edge+48 := by omega
    rw [htime] at h
    simpa only [literalPrefix,List.append_assoc] using h
  have h := forRegTM_hoareTime (literalBodyTM (0 : Fin 6) 1 2 3 4) 5 fuel inp
    (literalRegs edge fuel) (fun i => ys ++ literalPrefix edge i) (14*edge+48) hp
    (fun _ => rfl) (fun i j _ => hw i j) hbody
  have htime : fuel*((14*edge+48)+2)+(fuel+2) = fuel*(14*edge+51)+2 := by ring
  simpa only [literalPhaseTM,literalPrefix,List.append_nil,htime] using h

end IrrRAFEnumeration.SATSource
