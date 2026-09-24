import proofs.IrrRAFEnumeration.SATConflictBody

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def conflictWork (n m W Q M R i : Nat) (stream : Tape) : Fin 13 → Tape :=
  ![regTape (2*i+1),regTape (M-(2*i+1)-2),regTape i,regTape (Q-i),
    regTape (W+i+2),regTape (Q-i-1),regTape n,regTape m,regTape W,
    regTape Q,regTape M,regTape R,stream]

def conflictPrefix (W Q M : Nat) : Nat → List Bool
  | 0 => []
  | i+1 => conflictPrefix W Q M i ++
      conflictPattern W (2*i+1) (M-(2*i+1)-2) i (Q-i) (W+i+2) (Q-i-1)

def conflictPhaseTM : TM 13 := forRegTM conflictBodyTM 6

/-- Complete conflict loop with a binary stream frame and all source counts
preserved. Positions drift; the fuel register is restored by the loop. -/
theorem conflictPhaseTM_correct (n m W Q M R : Nat) (stream inp : Tape) (ys : List Bool)
    (hs : Parked stream) (hp : Parked inp) (hn : n ≤ Q) (hM : M = W+Q+2)
    (hspace : 2*n+3 ≤ M) :
    conflictPhaseTM.HoareTime (EmitPred inp (conflictWork n m W Q M R 0 stream) ys)
      (EmitPred inp (conflictWork n m W Q M R n stream) (ys ++ conflictPrefix W Q M n))
      (n*(100*(M+1)+3)+2) := by
  have hw : ∀ i j, Parked (conflictWork n m W Q M R i stream j) := by
    intro i j
    fin_cases j <;> first | exact parked_regTape _ | exact hs
  have hbody : ∀ i, i < n → conflictBodyTM.HoareTime
      (EmitPred inp (Function.update (conflictWork n m W Q M R i stream) 6 ⟨i+2,regCells n⟩)
        (ys ++ conflictPrefix W Q M i))
      (EmitPred inp (Function.update (conflictWork n m W Q M R (i+1) stream) 6 ⟨i+2,regCells n⟩)
        (ys ++ conflictPrefix W Q M (i+1))) (100*(M+1)) := by
    intro i hi
    let V := Function.update (conflictWork n m W Q M R i stream) 6 ⟨i+2,regCells n⟩
    have hv : ∀ j, Parked (V j) := by
      intro j
      by_cases he : j = 6
      · subst j
        exact parked_regCells (by omega)
      · simpa only [V,Function.update_of_ne he] using hw i j
    have h := conflictBodyTM_correct W (2*i+1) (M-(2*i+1)-2) i (Q-i)
      (W+i+2) (Q-i-1) M inp V (ys ++ conflictPrefix W Q M i) hp hv
      (by simp [V,conflictWork]) (by simp [V,conflictWork]) (by simp [V,conflictWork])
      (by simp [V,conflictWork]) (by simp [V,conflictWork]) (by simp [V,conflictWork])
      (by simp [V,conflictWork]) (by omega)
    have he : conflictAdvance V (2*i+1) (M-(2*i+1)-2) i (Q-i) (W+i+2) (Q-i-1) =
        Function.update (conflictWork n m W Q M R (i+1) stream) 6 ⟨i+2,regCells n⟩ := by
      have h0 : 2*i+1+2 = 2*(i+1)+1 := by omega
      have h1 : M-(2*i+1)-2-2 = M-(2*(i+1)+1)-2 := by omega
      have h3 : Q-i-1 = Q-(i+1) := by omega
      have h4 : W+i+2+1 = W+(i+1)+2 := by omega
      funext j
      fin_cases j <;> simp [conflictAdvance,V,conflictWork,h0,h1,h3,h4]
    rw [he] at h
    simpa only [conflictPrefix,List.append_assoc] using h
  have h := forRegTM_hoareTime conflictBodyTM (6 : Fin 13) n inp
    (fun i => conflictWork n m W Q M R i stream) (fun i => ys ++ conflictPrefix W Q M i)
    (100*(M+1)) hp (fun _ => rfl) (fun i j _ => hw i j) hbody
  have ht : n*(100*(M+1)+2)+(n+2) = n*(100*(M+1)+3)+2 := by ring
  simpa only [conflictPhaseTM,conflictPrefix,List.append_nil,ht] using h

end IrrRAFEnumeration.SATSource
