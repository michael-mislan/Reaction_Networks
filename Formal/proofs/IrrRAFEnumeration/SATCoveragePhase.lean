import proofs.IrrRAFEnumeration.SATCoveragePair

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def coverageWork (n m W Q M R i : Nat) (stream : Tape) : Fin 13 → Tape :=
  ![regTape (2*i+1),regTape (M-(2*i+1)-1),regTape (2*n+i+1),
    regTape (2*n+m+i),regTape (Q-n-2*i),regTape (W+n+2*i+2),
    regTape n,regTape m,regTape W,regTape Q,regTape M,regTape R,stream]

def coveragePrefix (n m W Q M : Nat) : Nat → List Bool
  | 0 => []
  | i+1 => coveragePrefix n m W Q M i ++
      coveragePairPattern (2*i+1) (M-(2*i+1)-1) (2*n+i+1)
        (2*n+m+i) (Q-n-2*i) (W+n+2*i+2)

def coveragePhaseTM : TM 13 := forRegTM coveragePairTM 6

theorem coveragePhaseTM_correct (n m W Q M R : Nat) (stream inp : Tape) (ys : List Bool)
    (hs : Parked stream) (hp : Parked inp) (hW : W = 3*n+m+1)
    (hQ : 3*n+1 ≤ Q) (hM : M = W+Q+2) :
    coveragePhaseTM.HoareTime (EmitPred inp (coverageWork n m W Q M R 0 stream) ys)
      (EmitPred inp (coverageWork n m W Q M R n stream) (ys ++ coveragePrefix n m W Q M n))
      (n*(400*(M+1)+3)+2) := by
  have hw : ∀ i j, Parked (coverageWork n m W Q M R i stream j) := by
    intro i j
    fin_cases j <;> first | exact parked_regTape _ | exact hs
  have hbody : ∀ i, i < n → coveragePairTM.HoareTime
      (EmitPred inp (Function.update (coverageWork n m W Q M R i stream) 6 ⟨i+2,regCells n⟩)
        (ys ++ coveragePrefix n m W Q M i))
      (EmitPred inp (Function.update (coverageWork n m W Q M R (i+1) stream) 6 ⟨i+2,regCells n⟩)
        (ys ++ coveragePrefix n m W Q M (i+1))) (400*(M+1)) := by
    intro i hi
    let V := Function.update (coverageWork n m W Q M R i stream) 6 ⟨i+2,regCells n⟩
    have hv : ∀ j, Parked (V j) := by
      intro j
      by_cases he : j = 6
      · subst j
        exact parked_regCells (by omega)
      · simpa only [V,Function.update_of_ne he] using hw i j
    have h := coveragePairTM_correct (2*i+1) (M-(2*i+1)-1) (2*n+i+1)
      (2*n+m+i) (Q-n-2*i) (W+n+2*i+2) M inp V
      (ys ++ coveragePrefix n m W Q M i) hp hv
      (by simp [V,coverageWork]) (by simp [V,coverageWork]) (by simp [V,coverageWork])
      (by simp [V,coverageWork]) (by simp [V,coverageWork]) (by simp [V,coverageWork]) (by omega)
    have he : coveragePairAdvance V (2*i+1) (M-(2*i+1)-1) (2*n+i+1)
        (2*n+m+i) (Q-n-2*i) (W+n+2*i+2) =
        Function.update (coverageWork n m W Q M R (i+1) stream) 6 ⟨i+2,regCells n⟩ := by
      have h0 : 2*i+1+2 = 2*(i+1)+1 := by omega
      have h1 : M-(2*i+1)-1-2 = M-(2*(i+1)+1)-1 := by omega
      have h4 : Q-n-2*i-2 = Q-n-2*(i+1) := by omega
      funext j
      fin_cases j <;> simp [coveragePairAdvance,V,coverageWork,h0,h1,h4,Nat.add_assoc]
      congr 1
    rw [he] at h
    simpa only [coveragePrefix,List.append_assoc] using h
  have h := forRegTM_hoareTime coveragePairTM (6 : Fin 13) n inp
    (fun i => coverageWork n m W Q M R i stream) (fun i => ys ++ coveragePrefix n m W Q M i)
    (400*(M+1)) hp (fun _ => rfl) (fun i j _ => hw i j) hbody
  have ht : n*(400*(M+1)+2)+(n+2) = n*(400*(M+1)+3)+2 := by ring
  simpa only [coveragePhaseTM,coveragePrefix,List.append_nil,ht] using h

end IrrRAFEnumeration.SATSource
