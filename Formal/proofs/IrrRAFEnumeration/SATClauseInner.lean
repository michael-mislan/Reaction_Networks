import proofs.IrrRAFEnumeration.SATClauseDock

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

/-- Tape 7 is the possibly moving outer fuel; tape 11 is inner fuel.
The old saved reaction count has already had its final consumer. -/
def clauseWork {n m : Nat} (Φ : Fin m → Finset (Choice n)) (j i : Nat) (outer : Tape) : Fin 13 → Tape :=
  ![regTape (i+1),regTape (moleculeCount n m-(i+1)-1),regTape (3*n+j+1),
    regTape (3*n+m+2*n*j+i-j),regTape (Fintype.card (Step n m)-3*n-2*n*j-i),
    regTape (Fintype.card (Wire n m)+3*n+2*n*j+i+2),
    regTape n,outer,regTape (Fintype.card (Wire n m)),regTape (Fintype.card (Step n m)),
    regTape (moleculeCount n m),regTape (2*n),cnfStreamCursor Φ (2*n*j+i)]

def clauseRowAt {n m : Nat} (Φ : Fin m → Finset (Choice n)) (j : Fin m) (i : Nat) : List Bool :=
  if hi : i < n*2 then
    reactionRows Φ (auxiliaryReaction (.clause j ((choiceOffset n).symm ⟨i,hi⟩)))
  else []

def clauseRowsPrefix {n m : Nat} (Φ : Fin m → Finset (Choice n)) (j : Fin m) : Nat → List Bool
  | 0 => []
  | i+1 => clauseRowsPrefix Φ j i ++ clauseRowAt Φ j i

def clauseInnerTM : TM 13 := forRegTM clauseBodyTM 11

theorem clauseInnerTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (j : Fin m) (outer : Tape) (ho : Parked outer) (ys : List Bool) :
    clauseInnerTM.HoareTime
      (EmitPred (parkedInput (cnfBits Φ)) (clauseWork Φ j.val 0 outer) ys)
      (EmitPred (parkedInput (cnfBits Φ)) (clauseWork Φ j.val (2*n) outer)
        (ys ++ clauseRowsPrefix Φ j (2*n)))
      (2*n*(100*(moleculeCount n m+1)+3)+2) := by
  have hp := parkedInput_parked (cnfBits Φ)
  have hw : ∀ i k, Parked (clauseWork Φ j.val i outer k) := by
    intro i k
    fin_cases k <;> first | exact parked_regTape _ | exact ho | exact cnfStreamCursor_parked Φ _
  have hbody : ∀ i, i < 2*n → clauseBodyTM.HoareTime
      (EmitPred (parkedInput (cnfBits Φ))
        (Function.update (clauseWork Φ j.val i outer) 11 ⟨i+2,regCells (2*n)⟩)
        (ys ++ clauseRowsPrefix Φ j i))
      (EmitPred (parkedInput (cnfBits Φ))
        (Function.update (clauseWork Φ j.val (i+1) outer) 11 ⟨i+2,regCells (2*n)⟩)
        (ys ++ clauseRowsPrefix Φ j (i+1))) (100*(moleculeCount n m+1)) := by
    intro i hi
    let x : Choice n := (choiceOffset n).symm ⟨i,by omega⟩
    have hx : (choiceOffset n x).val = i := by simp [x]
    have hpos : (finProdFinEquiv (j,choiceOffset n x)).val = 2*n*j.val+i := by
      simp [finProdFinEquiv,hx]
      ring
    have hj := j.isLt
    have hmul := Nat.mul_le_mul_left (2*n) hj
    have hlimit : 2*n*j.val+i < 2*n*m := by nlinarith
    let V := Function.update (clauseWork Φ j.val i outer) (11 : Fin 13) ⟨i+2,regCells (2*n)⟩
    have hv : ∀ k, Parked (V k) := by
      intro k
      by_cases hk : k = 11
      · subst k
        exact parked_regCells (by omega)
      · simpa only [V,Function.update_of_ne hk] using hw i k
    have hread : (V 12).read = Γ.ofBool (decide (x ∈ Φ j)) := by
      have hr := cnfStreamCursor_read Φ j x
      rw [hpos] at hr
      exact hr
    have h := clauseBodyTM_correct (i+1) (moleculeCount n m-(i+1)-1)
      (3*n+j.val+1) (3*n+m+2*n*j.val+i-j.val)
      (Fintype.card (Step n m)-3*n-2*n*j.val-i)
      (Fintype.card (Wire n m)+3*n+2*n*j.val+i+2)
      (moleculeCount n m) (decide (x ∈ Φ j)) (parkedInput (cnfBits Φ)) V
      (ys ++ clauseRowsPrefix Φ j i) hp hv
      (by simp [V,clauseWork]) (by simp [V,clauseWork]) (by simp [V,clauseWork])
      (by simp [V,clauseWork]) (by simp [V,clauseWork]) (by simp [V,clauseWork]) hread
      (by simp only [moleculeCount,wire_card,step_card]; omega)
    have he : clauseAdvance V (i+1) (moleculeCount n m-(i+1)-1)
        (3*n+m+2*n*j.val+i-j.val) (Fintype.card (Step n m)-3*n-2*n*j.val-i)
        (Fintype.card (Wire n m)+3*n+2*n*j.val+i+2) =
        Function.update (clauseWork Φ j.val (i+1) outer) 11 ⟨i+2,regCells (2*n)⟩ := by
      have hg : 3*n+m+2*n*j.val+i-j.val+1 = 3*n+m+2*n*j.val+(i+1)-j.val := by omega
      have hs : moleculeCount n m-(i+1)-1-1 = moleculeCount n m-(i+1+1)-1 := by omega
      have hl : Fintype.card (Step n m)-3*n-2*n*j.val-i-1 =
          Fintype.card (Step n m)-3*n-2*n*j.val-(i+1) := by omega
      funext k
      fin_cases k <;> simp [clauseAdvance,V,clauseWork,cnfStreamCursor_next,hs,hl,Nat.add_assoc]
      exact congrArg regTape (by simpa only [Nat.add_assoc] using hg)
    have hr := clausePattern_eq_reactionRows Φ j x
    rw [hx,hpos] at hr
    have hgap : 3*n+m+(2*n*j.val+i)-j.val = 3*n+m+2*n*j.val+i-j.val := by omega
    have htail : Fintype.card (Step n m)-3*n-(2*n*j.val+i) =
        Fintype.card (Step n m)-3*n-2*n*j.val-i := by omega
    have hcat : Fintype.card (Wire n m)+3*n+(2*n*j.val+i)+2 =
        Fintype.card (Wire n m)+3*n+2*n*j.val+i+2 := by omega
    rw [hgap,htail,hcat] at hr
    rw [he,hr] at h
    simpa only [clauseRowsPrefix,clauseRowAt,dif_pos (show i < n*2 by omega),List.append_assoc]
      using h
  have h := forRegTM_hoareTime clauseBodyTM (11 : Fin 13) (2*n) (parkedInput (cnfBits Φ))
    (fun i => clauseWork Φ j.val i outer) (fun i => ys ++ clauseRowsPrefix Φ j i)
    (100*(moleculeCount n m+1)) hp (fun _ => rfl) (fun i k _ => hw i k) hbody
  have ht : 2*n*(100*(moleculeCount n m+1)+2)+(2*n+2) =
      2*n*(100*(moleculeCount n m+1)+3)+2 := by ring
  simpa only [clauseInnerTM,clauseRowsPrefix,List.append_nil,ht] using h

end IrrRAFEnumeration.SATSource
