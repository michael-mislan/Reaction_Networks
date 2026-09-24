import proofs.IrrRAFEnumeration.SATClauseInner

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

def clauseBoundaryTM : TM 13 := seqTM (clearRegTM 0) (seqTM (incRegTM 0) (seqTM (copyIntoTM 10 1) (seqTM (decRegTM 1) (seqTM (decRegTM 1) (seqTM (incRegTM 2) (decRegTM 3))))))

theorem clauseBoundaryTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (j : Nat) (hj : j < m) (outer : Tape) (ho : Parked outer) (ys : List Bool) :
    clauseBoundaryTM.HoareTime
      (EmitPred (parkedInput (cnfBits Φ)) (clauseWork Φ j (2*n) outer) ys)
      (EmitPred (parkedInput (cnfBits Φ)) (clauseWork Φ (j+1) 0 outer) ys)
      (4096*(n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+
        moleculeCount n m+reactionCount n m+1)^2) := by
  let M := moleculeCount n m
  let inp := parkedInput (cnfBits Φ)
  have hp := parkedInput_parked (cnfBits Φ)
  let v0 := clauseWork Φ j (2*n) outer
  have hp0 : ∀ i, Parked (v0 i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact ho | exact cnfStreamCursor_parked Φ _
  let v1 := Function.update v0 (0 : Fin 13) (regTape (0))
  have hp1 : ∀ i, Parked (v1 i) := updateReg_parked v0 hp0 _ _
  have h1 := clearRegTM_hoareTime (0 : Fin 13) (2*n+1)
    inp v0 ys hp (fun i _ => hp0 i) rfl
  let v2 := Function.update v1 (0 : Fin 13) (regTape ((0)+1))
  have hp2 : ∀ i, Parked (v2 i) := updateReg_parked v1 hp1 _ _
  have h2 := incRegTM_hoareTime (0 : Fin 13) (0)
    inp v1 ys hp (fun i _ => hp1 i) rfl
  let v3 := Function.update v2 (1 : Fin 13) (regTape (M))
  have hp3 : ∀ i, Parked (v3 i) := updateReg_parked v2 hp2 _ _
  have h3 := copyIntoTM_hoareTime (10 : Fin 13) 1 (by decide) (M) (M-(2*n+1)-1)
    inp v2 ys hp (fun i _ => hp2 i) rfl rfl
  let v4 := Function.update v3 (1 : Fin 13) (regTape ((M)-1))
  have hp4 : ∀ i, Parked (v4 i) := updateReg_parked v3 hp3 _ _
  have h4 := decRegTM_hoareTime (1 : Fin 13) (M)
    inp v3 ys hp (fun i _ => hp3 i) rfl
  let v5 := Function.update v4 (1 : Fin 13) (regTape (((M)-1)-1))
  have hp5 : ∀ i, Parked (v5 i) := updateReg_parked v4 hp4 _ _
  have h5 := decRegTM_hoareTime (1 : Fin 13) ((M)-1)
    inp v4 ys hp (fun i _ => hp4 i) rfl
  let v6 := Function.update v5 (2 : Fin 13) (regTape ((3*n+j+1)+1))
  have hp6 : ∀ i, Parked (v6 i) := updateReg_parked v5 hp5 _ _
  have h6 := incRegTM_hoareTime (2 : Fin 13) (3*n+j+1)
    inp v5 ys hp (fun i _ => hp5 i) rfl
  let v7 := Function.update v6 (3 : Fin 13) (regTape ((3*n+m+2*n*j+2*n-j)-1))
  have hp7 : ∀ i, Parked (v7 i) := updateReg_parked v6 hp6 _ _
  have h7 := decRegTM_hoareTime (3 : Fin 13) (3*n+m+2*n*j+2*n-j)
    inp v6 ys hp (fun i _ => hp6 i) rfl
  have h6end := seqTM_hoareTime _ _ h6 (emitPred_transition hp hp6 ys) h7
  have h5end := seqTM_hoareTime _ _ h5 (emitPred_transition hp hp5 ys) h6end
  have h4end := seqTM_hoareTime _ _ h4 (emitPred_transition hp hp4 ys) h5end
  have h3end := seqTM_hoareTime _ _ h3 (emitPred_transition hp hp3 ys) h4end
  have h2end := seqTM_hoareTime _ _ h2 (emitPred_transition hp hp2 ys) h3end
  have h1end := seqTM_hoareTime _ _ h1 (emitPred_transition hp hp1 ys) h2end
  have he : v7 = clauseWork Φ (j+1) 0 outer := by
    funext i
    fin_cases i <;> simp [v7,v6,v5,v4,v3,v2,v1,v0,clauseWork,M,
      Nat.mul_add,Nat.sub_sub,Nat.add_assoc]
  change clauseBoundaryTM.HoareTime _ (EmitPred inp v7 ys) _ at h1end
  rw [he] at h1end
  apply h1end.mono_bound
  let B := n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+M+reactionCount n m+1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hn : n ≤ B := by dsimp [B]; omega
  have hm : m ≤ B := by dsimp [B]; omega
  have hM : M ≤ B := by dsimp [B]; omega
  have hM2 := Nat.pow_le_pow_left hM 2
  have hB2 : B ≤ B^2 := by nlinarith
  have hprod := Nat.mul_le_mul_left (2*n) hj
  have hg : 3*n+m+2*n*j+2*n-j ≤ M := by
    dsimp [M,moleculeCount]
    rw [wire_card,step_card]
    nlinarith [Nat.sub_le (3*n+m+2*n*j+2*n) j]
  change _ ≤ 4096*B^2
  nlinarith [Nat.sub_le M (2*n+1),Nat.sub_le (M-(2*n+1)) 1,Nat.sub_le M 1]

end IrrRAFEnumeration.SATSource
