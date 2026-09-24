import proofs.IrrRAFEnumeration.SATConflictSetup
import proofs.IrrRAFEnumeration.SATCoveragePhase

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

def coverageSetupTM : TM 13 := seqTM (copyIntoTM 4 5) (seqTM (copyIntoTM 3 4) (seqTM (copyIntoTM 6 2) (seqTM (addIntoTM 6 2) (seqTM (incRegTM 2) (seqTM (copyIntoTM 6 3) (seqTM (addIntoTM 6 3) (seqTM (addIntoTM 7 3) (seqTM (clearRegTM 0) (seqTM (incRegTM 0) (seqTM (copyIntoTM 10 1) (seqTM (decRegTM 1) (decRegTM 1))))))))))))

theorem coverageSetupTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) (ys : List Bool) :
    coverageSetupTM.HoareTime
      (EmitPred (parkedInput (cnfBits Φ))
        (conflictWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
          (moleculeCount n m) (reactionCount n m) n (cnfStreamCursor Φ 0)) ys)
      (EmitPred (parkedInput (cnfBits Φ))
        (coverageWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
          (moleculeCount n m) (reactionCount n m) 0 (cnfStreamCursor Φ 0)) ys)
      (4096*(n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+
        moleculeCount n m+reactionCount n m+1)^2) := by
  let W := Fintype.card (Wire n m)
  let Q := Fintype.card (Step n m)
  let M := moleculeCount n m
  let R := reactionCount n m
  let inp := parkedInput (cnfBits Φ)
  have hp := parkedInput_parked (cnfBits Φ)
  let v0 := conflictWork n m W Q M R n (cnfStreamCursor Φ 0)
  have hp0 : ∀ i, Parked (v0 i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact cnfStreamCursor_parked Φ 0
  let v1 := Function.update v0 (5 : Fin 13) (regTape (W+n+2))
  have hp1 : ∀ i, Parked (v1 i) := updateReg_parked v0 hp0 _ _
  have h1 := copyIntoTM_hoareTime (4 : Fin 13) 5 (by decide) (W+n+2) (Q-n-1)
    inp v0 ys hp (fun j _ => hp0 j) rfl rfl
  let v2 := Function.update v1 (4 : Fin 13) (regTape (Q-n))
  have hp2 : ∀ i, Parked (v2 i) := updateReg_parked v1 hp1 _ _
  have h2 := copyIntoTM_hoareTime (3 : Fin 13) 4 (by decide) (Q-n) (W+n+2)
    inp v1 ys hp (fun j _ => hp1 j) rfl rfl
  let v3 := Function.update v2 (2 : Fin 13) (regTape (n))
  have hp3 : ∀ i, Parked (v3 i) := updateReg_parked v2 hp2 _ _
  have h3 := copyIntoTM_hoareTime (6 : Fin 13) 2 (by decide) (n) (n)
    inp v2 ys hp (fun j _ => hp2 j) rfl rfl
  let v4 := Function.update v3 (2 : Fin 13) (regTape ((n)+(n)))
  have hp4 : ∀ i, Parked (v4 i) := updateReg_parked v3 hp3 _ _
  have h4 := addIntoTM_hoareTime (6 : Fin 13) 2 (by decide) (n) (n)
    inp v3 ys hp (fun j _ => hp3 j) rfl rfl
  let v5 := Function.update v4 (2 : Fin 13) (regTape (((n)+(n))+1))
  have hp5 : ∀ i, Parked (v5 i) := updateReg_parked v4 hp4 _ _
  have h5 := incRegTM_hoareTime (2 : Fin 13) ((n)+(n))
    inp v4 ys hp (fun j _ => hp4 j) rfl
  let v6 := Function.update v5 (3 : Fin 13) (regTape (n))
  have hp6 : ∀ i, Parked (v6 i) := updateReg_parked v5 hp5 _ _
  have h6 := copyIntoTM_hoareTime (6 : Fin 13) 3 (by decide) (n) (Q-n)
    inp v5 ys hp (fun j _ => hp5 j) rfl rfl
  let v7 := Function.update v6 (3 : Fin 13) (regTape ((n)+(n)))
  have hp7 : ∀ i, Parked (v7 i) := updateReg_parked v6 hp6 _ _
  have h7 := addIntoTM_hoareTime (6 : Fin 13) 3 (by decide) (n) (n)
    inp v6 ys hp (fun j _ => hp6 j) rfl rfl
  let v8 := Function.update v7 (3 : Fin 13) (regTape (((n)+(n))+(m)))
  have hp8 : ∀ i, Parked (v8 i) := updateReg_parked v7 hp7 _ _
  have h8 := addIntoTM_hoareTime (7 : Fin 13) 3 (by decide) (m) ((n)+(n))
    inp v7 ys hp (fun j _ => hp7 j) rfl rfl
  let v9 := Function.update v8 (0 : Fin 13) (regTape (0))
  have hp9 : ∀ i, Parked (v9 i) := updateReg_parked v8 hp8 _ _
  have h9 := clearRegTM_hoareTime (0 : Fin 13) (2*n+1)
    inp v8 ys hp (fun j _ => hp8 j) rfl
  let v10 := Function.update v9 (0 : Fin 13) (regTape ((0)+1))
  have hp10 : ∀ i, Parked (v10 i) := updateReg_parked v9 hp9 _ _
  have h10 := incRegTM_hoareTime (0 : Fin 13) (0)
    inp v9 ys hp (fun j _ => hp9 j) rfl
  let v11 := Function.update v10 (1 : Fin 13) (regTape (M))
  have hp11 : ∀ i, Parked (v11 i) := updateReg_parked v10 hp10 _ _
  have h11 := copyIntoTM_hoareTime (10 : Fin 13) 1 (by decide) (M) (M-(2*n+1)-2)
    inp v10 ys hp (fun j _ => hp10 j) rfl rfl
  let v12 := Function.update v11 (1 : Fin 13) (regTape ((M)-1))
  have hp12 : ∀ i, Parked (v12 i) := updateReg_parked v11 hp11 _ _
  have h12 := decRegTM_hoareTime (1 : Fin 13) (M)
    inp v11 ys hp (fun j _ => hp11 j) rfl
  let v13 := Function.update v12 (1 : Fin 13) (regTape (((M)-1)-1))
  have hp13 : ∀ i, Parked (v13 i) := updateReg_parked v12 hp12 _ _
  have h13 := decRegTM_hoareTime (1 : Fin 13) ((M)-1)
    inp v12 ys hp (fun j _ => hp12 j) rfl
  have h12end := seqTM_hoareTime _ _ h12 (emitPred_transition hp hp12 ys) h13
  have h11end := seqTM_hoareTime _ _ h11 (emitPred_transition hp hp11 ys) h12end
  have h10end := seqTM_hoareTime _ _ h10 (emitPred_transition hp hp10 ys) h11end
  have h9end := seqTM_hoareTime _ _ h9 (emitPred_transition hp hp9 ys) h10end
  have h8end := seqTM_hoareTime _ _ h8 (emitPred_transition hp hp8 ys) h9end
  have h7end := seqTM_hoareTime _ _ h7 (emitPred_transition hp hp7 ys) h8end
  have h6end := seqTM_hoareTime _ _ h6 (emitPred_transition hp hp6 ys) h7end
  have h5end := seqTM_hoareTime _ _ h5 (emitPred_transition hp hp5 ys) h6end
  have h4end := seqTM_hoareTime _ _ h4 (emitPred_transition hp hp4 ys) h5end
  have h3end := seqTM_hoareTime _ _ h3 (emitPred_transition hp hp3 ys) h4end
  have h2end := seqTM_hoareTime _ _ h2 (emitPred_transition hp hp2 ys) h3end
  have h1end := seqTM_hoareTime _ _ h1 (emitPred_transition hp hp1 ys) h2end
  have he : v13 = coverageWork n m W Q M R 0 (cnfStreamCursor Φ 0) := by
    funext i
    fin_cases i <;> simp [v13,v12,v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1,v0,conflictWork,coverageWork,
      Nat.sub_sub,two_mul,Nat.add_assoc]
  change coverageSetupTM.HoareTime _ (EmitPred inp v13 ys) _ at h1end
  rw [he] at h1end
  apply h1end.mono_bound
  let B := n+m+W+Q+M+R+1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hn : n ≤ B := by dsimp [B]; omega
  have hm : m ≤ B := by dsimp [B]; omega
  have hQ : Q ≤ B := by dsimp [B]; omega
  have hM : M ≤ B := by dsimp [B]; omega
  have hA : W+n+2 ≤ 3*B := by dsimp [B]; omega
  have hA2 := Nat.pow_le_pow_left hA 2
  have hn2 := Nat.pow_le_pow_left hn 2
  have hm2 := Nat.pow_le_pow_left hm 2
  have hQ2 := Nat.pow_le_pow_left (Nat.le_trans (Nat.sub_le Q n) hQ) 2
  have hM2 := Nat.pow_le_pow_left hM 2
  have hnm : n*m ≤ B^2 := by simpa [pow_two] using Nat.mul_le_mul hn hm
  have hB2 : B ≤ B^2 := by nlinarith
  change _ ≤ 4096*B^2
  nlinarith [Nat.sub_le Q n,Nat.sub_le (Q-n) 1,Nat.sub_le M (2*n+1),
    Nat.sub_le (M-(2*n+1)) 2,Nat.sub_le M 1]

end IrrRAFEnumeration.SATSource

