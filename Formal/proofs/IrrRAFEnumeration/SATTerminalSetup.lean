import proofs.IrrRAFEnumeration.SATClauseEndpoint

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def finishWork (n m W Q M tail : Nat) (stream : Tape) : Fin 13 → Tape :=
  ![regTape (2*n+1),regTape (Q+2),regTape W,regTape (Q-1),regTape tail,regTape (M-1),
    regTape (n+m),regTape m,regTape W,regTape Q,regTape M,regTape (2*n),stream]

def resetWork (n m W Q M : Nat) (stream : Tape) : Fin 13 → Tape :=
  ![regTape 1,regTape (Q+1),regTape W,regTape Q,regTape 0,regTape (W+1),
    regTape (n+m),regTape m,regTape W,regTape Q,regTape M,regTape (2*n),stream]

def finishSetupTM : TM 13 := seqTM (copyIntoTM 6 0) (seqTM (addIntoTM 6 0) (seqTM (incRegTM 0) (seqTM (addIntoTM 7 6) (seqTM (copyIntoTM 9 1) (seqTM (incRegTM 1) (incRegTM 1))))))

theorem finishSetupTM_correct (n m W Q M : Nat) (stream inp : Tape) (ys : List Bool)
    (hs : Parked stream) (hp : Parked inp) :
    finishSetupTM.HoareTime (EmitPred inp (terminalWork n m W Q M stream) ys)
      (EmitPred inp (finishWork n m W Q M 1 stream) ys) (4096*(n+m+W+Q+M+1)^2) := by
  let v0 := terminalWork n m W Q M stream
  have hp0 : ∀ i, Parked (v0 i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact hs
  let v1 := Function.update v0 (0 : Fin 13) (regTape (n))
  have hp1 : ∀ i, Parked (v1 i) := updateReg_parked v0 hp0 _ _
  have h1 := copyIntoTM_hoareTime (6 : Fin 13) 0 (by decide) (n) (1)
    inp v0 ys hp (fun i _ => hp0 i) rfl rfl
  let v2 := Function.update v1 (0 : Fin 13) (regTape ((n)+(n)))
  have hp2 : ∀ i, Parked (v2 i) := updateReg_parked v1 hp1 _ _
  have h2 := addIntoTM_hoareTime (6 : Fin 13) 0 (by decide) (n) (n)
    inp v1 ys hp (fun i _ => hp1 i) rfl rfl
  let v3 := Function.update v2 (0 : Fin 13) (regTape (((n)+(n))+1))
  have hp3 : ∀ i, Parked (v3 i) := updateReg_parked v2 hp2 _ _
  have h3 := incRegTM_hoareTime (0 : Fin 13) ((n)+(n))
    inp v2 ys hp (fun i _ => hp2 i) rfl
  let v4 := Function.update v3 (6 : Fin 13) (regTape ((n)+(m)))
  have hp4 : ∀ i, Parked (v4 i) := updateReg_parked v3 hp3 _ _
  have h4 := addIntoTM_hoareTime (7 : Fin 13) 6 (by decide) (m) (n)
    inp v3 ys hp (fun i _ => hp3 i) rfl rfl
  let v5 := Function.update v4 (1 : Fin 13) (regTape (Q))
  have hp5 : ∀ i, Parked (v5 i) := updateReg_parked v4 hp4 _ _
  have h5 := copyIntoTM_hoareTime (9 : Fin 13) 1 (by decide) (Q) (M-2)
    inp v4 ys hp (fun i _ => hp4 i) rfl rfl
  let v6 := Function.update v5 (1 : Fin 13) (regTape ((Q)+1))
  have hp6 : ∀ i, Parked (v6 i) := updateReg_parked v5 hp5 _ _
  have h6 := incRegTM_hoareTime (1 : Fin 13) (Q)
    inp v5 ys hp (fun i _ => hp5 i) rfl
  let v7 := Function.update v6 (1 : Fin 13) (regTape (((Q)+1)+1))
  have hp7 : ∀ i, Parked (v7 i) := updateReg_parked v6 hp6 _ _
  have h7 := incRegTM_hoareTime (1 : Fin 13) ((Q)+1)
    inp v6 ys hp (fun i _ => hp6 i) rfl
  have h6end := seqTM_hoareTime _ _ h6 (emitPred_transition hp hp6 ys) h7
  have h5end := seqTM_hoareTime _ _ h5 (emitPred_transition hp hp5 ys) h6end
  have h4end := seqTM_hoareTime _ _ h4 (emitPred_transition hp hp4 ys) h5end
  have h3end := seqTM_hoareTime _ _ h3 (emitPred_transition hp hp3 ys) h4end
  have h2end := seqTM_hoareTime _ _ h2 (emitPred_transition hp hp2 ys) h3end
  have h1end := seqTM_hoareTime _ _ h1 (emitPred_transition hp hp1 ys) h2end
  have he : v7 = finishWork n m W Q M 1 stream := by
    funext i
    fin_cases i <;> simp [v7,v6,v5,v4,v3,v2,v1,v0,terminalWork,finishWork,two_mul,Nat.add_assoc]
  change finishSetupTM.HoareTime _ (EmitPred inp v7 ys) _ at h1end
  rw [he] at h1end
  apply h1end.mono_bound
  let B := n+m+W+Q+M+1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hn : n ≤ B := by dsimp [B]; omega
  have hm : m ≤ B := by dsimp [B]; omega
  have hw : W ≤ B := by dsimp [B]; omega
  have hq : Q ≤ B := by dsimp [B]; omega
  have hM : M ≤ B := by dsimp [B]; omega
  have hn2 := Nat.pow_le_pow_left hn 2
  have hm2 := Nat.pow_le_pow_left hm 2
  have hw2 := Nat.pow_le_pow_left hw 2
  have hq2 := Nat.pow_le_pow_left hq 2
  have hnm : n*m ≤ B^2 := by simpa [pow_two] using Nat.mul_le_mul hn hm
  have hB2 : B ≤ B^2 := by nlinarith
  change _ ≤ 4096*B^2
  nlinarith [Nat.sub_le M 2,Nat.sub_le M 1,Nat.sub_le Q 1]

def resetSetupTM : TM 13 := seqTM (clearRegTM 0) (seqTM (incRegTM 0) (seqTM (decRegTM 1) (seqTM (incRegTM 3) (seqTM (copyIntoTM 8 5) (incRegTM 5)))))

theorem resetSetupTM_correct (n m W Q M : Nat) (stream inp : Tape) (ys : List Bool)
    (hs : Parked stream) (hp : Parked inp) (hQ : 1 ≤ Q) :
    resetSetupTM.HoareTime (EmitPred inp (finishWork n m W Q M 0 stream) ys)
      (EmitPred inp (resetWork n m W Q M stream) ys) (4096*(n+m+W+Q+M+1)^2) := by
  let v0 := finishWork n m W Q M 0 stream
  have hp0 : ∀ i, Parked (v0 i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact hs
  let v1 := Function.update v0 (0 : Fin 13) (regTape (0))
  have hp1 : ∀ i, Parked (v1 i) := updateReg_parked v0 hp0 _ _
  have h1 := clearRegTM_hoareTime (0 : Fin 13) (2*n+1)
    inp v0 ys hp (fun i _ => hp0 i) rfl
  let v2 := Function.update v1 (0 : Fin 13) (regTape ((0)+1))
  have hp2 : ∀ i, Parked (v2 i) := updateReg_parked v1 hp1 _ _
  have h2 := incRegTM_hoareTime (0 : Fin 13) (0)
    inp v1 ys hp (fun i _ => hp1 i) rfl
  let v3 := Function.update v2 (1 : Fin 13) (regTape ((Q+2)-1))
  have hp3 : ∀ i, Parked (v3 i) := updateReg_parked v2 hp2 _ _
  have h3 := decRegTM_hoareTime (1 : Fin 13) (Q+2)
    inp v2 ys hp (fun i _ => hp2 i) rfl
  let v4 := Function.update v3 (3 : Fin 13) (regTape ((Q-1)+1))
  have hp4 : ∀ i, Parked (v4 i) := updateReg_parked v3 hp3 _ _
  have h4 := incRegTM_hoareTime (3 : Fin 13) (Q-1)
    inp v3 ys hp (fun i _ => hp3 i) rfl
  let v5 := Function.update v4 (5 : Fin 13) (regTape (W))
  have hp5 : ∀ i, Parked (v5 i) := updateReg_parked v4 hp4 _ _
  have h5 := copyIntoTM_hoareTime (8 : Fin 13) 5 (by decide) (W) (M-1)
    inp v4 ys hp (fun i _ => hp4 i) rfl rfl
  let v6 := Function.update v5 (5 : Fin 13) (regTape ((W)+1))
  have hp6 : ∀ i, Parked (v6 i) := updateReg_parked v5 hp5 _ _
  have h6 := incRegTM_hoareTime (5 : Fin 13) (W)
    inp v5 ys hp (fun i _ => hp5 i) rfl
  have h5end := seqTM_hoareTime _ _ h5 (emitPred_transition hp hp5 ys) h6
  have h4end := seqTM_hoareTime _ _ h4 (emitPred_transition hp hp4 ys) h5end
  have h3end := seqTM_hoareTime _ _ h3 (emitPred_transition hp hp3 ys) h4end
  have h2end := seqTM_hoareTime _ _ h2 (emitPred_transition hp hp2 ys) h3end
  have h1end := seqTM_hoareTime _ _ h1 (emitPred_transition hp hp1 ys) h2end
  have he : v6 = resetWork n m W Q M stream := by
    funext i
    fin_cases i <;> simp [v6,v5,v4,v3,v2,v1,v0,finishWork,resetWork,Nat.sub_add_cancel hQ]
  change resetSetupTM.HoareTime _ (EmitPred inp v6 ys) _ at h1end
  rw [he] at h1end
  apply h1end.mono_bound
  let B := n+m+W+Q+M+1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hn : n ≤ B := by dsimp [B]; omega
  have hm : m ≤ B := by dsimp [B]; omega
  have hw : W ≤ B := by dsimp [B]; omega
  have hq : Q ≤ B := by dsimp [B]; omega
  have hM : M ≤ B := by dsimp [B]; omega
  have hn2 := Nat.pow_le_pow_left hn 2
  have hm2 := Nat.pow_le_pow_left hm 2
  have hw2 := Nat.pow_le_pow_left hw 2
  have hq2 := Nat.pow_le_pow_left hq 2
  have hnm : n*m ≤ B^2 := by simpa [pow_two] using Nat.mul_le_mul hn hm
  have hB2 : B ≤ B^2 := by nlinarith
  change _ ≤ 4096*B^2
  nlinarith [Nat.sub_le M 2,Nat.sub_le M 1,Nat.sub_le Q 1]

end IrrRAFEnumeration.SATSource
