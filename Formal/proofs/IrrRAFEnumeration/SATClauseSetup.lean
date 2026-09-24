import proofs.IrrRAFEnumeration.SATClauseInner
import proofs.IrrRAFEnumeration.SATCoveragePrefix

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

def clauseSetupTM : TM 13 := seqTM (clearRegTM 0) (seqTM (incRegTM 0) (seqTM (copyIntoTM 10 1) (seqTM (decRegTM 1) (seqTM (decRegTM 1) (seqTM (copyIntoTM 6 11) (addIntoTM 6 11))))))

theorem clauseSetupTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) (ys : List Bool) :
    clauseSetupTM.HoareTime
      (EmitPred (parkedInput (cnfBits Φ))
        (coverageWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
          (moleculeCount n m) (reactionCount n m) n (cnfStreamCursor Φ 0)) ys)
      (EmitPred (parkedInput (cnfBits Φ)) (clauseWork Φ 0 0 (regTape m)) ys)
      (4096*(n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+
        moleculeCount n m+reactionCount n m+1)^2) := by
  let M := moleculeCount n m
  let R := reactionCount n m
  let inp := parkedInput (cnfBits Φ)
  have hp := parkedInput_parked (cnfBits Φ)
  let v0 := coverageWork n m (Fintype.card (Wire n m)) (Fintype.card (Step n m))
    M R n (cnfStreamCursor Φ 0)
  have hp0 : ∀ i, Parked (v0 i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact cnfStreamCursor_parked Φ _
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
  let v6 := Function.update v5 (11 : Fin 13) (regTape (n))
  have hp6 : ∀ i, Parked (v6 i) := updateReg_parked v5 hp5 _ _
  have h6 := copyIntoTM_hoareTime (6 : Fin 13) 11 (by decide) (n) (R)
    inp v5 ys hp (fun i _ => hp5 i) rfl rfl
  let v7 := Function.update v6 (11 : Fin 13) (regTape ((n)+(n)))
  have hp7 : ∀ i, Parked (v7 i) := updateReg_parked v6 hp6 _ _
  have h7 := addIntoTM_hoareTime (6 : Fin 13) 11 (by decide) (n) (n)
    inp v6 ys hp (fun i _ => hp6 i) rfl rfl
  have h6end := seqTM_hoareTime _ _ h6 (emitPred_transition hp hp6 ys) h7
  have h5end := seqTM_hoareTime _ _ h5 (emitPred_transition hp hp5 ys) h6end
  have h4end := seqTM_hoareTime _ _ h4 (emitPred_transition hp hp4 ys) h5end
  have h3end := seqTM_hoareTime _ _ h3 (emitPred_transition hp hp3 ys) h4end
  have h2end := seqTM_hoareTime _ _ h2 (emitPred_transition hp hp2 ys) h3end
  have h1end := seqTM_hoareTime _ _ h1 (emitPred_transition hp hp1 ys) h2end
  have he : v7 = clauseWork Φ 0 0 (regTape m) := by
    funext i
    fin_cases i <;> simp [v7,v6,v5,v4,v3,v2,v1,v0,coverageWork,clauseWork,M,
      Nat.sub_sub,two_mul,Nat.add_assoc]
    all_goals (congr 1; omega)
  change clauseSetupTM.HoareTime _ (EmitPred inp v7 ys) _ at h1end
  rw [he] at h1end
  apply h1end.mono_bound
  let B := n+m+Fintype.card (Wire n m)+Fintype.card (Step n m)+M+R+1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hn : n ≤ B := by dsimp [B]; omega
  have hR : R ≤ B := by dsimp [B]; omega
  have hM : M ≤ B := by dsimp [B]; omega
  have hn2 := Nat.pow_le_pow_left hn 2
  have hM2 := Nat.pow_le_pow_left hM 2
  have hB2 : B ≤ B^2 := by nlinarith
  change _ ≤ 4096*B^2
  nlinarith [Nat.sub_le M (2*n+1),Nat.sub_le (M-(2*n+1)) 1,Nat.sub_le M 1]

end IrrRAFEnumeration.SATSource
