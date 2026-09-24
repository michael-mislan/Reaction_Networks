import proofs.IrrRAFEnumeration.SATSourceStreamInit
import proofs.Complexitylib.Models.TuringMachine.Registers.Arith

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def unsavedCounts (n m w q M r : Nat) (stream : Tape) : Fin 13 → Tape :=
  ![regTape n,regTape m,regTape w,regTape q,regTape M,regTape r,
    regTape 0,regTape 0,regTape 0,regTape 0,regTape 0,regTape 0,stream]

def savedCounts (n m w q M r : Nat) (stream : Tape) : Fin 13 → Tape :=
  ![regTape n,regTape m,regTape w,regTape q,regTape M,regTape r,
    regTape n,regTape m,regTape w,regTape q,regTape M,regTape r,stream]

def saveCountsTM : TM 13 := seqTM (copyIntoTM 0 6) (seqTM (copyIntoTM 1 7) (seqTM (copyIntoTM 2 8) (seqTM (copyIntoTM 3 9) (seqTM (copyIntoTM 4 10) (copyIntoTM 5 11)))))

/-- Save all source counts while preserving the binary incidence stream. -/
theorem saveCountsTM_correct (n m w q M r : Nat) (stream inp : Tape) (ys : List Bool)
    (hs : Parked stream) (hp : Parked inp) :
    saveCountsTM.HoareTime (EmitPred inp (unsavedCounts n m w q M r stream) ys)
      (EmitPred inp (savedCounts n m w q M r stream) ys)
      (128*(n+m+w+q+M+r+1)^2) := by
  let v0 := unsavedCounts n m w q M r stream
  have hp0 : ∀ i, Parked (v0 i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact hs
  let v1 := Function.update v0 (6 : Fin 13) (regTape n)
  have hp1 : ∀ j, Parked (v1 j) := updateReg_parked v0 hp0 _ _
  have h1 := copyIntoTM_hoareTime (0 : Fin 13) 6 (by decide) n 0
    inp v0 ys hp (fun j _ => hp0 j) rfl rfl
  let v2 := Function.update v1 (7 : Fin 13) (regTape m)
  have hp2 : ∀ j, Parked (v2 j) := updateReg_parked v1 hp1 _ _
  have h2 := copyIntoTM_hoareTime (1 : Fin 13) 7 (by decide) m 0
    inp v1 ys hp (fun j _ => hp1 j) rfl rfl
  let v3 := Function.update v2 (8 : Fin 13) (regTape w)
  have hp3 : ∀ j, Parked (v3 j) := updateReg_parked v2 hp2 _ _
  have h3 := copyIntoTM_hoareTime (2 : Fin 13) 8 (by decide) w 0
    inp v2 ys hp (fun j _ => hp2 j) rfl rfl
  let v4 := Function.update v3 (9 : Fin 13) (regTape q)
  have hp4 : ∀ j, Parked (v4 j) := updateReg_parked v3 hp3 _ _
  have h4 := copyIntoTM_hoareTime (3 : Fin 13) 9 (by decide) q 0
    inp v3 ys hp (fun j _ => hp3 j) rfl rfl
  let v5 := Function.update v4 (10 : Fin 13) (regTape M)
  have hp5 : ∀ j, Parked (v5 j) := updateReg_parked v4 hp4 _ _
  have h5 := copyIntoTM_hoareTime (4 : Fin 13) 10 (by decide) M 0
    inp v4 ys hp (fun j _ => hp4 j) rfl rfl
  let v6 := Function.update v5 (11 : Fin 13) (regTape r)
  have hp6 : ∀ j, Parked (v6 j) := updateReg_parked v5 hp5 _ _
  have h6 := copyIntoTM_hoareTime (5 : Fin 13) 11 (by decide) r 0
    inp v5 ys hp (fun j _ => hp5 j) rfl rfl
  have h56 := seqTM_hoareTime _ _ h5 (emitPred_transition hp hp5 ys) h6
  have h456 := seqTM_hoareTime _ _ h4 (emitPred_transition hp hp4 ys) h56
  have h3456 := seqTM_hoareTime _ _ h3 (emitPred_transition hp hp3 ys) h456
  have h23456 := seqTM_hoareTime _ _ h2 (emitPred_transition hp hp2 ys) h3456
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hp1 ys) h23456
  have he : v6 = savedCounts n m w q M r stream := by
    funext i
    fin_cases i <;> simp [v6,v5,v4,v3,v2,v1,v0,unsavedCounts,savedCounts]
  change saveCountsTM.HoareTime _ (EmitPred inp v6 ys) _ at h
  rw [he] at h
  apply h.mono_bound
  let B := n+m+w+q+M+r+1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hn : n ≤ B := by dsimp [B]; omega
  have hn2 : n^2 ≤ B^2 := Nat.pow_le_pow_left hn 2
  have hm : m ≤ B := by dsimp [B]; omega
  have hm2 : m^2 ≤ B^2 := Nat.pow_le_pow_left hm 2
  have hw : w ≤ B := by dsimp [B]; omega
  have hw2 : w^2 ≤ B^2 := Nat.pow_le_pow_left hw 2
  have hq : q ≤ B := by dsimp [B]; omega
  have hq2 : q^2 ≤ B^2 := Nat.pow_le_pow_left hq 2
  have hM : M ≤ B := by dsimp [B]; omega
  have hM2 : M^2 ≤ B^2 := Nat.pow_le_pow_left hM 2
  have hr : r ≤ B := by dsimp [B]; omega
  have hr2 : r^2 ≤ B^2 := Nat.pow_le_pow_left hr 2
  have hB2 : B ≤ B^2 := by nlinarith
  change _ ≤ 128*B^2
  nlinarith

end IrrRAFEnumeration.SATSource

