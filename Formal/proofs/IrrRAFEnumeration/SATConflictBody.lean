import proofs.IrrRAFEnumeration.SATFixedRows
import proofs.Complexitylib.Models.TuringMachine.Registers.DecReg

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def conflictPattern (W p s j l c t : Nat) : List Bool :=
  spanRow p 2 s ++ markedRow W j l true ++ spanRow c 1 t

def conflictAdvance (work : Fin 13 → Tape) (p s j l c t : Nat) : Fin 13 → Tape :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update work 0 (regTape (p+2))) 1 (regTape (s-2)))
      2 (regTape (j+1))) 3 (regTape (l-1))) 4 (regTape (c+1))) 5 (regTape (t-1))

def conflictBodyTM : TM 13 := seqTM (fixedSpanRowTM 2 0 1) (seqTM (twoMarkRowTM 8 2 3) (seqTM (fixedSpanRowTM 1 4 5) (seqTM (incRegTM 0) (seqTM (incRegTM 0) (seqTM (decRegTM 1) (seqTM (decRegTM 1) (seqTM (incRegTM 2) (seqTM (decRegTM 3) (seqTM (incRegTM 4) (decRegTM 5))))))))))

theorem conflictBodyTM_correct (W p s j l c t B : Nat)
    (inp : Tape) (work : Fin 13 → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (h0 : work 0 = regTape p) (h1 : work 1 = regTape s)
    (h2 : work 2 = regTape j) (h3 : work 3 = regTape l)
    (h4 : work 4 = regTape c) (h5 : work 5 = regTape t) (h8 : work 8 = regTape W)
    (hB : W ≤ B ∧ p ≤ B ∧ s ≤ B ∧ j ≤ B ∧ l ≤ B ∧ c ≤ B ∧ t ≤ B) :
    conflictBodyTM.HoareTime (EmitPred inp work ys)
      (EmitPred inp (conflictAdvance work p s j l c t) (ys ++ conflictPattern W p s j l c t))
      (100*(B+1)) := by
  have hr1 := fixedSpanRowTM_correct 2 (0 : Fin 13) 1 p s inp work ys hp hw h0 h1
  have hr2 := twoMarkRowTM_correct (8 : Fin 13) 2 3 W j l inp work
    (ys ++ spanRow p 2 s) hp hw h8 h2 h3
  have hr3 := fixedSpanRowTM_correct 1 (4 : Fin 13) 5 c t inp work
    ((ys ++ spanRow p 2 s) ++ markedRow W j l true) hp hw h4 h5
  let outBits := ((ys ++ spanRow p 2 s) ++ markedRow W j l true) ++ spanRow c 1 t
  let v0 := work
  have hp0 : ∀ i, Parked (v0 i) := hw
  let v1 := Function.update v0 (0 : Fin 13) (regTape (p+1))
  have hp1 : ∀ i, Parked (v1 i) := updateReg_parked v0 hp0 _ _
  have hu1 := incRegTM_hoareTime (0 : Fin 13) (p) inp v0 outBits hp
    (fun i _ => hp0 i) (by simpa [v0] using h0)
  let v2 := Function.update v1 (0 : Fin 13) (regTape (p+1+1))
  have hp2 : ∀ i, Parked (v2 i) := updateReg_parked v1 hp1 _ _
  have hu2 := incRegTM_hoareTime (0 : Fin 13) (p+1) inp v1 outBits hp
    (fun i _ => hp1 i) rfl
  let v3 := Function.update v2 (1 : Fin 13) (regTape (s-1))
  have hp3 : ∀ i, Parked (v3 i) := updateReg_parked v2 hp2 _ _
  have hu3 := decRegTM_hoareTime (1 : Fin 13) (s) inp v2 outBits hp
    (fun i _ => hp2 i) (by simpa [v2,v1,v0] using h1)
  let v4 := Function.update v3 (1 : Fin 13) (regTape (s-1-1))
  have hp4 : ∀ i, Parked (v4 i) := updateReg_parked v3 hp3 _ _
  have hu4 := decRegTM_hoareTime (1 : Fin 13) (s-1) inp v3 outBits hp
    (fun i _ => hp3 i) rfl
  let v5 := Function.update v4 (2 : Fin 13) (regTape (j+1))
  have hp5 : ∀ i, Parked (v5 i) := updateReg_parked v4 hp4 _ _
  have hu5 := incRegTM_hoareTime (2 : Fin 13) (j) inp v4 outBits hp
    (fun i _ => hp4 i) (by simpa [v4,v3,v2,v1,v0] using h2)
  let v6 := Function.update v5 (3 : Fin 13) (regTape (l-1))
  have hp6 : ∀ i, Parked (v6 i) := updateReg_parked v5 hp5 _ _
  have hu6 := decRegTM_hoareTime (3 : Fin 13) (l) inp v5 outBits hp
    (fun i _ => hp5 i) (by simpa [v5,v4,v3,v2,v1,v0] using h3)
  let v7 := Function.update v6 (4 : Fin 13) (regTape (c+1))
  have hp7 : ∀ i, Parked (v7 i) := updateReg_parked v6 hp6 _ _
  have hu7 := incRegTM_hoareTime (4 : Fin 13) (c) inp v6 outBits hp
    (fun i _ => hp6 i) (by simpa [v6,v5,v4,v3,v2,v1,v0] using h4)
  let v8 := Function.update v7 (5 : Fin 13) (regTape (t-1))
  have hp8 : ∀ i, Parked (v8 i) := updateReg_parked v7 hp7 _ _
  have hu8 := decRegTM_hoareTime (5 : Fin 13) (t) inp v7 outBits hp
    (fun i _ => hp7 i) (by simpa [v7,v6,v5,v4,v3,v2,v1,v0] using h5)
  have hu78 := seqTM_hoareTime _ _ hu7 (emitPred_transition hp hp7 outBits) hu8
  have hu6end := seqTM_hoareTime _ _ hu6 (emitPred_transition hp hp6 outBits) hu78
  have hu5end := seqTM_hoareTime _ _ hu5 (emitPred_transition hp hp5 outBits) hu6end
  have hu4end := seqTM_hoareTime _ _ hu4 (emitPred_transition hp hp4 outBits) hu5end
  have hu3end := seqTM_hoareTime _ _ hu3 (emitPred_transition hp hp3 outBits) hu4end
  have hu2end := seqTM_hoareTime _ _ hu2 (emitPred_transition hp hp2 outBits) hu3end
  have hu1end := seqTM_hoareTime _ _ hu1 (emitPred_transition hp hp1 outBits) hu2end
  have hr3end := seqTM_hoareTime _ _ hr3 (emitPred_transition hp hw outBits) hu1end
  have hr2end := seqTM_hoareTime _ _ hr2 (emitPred_transition hp hw _) hr3end
  have hall := seqTM_hoareTime _ _ hr1 (emitPred_transition hp hw _) hr2end
  have he : v8 = conflictAdvance work p s j l c t := by
    have hs : s-1-1 = s-2 := by omega
    funext i
    fin_cases i <;> simp [v8,v7,v6,v5,v4,v3,v2,v1,v0,conflictAdvance,hs,Nat.add_assoc]
  change conflictBodyTM.HoareTime _ (EmitPred inp v8 outBits) _ at hall
  rw [he] at hall
  have ho : outBits = ys ++ conflictPattern W p s j l c t := by
    simp [outBits,conflictPattern,List.append_assoc]
  rw [ho] at hall
  apply hall.mono_bound
  rcases hB with ⟨hW,hpB,hsB,hjB,hlB,hcB,htB⟩
  nlinarith [Nat.sub_le s 1]

end IrrRAFEnumeration.SATSource
