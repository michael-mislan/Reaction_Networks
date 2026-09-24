import proofs.IrrRAFEnumeration.SATDimensionInit
import proofs.Complexitylib.Models.TuringMachine.Registers.Arith

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

inductive CountOp where
  | inc (dst : Fin 6)
  | add (src dst : Fin 6)
  | mul (src₁ src₂ dst : Fin 6)

def CountOp.Valid : CountOp → Prop
  | .inc _ => True
  | .add s d => s ≠ d
  | .mul s t d => s ≠ t ∧ s ≠ d ∧ t ≠ d

def countEval (op : CountOp) (v : Fin 6 → Nat) : Fin 6 → Nat :=
  match op with
  | .inc d => Function.update v d (v d+1)
  | .add s d => Function.update v d (v d+v s)
  | .mul s t d => Function.update v d (v d+v s*v t)

def countOpTM : CountOp → TM 6
  | .inc d => incRegTM d
  | .add s d => addIntoTM s d
  | .mul s t d => mulAddIntoTM s t d

def countOpCost (op : CountOp) (v : Fin 6 → Nat) : Nat :=
  match op with
  | .inc d => 2*v d+4
  | .add s d => v s*((2*(v d+v s)+4)+2)+(v s+2)
  | .mul s t d => v s*(mulAddBound (v s) (v t) (v d)+2)+(v s+2)

def countTapes (v : Fin 6 → Nat) : Fin 6 → Tape := fun i => regTape (v i)

theorem countTapes_update (v : Fin 6 → Nat) (d : Fin 6) (x : Nat) :
    countTapes (Function.update v d x) = Function.update (countTapes v) d (regTape x) := by
  funext i
  by_cases hi : i = d
  · subst i
    simp [countTapes]
  · simp [countTapes, Function.update_of_ne hi]

theorem countOp_correct (op : CountOp) (hv : op.Valid) (v : Fin 6 → Nat)
    (inp : Tape) (ys : List Bool) (hp : Parked inp) :
    (countOpTM op).HoareTime (EmitPred inp (countTapes v) ys)
      (EmitPred inp (countTapes (countEval op v)) ys) (countOpCost op v) := by
  cases op with
  | inc d =>
      simpa only [countOpTM, countEval, countOpCost, countTapes_update] using
        incRegTM_hoareTime d (v d) inp (countTapes v) ys hp
          (fun _ _ => parked_regTape _) rfl
  | add s d =>
      simpa only [countOpTM, countEval, countOpCost, countTapes_update] using
        addIntoTM_hoareTime s d hv (v s) (v d) inp (countTapes v) ys hp
          (fun _ _ => parked_regTape _) rfl rfl
  | mul s t d =>
      simpa only [countOpTM, countEval, countOpCost, countTapes_update] using
        mulAddIntoTM_hoareTime s t d hv.1 hv.2.1 hv.2.2 (v s) (v t) (v d)
          inp (countTapes v) ys hp (fun _ _ => parked_regTape _) rfl rfl rfl

def countRun : List CountOp → (Fin 6 → Nat) → (Fin 6 → Nat)
  | [], v => v
  | op :: ops, v => countRun ops (countEval op v)

def countCost : List CountOp → (Fin 6 → Nat) → Nat
  | [], _ => 1
  | op :: ops, v => countOpCost op v+1+countCost ops (countEval op v)

def countSeqTM : List CountOp → TM 6
  | [] => skipTM
  | op :: ops => seqTM (countOpTM op) (countSeqTM ops)

theorem countSeq_correct (ops : List CountOp) (hv : ∀ op ∈ ops, op.Valid)
    (v : Fin 6 → Nat) (inp : Tape) (ys : List Bool) (hp : Parked inp) :
    (countSeqTM ops).HoareTime (EmitPred inp (countTapes v) ys)
      (EmitPred inp (countTapes (countRun ops v)) ys) (countCost ops v) := by
  induction ops generalizing v with
  | nil => exact skipTM_hoareTime inp (countTapes v) ys hp (fun _ => parked_regTape _)
  | cons op ops ih =>
      exact seqTM_hoareTime _ _ (countOp_correct op (hv op (by simp)) v inp ys hp)
        (emitPred_transition hp (fun _ => parked_regTape _) ys)
        (ih (fun op hop => hv op (by simp [hop])) (countEval op v))

theorem countEval_mono (op : CountOp) {v w : Fin 6 → Nat} (h : ∀ i, v i ≤ w i) :
    ∀ i, countEval op v i ≤ countEval op w i := by
  intro i
  cases op <;> simp only [countEval, Function.update_apply]
  all_goals split_ifs
  all_goals first | exact h _ | (gcongr <;> apply h)

theorem countOpCost_mono (op : CountOp) {v w : Fin 6 → Nat} (h : ∀ i, v i ≤ w i) :
    countOpCost op v ≤ countOpCost op w := by
  cases op <;> dsimp [countOpCost, mulAddBound] <;> gcongr <;> apply h

theorem countCost_mono (ops : List CountOp) {v w : Fin 6 → Nat} (h : ∀ i, v i ≤ w i) :
    countCost ops v ≤ countCost ops w := by
  induction ops generalizing v w with
  | nil => exact le_rfl
  | cons op ops ih =>
      exact Nat.add_le_add (Nat.add_le_add_right (countOpCost_mono op h) 1)
        (ih (countEval_mono op h))


end IrrRAFEnumeration.SATSource
