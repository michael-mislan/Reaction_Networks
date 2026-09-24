import proofs.IrrRAFEnumeration.SATRawRectangle
import proofs.Complexitylib.Models.TuringMachine.Registers.ForReg

namespace IrrRAFEnumeration.SATSource
open Complexity SAT Complexity.TM

theorem rectangleWork_parked (j v : Nat) (inner outer : Tape)
    (hi : Parked inner) (ho : Parked outer) :
    ∀ i, Parked (rectangleWork j v inner outer i) := by
  intro i
  fin_cases i <;> first | exact parked_regTape _ | exact hi | exact ho

def rectangleRowPrefix (φ : CNF) (j : Nat) : Nat → List Bool
  | 0 => []
  | v+1 => rectangleRowPrefix φ j v ++
      [incidenceCNFMatch false v φ j,incidenceCNFMatch true v φ j]

def rectangleBodyTM : TM 4 := seqTM rectanglePairTM (incRegTM 1)

theorem rectangleBodyTM_correct (v j : Nat) (φ : CNF)
    (inp inner outer : Tape) (ys : List Bool) (hin : inp.HasBinarySuffix φ.encode)
    (hhead : inp.head = 1) (hzero : inp.cells 0 = Γ.start)
    (hp : Parked inp) (hi : Parked inner) (ho : Parked outer) :
    rectangleBodyTM.HoareTime
      (EmitPred inp (rectangleWork j v inner outer) ys)
      (EmitPred inp (rectangleWork j (v+1) inner outer)
        (ys ++ [incidenceCNFMatch false v φ j,incidenceCNFMatch true v φ j]))
      (8*φ.encode.length+2*v+28) := by
  have hw := rectangleWork_parked j v inner outer hi ho
  have he : Function.update (rectangleWork j v inner outer) 1 (regTape (v+1)) =
      rectangleWork j (v+1) inner outer := by
    funext i
    fin_cases i <;> rfl
  have h := seqTM_hoareTime _ _
    (rectanglePairTM_correct v j φ inp inner outer ys hin hhead hzero hp hi ho)
    (emitPred_transition hp hw _)
    (incRegTM_hoareTime (1 : Fin 4) v inp (rectangleWork j v inner outer) _ hp
      (fun i _ => hw i) rfl)
  rw [he] at h
  exact h.mono_bound (by omega)

def rectangleInnerTM : TM 4 := forRegTM rectangleBodyTM 2

theorem rectangleInnerTM_correct (N j : Nat) (φ : CNF)
    (inp outer : Tape) (ys : List Bool) (hin : inp.HasBinarySuffix φ.encode)
    (hhead : inp.head = 1) (hzero : inp.cells 0 = Γ.start)
    (hp : Parked inp) (ho : Parked outer) :
    rectangleInnerTM.HoareTime
      (EmitPred inp (rectangleWork j 0 (regTape N) outer) ys)
      (EmitPred inp (rectangleWork j N (regTape N) outer)
        (ys ++ rectangleRowPrefix φ j N))
      (N*(8*φ.encode.length+2*N+31)+2) := by
  have hw := fun v => rectangleWork_parked j v (regTape N) outer (parked_regTape N) ho
  have he : ∀ v (t : Tape), Function.update (rectangleWork j v (regTape N) outer) 2 t =
      rectangleWork j v t outer := by
    intro v t
    funext i
    fin_cases i <;> rfl
  have hb : ∀ v, v < N → rectangleBodyTM.HoareTime
      (EmitPred inp (Function.update (rectangleWork j v (regTape N) outer) 2
        ⟨v+2,regCells N⟩) (ys ++ rectangleRowPrefix φ j v))
      (EmitPred inp (Function.update (rectangleWork j (v+1) (regTape N) outer) 2
        ⟨v+2,regCells N⟩) (ys ++ rectangleRowPrefix φ j (v+1)))
      (8*φ.encode.length+2*N+28) := by
    intro v hv
    rw [he,he]
    have h := rectangleBodyTM_correct v j φ inp ⟨v+2,regCells N⟩ outer
      (ys ++ rectangleRowPrefix φ j v) hin hhead hzero hp (parked_regCells (by omega)) ho
    have h' := h.mono_bound (show 8*φ.encode.length+2*v+28 ≤
      8*φ.encode.length+2*N+28 by omega)
    simpa only [rectangleRowPrefix,List.append_assoc] using h'
  have h := forRegTM_hoareTime rectangleBodyTM (2 : Fin 4) N inp
    (fun v => rectangleWork j v (regTape N) outer)
    (fun v => ys ++ rectangleRowPrefix φ j v) (8*φ.encode.length+2*N+28)
    hp (fun _ => rfl) (fun v i _ => hw v i) hb
  have ht : N*((8*φ.encode.length+2*N+28)+2)+(N+2) =
      N*(8*φ.encode.length+2*N+31)+2 := by ring
  simpa only [rectangleInnerTM,rectangleRowPrefix,List.append_nil,ht] using h

end IrrRAFEnumeration.SATSource
