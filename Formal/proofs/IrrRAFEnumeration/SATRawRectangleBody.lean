import proofs.IrrRAFEnumeration.SATRawRectangleRows

namespace IrrRAFEnumeration.SATSource
open Complexity SAT Complexity.TM

def rectangleAdvanceTM : TM 4 := seqTM (clearRegTM 1) (incRegTM 0)

theorem rectangleAdvanceTM_correct (N j : Nat) (inp inner outer : Tape)
    (ys : List Bool) (hp : Parked inp) (hi : Parked inner) (ho : Parked outer) :
    rectangleAdvanceTM.HoareTime
      (EmitPred inp (rectangleWork j N inner outer) ys)
      (EmitPred inp (rectangleWork (j+1) 0 inner outer) ys) (2*N+2*j+9) := by
  have hw := rectangleWork_parked j N inner outer hi ho
  have hz := rectangleWork_parked j 0 inner outer hi ho
  have he : Function.update (rectangleWork j N inner outer) 1 (regTape 0) =
      rectangleWork j 0 inner outer := by
    funext i
    fin_cases i <;> rfl
  have he' : Function.update (rectangleWork j 0 inner outer) 0 (regTape (j+1)) =
      rectangleWork (j+1) 0 inner outer := by
    funext i
    fin_cases i <;> rfl
  have hclear := clearRegTM_hoareTime (1 : Fin 4) N inp
    (rectangleWork j N inner outer) ys hp (fun i _ => hw i) rfl
  rw [he] at hclear
  have h := seqTM_hoareTime _ _ hclear (emitPred_transition hp hz _)
    (incRegTM_hoareTime (0 : Fin 4) j inp (rectangleWork j 0 inner outer) ys
      hp (fun i _ => hz i) rfl)
  rw [he'] at h
  exact h.mono_bound (by omega)

def rectangleBlockTM : TM 4 := seqTM rectangleInnerTM rectangleAdvanceTM

def rectangleBlockBound (L N M : Nat) := N*(8*L+2*N+31)+2*N+2*M+12

theorem rectangleBlockTM_correct (N j M : Nat) (hj : j ≤ M) (φ : CNF)
    (inp outer : Tape) (ys : List Bool) (hin : inp.HasBinarySuffix φ.encode)
    (hhead : inp.head = 1) (hzero : inp.cells 0 = Γ.start)
    (hp : Parked inp) (ho : Parked outer) :
    rectangleBlockTM.HoareTime
      (EmitPred inp (rectangleWork j 0 (regTape N) outer) ys)
      (EmitPred inp (rectangleWork (j+1) 0 (regTape N) outer)
        (ys ++ rectangleRowPrefix φ j N)) (rectangleBlockBound φ.encode.length N M) := by
  have h := seqTM_hoareTime _ _
    (rectangleInnerTM_correct N j φ inp outer ys hin hhead hzero hp ho)
    (emitPred_transition hp (rectangleWork_parked j N _ outer (parked_regTape N) ho) _)
    (rectangleAdvanceTM_correct N j inp (regTape N) outer _ hp (parked_regTape N) ho)
  exact h.mono_bound (by unfold rectangleBlockBound; omega)

def rectangleRowsPrefix (φ : CNF) (N : Nat) : Nat → List Bool
  | 0 => []
  | j+1 => rectangleRowsPrefix φ N j ++ rectangleRowPrefix φ j N

def rectangleRowsTM : TM 4 := forRegTM rectangleBlockTM 3

theorem rectangleRowsTM_correct (N M : Nat) (φ : CNF) (inp : Tape) (ys : List Bool)
    (hin : inp.HasBinarySuffix φ.encode) (hhead : inp.head = 1)
    (hzero : inp.cells 0 = Γ.start) (hp : Parked inp) :
    rectangleRowsTM.HoareTime
      (EmitPred inp (rectangleWork 0 0 (regTape N) (regTape M)) ys)
      (EmitPred inp (rectangleWork M 0 (regTape N) (regTape M))
        (ys ++ rectangleRowsPrefix φ N M))
      (M*(rectangleBlockBound φ.encode.length N M+3)+2) := by
  have hw := fun j => rectangleWork_parked j 0 (regTape N) (regTape M)
    (parked_regTape N) (parked_regTape M)
  have he : ∀ j (t : Tape), Function.update (rectangleWork j 0 (regTape N) (regTape M)) 3 t =
      rectangleWork j 0 (regTape N) t := by
    intro j t
    funext i
    fin_cases i <;> rfl
  have hb : ∀ j, j < M → rectangleBlockTM.HoareTime
      (EmitPred inp (Function.update (rectangleWork j 0 (regTape N) (regTape M)) 3
        ⟨j+2,regCells M⟩) (ys ++ rectangleRowsPrefix φ N j))
      (EmitPred inp (Function.update (rectangleWork (j+1) 0 (regTape N) (regTape M)) 3
        ⟨j+2,regCells M⟩) (ys ++ rectangleRowsPrefix φ N (j+1)))
      (rectangleBlockBound φ.encode.length N M) := by
    intro j hj
    rw [he,he]
    have h := rectangleBlockTM_correct N j M (by omega) φ inp ⟨j+2,regCells M⟩
      (ys ++ rectangleRowsPrefix φ N j) hin hhead hzero hp (parked_regCells (by omega))
    simpa only [rectangleRowsPrefix,List.append_assoc] using h
  have h := forRegTM_hoareTime rectangleBlockTM (3 : Fin 4) M inp
    (fun j => rectangleWork j 0 (regTape N) (regTape M))
    (fun j => ys ++ rectangleRowsPrefix φ N j) (rectangleBlockBound φ.encode.length N M)
    hp (fun _ => rfl) (fun j i _ => hw j i) hb
  have ht : M*(rectangleBlockBound φ.encode.length N M+2)+(M+2) =
      M*(rectangleBlockBound φ.encode.length N M+3)+2 := by ring
  simpa only [rectangleRowsTM,rectangleRowsPrefix,List.append_nil,ht] using h

end IrrRAFEnumeration.SATSource
