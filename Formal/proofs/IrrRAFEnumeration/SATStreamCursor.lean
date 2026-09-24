import proofs.Complexitylib.Models.TuringMachine.Registers.Emit
import proofs.Complexitylib.Models.TuringMachine.Tape.Encoding

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

theorem parked_move_right (t : Tape) (h : Parked t) : Parked (t.move .right) := by
  refine ⟨?_,h.2⟩
  change 1 ≤ t.head+1
  omega

theorem parked_writeBack_right (t : Tape) (h : Parked t) :
    t.writeAndMove (readBackWrite t.read) .right = t.move .right := by
  have hi := h.writeAndMove_readBack_idle
  have hw : t.write (readBackWrite t.read) = t := by
    simpa only [Tape.writeAndMove,idleDir,if_neg h.read_ne_start,Tape.move] using hi
  exact congrArg (fun s => s.move .right) hw

def emitCursorBitTM {k : Nat} (cursor : Fin k) : TM k where
  Q := BumpPhase
  qstart := .go
  qhalt := .done
  δ := fun _ ih wh _ =>
    (.done, fun i => readBackWrite (wh i),
      if wh cursor = Γ.one then Γw.one else Γw.zero,
      idleDir ih, fun i => if i = cursor then .right else idleDir (wh i), .right)
  δ_right_of_start := by
    intro _ _ _ _
    refine ⟨idleDir_right_of_start,?_,fun _ => rfl⟩
    intro i hi
    by_cases he : i = cursor
    · simp [he]
    · simpa [he] using idleDir_right_of_start hi

/-- Copy the current incidence bit to output and advance its work-tape
cursor, without any address calculation or unary-result register. -/
theorem emitCursorBitTM_correct {k : Nat} (cursor : Fin k) (bit : Bool)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (hr : (work cursor).read = Γ.ofBool bit) :
    (emitCursorBitTM cursor).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work cursor ((work cursor).move .right)) (ys ++ [bit])) 1 := by
  rintro inp' work' out ⟨hi,hwork,hout⟩
  subst inp'
  subst work'
  have hb : (if (work cursor).read = Γ.one then Γw.one else Γw.zero) = Γ.ofBool bit := by
    rw [hr]
    cases bit <;> rfl
  have hs : (emitCursorBitTM cursor).step
      {state := .go,input := inp,work := work,output := out} = some
      {state := .done,input := inp,
       work := Function.update work cursor ((work cursor).move .right),
       output := out.writeAndMove (Γ.ofBool bit) .right} := by
    simp only [TM.step,emitCursorBitTM,reduceCtorEq,↓reduceIte]
    rw [hb]
    refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl,?_,?_,rfl⟩)
    · exact hp.move_idle
    · funext i
      by_cases he : i = cursor
      · subst i
        simpa only [if_pos rfl,Function.update_self] using parked_writeBack_right (work cursor) (hw cursor)
      · simpa only [if_neg he,Function.update_of_ne he] using (hw i).writeAndMove_readBack_idle
  exact ⟨_,1,le_rfl,.step hs .zero,rfl,rfl,rfl,outAcc_append_bit hout bit⟩

end IrrRAFEnumeration.SATSource
