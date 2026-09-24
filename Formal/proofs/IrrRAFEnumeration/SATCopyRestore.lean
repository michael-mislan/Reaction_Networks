import proofs.IrrRAFEnumeration.SATPlacedCopy
import proofs.IrrRAFEnumeration.SATDimensionInit

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

theorem copiedEnd_parked (xs : List Bool) : Parked (copiedEnd xs) :=
  ⟨by change 1 ≤ xs.length+1; omega,Tape.init_ofBool_cells_ne_start xs⟩

theorem updateTape_parked {k : Nat} (w : Fin k → Tape) (q : Fin k) (t : Tape)
    (hw : ∀ i, Parked (w i)) (ht : Parked t) :
    ∀ i, Parked (Function.update w q t i) := by
  intro i
  by_cases hi : i = q
  · subst i; simpa only [Function.update_self] using ht
  · simpa only [Function.update_of_ne hi] using hw i

theorem rewindCopiedWork_correct {k : Nat} (q : Fin k) (xs ys : List Bool)
    (inp : Tape) (w : Fin k → Tape) (hp : Parked inp)
    (hw : ∀ i, Parked (w i)) (hq : w q = copiedEnd xs) :
    (rewindWorkTM q).HoareTime (EmitPred inp w ys)
      (EmitPred inp (Function.update w q (parkedInput xs)) ys) (xs.length+3) := by
  let P : TM.TapePred k := fun input work out =>
    input = inp ∧ (work q).cells = (w q).cells ∧
      (∀ i, i ≠ q → work i = w i) ∧ OutAcc ys out
  have h := rewindWorkTM_hoareTime_frame q (xs.length+1) (P := P) (by
    intro input work out input' work' out' hP hc _ hother hi hoc hoh
    refine ⟨hi.trans hP.1,hc.trans hP.2.1,?_,?_⟩
    · intro i hne; exact (hother i hne).trans (hP.2.2.1 i hne)
    · have he : out' = out := Tape.ext hoh hoc
      rw [he]; exact hP.2.2.2)
  apply h.consequence
  · rintro input work out ⟨rfl,rfl,hout⟩
    refine ⟨?_,(hw q).2,?_,hp.read_ne_start,hout.parked.read_ne_start,
      hout.parked.1,fun i _ => ⟨(hw i).read_ne_start,(hw i).1⟩,
      rfl,rfl,fun _ _ => rfl,hout⟩
    · rw [hq]; rfl
    · rw [hq]; rfl
  · rintro input work out ⟨hh,hi,hc,hother,hout⟩
    refine ⟨hi,?_,hout⟩
    funext i
    by_cases he : i = q
    · subst i
      rw [Function.update_self]
      exact Tape.ext hh (by simpa [hq,copiedEnd,parkedInput] using hc)
    · rw [Function.update_of_ne he]
      exact hother i he
  · omega

def copyRestoreTM (pre post : Nat) : TM (pre+1+post) :=
  seqTM (placedCopyTM pre post)
    (seqTM rewindInputTM (rewindWorkTM (placeWorkIdx pre post (0 : Fin 1))))

/-- Copy the real input while preserving all occupied surrounding tapes,
then restore both input and copied-stream heads to cell one. -/
theorem copyRestore_correct (pre post : Nat) (xs ys : List Bool)
    (work : Fin (pre+1+post) → Tape) (hw : ∀ i, Parked (work i))
    (hd : work (placeWorkIdx pre post (0 : Fin 1)) = (Tape.init []).move .right) :
    (copyRestoreTM pre post).HoareTime (EmitPred (parkedInput xs) work ys)
      (EmitPred (parkedInput xs)
        (Function.update work (placeWorkIdx pre post (0 : Fin 1)) (parkedInput xs)) ys)
      (3*xs.length+9) := by
  let q := placeWorkIdx pre post (0 : Fin 1)
  let W := Function.update work q (copiedEnd xs)
  have hwp : ∀ i, Parked (W i) := updateTape_parked work q _ hw (copiedEnd_parked xs)
  have hc := placedCopy_correct pre post xs ys work hw hd
  have hr := rewindParsedInput_correct xs xs.length W ys hwp
  have he : advanceInput (parkedInput xs) xs.length = copiedEnd xs := by
    apply Tape.ext
    · simp [advanceInput,parkedInput,copiedEnd,Nat.add_comm]
    · rfl
  rw [he] at hr
  have hwc := rewindCopiedWork_correct q xs ys (parkedInput xs) W
    (parkedInput_parked xs) hwp (by simp [W])
  have hrs := seqTM_hoareTime _ _ hr (emitPred_transition (parkedInput_parked xs) hwp ys) hwc
  have hall := seqTM_hoareTime _ _ hc (emitPred_transition (copiedEnd_parked xs) hwp ys) hrs
  have hwe : Function.update W q (parkedInput xs) = Function.update work q (parkedInput xs) := by
    simp [W]
  rw [hwe] at hall
  apply hall.mono_bound
  omega

end IrrRAFEnumeration.SATSource
