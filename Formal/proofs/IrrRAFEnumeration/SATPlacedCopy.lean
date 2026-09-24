import proofs.Complexitylib.Models.TuringMachine.Subroutines.Internal
import proofs.Complexitylib.Models.TuringMachine.Placement.Internal
import proofs.Complexitylib.Models.TuringMachine.Registers.Emit

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

/-- Canonical copied binary tape, positioned at the first trailing blank. -/
def copiedEnd (xs : List Bool) : Tape :=
  { head := xs.length + 1, cells := (Tape.init (xs.map Γ.ofBool)).cells }

theorem copy_output_step {k : Nat} (idx : Fin k)
    {c c' : Cfg k (copyInputToWorkTM idx).Q}
    (hs : (copyInputToWorkTM idx).step c = some c')
    (hr : c.output.read = Γ.blank) : c'.output = c.output := by
  have hout : c.output.writeAndMove Γ.blank (idleDir c.output.read) = c.output := by
    simpa [hr,readBackWrite] using Tape.writeAndMove_readBack_idle_of_ne_start
      c.output (by rw [hr]; decide)
  cases hstate : c.state with
  | done => simp [TM.step,copyInputToWorkTM,hstate] at hs
  | copying =>
      have ho := congrArg (fun z : Option (Cfg k (copyInputToWorkTM idx).Q) =>
        z.map Cfg.output) hs
      by_cases hi : c.input.read = Γ.blank
      · simpa [TM.step,copyInputToWorkTM,hstate,hi,allIdle,hout] using ho.symm
      · simpa [TM.step,copyInputToWorkTM,hstate,hi,hout] using ho.symm

theorem copy_output_reaches {k t : Nat} (idx : Fin k)
    {c c' : Cfg k (copyInputToWorkTM idx).Q}
    (h : (copyInputToWorkTM idx).reachesIn t c c')
    (hr : c.output.read = Γ.blank) : c'.output = c.output := by
  induction h with
  | zero => rfl
  | step hs _ ih =>
      have he := copy_output_step idx hs hr
      exact (ih (by rw [he]; exact hr)).trans he

/-- With one work tape the copier has no unrelated active tapes to erase.
The arbitrary accumulated output is preserved because its head reads blank. -/
theorem soloCopy_correct (xs ys : List Bool) :
    (copyInputToWorkTM (0 : Fin 1)).HoareTime
      (EmitPred ((Tape.init (xs.map Γ.ofBool)).move .right)
        (fun _ => (Tape.init []).move .right) ys)
      (EmitPred (copiedEnd xs) (fun _ => copiedEnd xs) ys) (xs.length + 1) := by
  rintro inp work out ⟨hi,hw,ho⟩
  subst inp
  subst work
  obtain ⟨c,t,ht,hr,hh,hcells,hhead,hprefix⟩ :=
    copyInputToWorkTM_started_hoareTime (0 : Fin 1) xs
      ((Tape.init (xs.map Γ.ofBool)).move .right)
      (fun _ => (Tape.init []).move .right) out
      ⟨rfl,Tape.init_nil_move_right_hasBinaryPrefix_nil⟩
  have hc0 := work_cells_zero_eq_start_of_reachesIn (0 : Fin 1) hr
    (by rfl)
  have hi' : c.input = copiedEnd xs := Tape.ext hhead hcells
  have hw' : c.work = fun _ => copiedEnd xs := by
    funext i
    have he : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact Tape.ext hprefix.1 (hprefix.cells_eq_init hc0)
  have ho' := copy_output_reaches (0 : Fin 1) hr ho.read_blank
  exact ⟨c,t,ht,hr,hh,hi',hw',by simpa [ho'] using ho⟩

/-- Place the sole copying tape among persistent surrounding registers. -/
def placedCopyTM (pre post : Nat) : TM (pre + 1 + post) :=
  placeWorkTM pre post (copyInputToWorkTM (0 : Fin 1))

theorem placedCopy_correct (pre post : Nat) (xs ys : List Bool)
    (work : Fin (pre + 1 + post) → Tape)
    (hw : ∀ i, Parked (work i))
    (hd : work (placeWorkIdx pre post (0 : Fin 1)) = (Tape.init []).move .right) :
    (placedCopyTM pre post).HoareTime
      (EmitPred ((Tape.init (xs.map Γ.ofBool)).move .right) work ys)
      (EmitPred (copiedEnd xs)
        (Function.update work (placeWorkIdx pre post (0 : Fin 1)) (copiedEnd xs)) ys)
      (xs.length + 1) := by
  rintro inp work' out ⟨hi,hwork,ho⟩
  subst inp
  subst work'
  obtain ⟨c,t,ht,hr,hh,hi',hw',ho'⟩ := soloCopy_correct xs ys
    ((Tape.init (xs.map Γ.ofBool)).move .right)
    (fun _ => (Tape.init []).move .right) out ⟨rfl,rfl,ho⟩
  have hf : ∀ i, ¬ placeWorkInMiddle pre 1 i → (work i).read ≠ Γ.start :=
    fun i _ => (hw i).read_ne_start
  have hre := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    (copyInputToWorkTM (0 : Fin 1)) pre post work hr hf
  have hinit : placeWorkCfg (copyInputToWorkTM (0 : Fin 1)) pre post work
      {state := (copyInputToWorkTM (0 : Fin 1)).qstart,
       input := (Tape.init (xs.map Γ.ofBool)).move .right,
       work := fun _ => (Tape.init []).move .right,output := out} =
      {state := (placedCopyTM pre post).qstart,
       input := (Tape.init (xs.map Γ.ofBool)).move .right,work := work,output := out} := by
    refine (Cfg.mk.injEq ..).mpr ⟨rfl,rfl,?_,rfl⟩
    funext i
    dsimp only [placeWorkCfg]
    split
    · rename_i hm
      have he : i = placeWorkIdx pre post (0 : Fin 1) := by
        apply Fin.ext
        have := hm
        unfold placeWorkInMiddle at this
        simp only [placeWorkIdx_val]
        omega
      simpa [he] using hd.symm
    · rfl
  rw [hinit] at hre
  refine ⟨_,t,ht,hre,hh,hi',?_,ho'⟩
  funext i
  dsimp only [placeWorkCfg]
  split
  · rename_i hm
    have he : i = placeWorkIdx pre post (0 : Fin 1) := by
      apply Fin.ext
      unfold placeWorkInMiddle at hm
      simp only [placeWorkIdx_val]
      omega
    rw [hw']
    change copiedEnd xs = _
    rw [he,Function.update_self]
  · rename_i hm
    have he : i ≠ placeWorkIdx pre post (0 : Fin 1) := by
      intro he
      exact hm (he ▸ placeWorkInMiddle_placeWorkIdx pre post (0 : Fin 1))
    simp [he]

end IrrRAFEnumeration.SATSource
