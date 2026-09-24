import proofs.IrrRAFEnumeration.SATSyntaxBoundary
import proofs.IrrRAFEnumeration.SATRawRectangleCompiler
import proofs.IrrRAFEnumeration.DeadlineFirstEntry
import proofs.Complexitylib.Models.TuringMachine.Subroutines.Internal

namespace IrrRAFEnumeration.SATSource
open Complexity SAT Complexity.TM DeadlineFirstEntry

def clearFlagTM : TM 4 where
  Q := Bool
  qstart := false
  qhalt := true
  δ := fun _ ih wh oh => (true,fun i => readBackWrite (wh i),Γw.blank,
    idleDir ih,fun i => idleDir (wh i),idleDir oh)
  δ_right_of_start := fun _ _ _ _ =>
    ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩

theorem clearFlagTM_correct (inp : Tape) (work : Fin 4 → Tape) (b : Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i)) :
    clearFlagTM.HoareTime
      (fun a w out => a = inp ∧ w = work ∧ out = syntaxVerdict b)
      (EmitPred inp work []) 1 := by
  rintro a w out ⟨rfl,rfl,rfl⟩
  have hout : (syntaxVerdict b).writeAndMove Γw.blank
      (idleDir (syntaxVerdict b).read) = syntaxBlankOut := by
    apply Tape.ext
    · cases b <;> rfl
    · simp only [Tape.writeAndMove,Tape.move_cells]
      funext j
      by_cases hj : j = 1
      · subst j; cases b <;> rfl
      · cases b <;> simp [syntaxVerdict,syntaxBlankOut,Tape.writeAndMove,Tape.write,Tape.move,
          Tape.init,Function.update,hj]
  have hs : clearFlagTM.step ⟨false,a,w,syntaxVerdict b⟩ =
      some ⟨true,a,w,syntaxBlankOut⟩ := by
    simp only [TM.step,clearFlagTM]
    apply congrArg some
    exact Cfg.ext rfl hp.move_idle (funext (fun i => (hw i).writeAndMove_readBack_idle)) hout
  exact ⟨_,1,le_refl _,.step hs .zero,rfl,rfl,rfl,outAcc_nil_init⟩

def branchPrepareTM : TM 4 := seqTM rewindInputTM clearFlagTM

theorem branchPrepareTM_correct (z : List Bool) (b : Bool) :
    branchPrepareTM.HoareTime
      (fun inp work out => inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
        inp.head = z.length+1 ∧ work = (fun _ => regTape 0) ∧ out = syntaxVerdict b)
      (EmitPred ⟨1,(Tape.init (z.map Γ.ofBool)).cells⟩ (fun _ => regTape 0) [])
      (z.length+5) := by
  intro inp work out hpre
  rcases hpre with ⟨hc,hh,rfl,rfl⟩
  let P := fun (a : Tape) (w : Fin 4 → Tape) (o : Tape) =>
    a.cells = (Tape.init (z.map Γ.ofBool)).cells ∧ w = (fun _ => regTape 0) ∧ o = syntaxVerdict b
  have hpres : ∀ a w o a' w' o', P a w o → a'.cells = a.cells → a'.head = 1 →
      w' = w → o' = o → P a' w' o' := by
    rintro a w o a' w' o' ⟨ha,hw,ho⟩ he _ rfl rfl
    exact ⟨he.trans ha,hw,ho⟩
  obtain ⟨c,t,ht,hr,hhalt,hhead,hcells,hwork,houtput⟩ :=
    rewindInputTM_hoareTime_frame (z.length+1) hpres inp (fun _ => regTape 0)
      (syntaxVerdict b) ⟨by rw [hc]; rfl,by rw [hc]; exact Tape.init_ofBool_cells_ne_start z,
        by omega,(syntaxVerdict_parked b).read_ne_start,(syntaxVerdict_parked b).1,
        fun _ => ⟨(parked_regTape 0).read_ne_start,by rfl⟩,hc,rfl,rfl⟩
  have hi : c.input = (⟨1,(Tape.init (z.map Γ.ofBool)).cells⟩ : Tape) := Tape.ext hhead hcells
  have hp : Parked c.input := by rw [hi]; exact parked_init_input z
  have hwp : ∀ i, Parked (c.work i) := by rw [hwork]; exact fun _ => parked_regTape 0
  have hop : Parked c.output := by rw [houtput]; exact syntaxVerdict_parked b
  obtain ⟨d,s,hs,hsr,hsh,hsi,hsw,hso⟩ := clearFlagTM_correct c.input c.work b hp hwp
    c.input c.work c.output ⟨rfl,rfl,houtput⟩
  have hwt : (fun i => transitionTape (c.work i)) = c.work :=
    funext (fun i => (hwp i).transitionTape_eq_self)
  have hseq := seqTM_reachesIn_of_reachesIn (rewindInputTM (n := 4)) clearFlagTM hr hhalt (by
    simpa only [hp.transitionInput_eq_self,hwt,hop.transitionTape_eq_self] using hsr)
  exact ⟨phase2Wrap rewindInputTM clearFlagTM d,t+1+s,by omega,hseq,
    (phase2Wrap_halted_iff _ _ _).mpr hsh,hsi.trans hi,hsw.trans hwork,hso⟩

end IrrRAFEnumeration.SATSource
