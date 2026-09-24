import proofs.IrrRAFEnumeration.SATAdapterBranch

namespace IrrRAFEnumeration.GuardPreparation
open Complexity SAT Complexity.TM SATSource DeadlineFirstEntry

def clearVerdictTM (n : Nat) : TM n where
  Q := Bool
  qstart := false
  qhalt := true
  δ := fun _ i w o => (true,fun j => readBackWrite (w j),Γw.blank,
    idleDir i,fun j => idleDir (w j),idleDir o)
  δ_right_of_start := fun _ _ _ _ =>
    ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩

theorem clear_verdict_correct (n : Nat) (inp : Tape) (work : Fin n → Tape) (b : Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i)) :
    (clearVerdictTM n).HoareTime
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
  have hs : (clearVerdictTM n).step ⟨false,a,w,syntaxVerdict b⟩ =
      some ⟨true,a,w,syntaxBlankOut⟩ := by
    simp only [TM.step,clearVerdictTM]
    apply congrArg some
    exact Cfg.ext rfl hp.move_idle (funext (fun i => (hw i).writeAndMove_readBack_idle)) hout
  exact ⟨_,1,le_refl _,.step hs .zero,rfl,rfl,rfl,outAcc_nil_init⟩

def guardPrepareTM (n : Nat) : TM n := seqTM rewindInputTM (clearVerdictTM n)

def guardPre (n : Nat) (z : List Bool) (b : Bool) (inp : Tape) (work : Fin n → Tape) (out : Tape) :=
  inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧ inp.head = z.length+1 ∧
    work = (fun _ => regTape 0) ∧ out = syntaxVerdict b

theorem guard_prepare_correct (n : Nat) (z : List Bool) (b : Bool) :
    (guardPrepareTM n).HoareTime (guardPre n z b)
      (EmitPred ⟨1,(Tape.init (z.map Γ.ofBool)).cells⟩ (fun _ => regTape 0) []) (z.length+5) := by
  intro inp work out hpre
  rcases hpre with ⟨hc,hh,rfl,rfl⟩
  let P := fun (a : Tape) (w : Fin n → Tape) (o : Tape) =>
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
  obtain ⟨d,s,hs,hsr,hsh,hsi,hsw,hso⟩ := clear_verdict_correct n c.input c.work b hp hwp
    c.input c.work c.output ⟨rfl,rfl,houtput⟩
  have hwt : (fun i => transitionTape (c.work i)) = c.work :=
    funext (fun i => (hwp i).transitionTape_eq_self)
  have hseq := seqTM_reachesIn_of_reachesIn (rewindInputTM (n := n)) (clearVerdictTM n) hr hhalt (by
    simpa only [hp.transitionInput_eq_self,hwt,hop.transitionTape_eq_self] using hsr)
  exact ⟨phase2Wrap rewindInputTM (clearVerdictTM n) d,t+1+s,by omega,hseq,
    (phase2Wrap_halted_iff _ _ _).mpr hsh,hsi.trans hi,hsw.trans hwork,hso⟩

def startedTM {n : Nat} (tm : TM n) : TM n := { tm with qstart := firstState tm }

theorem started_run {n t : Nat} (tm : TM n) {c d : Cfg n tm.Q} (hr : tm.reachesIn t c d) :
    (startedTM tm).reachesIn t c d := by
  induction hr with
  | zero => exact .zero
  | step hs _ ih => exact .step hs ih

theorem started_from_run {n : Nat} (tm : TM n) (hne : tm.qstart ≠ tm.qhalt)
    (x : List Bool) (T : Nat) (P : Tape → Prop)
    (h : ∃ c t, t ≤ T ∧ tm.reachesIn t (tm.initCfg x) c ∧ tm.halted c ∧ P c.output) :
    (startedTM tm).HoareTime
      (EmitPred ⟨1,(Tape.init (x.map Γ.ofBool)).cells⟩ (fun _ => regTape 0) [])
      (fun _ _ out => P out ∧ out.StartInvariant) T := by
  rintro inp work out ⟨rfl,rfl,hout⟩
  have hoeq := hout.eq outAcc_nil_init
  obtain ⟨c,t,ht,hr,hh,ho⟩ := h
  have hn : t ≠ 0 := by
    intro he
    subst t
    cases hr
    exact hne hh
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have htail := started_run tm (positive_run_tail tm hne x hr)
  have hw : (fun _ : Fin n => regTape 0) = (firstCfg tm x).work :=
    funext (fun _ => reg_zero_init_bumped.eq_regT.symm)
  have hstart : ({
      state := (startedTM tm).qstart
      input := ⟨1,(Tape.init (x.map Γ.ofBool)).cells⟩
      work := fun _ => regTape 0
      output := out } : Cfg n (startedTM tm).Q) = firstCfg tm x := Cfg.ext rfl rfl hw hoeq
  refine ⟨c,s,by omega,hstart ▸ htail,hh,ho,?_,?_⟩
  · exact output_cells_zero_eq_start_of_reachesIn hr rfl
  · exact output_cells_ne_start_of_reachesIn hr Tape.StartInvariant.init_nil.2

end IrrRAFEnumeration.GuardPreparation
