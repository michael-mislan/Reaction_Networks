import proofs.IrrRAFEnumeration.CompletionQueryRouting

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

/-- A solver may halt with a head on the sentinel. Normalize only that case. -/
def normalizeScratchHead (t : Tape) : Tape := ⟨max 1 t.head,t.cells⟩

theorem normalizeScratchHead_parked (t : Tape) (hs : t.StartInvariant) :
    Parked (normalizeScratchHead t) := ⟨Nat.le_max_left _ _,hs.2⟩

theorem normalizeScratchHead_eq (t : Tape) (hp : Parked t) :
    normalizeScratchHead t = t := by
  apply Tape.ext
  · exact max_eq_right hp.1
  · rfl

theorem normalizeScratchHead_action (t : Tape) (hs : t.StartInvariant) :
    t.writeAndMove (readBackWrite t.read) (idleDir t.read) = normalizeScratchHead t := by
  by_cases hh : t.head = 0
  · have hr : t.read = Γ.start := by simpa [Tape.read,hh] using hs.1
    simp [Tape.writeAndMove,Tape.write,hh,idleDir,hr,Tape.move,normalizeScratchHead]
  · have hp : Parked t := ⟨by omega,hs.2⟩
    rw [hp.writeAndMove_readBack_idle,normalizeScratchHead_eq t hp]

/-- One existing skip step parks all scratch heads, preserves all cells,
and leaves already parked persistent tapes unchanged. -/
theorem normalizeScratchTM_correct {n : Nat} (inp : Tape) (work : Fin n → Tape)
    (ys : List Bool) (hp : Parked inp) (hs : ∀ i, (work i).StartInvariant) :
    (skipTM (n := n)).HoareTime (EmitPred inp work ys)
      (EmitPred inp (fun i => normalizeScratchHead (work i)) ys) 1 := by
  rintro a w out ⟨ha,hww,ho⟩
  subst a
  subst w
  have hstep : (skipTM (n := n)).step ⟨.go,inp,work,out⟩ =
      some ⟨.done,inp,(fun i => normalizeScratchHead (work i)),out⟩ := by
    simp only [TM.step,skipTM,reduceCtorEq,if_false]
    apply congrArg some
    exact Cfg.ext rfl hp.move_idle
      (funext (fun i => normalizeScratchHead_action (work i) (hs i)))
      ho.parked.writeAndMove_readBack_idle
  exact ⟨_,1,le_rfl,.step hstep .zero,rfl,rfl,rfl,ho⟩

/-- A work cell beyond the run's head reach is untouched, even if scratch has gaps. -/
theorem workCells_far {n : Nat} {M : TM n} (idx : Fin n) {t : Nat}
    {c c' : Cfg n M.Q} (hr : M.reachesIn t c c') (j : Nat)
    (hj : (c.work idx).head+t < j) : (c'.work idx).cells j = (c.work idx).cells j := by
  induction hr with
  | zero => rfl
  | @step a b c t hs hr ih =>
    have hb : (b.work idx).head ≤ (a.work idx).head+1 :=
      M.work_head_reachesIn_bound (.step hs .zero) idx
    have he : (b.work idx).cells j = (a.work idx).cells j := by
      simp only [TM.step] at hs
      split at hs
      · simp at hs
      · simp only [Option.some.injEq] at hs
        rw [← hs]
        simp only [Tape.move_cells,Tape.write]
        split
        · rfl
        · change Function.update (a.work idx).cells (a.work idx).head _ j = _
          rw [Function.update_of_ne (by omega : j ≠ (a.work idx).head)]
    exact (ih (by omega)).trans he

theorem workCells_blank_after_run {n : Nat} {M : TM n} (idx : Fin n)
    {t bound : Nat} {c c' : Cfg n M.Q} (hr : M.reachesIn t c c')
    (hhead : (c.work idx).head+t ≤ bound)
    (htail : ∀ j, bound < j → (c.work idx).cells j = Γ.blank) :
    ∀ j, bound < j → (c'.work idx).cells j = Γ.blank := by
  intro j hj
  rw [workCells_far idx hr j (by omega)]
  exact htail j hj

/-- Erase exactly n cells starting at the current head, including blank gaps. -/
def erasedTape (t : Tape) (n : Nat) : Tape :=
  ⟨t.head+n,fun j => if t.head ≤ j ∧ j < t.head+n then Γ.blank else t.cells j⟩

theorem erasedTape_zero (t : Tape) : erasedTape t 0 = t := by
  apply Tape.ext
  · simp [erasedTape]
  · funext j
    have hn : ¬(t.head ≤ j ∧ j < t.head) := by omega
    simp [erasedTape,hn]

theorem erasedTape_parked (t : Tape) (n : Nat) (hp : Parked t) :
    Parked (erasedTape t n) := by
  constructor
  · dsimp [erasedTape]
    have := hp.1
    omega
  · intro j hj
    dsimp [erasedTape]
    split
    · decide
    · exact hp.2 j hj

theorem erasedTape_succ (t : Tape) (n : Nat) (hp : Parked t) :
    (erasedTape t n).writeAndMove Γ.blank .right = erasedTape t (n+1) := by
  have hn : (erasedTape t n).head ≠ 0 := by have := hp.1; dsimp [erasedTape]; omega
  apply Tape.ext
  · change ((erasedTape t n).write Γ.blank).head+1 = t.head+(n+1)
    rw [Tape.write_head]
    simp [erasedTape,Nat.add_assoc]
  · funext j
    simp only [Tape.writeAndMove,Tape.move_cells,Tape.write,hn,if_false]
    change Function.update (erasedTape t n).cells (t.head+n) Γ.blank j = _
    by_cases hj : j = t.head+n
    · subst j
      simp [erasedTape]
    · rw [Function.update_of_ne hj]
      change (if t.head ≤ j ∧ j < t.head+n then Γ.blank else t.cells j) =
        (if t.head ≤ j ∧ j < t.head+(n+1) then Γ.blank else t.cells j)
      by_cases hc : t.head ≤ j ∧ j < t.head+n
      · rw [if_pos hc,if_pos (by omega)]
      · rw [if_neg hc,if_neg (by omega)]

/-- One physical erase-and-advance, with every other tape preserved. -/
def eraseStepTM {n : Nat} (dst : Fin n) : TM n where
  Q := Bool
  qstart := false
  qhalt := true
  δ := fun _ i w o =>
    (true,fun j => if j = dst then .blank else readBackWrite (w j),readBackWrite o,
      idleDir i,fun j => if j = dst then .right else idleDir (w j),idleDir o)
  δ_right_of_start := by
    intro q i w o
    refine ⟨idleDir_right_of_start,?_,idleDir_right_of_start⟩
    intro j hj
    by_cases h : j = dst
    · simp [h]
    · simpa [h] using idleDir_right_of_start hj

theorem eraseStepTM_correct {n : Nat} (dst : Fin n) (inp : Tape)
    (work : Fin n → Tape) (ys : List Bool) (hp : Parked inp)
    (hw : ∀ j, Parked (work j)) :
    (eraseStepTM dst).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work dst ((work dst).writeAndMove Γ.blank .right)) ys) 1 := by
  rintro a w out ⟨ha,hww,ho⟩
  subst a
  subst w
  have hs : (eraseStepTM dst).step ⟨false,inp,work,out⟩ = some
      ⟨true,inp,Function.update work dst ((work dst).writeAndMove Γ.blank .right),out⟩ := by
    simp only [TM.step,eraseStepTM,Bool.false_eq_true,if_false]
    apply congrArg some
    refine Cfg.ext rfl hp.move_idle ?_ ho.parked.writeAndMove_readBack_idle
    funext j
    by_cases hj : j = dst
    · subst j
      simp
    · simp only [hj,if_false,Function.update_of_ne hj]
      exact (hw j).writeAndMove_readBack_idle
  exact ⟨_,1,le_rfl,.step hs .zero,rfl,rfl,rfl,ho⟩

/-- The fuel register, not scratch contents, controls the erasure length. -/
def boundedEraseTM {n : Nat} (fuel dst : Fin n) : TM n := forRegTM (eraseStepTM dst) fuel

theorem boundedEraseTM_correct {n : Nat} (fuel dst : Fin n) (hne : dst ≠ fuel)
    (bound : Nat) (inp : Tape) (work : Fin n → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ j, Parked (work j)) (hf : work fuel = regTape bound) :
    (boundedEraseTM fuel dst).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work dst (erasedTape (work dst) bound)) ys)
      (4*bound+2) := by
  let W := fun i => Function.update work dst (erasedTape (work dst) i)
  have hwp : ∀ i j, Parked (W i j) := by
    intro i j
    by_cases hj : j = dst
    · subst j
      simpa [W] using erasedTape_parked (work dst) i (hw dst)
    · simpa [W,Function.update_of_ne hj] using hw j
  have hbody : ∀ i, i < bound → (eraseStepTM dst).HoareTime
      (EmitPred inp (Function.update (W i) fuel ⟨i+2,regCells bound⟩) ys)
      (EmitPred inp (Function.update (W (i+1)) fuel ⟨i+2,regCells bound⟩) ys) 1 := by
    intro i _
    let V := Function.update (W i) fuel ⟨i+2,regCells bound⟩
    have hv : ∀ j, Parked (V j) := by
      intro j
      by_cases hj : j = fuel
      · subst j
        simpa [V] using (parked_regCells (v := bound) (h := i+2) (by omega))
      · simpa [V,Function.update_of_ne hj] using hwp i j
    have h := eraseStepTM_correct dst inp V ys hp hv
    have he : Function.update V dst ((V dst).writeAndMove Γ.blank .right) =
        Function.update (W (i+1)) fuel ⟨i+2,regCells bound⟩ := by
      funext j
      by_cases hj : j = dst
      · subst j
        simp only [V,Function.update_self,Function.update_of_ne hne,W]
        exact erasedTape_succ (work dst) i (hw dst)
      · by_cases hjf : j = fuel
        · subst j
          simp [V,W,Ne.symm hne]
        · simp [V,W,Function.update_of_ne hj,Function.update_of_ne hjf]
    rw [he] at h
    exact h
  have h := forRegTM_hoareTime (eraseStepTM dst) fuel bound inp W (fun _ => ys) 1 hp
    (fun i => by simp [W,Function.update_of_ne (Ne.symm hne),hf])
    (fun i j _ => hwp i j) hbody
  have hcost : bound*(1+2)+(bound+2) = 4*bound+2 := by omega
  simpa only [boundedEraseTM,W,erasedTape_zero,Function.update_eq_self,hcost] using h

theorem erasedTape_eq_blank (t : Tape) (bound : Nat) (hh : t.head = 1)
    (hs : t.cells 0 = Γ.start) (ht : ∀ j, bound < j → t.cells j = Γ.blank) :
    erasedTape t bound = advanceInput (parkedInput []) bound := by
  apply Tape.ext
  · simp [erasedTape,advanceInput,parkedInput,hh]
  · funext j
    by_cases hj : j = 0
    · subst j
      simp [erasedTape,hh,hs,advanceInput,parkedInput,Tape.init]
    · by_cases hb : j ≤ bound
      · have hin : t.head ≤ j ∧ j < t.head+bound := by rw [hh]; omega
        simp [erasedTape,hin,advanceInput,parkedInput,Tape.init,hj]
      · have hout : ¬(t.head ≤ j ∧ j < t.head+bound) := by rw [hh]; omega
        simp [erasedTape,hout,ht j (by omega),advanceInput,parkedInput,Tape.init,hj]

/-- Clear a bounded, potentially gapped tape and restore head 1. -/
def boundedClearTM {n : Nat} (fuel dst : Fin n) : TM n :=
  seqTM (boundedEraseTM fuel dst) (rewindWorkTM dst)

theorem boundedClearTM_correct {n : Nat} (fuel dst : Fin n) (hne : dst ≠ fuel)
    (bound : Nat) (inp : Tape) (work : Fin n → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ j, Parked (work j)) (hf : work fuel = regTape bound)
    (hh : (work dst).head = 1) (hs : (work dst).cells 0 = Γ.start)
    (ht : ∀ j, bound < j → (work dst).cells j = Γ.blank) :
    (boundedClearTM fuel dst).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work dst (parkedInput [])) ys) (5*bound+6) := by
  let W := Function.update work dst (parkedInput [])
  have hw' : ∀ i, Parked (W i) := by
    intro i
    by_cases hi : i = dst
    · subst i
      simpa [W] using parkedInput_parked []
    · simpa [W,Function.update_of_ne hi] using hw i
  have he := erasedTape_eq_blank (work dst) bound hh hs ht
  have h1 := boundedEraseTM_correct fuel dst hne bound inp work ys hp hw hf
  rw [he] at h1
  have h2 := rewindBuffer_correct dst inp W ys bound hp hw'
    (by simp [W,parkedInput]) (by simp [W,parkedInput,Tape.init])
  have hwiden : Function.update W dst (advanceInput (W dst) bound) =
      Function.update work dst (advanceInput (parkedInput []) bound) := by
    simp [W,Function.update_idem]
  rw [hwiden] at h2
  have hmid : ∀ i, Parked ((Function.update work dst (advanceInput (parkedInput []) bound)) i) := by
    intro i
    by_cases hi : i = dst
    · subst i
      simpa using advanceInput_parked (parkedInput []) bound (parkedInput_parked [])
    · simpa [Function.update_of_ne hi] using hw i
  exact (seqTM_hoareTime _ _ h1 (emitPred_transition hp hmid ys) h2).mono_bound (by omega)

/-- Normalize an arbitrary positive scratch head, clear its bounded support,
and return to the same canonical blank interface. -/
def resetScratchTM {n : Nat} (fuel dst : Fin n) : TM n :=
  seqTM (rewindWorkTM dst) (boundedClearTM fuel dst)

theorem resetScratchTM_correct {n : Nat} (fuel dst : Fin n) (hne : dst ≠ fuel)
    (bound : Nat) (inp : Tape) (work : Fin n → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ j, Parked (work j)) (hf : work fuel = regTape bound)
    (hs : (work dst).cells 0 = Γ.start)
    (ht : ∀ j, bound < j → (work dst).cells j = Γ.blank) :
    (resetScratchTM fuel dst).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work dst (parkedInput [])) ys)
      ((work dst).head+5*bound+9) := by
  let W := Function.update work dst (⟨1,(work dst).cells⟩ : Tape)
  have hw' : ∀ i, Parked (W i) := by
    intro i
    by_cases hi : i = dst
    · subst i
      exact ⟨by simp [W],by simpa [W] using (hw dst).2⟩
    · simpa [W,Function.update_of_ne hi] using hw i
  have hr := rewindBuffer_correct dst inp W ys ((work dst).head-1) hp hw'
    (by simp [W]) (by simpa [W] using hs)
  have he : Function.update W dst (advanceInput (W dst) ((work dst).head-1)) = work := by
    funext i
    by_cases hi : i = dst
    · subst i
      apply Tape.ext
      · have := (hw dst).1
        dsimp [W,advanceInput]
        simp only [Function.update_self]
        omega
      · simp [W,advanceInput]
    · simp [W,Function.update_of_ne hi]
  rw [he] at hr
  have hc := boundedClearTM_correct fuel dst hne bound inp W ys hp hw'
    (by simpa [W,Function.update_of_ne (Ne.symm hne)] using hf)
    (by simp [W]) (by simpa [W] using hs) (by simpa [W] using ht)
  have hpost : Function.update W dst (parkedInput []) =
      Function.update work dst (parkedInput []) := by simp [W,Function.update_idem]
  rw [hpost] at hc
  have hhead := (hw dst).1
  exact (seqTM_hoareTime _ _ hr (emitPred_transition hp hw' ys) hc).mono_bound (by omega)

end IrrRAFEnumeration.CompletionQuery
