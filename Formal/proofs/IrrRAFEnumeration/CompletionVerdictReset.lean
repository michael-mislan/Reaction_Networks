import proofs.IrrRAFEnumeration.CompletionBoundedCleanup

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

def verdictNat (s : Γ) : Nat := if s = Γ.one then 1 else 0

/-- Save the yes/no interpretation into a fresh unary flag register. -/
def saveVerdictTM {n : Nat} (src flag : Fin n) : TM n where
  Q := Bool
  qstart := false
  qhalt := true
  δ := fun _ i w o =>
    (true,fun j => if j = flag then (if w src = Γ.one then .one else .blank)
      else readBackWrite (w j),readBackWrite o,
      idleDir i,fun j => idleDir (w j),idleDir o)
  δ_right_of_start := fun _ _ _ _ =>
    ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩

theorem flagWrite (s : Γ) :
    (regTape 0).writeAndMove (if s = Γ.one then Γ.one else Γ.blank) .stay =
      regTape (verdictNat s) := by
  apply Tape.ext
  · rfl
  · funext j
    by_cases hj0 : j = 0
    · subst j
      simp [Tape.writeAndMove,Tape.write,Tape.move,regTape,regCells]
    · by_cases hj1 : j = 1
      · subst j
        by_cases hs : s = Γ.one <;>
          simp [Tape.writeAndMove,Tape.write,Tape.move,regTape,regCells,verdictNat,hs]
      · have hj : 1 < j := by omega
        by_cases hs : s = Γ.one <;>
          simp [Tape.writeAndMove,Tape.write,Tape.move,regTape,regCells,verdictNat,
            hs,hj0,hj1,show ¬j ≤ 1 by omega]

theorem saveVerdictTM_correct {n : Nat} (src flag : Fin n)
    (inp : Tape) (work : Fin n → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ j, Parked (work j)) (hf : work flag = regTape 0) :
    (saveVerdictTM src flag).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work flag (regTape (verdictNat (work src).read))) ys) 1 := by
  rintro a w out ⟨ha,hww,ho⟩
  subst a
  subst w
  have hs : (saveVerdictTM src flag).step ⟨false,inp,work,out⟩ = some
      ⟨true,inp,Function.update work flag (regTape (verdictNat (work src).read)),out⟩ := by
    simp only [TM.step,saveVerdictTM,Bool.false_eq_true,if_false]
    apply congrArg some
    refine Cfg.ext rfl hp.move_idle ?_ ho.parked.writeAndMove_readBack_idle
    funext j
    by_cases hj : j = flag
    · subst j
      simp only [ite_true,Function.update_self]
      have hidle : idleDir (work flag).read = .stay := by
        simp [idleDir,(hw flag).read_ne_start]
      rw [hidle]
      have he : (↑(if (work src).read = Γ.one then Γw.one else Γw.blank) : Γ) =
          (if (work src).read = Γ.one then Γ.one else Γ.blank) := by split <;> rfl
      rw [he,hf]
      exact flagWrite _
    · simp only [if_neg hj,Function.update_of_ne hj]
      exact (hw j).writeAndMove_readBack_idle
  exact ⟨_,1,le_rfl,.step hs .zero,rfl,rfl,rfl,ho⟩

/-- Capture before clearing the solver's output buffer; the flag survives. -/
def verdictClearTM {n : Nat} (fuel src flag : Fin n) : TM n :=
  seqTM (saveVerdictTM src flag) (boundedClearTM fuel src)

theorem verdictClearTM_correct {n : Nat} (fuel src flag : Fin n)
    (hsf : src ≠ fuel) (hfl : flag ≠ fuel) (hsflag : src ≠ flag)
    (bound : Nat) (inp : Tape) (work : Fin n → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ j, Parked (work j))
    (hf : work fuel = regTape bound) (hflag : work flag = regTape 0)
    (hh : (work src).head = 1) (hs : (work src).cells 0 = Γ.start)
    (ht : ∀ j, bound < j → (work src).cells j = Γ.blank) :
    (verdictClearTM fuel src flag).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update
        (Function.update work flag (regTape (verdictNat ((work src).cells 1))))
        src (parkedInput [])) ys) (5*bound+8) := by
  let W := Function.update work flag (regTape (verdictNat (work src).read))
  have hw' : ∀ i, Parked (W i) := by
    intro i
    by_cases hi : i = flag
    · subst i
      simpa [W] using parked_regTape (verdictNat (work src).read)
    · simpa [W,Function.update_of_ne hi] using hw i
  have h1 := saveVerdictTM_correct src flag inp work ys hp hw hflag
  have h2 := boundedClearTM_correct fuel src hsf bound inp W ys hp hw'
    (by simpa [W,Function.update_of_ne (Ne.symm hfl)] using hf)
    (by simpa [W,Function.update_of_ne hsflag] using hh)
    (by simpa [W,Function.update_of_ne hsflag] using hs)
    (by simpa [W,Function.update_of_ne hsflag] using ht)
  have hall := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw' ys) h2
  have hr : (work src).read = (work src).cells 1 := by simp [Tape.read,hh]
  have hall' := hall.mono_bound (by omega : 1+1+(5*bound+6) ≤ 5*bound+8)
  simpa only [verdictClearTM,W,hr] using hall'

/-- Rewind an exited solver-output buffer, save its verdict, then erase it. -/
def verdictResetTM {n : Nat} (fuel src flag : Fin n) : TM n :=
  seqTM (rewindWorkTM src) (verdictClearTM fuel src flag)

theorem verdictResetTM_correct {n : Nat} (fuel src flag : Fin n)
    (hsf : src ≠ fuel) (hfl : flag ≠ fuel) (hsflag : src ≠ flag)
    (bound : Nat) (inp : Tape) (work : Fin n → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ j, Parked (work j))
    (hf : work fuel = regTape bound) (hflag : work flag = regTape 0)
    (hs : (work src).cells 0 = Γ.start)
    (ht : ∀ j, bound < j → (work src).cells j = Γ.blank) :
    (verdictResetTM fuel src flag).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update
        (Function.update work flag (regTape (verdictNat ((work src).cells 1))))
        src (parkedInput [])) ys) ((work src).head+5*bound+11) := by
  let W := Function.update work src (⟨1,(work src).cells⟩ : Tape)
  have hw' : ∀ i, Parked (W i) := by
    intro i
    by_cases hi : i = src
    · subst i
      exact ⟨by simp [W],by simpa [W] using (hw src).2⟩
    · simpa [W,Function.update_of_ne hi] using hw i
  have hr := rewindBuffer_correct src inp W ys ((work src).head-1) hp hw'
    (by simp [W]) (by simpa [W] using hs)
  have he : Function.update W src (advanceInput (W src) ((work src).head-1)) = work := by
    funext i
    by_cases hi : i = src
    · subst i
      apply Tape.ext
      · have := (hw src).1
        dsimp [W,advanceInput]
        simp only [Function.update_self]
        omega
      · simp [W,advanceInput]
    · simp [W,Function.update_of_ne hi]
  rw [he] at hr
  have hc := verdictClearTM_correct fuel src flag hsf hfl hsflag bound inp W ys hp hw'
    (by simpa [W,Function.update_of_ne (Ne.symm hsf)] using hf)
    (by simpa [W,Function.update_of_ne (Ne.symm hsflag)] using hflag)
    (by simp [W]) (by simpa [W] using hs) (by simpa [W] using ht)
  have hpost : Function.update
        (Function.update W flag (regTape (verdictNat ((W src).cells 1)))) src (parkedInput []) =
      Function.update (Function.update work flag (regTape (verdictNat ((work src).cells 1))))
        src (parkedInput []) := by
    funext i
    by_cases hi : i = src
    · subst i
      simp
    · by_cases hif : i = flag
      · subst i
        simp [W,Function.update_of_ne (Ne.symm hsflag)]
      · simp [W,Function.update_of_ne hi,Function.update_of_ne hif]
  rw [hpost] at hc
  have hhead := (hw src).1
  exact (seqTM_hoareTime _ _ hr (emitPred_transition hp hw' ys) hc).mono_bound (by omega)

end IrrRAFEnumeration.CompletionQuery
