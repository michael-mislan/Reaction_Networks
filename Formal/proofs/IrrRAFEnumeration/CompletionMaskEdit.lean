import proofs.IrrRAFEnumeration.CompletionMaskMutation

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

def overwriteWorkTM {n : Nat} (dst : Fin n) (s : Γw) : TM n where
  Q := Bool
  qstart := false
  qhalt := true
  δ := fun _ i w o =>
    (true,fun j => if j = dst then s else readBackWrite (w j),readBackWrite o,
      idleDir i,fun j => idleDir (w j),idleDir o)
  δ_right_of_start := by
    intro q i w o
    exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩

theorem overwriteWorkTM_correct {n : Nat} (dst : Fin n) (s : Γw) (inp : Tape)
    (work : Fin n → Tape) (ys : List Bool) (hp : Parked inp) (hw : ∀ j, Parked (work j)) :
    (overwriteWorkTM dst s).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work dst ((work dst).write s.toΓ)) ys) 1 := by
  rintro a w out ⟨ha,hww,ho⟩
  subst a
  subst w
  have hs : (overwriteWorkTM dst s).step ⟨false,inp,work,out⟩ = some
      ⟨true,inp,Function.update work dst ((work dst).write s.toΓ),out⟩ := by
    simp only [TM.step,overwriteWorkTM,Bool.false_eq_true,if_false]
    apply congrArg some
    refine Cfg.ext rfl hp.move_idle ?_ ho.parked.writeAndMove_readBack_idle
    funext j
    by_cases hj : j = dst
    · subst j
      simp [Tape.writeAndMove,idleDir,(hw dst).read_ne_start,Tape.move]
    · simp only [if_neg hj,Function.update_of_ne hj]
      exact (hw j).writeAndMove_readBack_idle
  exact ⟨_,1,le_rfl,.step hs .zero,rfl,rfl,rfl,ho⟩

def editedTape (t : Tape) (j : Nat) (s : Γw) : Tape :=
  ⟨t.head,Function.update t.cells (t.head+j) s.toΓ⟩

theorem editedTape_parked (t : Tape) (j : Nat) (s : Γw) (hp : Parked t) :
    Parked (editedTape t j s) := by
  refine ⟨hp.1,?_⟩
  intro l hl
  by_cases he : l = t.head+j
  · subst l
    simp only [editedTape,Function.update_self]
    cases s <;> decide
  · simpa [editedTape,Function.update_of_ne he] using hp.2 l hl

theorem editedTape_start (t : Tape) (j : Nat) (s : Γw) (hp : Parked t)
    (hs : t.cells 0 = Γ.start) : (editedTape t j s).cells 0 = Γ.start := by
  have he : 0 ≠ t.head+j := by have := hp.1; omega
  simpa [editedTape,Function.update_of_ne he] using hs

theorem edit_at_advance (t : Tape) (j : Nat) (s : Γw) (hp : Parked t) :
    (advanceInput t j).write s.toΓ = advanceInput (editedTape t j s) j := by
  have he : (advanceInput t j).head ≠ 0 := by have := hp.1; dsimp [advanceInput]; omega
  rw [Tape.write,if_neg he]
  rfl

def editWorkTM {n : Nat} (address dst : Fin n) (s : Γw) : TM n :=
  seqTM (advanceWorkTM address dst) (seqTM (overwriteWorkTM dst s) (rewindWorkTM dst))

/-- Edit the addressed cell and return its head to one, with address and all
other tapes unchanged. The address is a runtime unary register, not a machine parameter. -/
theorem editWorkTM_correct {n : Nat} (address dst : Fin n) (hne : dst ≠ address)
    (j : Nat) (s : Γw) (inp : Tape) (work : Fin n → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i)) (ha : work address = regTape j)
    (hh : (work dst).head = 1) (hs : (work dst).cells 0 = Γ.start) :
    (editWorkTM address dst s).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work dst (editedTape (work dst) j s)) ys) (5*j+8) := by
  let W := Function.update work dst (advanceInput (work dst) j)
  let V := Function.update work dst (editedTape (work dst) j s)
  have hwp : ∀ i, Parked (W i) := by
    intro i
    by_cases hi : i = dst
    · subst i
      simpa [W] using advanceInput_parked (work dst) j (hw dst)
    · simpa [W,Function.update_of_ne hi] using hw i
  have hvp : ∀ i, Parked (V i) := by
    intro i
    by_cases hi : i = dst
    · subst i
      simpa [V] using editedTape_parked (work dst) j s (hw dst)
    · simpa [V,Function.update_of_ne hi] using hw i
  have h1 := advanceWorkTM_correct address dst hne j inp work ys hp hw ha
  have h2 := overwriteWorkTM_correct dst s inp W ys hp hwp
  have h3 := rewindBuffer_correct dst inp V ys j hp hvp
    (by simp [V,editedTape,hh])
    (by simpa [V] using editedTape_start (work dst) j s (hw dst) hs)
  have he : Function.update W dst ((W dst).write s.toΓ) =
      Function.update V dst (advanceInput (V dst) j) := by
    funext i
    by_cases hi : i = dst
    · subst i
      simp only [W,V,Function.update_self]
      exact edit_at_advance (work dst) j s (hw dst)
    · simp [W,V,Function.update_of_ne hi]
  rw [he] at h2
  have hmid : ∀ i, Parked (Function.update V dst (advanceInput (V dst) j) i) := by
    intro i
    by_cases hi : i = dst
    · subst i
      simpa using advanceInput_parked (V dst) j (hvp dst)
    · simpa [Function.update_of_ne hi] using hvp i
  have h23 := seqTM_hoareTime _ _ h2 (emitPred_transition hp hmid ys) h3
  exact (seqTM_hoareTime _ _ h1 (emitPred_transition hp hwp ys) h23).mono_bound (by omega)

end IrrRAFEnumeration.CompletionQuery
