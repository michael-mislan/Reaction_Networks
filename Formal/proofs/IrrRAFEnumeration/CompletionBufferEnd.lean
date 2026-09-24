import proofs.IrrRAFEnumeration.CompletionSATMinimize

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

/-- Find the append position of a stored Boolean buffer without copying it. -/
def seekBufferEndTM {k : Nat} (src : Fin k) : TM k where
  Q := Bool
  qstart := false
  qhalt := true
  δ := fun _ i w o =>
    (w src == Γ.blank,fun j => readBackWrite (w j),readBackWrite o,
      idleDir i,fun j => if j = src ∧ w src ≠ Γ.blank then .right else idleDir (w j),idleDir o)
  δ_right_of_start := by
    intro q i w o
    refine ⟨idleDir_right_of_start,?_,idleDir_right_of_start⟩
    intro j hj
    dsimp only
    split
    · rfl
    · exact idleDir_right_of_start hj

theorem seekBufferEnd_step {k : Nat} (src : Fin k) (inp : Tape)
    (work : Fin k → Tape) (out : Tape) (hp : Parked inp)
    (hw : ∀ i, Parked (work i)) (ho : Parked out) :
    (seekBufferEndTM src).step ⟨false,inp,work,out⟩ = some
      ⟨(work src).read == Γ.blank,inp,
        if (work src).read = Γ.blank then work
        else Function.update work src (advanceInput (work src) 1),out⟩ := by
  simp only [TM.step,seekBufferEndTM,Bool.false_eq_true,if_false]
  apply congrArg some
  refine Cfg.ext rfl hp.move_idle ?_ ho.writeAndMove_readBack_idle
  funext j
  by_cases hs : (work src).read = Γ.blank
  · simp only [hs,ne_eq,not_true_eq_false,and_false,if_false,if_true]
    exact (hw j).writeAndMove_readBack_idle
  · by_cases hj : j = src
    · subst j
      simp only [hs,ne_eq,not_false_eq_true,and_self,if_true,if_false,Function.update_self]
      exact writeAndMove_readBack _ (hw src).read_ne_start .right
    · simp only [hj,false_and,if_false,hs,Function.update_of_ne hj]
      exact (hw j).writeAndMove_readBack_idle

theorem seekBufferEndTM_correct {k : Nat} (src : Fin k) (xs : List Bool)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i)) (hx : BufferChunk xs (work src)) :
    (seekBufferEndTM src).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work src (advanceInput (work src) xs.length)) ys)
      (xs.length+1) := by
  induction xs generalizing work with
  | nil =>
    rintro a w out ⟨ha,hww,ho⟩
    subst a
    subst w
    have hr : (work src).read = Γ.blank := by simpa [BufferChunk,Tape.read] using hx.2
    have hs := seekBufferEnd_step src inp work out hp hw ho.parked
    simp only [hr,beq_self_eq_true,if_true] at hs
    refine ⟨⟨true,inp,work,out⟩,1,le_rfl,.step hs .zero,rfl,rfl,?_,ho⟩
    simp [advanceInput]
  | cons bit xs ih =>
    rintro a w out ⟨ha,hww,ho⟩
    subst a
    subst w
    have hr : (work src).read = Γ.ofBool bit := by
      simpa [Tape.read] using hx.1 0 (by simp)
    have hn : (work src).read ≠ Γ.blank := by rw [hr]; cases bit <;> decide
    let W := Function.update work src (advanceInput (work src) 1)
    have hw' : ∀ i, Parked (W i) := by
      intro i
      by_cases hi : i = src
      · subst i
        simpa [W] using advanceInput_parked (work src) 1 (hw src)
      · simpa [W,Function.update_of_ne hi] using hw i
    have hx' : BufferChunk xs (W src) := by
      constructor
      · intro i hi
        have h := hx.1 (i+1) (by simpa using hi)
        simpa [W,advanceInput,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
      · simpa [W,advanceInput,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hx.2
    obtain ⟨c,t,ht,hrun,hh,ha,hww,ho'⟩ := ih W hw' hx' inp W out ⟨rfl,rfl,ho⟩
    have hs := seekBufferEnd_step src inp work out hp hw ho.parked
    simp only [hn,beq_eq_false_iff_ne.mpr hn,if_false] at hs
    have he : Function.update W src (advanceInput (W src) xs.length) =
        Function.update work src (advanceInput (work src) (bit::xs).length) := by
      have he' : advanceInput (advanceInput (work src) 1) xs.length =
          advanceInput (work src) (bit::xs).length := by
        apply Tape.ext
        · dsimp [advanceInput]
          omega
        · rfl
      simpa only [W,Function.update_self,Function.update_idem] using
        congrArg (Function.update work src) he'
    exact ⟨c,t+1,by simp only [List.length_cons]; omega,.step hs hrun,hh,ha,hww.trans he,ho'⟩

end IrrRAFEnumeration.CompletionQuery
