import proofs.IrrRAFEnumeration.CompletionResultClear

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

theorem advanceInput_zero (t : Tape) : advanceInput t 0 = t := by rfl

def advanceWorkStepTM {n : Nat} (dst : Fin n) : TM n where
  Q := Bool
  qstart := false
  qhalt := true
  δ := fun _ i w o =>
    (true,fun j => readBackWrite (w j),readBackWrite o,
      idleDir i,fun j => if j = dst then .right else idleDir (w j),idleDir o)
  δ_right_of_start := by
    intro q i w o
    refine ⟨idleDir_right_of_start,?_,idleDir_right_of_start⟩
    intro j hj
    by_cases h : j = dst
    · simp [h]
    · simpa [h] using idleDir_right_of_start hj

theorem advanceWorkStepTM_correct {n : Nat} (dst : Fin n) (inp : Tape)
    (work : Fin n → Tape) (ys : List Bool) (hp : Parked inp)
    (hw : ∀ j, Parked (work j)) :
    (advanceWorkStepTM dst).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work dst ((work dst).move .right)) ys) 1 := by
  rintro a w out ⟨ha,hww,ho⟩
  subst a
  subst w
  have hs : (advanceWorkStepTM dst).step ⟨false,inp,work,out⟩ = some
      ⟨true,inp,Function.update work dst ((work dst).move .right),out⟩ := by
    simp only [TM.step,advanceWorkStepTM,Bool.false_eq_true,if_false]
    apply congrArg some
    refine Cfg.ext rfl hp.move_idle ?_ ho.parked.writeAndMove_readBack_idle
    funext j
    by_cases hj : j = dst
    · subst j
      simp only [Function.update_self]
      exact writeAndMove_readBack _ (hw dst).read_ne_start _
    · simp only [hj,if_false,Function.update_of_ne hj]
      exact (hw j).writeAndMove_readBack_idle
  exact ⟨_,1,le_rfl,.step hs .zero,rfl,rfl,rfl,ho⟩

/-- Advance by the value of a preserved unary address register. -/
def advanceWorkTM {n : Nat} (fuel dst : Fin n) : TM n := forRegTM (advanceWorkStepTM dst) fuel

theorem advanceWorkTM_correct {n : Nat} (fuel dst : Fin n) (hne : dst ≠ fuel)
    (bound : Nat) (inp : Tape) (work : Fin n → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ j, Parked (work j)) (hf : work fuel = regTape bound) :
    (advanceWorkTM fuel dst).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work dst (advanceInput (work dst) bound)) ys)
      (4*bound+2) := by
  let W := fun i => Function.update work dst (advanceInput (work dst) i)
  have hwp : ∀ i j, Parked (W i j) := by
    intro i j
    by_cases hj : j = dst
    · subst j
      simpa [W] using advanceInput_parked (work dst) i (hw dst)
    · simpa [W,Function.update_of_ne hj] using hw j
  have hbody : ∀ i, i < bound → (advanceWorkStepTM dst).HoareTime
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
    have h := advanceWorkStepTM_correct dst inp V ys hp hv
    have he : Function.update V dst ((V dst).move .right) =
        Function.update (W (i+1)) fuel ⟨i+2,regCells bound⟩ := by
      funext j
      by_cases hj : j = dst
      · subst j
        simp only [V,Function.update_self,Function.update_of_ne hne,W]
        exact advanceInput_move (work dst) i
      · by_cases hjf : j = fuel
        · subst j
          simp [V,W,Ne.symm hne]
        · simp [V,W,Function.update_of_ne hj,Function.update_of_ne hjf]
    rw [he] at h
    exact h
  have h := forRegTM_hoareTime (advanceWorkStepTM dst) fuel bound inp W (fun _ => ys) 1 hp
    (fun i => by simp [W,Function.update_of_ne (Ne.symm hne),hf])
    (fun i j _ => hwp i j) hbody
  have hcost : bound*(1+2)+(bound+2) = 4*bound+2 := by omega
  simpa only [advanceWorkTM,W,advanceInput_zero,Function.update_eq_self,hcost] using h


end IrrRAFEnumeration.CompletionQuery
