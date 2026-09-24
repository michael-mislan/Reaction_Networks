import proofs.IrrRAFEnumeration.CompletionContainerEdit

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

/-- Conditional state mutation using the existing physical one-symbol branch. -/
theorem onRead_work_correct {n : Nat} (reader : Option (Fin n)) (symbol : Γ) (body : TM n)
    (inp : Tape) (work work' : Fin n → Tape) (ys : List Bool) (b : Nat)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (hb : body.HoareTime (EmitPred inp work ys) (EmitPred inp work' ys) b) :
    (onReadTM reader symbol body).HoareTime (EmitPred inp work ys)
      (EmitPred inp (if selectRead reader inp.read (fun i => (work i).read) = symbol
        then work' else work) ys) (b+1) := by
  rintro a w out ⟨ha,hww,ho⟩
  subst a
  subst w
  have he := onRead_entry reader symbol body inp work out hp hw ho.parked
  by_cases hs : selectRead reader inp.read (fun i => (work i).read) = symbol
  · rw [if_pos hs] at he
    obtain ⟨c,t,ht,hr,hh,ha,hww,ho⟩ := hb inp work out ⟨rfl,rfl,ho⟩
    have hl : (onReadTM reader symbol body).reachesIn t
        (onReadCfg reader symbol body ⟨body.qstart,inp,work,out⟩) (onReadCfg reader symbol body c) := by
      exact reachesIn_map (onReadCfg reader symbol body)
        (fun a b h => by rw [onRead_step,h]; rfl) hr
    refine ⟨onReadCfg reader symbol body c,t+1,by omega,.step he hl,?_,ha,?_,ho⟩
    · exact congrArg some hh
    · simpa [hs,onReadCfg] using hww
  · rw [if_neg hs] at he
    exact ⟨⟨some body.qhalt,inp,work,out⟩,1,by omega,.step he .zero,rfl,rfl,by simp [hs],ho⟩

def restoreRejectedTM {n : Nat} (address dst flag : Fin n) : TM n :=
  onReadTM (some flag) Γ.blank (editWorkTM address dst Γw.one)

/-- The negative verdict restores the old viable container; the positive verdict
keeps the deletion. No separate register storing the old membership bit is needed. -/
theorem restoreRejectedTM_correct {n r : Nat} (address dst flag : Fin n) (hne : dst ≠ address)
    (P : Finset (Fin r) → Prop) (U : Finset (Fin r)) (j : Fin r)
    (hU : P U) (v : Nat) (hv : v ≤ 1) (hanswer : v = 1 ↔ P (U.erase j))
    (inp : Tape) (work : Fin n → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (ha : work address = regTape j.val) (hm : work dst = parkedInput (containerMask (U.erase j)))
    (hf : work flag = regTape v) :
    (restoreRejectedTM address dst flag).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work dst
        (parkedInput (containerMask (if v = 1 then U.erase j else U)))) ys) (5*j.val+9) := by
  have hc := editContainerTM_correct address dst hne (U.erase j) j true inp work ys hp hw ha hm
  have h := onRead_work_correct (some flag) Γ.blank (editWorkTM address dst Γw.one) inp work
    (Function.update work dst (parkedInput (containerMask (insert j (U.erase j))))) ys
    (5*j.val+8) hp hw hc
  have hv' : v = 0 ∨ v = 1 := by omega
  rcases hv' with rfl | rfl
  · have hn : ¬P (U.erase j) := by
      intro hP
      have := hanswer.mpr hP
      omega
    have he := rejectedDeletion_restore P U j hU hn
    simpa [restoreRejectedTM,selectRead,hf,regTape,regCells,Tape.read,he] using h
  · simpa [restoreRejectedTM,selectRead,hf,regTape,regCells,Tape.read,← hm,
      Function.update_eq_self] using h

end IrrRAFEnumeration.CompletionQuery
