import proofs.IrrRAFEnumeration.CompletionMaskEdit

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

/-- A failed deletion from a viable container necessarily removed a member. -/
theorem rejectedDeletion_present {α : Type} [DecidableEq α] (P : Finset α → Prop)
    (U : Finset α) (j : α) (h : P U) (hn : ¬P (U.erase j)) : j ∈ U := by
  by_contra hnot
  have he : U.erase j = U := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_erase.mp hx).2
    · intro hx
      refine Finset.mem_erase.mpr ⟨?_,hx⟩
      intro hEq
      subst x
      exact hnot hx
  rw [he] at hn
  exact hn h

theorem rejectedDeletion_restore {α : Type} [DecidableEq α] (P : Finset α → Prop)
    (U : Finset α) (j : α) (h : P U) (hn : ¬P (U.erase j)) : insert j (U.erase j) = U :=
  Finset.insert_erase (rejectedDeletion_present P U j h hn)

theorem editedMask_set {r : Nat} (U : Finset (Fin r)) (j : Fin r) (bit : Bool) :
    editedTape (parkedInput (containerMask U)) j.val (if bit then Γw.one else Γw.zero) =
      parkedInput (containerMask (if bit then insert j U else U.erase j)) := by
  apply Tape.ext
  · rfl
  · funext l
    cases l with
    | zero =>
      change Function.update _ (1+j.val) _ 0 = _
      rw [Function.update_of_ne (by omega : 0 ≠ 1+j.val)]
      rfl
    | succ l =>
      change Function.update (parkedInput (containerMask U)).cells (1+j.val)
        (if bit then Γw.one else Γw.zero).toΓ (l+1) =
        (parkedInput (containerMask (if bit then insert j U else U.erase j))).cells (l+1)
      by_cases hl : l < r
      · by_cases he : l = j.val
        · subst l
          rw [Nat.add_comm j.val 1,Function.update_self]
          cases bit <;> simp [containerMask_cell,Γ.ofBool]
        · have he' : l+1 ≠ 1+j.val := by omega
          rw [Function.update_of_ne he']
          have hfin : (⟨l,hl⟩ : Fin r) ≠ j := by
            intro h
            exact he (congrArg Fin.val h)
          have hOld := containerMask_cell U (⟨l,hl⟩ : Fin r)
          have hNew := containerMask_cell (if bit then insert j U else U.erase j) (⟨l,hl⟩ : Fin r)
          rw [Nat.add_comm l 1,hOld,hNew]
          cases bit <;> simp [hfin]
      · have hj := j.isLt
        have he : l+1 ≠ 1+j.val := by omega
        rw [Function.update_of_ne he]
        have hOld := Tape.init_ofBool_cells_ge (containerMask U) l (by simp [containerMask]; omega)
        have hNew := Tape.init_ofBool_cells_ge
          (containerMask (if bit then insert j U else U.erase j)) l (by simp [containerMask]; omega)
        exact hOld.trans hNew.symm

theorem editContainerTM_correct {n r : Nat} (address dst : Fin n) (hne : dst ≠ address)
    (U : Finset (Fin r)) (j : Fin r) (bit : Bool)
    (inp : Tape) (work : Fin n → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (ha : work address = regTape j.val) (hm : work dst = parkedInput (containerMask U)) :
    (editWorkTM address dst (if bit then Γw.one else Γw.zero)).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work dst
        (parkedInput (containerMask (if bit then insert j U else U.erase j)))) ys) (5*j.val+8) := by
  have h := editWorkTM_correct address dst hne j.val (if bit then Γw.one else Γw.zero)
    inp work ys hp hw ha (by simp [hm,parkedInput]) (by simp [hm,parkedInput,Tape.init])
  simpa only [hm,editedMask_set] using h

end IrrRAFEnumeration.CompletionQuery
