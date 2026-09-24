import proofs.IrrRAFEnumeration.CompletionInitialPlacement
import proofs.IrrRAFEnumeration.CompletionOriginalApplication

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def initCountSource (k : Nat) : Fin (enumTapes k+24) := ⟨enumTapes k+13,by omega⟩
def initSmall (k : Nat) (i : Fin 7) : Fin (enumTapes k+24) :=
  ⟨i.val,by have := i.isLt; unfold enumTapes bufferedCount; omega⟩
def initFuel (k : Nat) : Fin (enumTapes k+24) :=
  ⟨bufferedCount k+1,by unfold enumTapes; omega⟩

def initialRegisterTM (k : Nat) : TM (enumTapes k+24) :=
  seqTM (copyIntoTM (initCountSource k) (initSmall k 0))
    (seqTM (copyIntoTM (initCountSource k) (initSmall k 4))
      (seqTM (copyIntoTM (initCountSource k) (initFuel k))
        (setConstTM (initSmall k 1) 1)))

def initialRegisterWork (k r : Nat) (work : Fin (enumTapes k+24) → Tape) :=
  Function.update (Function.update (Function.update (Function.update work
    (initSmall k 0) (regTape r)) (initSmall k 4) (regTape r))
      (initFuel k) (regTape r)) (initSmall k 1) (regTape 1)

theorem initialRegisterTM_correct (k r : Nat) (inp : Tape)
    (work : Fin (enumTapes k+24) → Tape)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (hs : work (initCountSource k) = regTape r)
    (h0 : work (initSmall k 0) = regTape 0)
    (h4 : work (initSmall k 4) = regTape 0)
    (hf : work (initFuel k) = regTape 0)
    (h1 : work (initSmall k 1) = regTape 0) :
    (initialRegisterTM k).HoareTime (EmitPred inp work [])
      (EmitPred inp (initialRegisterWork k r work) []) (6*r*r+21*r+37) := by
  have hs0 : initCountSource k ≠ initSmall k 0 := by
    intro h; have := congrArg Fin.val h; dsimp [initCountSource,initSmall,enumTapes,bufferedCount] at this; omega
  have hs4 : initCountSource k ≠ initSmall k 4 := by
    intro h; have := congrArg Fin.val h; dsimp [initCountSource,initSmall,enumTapes,bufferedCount] at this; omega
  have hsf : initCountSource k ≠ initFuel k := by
    intro h; have := congrArg Fin.val h; dsimp [initCountSource,initFuel,enumTapes] at this; omega
  have hf0 : initFuel k ≠ initSmall k 0 := by
    intro h; have := congrArg Fin.val h; dsimp [initFuel,initSmall,bufferedCount] at this; omega
  have hf4 : initFuel k ≠ initSmall k 4 := by
    intro h; have := congrArg Fin.val h; dsimp [initFuel,initSmall,bufferedCount] at this; omega
  have h1f : initSmall k 1 ≠ initFuel k := by
    intro h
    have he : 1 = bufferedCount k+1 := congrArg Fin.val h
    unfold bufferedCount at he
    omega
  have h40 : initSmall k 4 ≠ initSmall k 0 := by simp [initSmall,Fin.ext_iff]
  have h10 : initSmall k 1 ≠ initSmall k 0 := by simp [initSmall]
  have h14 : initSmall k 1 ≠ initSmall k 4 := by simp [initSmall,Fin.ext_iff]
  let W₁ := Function.update work (initSmall k 0) (regTape r)
  let W₂ := Function.update W₁ (initSmall k 4) (regTape r)
  let W₃ := Function.update W₂ (initFuel k) (regTape r)
  have hw₁ := updateReg_parked work hw (initSmall k 0) r
  have hw₂ := updateReg_parked W₁ hw₁ (initSmall k 4) r
  have hw₃ := updateReg_parked W₂ hw₂ (initFuel k) r
  have ha := copyIntoTM_hoareTime (initCountSource k) (initSmall k 0) hs0 r 0
    inp work [] hp (fun i _ => hw i) hs h0
  have hb := copyIntoTM_hoareTime (initCountSource k) (initSmall k 4) hs4 r 0
    inp W₁ [] hp (fun i _ => hw₁ i)
    (by simp [W₁,Function.update_of_ne hs0,hs])
    (by simp [W₁,Function.update_of_ne h40,h4])
  have hc := copyIntoTM_hoareTime (initCountSource k) (initFuel k) hsf r 0
    inp W₂ [] hp (fun i _ => hw₂ i)
    (by simp [W₂,W₁,Function.update_of_ne hs0,Function.update_of_ne hs4,hs])
    (by simp [W₂,W₁,Function.update_of_ne hf0,Function.update_of_ne hf4,hf])
  have hd := setConstTM_hoareTime (initSmall k 1) 1 0 inp W₃ [] hp hw₃
    (by simp [W₃,W₂,W₁,Function.update_of_ne h1f,Function.update_of_ne h10,Function.update_of_ne h14,h1])
  have hcd := seqTM_hoareTime _ _ hc (emitPred_transition hp hw₃ []) hd
  have hbcd := seqTM_hoareTime _ _ hb (emitPred_transition hp hw₂ []) hcd
  have h := seqTM_hoareTime _ _ ha (emitPred_transition hp hw₁ []) hbcd
  apply h.mono_bound
  ring_nf
  omega

/-- The full-container mask is exactly the unary count tape, including r=0. -/
theorem fullMask_regTape (r : Nat) :
    parkedInput (containerMask (Finset.univ : Finset (Fin r))) = regTape r := by
  have hmask : containerMask (Finset.univ : Finset (Fin r)) = List.replicate r true := by
    simp [containerMask,List.ofFn_const]
  rw [hmask]
  apply Tape.ext
  · rfl
  · funext i
    by_cases hi : i = 0
    · subst i; rfl
    · by_cases hir : i ≤ r
      · have hil : i-1 < r := by omega
        simp [parkedInput,Tape.init,regTape,regCells,hi,hir,hil,Γ.ofBool]
      · have hil : ¬i-1 < r := by omega
        simp [parkedInput,Tape.init,regTape,regCells,hi,hir,hil]

/-- Exact flattening of the consumer's initial prefix. -/
theorem enumWork_initial_cell (k r : Nat) (base : List Bool) (i : Fin (enumTapes k)) :
    enumWork k (Finset.univ : Finset (Fin r)) base [] [] 0 0 i =
      if i.val = 0 then regTape r
      else if i.val = 1 then regTape 1
      else if i.val = 4 then regTape r
      else if i.val = 5 then parkedInput base
      else if i.val = bufferedCount k+1 then regTape r
      else regTape 0 := by
  have hz : accumulatorTape [] = regTape 0 := reg_zero_init_bumped.eq_regT
  have hlow (j : Fin 10) :
      enumWork k (Finset.univ : Finset (Fin r)) base [] [] 0 0
        ⟨j.val,by have := j.isLt; omega⟩ =
        if j.val = 0 then regTape r else if j.val = 1 then regTape 1
        else if j.val = 4 then regTape r else if j.val = 5 then parkedInput base
        else regTape 0 := by
    fin_cases j <;>
      simp [enumWork,minimizeWork,trialWork,completionWork,bufferedWork,
        queryDecisionWork,queryPrefix,dynamicWork,frameWork,completionFlag,
        maskWork,fullMask_regTape,hz,← regTape_zero_eq_parked,bufferedCount] <;>
        (try split_ifs) <;> first | rfl | omega | simp
  by_cases hi : i.val < 10
  · have hf : i.val ≠ bufferedCount k+1 := by unfold bufferedCount; omega
    simpa only [Fin.val_mk,hf,if_false] using hlow ⟨i.val,hi⟩
  · have h0 : i.val ≠ 0 := by omega
    have h1 : i.val ≠ 1 := by omega
    have h3 : i.val ≠ 3 := by omega
    have h4 : i.val ≠ 4 := by omega
    have h5 : i.val ≠ 5 := by omega
    simp only [h0,h1,h4,h5,if_false]
    by_cases hb : i.val < bufferedCount k
    · have hb1 : i.val < bufferedCount k+1 := by omega
      have hb2 : i.val < (bufferedCount k+1)+1 := by omega
      have hb3 : i.val < ((bufferedCount k+1)+1)+1 := by omega
      have hf : i.val ≠ bufferedCount k+1 := by omega
      simp only [enumWork,minimizeWork,trialWork,frameWork,hb,hb1,hb2,hb3,
        ↓reduceDIte,Function.update_apply,completionFlag,Fin.ext_iff,Fin.val_mk,
        h3,hf,if_false]
      exact (completionWork_high k Finset.univ base [] ⟨i.val,hb⟩ (by change 10 ≤ i.val; omega)).trans
        regTape_zero_eq_parked.symm
    · by_cases hf : i.val = bufferedCount k+1
      · simp [enumWork,minimizeWork,frameWork,hf]
      · have he : (i.val < bufferedCount k+1+1) ↔ (i.val < bufferedCount k+1) := by omega
        simp only [enumWork,minimizeWork,trialWork,frameWork,hb,hf,if_false,he]
        split_ifs <;> first | rfl | exact hz | (exfalso; simp_all)

end IrrRAFEnumeration.CompletionQuery
