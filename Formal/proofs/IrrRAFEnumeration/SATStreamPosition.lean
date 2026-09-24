import proofs.IrrRAFEnumeration.SATCopyRestore
import proofs.IrrRAFEnumeration.SATStreamCursor

namespace IrrRAFEnumeration.SATSource

open SATCompletion Complexity Complexity.TM

/-- Consume a true-unary header and its false delimiter on a work stream. -/
def skipWorkHeaderTM {k : Nat} (q : Fin k) : TM k where
  Q := BumpPhase
  qstart := .go
  qhalt := .done
  δ := fun _ ih wh oh =>
    (if wh q = Γ.one then .go else .done,
      fun i => readBackWrite (wh i),readBackWrite oh,idleDir ih,
      fun i => if i = q then .right else idleDir (wh i),idleDir oh)
  δ_right_of_start := by
    intro _ _ _ _
    refine ⟨idleDir_right_of_start,?_,idleDir_right_of_start⟩
    intro i hi
    by_cases he : i = q
    · simp [he]
    · simp [he,idleDir_right_of_start hi]

theorem skipWorkHeader_step {k : Nat} (q : Fin k) (bit : Bool)
    (inp : Tape) (work : Fin k → Tape) (out : Tape)
    (hp : Parked inp) (hw : ∀ i, Parked (work i)) (ho : Parked out)
    (hr : (work q).read = Γ.ofBool bit) :
    (skipWorkHeaderTM q).step {state := .go,input := inp,work := work,output := out} = some
      {state := if bit then .go else .done,input := inp,
       work := Function.update work q ((work q).move .right),output := out} := by
  have hs : (if (work q).read = Γ.one then BumpPhase.go else .done) =
      if bit then .go else .done := by rw [hr]; cases bit <;> rfl
  simp only [TM.step,skipWorkHeaderTM,reduceCtorEq,↓reduceIte]
  rw [hs]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl,hp.move_idle,?_,ho.writeAndMove_readBack_idle⟩)
  funext i
  by_cases he : i = q
  · subst i
    simpa only [if_pos rfl,Function.update_self] using parked_writeBack_right (work q) (hw q)
  · simpa only [if_neg he,Function.update_of_ne he] using (hw i).writeAndMove_readBack_idle

theorem skipWorkHeader_correct {k : Nat} (q : Fin k) (v : Nat)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (hones : ∀ i, i < v → (work q).cells ((work q).head+i) = Γ.one)
    (hend : (work q).cells ((work q).head+v) = Γ.zero) :
    (skipWorkHeaderTM q).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work q (advanceInput (work q) (v+1))) ys) (v+1) := by
  rintro input w out ⟨hi,he,ho⟩
  subst input
  subst w
  let W := fun i => Function.update work q (advanceInput (work q) i)
  let C : Nat → Cfg k (skipWorkHeaderTM q).Q := fun i =>
    {state := .go,input := inp,work := W i,output := out}
  have hwp : ∀ i j, Parked (W i j) := fun i =>
    updateTape_parked work q _ hw (advanceInput_parked _ _ (hw q))
  have hscan : ∀ i, i ≤ v → (skipWorkHeaderTM q).reachesIn i (C 0) (C i) := by
    intro i
    induction i with
    | zero => intro _; exact .zero
    | succ i ih =>
        intro hv
        have hs := skipWorkHeader_step q true inp (W i) out hp (hwp i) ho.parked
          (by simpa [W,Tape.read,advanceInput] using hones i (by omega))
        have he : Function.update (W i) q (((W i) q).move .right) = W (i+1) := by
          simp only [W,Function.update_self,advanceInput_move,Function.update_idem]
        rw [he] at hs
        exact reachesIn_trans _ (ih (by omega)) (.step hs .zero)
  have hdel := skipWorkHeader_step q false inp (W v) out hp (hwp v) ho.parked
    (by simpa [W,Tape.read,advanceInput] using hend)
  have he : Function.update (W v) q (((W v) q).move .right) = W (v+1) := by
    simp only [W,Function.update_self,advanceInput_move,Function.update_idem]
  rw [he] at hdel
  have hall := reachesIn_trans _ (hscan v le_rfl) (.step hdel .zero)
  have hz : C 0 = {state := (skipWorkHeaderTM q).qstart,input := inp,work := work,output := out} := by
    dsimp [C,W,advanceInput]
    rw [Function.update_eq_self]
    rfl
  rw [hz] at hall
  exact ⟨_,v+1,le_rfl,hall,rfl,rfl,rfl,ho⟩

theorem skipWorkHeader_bits {k : Nat} (q : Fin k) (pre tail : List Bool) (v : Nat)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (hq : work q = advanceInput
      (parkedInput (pre ++ (List.replicate v true ++ false :: tail))) pre.length) :
    (skipWorkHeaderTM q).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work q (advanceInput
        (parkedInput (pre ++ (List.replicate v true ++ false :: tail))) (pre.length+v+1))) ys)
      (v+1) := by
  have h := skipWorkHeader_correct q v inp work ys hp hw
    (by
      intro i hi
      have hc := unary_header_cell pre tail v i (by omega)
      simpa [hq,advanceInput,parkedInput,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,hi] using hc)
    (by
      have hc := unary_header_cell pre tail v v le_rfl
      simpa [hq,advanceInput,parkedInput,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc)
  simpa only [hq,advanceInput,Nat.add_assoc] using h

def skipCNFHeadersTM {k : Nat} (q : Fin k) : TM k :=
  seqTM (skipWorkHeaderTM q) (skipWorkHeaderTM q)

def cnfStreamCursor {n m : Nat} (Φ : Fin m → Finset (Choice n)) (pos : Nat) : Tape :=
  advanceInput (parkedInput (cnfBits Φ)) (n+m+2+pos)

theorem skipCNFHeaders_correct {n m k : Nat} (Φ : Fin m → Finset (Choice n))
    (q : Fin k) (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i)) (hq : work q = parkedInput (cnfBits Φ)) :
    (skipCNFHeadersTM q).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work q (cnfStreamCursor Φ 0)) ys) (n+m+3) := by
  let W := Function.update work q (advanceInput (parkedInput (cnfBits Φ)) (n+1))
  have hwp : ∀ i, Parked (W i) := updateTape_parked work q _ hw
    (advanceInput_parked _ _ (parkedInput_parked _))
  have he₁ : [] ++ (List.replicate n true ++ false :: (List.replicate m true ++ false :: cnfBody Φ)) =
      cnfBits Φ := by simp [cnfBits,List.append_assoc]
  have he₂ : (List.replicate n true ++ [false]) ++ (List.replicate m true ++ false :: cnfBody Φ) =
      cnfBits Φ := by simp [cnfBits,List.append_assoc]
  have h₁ := skipWorkHeader_bits q [] (List.replicate m true ++ false :: cnfBody Φ) n
    inp work ys hp hw (by simpa [he₁,advanceInput] using hq)
  rw [he₁] at h₁
  simp only [List.length_nil,zero_add] at h₁
  have h₂ := skipWorkHeader_bits q (List.replicate n true ++ [false]) (cnfBody Φ) m
    inp W ys hp hwp (by simp [W,he₂])
  rw [he₂] at h₂
  have hall := seqTM_hoareTime _ _ h₁ (emitPred_transition hp hwp ys) h₂
  have he : Function.update W q
      (advanceInput (parkedInput (cnfBits Φ)) ((List.replicate n true ++ [false]).length+m+1)) =
      Function.update work q (cnfStreamCursor Φ 0) := by
    simp [W,cnfStreamCursor]
    congr 2
    omega
  rw [he] at hall
  apply hall.mono_bound
  omega

end IrrRAFEnumeration.SATSource
