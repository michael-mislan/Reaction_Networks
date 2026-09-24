import proofs.IrrRAFEnumeration.CompletionSATTrial

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

theorem frameWork_update_last {n : Nat} (w : Fin n → Tape) (s t : Tape) :
    Function.update (frameWork (m := 1) w (fun _ => s)) (Fin.last n) t =
      frameWork w (fun _ => t) := by
  funext i
  by_cases hi : i.val < n
  · have hn : i ≠ Fin.last n := by
      intro he
      have := congrArg (fun x : Fin (n+1) => x.val) he
      change i.val = n at this
      omega
    simp [Function.update_of_ne hn,frameWork,hi]
  · have he : i = Fin.last n := by
      apply Fin.ext
      have := i.isLt
      change i.val < n+1 at this
      change i.val = n
      omega
    subst i
    simp [frameWork]

def minimizeFuel (k : Nat) : Fin ((bufferedCount k+1)+1) := Fin.last (bufferedCount k+1)

def minimizeWork {r : Nat} (k : Nat) (U : Finset (Fin r))
    (base blocks : List Bool) (j : Nat) :=
  frameWork (m := 1) (trialWork k U base blocks j 0) (fun _ => regTape r)

def minimizeTM {k : Nat} (call : TM (bufferedCount k)) : TM ((bufferedCount k+1)+1) :=
  forRegTM ((deletionTrialTM call).liftTM 1) (minimizeFuel k)

/-- Realize a full fixed-order deletion sequence. The extra loop-fuel tape is
outside both the trial's address register and the reusable solver workspace. -/
theorem minimizeTM_sequence_correct {r k : Nat} (call : TM (bufferedCount k))
    (P : Finset (Fin r) → Prop) [DecidablePred P] (U : Nat → Finset (Fin r))
    (base blocks : List Bool) (inp : Tape) (hp : Parked inp) (b : Nat)
    (hU : ∀ i, i < r → P (U i))
    (hstep : ∀ i (hi : i < r), U (i+1) =
      if P ((U i).erase ⟨i,hi⟩) then (U i).erase ⟨i,hi⟩ else U i)
    (hcall : ∀ i (hi : i < r), call.HoareTime
      (EmitPred inp (completionWork k ((U i).erase ⟨i,hi⟩) base blocks) [])
      (completionResult k ((U i).erase ⟨i,hi⟩) base blocks inp (P ((U i).erase ⟨i,hi⟩))) b) :
    (minimizeTM call).HoareTime
      (EmitPred inp (minimizeWork k (U 0) base blocks 0) [])
      (EmitPred inp (minimizeWork k (U r) base blocks r) [])
      (r*(b+12*r+33)+(r+2)) := by
  let W := fun i => minimizeWork k (U i) base blocks i
  have hw : ∀ i j, Parked (W i j) := by
    intro i j
    unfold W minimizeWork frameWork
    split
    · exact trialWork_parked _ _ _ _ _ _ _
    · exact parked_regTape _
  have hf : ∀ i, W i (minimizeFuel k) = regTape r := by
    intro i
    simp [W,minimizeWork,minimizeFuel,frameWork]
  have hb : ∀ i, i < r → ((deletionTrialTM call).liftTM 1).HoareTime
      (EmitPred inp (Function.update (W i) (minimizeFuel k) ⟨i+2,regCells r⟩) [])
      (EmitPred inp (Function.update (W (i+1)) (minimizeFuel k) ⟨i+2,regCells r⟩) [])
      (b+12*r+31) := by
    intro i hi
    let j : Fin r := ⟨i,hi⟩
    have ht := deletionTrialTM_correct call P (U i) j (hU i hi) base blocks inp hp b (hcall i hi)
    have he : (deletionTrialTM call).HoareTime
        (EmitPred inp (trialWork k (U i) base blocks i 0) [])
        (EmitPred inp (trialWork k (U (i+1)) base blocks (i+1) 0) [])
        (b+12*i+31) := ht.strengthen_post (by
      rintro a w out ⟨v,hv,ha,hP,hpost⟩
      have hc : (if v = 1 then (U i).erase j else U i) = U (i+1) := by
        rw [hstep i hi]
        by_cases hh : v = 1
        · simp [hh,ha.mp hh,j]
        · have hn : ¬P ((U i).erase j) := fun h => hh (ha.mpr h)
          simp [hh,hn,j] at *
      simpa only [hc] using hpost)
    have hl := liftTM_frame_correct (deletionTrialTM call) 1
      (fun _ => (⟨i+2,regCells r⟩ : Tape))
      (fun _ _ => parked_regCells (v := r) (h := i+2) (by omega))
      inp inp _ _ [] [] _ he
    have hl' := hl.mono_bound (show b+12*i+31 ≤ b+12*r+31 by omega)
    simpa only [W,minimizeWork,minimizeFuel,frameWork_update_last] using hl'
  have h := forRegTM_hoareTime ((deletionTrialTM call).liftTM 1) (minimizeFuel k)
    r inp W (fun _ => []) (b+12*r+31) hp hf (fun i j _ => hw i j) hb
  exact h

end IrrRAFEnumeration.CompletionQuery
