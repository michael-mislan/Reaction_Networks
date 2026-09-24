import proofs.IrrRAFEnumeration.SATStreamInit
import proofs.IrrRAFEnumeration.SATSourceInit
import proofs.IrrRAFEnumeration.SATTapeFrame

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

/-- Six initialized source counts, six reserved zero registers and a blank
stream destination. All thirteen tapes are parked after initialization. -/
def sourceCountWork (n m : Nat) : Fin 13 → Tape := fun i =>
  if h : i.val < 6 then
    countTapes ![n,m,Fintype.card (Wire n m),Fintype.card (Step n m),
      moleculeCount n m,reactionCount n m] ⟨i.val,h⟩
  else (Tape.init []).move .right

theorem sourceCountWork_parked (n m : Nat) : ∀ i, Parked (sourceCountWork n m i) := by
  intro i
  dsimp only [sourceCountWork]
  split
  · exact parked_regTape _
  · exact parked_init_input []

theorem sourceInit13_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    (sourceInitTM.liftTM 7).HoareTime
      (fun inp work out => inp = Tape.init ((cnfBits Φ).map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred (parkedInput (cnfBits Φ)) (sourceCountWork n m) [])
      (710*((cnfBits Φ).length+1)^4) := by
  rintro inp work out ⟨hi,hw,ho⟩
  subst inp
  subst out
  have hwe : work = fun _ => Tape.init [] := funext hw
  subst work
  obtain ⟨c,t,ht,hr,hh,hi,hw,ho⟩ := sourceInitTM_correct Φ
    (Tape.init ((cnfBits Φ).map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
    ⟨rfl,fun _ => rfl,rfl⟩
  have htpos : 0 < t := by
    by_contra h
    have he : t = 0 := by omega
    subst t
    cases hr
    simp only [TM.halted,Cfg.isHalted,sourceInitTM,seqTM,reduceCtorEq] at hh
  have hre := liftTM_reachesIn_initCfg_of_pos sourceInitTM 7 (cnfBits Φ) htpos hr
  refine ⟨_,t,ht,hre,hh,hi,?_,ho⟩
  funext i
  dsimp only [liftCfg,sourceCountWork]
  split
  · rw [hw]
  · rfl

def sourceStreamWork {n m : Nat} (Φ : Fin m → Finset (Choice n)) : Fin 13 → Tape :=
  Function.update (sourceCountWork n m) 12 (cnfStreamCursor Φ 0)

theorem sourceStreamWork_parked {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    ∀ i, Parked (sourceStreamWork Φ i) :=
  updateTape_parked _ _ _ (sourceCountWork_parked n m) (cnfStreamCursor_parked Φ 0)

def sourceStreamInitTM : TM 13 := seqTM (sourceInitTM.liftTM 7) (streamInitTM 12 0)

/-- Starting from the actual input and entirely blank auxiliary/output tapes,
load the source dimensions and a ready-to-consume CNF incidence stream.
No initial count, copied input or positioned cursor is assumed. -/
theorem sourceStreamInitTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    sourceStreamInitTM.HoareTime
      (fun inp work out => inp = Tape.init ((cnfBits Φ).map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (EmitPred (parkedInput (cnfBits Φ)) (sourceStreamWork Φ) [])
      (730*((cnfBits Φ).length+1)^4) := by
  have hi := sourceInit13_correct Φ
  have hs := streamInit_correct Φ 12 0 (sourceCountWork n m) []
    (sourceCountWork_parked n m) (by simp [sourceCountWork,placeWorkIdx])
  have h := seqTM_hoareTime _ _ hi
    (emitPred_transition (parkedInput_parked _) (sourceCountWork_parked n m) []) hs
  change sourceStreamInitTM.HoareTime _ (EmitPred _ (sourceStreamWork Φ) []) _ at h
  apply h.mono_bound
  let L := (cnfBits Φ).length+1
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hlp : L ≤ L^4 := by
    simpa using Nat.pow_le_pow_right hL (show 1 ≤ 4 by decide)
  change 710*L^4+1+(4*(cnfBits Φ).length+13) ≤ 730*L^4
  dsimp [L] at hlp
  dsimp [L]
  omega

end IrrRAFEnumeration.SATSource
