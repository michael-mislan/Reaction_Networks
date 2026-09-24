import proofs.IrrRAFEnumeration.SATSourceCompiler
import proofs.Complexitylib.Models.TuringMachine.Composition.Internal.Tail

namespace IrrRAFEnumeration.SATSource

open SATCompletion Complexity Complexity.TM

/-- The complete source compiler can run on a canonical virtual rectangle.
Only this particular well-formed input is assumed, not a global FP contract. -/
theorem sourceCompiler_virtual_correct {n m : Nat}
    (Φ : Fin m → Finset (Choice n)) (realInput : Tape) :
    ∃ (c' : Cfg 14 sourceCompilerTM.Q) (t : Nat),
      t ≤ 10000000000*((cnfBits Φ).length+1)^5 ∧
      (retargetInputStarted sourceCompilerTM).reachesIn t
        (retargetInputStartedCfg sourceCompilerTM (cnfBits Φ) realInput) c' ∧
      (retargetInputStarted sourceCompilerTM).halted c' ∧
      c'.output.HasOutput (sourceBits Φ) := by
  let M := sourceCompilerTM
  let y := cnfBits Φ
  have hne : M.qstart ≠ M.qhalt := by intro h; cases h
  obtain ⟨cM, t, ht, hreach, hhalt, hout⟩ :=
    sourceCompilerTM_correct Φ (Tape.init (y.map Γ.ofBool))
      (fun _ => Tape.init []) (Tape.init []) ⟨rfl, fun _ => rfl, rfl⟩
  change M.reachesIn t (M.initCfg y) cM at hreach
  have ht_ne : t ≠ 0 := by
    intro ht0
    subst t
    cases hreach
    exact hne hhalt
  obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht_ne
  cases hreach with
  | step hstep hrest =>
    next cMid =>
      have hmid : cMid = startedCfg M y hne := by
        have hs : some cMid = some (startedCfg M y hne) := by
          rw [← hstep, step_initCfg_startedCfg M y hne]
        exact Option.some.inj hs
      subst cMid
      obtain ⟨hinv, hworkInv, houtInv⟩ := Tape.StartInvariant.step M
        (step_initCfg_startedCfg M y hne)
        (Tape.StartInvariant.init_ofBool y)
        (fun _ => Tape.StartInvariant.init_nil) Tape.StartInvariant.init_nil
      obtain ⟨finalReal, hsim⟩ := retargetInput_reachesIn_of_reachesIn M hrest
        hinv hworkInv houtInv realInput
      let c' := retargetWrap M finalReal cM
      have hsim' : (retargetInputStarted M).reachesIn t'
          (retargetInputStartedCfg M y realInput) c' := by
        rw [retargetInputStartedCfg_eq_retargetWrap M y realInput hne]
        exact retargetInputStarted_reachesIn_of_retargetInput M hsim
      refine ⟨c', t', by omega, hsim', ?_, ?_⟩
      · exact hhalt
      · exact hout.2.2.hasOutput

/-- Actual normalization/rewind/copy pipeline followed by the source compiler.
The first machine need only establish this rectangle boundary. -/
theorem sourceCompiler_tail_correct {nf n m : Nat}
    (Φ : Fin m → Finset (Choice n)) (B : Nat) :
    (compositionTailTM nf 13 sourceCompilerTM).HoareTime
      (CompositionTailPre nf 13 (cnfBits Φ) B)
      (fun _ _ out => out.HasOutput (sourceBits Φ))
      ((B+2)+1+(((cnfBits Φ).length+1)+1+
        (((cnfBits Φ).length+1+2)+1+10000000000*((cnfBits Φ).length+1)^5))) := by
  apply compositionTailTM_hoareTime_of_virtualRun_internal (nf := nf)
    (G := fun l => 10000000000*(l+1)^5) sourceCompilerTM
    (cnfBits Φ) B (fun out => out.HasOutput (sourceBits Φ))
  exact sourceCompiler_virtual_correct Φ

end IrrRAFEnumeration.SATSource
