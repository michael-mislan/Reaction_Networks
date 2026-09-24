import proofs.IrrRAFEnumeration.SATRawRectangleCompiler
import proofs.IrrRAFEnumeration.SATLibraryAdapterSpec
import proofs.IrrRAFEnumeration.SATSourceVirtual
import proofs.Complexitylib.Models.TuringMachine.Composition.Internal.FirstPhase

namespace IrrRAFEnumeration.SATSource
open Complexity SAT Complexity.TM

def rawSourceCompilerTM := compositionTM rawRectangleCompilerTM sourceCompilerTM

/-- The complete raw SAT-to-CRS compiler on valid formula encodings, with
actual normalization and virtual-input execution included in its time bound. -/
theorem rawSourceCompilerTM_correct (φ : CNF) :
    ∃ c t, t ≤ 1000000000000000*(φ.encode.length+2)^10 ∧
      rawSourceCompilerTM.reachesIn t (rawSourceCompilerTM.initCfg φ.encode) c ∧
      rawSourceCompilerTM.halted c ∧
      c.output.HasOutput (sourceBits (libraryRect φ (φ.encode.length+2))) := by
  let y := libraryRectangle φ
  let B := 1000*(φ.encode.length+2)^3
  obtain ⟨C,t,ht,hreach,hhalt,hraw,hhead,hvirtual,hscratch,hinv,hinhead,hwork,hout⟩ :=
    compositionFirstTM_boundary_of_run_internal rawRectangleCompilerTM 13 φ.encode
      y B (rawRectangleCompilerTM_correct φ)
  obtain ⟨D,u,hu,hr,hh,ho⟩ := sourceCompiler_tail_correct (nf := 4)
    (libraryRect φ (φ.encode.length+2)) (B+1)
    (transitionInput C.input) (fun i => transitionTape (C.work i)) (transitionTape C.output)
    ⟨hraw,(hwork _).1,hhead.trans (Nat.add_le_add_right ht 1),hvirtual,hscratch,hout,hinv,hinhead,
      fun i => hwork (compositionPrefixIdx 4 13 i)⟩
  have hseq := seqTM_reachesIn_of_reachesIn (compositionFirstTM rawRectangleCompilerTM 13)
    (compositionTailTM 4 13 sourceCompilerTM) hreach hhalt hr
  refine ⟨phase2Wrap (compositionFirstTM rawRectangleCompilerTM 13)
    (compositionTailTM 4 13 sourceCompilerTM) D,t+1+u,?_,hseq,
    (phase2Wrap_halted_iff _ _ _).mpr hh,ho⟩
  have hy : y.length ≤ 4*(φ.encode.length+2)^2 := libraryRectangle_length_bound φ
  have ha : 1 ≤ φ.encode.length+2 := by omega
  have ha2 : 1 ≤ (φ.encode.length+2)^2 := one_le_pow₀ ha
  have hy1 : y.length+1 ≤ 5*(φ.encode.length+2)^2 := by omega
  have hpow := Nat.pow_le_pow_left hy1 5
  have he : (5*(φ.encode.length+2)^2)^5 = 3125*(φ.encode.length+2)^10 := by ring
  rw [he] at hpow
  have h2 := Nat.pow_le_pow_right ha (by decide : 2 ≤ 10)
  have h3 := Nat.pow_le_pow_right ha (by decide : 3 ≤ 10)
  have h10 : 1 ≤ (φ.encode.length+2)^10 := one_le_pow₀ ha
  change u ≤ ((B+1+2)+1+((y.length+1)+1+
    ((y.length+1+2)+1+10000000000*(y.length+1)^5))) at hu
  dsimp [B] at ht hu
  nlinarith

end IrrRAFEnumeration.SATSource
