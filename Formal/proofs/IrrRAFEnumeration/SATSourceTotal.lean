import proofs.IrrRAFEnumeration.SATAdapterTotal
import proofs.IrrRAFEnumeration.SATRawSourceCompiler

namespace IrrRAFEnumeration.SATSource
open Complexity SAT SATCompletion Complexity.TM

def librarySource (z : List Bool) : List Bool :=
  match CNF.decode? z with
  | some φ => sourceBits (libraryRect φ (φ.encode.length+2))
  | none => sourceBits (fun _ : Fin 1 => (∅ : Finset (Choice 2)))

theorem librarySource_representation (z : List Bool) :
    ∃ (n m : Nat) (Φ : Fin m → Finset (Choice n)),
      2 ≤ n ∧ librarySATAdapter z = cnfBits Φ ∧ librarySource z = sourceBits Φ ∧
      ((∃ f, Satisfies Φ f) ↔ z ∈ SAT.language) := by
  cases hd : CNF.decode? z with
  | some φ =>
    refine ⟨φ.encode.length+2,φ.length,libraryRect φ _,by omega,?_,?_,?_⟩
    · simp [librarySATAdapter,hd,libraryRectangle]
    · simp [librarySource,hd]
    · exact (libraryRect_encode_satisfiable φ).trans (libraryCNF_decode_language hd).symm
  | none =>
    refine ⟨2,1,fun _ => ∅,by decide,?_,?_,?_⟩
    · simp [librarySATAdapter,hd]
    · simp [librarySource,hd]
    · constructor
      · rintro ⟨f,hf⟩
        obtain ⟨x,hx,_⟩ := hf (0 : Fin 1)
        exact False.elim (Finset.notMem_empty x hx)
      · rintro ⟨φ,hz,_⟩
        rw [hz,CNF.decode?_encode] at hd
        contradiction

def totalSourceCompilerTM := compositionTM totalRectangleAdapterTM sourceCompilerTM

theorem totalSourceCompilerTM_computes : totalSourceCompilerTM.ComputesInTime
    librarySource (fun L => 1000000000000000*(L+2)^10) := by
  intro z
  obtain ⟨n,m,Φ,_,hy,hsource,_⟩ := librarySource_representation z
  let y := librarySATAdapter z
  let B := 2000*(z.length+2)^3
  obtain ⟨C,t,ht,hreach,hhalt,hraw,hhead,hvirtual,hscratch,hinv,hinhead,hwork,hout⟩ :=
    compositionFirstTM_boundary_of_run_internal totalRectangleAdapterTM 13 z
      y B (totalRectangleAdapterTM_computes z)
  have hraw' : (transitionTape (C.work (compositionRawOutputIdx 4 13))).HasOutput (cnfBits Φ) := by
    simpa only [y,hy] using hraw
  obtain ⟨D,u,hu,hr,hh,ho⟩ := sourceCompiler_tail_correct (nf := 4) Φ (B+1)
    (transitionInput C.input) (fun i => transitionTape (C.work i)) (transitionTape C.output)
    ⟨hraw',(hwork _).1,hhead.trans (Nat.add_le_add_right ht 1),hvirtual,hscratch,hout,
      hinv,hinhead,fun i => hwork (compositionPrefixIdx 4 13 i)⟩
  have hseq := seqTM_reachesIn_of_reachesIn (compositionFirstTM totalRectangleAdapterTM 13)
    (compositionTailTM 4 13 sourceCompilerTM) hreach hhalt hr
  refine ⟨phase2Wrap (compositionFirstTM totalRectangleAdapterTM 13)
    (compositionTailTM 4 13 sourceCompilerTM) D,t+1+u,?_,hseq,
    (phase2Wrap_halted_iff _ _ _).mpr hh,?_⟩
  · have hyl : y.length ≤ 4*(z.length+2)^2 := librarySATAdapter_length_bound z
    have ha : 1 ≤ z.length+2 := by omega
    have ha2 : 1 ≤ (z.length+2)^2 := one_le_pow₀ ha
    have hy1 : y.length+1 ≤ 5*(z.length+2)^2 := by omega
    have hpow := Nat.pow_le_pow_left hy1 5
    have he : (5*(z.length+2)^2)^5 = 3125*(z.length+2)^10 := by ring
    rw [he] at hpow
    have h2 := Nat.pow_le_pow_right ha (by decide : 2 ≤ 10)
    have h3 := Nat.pow_le_pow_right ha (by decide : 3 ≤ 10)
    have h10 : 1 ≤ (z.length+2)^10 := one_le_pow₀ ha
    rw [← hy] at hu
    change u ≤ ((B+1+2)+1+((y.length+1)+1+
      ((y.length+1+2)+1+10000000000*(y.length+1)^5))) at hu
    dsimp [B] at ht hu
    nlinarith
  · simpa only [hsource] using ho

theorem librarySource_mem_FP : librarySource ∈ FP := by
  apply mem_FP_iff_computesInTime_polynomial.mpr
  refine ⟨_,totalSourceCompilerTM,
    Polynomial.C 1000000000000000*(Polynomial.X+Polynomial.C 2)^10,?_⟩
  simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_X] using totalSourceCompilerTM_computes

end IrrRAFEnumeration.SATSource
