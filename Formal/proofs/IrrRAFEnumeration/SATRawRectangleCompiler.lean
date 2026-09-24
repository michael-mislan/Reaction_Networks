import proofs.IrrRAFEnumeration.SATRawRectangleSetup
import proofs.IrrRAFEnumeration.SATRawRectangleEncoding
import proofs.IrrRAFEnumeration.SATMachineRuns

namespace IrrRAFEnumeration.SATSource
open Complexity SAT Complexity.TM

def rectangleHeaderTM : TM 4 := seqTM (emitRunTM true 2)
  (seqTM (emitBitsTM [false]) (seqTM (emitRunTM true 3) (emitBitsTM [false])))

def rectangleHeader (N M : Nat) := List.replicate N true ++ [false] ++
  List.replicate M true ++ [false]

theorem rectangleHeaderTM_correct (N M : Nat) (inp : Tape) (ys : List Bool)
    (hp : Parked inp) :
    rectangleHeaderTM.HoareTime
      (EmitPred inp (rectangleWork 0 0 (regTape N) (regTape M)) ys)
      (EmitPred inp (rectangleWork 0 0 (regTape N) (regTape M))
        (ys ++ rectangleHeader N M)) (4*N+4*M+9) := by
  let w := rectangleWork 0 0 (regTape N) (regTape M)
  have hw := rectangleWork_parked 0 0 (regTape N) (regTape M)
    (parked_regTape N) (parked_regTape M)
  have h₁ := emitRunTM_correct true (2 : Fin 4) N inp w ys hp hw rfl
  have h₂ := emitBitsTM_hoareTime [false] inp w (ys ++ List.replicate N true) hp hw
  have h₃ := emitRunTM_correct true (3 : Fin 4) M inp w
    ((ys ++ List.replicate N true) ++ [false]) hp hw rfl
  have h₄ := emitBitsTM_hoareTime [false] inp w
    (((ys ++ List.replicate N true) ++ [false]) ++ List.replicate M true) hp hw
  have h₃₄ := seqTM_hoareTime _ _ h₃ (emitPred_transition hp hw _) h₄
  have h₂₃₄ := seqTM_hoareTime _ _ h₂ (emitPred_transition hp hw _) h₃₄
  have h := seqTM_hoareTime _ _ h₁ (emitPred_transition hp hw _) h₂₃₄
  have ht : (4*N+2)+1+(1+1+((4*M+2)+1+1)) = 4*N+4*M+9 := by omega
  simpa only [rectangleHeaderTM,rectangleHeader,List.append_assoc,List.length_singleton,ht] using h

def rectangleEmitTM : TM 4 := seqTM rectangleHeaderTM rectangleRowsTM

theorem rectangleEmitTM_correct (φ : CNF) (N : Nat) (inp : Tape)
    (hin : inp.HasBinarySuffix φ.encode) (hhead : inp.head = 1)
    (hzero : inp.cells 0 = Γ.start) (hp : Parked inp) :
    rectangleEmitTM.HoareTime
      (EmitPred inp (rectangleWork 0 0 (regTape N) (regTape φ.length)) [])
      (EmitPred inp (rectangleWork φ.length 0 (regTape N) (regTape φ.length))
        (cnfBits (libraryRect φ N)))
      (4*N+4*φ.length+12+φ.length*(rectangleBlockBound φ.encode.length N φ.length+3)) := by
  have hw := rectangleWork_parked 0 0 (regTape N) (regTape φ.length)
    (parked_regTape N) (parked_regTape φ.length)
  have h := seqTM_hoareTime _ _ (rectangleHeaderTM_correct N φ.length inp [] hp)
    (emitPred_transition hp hw _)
    (rectangleRowsTM_correct N φ.length φ inp (rectangleHeader N φ.length) hin hhead hzero hp)
  have ht : (4*N+4*φ.length+9)+1+
      (φ.length*(rectangleBlockBound φ.encode.length N φ.length+3)+2) =
      4*N+4*φ.length+12+φ.length*(rectangleBlockBound φ.encode.length N φ.length+3) := by omega
  simpa only [rectangleEmitTM,List.nil_append,rectangleRowsPrefix_eq_cnfBody,
    cnfBits,rectangleHeader,List.append_assoc,ht] using h

def rawRectangleCompilerTM : TM 4 := seqTM rawRectangleSetupTM rectangleEmitTM

/-- Actual uniform raw CNF adapter on every valid encoded formula. -/
theorem rawRectangleCompilerTM_correct (φ : CNF) :
    ∃ c t, t ≤ 1000*(φ.encode.length+2)^3 ∧
      rawRectangleCompilerTM.reachesIn t (rawRectangleCompilerTM.initCfg φ.encode) c ∧
      rawRectangleCompilerTM.halted c ∧ c.output.HasOutput (libraryRectangle φ) := by
  obtain ⟨a,t,ht,ha,hh,hi,hw,ho⟩ := rawRectangleSetupTM_correct φ
  have hp : Parked a.input := by rw [hi]; exact parked_init_input _
  have hwp : ∀ i, Parked (a.work i) := by
    rw [hw]
    exact rectangleWork_parked 0 0 _ _ (parked_regTape _) (parked_regTape _)
  have hin : a.input.HasBinarySuffix φ.encode := by
    rw [hi]
    exact Tape.init_move_right_hasBinarySuffix _
  obtain ⟨c,s,hs,hr,hhalt,hinput,hwork,houtput⟩ :=
    rectangleEmitTM_correct φ (φ.encode.length+2) a.input hin
      (by rw [hi]) (by rw [hi]; rfl) hp a.input a.work a.output ⟨rfl,hw,ho⟩
  have hwt : (fun i => transitionTape (a.work i)) = a.work :=
    funext (fun i => (hwp i).transitionTape_eq_self)
  have hrun := seqTM_reachesIn_of_reachesIn rawRectangleSetupTM rectangleEmitTM ha hh (by
    simpa only [hp.transitionInput_eq_self,hwt,ho.parked.transitionTape_eq_self] using hr)
  refine ⟨phase2Wrap rawRectangleSetupTM rectangleEmitTM c,t+1+s,?_,hrun,
    (phase2Wrap_halted_iff _ _ _).mpr hhalt,houtput.hasOutput⟩
  have hm : φ.length ≤ φ.encode.length := by
    simpa [clauseMarks_encode] using clauseMarks_length_le none φ.encode
  calc
    t+1+s ≤ (9*φ.encode.length+28+rectanglePrepareBound (φ.encode.length+2) φ.length)+1+
        (4*(φ.encode.length+2)+4*φ.length+12+
          φ.length*(rectangleBlockBound φ.encode.length (φ.encode.length+2) φ.length+3)) := by omega
    _ ≤ (9*φ.encode.length+28+rectanglePrepareBound (φ.encode.length+2) φ.encode.length)+1+
        (4*(φ.encode.length+2)+4*φ.encode.length+12+
          φ.encode.length*(rectangleBlockBound φ.encode.length (φ.encode.length+2) φ.encode.length+3)) := by
      unfold rectanglePrepareBound rectangleBlockBound
      gcongr
    _ ≤ 1000*(φ.encode.length+2)^3 := by
      unfold rectanglePrepareBound rectangleBlockBound
      ring_nf
      omega

end IrrRAFEnumeration.SATSource
