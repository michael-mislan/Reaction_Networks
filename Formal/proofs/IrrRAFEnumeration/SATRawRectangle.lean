import proofs.IrrRAFEnumeration.SATRawIncidenceReusable
import proofs.Complexitylib.Models.TuringMachine.Placement.Internal
import proofs.Complexitylib.Models.TuringMachine.Registers.Emit
import Mathlib.Tactic.FinCases

namespace IrrRAFEnumeration.SATSource
open Complexity SAT Complexity.TM

/-- Two query indices and two preserved loop tapes. -/
def rectangleWork (j v : Nat) (inner outer : Tape) : Fin 4 → Tape :=
  ![regTape j,regTape v,inner,outer]

def rectangleQueryTM (sign : Bool) : TM 4 :=
  placeWorkTM 0 2 (rawIncidenceReusableTM sign)

theorem rectangleQueryTM_correct (sign : Bool) (v j : Nat) (φ : CNF)
    (inp inner outer : Tape) (ys : List Bool) (hin : inp.HasBinarySuffix φ.encode)
    (hhead : inp.head = 1) (hzero : inp.cells 0 = Γ.start)
    (hi : Parked inner) (ho : Parked outer) :
    (rectangleQueryTM sign).HoareTime
      (EmitPred inp (rectangleWork j v inner outer) ys)
      (EmitPred inp (rectangleWork j v inner outer)
        (ys ++ [incidenceCNFMatch sign v φ j])) (4*φ.encode.length+11) := by
  rintro a w out ⟨rfl,rfl,hout⟩
  obtain ⟨c,t,ht,hr,hh,hinput,hwork,houtput⟩ :=
    rawIncidenceReusableTM_correct sign v j φ a ys hin hhead hzero
      a (incidenceQueryWork j v) out ⟨rfl,rfl,hout⟩
  let frame := rectangleWork j v inner outer
  have hextra : ∀ i, ¬placeWorkInMiddle (post := 2) 0 2 i → (frame i).read ≠ Γ.start := by
    intro i h
    fin_cases i
    · exact False.elim (h (by decide))
    · exact False.elim (h (by decide))
    · exact hi.read_ne_start
    · exact ho.read_ne_start
  have hrun := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    (rawIncidenceReusableTM sign) 0 2 frame hr hextra
  have hstart : placeWorkCfg (rawIncidenceReusableTM sign) 0 2 frame
      { state := (rawIncidenceReusableTM sign).qstart,
        input := a, work := incidenceQueryWork j v, output := out } =
      ({ state := (rectangleQueryTM sign).qstart
         input := a
         work := rectangleWork j v inner outer
         output := out } :
        Cfg 4 (rectangleQueryTM sign).Q) := by
    unfold placeWorkCfg
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hstart] at hrun
  refine ⟨placeWorkCfg (rawIncidenceReusableTM sign) 0 2 frame c,
    t,ht,hrun,hh,hinput,?_,houtput⟩
  funext i
  fin_cases i <;> simp [placeWorkCfg,hwork,incidenceQueryWork,
    placeWorkInMiddle,placeWorkCoord,rectangleWork,frame]

def rectanglePairTM : TM 4 :=
  seqTM (rectangleQueryTM false) (rectangleQueryTM true)

theorem rectanglePairTM_correct (v j : Nat) (φ : CNF)
    (inp inner outer : Tape) (ys : List Bool) (hin : inp.HasBinarySuffix φ.encode)
    (hhead : inp.head = 1) (hzero : inp.cells 0 = Γ.start)
    (hp : Parked inp) (hi : Parked inner) (ho : Parked outer) :
    rectanglePairTM.HoareTime
      (EmitPred inp (rectangleWork j v inner outer) ys)
      (EmitPred inp (rectangleWork j v inner outer)
        (ys ++ [incidenceCNFMatch false v φ j,incidenceCNFMatch true v φ j]))
      (8*φ.encode.length+23) := by
  have hw : ∀ i, Parked (rectangleWork j v inner outer i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact hi | exact ho
  have h := seqTM_hoareTime _ _
    (rectangleQueryTM_correct false v j φ inp inner outer ys hin hhead hzero hi ho)
    (emitPred_transition hp hw _)
    (rectangleQueryTM_correct true v j φ inp inner outer
      (ys ++ [incidenceCNFMatch false v φ j]) hin hhead hzero hi ho)
  have ht : (4*φ.encode.length+11)+1+(4*φ.encode.length+11) =
      8*φ.encode.length+23 := by omega
  simpa only [rectanglePairTM,List.append_assoc,List.singleton_append,ht] using h

end IrrRAFEnumeration.SATSource
