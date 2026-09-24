import proofs.IrrRAFEnumeration.ExpectedBaseline

namespace IrrRAFEnumeration.CountPostlude
open Complexity Complexity.TM HeaderComparison GatedHeader GatedDecision ExpectedBaseline

def postludeTM : TM 3 := seqTM baselineTM gatedDecisionTM

/-- Recover the SAT source baseline from the saved raw length, compare only
after successful completion, and publish the resulting decision bit. -/
theorem postlude_correct (length actual : Nat) (success : Bool)
    (inp flag clock out : Tape) (hi : Parked inp)
    (hf : Parked flag) (hc : Parked clock) (ho : Parked out) (hInv : out.StartInvariant)
    (hclock : clock.read = Γ.ofBool success)
    (hO : success = true → UnaryPrefix (parkOutput out) actual Γ.zero) :
    ∃ c t, t ≤ 3*out.head+6*length+25 ∧
      postludeTM.reachesIn t
        ⟨postludeTM.qstart,inp,baselineWork length flag clock,out⟩ c ∧
      postludeTM.halted c ∧
      c.output.cells 1 = Γ.ofBool (!(success && decide (actual = length+2))) := by
  obtain ⟨c,t,ht,hr,hh,hi',hw',ho'⟩ := baseline_correct length inp flag clock out hi hf hc ho
  obtain ⟨d,u,hu,hg,hd,hv⟩ := gated_decision_correct actual (length+2) success
    inp (regTape (length+2)) flag clock out hi (parked_regTape _) hf hc ho hInv
      hclock (register_prefix _) hO
  change gatedDecisionTM.reachesIn u
    ⟨gatedDecisionTM.qstart,inp,baselineWork (length+2) flag clock,out⟩ d at hg
  have hwp : ∀ i, Parked (baselineWork (length+2) flag clock i) := by
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact hf | exact hc
  have hwt : (fun i => transitionTape (baselineWork (length+2) flag clock i)) =
      baselineWork (length+2) flag clock := funext (fun i => (hwp i).transitionTape_eq_self)
  have hseq := seqTM_reachesIn_of_reachesIn baselineTM gatedDecisionTM hr hh (by
    simpa only [hi',hw',ho',hi.transitionInput_eq_self,hwt,ho.transitionTape_eq_self] using hg)
  exact ⟨phase2Wrap baselineTM gatedDecisionTM d,t+1+u,by omega,hseq,
    (phase2Wrap_halted_iff _ _ _).mpr hd,hv⟩

end IrrRAFEnumeration.CountPostlude
