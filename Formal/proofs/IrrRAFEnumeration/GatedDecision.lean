import proofs.IrrRAFEnumeration.DecisionReporter
import proofs.Complexitylib.Models.TuringMachine.Combinators.Internal.Seq

namespace IrrRAFEnumeration.GatedDecision
open Complexity Complexity.TM HeaderComparison GatedHeader DecisionReporter

def placedReporter : TM 3 := placeWorkTM 0 1 reporterTM

theorem placed_reporter_correct (inp out : Tape) (work : Fin 3 → Tape) (answer : Bool)
    (hi : Parked inp) (hw : ∀ i, Parked (work i))
    (ho : out.StartInvariant) (hr : (work 1).read = Γ.ofBool answer) :
    ∃ c, placedReporter.reachesIn (out.head+2) ⟨(0 : Fin 3),inp,work,out⟩ c ∧
      placedReporter.halted c ∧ c.output.cells 1 = Γ.ofBool (!answer) := by
  obtain ⟨c,hc,hh,hv,_,_⟩ := reporter_correct inp (work 0) (work 1) out answer
    hi (hw 0) (hw 1) ho hr
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal reporterTM 0 1
    (fun _ => work 2) hc (fun _ _ => (hw 2).read_ne_start)
  have heq : placeWorkCfg reporterTM 0 1 (fun _ => work 2)
      (config 0 inp (work 0) (work 1) out) = (⟨(0 : Fin 3),inp,work,out⟩ : Cfg 3 placedReporter.Q) := by
    refine Cfg.ext rfl rfl ?_ rfl
    funext i
    fin_cases i <;> rfl
  rw [heq] at hp
  exact ⟨_,hp,hh,hv⟩

def gatedDecisionTM : TM 3 := seqTM gateTM placedReporter

/-- A physical verdict machine: failure of the no-case certificate is reported
as a one in output cell one, including when the source computation timed out. -/
theorem gated_decision_correct (actual supplied : Nat) (success : Bool)
    (inp expected flag clock out : Tape) (hi : Parked inp) (he : Parked expected)
    (hf : Parked flag) (hc : Parked clock) (ho : Parked out) (hInv : out.StartInvariant)
    (hclock : clock.read = Γ.ofBool success) (hE : UnaryPrefix expected supplied Γ.blank)
    (hO : success = true → UnaryPrefix (parkOutput out) actual Γ.zero) :
    ∃ c t, t ≤ 3*out.head+2*supplied+9 ∧
      gatedDecisionTM.reachesIn t
        (phase1Wrap gateTM placedReporter (gateConfig none inp expected flag clock out)) c ∧
      gatedDecisionTM.halted c ∧
      c.output.cells 1 = Γ.ofBool (!(success && decide (actual = supplied))) := by
  obtain ⟨c,t,ht,hgate,hhalt,hver,hcells,hinput,hwork,hout⟩ :=
    gated_comparison_correct actual supplied success inp expected flag clock out
      hi he hf hc ho hInv hclock hE hO
  have hci : Parked c.input := by rw [hinput]; exact hi
  have hco : c.output.StartInvariant := ⟨by rw [hcells]; exact hInv.1,
    by rw [hcells]; exact hInv.2⟩
  obtain ⟨d,hreport,hd,hv⟩ := placed_reporter_correct c.input c.output c.work
    (success && decide (actual = supplied)) hci hwork hco hver
  have hwt : (fun i => transitionTape (c.work i)) = c.work :=
    funext (fun i => (hwork i).transitionTape_eq_self)
  have hseq := seqTM_reachesIn_of_reachesIn gateTM placedReporter hgate hhalt (by
    simpa only [hci.transitionInput_eq_self,hwt,hout.transitionTape_eq_self] using hreport)
  refine ⟨phase2Wrap gateTM placedReporter d,t+1+(c.output.head+2),?_,hseq,
    (phase2Wrap_halted_iff _ _ _).mpr hd,hv⟩
  have hhead := TM.output_head_reachesIn_bound gateTM hgate
  change c.output.head ≤ out.head+t at hhead
  omega

end IrrRAFEnumeration.GatedDecision
