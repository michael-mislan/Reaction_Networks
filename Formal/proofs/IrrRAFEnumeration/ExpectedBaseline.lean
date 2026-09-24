import proofs.IrrRAFEnumeration.GatedDecision
import proofs.Complexitylib.Models.TuringMachine.Registers.RegisterOps

namespace IrrRAFEnumeration.ExpectedBaseline
open Complexity Complexity.TM HeaderComparison

def baselineWork (k : Nat) (flag clock : Tape) : Fin 3 → Tape :=
  ![regTape k,flag,clock]

theorem increment_baseline (k : Nat) (inp flag clock out : Tape)
    (hi : Parked inp) (hf : Parked flag) (hc : Parked clock) (ho : Parked out) :
    ∃ c t, t ≤ 2*k+4 ∧ (incRegTM (n := 3) 0).reachesIn t
      ⟨(incRegTM (n := 3) 0).qstart,inp,baselineWork k flag clock,out⟩ c ∧
      (incRegTM (n := 3) 0).halted c ∧ c.input = inp ∧
      c.work = baselineWork (k+1) flag clock ∧ c.output = out := by
  have hw : ∀ i : Fin 3, i ≠ 0 → Parked (baselineWork k flag clock i) := by
    intro i hn
    fin_cases i
    · exact (hn rfl).elim
    · exact hf
    · exact hc
  obtain ⟨c,t,ht,hr,hh,hi',hw',ho'⟩ :=
    incRegTM_hoareTime_frame (0 : Fin 3) k inp (baselineWork k flag clock)
      (fun o => o = out) (fun _ h => h ▸ ho) hi hw rfl
      inp (baselineWork k flag clock) out ⟨rfl,rfl,rfl⟩
  refine ⟨c,t,ht,hr,hh,hi',?_,ho'⟩
  rw [hw']
  funext i
  fin_cases i <;> rfl

def baselineTM : TM 3 := seqTM (incRegTM 0) (incRegTM 0)

theorem baseline_correct (k : Nat) (inp flag clock out : Tape)
    (hi : Parked inp) (hf : Parked flag) (hc : Parked clock) (ho : Parked out) :
    ∃ c t, t ≤ 4*k+11 ∧ baselineTM.reachesIn t
      ⟨baselineTM.qstart,inp,baselineWork k flag clock,out⟩ c ∧
      baselineTM.halted c ∧ c.input = inp ∧
      c.work = baselineWork (k+2) flag clock ∧ c.output = out := by
  obtain ⟨c,t,ht,hr,hh,hi',hw',ho'⟩ := increment_baseline k inp flag clock out hi hf hc ho
  obtain ⟨d,s,hs,hr2,hh2,hi2,hw2,ho2⟩ := increment_baseline (k+1) inp flag clock out hi hf hc ho
  have hwp : ∀ i, Parked (c.work i) := by
    rw [hw']
    intro i
    fin_cases i <;> first | exact parked_regTape _ | exact hf | exact hc
  have hwt : (fun i => transitionTape (c.work i)) = c.work :=
    funext (fun i => (hwp i).transitionTape_eq_self)
  rw [hw'] at hwt
  have hseq := seqTM_reachesIn_of_reachesIn (incRegTM (n := 3) 0) (incRegTM 0) hr hh (by
    simpa only [hi',hw',ho',hi.transitionInput_eq_self,hwt,ho.transitionTape_eq_self] using hr2)
  exact ⟨phase2Wrap (incRegTM 0) (incRegTM 0) d,t+1+s,by omega,hseq,
    (phase2Wrap_halted_iff _ _ _).mpr hh2,hi2,hw2,ho2⟩

theorem register_prefix (k : Nat) : UnaryPrefix (regTape k) k Γ.blank := by
  constructor
  · intro j hj
    change regCells k (1+j) = Γ.one
    exact regCells_one (by omega) (by omega)
  · change regCells k (1+k) = Γ.blank
    exact regCells_blank (by omega)

end IrrRAFEnumeration.ExpectedBaseline
