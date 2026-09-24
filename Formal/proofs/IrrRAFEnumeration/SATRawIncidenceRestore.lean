import proofs.IrrRAFEnumeration.SATRawIncidenceQuery

namespace IrrRAFEnumeration.SATSource

open Complexity SAT Complexity.TM

def incidenceQueryWork (j v : Nat) : Fin 2 → Tape :=
  fun i => if i = 0 then regTape j else regTape v

def incidenceRestoreTM : TM 2 := seqTM rewindInputTM (rewindWorkTM 0)

/-- Restore both displaced heads without changing source, query values, or
the output accumulator. The two rewind budgets and their boundary are charged. -/
theorem incidence_restore_run (inp out : Tape) (j v h B : Nat) (ys : List Bool)
    (hip : Parked inp) (hzero : inp.cells 0 = Γ.start) (hib : inp.head ≤ B)
    (hh : 1 ≤ h) (hhb : h ≤ B) (hout : OutAcc ys out) :
    ∃ c t, t ≤ 2*B+5 ∧
      incidenceRestoreTM.reachesIn t
        ⟨incidenceRestoreTM.qstart,inp,(fun i => if i = 0 then ⟨h,regCells j⟩ else regTape v),out⟩ c ∧
      incidenceRestoreTM.halted c ∧ c.input = ⟨1,inp.cells⟩ ∧
      c.work = incidenceQueryWork j v ∧ OutAcc ys c.output := by
  let W : Fin 2 → Tape := fun i => if i = 0 then ⟨h,regCells j⟩ else regTape v
  have hjp : Parked (⟨h,regCells j⟩ : Tape) := by
    refine ⟨hh,?_⟩
    intro x hx
    simp [regCells,show x ≠ 0 from by omega]
    split <;> decide
  have hwp : ∀ i, Parked (W i) := by
    intro i
    dsimp [W]
    split
    · exact hjp
    · exact parked_regTape v
  let P : Tape → (Fin 2 → Tape) → Tape → Prop := fun a w o =>
    a.cells = inp.cells ∧ w = W ∧ OutAcc ys o
  have hri := rewindInputTM_hoareTime_frame (n := 2) B (P := P) (by
    intro a w o a' w' o' hp hc _ hw ho
    exact ⟨hc.trans hp.1,hw.trans hp.2.1,ho ▸ hp.2.2⟩)
  obtain ⟨c₁,t₁,ht₁,hr₁,hh₁,hhead₁,hcells₁,hw₁,ho₁⟩ := hri inp W out
    ⟨hzero,hip.2,hib,hout.parked.read_ne_start,hout.parked.1,
      fun i => ⟨(hwp i).read_ne_start,(hwp i).1⟩,rfl,rfl,hout⟩
  have hi₁ : c₁.input = ⟨1,inp.cells⟩ := Tape.ext hhead₁ hcells₁
  have hip₁ : Parked c₁.input := by rw [hi₁]; exact ⟨by rfl,hip.2⟩
  have hwp₁ : ∀ i, Parked (c₁.work i) := by rw [hw₁]; exact hwp
  let P₂ : Tape → (Fin 2 → Tape) → Tape → Prop := fun a w o =>
    a = c₁.input ∧ (w 0).cells = regCells j ∧ w 1 = regTape v ∧ OutAcc ys o
  have hrw := rewindWorkTM_hoareTime_frame (0 : Fin 2) B (P := P₂) (by
    intro a w o a' w' o' hp hc _ hw hi hoc hoh
    exact ⟨hi.trans hp.1,hc.trans hp.2.1,
      (hw 1 (by decide)).trans hp.2.2.1,(Tape.ext hoh hoc) ▸ hp.2.2.2⟩)
  obtain ⟨c₂,t₂,ht₂,hr₂,hh₂,hhead₂,hi₂,hc₂,hv₂,ho₂⟩ := hrw c₁.input c₁.work c₁.output
    ⟨by rw [hw₁]; rfl, (hwp₁ 0).2, by simpa [hw₁,W] using hhb,
      hip₁.read_ne_start,ho₁.parked.read_ne_start,ho₁.parked.1,
      fun i _ => ⟨(hwp₁ i).read_ne_start,(hwp₁ i).1⟩,
      rfl,by rw [hw₁]; rfl,by simp [hw₁,W],ho₁⟩
  have hw₂ : c₂.work = incidenceQueryWork j v := by
    funext i
    fin_cases i
    · exact Tape.ext hhead₂ hc₂
    · exact hv₂
  have htrans : (fun i => transitionTape (c₁.work i)) = c₁.work :=
    funext fun i => (hwp₁ i).transitionTape_eq_self
  have hall := seqTM_reachesIn_of_reachesIn (rewindInputTM (n := 2)) (rewindWorkTM 0)
    hr₁ hh₁ (by
      simpa only [hip₁.transitionInput_eq_self,htrans,ho₁.parked.transitionTape_eq_self] using hr₂)
  refine ⟨phase2Wrap rewindInputTM (rewindWorkTM 0) c₂,t₁+1+t₂,by omega,hall,?_,
    hi₂.trans hi₁,hw₂,ho₂⟩
  exact (phase2Wrap_halted_iff _ _ _).mpr hh₂

end IrrRAFEnumeration.SATSource
