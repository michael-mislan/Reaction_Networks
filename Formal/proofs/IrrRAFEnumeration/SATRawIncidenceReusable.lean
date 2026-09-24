import proofs.IrrRAFEnumeration.SATRawIncidenceRestore

namespace IrrRAFEnumeration.SATSource

open Complexity SAT Complexity.TM

def rawIncidenceReusableTM (sign : Bool) : TM 2 :=
  seqTM (rawIncidenceTM sign) incidenceRestoreTM

/-- Uniform reusable incidence query, including absent clause indices. The
source and both runtime unary indices return exactly to their entry tapes. -/
theorem rawIncidenceReusableTM_correct (sign : Bool) (v j : Nat) (φ : CNF)
    (inp : Tape) (ys : List Bool) (hin : inp.HasBinarySuffix φ.encode)
    (hhead : inp.head = 1) (hzero : inp.cells 0 = Γ.start) :
    (rawIncidenceReusableTM sign).HoareTime
      (EmitPred inp (incidenceQueryWork j v) ys)
      (EmitPred inp (incidenceQueryWork j v) (ys ++ [incidenceCNFMatch sign v φ j]))
      (4*φ.encode.length+11) := by
  rintro a w out ⟨rfl,rfl,hout⟩
  obtain ⟨inp₁,out₁,t₁,h,ht₁,hh,hhb,hr₁,ho₁,hip₁,hc₁,hb₁⟩ :=
    incidence_query_run sign v j φ a out ys hin hout
  have hm : φ.length ≤ φ.encode.length := by
    simpa [clauseMarks_encode] using clauseMarks_length_le none φ.encode
  obtain ⟨c₂,t₂,ht₂,hr₂,hh₂,hi₂,hw₂,ho₂⟩ := incidence_restore_run inp₁ out₁ j v h
    (φ.encode.length+1) (ys ++ [incidenceCNFMatch sign v φ j]) hip₁
    (by rw [hc₁]; exact hzero) (by omega) hh (by omega) ho₁
  let c₁ := incidenceCfg incidenceHalt inp₁ ⟨h,regCells j⟩ (regTape v) out₁
  have hjp : Parked (⟨h,regCells j⟩ : Tape) := by
    refine ⟨hh,?_⟩
    intro x hx
    simp [regCells,show x ≠ 0 from by omega]
    split <;> decide
  have hwp : ∀ i, Parked (c₁.work i) := by
    intro i
    dsimp [c₁,incidenceCfg]
    split
    · exact hjp
    · exact parked_regTape v
  have hw : (fun i => transitionTape (c₁.work i)) = c₁.work :=
    funext fun i => (hwp i).transitionTape_eq_self
  change (rawIncidenceTM sign).reachesIn t₁ _ c₁ at hr₁
  have hp : Parked c₁.input := hip₁
  have ho : OutAcc (ys ++ [incidenceCNFMatch sign v φ j]) c₁.output := ho₁
  have hall := seqTM_reachesIn_of_reachesIn (rawIncidenceTM sign) incidenceRestoreTM hr₁
    (show (rawIncidenceTM sign).halted c₁ from rfl) (by
      simpa only [hp.transitionInput_eq_self,hw,ho.parked.transitionTape_eq_self] using hr₂)
  refine ⟨phase2Wrap (rawIncidenceTM sign) incidenceRestoreTM c₂,t₁+1+t₂,
    by omega,hall,?_,?_,hw₂,ho₂⟩
  · exact (phase2Wrap_halted_iff _ _ _).mpr hh₂
  · change c₂.input = a
    rw [hi₂]
    exact Tape.ext hhead.symm hc₁

end IrrRAFEnumeration.SATSource
