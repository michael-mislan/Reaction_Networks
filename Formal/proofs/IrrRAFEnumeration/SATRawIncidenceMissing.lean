import proofs.IrrRAFEnumeration.SATRawIncidenceLocate

namespace IrrRAFEnumeration.SATSource

open Complexity SAT Complexity.TM

theorem incidence_eof_run (sign found : Bool) (inp jt vt out : Tape)
    (hi : inp.read = Γ.blank) (hj : jt.read ≠ Γ.start)
    (hv : vt.read ≠ Γ.start) (ho : out.read ≠ Γ.start) :
    (rawIncidenceTM sign).reachesIn 2
      (incidenceCfg (incidenceScan found) inp jt vt out)
      (incidenceCfg incidenceHalt inp jt vt (out.writeAndMove (Γ.ofBool found) .right)) := by
  have hip : inp.read ≠ Γ.start := by rw [hi]; decide
  have h₁ := incidence_control_step sign (incidenceScan found) (incidenceAnswer found)
    inp jt vt out .stay .stay .stay (by simp [incidenceScan,incidenceHalt])
    hip hj hv ho (by rw [hi]; rfl)
  exact .step h₁ (.step (incidence_emit_step sign found inp jt vt out hip hj hv ho) .zero)

/-- Out-of-range clause queries halt with false, including the empty CNF.
No traversal of the unused tail of an oversized query register occurs. -/
theorem incidence_missing_clause_run (sign : Bool) (v j : Nat) (φ : CNF)
    (inp out : Tape) (ys : List Bool)
    (hin : inp.HasBinarySuffix φ.encode) (hj : φ.length ≤ j) (hout : OutAcc ys out) :
    ∃ inp' out', (rawIncidenceTM sign).reachesIn (φ.encode.length+2)
      (incidenceCfg (incidenceScan false) inp (regTape j) (regTape v) out)
      (incidenceCfg incidenceHalt inp' ⟨φ.length+1,regCells j⟩ (regTape v) out') ∧
      OutAcc (ys ++ [false]) out' ∧ inp'.HasBinarySuffix [] ∧
      inp'.cells = inp.cells ∧ inp'.head = inp.head+φ.encode.length := by
  obtain ⟨inp₁,hr₁,hs,hc,hh⟩ := incidence_skip_prefix_run sign φ j 1 inp (regTape v) out []
    (by simpa using hin) (by omega) (by omega)
    (parked_regTape v).read_ne_start hout.parked.read_ne_start
  have hjp : (⟨1+φ.length,regCells j⟩ : Tape).read ≠ Γ.start := by
    simp [Tape.read, regCells]
    split <;> decide
  have hr₂ := incidence_eof_run sign false inp₁ ⟨1+φ.length,regCells j⟩ (regTape v) out
    hs.read_nil hjp (parked_regTape v).read_ne_start hout.parked.read_ne_start
  refine ⟨inp₁, _, ?_, outAcc_append_bit hout false, hs, hc, hh⟩
  simpa only [Nat.add_comm 1 φ.length] using (rawIncidenceTM sign).reachesIn_trans hr₁ hr₂

end IrrRAFEnumeration.SATSource
