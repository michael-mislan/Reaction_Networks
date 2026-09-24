import proofs.IrrRAFEnumeration.SATRawIncidenceRuns

namespace IrrRAFEnumeration.SATSource

open Complexity SAT Complexity.TM

theorem incidence_sign_pair_run (sign b found : Bool) (v : Nat)
    (inp jt out : Tape) (hr : inp.read = Γ.ofBool b)
    (hr' : (inp.move .right).read = Γ.ofBool b)
    (hj : jt.read = Γ.blank) (ho : out.read ≠ Γ.start) :
    (rawIncidenceTM sign).reachesIn 2
      (incidenceCfg (incidenceScan found) inp jt (regTape v) out)
      (incidenceCfg ⟨0,none,some (b == sign),false,found⟩
        ((inp.move .right).move .right) jt (regTape v) out) := by
  have hjp : jt.read ≠ Γ.start := by rw [hj]; decide
  have hvp := (parked_regTape v).read_ne_start
  have h₁ := incidence_first_step sign found false b none inp jt (regTape v) out
    hr hjp hvp ho
  have h₂ := incidence_control_step sign ⟨0,some b,none,false,found⟩
    ⟨0,none,some (b == sign),false,found⟩ (inp.move .right) jt (regTape v) out
    .right .stay .stay (by simp [incidenceHalt])
    (by rw [hr']; cases b <;> decide) hjp hvp ho (by
      rw [hr',hj]; exact incidenceControl_sign sign b found _)
  exact .step h₁ (.step h₂ .zero)

theorem incidence_separator_run (sign b found : Bool) (v n : Nat)
    (inp jt out : Tape) (tail : List Bool)
    (hin : inp.HasBinarySuffix (false :: true :: tail))
    (hjp : Parked jt) (hj : jt.read = Γ.blank) (hop : Parked out) :
    (rawIncidenceTM sign).reachesIn (min n v+3)
      (incidenceCfg ⟨0,none,some (b == sign),(incidenceUnary v n).2,found⟩
        inp jt ⟨(incidenceUnary v n).1,regCells v⟩ out)
      (incidenceCfg (incidenceScan (found || ((b == sign) && decide (n = v))))
        ((inp.move .right).move .right) jt (regTape v) out) := by
  have hvp : (⟨(incidenceUnary v n).1,regCells v⟩ : Tape).read ≠ Γ.start := by
    rw [incidenceUnary_exact]
    simp [Tape.read, regCells]
    split <;> decide
  have h₁ := incidence_first_step sign found (incidenceUnary v n).2 false (some (b == sign))
    inp jt ⟨(incidenceUnary v n).1,regCells v⟩ out hin.read_cons
    hjp.read_ne_start hvp hop.read_ne_start
  have h₂ := incidence_control_step sign
    ⟨0,some false,some (b == sign),(incidenceUnary v n).2,found⟩
    (incidenceRewind (found || ((b == sign) && decide (n = v))))
    (inp.move .right) jt ⟨(incidenceUnary v n).1,regCells v⟩ out
    .right .stay .left (by simp [incidenceHalt])
    hin.move_right_cons.read_ne_start hjp.read_ne_start hvp hop.read_ne_start (by
      rw [hin.move_right_cons.read_cons,hj]
      exact incidenceControl_literal_match sign b found v n)
  have hm : (⟨(incidenceUnary v n).1,regCells v⟩ : Tape).move .left =
      ⟨min n v,regCells v⟩ := by rw [incidenceUnary_exact]; simp [Tape.move]
  rw [hm] at h₂
  have hs := hin.move_right_cons.move_right_cons
  have h₃ := incidence_rewind_run sign (found || ((b == sign) && decide (n = v)))
    ((inp.move .right).move .right) jt out v (min n v) ⟨hs.1,hs.2.2.2⟩ hjp hop
  have hall := TM.reachesIn.step h₁ (TM.reachesIn.step h₂ h₃)
  simpa [Nat.add_assoc] using hall

/-- A full encoded literal, including its terminator and query reset, updates
the membership answer correctly and consumes exactly 2n+min(n,v)+5 steps. -/
theorem incidence_literal_run (sign b found : Bool) (v n : Nat)
    (inp jt out : Tape) (tail : List Bool)
    (hin : inp.HasBinarySuffix
      (doubleBits (b :: List.replicate n true) ++ [false,true] ++ tail))
    (hjp : Parked jt) (hj : jt.read = Γ.blank) (hop : Parked out) :
    ∃ inp', (rawIncidenceTM sign).reachesIn (2*n+min n v+5)
      (incidenceCfg (incidenceScan found) inp jt (regTape v) out)
      (incidenceCfg (incidenceScan (found || ((b == sign) && decide (n = v))))
        inp' jt (regTape v) out) ∧
      inp'.HasBinarySuffix tail ∧ inp'.cells = inp.cells ∧ inp'.head = inp.head+2*n+4 := by
  have hb : inp.HasBinarySuffix
      (b :: b :: (doubleBits (List.replicate n true) ++ (false :: true :: tail))) := by
    simpa [doubleBits, List.append_assoc] using hin
  have hsign := incidence_sign_pair_run sign b found v inp jt out hb.read_cons
    hb.move_right_cons.read_cons hj hop.read_ne_start
  obtain ⟨inp₂,hun,hs,hc,hh⟩ := incidence_unary_block_run sign (b == sign) found v n 0
    ((inp.move .right).move .right) jt out (false :: true :: tail)
    hb.move_right_cons.move_right_cons hj hop.read_ne_start
  simp only [incidenceUnary, Nat.zero_add] at hun
  have hsep := incidence_separator_run sign b found v n inp₂ jt out tail hs hjp hj hop
  have hall := (rawIncidenceTM sign).reachesIn_trans
    ((rawIncidenceTM sign).reachesIn_trans hsign hun) hsep
  refine ⟨(inp₂.move .right).move .right, ?_, hs.move_right_cons.move_right_cons, ?_, ?_⟩
  · convert hall using 1
    omega
  · exact (Tape.move_cells _ _).trans ((Tape.move_cells _ _).trans
      (hc.trans ((Tape.move_cells _ _).trans (Tape.move_cells _ _))))
  · simp only [Tape.move] at hh ⊢
    omega

end IrrRAFEnumeration.SATSource
