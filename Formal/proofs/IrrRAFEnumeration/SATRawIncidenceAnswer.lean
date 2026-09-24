import proofs.IrrRAFEnumeration.SATRawIncidenceClause

namespace IrrRAFEnumeration.SATSource

open Complexity SAT Complexity.TM

theorem incidence_emit_step (sign found : Bool) (inp jt vt out : Tape)
    (hip : inp.read ≠ Γ.start) (hjp : jt.read ≠ Γ.start)
    (hvp : vt.read ≠ Γ.start) (hop : out.read ≠ Γ.start) :
    (rawIncidenceTM sign).step (incidenceCfg (incidenceAnswer found) inp jt vt out) =
      some (incidenceCfg incidenceHalt inp jt vt (out.writeAndMove (Γ.ofBool found) .right)) := by
  cases found <;>
    simp [TM.step, rawIncidenceTM, incidenceCfg, incidenceAnswer, incidenceHalt,
      incidenceControl, incidenceSafeDir, hip, hop, Γ.ofBool] <;>
    refine ⟨rfl, ?_⟩ <;>
    funext i <;> by_cases hi : i = 0
  all_goals
    simp only [hi, ↓reduceIte, hjp, hvp]
    first
    | exact writeAndMove_readBack jt hjp .stay
    | exact writeAndMove_readBack vt hvp .stay

theorem incidence_terminator_run (sign found : Bool) (v : Nat)
    (inp jt out : Tape) (tail : List Bool)
    (hin : inp.HasBinarySuffix (true :: false :: tail))
    (hj : jt.read = Γ.blank) (hop : out.read ≠ Γ.start) :
    (rawIncidenceTM sign).reachesIn 3
      (incidenceCfg (incidenceScan found) inp jt (regTape v) out)
      (incidenceCfg incidenceHalt ((inp.move .right).move .right) jt (regTape v)
        (out.writeAndMove (Γ.ofBool found) .right)) := by
  have hjp : jt.read ≠ Γ.start := by rw [hj]; decide
  have hvp := (parked_regTape v).read_ne_start
  have h₁ := incidence_first_step sign found false true none inp jt (regTape v) out
    hin.read_cons hjp hvp hop
  have h₂ := incidence_control_step sign ⟨0,some true,none,false,found⟩
    (incidenceAnswer found) (inp.move .right) jt (regTape v) out .right .stay .stay
    (by simp [incidenceHalt]) hin.move_right_cons.read_ne_start hjp hvp hop (by
      rw [hin.move_right_cons.read_cons, hj]
      rfl)
  have h₃ := incidence_emit_step sign found ((inp.move .right).move .right) jt
    (regTape v) out hin.move_right_cons.move_right_cons.read_ne_start hjp hvp hop
  exact .step h₁ (.step h₂ (.step h₃ .zero))

/-- Once the clause-query head selects this clause, the fixed machine emits
its exact membership bit and halts in linear time. -/
theorem incidence_selected_clause_run (sign : Bool) (v : Nat) (c : Clause)
    (inp jt out : Tape) (tail ys : List Bool)
    (hin : inp.HasBinarySuffix (c.encode ++ (true :: false :: tail)))
    (hjp : Parked jt) (hj : jt.read = Γ.blank) (hout : OutAcc ys out) :
    ∃ inp' out' t, t ≤ 2*c.encode.length+3 ∧
      (rawIncidenceTM sign).reachesIn t
        (incidenceCfg (incidenceScan false) inp jt (regTape v) out)
        (incidenceCfg incidenceHalt inp' jt (regTape v) out') ∧
      OutAcc (ys ++ [incidenceClauseMatch sign v c]) out' ∧
      inp'.HasBinarySuffix tail ∧ inp'.cells = inp.cells ∧
      inp'.head = inp.head+c.encode.length+2 := by
  obtain ⟨inp₁,hr₁,hs,hc,hh⟩ := incidence_clause_body_run sign false v c inp jt out
    (true :: false :: tail) hin hjp hj hout.parked
  simp only [Bool.false_or] at hr₁
  have hr₂ := incidence_terminator_run sign (incidenceClauseMatch sign v c) v inp₁ jt out
    tail hs hj hout.parked.read_ne_start
  refine ⟨(inp₁.move .right).move .right, _, incidenceClauseTime v c+3,
    Nat.add_le_add_right (incidenceClauseTime_bound v c) 3,
    (rawIncidenceTM sign).reachesIn_trans hr₁ hr₂,
    outAcc_append_bit hout _, hs.move_right_cons.move_right_cons, ?_, ?_⟩
  · exact (Tape.move_cells _ _).trans ((Tape.move_cells _ _).trans hc)
  · simp only [Tape.move]
    omega

end IrrRAFEnumeration.SATSource
