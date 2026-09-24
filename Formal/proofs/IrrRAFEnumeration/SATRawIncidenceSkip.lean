import proofs.IrrRAFEnumeration.SATRawIncidenceAnswer

namespace IrrRAFEnumeration.SATSource

open Complexity SAT Complexity.TM

theorem incidence_skip_pair_run (sign a b : Bool) (inp jt vt out : Tape)
    (hr : inp.read = Γ.ofBool a) (hr' : (inp.move .right).read = Γ.ofBool b)
    (hj : jt.read = Γ.one) (hv : vt.read ≠ Γ.start) (ho : out.read ≠ Γ.start) :
    (rawIncidenceTM sign).reachesIn 2
      (incidenceCfg (incidenceScan false) inp jt vt out)
      (incidenceCfg (incidenceScan false) ((inp.move .right).move .right)
        (jt.move (if a && !b then .right else .stay)) vt out) := by
  have hjp : jt.read ≠ Γ.start := by rw [hj]; decide
  have h₁ := incidence_first_step sign false false a none inp jt vt out hr hjp hv ho
  have h₂ := incidence_control_step sign ⟨0,some a,none,false,false⟩ (incidenceScan false)
    (inp.move .right) jt vt out .right (if a && !b then .right else .stay) .stay
    (by simp [incidenceHalt]) (by rw [hr']; cases b <;> decide) hjp hv ho (by
      rw [hr',hj]
      cases a <;> cases b <;> rfl)
  exact .step h₁ (.step h₂ .zero)

theorem incidence_skip_data_run (sign : Bool) (data tail : List Bool)
    (inp jt vt out : Tape) (hin : inp.HasBinarySuffix (doubleBits data ++ tail))
    (hj : jt.read = Γ.one) (hv : vt.read ≠ Γ.start) (ho : out.read ≠ Γ.start) :
    ∃ inp', (rawIncidenceTM sign).reachesIn (2*data.length)
      (incidenceCfg (incidenceScan false) inp jt vt out)
      (incidenceCfg (incidenceScan false) inp' jt vt out) ∧
      inp'.HasBinarySuffix tail ∧ inp'.cells = inp.cells ∧ inp'.head = inp.head+2*data.length := by
  induction data generalizing inp with
  | nil =>
    refine ⟨inp, ?_, ?_, rfl, by simp⟩
    · exact .zero
    · simpa [doubleBits] using hin
  | cons b data ih =>
    have hb : inp.HasBinarySuffix (b :: b :: (doubleBits data ++ tail)) := by
      simpa [doubleBits] using hin
    have hp := incidence_skip_pair_run sign b b inp jt vt out hb.read_cons
      hb.move_right_cons.read_cons hj hv ho
    have hn : (b && !b) = false := by cases b <;> rfl
    simp only [hn, Bool.false_eq_true, ↓reduceIte, Tape.move] at hp
    obtain ⟨inp',hr,hs,hc,hh⟩ := ih ((inp.move .right).move .right)
      hb.move_right_cons.move_right_cons
    refine ⟨inp', ?_, hs, hc.trans ((Tape.move_cells _ _).trans (Tape.move_cells _ _)), ?_⟩
    · convert (rawIncidenceTM sign).reachesIn_trans hp hr using 1
      simp; omega
    · simp only [Tape.move] at hh
      simp only [List.length_cons]
      omega

theorem incidence_skip_clause_body_run (sign : Bool) (c : Clause) (tail : List Bool)
    (inp jt vt out : Tape) (hin : inp.HasBinarySuffix (c.encode ++ tail))
    (hj : jt.read = Γ.one) (hv : vt.read ≠ Γ.start) (ho : out.read ≠ Γ.start) :
    ∃ inp', (rawIncidenceTM sign).reachesIn c.encode.length
      (incidenceCfg (incidenceScan false) inp jt vt out)
      (incidenceCfg (incidenceScan false) inp' jt vt out) ∧
      inp'.HasBinarySuffix tail ∧ inp'.cells = inp.cells ∧ inp'.head = inp.head+c.encode.length := by
  induction c generalizing inp with
  | nil =>
    refine ⟨inp, .zero, ?_, rfl, by simp⟩
    simpa using hin
  | cons lit c ih =>
    have hb : inp.HasBinarySuffix (doubleBits lit.encodeRaw ++
        (false :: true :: (Clause.encode c ++ tail))) := by
      simpa [Clause.encode_cons, List.append_assoc] using hin
    obtain ⟨inp₁,hr₁,hs₁,hc₁,hh₁⟩ := incidence_skip_data_run sign lit.encodeRaw
      (false :: true :: (Clause.encode c ++ tail)) inp jt vt out hb hj hv ho
    have hr₂ := incidence_skip_pair_run sign false true inp₁ jt vt out hs₁.read_cons
      hs₁.move_right_cons.read_cons hj hv ho
    obtain ⟨inp₂,hr₃,hs₂,hc₂,hh₂⟩ := ih ((inp₁.move .right).move .right)
      hs₁.move_right_cons.move_right_cons
    refine ⟨inp₂, ?_, hs₂, ?_, ?_⟩
    · convert (rawIncidenceTM sign).reachesIn_trans
        ((rawIncidenceTM sign).reachesIn_trans hr₁ hr₂) hr₃ using 1
      simp only [Clause.encode_cons, List.length_append, doubleBits_length,
        List.length_cons, List.length_nil]
    · exact hc₂.trans ((Tape.move_cells _ _).trans ((Tape.move_cells _ _).trans hc₁))
    · simp only [Tape.move] at hh₂
      simp only [Clause.encode_cons, List.length_append, doubleBits_length,
        List.length_cons, List.length_nil]
      omega

/-- One preceding clause is skipped in exactly its encoded length plus two;
only its terminator advances the unary clause-query head. -/
theorem incidence_skip_clause_run (sign : Bool) (c : Clause) (tail : List Bool)
    (inp jt vt out : Tape)
    (hin : inp.HasBinarySuffix (c.encode ++ (true :: false :: tail)))
    (hj : jt.read = Γ.one) (hv : vt.read ≠ Γ.start) (ho : out.read ≠ Γ.start) :
    ∃ inp', (rawIncidenceTM sign).reachesIn (c.encode.length+2)
      (incidenceCfg (incidenceScan false) inp jt vt out)
      (incidenceCfg (incidenceScan false) inp' (jt.move .right) vt out) ∧
      inp'.HasBinarySuffix tail ∧ inp'.cells = inp.cells ∧
      inp'.head = inp.head+c.encode.length+2 := by
  obtain ⟨inp₁,hr₁,hs,hc,hh⟩ := incidence_skip_clause_body_run sign c (true :: false :: tail)
    inp jt vt out hin hj hv ho
  have hr₂ := incidence_skip_pair_run sign true false inp₁ jt vt out hs.read_cons
    hs.move_right_cons.read_cons hj hv ho
  refine ⟨(inp₁.move .right).move .right, (rawIncidenceTM sign).reachesIn_trans hr₁ hr₂,
    hs.move_right_cons.move_right_cons,
    (Tape.move_cells _ _).trans ((Tape.move_cells _ _).trans hc), ?_⟩
  simp only [Tape.move]
  omega

end IrrRAFEnumeration.SATSource
