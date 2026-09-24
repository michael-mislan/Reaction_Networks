import proofs.IrrRAFEnumeration.SATRawIncidenceLiteral

namespace IrrRAFEnumeration.SATSource

open Complexity SAT Complexity.TM

def incidenceClauseMatch (sign : Bool) (v : Nat) (c : Clause) : Bool :=
  c.any (fun lit => (lit.sign == sign) && decide (lit.var = v))

def incidenceClauseTime (v : Nat) : Clause → Nat
  | [] => 0
  | lit :: c => (2*lit.var+min lit.var v+5) + incidenceClauseTime v c

theorem incidenceClauseTime_bound (v : Nat) (c : Clause) :
    incidenceClauseTime v c ≤ 2*c.encode.length := by
  induction c with
  | nil => simp [incidenceClauseTime]
  | cons lit c ih =>
    have hm := Nat.min_le_left lit.var v
    simp only [incidenceClauseTime, Clause.encode_cons, List.length_append,
      doubleBits_length, Lit.encodeRaw_length, List.length_cons, List.length_nil]
    omega

/-- The actual machine accumulates membership across all literals of a clause,
resetting the variable query after each one. Duplicate literals are harmless. -/
theorem incidence_clause_body_run (sign found : Bool) (v : Nat) (c : Clause)
    (inp jt out : Tape) (tail : List Bool)
    (hin : inp.HasBinarySuffix (c.encode ++ tail))
    (hjp : Parked jt) (hj : jt.read = Γ.blank) (hop : Parked out) :
    ∃ inp', (rawIncidenceTM sign).reachesIn (incidenceClauseTime v c)
      (incidenceCfg (incidenceScan found) inp jt (regTape v) out)
      (incidenceCfg (incidenceScan (found || incidenceClauseMatch sign v c))
        inp' jt (regTape v) out) ∧
      inp'.HasBinarySuffix tail ∧ inp'.cells = inp.cells ∧
      inp'.head = inp.head+c.encode.length := by
  induction c generalizing found inp with
  | nil =>
    refine ⟨inp, ?_, ?_, rfl, by simp⟩
    · simpa [incidenceClauseTime, incidenceClauseMatch] using
        (TM.reachesIn.zero (tm := rawIncidenceTM sign)
          (c := incidenceCfg (incidenceScan found) inp jt (regTape v) out))
    · simpa using hin
  | cons lit c ih =>
    have hb : inp.HasBinarySuffix
        (doubleBits (lit.sign :: List.replicate lit.var true) ++ [false,true] ++
          (Clause.encode c ++ tail)) := by
      simpa [Clause.encode_cons, Lit.encodeRaw, Unary.encode, List.append_assoc] using hin
    obtain ⟨inp₁,hr₁,hs₁,hc₁,hh₁⟩ := incidence_literal_run sign lit.sign found v lit.var
      inp jt out (Clause.encode c ++ tail) hb hjp hj hop
    obtain ⟨inp₂,hr₂,hs₂,hc₂,hh₂⟩ := ih
      (found || ((lit.sign == sign) && decide (lit.var = v))) inp₁ hs₁
    refine ⟨inp₂, ?_, hs₂, hc₂.trans hc₁, ?_⟩
    · simpa [incidenceClauseTime, incidenceClauseMatch, Bool.or_assoc] using
        (rawIncidenceTM sign).reachesIn_trans hr₁ hr₂
    · simp only [Clause.encode_cons, List.length_append, doubleBits_length,
        Lit.encodeRaw_length, List.length_cons, List.length_nil]
      omega

end IrrRAFEnumeration.SATSource
