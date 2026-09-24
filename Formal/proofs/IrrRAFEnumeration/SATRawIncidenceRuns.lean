import proofs.IrrRAFEnumeration.SATRawIncidenceSemantics

namespace IrrRAFEnumeration.SATSource

open Complexity SAT Complexity.TM

theorem incidence_first_step (sign found ofl b : Bool) (sm : Option Bool)
    (inp jt vt out : Tape) (hr : inp.read = Γ.ofBool b)
    (hjp : jt.read ≠ Γ.start) (hvp : vt.read ≠ Γ.start) (hop : out.read ≠ Γ.start) :
    (rawIncidenceTM sign).step (incidenceCfg ⟨0,none,sm,ofl,found⟩ inp jt vt out) =
      some (incidenceCfg ⟨0,some b,sm,ofl,found⟩ (inp.move .right) jt vt out) := by
  apply incidence_control_step sign _ _ inp jt vt out .right .stay .stay
    (by simp [incidenceHalt])
    (by rw [hr]; cases b <;> decide) hjp hvp hop
  rw [hr]
  exact incidenceControl_first_bit sign found sm ofl b jt.read vt.read

/-- Every doubled unary mark is processed by exactly two real transitions,
with the capped head and overflow state given by incidenceUnaryStep. -/
theorem incidence_unary_pair_run (sign sm ofl found : Bool) (v h : Nat)
    (inp jt out : Tape) (hh : 1 ≤ h)
    (hr : inp.read = Γ.one) (hr' : (inp.move .right).read = Γ.one)
    (hj : jt.read = Γ.blank) (ho : out.read ≠ Γ.start) :
    (rawIncidenceTM sign).reachesIn 2
      (incidenceCfg ⟨0,none,some sm,ofl,found⟩ inp jt ⟨h,regCells v⟩ out)
      (incidenceCfg ⟨0,none,some sm,(incidenceUnaryStep v (h,ofl)).2,found⟩
        ((inp.move .right).move .right) jt
        ⟨(incidenceUnaryStep v (h,ofl)).1,regCells v⟩ out) := by
  have hjp : jt.read ≠ Γ.start := by rw [hj]; decide
  have hvp : (⟨h,regCells v⟩ : Tape).read ≠ Γ.start := by
    simp [Tape.read, regCells, show h ≠ 0 from by omega]
    split <;> decide
  have h₁ := incidence_first_step sign found ofl true (some sm) inp jt
    ⟨h,regCells v⟩ out hr hjp hvp ho
  have h₂ := incidence_control_step sign
    ⟨0,some true,some sm,ofl,found⟩
    ⟨0,none,some sm,(incidenceUnaryStep v (h,ofl)).2,found⟩
    (inp.move .right) jt ⟨h,regCells v⟩ out .right .stay
    (if h ≤ v then .right else .stay) (by simp [incidenceHalt])
    (by rw [hr']; decide) hjp hvp ho (by
      rw [hr', hj]
      exact incidenceControl_unary sign sm ofl found v h hh)
  have hmove : (⟨h,regCells v⟩ : Tape).move (if h ≤ v then .right else .stay) =
      ⟨(incidenceUnaryStep v (h,ofl)).1,regCells v⟩ := by
    by_cases hv : h ≤ v <;> simp [hv, Tape.move, incidenceUnaryStep]
  rw [hmove] at h₂
  exact .step h₁ (.step h₂ .zero)

/-- An arbitrary unary identifier block consumes exactly twice its length in
machine steps. The source suffix and all unconsumed data are retained. -/
theorem incidence_unary_block_run (sign sm found : Bool) (v n m : Nat)
    (inp jt out : Tape) (tail : List Bool)
    (hin : inp.HasBinarySuffix (doubleBits (List.replicate n true) ++ tail))
    (hj : jt.read = Γ.blank) (ho : out.read ≠ Γ.start) :
    ∃ inp', (rawIncidenceTM sign).reachesIn (2*n)
      (incidenceCfg ⟨0,none,some sm,(incidenceUnary v m).2,found⟩
        inp jt ⟨(incidenceUnary v m).1,regCells v⟩ out)
      (incidenceCfg ⟨0,none,some sm,(incidenceUnary v (m+n)).2,found⟩
        inp' jt ⟨(incidenceUnary v (m+n)).1,regCells v⟩ out) ∧
      inp'.HasBinarySuffix tail ∧ inp'.cells = inp.cells ∧ inp'.head = inp.head+2*n := by
  induction n generalizing m inp with
  | zero =>
    refine ⟨inp, ?_, ?_, rfl, by simp⟩
    · simpa using (TM.reachesIn.zero (tm := rawIncidenceTM sign)
        (c := incidenceCfg ⟨0,none,some sm,(incidenceUnary v m).2,found⟩
          inp jt ⟨(incidenceUnary v m).1,regCells v⟩ out))
    · simpa [doubleBits] using hin
  | succ n ih =>
    have hb : inp.HasBinarySuffix
        (true :: true :: (doubleBits (List.replicate n true) ++ tail)) := by
      simpa [List.replicate_succ, doubleBits] using hin
    have hp := incidence_unary_pair_run sign sm (incidenceUnary v m).2 found v
      (incidenceUnary v m).1 inp jt out
      (by rw [incidenceUnary_exact]; simp) hb.read_cons
      hb.move_right_cons.read_cons hj ho
    have he : incidenceUnaryStep v (incidenceUnary v m) = incidenceUnary v (m+1) := rfl
    simp only [he] at hp
    obtain ⟨inp',hr,hs,hc,hh⟩ := ih (m+1) ((inp.move .right).move .right)
      hb.move_right_cons.move_right_cons
    refine ⟨inp', ?_, hs, ?_, ?_⟩
    · simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (rawIncidenceTM sign).reachesIn_trans hp hr
    · exact hc.trans ((Tape.move_cells _ _).trans (Tape.move_cells _ _))
    · simp only [Tape.move] at hh
      omega

end IrrRAFEnumeration.SATSource
