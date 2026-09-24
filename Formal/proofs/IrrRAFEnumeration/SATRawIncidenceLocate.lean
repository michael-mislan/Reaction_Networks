import proofs.IrrRAFEnumeration.SATRawIncidenceSkip

namespace IrrRAFEnumeration.SATSource

open Complexity SAT Complexity.TM

/-- Skip any prefix whose clause indices precede the requested index. -/
theorem incidence_skip_prefix_run (sign : Bool) (pre : CNF) (j h : Nat)
    (inp vt out : Tape) (tail : List Bool)
    (hin : inp.HasBinarySuffix (pre.encode ++ tail))
    (hh : 1 ≤ h) (hb : h+pre.length ≤ j+1)
    (hv : vt.read ≠ Γ.start) (ho : out.read ≠ Γ.start) :
    ∃ inp', (rawIncidenceTM sign).reachesIn pre.encode.length
      (incidenceCfg (incidenceScan false) inp ⟨h,regCells j⟩ vt out)
      (incidenceCfg (incidenceScan false) inp' ⟨h+pre.length,regCells j⟩ vt out) ∧
      inp'.HasBinarySuffix tail ∧ inp'.cells = inp.cells ∧ inp'.head = inp.head+pre.encode.length := by
  induction pre generalizing h inp with
  | nil =>
    refine ⟨inp, ?_, ?_, rfl, by simp⟩
    · simpa using (TM.reachesIn.zero (tm := rawIncidenceTM sign)
        (c := incidenceCfg (incidenceScan false) inp ⟨h,regCells j⟩ vt out))
    · simpa using hin
  | cons c pre ih =>
    have hj : (⟨h,regCells j⟩ : Tape).read = Γ.one := by
      simp [Tape.read, regCells, show h ≠ 0 from by omega,
        show h ≤ j from by simp only [List.length_cons] at hb; omega]
    have hs : inp.HasBinarySuffix (c.encode ++ (true :: false :: (CNF.encode pre ++ tail))) := by
      simpa [CNF.encode_cons, List.append_assoc] using hin
    obtain ⟨inp₁,hr₁,hs₁,hc₁,hh₁⟩ := incidence_skip_clause_run sign c (CNF.encode pre ++ tail)
      inp ⟨h,regCells j⟩ vt out hs hj hv ho
    obtain ⟨inp₂,hr₂,hs₂,hc₂,hh₂⟩ := ih (h+1) inp₁ hs₁ (by omega) (by
      simp only [List.length_cons] at hb
      omega)
    refine ⟨inp₂, ?_, hs₂, hc₂.trans hc₁, ?_⟩
    · convert (rawIncidenceTM sign).reachesIn_trans hr₁ hr₂ using 1 <;>
        simp [CNF.encode_cons, List.length_append, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm]
      omega
    · simp only [CNF.encode_cons, List.length_append, List.length_cons, List.length_nil]
      omega

/-- Locate a requested clause from the beginning of a CNF and emit its exact
membership bit. The runtime index is the length of the skipped prefix. -/
theorem incidence_located_clause_run (sign : Bool) (v : Nat) (pre post : CNF) (c : Clause)
    (inp out : Tape) (ys : List Bool)
    (hin : inp.HasBinarySuffix ((pre ++ c :: post).encode)) (hout : OutAcc ys out) :
    ∃ inp' out' t, t ≤ 2*(pre ++ c :: post).encode.length+3 ∧
      (rawIncidenceTM sign).reachesIn t
        (incidenceCfg (incidenceScan false) inp (regTape pre.length) (regTape v) out)
        (incidenceCfg incidenceHalt inp' ⟨pre.length+1,regCells pre.length⟩ (regTape v) out') ∧
      OutAcc (ys ++ [incidenceClauseMatch sign v c]) out' ∧
      inp'.HasBinarySuffix post.encode ∧ inp'.cells = inp.cells ∧
      inp'.head = inp.head+pre.encode.length+c.encode.length+2 := by
  have hp : inp.HasBinarySuffix (pre.encode ++ (c.encode ++ (true :: false :: post.encode))) := by
    simpa [CNF.encode_append, CNF.encode_cons, List.append_assoc] using hin
  obtain ⟨inp₁,hr₁,hs,hc,hh⟩ := incidence_skip_prefix_run sign pre pre.length 1 inp
    (regTape v) out (c.encode ++ (true :: false :: post.encode)) hp (by omega) (by omega)
    (parked_regTape v).read_ne_start hout.parked.read_ne_start
  have hjp : Parked (⟨1+pre.length,regCells pre.length⟩ : Tape) := by
    refine ⟨by simp, ?_⟩
    intro x hx
    simp [regCells, show x ≠ 0 from by omega]
    split <;> decide
  have hj : (⟨1+pre.length,regCells pre.length⟩ : Tape).read = Γ.blank := by
    simp [Tape.read, regCells, Nat.add_comm]
  obtain ⟨inp₂,out₂,t₂,ht₂,hr₂,ho₂,hs₂,hc₂,hh₂⟩ := incidence_selected_clause_run sign v c
    inp₁ ⟨1+pre.length,regCells pre.length⟩ out post.encode ys hs hjp hj hout
  refine ⟨inp₂,out₂,pre.encode.length+t₂, ?_, ?_, ho₂,hs₂,hc₂.trans hc,?_⟩
  · simp only [CNF.encode_append, CNF.encode_cons, List.length_append,
      List.length_cons, List.length_nil]
    omega
  · simpa only [Nat.add_comm 1 pre.length] using (rawIncidenceTM sign).reachesIn_trans hr₁ hr₂
  · omega

end IrrRAFEnumeration.SATSource
