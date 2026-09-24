import proofs.IrrRAFEnumeration.SATRawIncidence

namespace IrrRAFEnumeration.SATSource

open Complexity SAT Complexity.TM

/-- The variable head is capped at its first blank. The Boolean remembers
whether the source literal continued beyond that blank. -/
def incidenceUnaryStep (v : Nat) (p : Nat × Bool) : Nat × Bool :=
  (if p.1 ≤ v then p.1+1 else p.1, p.2 || decide (v < p.1))

def incidenceUnary (v : Nat) : Nat → Nat × Bool
  | 0 => (1, false)
  | n+1 => incidenceUnaryStep v (incidenceUnary v n)

theorem incidenceUnary_exact (v n : Nat) :
    incidenceUnary v n = (min n v + 1, decide (v < n)) := by
  induction n with
  | zero => simp [incidenceUnary]
  | succ n ih =>
    rw [incidenceUnary, ih]
    unfold incidenceUnaryStep
    by_cases hn : n < v
    · have hnv : n ≤ v := by omega
      have hnv' : n+1 ≤ v := by omega
      simp [Nat.min_eq_left hnv, hnv', show ¬v < n from by omega,
        show ¬v < n+1 from by omega]
    · have hvn : v ≤ n := by omega
      have hvn' : v ≤ n+1 := by omega
      simp [Nat.min_eq_right hvn, Nat.min_eq_right hvn', show ¬v+1 ≤ v from by omega,
        show v < v+1 from by omega, show v < n+1 from by omega]

theorem incidenceUnary_match (v n : Nat) :
    (!(incidenceUnary v n).2 && decide (v < (incidenceUnary v n).1)) =
      decide (n = v) := by
  rw [incidenceUnary_exact]
  by_cases hn : n = v
  · subst n; simp
  · by_cases hl : n < v
    · simp [Nat.min_eq_left (by omega : n ≤ v), show ¬v < n from by omega,
        show ¬v < n+1 from by omega, hn]
    · simp [show v < n from by omega, hn]

/-- The two source bits for a unary mark use exactly the tested head/overflow
update in the actual finite control, with the clause query at blank. -/
theorem incidenceControl_unary (sign sm ofl found : Bool) (v h : Nat) (hh : 1 ≤ h) :
    incidenceControl sign ⟨0, some true, some sm, ofl, found⟩ Γ.one Γ.blank
      (regCells v h) =
      (⟨0, none, some sm, (incidenceUnaryStep v (h,ofl)).2, found⟩,
        Dir3.right, Dir3.stay, if h ≤ v then Dir3.right else Dir3.stay, none) := by
  by_cases hv : h ≤ v
  · simp [incidenceControl, regCells, show h ≠ 0 from by omega, hv,
      incidenceUnaryStep, show ¬v < h from by omega]
  · simp [incidenceControl, regCells, show h ≠ 0 from by omega, hv,
      incidenceUnaryStep, show v < h from by omega]

theorem incidenceControl_first_bit (sign found : Bool) (sm : Option Bool)
    (ofl b : Bool) (jh vh : Γ) :
    incidenceControl sign ⟨0, none, sm, ofl, found⟩ (Γ.ofBool b) jh vh =
      (⟨0, some b, sm, ofl, found⟩, Dir3.right, Dir3.stay, Dir3.stay, none) := by
  cases b <;> simp [incidenceControl, Γ.ofBool]

theorem incidenceControl_sign (sign b found : Bool) (vh : Γ) :
    incidenceControl sign ⟨0, some b, none, false, found⟩ (Γ.ofBool b) Γ.blank vh =
      (⟨0, none, some (b == sign), false, found⟩,
        Dir3.right, Dir3.stay, Dir3.stay, none) := by
  cases b <;> cases sign <;> simp [incidenceControl, Γ.ofBool]

/-- A literal separator recognizes exactly equality of sign and identifier.
This includes identifier zero, oversized queries, and source overflow. -/
theorem incidenceControl_literal_match (sign b found : Bool) (v n : Nat) :
    incidenceControl sign
      ⟨0, some false, some (b == sign), (incidenceUnary v n).2, found⟩
      Γ.one Γ.blank (regCells v (incidenceUnary v n).1) =
      (incidenceRewind (found || ((b == sign) && decide (n = v))),
        Dir3.right, Dir3.stay, Dir3.left, none) := by
  have hh : 1 ≤ (incidenceUnary v n).1 := by rw [incidenceUnary_exact]; simp
  have hblank : (regCells v (incidenceUnary v n).1 == Γ.blank) =
      decide (v < (incidenceUnary v n).1) := by
    by_cases hv : (incidenceUnary v n).1 ≤ v
    · simp [regCells, show (incidenceUnary v n).1 ≠ 0 from by omega, hv,
        show ¬v < (incidenceUnary v n).1 from by omega]
    · simp [regCells, show (incidenceUnary v n).1 ≠ 0 from by omega, hv,
        show v < (incidenceUnary v n).1 from by omega]
  simp only [incidenceControl, Fin.isValue, reduceCtorEq, ↓reduceIte,
    beq_self_eq_true, Bool.false_eq_true, hblank, incidenceRewind]
  have hm := incidenceUnary_match v n
  cases b <;> cases sign <;> cases found <;>
    simp_all

/-- Lift a non-emitting control action to one concrete machine transition.
This lets the literal induction reuse the exact control identities above. -/
theorem incidence_control_step (sign : Bool) (q q' : RawIncidenceState)
    (inp jt vt out : Tape) (di dj dv : Dir3)
    (hq : q ≠ incidenceHalt) (hip : inp.read ≠ Γ.start)
    (hjp : jt.read ≠ Γ.start) (hvp : vt.read ≠ Γ.start) (hop : out.read ≠ Γ.start)
    (hc : incidenceControl sign q inp.read jt.read vt.read = (q',di,dj,dv,none)) :
    (rawIncidenceTM sign).step (incidenceCfg q inp jt vt out) =
      some (incidenceCfg q' (inp.move di) (jt.move dj) (vt.move dv) out) := by
  simp [TM.step, rawIncidenceTM, incidenceCfg, hq, hc, incidenceSafeDir, hip, hop]
  constructor
  · funext i
    by_cases hi : i = 0
    · simp only [hi, ↓reduceIte, hjp]
      exact writeAndMove_readBack jt hjp dj
    · simp only [hi, ↓reduceIte, hvp]
      exact writeAndMove_readBack vt hvp dv
  · exact writeAndMove_readBack out hop .stay

end IrrRAFEnumeration.SATSource
